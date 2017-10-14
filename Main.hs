{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Control.Applicative
import           Data.Attoparsec.ByteString.Char8
import           Data.ByteString                  (ByteString)
import           Data.Map.Strict                  (Map, (!), (\\))
import           Data.Typeable                    (typeOf)
import           Data.Word
import           Debug.Trace                      (trace)
import           Test.HUnit                       as Test
import           Text.Printf                      (printf)

import qualified Control.Exception                as Ex
import qualified Control.Monad.State              as State
import qualified Data.List                        as List
import qualified Data.Map.Strict                  as Map


--------------------------------------------------------------------------------
-- TERMS


type Identifier = String


data Literal
    = Bool Bool
    | Number Int
    deriving (Eq)


data Expr
    = Lam Identifier Expr
    | App Expr Expr
    | Lit Literal
    | Ident Identifier
    deriving (Eq)


instance Show Expr where
    show (Lam i e)        = "lam " ++ i ++ " " ++ show e
    show (App e1 e2)      = "app " ++ show e1 ++ " " ++ show e2
    show (Lit (Bool b))   = if b then "true" else "false"
    show (Lit (Number n)) = show n
    show (Ident i)        = i


expr :: Parser Expr
expr = char '(' &> expr <& char ')'
    <|> pure Lam <&> (string "lam" &> ident) <&> expr
    <|> pure App <&> (string "app" &> expr) <&> expr
    <|> Lit <$> literal
    <|> Ident <$> ident


ident :: Parser Identifier
ident = do
    x <- letter
    xs <- many' (letter <|> digit)
    return (x : xs)


literal :: Parser Literal
literal = Number <$> num
    <|> Bool <$> bool


num :: Parser Int
num = decimal


bool :: Parser Bool
bool = true <|> false where
    true = string "true" &> pure True
    false = string "false" &> pure False


letter :: Parser Char
letter = satisfy (inClass "A-Za-z")


-- Space-skipping applicative operators
(&>) :: Parser a -> Parser b -> Parser b
(&>) a b = (a *> skipSpace) *> (b <* skipSpace)


(<&) :: Parser a -> Parser b -> Parser a
(<&) a b = (a <* skipSpace) <* (b <* skipSpace)


(<&>) :: (Parser (a -> b)) -> Parser a -> Parser b
(<&>) f x = f <*> (skipSpace *> x)


-- (P)arse expressions
p :: ByteString -> Expr
p bs = case parseOnly (expr <* endOfInput) bs of
    Left e  -> error e
    Right x -> x


--------------------------------------------------------------------------------
-- TYPES


data Type
    = TInt | TBool
    | TLam Type Type
    | TIdent Identifier
    deriving (Eq, Ord)


instance Show Type where
    show TInt                      = "int"
    show TBool                     = "bool"
    show (TLam ty1@(TLam _ _) ty2) = "(" ++ show ty1 ++ ") → " ++ show ty2
    show (TLam ty1 ty2)            = show ty1 ++ " → " ++ show ty2
    show (TIdent i)                = i


ty :: Parser Type
ty = char '(' &> ty <& char ')'
    <|> (string "int" &> pure TInt)
    <|> (string "bool" &> pure TBool)
    <|> TLam <$> (string "lam" &> ty) <*> ty
    <|> TIdent <$> ident


-- Parse type signatures
t :: ByteString -> Type
t bs = case parseOnly (ty <* endOfInput) bs of
    Left e  -> error e
    Right x -> x


--------------------------------------------------------------------------------
-- CONSTRAINT-GENERATION


type Environment = Map Identifier Type
newtype Constraints = Constraints (Map Type Type) deriving (Eq)
data ConstraintSet = CS
    { cType        :: Type
    , cConstraints :: Constraints
    , cEnvironment :: Environment
    }


instance Show Constraints where
    show (Constraints m) = showMap m


instance Show ConstraintSet where
    show (CS t (Constraints c) e) = printf
        "type:\t\t%s\n\
        \constraints:\t%s\n\
        \environment:\t%s\n" (show t) (show c) (showMap e)


showMap :: (Show k, Show v) => Map k v -> String
showMap m = List.intercalate ", " (map s (Map.toList m))
    where s (k, v) = printf "%s = %s" (show k) (show v)


stdlib :: Environment
stdlib = Map.fromList
    [ ("add", t "lam int (lam int int)")
    , ("gt",  t "lam int (lam int bool)")
    , ("if",  t "lam bool (lam a (lam a a))")
    , ("fix", t "lam (lam a a) a")
    ]


gensym :: State.State Int String
gensym = do
    i <- State.get
    State.put (i+1)
    return ("a" ++ show i)


-- Constraint-generation function raw version
cg' :: Environment -> Expr -> State.State Int ConstraintSet
cg' env expr = case expr of
    Lit (Bool _) ->
        return $ CS TBool (Constraints Map.empty) env

    Lit (Number _) ->
        return $ CS  TInt (Constraints Map.empty) env

    Ident name ->
        return $ CS (env ! name) (Constraints Map.empty) env

    Lam arg body -> do
        sym <- gensym
        let env1 = Map.insert arg typeVar env
            typeVar = TIdent sym
        CS bodyType bodyConstraints env2 <- cg' env1 body
        return $ CS (TLam typeVar bodyType) bodyConstraints (Map.delete arg env2)

    App left right -> do
        CS leftType (Constraints leftConstraints) leftEnv <- cg' env left
        CS rightType (Constraints rightConstraints) rightEnv <- cg' env right
        sym <- gensym
        let typeVar = TIdent sym
            funcType = TLam rightType typeVar
            constraints = Map.insert leftType funcType
                (Map.union leftConstraints rightConstraints)
        return $ CS typeVar (Constraints constraints) env


cg :: Expr -> ConstraintSet
cg expr = State.evalState (cg' stdlib expr) 0


--------------------------------------------------------------------------------
-- SOLVING / SUBSTITUTION / UNIFICATION


newtype Substitution = Sub (Map Type Type) deriving (Eq)


instance Show Substitution where
    show (Sub m) = showMap m


-- Combine proceeds in two steps:
-- 1. Apply left substitution to the right
-- 2. Merge substitutions, favoring the right (replaced) substitutions
combine :: Substitution -> Substitution -> Substitution
combine left@(Sub left') (Sub right) = Sub (Map.union right' left')
    where right' = fmap (applySub left) right


-- sub algorithm. recursively replace idents, drawing from left as a
-- dictionary of replacements
applySub :: Substitution -> Type -> Type
applySub _ TInt = TInt
applySub _ TBool = TBool
applySub s (TLam t1 t2) = TLam (applySub s t1) (applySub s t2)
applySub (Sub s) var@(TIdent ident) =
    case Map.lookup var s of
        Nothing  -> var
        Just hit -> hit


-- unification: return a substitution that, if applied to the first type,
-- would produce the second type
unify :: Type -> Type -> Either String Substitution
unify type1 type2
    | type1 == type2 = Right $ Sub (Map.empty)
    | otherwise = case (type1, type2) of
          (TIdent x, TIdent y) -> Right $ Sub (Map.fromList [(TIdent x, TIdent y)])
          (x, TIdent y)        -> Right $ Sub (Map.fromList [(TIdent y, x)])
          (TIdent x, y)        -> Right $ Sub (Map.fromList [(TIdent x, y)])
          (TLam type1Arg type1Body, TLam type2Arg type2Body) -> do
              argSub <- unify type1Arg type2Arg
              let type1Body' = applySub argSub type1Body
              let type2Body' = applySub argSub type2Body
              bodySub <- unify type1Body' type2Body'
              return $ combine bodySub argSub
          (x, y) -> Left $ printf "Can't unify '%s' with '%s'" (show x) (show y)


-- Solving the constraints to get a substitution
-- 1. Iterate through the constraints
-- 2. Unify the key & value to get a substitution
-- 3. Merge this substitution into the rest, building up a final substitution
solve :: Constraints -> Substitution
solve (Constraints cs) = Map.foldlWithKey' f (Sub Map.empty) cs
    where
        f :: Substitution -> Type -> Type -> Substitution
        f final key val =
            let sub = orElse (unify key val)
            in  combine sub final


-- Full H-M type-checking
-- 1. Examine expression to discover constraints
-- 2. Solve the constraints to produce a substitution for all type vars
-- 3. Apply the substitution to the original type to yield the inferred type
hm :: Expr -> Type
hm expr =
    let CS ty constraints _ = cg expr
        finalSub = solve constraints
    in  applySub finalSub ty


orElse :: Show e => Either e a -> a
orElse e = either (error . show) id e


--------------------------------------------------------------------------------
-- TEST DATA / TESTS


tests :: Test
tests = test
    [ "term parsing" ~: test
          [ "lam f 5" ~: p "lam f 5" ~=? Lam "f" (Lit (Number 5))
          , "app f 4" ~: p "app f 4" ~=? App (Ident "f") (Lit (Number 4))
          , "true" ~: p "true" ~=? Lit (Bool True)
          , "cat" ~: p "cat" ~=? Ident "cat"
          , "5" ~: p "5" ~=? Lit (Number 5)
          , "(5)" ~: p "(5)" ~=? Lit (Number 5)
          ]
    , "type parsing" ~: test
          [ "add" ~: t "lam int (lam int int)"  ~=? TLam TInt (TLam TInt TInt)
          , "gt"  ~: t "lam int (lam int bool)" ~=? TLam TInt (TLam TInt TBool)
          , "if"  ~: t "lam bool (lam a (lam a a))" ~=?
                TLam TBool (TLam (TIdent "a") (TLam (TIdent "a") (TIdent "a")))
          , "fix" ~: t "lam (lam a a) a" ~=?
                TLam (TLam (TIdent "a") (TIdent "a")) (TIdent "a")
          ]
    , "constraint-generation" ~: test
          [ "lam x (app (app add 2) x)" ~: constraintTest ]
    , "constraint-substitution & combination" ~: test
          [ "combination" ~: combineTest
          ]
    , "unification" ~: test
          [ unifyTest1
          , unifyTest2
          , unifyTest3
          ]
    , "Hindley-Milner" ~: test
          [ "2 : int" ~: hm (p "2") ~=? t "int"
          , "true : bool" ~: hm (p "true") ~=? t "bool"
          , "lam x x : lam a a" ~: hm (p "lam x x") ~=? t "lam a0 a0"
          , "app (lam x x) 2 : int" ~: hm (p "app (lam x x) 2") ~=? t "int"
          , "app lam x (x) 2 : int" ~: hm (p "app lam x (x) 2") ~=? t "int"
          , "add" ~: hm (p "add") ~=? t "lam int (lam int int)"
          ]
    ]


constraintTest :: Test
constraintTest =
    let expr = p "lam x (app (app add 2) x)"
        expectedType = t "lam a0 a2"
        expectedConstraints = Constraints . Map.fromList $
            [ (t "a1", t "lam a0 a2")
            , (t "lam int (lam int int)", t "lam int a1")
            ]
        CS actualType actualConstraints _ = cg expr
    in  "type and constraints both match" ~: test
            [ assertBool
                  (show expectedType ++ " != " ++ show actualType)
                  (expectedType == actualType)
            , assertBool
                  (show expectedConstraints ++ " != " ++ show actualConstraints)
                  (expectedConstraints == actualConstraints)
            ]


combineTest :: Test
combineTest =
    let left = Sub . Map.fromList $
            [ (t "a", t "lam int c")
            , (t "b", t "int")
            ]
        right = Sub . Map.fromList $
            [ (t "d", t "lam a int")
            , (t "b", t "bool")
            ]
        expected = Sub . Map.fromList $
            [ (t "a", t "lam int c")
            , (t "b", t "bool")
            , (t "d", t "lam (lam int c) int")
            ]
        actual = combine left right
    in  test $ assertBool (show expected ++ " != " ++ show actual)
            (expected == actual)


unifyTest :: Eq a => String -> (Either String a) -> a -> Test
unifyTest msg expr expectation = test $ case expr of
    Left err -> assertFailure err
    Right x  -> assertBool msg (expectation == x)


unifyTest1 =
    let expected = Sub $ Map.fromList [(t "a", t "int")]
        actual = unify (t "a") (t "int")
    in  unifyTest "a / int" actual expected


unifyTest2 =
    let expected = Sub $ Map.fromList [(t "a", t "int"), (t "b", t "bool")]
        actual = unify (t "lam a b") (t "lam int bool")
    in  unifyTest "a -> b / int" actual expected


unifyTest3 :: Test
unifyTest3 = test $ case unify (t "int") (t "bool") of
    Left msg -> assertBool "Incorrect error" (msg == "Can't unify 'int' with 'bool'")
    Right _ -> assertFailure "Unification should have failed"


--------------------------------------------------------------------------------
-- MAIN


main :: IO ()
main = runTestTT tests >> return ()
