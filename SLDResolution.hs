module Main where

import Data.List
import Array
import Text.ParserCombinators.Parsec
import qualified Data.Map as Map
import Data.Maybe
import Test.HUnit

infix  6 :-
infixl 6 @@
infixl 6 ->>

type Structure    = (String, [Term])
type Variable     = (String, Int)
type Constant     = String
type Db           = [Clause] --Map.Map String [Clause]
type Subst        = Variable -> Term
type Substitution = [Subst]

data Term         = V Variable | C Constant | S Structure deriving (Eq)
data Clause       = Structure :- [Term]                   deriving (Eq)          
data Cmd          = Assertion Clause | Query [Term]

instance Show Term where
    show (V (v, n))  = v++(show n)
    show (C c)       = c
    show (S (s, ts)) = s ++ "(" ++ (show ts) ++ ")"
    showList x       = showString (intercalate ", " (map show x))
    
instance Show Clause where
    show (s :- ts) = (show (S s)) ++ " :- " ++ (show ts)

assigning x = intercalate ", " (map (\((v,_),t) -> v ++ " = " ++ (show t)) x)

listing' :: Db -> String
listing' db    = intercalate "\n" (map show db)
listing        = putStrLn . listing'

varsIn :: Term -> [Variable]
varsIn (V v)       = [v]
varsIn (C c)       = []
varsIn (S (_, ts)) = concatMap varsIn ts

arity :: Term -> Int
arity (S (_, t)) = length t
arity _          = 0

depth :: Term -> Int
depth (S (_, t)) = 1 + maximum (map depth t)
depth _          = 1

-- UNIFICATION --
concatOrNothing :: Maybe [a] -> Maybe [a] -> Maybe [a]
concatOrNothing (Just x) (Just y) = Just (x ++ y)
concatOrNothing _ _               = Nothing

unify :: Term -> Term -> Maybe Substitution
unify (V v) y     = Just [(v ->> y)]
unify x (V v)     = Just [(v ->> x)]
unify (C c) (C d) = if c == d then Just [] else Nothing
unify (S (s, ts)) (S (s', ts')) 
                  | s == s'   = listUnify ts ts'
                  | otherwise = Nothing
unify _ _         = Nothing                 

listUnify :: [Term] -> [Term] -> Maybe Substitution
listUnify [] []         = Just []
listUnify (x:xs) (y:ys) = concatOrNothing cur (listUnify (map (sub cur) xs) (map (sub cur) ys))
                            where cur = unify x y
listUnify _ _           = Nothing

sub :: Maybe Substitution -> Term -> Term
sub Nothing x  = x
sub (Just s) x = sub' s x

-- Given [
--   \v -> if _ == v then _ else _,
--   ...
-- ]
-- so s is [Subst, Subst, Subst]
-- so foldl1 :: (a -> b -> a) -> [b] -> a
-- so foldl1 here :: (Term -> (Variable -> Term) -> Term) -> [(Variable -> Term)] -> Term
sub' :: Substitution -> Term -> Term
sub' s x = foldl (flip app) x s

(->>) :: Variable -> Term -> Subst
(v ->> t) v' = if v == v' then t else V v'

app :: Subst -> Term -> Term
app s (S (t, ts)) = (S (t, map (app s) ts))
app s (V v)       = s v
app s (C c)       = C c

(@@) :: Subst -> Subst -> Subst
(@@) s t = app s . t

-- PROOF SEARCH --

-- To prove goal,
-- 1. Try to unify goal with each clause hd:-tl in DB.
--      - If fail, next.
--      - If success, go to 2
-- 2. We have a Substitution s between goal and hd. Apply it to each term in tl.
-- 3. Now prove tl

-- Exmample runthrough
-- DB: lt(z, S(Y)). lt(s(X), s(Y)) :- lt(X, Y).
-- > proveGoal db (lt(s(z), Y))
--         > proveClause 

foldMaybe = foldMaybe' (Just [])
foldMaybe' = foldl concatOrNothing 

-- To prove a number of goals, we need to prove them all
proveGoals :: Db -> [Term] -> Maybe Substitution
proveGoals db goals = foldMaybe (map (proveGoal db) goals)

-- For each rule we can prove, we will get a Just Substitution
-- If there are no Just Substitutions, return Nothing
proveGoal :: Db -> Term -> Maybe Substitution
proveGoal db goal = listToMaybe (proveRules (renamed db) goal)

-- This returns a list of rules that prove the term given the db.
-- The empty list implies there are no rules in the db that prove it.
-- First proveRule each rule on the Term
-- then get back a Maybe (Substitution, [Term])
-- If Nothing, Nothing
-- If Just (s, ts), then proveGoals ts and use that substitution
proveRules :: Db -> Term -> [Substitution]
proveRules db term = mapMaybe (\(s, ts) -> (s ++) `fmap` proveGoals db ts) validRules
                     where validRules = mapMaybe (flip proveRule term) db

-- First unify term and hd as s
-- Then try to apply substitutions to tl
-- If any fails, Return Nothing
-- If all success, return Just (s, subbed tl)
proveRule :: Clause -> Term -> Maybe (Substitution, [Term])
proveRule (hd :- tl) term = (\x -> (x, map (sub' x) tl)) `fmap` unify term (S hd)

-- Given a db, hd :- tl, and a term t, prove t by 
-- unifying with hd, and apply the substitution to tl
-- then proveGoals on the subbed tail
proveClause :: Db -> Clause -> Term -> Maybe Substitution
proveClause db (hd :- tl) t = proveGoals db (map (sub s) tl) where s = unify (S hd) t

renamed :: Db -> Db
renamed db = map (\((h,hs) :- t) -> (h, renameVars hs) :- renameVars t ) db
            where renameVar (V (v, i))  = V (v, i+1 )
                  renameVar (S (s, ts)) = S (s, renameVars ts)
                  renameVar x           = x
                  renameVars ts         = map renameVar ts
                  
-- varsIn term :: [Variable]
-- assignedFrom :: [Variable] -> Substitution -> (Variable, Term)
-- proveGoal :: Db -> Term -> Maybe Substitution
-- fmap here :: (Substitution -> (Variable, Term)) -> Maybe Substitution -> Maybe [(Variable, Term)]
prove :: Db -> Term -> Maybe [(Variable, Term)]
prove db term = fmap (varsIn term `assignedFrom`) (proveGoal db term)

assignedFrom :: [Variable] -> Substitution -> [(Variable, Term)]
assignedFrom vs sb = map (\x -> (x, sub' sb (V x))) vs

-- PARSING --
e2m :: Either ParseError a -> Maybe a
e2m = either (\x -> Nothing) (\x -> Just x)

p :: String -> Maybe Term 
p  i = e2m (parse textTerm "" i)
p' i = (C "fail") `fromMaybe` p i

pc :: String -> Maybe Clause
pc i = e2m (parse textClause "" i)

pdb :: String -> Maybe Db
pdb  i = e2m (parse textDb "" i)
pdb' i = [] `fromMaybe` e2m (parse textDb "" i)

textDb = textClause `endBy` ((char '.') >> spaces)

textClause = try textFullClause <|> do { s <- textStruct; return (s :- []) }
textFullClause =
    do hd <- textStruct
       s  <- spaces >> string ":-" >> spaces
       tl <- textArgList
       return (hd :- tl)
textStruct =
    do functor <- textId
       args    <- between (char '(') (char ')') textArgList
       return (functor, args)
textStructure = do
    str <- textStruct
    return (S str)

textId = 
    do first <- oneOf ['a'..'z']
       rest  <- many numOrLetter
       return (first:rest)
textConst = do
    c <- textId
    return (C c)
       
numOrLetter = oneOf (['a'..'z']++['A'..'Z']++"_"++['0'..'9'])

textTerm = try textStructure <|> try textConst <|> try textVar

textArgList = (try trueString) <|> textTerm `sepBy` (spaces >> (char ',') >> spaces)
            where trueString = do { string "true"; return [] }


textVar =
    do first <- oneOf ['A'..'Z']
       rest  <- many numOrLetter <|> (string "")
       return (V (first:rest, 0))
       
failure = [(("FAIL",0), (C "fail"))]
ffmp db s = failure `fromMaybe` prove db (p' s)
testQuery desired db query = TestCase (assertEqual desired desired output)
                             where output = assigning (ffmp db query)

lt      = pdb' "lt(z, s(Y)). lt(s(X), s(Y)) :- lt(X, Y)."
plus    = pdb' "plus(z,z,z). plus(z, X, X). plus(s(X), Y, s(Z)) :- plus(X, Y, Z)."

tests = TestList [ (testQuery "Y = s(s(Y2))"            lt "lt(s(z), Y)")
                 , (testQuery "Y = z"                   lt "lt(Y, s(z))")
                 , (testQuery (assigning failure)       lt "lt(s(s(z)),s(z))")
                 -- plus tests
                 , (testQuery (assigning failure)       plus "plus(s(z), z)")
                 , (testQuery "X = z"                   plus "plus(z, X, z)")
                 , (testQuery "X = z, Y = z, Z = z"     plus "plus(X, Y, Z)")
                 , (testQuery "X = X0, Y = s(s(X0))"    plus "plus(s(s(s(z))), s(s(s(X))), s(s(s(s(Y)))))")
                 ]
