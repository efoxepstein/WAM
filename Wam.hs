module Main where
    
import Data.Maybe
import Data.List
--import Data.Array.IO
import Data.Array.IArray
import Text.ParserCombinators.Parsec

type Func   = (String, Int)
type Struct = (Func, [Term])
type Var    = String

data Term   = V Var | S Struct               deriving (Eq)
data RefTerm = RefV Var | RefS (Func, [Int]) deriving (Eq)
data Clause = Struct :- [Term]               deriving (Eq)
data Cmd = Assertion Clause | Query [Term]
data Cell = REF Int | STR Int | FUN Func | NULL

-- Heap has an array and its current index (H)
type Heap = ((Array Int Cell), Int)

instance Show Term where
    show (V v)           = v
    show (S ((f,a), [])) = f ++ "/" ++ (show a)
    show (S ((f,a), ts)) = f ++ "/" ++ (show a) ++ "(" ++ (show ts) ++ ")"
    showList x           = showString (intercalate ", " (map show x))

instance Show RefTerm where
    show (RefV v)           = v
    show (RefS ((f,a), [])) = f ++ "/" ++ (show a)
    show (RefS ((f,a), ts)) = f ++ "/" ++ (show a) ++ "(" ++ (intercalate ", " (map show ts)) ++ ")"
    showList x           = showString (intercalate ", " (map show x))
    
instance Show Clause where
    show (s :- ts) = (show (S s)) ++ " :- " ++ (show ts)

instance Show Cell where
    show (REF i) = "REF " ++ (show i)
    show (STR i) = "STR " ++ (show i)
    show (FUN f) = "FUN " ++ (show f)
    show NULL    = "NULL"

getHeap :: Heap
getHeap = (array (1, 1024) (zip [1..1024] $ repeat NULL), 1)

putStructure :: Heap -> Func -> (Heap, Int)
putStructure (heap, h) fnc = ((heap//[(h, STR (h+1)), (h+1, (FUN fnc))], h+2), h)

setVariable :: Heap -> (Heap, Int)
setVariable (heap, h) = (((heap // [(h, REF h)]), h+1), h)

setValue :: Heap -> Cell -> Heap
setValue (heap, h) val = (heap // [(h, val)], h+1)

-- > referentiate $ p'"f(X, g(X, a), X)"
-- f/3(1, 2, 1), X, g/2(1, 3), a/0

referentiate :: Term -> [RefTerm]
referentiate t = map (refTerm flat) flat
                 where flat = flattenTerm t

refTerm :: [Term] -> Term -> RefTerm
refTerm ts (V v) = RefV v
refTerm ts (S (f, subs)) = (RefS (f, mapMaybe (\x->elemIndex x ts) subs))

flattenTerm :: Term -> [Term]
flattenTerm t = elimDupes $ flattenHelper t

flattenHelper :: Term -> [Term]
flattenHelper (V v)                    = [V v]
flattenHelper s@(S ((n, a), subterms)) = [s] ++ concatMap flattenHelper subterms

elimDupes :: [Term] -> [Term]
elimDupes terms = mapMaybe (\x -> elimDupe (init x) (last x)) (tail $ inits terms)

elimDupe :: [Term] -> Term -> Maybe Term
elimDupe terms v@(V _) | elemIndex v terms == Nothing = Just v
                       | otherwise                    = Nothing
elimDupe terms s = Just s



------- PARSING --------
e2m :: Either ParseError a -> Maybe a
e2m = either (\x -> Nothing) (\x -> Just x)

p :: String -> Maybe Term 
p  i = e2m (parse textTerm "" i)
p' i = (V "fail") `fromMaybe` p i

textTerm = try textStructure <|> try textVar <|> try textConst
textStructure = do
    str <- textStruct
    return (S str)
textStruct =
    do functor <- textId
       args    <- between (char '(') (char ')') textArgList
       return ((functor, length args), args)

textConst = do { first <- oneOf ['a'..'z']; rest <- many numOrLetter; return (S ((first:rest, 0), [])) }

textId = 
    do first <- oneOf ['a'..'z']
       rest  <- many numOrLetter
       return (first:rest)
       
numOrLetter = oneOf (['a'..'z']++['A'..'Z']++"_"++['0'..'9'])

textArgList = (try trueString) <|> textTerm `sepBy` (spaces >> (char ',') >> spaces)
            where trueString = do { string "true"; return [] }

textVar =
    do first <- oneOf ['A'..'Z']
       rest  <- many numOrLetter <|> (string "")
       return (V (first:rest))
       
testTerm = p'"f(X, g(X, a), X)"
       