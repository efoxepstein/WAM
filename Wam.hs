module Main where
    
import Data.Maybe
import Data.List
--import Data.Array.IO
import Data.Array.IArray
import Text.ParserCombinators.Parsec

type Func   = (String, Int)
type Struct = (Func, [Term])
type Var    = String

-- TODO: make right case
data Address = HEAP Int | CODE Int | REGISTER Int deriving (Eq) 

data Term   = V Var | S Struct               deriving (Eq)
data RefTerm = RefV Var | RefS (Func, [Int]) deriving (Eq)
data Clause = Struct :- [Term]               deriving (Eq)
data Cmd = Assertion Clause | Query [Term]
data Cell = REF Address | STR Address | FUN Func | NULL deriving (Eq)

-- Heap has an array and its current index (H)
type Heap = ((Array Int Cell), Int)

-- The real heap, the code heap, the registers
type Db = Db {heap :: Heap, code :: Heap, regs :: Heap}

instance Show Term where
    show (V v)           = v
    show (S ((f,a), [])) = f
    show (S ((f,a), ts)) = f ++ "(" ++ (show ts) ++ ")"
    showList x           = showString (intercalate ", " (map show x))

instance Show RefTerm where
    show (RefV v)           = v
    show (RefS ((f,a), [])) = f
    show (RefS ((f,a), ts)) = f ++ "(" ++ (intercalate ", " (map show ts)) ++ ")"
    
instance Show Clause where
    show (s :- ts) = (show (S s)) ++ " :- " ++ (show ts)

instance Show Cell where
    show (REF i) = "REF " ++ (show i)
    show (STR i) = "STR " ++ (show i)
    show (FUN f) = "FUN " ++ (show f)
    show NULL    = "NULL"

getHeap :: Int -> Heap
getHeap size = (array (1, size) (map (\x -> (x, REF x)) [1..size]), 1)

getDb :: Db
getStore = Db { heap = getHeap 512
              , code = getHeap 512
              , regs = getHeap 512 }

getCell :: Db -> Address -> Cell
getCell db (HEAP idx)     = (fst $ heap db) ! idx
getCell db (CODE idx)     = (fst $ code db) ! idx
getCell db (REGISTER idx) = (fst $ regs db) ! idx

cellAddr :: Cell -> Address
cellAddr (REF x) = x
cellAddr (STR x) = x
cellAddr _       = HEAP -1 -- This kinda makes no sense

-- Put a term into the registers 
termToCodeArea :: Db -> Term -> Store
termToCodeArea db term =
        foldl compileRefTerm (db, []) (flattenProgramTerm term)

-- DO all you can, and more. Strive for five, baby.
compileRefTerm :: (Db, [Int]) -> RefTerm -> (Db, [Int])
compileRefTerm (db, idxs) (RefS (f, is)) = (getStructure db f)
compileRefTerm x _                       = x

getStructure :: Db -> Func -> Db
getStructure db f = 
    getStructure' db f $ getCell db $ deref db (REGISTER (snd $ regs db))
    
getStructure' :: Db -> Func -> Cell -> Db
getStructure' db f cell =
    let
        code'  = pushOnHeap (code db)  (STR (i+1))
        code'' = pushOnHeap code' (FUN f)
        -- We ought to bind here
    in
        

pushOnHeap :: Heap -> Cell -> Heap
pushOnHeap (heap, idx) cell = (heap // [(idx, cell)], idx + 1)
    
-- Convert a list of RefTerms to Cells
refsToCells :: [RefTerm] -> [Cell]
refsToCells refs = map refToCell

deref :: Store -> Address -> Address
deref store adr@(loc, idx) | REF idx /= cell = deref store (loc, cellAddr cell)
                           | otherwise       = adr
                           where cell = getCell store adr

putStructure :: Heap -> Func -> (Heap, Int)
putStructure (heap, h) fnc = ((heap//[(h, STR (h+1)), (h+1, (FUN fnc))], h+2), h)

setVariable :: Heap -> (Heap, Int)
setVariable (heap, h) = (((heap // [(h, REF h)]), h+1), h)

setValue :: Heap -> Cell -> Heap
setValue (heap, h) val = (heap // [(h, val)], h+1)


-- We still need flattenQueryTerm

flattenProgramTerm :: Term -> [RefTerm]
flattenProgramTerm = referentiate . flattenTerm
    
referentiate :: [Term] -> [RefTerm]
referentiate ts = map (refTerm ts) ts

refTerm :: [Term] -> Term -> RefTerm
refTerm ts (V v) = RefV v
refTerm ts (S (f, subs)) = (RefS (f, mapMaybe (\x->elemIndex x ts) subs))

flattenTerm :: Term -> [Term]
flattenTerm t = elimDupes $ flattenHelper t

flattenHelper :: Term -> [Term]
flattenHelper v@(V _)             = [v]
flattenHelper s@(S (_, subterms)) = [s] ++ concatMap flattenHelper subterms

elimDupes :: [Term] -> [Term]
elimDupes = nubBy sameVar
            where sameVar (V u) (V v) = u == v
                  sameVar _ _         = False

------- PARSING --------
e2m :: Either ParseError a -> Maybe a
e2m = either (\x -> Nothing) (\x -> Just x)

p' :: String -> Maybe Term 
p' i = e2m (parse textTerm "" i)
p  i = (V "fail") `fromMaybe` p' i

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
       
testTerm = p"add(o, X, X)"
       