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
data Address = HEAP Int | CODE Int | REGISTER Int deriving (Eq, Show) 

data Term   = V Var | S Struct               deriving (Eq)
data RefTerm = RefV Var | RefS (Func, [Int]) deriving (Eq)
data Clause = Struct :- [Term]               deriving (Eq)
data Cmd = Assertion Clause | Query [Term]
data Cell = REF Address | STR Address | FUN Func | NULL deriving (Eq)

-- Heap has an array and its current index (H)
type Heap = ((Array Int Cell), Int)

data Mode = READ | WRITE deriving (Show, Eq)

-- The real heap, the code heap, the registers
data Db = Db { heap :: Heap
             , code :: Heap
             , regs :: Heap
             , mode :: Mode
             ,    s :: Address
             } deriving (Show)

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

getHeap :: Address -> Int -> Heap
getHeap addr size =
    let arr      = array (1, size) (map (\x -> (x, REF addr)) [1..size])
        (ads, _) = foldl helper ([], addr) [1..size]
    in  (arr // ads, 1)
    where helper (ar, ad) i = ((i, REF ad):ar, incrAddr ad)

getDb :: Db
getDb = Db { heap = (getHeap (HEAP 1) 10)
           , code = (getHeap (CODE 1) 10)
           , regs = (getHeap (REGISTER 1) 10)
           , mode = WRITE
           ,    s = (CODE 1) }

getCell :: Db -> Address -> Cell
getCell db (HEAP idx)     = (fst $ heap db) ! idx
getCell db (CODE idx)     = (fst $ code db) ! idx
getCell db (REGISTER idx) = (fst $ regs db) ! idx

putCell :: Db -> Address -> Cell -> Db
putCell db@(Db {heap=(h', h)}) (HEAP i) cell     = db {heap=(h' // [(i, cell)], h)} 
putCell db@(Db {code=(h', h)}) (CODE i) cell     = db {code=(h' // [(i, cell)], h)} 
putCell db@(Db {regs=(h', h)}) (REGISTER i) cell = db {regs=(h' // [(i, cell)], h)} 

cellAddr :: Cell -> Address
cellAddr (REF x) = x
cellAddr (STR x) = x
cellAddr _       = (HEAP 0) -- This kinda makes no sense

incrAddr :: Address -> Address
incrAddr (HEAP i)     = HEAP (i+1)
incrAddr (CODE i)     = CODE (i+1)
incrAddr (REGISTER i) = REGISTER (i+1)

-- Put a term into the registers 
termToCodeArea :: Db -> Term -> Db
termToCodeArea db term =
        fst $ foldl compileRefTerm (db, []) (flattenProgramTerm term)

-- DO all you can, and more. Strive for five, baby.
compileRefTerm :: (Db, [Int]) -> RefTerm -> (Db, [Int])
compileRefTerm (db, idxs) (RefS (f, is)) =
    let db' = getStructure db f
    in  foldl unifyVarVal (db, idxs) is
    
compileRefTerm x _ = x

unifyVarVal :: (Db, [Int]) -> Int -> (Db, [Int])
unifyVarVal (db, idxs) idx | elem idx idxs = (unifyValue db idx, idxs)
                           | otherwise     = (unifyVariable db idx, idx:idxs)
                           
unifyValue :: Db -> Int -> Db
unifyValue db@(Db {mode=READ}) i        = unify db (REGISTER i) (s db)
unifyValue db@(Db {code=code', s=s'}) i = 
    let code'' = pushOnHeap code' (REF (REGISTER i))
    in  db {code = code'', s = incrAddr s' }

unifyVariable :: Db -> Int -> Db
unifyVariable db@(Db {mode=READ, s=s}) i =
    let cell = getCell db s
        db'  = putCell db (REGISTER i) cell
    in  db' { s = (incrAddr s) }
    
unifyVariable db@(Db {code=code, s=s, regs=regs}) i =
    let h     = snd code
        db1   = db { code = pushOnHeap code (REF (CODE h)) }
        db2   = db { regs = pushOnHeap regs (REF (CODE h)) }
    in db2 { s = (incrAddr s) }

getStructure :: Db -> Func -> Db
getStructure db f = 
    getStructure' db f $ getCell db $ deref db (REGISTER (snd $ regs db))
    
getStructure' :: Db -> Func -> Cell -> Db
getStructure' db@(Db {code=code}) f (REF addr) =
    let code1 = pushOnHeap code  (STR (CODE (snd code)))
        code2 = pushOnHeap code1 (FUN f)
        -- We ought to bind here
    in  db {mode = WRITE, code = code2}

unify :: Db -> Address -> Address -> Db
unify db _ _ = db

pushOnHeap :: Heap -> Cell -> Heap
pushOnHeap (heap, idx) cell = (heap // [(idx, cell)], idx + 1)
    
-- Convert a list of RefTerms to Cells
--refsToCells :: [RefTerm] -> [Cell]
--refsToCells refs = map refToCell

deref :: Db -> Address -> Address
deref db adr | cellAddr cell /= adr  = deref db (cellAddr cell)
             | otherwise             = adr
             where cell = getCell db adr

-- putStructure :: Heap -> Func -> (Heap, Int)
-- putStructure (heap, h) fnc = ((heap//[(h, STR (h+1)), (h+1, (FUN fnc))], h+2), h)
-- 
-- setVariable :: Heap -> (Heap, Int)
-- setVariable (heap, h) = (((heap // [(h, REF h)]), h+1), h)
-- 
-- setValue :: Heap -> Cell -> Heap
-- setValue (heap, h) val = (heap // [(h, val)], h+1)


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
       