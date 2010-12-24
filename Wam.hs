module Main where
    
import Debug.Trace
import Data.Maybe
import Data.List
--import Data.Array.IO
import Data.Array.IArray
import Text.ParserCombinators.Parsec

-- A functor is a string and an arity. Technically, a functor is an identifier
-- with an arity, but for the sake of this Prolog implementation, there is no
-- strict need to use the type system to guarantee this.
type Func   = (String, Int)

-- A Struct is a functor with its arguments. The type system does not promise
-- that the number of arguments is the same as the arity.
type Struct = (Func, [Term])

-- A Variable is any string. Technically, it should be a capital letter, but this
-- is not enforced within the type system.
type Var    = String

-- An address is the index in either the HEAP, CODE, or REGS heaps
data Address = HEAP Int | CODE Int | REGS Int deriving (Eq, Show) 

-- A Term is a variable or a struct
data Term   = V Var | S Struct               deriving (Eq)

-- RefTerms are used in query compilation.
data RefTerm = RefV Var | RefS (Func, [Int]) deriving (Eq)

-- A Clause is a struct followed by the conjunction of many terms
data Clause = Struct :- [Term]               deriving (Eq)

-- Not used yet
data Cmd = Assertion Clause | Query [Term]

-- An entry on the heap is a REF, STR, or FUN
data Cell = REF Address | STR Address | FUN Func deriving (Eq)

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

-- Display things prettily
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
    
-- Returns a heap of a specific size defaulting to sequential addresses starting
-- with the one passed in    
getHeap :: Address -> Int -> Heap
getHeap addr size =
    let arr      = array (0, size-1) (map (\x -> (x, REF addr)) [0..size-1])
        (ads, _) = foldl helper ([], addr) [0..size-1]
    in  (arr // ads, 0)
    where helper (ar, ad) i = ((i, REF ad):ar, incrAddr ad)

-- Returns a new database
getDb :: Db
getDb = Db { heap = (getHeap (HEAP 0) 20)
           , code = (getHeap (CODE 0) 20)
           , regs = (getHeap (REGS 0) 20)
           , mode = WRITE
           ,    s = (CODE 0) }

-- Convenience accessors for dealing with databases
getCell :: Db -> Address -> Cell
getCell db (HEAP idx) = (fst $ heap db) ! idx
getCell db (CODE idx) = (fst $ code db) ! idx
getCell db (REGS idx) = (fst $ regs db) ! idx

putCell :: Db -> Address -> Cell -> Db
putCell db@(Db {heap=(h', h)}) (HEAP i) cell = db {heap=(h' // [(i, cell)], h)} 
putCell db@(Db {code=(h', h)}) (CODE i) cell = db {code=(h' // [(i, cell)], h)} 
putCell db@(Db {regs=(h', h)}) (REGS i) cell = db {regs=(h' // [(i, cell)], h)} 

cellAddr :: Cell -> Address
cellAddr (REF x) = x
cellAddr (STR x) = x
cellAddr _       = (HEAP 999999)

incrAddr :: Address -> Address
incrAddr (HEAP i) = HEAP (i+1)
incrAddr (CODE i) = CODE (i+1)
incrAddr (REGS i) = REGS (i+1)

pushOnHeap :: Heap -> Cell -> Heap
pushOnHeap (heap, idx) cell = (heap // [(idx, cell)], idx + 1)


compileQueryTerm :: Db -> Term -> Db
compileQueryTerm db = fst . compileQueryRefs (db, []) . reorder . flattenTerm

reorder :: [RefTerm] -> [(Int, RefTerm)]
reorder ts = filter (isRefS . snd ) $ fixOrder $ zip [0..] ts

isRefS :: RefTerm -> Bool
isRefS (RefS _) = True
isRefS (RefV _) = False

fixOrder :: [(Int, RefTerm)] -> [(Int, RefTerm)]
fixOrder []                           = []
fixOrder (v@(_, RefV _) : ts)         = v : fixOrder ts
fixOrder (s@(_, RefS (_, idxs)) : ts) = (fixOrder front) ++ [s] ++ (fixOrder back)
                                      where (front, back) = pullToFront ts idxs

pullToFront :: [(Int,RefTerm)] -> [Int] -> ([(Int,RefTerm)],[(Int,RefTerm)])
pullToFront x []    = ([],x)
pullToFront ts idxs = partition (\(x,_) -> elem x idxs) ts

compileQueryRefs :: (Db, [Int]) -> [(Int, RefTerm)] -> (Db, [Int])
--compileQueryRefs (db, i) _ | trace ("compileQueryRefs: " ++ show i ++ (take 1 (show db))) False = undefined
compileQueryRefs db []                 = db
compileQueryRefs db ((_, RefV _) : ts) = compileQueryRefs db ts
compileQueryRefs (db, is) ((i, RefS s@(f, args)) : ts) = 
    let db1 = putStructure db s (REGS i)
        db2 = foldl setVarVal (db1, i : is) args
    in compileQueryRefs db2 ts
    
setVarVal :: (Db, [Int]) -> Int -> (Db, [Int])
setVarVal (_, i) j | trace ("setVarVal " ++ (show i) ++ ": " ++ show j) False = undefined
setVarVal (db, is) i | elem i is = (setValue db (getCell db (REGS i)), is)
                     | otherwise = (setVariable db (deref db (REGS i)), i : is)
                     
setValue :: Db -> Cell -> Db
--setValue db i | trace ("setValue " ++ (show i)) False = undefined
setValue db@(Db {code=code}) cell = db { code = pushOnHeap code cell }

setVariable :: Db -> Address -> Db
--setVariable db i | trace ("setVariable " ++ (show i)) False = undefined
setVariable db@(Db {code=code, regs=regs}) addr =
    let cell  = REF (CODE (snd code))
        code2 = pushOnHeap code cell
        db2 = putCell db addr cell
    in db2 { code = code2 }


putStructure :: Db -> (Func, [Int]) -> Address -> Db
putStructure _ (f,_) _ | trace ("putStructure " ++ (show f)) False = undefined
putStructure db@(Db {code=code, regs=regs}) (f, args) addr =
    let h     = 1 + (snd code)
        code1 = pushOnHeap code  (STR (CODE h))
        code2 = pushOnHeap code1 (FUN f)
        db1   = putCell db addr (STR (CODE h))
    in  db1 { code = code2 }
        

compileProgramTerm :: Db -> Term -> Db
compileProgramTerm db term =
    fst $ foldl compileRefTerm (db, []) (flattenTerm term)

-- This has some other responsibilities that it's not doing yet
compileRefTerm :: (Db, [Int]) -> RefTerm -> (Db, [Int])
compileRefTerm (db, idxs) (RefS (f, is)) =
    let db'  = getStructure db f
    in foldl unifyVarVal (db', idxs) is
    
compileRefTerm x _ = x

unifyVarVal :: (Db, [Int]) -> Int -> (Db, [Int])
unifyVarVal (db, idxs) idx | elem idx idxs = (unifyValue db idx, idxs)
                           | otherwise     = (unifyVariable db idx, idx:idxs)         
                           
unifyValue :: Db -> Int -> Db
unifyValue _ _ | trace ("unifyValue") False = undefined
unifyValue db@(Db {mode=READ, s=s}) i = unify db (REGS i) s
unifyValue db@(Db {code=code, s=s}) i = 
    let code' = pushOnHeap code (REF (CODE i))
    in  db { code = code', s = incrAddr s }

unifyVariable :: Db -> Int -> Db
unifyVariable _ _ | trace ("unifyVariable") False = undefined
unifyVariable db@(Db {mode=READ, s=s}) i =
    let cell = getCell db s
        db'  = putCell db (REGS i) cell
    in  db' { s = (incrAddr s) }
    
unifyVariable db@(Db {code=code, s=s, regs=regs}) i =
    let h   = snd code
        db1 = db  { code = pushOnHeap code (REF (CODE h)) }
        db2 = db1 { regs = pushOnHeap regs (REF (CODE h)) }
    in db2 { s = (incrAddr s) }

getStructure :: Db -> Func -> Db
getStructure db f = getStructure' db f $ getCell db $ deref db (REGS (snd $ regs db))
    
getStructure' :: Db -> Func -> Cell -> Db
getStructure' _ _ _ | trace ("getStructure'") False = undefined
getStructure' db@(Db {code=code, regs=(r,i)}) f (REF addr) =
    let code1 = pushOnHeap code  (STR (CODE (1 + (snd code))))
        code2 = pushOnHeap code1 (FUN f)
        db1 = db  {mode = WRITE, code = code2}
        db2 = db1 {regs = (r,i+1) }
    in  bind db2 addr (CODE ((snd code2) - 2)) 
getStructure' db@(Db {code=code}) f (STR addr) 
    -- | trace (show cell) False = undefined
    | isFun cell = db { s = incrAddr addr, mode = READ } 
    where cell = getCell db addr
    
    -- ^ we should set fail to be true here if things don't pattern match
    -- but we don't because we don't know what fail is in L0

unify :: Db -> Address -> Address -> Db
unify db _ _ = db

deref :: Db -> Address -> Address
--deref db adr | trace ("deref\t" ++ show adr) False = undefined
deref db adr | isSelfRef db cell = adr
             | isRef cell        = deref db $ (\(REF x) -> x) cell
             | otherwise         = adr
             where cell = getCell db adr

isFun :: Cell -> Bool
isFun (FUN _) = True
isFun _       = False

isSelfRef :: Db -> Cell -> Bool
isSelfRef db (REF x) | (REF x) == getCell db x = True
isSelfRef _ _                                  = False

unRef :: Db -> Cell -> Address
unRef db (REF x) = x
             
bind :: Db -> Address -> Address -> Db
--bind db a1 a2 | trace (show a1 ++ "\n" ++ show a2) False = undefined
bind db a1 a2 =
    let cell1 = getCell db a1
        cell2 = getCell db a2
    in bindHelper db (cell1, a1) (cell2, a2)

isRef :: Cell -> Bool
isRef (REF _) = True
isRef _       = False

addrLt :: Address -> Address -> Bool
addrLt (CODE a) (CODE b)         = a < b
addrLt (CODE _) _                = True
addrLt (REGS a) (REGS b) = a < b
addrLt _ _                       = False

bindHelper :: Db -> (Cell, Address) -> (Cell, Address) -> Db
bindHelper db (REF addr, a1) (cell2, a2)
--    | trace (show addr ++ "\t" ++ show cell2) False = undefined
    | (not $ isRef cell2) || (a2 `addrLt` a1) = 
        let db' = putCell db a1 cell2
        in  trail db' a1
    | otherwise =
        let db' = putCell db a2 (REF addr)
        in  trail db' a2
bindHelper db (cell, _) (_, a2) =
    let db' = putCell db a2 cell
    in  trail db' a2
        
trail :: Db -> Address -> Db
--trail db _ | trace (show (regs db)) False = undefined
trail db _ = db

flattenTerm :: Term -> [RefTerm]
flattenTerm t = referentiate $ elimDupes $ flattenHelper [t]
    
referentiate :: [Term] -> [RefTerm]
referentiate ts = map (refTerm ts) ts

refTerm :: [Term] -> Term -> RefTerm
refTerm ts (V v)         = RefV v
refTerm ts (S (f, subs)) = RefS (f, mapMaybe (\x->elemIndex x ts) subs)

flattenHelper :: [Term] -> [Term]
flattenHelper []                        = []
flattenHelper (v@(V _) : q)             = v : flattenHelper q
flattenHelper (s@(S (_, subterms)) : q) = s : flattenHelper (q ++ subterms)

elimDupes :: [Term] -> [Term]
elimDupes = nubBy sameVar
            where sameVar (V u) (V v) = u == v
                  sameVar _ _         = False

------- PARSING --------
e2m :: Either ParseError a -> Maybe a
e2m = either (\_ -> Nothing) (\x -> Just x)

p' :: String -> Maybe Term 
p' i = e2m (parse textTerm "" i)
p  i = (V "fail") `fromMaybe` p' i

h :: String -> Clause
h i = ((("fail",0), []) :- []) `fromMaybe` (e2m $ parse textHorn "" i)

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
       
textHorn =
    do hed   <- textStruct
       sepr  <- spaces >> (string ":-") >> spaces
       tale  <- textStructure `sepBy` (spaces >> (char ',') >> spaces)
       return (hed :- tale)
       
testTerm = p "add(o, X, X)"
testTerm2 = p "p(f(X), h(Y, f(a)), Y)"
testQuery = p "p(Z, h(Z, W), f(W))"

getCode = elems . fst . code
getRegs = elems . fst . regs

test     = getCode $ compileQueryTerm getDb testQuery
testRegs = getRegs $ compileQueryTerm getDb testQuery
