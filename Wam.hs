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

-- The real heap, the code heap, the registers, along with
-- some more state that we need to keep.
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
    show (S ((f,a), ts)) = f ++ "(" ++ (intercalate ", " (map show ts)) ++ ")"

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
getDb = Db { heap = (getHeap (HEAP 0) 30)
           , code = (getHeap (CODE 0) 30)
           , regs = (getHeap (REGS 0) 30)
           , mode = WRITE
           ,    s = (CODE 0) }

-- Convenience accessors for dealing with databases
getCell :: Db -> Address -> Cell
getCell db (HEAP idx) = (fst $ heap db) ! idx
getCell db (CODE idx) = (fst $ code db) ! idx
getCell db (REGS idx) = (fst $ regs db) ! idx

-- puts a cell at an address
putCell :: Db -> Address -> Cell -> Db
--putCell _ a c | trace ("putCell " ++ show c ++ " into " ++ show a) False = undefined
putCell db@(Db {heap=(h', h)}) (HEAP i) cell = db {heap=(h' // [(i, cell)], h)} 
putCell db@(Db {code=(h', h)}) (CODE i) cell = db {code=(h' // [(i, cell)], h)} 
putCell db@(Db {regs=(h', h)}) (REGS i) cell = db {regs=(h' // [(i, cell)], h)} 

-- increments the index part of an address
incrAddr :: Address -> Address
incrAddr (HEAP i) = HEAP (i+1)
incrAddr (CODE i) = CODE (i+1)
incrAddr (REGS i) = REGS (i+1)

-- puts a cell on top of the heap
pushOnHeap :: Heap -> Cell -> Heap
--pushOnHeap h c | trace ("pushHeap: " ++ show c) False = undefined
pushOnHeap (heap, idx) cell = (heap // [(idx, cell)], idx + 1)




-- ---------------------- --
-- QUERY TERM COMPILATION --
-- ---------------------- --

compileQueryTerm :: Db -> Term -> Db
compileQueryTerm db = fst . compileQueryRefs (db, []) . reorder . flattenTerm

-- reorders a list of refterms so that everything is in the list
-- before it's referenced. also removes references to variables (RefVs).
reorder :: [RefTerm] -> [(Int, RefTerm)]
reorder ts = filter (isRefS . snd) $ fixOrder $ zip [0..] ts

isRefS :: RefTerm -> Bool
isRefS (RefS _) = True
isRefS (RefV _) = False

-- takes a list of indexes and refterms and returns a 'fixed'
-- version where everything is in the list before it's referenced
fixOrder :: [(Int, RefTerm)] -> [(Int, RefTerm)]
fixOrder []                           = []
fixOrder (v@(_, RefV _) : ts)         = v : fixOrder ts
fixOrder (s@(_, RefS (_, idxs)) : ts) = (fixOrder front) ++ [s] ++ (fixOrder back)
                                      where (front, back) = pullToFront ts idxs
-- takes a list of indexes and refterms and returns a pair of lists.
-- the first pair has elements that are referenced somewhere in the
-- whole list, the second pair has elements that aren't.
pullToFront :: [(Int,RefTerm)] -> [Int] -> ([(Int,RefTerm)],[(Int,RefTerm)])
pullToFront x []    = ([],x)
pullToFront ts idxs = partition (\(x,_) -> elem x idxs) ts


-- takes a db and a correctly-ordered list of refterms (see above functions
-- for details about correct ordering) and does the actual compilation.
-- TODO: this should be spun out into a helper. outside functions shouldn't
-- have to deal with the list of ints at all.
compileQueryRefs :: (Db, [Int]) -> [(Int, RefTerm)] -> (Db, [Int])
--compileQueryRefs (db, i) _ | trace ("compileQueryRefs: " ++ show i ++ (take 1 (show db))) False = undefined
compileQueryRefs db []                 = db
compileQueryRefs db ((_, RefV _) : ts) = compileQueryRefs db ts
compileQueryRefs (db, is) ((i, RefS s@(f, args)) : ts) = 
    let db1 = putStructure db s (REGS i)
        db2 = foldl setVarVal (db1, i : is) args
    in compileQueryRefs db2 ts

-- does setVariable or setValue depending on if we've seen the ref before
setVarVal :: (Db, [Int]) -> Int -> (Db, [Int])
--setVarVal (_, i) j | trace ("setVarVal " ++ (show i) ++ ": " ++ show j) False = undefined
setVarVal (db, is) i | elem i is = (setValue db (getCell db (REGS i)), is)
                     | otherwise = (setVariable db (deref db (REGS i)), i : is)

-- compiles a query term variable into the heap
-- (when we've already seen it before and compiled it with setVariable)
-- defined on pg 14, fig 2.2
setValue :: Db -> Cell -> Db
--setValue db i | trace ("setValue " ++ (show i)) False = undefined
setValue db@(Db {code=code}) cell = db { code = pushOnHeap code cell }

-- compiles a query term variable into the heap
-- (when we haven't seen it before)
-- defined on pg 14, fig 2.2
setVariable :: Db -> Address -> Db
--setVariable db i | trace ("setVariable " ++ (show i)) False = undefined
setVariable db@(Db {code=code, regs=regs}) addr =
    let cell  = REF (CODE (snd code))
        code2 = pushOnHeap code cell
        db2 = putCell db addr cell
    in db2 { code = code2 }

-- compiles a query term structure into the heap
-- defined on pg 14, fig 2.2
putStructure :: Db -> (Func, [Int]) -> Address -> Db
--putStructure _ (f,_) _ | trace ("putStructure " ++ (show f)) False = undefined
putStructure db@(Db {code=code, regs=regs}) (f, args) addr =
    let h     = 1 + (snd code)
        code1 = pushOnHeap code  (STR (CODE h))
        code2 = pushOnHeap code1 (FUN f)
        db1   = putCell db addr (STR (CODE h))
    in  db1 { code = code2 }

-- So: (write mode)
--     unifyVariable:
--         (A) puts a self-referential REF when we encounter the g in f(g)
--         (B) puts a ref to that self-ref into the register
--     then getStructure:
--         makes a new str (C) and fun at top of CODE
--         encounters the REF (&A)
--         binds it to the str (&C)
--     thus, we end up with:
--         B points to A
--         A points to C
--         C is intact
-- What's not happening:
--     A is not being bound to point at C
--     Whereas, B is being bound
--     THUS, I suspect that deref isn't working
--     In fact, that is the case because we can see the bind call there is erroneous
--     That should be REF CODE 2 (&A)
--     But wait! The value at REGS 2 is (REF REGS 2) when it really should be (REF CODE 2)
--     So something before the deref call is erroneous, look:


-- ------------------------ --
-- PROGRAM TERM COMPILATION --
-- ------------------------ --

compileProgramTerm :: Db -> Term -> Db
compileProgramTerm db term =
    fst $ foldl compileRefTerm (db, []) (flattenTerm term)

-- does the actual compilation of a flattened term
-- TODO: this has some other responsibilities that it's not doing yet.. hmmm
compileRefTerm :: (Db, [Int]) -> RefTerm -> (Db, [Int])
compileRefTerm (db, idxs) (RefS (f, is)) =
    let db'  = getStructure db f (REGS (snd $ regs db))
    in foldl unifyVarVal (db', idxs) is
compileRefTerm (db@(Db {regs=(r,i)}), idxs) _ = (db {regs=(r,i+1)}, idxs)

-- picks unifyValue or unifyVariable depending on whether or not
-- we've already seen the variable
unifyVarVal :: (Db, [Int]) -> Int -> (Db, [Int])
unifyVarVal (db, idxs) idx | elem idx idxs = (unifyValue db idx, idxs)
                           | otherwise     = (unifyVariable db idx, idx:idxs)         

-- compiles a program term variable into the heap
-- (when we've already seen it and compiled it with unifyVariable)
-- defined on pg 18, fig 2.6
unifyValue :: Db -> Int -> Db
--unifyValue db@(Db {mode=m}) i | trace ("UNIFYVALUE: " ++ show (m,i)) False = undefined
unifyValue db@(Db {mode=READ, s=s}) i = unify db (REGS i) s
unifyValue db@(Db {code=code, s=s}) i = 
    let code' = pushOnHeap code $ getCell db (REGS i) -- (REF (CODE i))
    in  db { code = code', s = incrAddr s }

-- compiles a program term variable into the heap
-- (when we haven't seen it before)
-- defined on pg 18, fig 2.6
unifyVariable :: Db -> Int -> Db
--unifyVariable db@(Db {mode=m}) i | trace ("UNIFYVARIABLE: " ++ show (m, i)) False = undefined
unifyVariable db@(Db {mode=READ, s=s}) i =
    let cell = getCell db s
        db'  = putCell db (REGS i) cell
    in  db' { s = (incrAddr s) }
unifyVariable db@(Db {code=code, s=s, regs=regs}) i =
    let h   = snd code
        db2 = db { code = pushOnHeap code (REF (CODE h)), s = incrAddr s }
    in  putCell db2 (REGS i) (REF (CODE h))
        
-- compiles a program term structure into the heap
-- defined on pg 18, fig 2.6   
getStructure :: Db -> Func -> Address -> Db
--getStructure _ f addr | trace ("GETSTRUCTURE: " ++ show f ++ "\t" ++ show addr) False = undefined
getStructure db f addr = getStructure' db f $ getCell db $ deref db addr


-- helper for getStructure
getStructure' :: Db -> Func -> Cell -> Db
--getStructure' _ f c  | trace ("GETSTRUCTURE': " ++ show f ++ "\t" ++ show c) False = undefined
getStructure' db@(Db {code=code, regs=(r,i)}) f (REF addr) =
    let code1 = pushOnHeap code  (STR (CODE (1 + (snd code))))
        code2 = pushOnHeap code1 (FUN f)
        db1   = db {code=code2, mode = WRITE, regs=(r,i+1)}
    in  bind db1 addr (CODE (snd code))
getStructure' db@(Db {code=code}) f (STR addr) 
    -- | trace (show cell) False = undefined
    | isFun cell = db { s = incrAddr addr, mode = READ } 
    where cell = getCell db addr
    
    -- ^ we should set fail to be true here if things don't pattern match
    -- but we don't because we don't know what fail is in L0 (TODO)

-- finds the original address that's pointed to by an
-- address in the database
-- defined on pg 17, fig 2.5   
deref :: Db -> Address -> Address
deref db adr | isSelfRef db cell = adr
             | isRef cell        = deref db $ (\(REF x) -> x) cell
             | otherwise         = adr
             where cell = getCell db adr

-- some helpers for deref
isFun :: Cell -> Bool
isFun (FUN _) = True
isFun _       = False

isSelfRef :: Db -> Cell -> Bool
isSelfRef db (REF x) | (REF x) == getCell db x = True
isSelfRef _ _                                  = False

-- does 'bind' (TODO: expand on this explanation)
-- defined on pg 113
bind :: Db -> Address -> Address -> Db
--bind db a1 a2 | trace ("bind: " ++ show a1 ++ "\t" ++ show a2) False = undefined
bind db a1 a2 =
    let cell1 = getCell db a1
        cell2 = getCell db a2
    in bindHelper db (cell1, a1) (cell2, a2)

-- does the actual work of binding
bindHelper :: Db -> (Cell, Address) -> (Cell, Address) -> Db
--bindHelper _ x y
--    | trace ("bind: " ++ show x ++ "\t" ++ show y) False = undefined
bindHelper db (REF addr, a1) (cell2, a2)
    | (not $ isRef cell2) || (a2 `addrLt` a1) = 
        let db' = putCell db a1 cell2
        in  trail db' a1
    | otherwise =
        let db' = putCell db a2 (REF addr)
        in  trail db' a2
bindHelper db (cell, _) (_, a2) =
    let db' = putCell db a2 cell
    in  trail db' a2

-- helpers for bind/bindHelper
isRef :: Cell -> Bool
isRef (REF _) = True
isRef _       = False

-- does comparison of addresses. we can't just compare indexes
-- like is done in the book, because we have separate heaps instead of
-- one huge block of memory.
addrLt :: Address -> Address -> Bool
addrLt (CODE a) (CODE b)         = a < b
addrLt (CODE _) _                = True
addrLt (REGS a) (REGS b) = a < b
addrLt _ _                       = False

-- (this doesn't actually do anything right now, but might later if
-- we end up doing more of the WAM)
-- defined on pg 114
trail :: Db -> Address -> Db
--trail db _ | trace (show (regs db)) False = undefined
trail db _ = db

-- flattens a term into a list of refterms
flattenTerm :: Term -> [RefTerm]
flattenTerm t = elimDupes $ fixVars $ flattenHelper 0 [t]

flattenHelper :: Int -> [Term] -> [RefTerm]
flattenHelper _ [] = []
flattenHelper i (V v : ts) = RefV v : flattenHelper (i + 1) ts
flattenHelper i (S ((f,a), subs) : ts) = RefS ((f,a), range) : flattenHelper (i+1) (ts ++ subs)
    where range = [i + 1 + length ts .. i + length ts + length subs]

isRefV (RefV _) = True
isRefV _        = False

fixVars :: [RefTerm] -> [RefTerm]
fixVars ts = 
    let ts' = zip ts [0..]
        vs  = map (\(RefV v, i) -> (v, i)) $ filter (isRefV.fst) ts'
        vs' = sortBy (\x y -> compare (snd x) (snd y)) vs
    in straightenVars vs' ts

straightenVars :: [(Var, Int)] -> [RefTerm] -> [RefTerm]
straightenVars _ [] = []
straightenVars vs (RefV v : ts) = RefV v : straightenVars vs ts
straightenVars vs (RefS (f, ss) : ts) = RefS (f, map findLeast ss) : straightenVars vs ts
    where findLeast :: Int -> Int
          findLeast x = let v  = find ((x==).snd) vs
                            v' = v >>= (\y -> lookup (fst y) vs)
                        in  x `fromMaybe` v'

-- eliminates duplicates in a list of terms
elimDupes :: [RefTerm] -> [RefTerm]
elimDupes = nubBy sameVar
            where sameVar (RefV u) (RefV v) = u == v
                  sameVar _ _         = False

-- ----------- --
-- UNIFICATION --
-- ----------- --

unify :: Db -> Address -> Address -> Db
unify db a1 a2 = db `fromMaybe` unify' db [a2, a1] -- use list as a stack, TOS is head


-- What?

unify' :: Db -> [Address] -> Maybe Db
unify' _ as | trace ("unify': " ++ show as) False = undefined
unify' db (a1 : a2 : addrs) =
    let (d1, d2)      = (deref db a1, deref db a2)
        (db2, addrs') = unifyTags db d1 d2         -- <-- this does the bulk of the work
    in  db2 >>= (\x -> unify' x (addrs' ++ addrs)) -- <-- this is the while loop
unify' db _ = Just db
    
-- If the two addresses point to REFs, then bind the first to the second
-- Otherwise, they should be REFs that point to FUNs. If not, we're in trouble...
unifyTags :: Db -> Address -> Address -> (Maybe Db, [Address])
unifyTags _ _ _ | trace ("unifyTags") False = undefined
unifyTags db a1 a2 | a1 == a2  = (Just db, [])
                   | otherwise =
    let c1 = trace ("\tCell1: " ++ show (getCell db a1)) (getCell db a1)
        c2 = trace ("\tCell2: " ++ show (getCell db a2)) (getCell db a2)
    in if (isRef c1) || (isRef c2)
       then (Just (bind db a1 a2), [])
       else unifyFunctors db (c1, a1) (c2, a2)

-- Each cell should be a STR that points to a FUN.
unifyFunctors :: Db -> (Cell, Address) -> (Cell, Address) -> (Maybe Db, [Address])
unifyFunctors _ a b | trace ("unifyFunctors: " ++ show a ++ "\t" ++ show b) False = undefined
unifyFunctors db (STR a, aAddr) (STR b, bAddr) =
    let a' = trace ("\tCell1: " ++ show (getCell db a)) (getCell db a)
        b' = trace ("\tCell2: " ++ show (getCell db b)) (getCell db b)
    in if a' == b'
       then (Just db, takeCells db (incrAddr aAddr) (incrAddr bAddr))
       else (Nothing, [])

takeCells :: Db -> Address -> Address -> [Address]
takeCells _ a1 a2 | trace ("takeCells: " ++ show (a1, a2)) False = undefined
takeCells db a1 a2 =
    case traceShowRet (getCell db a1) of
        (FUN (_, arity)) -> traceShowRet $ takeCells' db arity (incrAddr a1) (incrAddr a2)
        _                -> []
    where takeCells' _  0 _ _ = []
          takeCells' db x a b = (b : a : takeCells' db (x-1) (incrAddr a) (incrAddr b))

traceShowRet x = traceShow x x

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

printCode x = putStrLn $ intercalate "\n" $ map (\(y,z)->(show y) ++ "\t" ++ (show z)) $ zip [0..] $ getCode x
printRegs x = putStrLn $ intercalate "\n" $ map (\(y,z)->(show y) ++ "\t" ++ (show z)) $ zip [0..] $ getRegs x

getCode = elems . fst . code
getRegs = elems . fst . regs

test     = getCode $ compileQueryTerm getDb testQuery
testRegs = getRegs $ compileQueryTerm getDb testQuery

testBoth = printCode $ compileQueryTerm (compileProgramTerm getDb testTerm2) testQuery
