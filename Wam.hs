module Main where
    
import Data.List
--import Data.Array.IO
import Data.Array.IArray

type Func   = (String, Int)
type Struct = (Func, [Term])
type Var    = String
type Const  = String

data Term   = V Var | C Const | S Struct deriving (Eq)
data Clause = Struct :- [Term]           deriving (Eq)

data Cmd = Assertion Clause | Query [Term]

data Cell = REF Int | STR Int | FUN Func | NULL

-- Heap has an array and its current index (H)
type Heap = ((Array Int Cell), Int)

instance Show Term where
    show (V v)  		 = v
    show (C c)       	 = c
    show (S ((f,a), ts)) = f ++ "/" ++ (show a) ++ "(" ++ (show ts) ++ ")"
    showList x       	 = showString (intercalate ", " (map show x))
    
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

compileQuery :: Heap -> Term -> Heap
compileQuery heap (V _) 			  = fst $ setVariable heap
compileQuery heap (C c)				  = fst $ putStructure heap (c, 0)
compileQuery heap (S ((n, a), terms)) = foldl (\h q -> compileQuery h q) heap' terms
										where (heap', _) = putStructure heap (n, a)

