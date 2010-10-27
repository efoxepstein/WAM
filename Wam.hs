module Main where
    
import Data.List
import Data.Array.IO

type Func   = (String, Int)
type Struct = (Func, [Term])
type Var    = (String, Int)
type Const  = String

data Term   = V Var | C Const | S Struct deriving (Eq)
data Clause = Struct :- [Term]           deriving (Eq)

data Cmd = Assertion Clause | Query [Term]

data Cell = REF Int | STR Int | FUNCTOR Func

instance Show Term where
    show (V (v, n))  = v++(show n)
    show (C c)       = c
    show (S ((f,a), ts)) = f ++ "/" ++ (show a) ++ "(" ++ (show ts) ++ ")"
    showList x       = showString (intercalate ", " (map show x))
    
instance Show Clause where
    show (s :- ts) = (show (S s)) ++ " :- " ++ (show ts)


putStructure :: Heap -> Functor -> (Int, Heap)
-- putStructure heap functor = heap[H] <- STR H+1, heap[H+1] <- functor, H += 2, H-2

setVariable :: Heap -> (Int, Heap)
-- setVariable heap = heap[H] <- REF H, H++, H-1

setValue :: Heap -> Int -> Heap
-- setValue heap val = heap[H] <- val, H++        

main = do arr <- getArray
          a   <- readArray arr 1
          writeArray arr 1 5
          b   <- readArray arr 1
          print (a,b)