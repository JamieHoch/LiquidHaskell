-- Automatically generate singleton types for data constructors
{-@ LIQUID "--exactdc" @-}
-- Disable ADTs (only used with exactDC)
{-@ LIQUID "--no-adt" @-}

module FibHeap
    (
        
    ) where
-- mergeable heap: makeHeap, insert, findMin, extractMin, union=merge
import Prelude

{-@ type Pos = {v:Int | 0 < v} @-}
{-@ type NEFibHeap = {v : FibHeap a | notEmptyFibHeap v} @-}
{-@ type EFibHeap = {v : FibHeap a | not (notEmptyFibHeap v)} @-}

{-@
data FibTree [rank] a =
    Node
        { root :: a
        , rank :: Nat
        , subtrees :: [FibTree a]
        , marked :: Bool
        }
@-}
data FibTree a =
    Node 
        { root :: a -- the element
        , rank :: Int -- size of the tree
        , subtrees :: [FibTree a]
        , marked :: Bool
    }

{-@
data FibHeap a =
    E | FH {  minTree :: FibTree a
            , trees :: [FibTree a]
            }
@-}
data FibHeap a = E | FH { minTree :: FibTree a
                        , trees :: [FibTree a] --wihout minTree
                     }


{-@ isMin ::  FibTree a -> [FibTree a] -> Bool @-}
isMin :: (Ord a) => FibTree a -> [FibTree a] -> Bool
isMin t [] = True
isMin t (t':ts) = root t <= root t' && isMin t ts

{-@ measure ranksum @-}
ranksum :: [FibTree a] -> Int
ranksum [] = 0
ranksum (t:ts) = rank t + ranksum ts

{-@ measure notEmptyFibHeap @-}
notEmptyFibHeap :: FibHeap a -> Bool
notEmptyFibHeap E = False
notEmptyFibHeap _ = True

{-@ measure isEmptyFibHeap @-}
{-@ isEmptyFibHeap :: t:(FibHeap a) -> {t':Bool | (not (notEmptyFibHeap t) && t') || (notEmptyFibHeap t && not t')} @-}
isEmptyFibHeap :: FibHeap a -> Bool 
isEmptyFibHeap E = True
isEmptyFibHeap _ = False

{-@ makeHeap :: EFibHeap @-}
makeHeap :: FibHeap a
makeHeap = E

{-@ singleton :: x:a -> {v: NEFibHeap | Rmin v == x && trees v = [] && subtrees (minTree v) = [] && rank (minTree v) = 1}@-}
singleton :: a -> FibHeap a
singleton x = FH (Node x 1 [] False) []

{-@ link :: t1:FibTree a -> {t2:FibTree a | rank t1 == rank t2} -> {v:FibTree a | rank v == 1 + (rank t1) && (root v == root t1 && root t1 <= root t2 || root v == root t2 && root t2 <= root t1)} @-}
link :: (Ord a) => FibTree a -> FibTree a -> FibTree a
link t1@(Node x r c1 _) t2@(Node y _ c2 _)
    | x < y = Node x (r+1) (t2:c1) False
    | otherwise = Node y (r+1) (t1:c2) False

{-@ predicate Rmin T = root (minTree T) @-}
-- constant time
{-@ merge :: t:(FibHeap a) -> t':NEFibHeap -> {v:NEFibHeap | Rmin v == Rmin t && Rmin t < Rmin t' || Rmin v == Rmin t' && (Rmin t' <= Rmin t || isEmptyFibHeap t)} @-}
merge:: (Ord a) => FibHeap a -> FibHeap a -> FibHeap a
merge E h = h
merge h1@(FH minTr1 ts1) h2@(FH minTr2 ts2)
    | root minTr1 < root minTr2 = FH minTr1 (minTr2:ts2++ts1)
    | otherwise = FH minTr2 (minTr1:ts1++ts2)

-- constant time  | Rmin v == Rmin t && Rmin t <= x || Rmin v == x && (x <= Rmin t || isEmptyFibHeap t)} 
{-@ insert :: t:(FibHeap a) -> x:a -> {v:NEFibHeap | Rmin v == Rmin t && Rmin t <= x || Rmin v == x && (x <= Rmin t || isEmptyFibHeap t)}  @-}
insert :: (Ord a) => FibHeap a -> a -> FibHeap a
insert h x = merge h (singleton x)

findMin :: (Ord a) => FibHeap a -> a
findMin = root . minTree

{-@ meld :: t:[FibTree a] -> FibTree a -> {v:[FibTree a] | len v > 0 && len v <= len t +1}@-}
meld :: Ord a => [FibTree a] -> FibTree a -> [FibTree a]
meld [] t = [t]
meld (t':ts) t = if rank t' == rank t then meld ts (link t t')
                     else t:t':ts

{-@ meld' :: {t:[FibTree a] | len t > 0} -> t':[FibTree a] -> {v:[FibTree a] | len v > 0 && len v <= len t + len t'} @-}
meld' :: Ord a => [FibTree a] -> [FibTree a] -> [FibTree a]
meld' (t:ts) [] = (t:ts)
meld' (t':ts') (t:ts) = if rank t' == rank t 
    then meld' (meld ts' (link t t')) ts 
    else meld' (t:t':ts') ts

{-@ consolidate :: {t:[FibTree a] | len t > 0} -> {t:[FibTree a] | len t > 0} @-}
consolidate :: (Ord a) => [FibTree a] -> [FibTree a]
consolidate (t:ts) = meld' [t] ts
   
{-@ extractMin :: {t:[FibTree a] | len t > 0} -> (FibTree a, [FibTree a]) @-}
extractMin :: (Ord a) => [FibTree a] -> (FibTree a, [FibTree a])
extractMin [t] = (t, [])
extractMin (t:ts) = 
    let (t', ts') = extractMin ts in
        if root t < root t' then (t, ts) else (t', t:ts')

-- Problem with (sz-1) -> need sz = rank minTr + ranksum trees -> Problem with merge

{-@ deleteMin :: h:NEFibHeap -> v: FibHeap a @-}
deleteMin :: (Ord a) => FibHeap a -> FibHeap a
deleteMin (FH (Node x _ [] _) [] ) = E
deleteMin h@(FH minTr ts@(x:xs)) = FH minTr' ts' where
    (minTr', ts') = extractMin $ consolidate (subtrees minTr ++ ts)
deleteMin h@(FH minTr@(Node _ _ subtr@(x:xs) _) ts) = FH minTr' ts' where
    (minTr', ts') = extractMin $ consolidate (subtr ++ ts)

fromList :: (Ord a) => [a] -> FibHeap a
fromList xs = foldl insert E xs

-- rank: binomial tree of rank r has 2^r nodes
-- size: number of nodes in fibheap
{-@ measure fibsize @-}
{-@ fibsize :: NEFibHeap -> Pos @-}
fibsize :: FibHeap a -> Int
fibsize (FH minTr ts) = size minTr + lsize ts

{-@ measure lsize @-}
{-@ lsize :: t:[FibTree a] -> {v:Int | v >= len t} @-}
lsize :: [FibTree a] -> Int
lsize [] = 0
lsize (t:ts) = size t + lsize ts

{-@ reflect pow2 @-}
{-@ pow2 :: Nat -> Pos @-}
pow2 :: Int -> Int
pow2 0 = 1
pow2 n = 2 * pow2 (n-1)

{-@ measure size @-}
{-@ size :: t:FibTree a -> {v:Pos| v == pow2 (rank t)} @-}
size :: FibTree a -> Int
size (Node _ r _ _) = pow2 r

{-
 decreaseKey and delete does not make sense to implement
 in Haskell since there is no reference to an object. Hence
 we cannot delete it in constant time which is the purpose of 
 Fibonacci Heaps

 left out following functionalities:
    decreaseKey
    delete
-}
