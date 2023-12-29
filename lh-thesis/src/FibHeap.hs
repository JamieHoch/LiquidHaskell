-- Automatically generate singleton types for data constructors
{-@ LIQUID "--exactdc" @-}

-- mergable heap
module FibHeap
    ( makeHeap
    , insert
    , findMin
    , extractMin
    , merge
    )
where

{-@ type Pos = {v:Int | 0 < v} @-}
{-@ type NEFibHeap = {v : FibHeap a | notEmptyFibHeap v} @-}
{-@ type EFibHeap = {v : FibHeap a | not (notEmptyFibHeap v)} @-}

{-@
data FibTree [rank] a =
    Node
        { rank :: Nat
        , root :: a
        , subtrees :: [FibTree a]
        , marked :: Bool
        }
@-}
data FibTree a =
    Node 
        { rank :: Int
        , root :: a
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

{-@ predicate Rmin H = root (minTree H) @-}

{-@ singleton :: x:a -> {v: NEFibHeap | Rmin v == x && trees v = []
        && subtrees (minTree v) = [] && rank (minTree v) = 1 }@-}
singleton :: a -> FibHeap a
singleton x = FH (Node 1 x [] False) []

{-@ link :: t1:FibTree a -> {t2:FibTree a | rank t1 == rank t2} 
        -> {v:FibTree a | rank v == 1 + (rank t1) 
        && (root v == root t1 && root t1 <= root t2 
        ||  root v == root t2 && root t2 <= root t1)} @-}
link :: (Ord a) => FibTree a -> FibTree a -> FibTree a
link t1@(Node r x ts1 _) t2@(Node _ y  ts2 _)
    | x < y = Node (r + 1) x (t2:ts1) False
    | otherwise = Node (r + 1) y (t1:ts2) False

{-@ merge :: h1:(FibHeap a) -> h2:NEFibHeap 
        -> {v:NEFibHeap | Rmin v == Rmin h1 && Rmin h1 < Rmin h2 
        || Rmin v == Rmin h2 && (Rmin h2 <= Rmin h1 || not notEmptyFibHeap h1)} @-}
merge:: (Ord a) => FibHeap a -> FibHeap a -> FibHeap a
merge E h = h
merge h1@(FH minTr1 ts1) h2@(FH minTr2 ts2)
    | root minTr1 < root minTr2 = FH minTr1 (minTr2:ts2++ts1)
    | otherwise = FH minTr2 (minTr1:ts1++ts2)
 
{-@ insert :: t:(FibHeap a) -> x:a 
        -> {v:NEFibHeap | Rmin v == Rmin t && Rmin t <= x || Rmin v == x 
        && (x <= Rmin t || not notEmptyFibHeap t)}  @-}
insert :: (Ord a) => FibHeap a -> a -> FibHeap a
insert h x = merge h (singleton x)

findMin :: (Ord a) => FibHeap a -> a
findMin = root . minTree

{-@ consolidate :: {t:[FibTree a] | len t > 0} -> {v:[FibTree a] | len v > 0} @-}
consolidate :: (Ord a) => [FibTree a] -> [FibTree a]
consolidate [x] = [x]
consolidate (x:xs) = foldl meld [x] xs where
    {-@ meld :: t:[FibTree a] -> FibTree a -> {v:[FibTree a] | len v > 0 && len v <= len t + 1} @-}
    meld :: Ord a => [FibTree a] -> FibTree a -> [FibTree a]
    meld [] x = [x]
    meld (x':xs) x
        | rank x == rank x' = meld xs (link x x')
        | otherwise = x:x':xs

{-@ extractMin :: {t:[FibTree a] | len t > 0} -> (FibTree a, [FibTree a]) @-}
extractMin :: (Ord a) => [FibTree a] -> (FibTree a, [FibTree a])
extractMin [t] = (t, [])
extractMin (t:ts)
    | root t < root t' = (t, ts)
    | otherwise = (t', t:ts')
    where (t', ts') = extractMin ts

{-@ deleteMin :: h:NEFibHeap -> v: FibHeap a @-}
deleteMin :: (Ord a) => FibHeap a -> FibHeap a
deleteMin (FH (Node _ x [] _) [] ) = E
deleteMin h@(FH minTr ts@(x:xs)) = FH minTr' ts' where
    (minTr', ts') = extractMin $ consolidate (subtrees minTr ++ ts)
deleteMin h@(FH minTr@(Node _ _ subtr@(x:xs) _) ts) = FH minTr' ts' where
    (minTr', ts') = extractMin $ consolidate (subtr ++ ts)


{-
 decreaseKey and delete does not make sense to implement
 in Haskell since there is no reference to an object. Hence
 we cannot delete it in constant time which is the purpose of 
 Fibonacci Heaps

 left out following functionalities:
    decreaseKey
    delete
-}