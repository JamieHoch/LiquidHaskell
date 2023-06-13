-- Automatically generate singleton types for data constructors
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module PotentialAnalysis_FibHeap where

import Language.Haskell.Liquid.RTick as RTick

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
            , numNodes :: Pos
            }
@-}
data FibHeap a = E | FH { minTree :: FibTree a
                        , trees :: [FibTree a] --wihout minTree
                        , numNodes :: Int
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

-- O(1)
{-@ makeHeap :: {t:Tick EFibHeap | tcost t == 1} @-}
makeHeap :: Tick (FibHeap a)
makeHeap = RTick.step 1 (RTick.pure E)

{-@ predicate Rmin T = root (minTree T) @-}
-- O(1)
{-@ singleton :: x:a -> {t:Tick {v: NEFibHeap | Rmin v == x && trees v = [] && subtrees (minTree v) = [] && rank (minTree v) = 1} | tcost t == 1} @-}
singleton :: a -> Tick (FibHeap a)
singleton x = RTick.step 1 (RTick.pure (FH (Node x 1 [] False) [] 1))

-- O(1)
{-@ link :: t1:FibTree a -> {t2:FibTree a | rank t1 == rank t2} -> {t:Tick ({v:FibTree a | rank v == 1 + (rank t1) && (root v == root t1 && root t1 <= root t2 || root v == root t2 && root t2 <= root t1)}) | tcost t == 1} @-}
link :: (Ord a) => FibTree a -> FibTree a -> Tick (FibTree a)
link t1@(Node x r c1 _) t2@(Node y _ c2 _)
    | x < y = RTick.step 1 (RTick.pure (Node x (r+1) (t2:c1) False))
    | otherwise = RTick.step 1 (RTick.pure (Node y (r+1) (t1:c2) False))

{-@ measure potHeap @-}
{-@ potHeap :: FibHeap a -> {v:Int | v == 1}@-}
potHeap :: FibHeap a -> Int
potHeap h = 1

-- O(1)
{-@ merge :: {h1:(FibHeap a) | potHeap h1 == 1} -> {t1:Tick (h2:NEFibHeap) | tcost t1 == 1} -> {t:Tick NEFibHeap | (potHeap h1) + (tcost t1)  >= tcost t} @-}
merge:: (Ord a) => FibHeap a -> Tick (FibHeap a) -> Tick (FibHeap a)
merge E h = RTick.step (potHeap E) h
merge h1@(FH minTr1 ts1 nodes1) h2@(Tick cost (FH minTr2 ts2 nodes2))
    | root minTr1 < root minTr2 = RTick.step (cost + 1) (RTick.pure (FH minTr1 (minTr2:ts2++ts1) (nodes1 + nodes2)))
    | otherwise = RTick.step (cost + 1) (RTick.pure (FH minTr2 (minTr1:ts1++ts2) (nodes1 + nodes2)))

-- O(1)
-- pot h + 1
{-@ insert :: h1:FibHeap a -> a -> {t:Tick NEFibHeap | (potHeap h1) + 1  >= tcost t}  @-}
insert :: (Ord a) => FibHeap a -> a -> Tick (FibHeap a)
insert h x = merge h (singleton x)

-- O(1)
{-@ findMin :: (Ord a) => {h:FibHeap a | potHeap h == 1} -> {t:Tick a | (potHeap h) >= tcost t} @-}
findMin :: (Ord a) => FibHeap a -> Tick a
findMin h = RTick.step 1 (RTick.pure (root (minTree h)))

-- geht t für ganze liste durch
{-@ meld :: xs:[FibTree a] -> FibTree a -> {ti:Tick ({t:[FibTree a] | len t > 0})| pot xs >= tcost ti} @-}
meld :: Ord a => [FibTree a] -> FibTree a -> Tick [FibTree a]
meld [] t = RTick.return [t]
meld (x:xs) t = if rank x == rank t then RTick.step 1 (meld xs (tval (link t x)))
                     else RTick.step 1 (RTick.pure (x: tval (meld xs t)))
-- O(log n)
-- ruft meld mit jedem element auf
{-@ consolidate :: {t:[FibTree a] | len t > 0} -> Tick ({t:[FibTree a] | len t > 0}) @-}
consolidate :: (Ord a) => [FibTree a] -> Tick [FibTree a]
consolidate [x] = RTick.return [x]
consolidate (t:ts) = meld (tval (consolidate ts)) t
{-
    consolidate mit foldl
    len v > 0 does not work because of  {-@ LIQUID "--reflection" @-} flag
    we need len v > 0 such that consolidate can be used in deleteMin
-}


{-@ measure pot @-}
{-@ pot :: xs:[a] ->  {v: Int | v = (len xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

{-@ measure acost @-}
{-@ acost :: xs:[a] ->  {v: Int | v = (len xs)} @-}
acost :: [a] -> Int
acost []     = 0
acost (x:xs) = 1 + (acost xs)


-- O(len list)
-- (pot ts) + acost >= (tcost t) + (pot t)
{-@ extractMin :: {ts:[FibTree a] | len ts > 0} -> {t:Tick (FibTree a, [FibTree a]) | (pot ts) >= (tcost t)} @-}
extractMin :: (Ord a) => [FibTree a] -> Tick (FibTree a, [FibTree a])
extractMin [t] = RTick.return (t, [])
extractMin (t:ts) =
    let (t', ts') = tval (extractMin ts) in
        if root t < root t' then RTick.step 1 (RTick.pure (t, ts))
        else RTick.step 1 (RTick.pure (t', t:ts'))

{-@ myextractmin :: (Ord a) => {h:NEFibHeap | numNodes h > 1 || (numNodes h == 1 && subtrees (minTree h) == [] && trees h == [])} -> FibHeap a @-}
myextractmin :: (Ord a) => FibHeap a -> FibHeap a
myextractmin (FH (Node x _ [] _) [] _) = E
myextractmin (FH (Node x _ subtr _) [] n) = FH (head subtr) subtr (n-1)
myextractmin (FH (Node x _ subtr _) ts n) = FH (head ts) (ts ++ subtr) (n-1)


-- O(log n)
{-@ deleteMin :: {h:NEFibHeap | numNodes h > 1 || (numNodes h == 1 && subtrees (minTree h) == [] && trees h == [])}  -> Tick (FibHeap a) @-}
deleteMin :: (Ord a) => FibHeap a -> Tick (FibHeap a)
deleteMin (FH (Node x _ [] _) [] _) = RTick.return E
deleteMin h@(FH minTr ts@(x:xs) n) = RTick.return (FH minTr' ts' (n-1)) where
    (minTr', ts') = tval (extractMin $ tval (consolidate (subtrees minTr ++ ts)))
deleteMin h@(FH minTr@(Node _ _ subtr@(x:xs) _) ts n) = RTick.return (FH minTr' ts' (n-1)) where
    (minTr', ts') = tval (extractMin $ tval (consolidate (subtr ++ ts)))

