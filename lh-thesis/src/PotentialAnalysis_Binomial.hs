{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--ple" @-}

module PotentialAnalysis_Binomial where

import Language.Haskell.Liquid.RTick as RTick

{-@ reflect treeListSize @-}
{-@ treeListSize :: xs:[BiTree a] -> {v:Nat | (len xs <= v) && (v = 0 <=> len xs = 0)} @-}
--{-@ treeListSize :: xs:[BiTree a] -> Nat @-} -- TODO Nat is not possible with measure
treeListSize :: Ord a => [BiTree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = treeSize x + treeListSize xs

{-@ type Pos = {n:Int | n >= 1} @-}
{-@ type NEList a = {xs:[a] | 0 < len xs} @-}
{-@ type NEHeap a = {h: Heap a | 0 < len (unheap h)} @-}

{-@
data BiTree [rank] a =
    Node
        { rank :: Nat
        , root :: a
        , subtrees :: [BiTree a]
        , treeSize :: {v:Pos | v = 1 + treeListSize subtrees}
        }
@-}
data BiTree a =
    Node
        { rank :: Int
        , root :: a
        , subtrees :: [BiTree a]
        , treeSize :: Int
        }

{-@ link :: t1:BiTree a -> {t2:BiTree a | rank t2 = rank t1} -> {v:BiTree a | rank v = rank t1 + 1 && treeSize v = treeSize t1 + treeSize t2} @-}
link :: (Ord a) => BiTree a -> BiTree a -> BiTree a
link t1@(Node r1 x1 ts1 sz1) t2@(Node r2 x2 ts2 sz2)
    | x1 <= x2 =
        Node (r1 + 1) x1 (t2:ts1) (sz1 + sz2)
    | otherwise =
        Node (r2 + 1) x2 (t1:ts2) (sz1 + sz2)

{-@ data Heap a = Heap { unheap :: [BiTree a] } @-}
data Heap a = 
    Heap { unheap :: [BiTree a] }

{-@ measure pot @-}
{-@ pot :: xs:[a] -> {v: Nat | v = (len xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

{-
 insTree links trees with same rank
 We assume that the list is ordered by rank
 O(1)

tcost ti = k+1; 
num trees before:    pot ts = t; 
num trees after:     pot (tval ti) = t-k+1;
pot (tval ti) - pot ts = change in potential = 1-k
tcost ti + pot (tval ti) - pot ts = 2 
-}
{-@ insTree :: BiTree a -> ts:[BiTree a] -> {ti:(Tick [BiTree a]) | tcost ti + pot (tval ti) - pot ts = 2 } @-}
insTree :: Ord a => BiTree a -> [BiTree a] -> Tick [BiTree a]
insTree t [] = RTick.step 1 (RTick.pure [t])
insTree t ts@(t':ts') 
    | rank t < rank t' = RTick.step 1 (RTick.pure (t : ts))
    | rank t > rank t' = RTick.step (tcost (insTree t ts')) (RTick.pure (t' : tval (insTree t ts'))) -- needed but never used if t is singleton
    | otherwise = RTick.step 1 (insTree (link t t') ts')

{-@ singleton :: a -> Tick (Heap a) @-}
singleton :: Ord a => a -> Tick (Heap a)
singleton x = RTick.return (Heap [Node 0 x [] 1])

-- O(1)
{-@ insert :: a -> Heap a -> Tick (Heap a) @-}
insert :: Ord a => a -> Heap a -> Tick (Heap a)
insert x (Heap ts) = RTick.step (tcost (insTree (Node 0 x [] 1) ts)) (RTick.pure (Heap (tval (insTree
 (Node 0 x [] 1) ts))))

mergeTree :: Ord a => [BiTree a] -> [BiTree a] -> [BiTree a] -> Tick [BiTree a]
mergeTree s ts1 [] = RTick.return (s++ts1)
mergeTree s [] ts2 = RTick.return (s++ts2)
mergeTree s ts1@(t1:ts1') ts2@(t2:ts2')
    | rank t1 < rank t2 = RTick.step 1 (mergeTree (s++[t1]) ts1' ts2)
    | rank t2 < rank t1 = RTick.step 1 (mergeTree (s++[t2]) ts1 ts2')
    | otherwise = insTree (link t1 t2) (tval (mergeTree s ts1' ts2'))

-- O(log n)
mergeHeap :: Ord a => Heap a -> Heap a -> Tick (Heap a)
mergeHeap (Heap ts1) (Heap ts2) = RTick.step (tcost (mergeTree [] ts1 ts2)) (RTick.pure (Heap (tval (mergeTree [] ts1 ts2))))

{-@ removeMinTree :: NEList (BiTree a) -> Tick (BiTree a, [BiTree a]) @-}
removeMinTree :: Ord a => [BiTree a] -> Tick (BiTree a, [BiTree a])
removeMinTree [t] = RTick.return (t,[])
removeMinTree (t:ts) =
    let (t', ts') = tval (removeMinTree ts) in
    if root t < root t' then RTick.step 1 (RTick.pure (t, ts)) else RTick.step 1 (RTick.pure (t', t:ts'))

{-@ findMin :: NEHeap a -> Tick a @-}
findMin :: Ord a => Heap a -> Tick a
findMin (Heap ts) = 
    let (t, ts') = tval (removeMinTree ts) in RTick.return (root t)

-- O(log n)
{-@ deleteMin :: NEHeap a -> Tick (Heap a) @-}
deleteMin :: Ord a => Heap a -> Tick (Heap a)
deleteMin (Heap ts) = let (Node r x ts1 sz1, ts2) = tval (removeMinTree ts) in
   RTick.return (Heap (tval (mergeTree [] (reverse ts1) ts2)))
