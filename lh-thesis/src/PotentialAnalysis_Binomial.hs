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

-- potential as length of list
{-@ measure pot @-}
{-@ pot :: xs:[a] -> {v: Nat | v = (len xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

-- potential as nodes
{-@ reflect potn @-}
{-@ potn :: xs:[BiTree a] -> {v: Nat | v = treeListSize xs} @-}
potn :: [BiTree a] -> Int
potn [] = 0
potn (x:xs) = treeSize x + potn xs

-- potential of tuple as nodes
{-@ reflect pottn @-}
pottn :: (BiTree a, [BiTree a]) -> Int
pottn (x,xs) = treeSize x + potn xs

-- potential of tuple
{-@ measure pott @-}
{-@ pott :: (a,[a]) -> Int @-}
pott :: (a,[a]) -> Int
pott (x,xs) = pot xs + 1

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
{-@ insTree :: BiTree a -> ts:[BiTree a] -> {ti:(Tick [BiTree a]) | tcost ti + pot (tval ti) - pot ts = 2 && len (tval ti) <= len ts + 1} @-}
insTree :: Ord a => BiTree a -> [BiTree a] -> Tick [BiTree a]
insTree t [] = RTick.step 1 (RTick.pure [t])
insTree t ts@(t':ts') 
    | rank t < rank t' = RTick.step 1 (RTick.return (t : ts))
    | rank t > rank t' = RTick.step (tcost (insTree t ts')) (RTick.return (t' : tval (insTree t ts'))) -- needed but never used if t is singleton
    | otherwise = RTick.step 1 (insTree (link t t') ts')

{-@ singleton :: a -> Tick (Heap a) @-}
singleton :: Ord a => a -> Tick (Heap a)
singleton x = RTick.return (Heap [Node 0 x [] 1])

-- O(1)
{-@ insert :: a -> h:Heap a -> {ti:Tick (Heap a) | tcost ti + pot (unheap (tval ti)) - pot (unheap h) = 2 }  @-}
insert :: Ord a => a -> Heap a -> Tick (Heap a)
insert x (Heap ts) = RTick.step (tcost (insTree (Node 0 x [] 1) ts)) (RTick.return (Heap (tval (insTree
 (Node 0 x [] 1) ts))))

-- tcost ti + pot (tval ti) - (pot ts1 + pot ts2) <= log n
-- length of list is log n ==> log n = pot (tval ti)
-- POTN: potn (tval ti) <= potn ts1 + potn ts2
{-@ mergeTree :: ts1:[BiTree a] -> ts2:[BiTree a] -> {ti:Tick [BiTree a] | tcost ti + pot (tval ti) - (pot ts1 + pot ts2) <= len (tval ti) && pot (tval ti) == len (tval ti) && len (tval ti) <= len ts1 + len ts2} @-}
mergeTree :: Ord a => [BiTree a] -> [BiTree a] -> Tick [BiTree a]
mergeTree ts1 [] = RTick.return ts1
mergeTree [] ts2 = RTick.return ts2
mergeTree ts1@(t1:ts1') ts2@(t2:ts2')
    | rank t1 < rank t2 = RTick.step (1 + tcost (mergeTree ts1' ts2)) (RTick.return (t1 : tval (mergeTree ts1' ts2)))
    | rank t2 < rank t1 = RTick.step (1 + tcost (mergeTree ts1 ts2')) (RTick.return (t2 : tval (mergeTree ts1 ts2')))
    | otherwise = RTick.step 2 (RTick.pure (tval (insTree (link t1 t2) (tval (mergeTree ts1' ts2'))))) 
--  | otherwise = RTick.step (tcost insTree (link t1 t2) (tval (mergeTree ts1' ts2')))) (RTick.pure (tval (insTree (link t1 t2) (tval (mergeTree ts1' ts2'))))) 
    -- cheat in last step because we know that insTree is constant amortized time (otherwise it counts worst case time)

-- O(log n)
{-@ mergeHeap :: h1:Heap a -> h2:Heap a -> {ti:Tick (Heap a) | tcost ti +  pot (unheap (tval ti)) - (pot (unheap h1) + pot (unheap h2)) <= pot (unheap (tval ti))} @-}
mergeHeap :: Ord a => Heap a -> Heap a -> Tick (Heap a)
mergeHeap (Heap ts1) (Heap ts2) = RTick.step (tcost (mergeTree ts1 ts2)) (RTick.return (Heap (tval (mergeTree ts1 ts2))))

{-@ removeMinTree :: ts:NEList (BiTree a) -> {ti:Tick (BiTree a, [BiTree a]) | tcost ti + pott (tval ti) - pot ts <= pot ts && pott (tval ti) == pot ts} @-}
removeMinTree :: Ord a => [BiTree a] -> Tick (BiTree a, [BiTree a])
removeMinTree [t] = RTick.return (t,[])
removeMinTree (t:ts) =
    let (t', ts') = tval (removeMinTree ts) in
    if root t < root t' then RTick.step (1 + tcost (removeMinTree ts)) (RTick.pure (t, ts)) 
    else RTick.step (1 + tcost (removeMinTree ts)) (RTick.pure (t', t:ts'))

{-@ findMin :: h:NEHeap a -> {ti:Tick a | tcost ti <= pot (unheap h)} @-}
findMin :: Ord a => Heap a -> Tick a
findMin (Heap ts) = 
    let (t, _) = tval (removeMinTree ts) in RTick.step (tcost (removeMinTree ts)) (RTick.pure (root t))

-- O(log n)
-- tcost ti + pot (unheap (tval ti)) - pot (unheap h) <= pot (unheap h) + pot (unheap h)
-- pott (tval (removeMinTree ts)) == pot ts
-- potn (tval (mergeTree (reverse ts1) ts2)) <= potn (unheap h)
-- TODO correct tcost --> find out why potn does not work
--tcost ti <= pot (unheap h) && tcost ti - pot (unheap (tval ti)) - pot (unheap h) <= pot (unheap h) + pot (unheap h)
{-@ deleteMin :: h:NEHeap a -> {ti:Tick (Heap a) | tcost ti <= pot (unheap h)}@-}
deleteMin :: Ord a => Heap a -> Tick (Heap a)
deleteMin (Heap ts) = let (Node _ x ts1 _, ts2) = tval (removeMinTree ts) in
   RTick.step (pott (tval (removeMinTree ts))) (RTick.pure (Heap (tval (mergeTree (reverse ts1) ts2))))

{-
for deleteMin we must work with potn because ts1 can make our list longer but the number of nodes is the same
-}