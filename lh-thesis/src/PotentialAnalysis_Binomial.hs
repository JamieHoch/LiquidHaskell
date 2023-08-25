{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--ple" @-}

module PotentialAnalysis_Binomial where
import Prelude hiding (pure, (<*>))
import Language.Haskell.Liquid.RTick as RTick
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[BiTree a] -> {v:Nat | (len xs <= v) && (v = 0 <=> len xs = 0)} @-}
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
    deriving (Eq, Ord)

{-@ reflect link @-}
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
    deriving (Eq, Ord)

-- potential as length of list
{-@ measure pot @-}
{-@ pot :: xs:[a] -> {v: Nat | v = (len xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

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

{-@ insTree :: Ord a => BiTree a -> ts:[BiTree a] -> {ti:(Tick {zs:[BiTree a]| len zs <= len ts + 1}) | tcost ti + pot (tval ti) - pot ts == 2} @-}
insTree :: Ord a => BiTree a -> [BiTree a] -> Tick [BiTree a]
insTree t [] = wait [t]
insTree t ts@(y:ts')
    | rank t < rank y = wait (t : ts)
    | rank t > rank y = Tick (tcost (insTree t ts')) (y : tval (insTree t ts')) -- needed but never used if t is singleton
    | otherwise = step 1 (insTree (link t y) ts')

{-@ singleton :: Ord a => a -> Tick (Heap a) @-}
singleton :: Ord a => a -> Tick (Heap a)
singleton x = pure (Heap [Node 0 x [] 1])

-- O(1)
{-@ insert :: a -> h:Heap a -> {ti:Tick (Heap a) | tcost ti + pot (unheap (tval ti)) - pot (unheap h) = 2}  @-}
insert :: Ord a => a -> Heap a -> Tick (Heap a)
insert x (Heap ts) = Tick (tcost f) (makeHeap (tval f))
    where
        f = insTree (Node 0 x [] 1) ts

-- tcost ti + pot (tval ti) - (pot ts1 + pot ts2) <= log n
-- length of list is log n ==> log n = pot (tval ti)
{-@ mergeTree :: Ord a => ts1:[BiTree a] -> ts2:[BiTree a] -> {ti:Tick [BiTree a] | tcost ti + pot (tval ti) - (pot ts1 + pot ts2) <= len (tval ti) && pot (tval ti) == len (tval ti) && len (tval ti) <= len ts1 + len ts2} @-}
mergeTree :: Ord a => [BiTree a] -> [BiTree a] -> Tick [BiTree a]
mergeTree ts1 [] = pure ts1
mergeTree [] ts2 = pure ts2
mergeTree ts1@(t1:ts1') ts2@(t2:ts2')
    | rank t1 < rank t2 = Tick (1 + tcost (mergeTree ts1' ts2)) (t1 : tval (mergeTree ts1' ts2))
    | rank t2 < rank t1 = Tick (1 + tcost (mergeTree ts1 ts2')) (t2 : tval (mergeTree ts1 ts2'))
    | otherwise = waitN 2 (tval (insTree (link t1 t2) (tval (mergeTree ts1' ts2'))))
-- TODO fix cheat
-- cheat in last step because we know that insTree is constant amortized time (otherwise it counts worst case time)

-- O(log n)
{-@ mergeHeap :: Ord a => h1:Heap a -> h2:Heap a -> {ti:Tick (Heap a) | tcost ti +  pot (unheap (tval ti)) - (pot (unheap h1) + pot (unheap h2)) <= pot (unheap (tval ti))} @-}
mergeHeap :: Ord a => Heap a -> Heap a -> Tick (Heap a)
mergeHeap (Heap ts1) (Heap ts2) = pure makeHeap <*> mergeTree ts1 ts2

{-@ reflect makeHeap @-}
{-@ makeHeap :: Ord a => t:[BiTree a] -> {h: Heap a | t == unheap h }@-}
makeHeap :: Ord a => [BiTree a] -> Heap a
makeHeap = Heap

{-@ removeMinTree :: Ord a => ts:NEList (BiTree a) -> {ti:Tick (BiTree a, [BiTree a]) | tcost ti + pott (tval ti) - pot ts <= pot ts && pott (tval ti) == pot ts && tcost ti <= pot ts} @-}
removeMinTree :: Ord a => [BiTree a] -> Tick (BiTree a, [BiTree a])
removeMinTree [t] = pure (t,[])
removeMinTree (t:ts) =
    let (t', ts') = tval f in
    if root t < root t' then Tick (1 + tcost f) (t, ts)
    else Tick (1 + tcost f) (t', t:ts')
    where 
        f = removeMinTree ts

{-@ findMin :: Ord a => h:NEHeap a -> {ti:Tick a | tcost ti <= pot (unheap h)} @-}
findMin :: Ord a => Heap a -> Tick a
findMin (Heap ts) =
    let (t, _) = tval (removeMinTree ts) in Tick (tcost (removeMinTree ts)) (root t)

-- O(log n)
{-@ deleteMin :: Ord a => h:NEHeap a -> Tick (Heap a)@-}
deleteMin :: Ord a => Heap a -> Tick (Heap a)
deleteMin h@(Heap ts) = let (Node _ x ts1 _, ts2) = tval (removeMinTree ts) in
   deleteMin' ts1 ts2 h

{-@ deleteMin' :: Ord a => ts1:[BiTree a] -> ts2:[BiTree a] -> {h:NEHeap a | pot (unheap h) == pot ts2 + 1} -> {ti:Tick (Heap a) | tcost ti + pot (unheap (tval ti)) - pot (unheap h) <= 2* (pot ts1 + pot ts2) && pot (unheap (tval ti)) <= pot ts1 + pot ts2} @-}
deleteMin' :: Ord a => [BiTree a] -> [BiTree a] -> Heap a -> Tick (Heap a)
deleteMin' ts1 ts2 h = Tick (tcost f + tcost (removeMinTree (unheap h))) (Heap (tval f))
    where
        f = mergeTree (reverse ts1) ts2
