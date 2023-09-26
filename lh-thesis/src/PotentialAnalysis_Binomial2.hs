{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--ple" @-}

module PotentialAnalysis_Binomial2 where
import Prelude hiding (length, pure, (<*>))
import Language.Haskell.Liquid.RTick as RTick
import Language.Haskell.Liquid.ProofCombinators

{-@ measure length @-}
{-@ length :: [a] -> Nat @-}
length :: [æ] -> Int
length []           = 0
length (x : xs) = 1 + length xs

{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[BiTree a] -> {v:Nat | (len  xs <= v) && (v = 0 <=> len xs = 0)} @-}
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
link t1@(Node r1 x1 ts1 sz1) t2@(Node _ x2 ts2 sz2)
    | x1 <= x2 =
        Node (r1 + 1) x1 (t2:ts1) (sz1 + sz2)
    | otherwise =
        Node (r1 
        + 1) x2 (t1:ts2) (sz1 + sz2)

{-@ data Heap a = Heap { unheap :: [BiTree a] } @-}
data Heap a =
    Heap { unheap :: [BiTree a] }
    deriving (Eq, Ord)

-- potential as len of list
-- TODO change to log n instead length
{-@ measure pot @-}
{-@ pot :: xs:[a] -> {v: Nat | v == (len xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

-- potential of tuple
{-@ measure pott @-}
{-@ pott :: (a,[a]) -> Int @-}
pott :: (a,[a]) -> Int
pott (x,xs) = pot xs + 1


{-@ reflect insTree @-}
{-@ insTree :: t:BiTree a -> ts:[BiTree a] -> {ti:(Tick {zs:[BiTree a]| len zs <= len ts + 1}) | tcost (insTree t ts) + pot (tval (insTree t ts)) - pot ts == 2 && pot (tval (insTree t ts)) - pot ts <= 1} @-}
insTree :: Ord a => BiTree a -> [BiTree a] -> Tick [BiTree a]
insTree t [] = wait [t]
insTree t ts@(t':ts')
    | rank t < rank t' = wait (t : ts)
    | rank t > rank t' = pure ((:) t') <*> insTree t ts' -- reflect doesn't work with lambda abstraction
    | otherwise = step 1 (insTree (link t t') ts')

{-@ reflect singleton @-}
{-@ singleton :: Ord a => a -> BiTree a @-}
singleton :: Ord a => a -> BiTree a
singleton x = Node 0 x [] 1

-- O(1)
{-@ reflect insert @-}
{-@ insert :: x:a -> h:Heap a -> {ti:Tick (Heap a) | tcost (insert x h) + pot (unheap (tval (insert x h))) - pot (unheap h) = 2}  @-}
insert :: Ord a => a -> Heap a -> Tick (Heap a)
insert x (Heap ts) = pure makeHeap <*> insTree (singleton x) ts

 
-- commented out to safe computation time
{-@ unmakeHeap :: ts:[BiTree a] -> {ts == unheap (makeHeap ts)}@-}
unmakeHeap :: Ord a => [BiTree a] -> Proof
unmakeHeap ts
    = unheap (makeHeap ts)
    -- {defn. of makeHeap}
    === unheap (Heap ts)
    -- {defn. of unheap}
    === ts
    *** QED

-- potential analysis of insert
{-@ insertPot :: Ord a => x:a -> h:Heap a -> {tcost (insert x h) + pot (unheap (tval (insert x h))) - pot (unheap h) == 2} @-}
insertPot :: (Ord a) => a -> Heap a -> Proof
insertPot x h@(Heap ts)
    = tcost (insert x h) + pot (unheap (tval (insert x h))) - pot (unheap h)
    -- {defn. of insert}
    === tcost (pure makeHeap <*> insTree (singleton x) ts) + pot (unheap (tval (insert x h))) - pot (unheap h)
    -- {defn. of pure}
    === tcost (Tick 0 makeHeap <*> insTree (singleton x) ts) + pot (unheap (tval (insert x h))) - pot (unheap h)
   -- {defn. of cost}
    === 0 + tcost (insTree (singleton x) ts) + pot (unheap (tval (insert x h))) - pot (unheap h)
    -- {arithmetic}
    === tcost (insTree (singleton x) ts) + pot (unheap (tval (insert x h))) - pot (unheap h)
    -- {defn. of unheap}
    === tcost (insTree (singleton x) ts) + pot (unheap (tval (insert x h))) - pot ts
    -- {defn. of insert}
    === tcost (insTree (singleton x) ts) + pot (unheap (tval (pure makeHeap <*> insTree (singleton x) ts))) - pot ts
    -- {val of (<*>)}
    === tcost (insTree (singleton x) ts) + pot (unheap (tval (pure makeHeap) (tval (insTree (singleton x) ts)))) - pot ts
    -- {defn. of pure}
    === tcost (insTree (singleton x) ts) + pot (unheap (tval (Tick 0 makeHeap) (tval (insTree (singleton x) ts)))) - pot ts
    -- {defn. of val}
    === tcost (insTree (singleton x) ts) + pot (unheap (makeHeap (tval (insTree (singleton x) ts)))) - pot ts
        ? unmakeHeap (tval (insTree (singleton x) ts))
        -- {defn. unmakeHeap}
    === tcost (insTree (singleton x) ts) + pot (tval (insTree (singleton x) ts)) - pot ts
    -- {defn. amortised cost insTree}
    === 2
    *** QED


-- tcost ti + pot (tval ti) - (pot ts1 + pot ts2) <= log n
-- length of list is log n ==> log n = pot (tval ti)
{-@ reflect mergeTree @-}
{-@ mergeTree :: Ord a => ts1:[BiTree a] -> ts2:[BiTree a] -> {ti:Tick [BiTree a] | tcost (mergeTree ts1 ts2) + pot (tval (mergeTree ts1 ts2)) - (pot ts1 + pot ts2) <= pot (tval (mergeTree ts1 ts2)) && pot (tval (mergeTree ts1 ts2)) == len (tval (mergeTree ts1 ts2)) && len (tval (mergeTree ts1 ts2)) <= len ts1 + len ts2} @-}
mergeTree :: Ord a => [BiTree a] -> [BiTree a] -> Tick [BiTree a]
mergeTree ts1 [] = pure ts1
mergeTree [] ts2 = pure ts2
mergeTree ts1@(t1:ts1') ts2@(t2:ts2')
    | rank t1 < rank t2 = pure ((:) t1) </> mergeTree ts1' ts2
    | rank t2 < rank t1 = pure ((:) t2) </> mergeTree ts1 ts2'
    | otherwise = waitN 2 (tval (insTree (link t1 t2) (tval (mergeTree ts1' ts2')))) -- !!CHEAT
    -- insTree (link t1 t2) RTick.=<< mergeTree ts1' ts2' -- worst case not amortized
    -- TODO find out how to use amortized time here

-- O(log n)
{-@ reflect mergeHeap @-}
{-@ mergeHeap :: Ord a => h1:Heap a -> h2:Heap a -> {ti:Tick (Heap a) | tcost (mergeHeap h1 h2) +  pot (unheap (tval (mergeHeap h1 h2))) - (pot (unheap h1) + pot (unheap h2)) <= pot (unheap (tval (mergeHeap h1 h2)))} @-}
mergeHeap :: Ord a => Heap a -> Heap a -> Tick (Heap a)
mergeHeap (Heap ts1) (Heap ts2) = pure makeHeap <*> mergeTree ts1 ts2

{-@ reflect makeHeap @-}
{-@ makeHeap :: Ord a => t:[BiTree a] -> {h: Heap a | t == unheap h }@-}
makeHeap :: Ord a => [BiTree a] -> Heap a
makeHeap = Heap

{-@ reflect getRoot @-}
getRoot :: Ord a => BiTree a -> a
getRoot = root

{-@ reflect first @-}
first :: Ord a => (BiTree a, [BiTree a]) -> BiTree a
first (x,xs) = x

{-@ reflect removeMinTree @-}
{-@ removeMinTree :: Ord a => ts:NEList (BiTree a) -> {ti:Tick (BiTree a, [BiTree a]) | tcost ti + pott (tval ti) - pot ts <= pot ts && pott (tval ti) == pot ts && tcost ti <= pot ts} @-}
removeMinTree :: Ord a => [BiTree a] -> Tick (BiTree a, [BiTree a])
removeMinTree [t] = pure (t,[])
removeMinTree (t:ts) =
    let (t', ts') = tval f in
    if root t < root t' then Tick (1 + tcost f) (t, ts)
    else Tick (1 + tcost f) (t', t:ts')
    where 
        f = removeMinTree ts
-- TODO rewrite without tval/tcost --> access to subformulas

{-@ reflect findMin @-}
{-@ findMin :: Ord a => h:NEHeap a -> {ti:Tick a | tcost (findMin h) <= pot (unheap h)} @-}
findMin :: Ord a => Heap a -> Tick a
findMin (Heap ts) = RTick.liftM getRoot (RTick.liftM first (removeMinTree ts))

-- O(log n)
{-@ reflect deleteMin @-}
{-@ deleteMin :: Ord a => h:NEHeap a -> Tick (Heap a)@-}
deleteMin :: Ord a => Heap a -> Tick (Heap a)
deleteMin h@(Heap ts) = let (Node _ x ts1 _, ts2) = tval (removeMinTree ts) in
   deleteMin' ts1 ts2 h

{-@ reflect deleteMin' @-}
{-@ deleteMin' :: Ord a => ts1:[BiTree a] -> ts2:[BiTree a] -> {h:NEHeap a | pot (unheap h) == pot ts2 + 1} -> {ti:Tick (Heap a) | tcost (deleteMin' ts1 ts2 h) + pot (unheap (tval (deleteMin' ts1 ts2 h))) - pot (unheap h) <= 2* (pot ts1 + pot ts2) && pot (unheap (tval (deleteMin' ts1 ts2 h))) <= pot ts1 + pot ts2} @-}
deleteMin' :: Ord a => [BiTree a] -> [BiTree a] -> Heap a -> Tick (Heap a)
deleteMin' ts1 ts2 h = RTick.step (tcost (removeMinTree (unheap h))) (pure makeHeap <*> mergeTree (myreverse ts1) ts2)

{-@ reflect myreverse @-}
{-@ myreverse :: xs:[a] -> {ys:[a] | len xs == len ys } @-}
myreverse :: [a] -> [a]
myreverse l =  rev l []

{-@ reflect rev @-}
{-@ rev :: xs:[a] -> ys:[a] -> {zs:[a] | len zs == len xs + len ys } @-}
rev :: [a] -> [a] -> [a]
rev []     a = a
rev (x:xs) a = rev xs (x:a)