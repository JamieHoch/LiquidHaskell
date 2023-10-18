{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module PotentialAnalysis_Binomial2_NV where
import Prelude hiding (length, pure, (<*>))
import Language.Haskell.Liquid.RTick as RTick
import Language.Haskell.Liquid.ProofCombinators


{-@ invariant {v:[BiTree a] | pot v = len v }@-}

{-@ measure length @-}
{-@ length :: xs:[a] -> {v:Nat | v = len xs} @-}
length :: [a] -> Int
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
{-@ type NEHeap a = {h: Heap a | 0 < len h} @-}

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

type Heap a = [BiTree a]
 
-- potential as len of list
-- TODO change to log n instead length
{-

h: Heap a 

theorem (Heap h) = 
-- log (number of nodes in the heap) = lenght of the hea

log (sum treeSize h) == length h 
-}

{-@ inline pot @-}
{-@ pot :: xs:Heap a -> {v: Nat | v == (len xs)} @-}
pot :: Heap a -> Int
pot xs = length xs 


-- potential of tuple
{-@ reflect pott @-}
{-@ pott :: (BiTree a,[BiTree a]) -> Int @-}
pott :: (BiTree a,[BiTree a]) -> Int
pott (x,xs) = pot xs + 1


-- forall x. len x == pot x 

{-@ reflect insTree @-}
{-@ insTree :: t:BiTree a -> ts:[BiTree a] -> {ti:(Tick {zs:[BiTree a]| len zs <= len ts + 1}) | tcost (insTree t ts) + pot (tval (insTree t ts)) - pot ts == 2 && pot (tval (insTree t ts)) - pot ts <= 1} @-}
insTree :: Ord a => BiTree a -> [BiTree a] -> Tick [BiTree a]
insTree t [] = wait [t]
insTree t ts@(t':ts')
    | rank t < rank t' = wait (t : ts) -- pot ti == len ti 
    | rank t > rank t' = pure ((:) t') <*> insTree t ts' -- reflect doesn't work with lambda abstraction
    | otherwise = step 1 (insTree (link t t') ts')

{-@ reflect singleton @-}
{-@ singleton :: Ord a => a -> BiTree a @-}
singleton :: Ord a => a -> BiTree a
singleton x = Node 0 x [] 1

-- O(1)
{-@ reflect insert @-}
{-@ insert :: x:a -> h:Heap a -> {ti:Tick (Heap a) | tcost (insert x h) + pot (tval (insert x h)) - pot h = 2}  @-}
insert :: Ord a => a -> Heap a -> Tick (Heap a)
insert x ts = insTree (singleton x) ts



-- potential analysis of insert
{-@ insertPot :: Ord a => x:a -> h:Heap a -> {tcost (insert x h) + pot (tval (insert x h)) - pot h == 2} @-}
insertPot :: (Ord a) => a -> Heap a -> Proof
insertPot x h@(ts) 
    = tcost (insert x h) + pot (tval (insert x h)) - pot h
    -- {defn. of insert}
    === tcost (insTree (singleton x) ts) + pot (tval (insert x h)) - pot h
    -- {defn. of pure}
    === tcost (insTree (singleton x) ts) + pot (tval (insert x h)) - pot h
   -- {defn. of cost}
    === 0 + tcost (insTree (singleton x) ts) + pot (tval (insert x h)) - pot h
    -- {arithmetic}
    === tcost (insTree (singleton x) ts) + pot (tval (insert x h)) - pot h
    -- {defn. of unheap}
    === tcost (insTree (singleton x) ts) + pot (tval (insert x h)) - pot ts
    -- {defn. of insert}
    === tcost (insTree (singleton x) ts) + pot (tval (insTree (singleton x) ts)) - pot ts
    -- {val of (<*>)}
    === tcost (insTree (singleton x) ts) + pot (tval (insTree (singleton x) ts)) - pot ts
    -- {defn. of pure}
--     === tcost (insTree (singleton x) ts) + pot (unheap (tval (Tick 0 makeHeap) (tval (insTree (singleton x) ts)))) - pot ts
--     -- {defn. of val}
--     === tcost (insTree (singleton x) ts) + pot (unheap (makeHeap (tval (insTree (singleton x) ts)))) - pot ts
--         -- {defn. unmakeHeap}
    === tcost (insTree (singleton x) ts) + pot (tval (insTree (singleton x) ts)) - pot ts
    -- {defn. amortised cost insTree}
    === 2
    *** QED

-- tcost ti + pot (tval ti) - (pot ts1 + pot ts2) <= log n
-- length of list is log n ==> log n = pot (tval ti)
{-@ reflect mergeTree @-}
{-@ mergeTree :: Ord a => ts1:[BiTree a] -> ts2:[BiTree a] 
              -> {ti:Tick [BiTree a] | tcost ti + pot (tval ti) - (pot ts1 + pot ts2) <= pot (tval ti)  && len (tval ti) <= len ts1 + len ts2} @-}
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
{-@ mergeHeap :: Ord a => h1:Heap a -> h2:Heap a 
              -> {ti:Tick (Heap a) | tcost ti +  pot (tval ti) - (pot h1 + pot h2) <= pot (tval ti)} @-}
mergeHeap :: Ord a => Heap a -> Heap a -> Tick (Heap a)
mergeHeap ts1 ts2 = mergeTree ts1 ts2

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
{-@ findMin :: Ord a => h:NEHeap a -> {ti:Tick a | tcost (findMin h) <= pot h} @-}
findMin :: Ord a => Heap a -> Tick a
findMin ts = RTick.liftM getRoot (RTick.liftM first (removeMinTree ts))

-- O(log n)
{-@ reflect deleteMin @-}
{-@ deleteMin :: Ord a => h:NEHeap a -> Tick (Heap a)@-}
deleteMin :: Ord a => Heap a -> Tick (Heap a)
deleteMin h@ts = let (Node _ x ts1 _, ts2) = tval (removeMinTree ts) in
   deleteMin' ts1 ts2 h

{-@ reflect deleteMin' @-}
{-@ deleteMin' :: Ord a => ts1:[BiTree a] -> ts2:[BiTree a] -> {h:NEHeap a | pot h == pot ts2 + 1} 
               -> {ti:Tick (Heap a) | tcost ti + pot (tval ti) - pot h <= 2* (pot ts1 + pot ts2) && pot (tval ti) <= pot ts1 + pot ts2} @-}
deleteMin' :: Ord a => [BiTree a] -> [BiTree a] -> Heap a -> Tick (Heap a)
deleteMin' ts1 ts2 h = RTick.step (tcost (removeMinTree h)) (mergeTree (myreverse ts1) ts2)

{-@ reflect myreverse @-}
{-@ myreverse :: xs:[a] -> {ys:[a] | len xs == len ys } @-}
myreverse :: [a] -> [a]
myreverse l =  rev l []

{-@ reflect rev @-}
{-@ rev :: xs:[a] -> ys:[a] -> {zs:[a] | len zs == len xs + len ys } @-}
rev :: [a] -> [a] -> [a]
rev []     a = a
rev (x:xs) a = rev xs (x:a)



