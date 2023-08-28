-- Automatically generate singleton types for data constructors
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module PotentialAnalysis_FibHeap where
import Prelude hiding (pure, (++), (<*>))
import Language.Haskell.Liquid.RTick as RTick

{-@ type Pos = {v:Int | 0 < v} @-}
{-@ type NEFibHeap = {v : FibHeap a | notEmptyFibHeap v} @-}
{-@ type EFibHeap = {v : FibHeap a | not (notEmptyFibHeap v)} @-}

{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[FibTree a] -> {v:Nat | (len  xs <= v) && (v = 0 <=> len xs = 0)} @-}
treeListSize :: Ord a => [FibTree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = treeSize x + treeListSize xs

{-@
data FibTree [rank] a =
    Node
        { root :: a
        , rank :: Nat
        , subtrees :: [FibTree a]
        , marked :: Bool
        , treeSize :: {v:Pos | v = 1 + treeListSize subtrees}
        }
@-}
data FibTree a =
    Node
        { root :: a -- the element
        , rank :: Int -- size of the tree
        , subtrees :: [FibTree a]
        , marked :: Bool
        , treeSize :: Int
    }

{-@
data FibHeap a =
    E | FH {  minTree :: FibTree a
            , trees :: [FibTree a]
            , numNodes :: Pos
            , markedNodes :: Nat
            }
@-}
data FibHeap a = E | FH { minTree :: FibTree a
                        , trees :: [FibTree a] --wihout minTree
                        , numNodes :: Int
                        , markedNodes :: Int
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
{-@ makeHeap :: {t:Tick EFibHeap | tcost t == 0} @-}
makeHeap :: Tick (FibHeap a)
makeHeap = pure E

{-@ reflect log2 @-}
{-@ log2 :: n:Nat -> Nat / [n]@-}
log2 :: Int -> Int
log2 n
  | n <= 2   = 1
  | otherwise = 1 + log2 (div n 2)

{-@ predicate Rmin T = root (minTree T) @-}
-- O(1)
{-@ reflect singleton @-}
{-@ singleton :: x:a -> {ti:Tick NEFibHeap | tcost (singleton x) + poth (tval (singleton x)) - pota x = 1 && poth (tval ti) = 1} @-}
singleton :: a -> Tick (FibHeap a)
singleton x = wait (FH (Node x 1 [] False 1) [] 1 0)

-- O(1)
{-@ reflect link @-}
{-@ link :: t1:FibTree a -> {t2:FibTree a | rank t1 == rank t2} -> {t:Tick ({v:FibTree a | rank v == 1 + (rank t1) && (root v == root t1 && root t1 <= root t2 || root v == root t2 && root t2 <= root t1)}) | tcost t == 1} @-}
link :: (Ord a) => FibTree a -> FibTree a -> Tick (FibTree a)
link t1@(Node x r c1 _ sz1) t2@(Node y _ c2 _ sz2)
    | x < y = wait (Node x (r+1) (t2:c1) False (sz1 + sz2))
    | otherwise = wait (Node y (r+1) (t1:c2) False (sz1 + sz2))

{-@ measure poth @-}
{-@ poth :: h:FibHeap a -> {v:Nat | v == 0 && isEmptyFibHeap h || v == len (trees h) + 1 + 2*markedNodes h}@-}
poth :: FibHeap a -> Int
poth E = 0
poth h = pot (trees h) + 1 + 2*markedNodes h

{-@ reflect pot @-}
{-@ pot :: xs:[a] -> {v: Nat | v = (len xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

{-@ reflect pota @-}
{-@ pota :: a -> {v: Pos | v == 1} @-}
pota :: a -> Int
pota x = 1

{-@ reflect pott @-}
{-@ pott :: (a,[a]) -> Int @-}
pott :: (a,[a]) -> Int
pott (x,xs) = pota x + pot xs

-- potential as nodes
{-@ reflect potn @-}
{-@ potn :: h:FibHeap a -> Nat @-}
potn :: FibHeap a -> Int
potn E = 0
potn h = numNodes h


-- O(1)
{-@ reflect merge @-}
{-@ merge :: h1:(FibHeap a) -> h2:NEFibHeap-> {ti:Tick NEFibHeap | tcost ti == 1 && tcost (merge h1 h2) + poth (tval (merge h1 h2)) - (poth h1 + poth h2) == 1} @-}
merge:: (Ord a) => FibHeap a -> FibHeap a -> Tick (FibHeap a)
merge E h = wait h
merge h1@(FH minTr1 ts1 nodes1 mark1) h2@(FH minTr2 ts2 nodes2 mark2)
    | root minTr1 < root minTr2 = wait (FH minTr1 (minTr2:ts2++ts1) (nodes1 + nodes2) (mark1 + mark2))
    | otherwise = wait (FH minTr2 (minTr1:ts1++ts2) (nodes1 + nodes2) (mark1 + mark2))

-- O(1)
{-@ reflect insert @-}
{-@ insert :: h:FibHeap a -> x:a -> {ti:Tick NEFibHeap | tcost (insert h x) + poth (tval (insert h x)) - (poth h + pota x) == 1}  @-}
insert :: (Ord a) => FibHeap a -> a -> Tick (FibHeap a)
insert h x = merge h (tval (singleton x))

-- O(1)
{-@ reflect findMin @-}
{-@ findMin :: (Ord a) => h:NEFibHeap -> {ti:Tick a | tcost (findMin h) + pota (tval (findMin h)) - poth h <= 2} @-}
findMin :: (Ord a) => FibHeap a -> Tick a
findMin h = wait (root (minTree h))

-- geht t für ganze liste durch
-- O(log n)
{-@ reflect meld @-}
{-@ meld :: xs:[FibTree a] -> t:FibTree a -> {ti:Tick ({t:[FibTree a] | len t > 0})| tcost (meld xs t) + pot (tval (meld xs t)) - (pot xs) - pota t <= pot xs && pot (tval (meld xs t)) <= pot xs + 1} @-}
meld :: Ord a => [FibTree a] -> FibTree a -> Tick [FibTree a]
meld [] t = pure [t]
meld (x:xs) t = if rank x == rank t then step 1 (meld xs (tval (link t x)))
                     else pure ((:) x) <*> meld xs t
-- O(log n)
-- ruft meld mit jedem element auf
-- ACHTUNG! cheat weil kein pointer
{-@ reflect consolidate @-}
{-@ consolidate :: {xs:[FibTree a] | len xs > 0} -> {ti:Tick ({t:[FibTree a] | len t > 0}) | tcost (consolidate xs) + pot (tval (consolidate xs)) - pot xs <= pot xs && tcost (consolidate xs) <= pot xs && pot (tval (consolidate xs)) <= pot xs} @-}
consolidate :: (Ord a) => [FibTree a] -> Tick [FibTree a]
consolidate [x] = wait [x]
consolidate (x:xs) = Tick (1 + tcost (consolidate xs)) (tval (meld (tval (consolidate xs)) x))
--consolidate (x:xs) = RTick.wmap (help x) (consolidate xs)

{-@ reflect help @-}
{-@ help :: FibTree a -> [FibTree a] -> {t:[FibTree a] | len t > 0} @-}
help :: (Ord a) => FibTree a -> [FibTree a] -> [FibTree a]
help x c = tval (meld c x)
{-
    consolidate mit foldl
    len v > 0 does not work because of  {-@ LIQUID "--reflection" @-} flag
    we need len v > 0 such that consolidate can be used in deleteMin
-}

-- O(len list)
{-@ reflect extractMin @-}
{-@ extractMin :: {ts:[FibTree a] | len ts > 0} -> {ti:Tick (FibTree a, {ts':[FibTree a] | len ts' <= len ts - 1}) | tcost ti + pott (tval ti) - pot ts <= pott (tval ti) && pott (tval ti) <= pot ts && tcost ti <= pot ts } @-}
extractMin :: (Ord a) => [FibTree a] -> Tick (FibTree a, [FibTree a])
extractMin [t] = wait (t, [])
extractMin (t:ts) =
    let (t', ts') = tval f in
        if root t < root t' then Tick (1 + tcost f) (t, ts)
        else Tick (1 + tcost f) (t', t:ts')
    where
        f = extractMin ts

{-
{-@ myextractmin :: (Ord a) => {h:NEFibHeap | not (marked (minTree h)) &&  numNodes h > 1 || (numNodes h == 1 && subtrees (minTree h) == [] && trees h == [])} -> FibHeap a @-}
myextractmin :: (Ord a) => FibHeap a -> FibHeap a
myextractmin (FH (Node x _ [] _) [] _ _) = E
myextractmin (FH (Node x _ subtr _) [] n m) = FH (head subtr) subtr (n-1) m
myextractmin (FH (Node x _ subtr _) ts n m) = FH (head ts) (ts ++ subtr) (n-1) m
-}

-- O(log n)
{-@ deleteMin :: {h:NEFibHeap | not (marked (minTree h)) && numNodes h > 1 || (numNodes h == 1 && subtrees (minTree h) == [] && trees h == [])} -> ti:Tick (FibHeap a) @-}
deleteMin :: (Ord a) => FibHeap a -> Tick (FibHeap a)
deleteMin (FH (Node x _ [] _ _) [] _ _) = pure E
deleteMin h@(FH minTr ts n m) = let (minTr', ts') = tval (extractMin $ tval (consolidate (subtrees minTr ++ ts))) in
   deleteMin' h (minTr', ts')

{-
tcost ti <= pot (subtrees (minTree h)) + pot (trees h) &&
poth h <= pot (trees h) + 1 + 2*markedNodes h && 
poth (tval ti) <= pot ts' + 1 + 2*markedNodes h
-}
{-@ deleteMin' :: (Ord a) => {h:NEFibHeap | numNodes h > 1 && (len (subtrees (minTree h)) + len (trees h) > 0)} -> {k:(FibTree a,[FibTree a])| pott k <= pot (subtrees (minTree h)) + pot (trees h) }-> {ti:Tick (FibHeap a) | tcost ti + poth (tval ti) - poth h <= 2 * pot (subtrees (minTree h)) + pot (trees h)} @-}
deleteMin' :: (Ord a) => FibHeap a -> (FibTree a ,[FibTree a]) -> Tick (FibHeap a)
deleteMin' h@(FH minTr ts n m) (minTr', ts') = Tick (tcost (extractMin $ tval (consolidate (subtrees minTr ++ ts)))) (FH minTr' ts' (n-1) m)

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {zs:[a] | len zs == len xs + len ys && pot zs == pot xs + pot ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

-- returns Heap where v is replaced by k
-- replace :: Ord a => FibHeap a -> a -> a -> FibHeap a
-- replace h v k = FH (replace'' minTree h) (replace' (trees h) v k) (numNodes h) (markedNodes h)

{-@ replace' :: Ord a => ts:[FibTree a] -> a -> a -> [FibTree a] / [treeListSize ts] @-}
replace' :: Ord a => [FibTree a] -> a -> a -> [FibTree a]
replace' [] v k = []
replace' (t:ts) v k = (replace'' [t] v k) : replace' ts v k

{-@ replace'' :: Ord a => {ts:[FibTree a] | len ts == 1} -> a -> a -> FibTree a / [treeListSize ts]@-}
replace'' :: Ord a => [FibTree a] -> a -> a -> FibTree a
replace'' [Node x r ts mark sz] v k = if x == v then Node k r ts mark sz else Node k r ts mark sz --Node x r (replace' ts v k) mark sz

{-@ reflect listRank @-}
listRank [] = 0
listRank (t:ts) = rank t + listRank ts

{-
{-@ numNod :: Ord a => ts:[FibTree a] -> Int / [treeListSize ts] @-}
numNod :: Ord a => [FibTree a] -> Int
numNod [] = 0
numNod (t:ts) = numNod' t + numNod ts

numNod' :: Ord a => FibTree a -> Int
numNod' t = 1 + numNod (subtrees t)
-}

-- getParent :: Ord a => FibHeap a -> a -> [FibTree a]
-- getParent h k = 

-- getTree :: Ord a => FibHeap a -> a -> FibTree a
-- getTree h k =

-- getTree' [] k = 
-- getTree' (t:ts) k = 

-- performCuts :: Ord a => FibHeap a -> a -> FibHeap a
-- performCuts h k = if y != [] && k < key (fst y) then 
    -- cut x y
    -- cascading_cut y
        -- where y = getParent h k
            --   x = getTree h k

-- updateMin h k = if k < root (minTree h) then FH (getTree h k) (trees (deleteTree (trees h) k) ++ minTree h) (numNodes h) (markedNodes h)

deleteTree :: Ord a => [FibTree a] -> a -> [FibTree a]
deleteTree [] _ = []
deleteTree (t:ts) k = if root t == k then ts else t : deleteTree ts k

-- O(1) mit pointer
-- verringert den Schlüssel von Knoten v auf k
-- {-@ decreasekey :: Ord a => FibHeap a -> v:a -> {k:a | k < v} -> FibHeap a @-}
-- decreasekey :: Ord a => FibHeap a -> a -> a -> FibHeap a
-- decreasekey h v k = performCuts (replace h v k) k

-- entfernt Knoten v mit Eintrag aus Q (ohne v zu suchen)
-- delete :: Ord a => FibHeap a -> FibTree a -> FibHeap a
-- delete h v = 

