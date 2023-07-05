-- Automatically generate singleton types for data constructors
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module PotentialAnalysis_FibHeap where
import Prelude 
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
makeHeap = RTick.return E

{-@ reflect log2 @-}
{-@ log2 :: n:Nat -> Nat / [n]@-}
log2 :: Int -> Int
log2 n
  | n <= 2   = 1
  | otherwise = 1 + log2 (div n 2)

{-
{-@ div10 :: n:Pos -> {m:Nat | m < n} / [n]@-}
div10 :: Int -> Int
div10 n 
  | n < 10    = 0 
  | n == 10   = 1
  | otherwise = 1 + div10 (n-10)
-}

{-@ predicate Rmin T = root (minTree T) @-}
-- O(1)
{-@ singleton :: x:a -> {ti:Tick NEFibHeap | tcost ti == 1 && poth (tval ti) == 1} @-}
singleton :: a -> Tick (FibHeap a)
singleton x = RTick.step 1 (RTick.pure (FH (Node x 1 [] False) [] 1 0))

-- O(1)
{-@ link :: t1:FibTree a -> {t2:FibTree a | rank t1 == rank t2} -> {t:Tick ({v:FibTree a | rank v == 1 + (rank t1) && (root v == root t1 && root t1 <= root t2 || root v == root t2 && root t2 <= root t1)}) | tcost t == 1} @-}
link :: (Ord a) => FibTree a -> FibTree a -> Tick (FibTree a)
link t1@(Node x r c1 _) t2@(Node y _ c2 _)
    | x < y = RTick.step 1 (RTick.pure (Node x (r+1) (t2:c1) False))
    | otherwise = RTick.step 1 (RTick.pure (Node y (r+1) (t1:c2) False))

{-@ measure poth @-}
{-@ poth :: h:FibHeap a -> {v:Nat | v == 0 && isEmptyFibHeap h || v == len (trees h) + 1 + 2*markedNodes h}@-}
poth :: FibHeap a -> Int
poth E = 0
poth h = pot (trees h) + 1 + 2*markedNodes h

{-@ measure pot @-}
{-@ pot :: xs:[a] -> {v: Nat | v = (len xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

{-@ reflect pota @-}
{-@ pota :: a -> {v: Pos | v == 1} @-}
pota :: a -> Int
pota x = 1

-- O(1)
{-@ merge :: h1:(FibHeap a) -> h2:NEFibHeap-> {ti:Tick NEFibHeap | tcost ti == 1 && tcost ti + poth (tval ti) - (poth h1 + poth h2) == 1} @-}
merge:: (Ord a) => FibHeap a -> FibHeap a -> Tick (FibHeap a)
merge E h = RTick.step 1 (RTick.pure h)
merge h1@(FH minTr1 ts1 nodes1 mark1) h2@(FH minTr2 ts2 nodes2 mark2)
    | root minTr1 < root minTr2 = RTick.step 1 (RTick.pure (FH minTr1 (minTr2:ts2++ts1) (nodes1 + nodes2) (mark1 + mark2)))
    | otherwise = RTick.step 1 (RTick.pure (FH minTr2 (minTr1:ts1++ts2) (nodes1 + nodes2) (mark1 + mark2)))

-- O(1)
{-@ insert :: h:FibHeap a -> a -> {ti:Tick NEFibHeap | tcost ti + poth (tval ti) - (poth h + 1) == 1}  @-}
insert :: (Ord a) => FibHeap a -> a -> Tick (FibHeap a)
insert h x = merge h (tval (singleton x))

-- O(1)
{-@ findMin :: (Ord a) => h:NEFibHeap -> {ti:Tick a | tcost ti + pota (tval ti) - poth h <= 2} @-}
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


-- O(len list)
-- (pot ts) + acost >= (tcost t) + (pot t)
{-@ extractMin :: {ts:[FibTree a] | len ts > 0} -> {t:Tick (FibTree a, [FibTree a]) | (pot ts) >= (tcost t)} @-}
extractMin :: (Ord a) => [FibTree a] -> Tick (FibTree a, [FibTree a])
extractMin [t] = RTick.return (t, [])
extractMin (t:ts) =
    let (t', ts') = tval (extractMin ts) in
        if root t < root t' then RTick.step 1 (RTick.pure (t, ts))
        else RTick.step 1 (RTick.pure (t', t:ts'))

-- TODO check marked node m
{-@ myextractmin :: (Ord a) => {h:NEFibHeap | numNodes h > 1 || (numNodes h == 1 && subtrees (minTree h) == [] && trees h == [])} -> FibHeap a @-}
myextractmin :: (Ord a) => FibHeap a -> FibHeap a
myextractmin (FH (Node x _ [] _) [] _ _) = E
myextractmin (FH (Node x _ subtr _) [] n m) = FH (head subtr) subtr (n-1) m
myextractmin (FH (Node x _ subtr _) ts n m) = FH (head ts) (ts ++ subtr) (n-1) m


-- O(log n)
-- TODO check marked node m
{-@ deleteMin :: {h:NEFibHeap | numNodes h > 1 || (numNodes h == 1 && subtrees (minTree h) == [] && trees h == [])}  -> Tick (FibHeap a) @-}
deleteMin :: (Ord a) => FibHeap a -> Tick (FibHeap a)
deleteMin (FH (Node x _ [] _) [] _ _) = RTick.return E
deleteMin h@(FH minTr ts@(x:xs) n m) = RTick.return (FH minTr' ts' (n-1) m) where
    (minTr', ts') = tval (extractMin $ tval (consolidate (subtrees minTr ++ ts)))
deleteMin h@(FH minTr@(Node _ _ subtr@(x:xs) _) ts n m) = RTick.return (FH minTr' ts' (n-1) m) where
    (minTr', ts') = tval (extractMin $ tval (consolidate (subtr ++ ts)))

