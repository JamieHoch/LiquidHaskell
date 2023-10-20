{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--ple" @-}

module PotentialAnalysis_Binomial2 where
import Prelude hiding (length, pure, (<*>))
import Language.Haskell.Liquid.RTick as RTick
import Language.Haskell.Liquid.ProofCombinators
import GHC.Base (undefined)

{-@ measure length @-}
{-@ length :: xs:[a] -> {v:Nat | v = len xs} @-}
length :: [a] -> Int
length [] = 0
length (x : xs) = 1 + length xs

{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[BiTree a] 
        -> {v:Nat | (len  xs <= v) && (v = 0 <=> len xs = 0)} @-}
treeListSize :: Ord a => [BiTree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = treeSize x + treeListSize xs

{-@ type Pos = {n:Int | n >= 1} @-}
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
{-@ link :: t1:BiTree a -> {t2:BiTree a | rank t2 = rank t1} 
        -> {v:BiTree a | rank v = rank t1 + 1 && treeSize v = treeSize t1 + treeSize t2} @-}
link :: (Ord a) => BiTree a -> BiTree a -> BiTree a
link t1@(Node r1 x1 ts1 sz1) t2@(Node _ x2 ts2 sz2)
    | x1 <= x2 = Node (r1 + 1) x1 (t2:ts1) (sz1 + sz2)
    | otherwise = Node (r1 + 1) x2 (t1:ts2) (sz1 + sz2)

type Heap a = [BiTree a]
{-
data Heap a =
    Heap {
        list :: [BiTree]
        numNodes :: {v:Int | v + 1 == powerOfTwo (len list)}
    }
-- because otherwise 
-}

{-@ reflect log2 @-}
{-@ log2 :: n:Pos -> v:Nat / [n]@-}
log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 (div n 2)

{-@ reflect powerOfTwo @-}
{-@ powerOfTwo :: Nat -> Pos @-}
powerOfTwo :: Int -> Int
powerOfTwo 0 = 1
powerOfTwo n = 2 * (powerOfTwo (n - 1))

{-@ reflect numNodes @-}
{-@ numNodes :: h:Heap a -> {v:Nat | v == 0 <=> h == []} @-}
numNodes :: Heap a -> Int
numNodes [] = 0
numNodes [t] = treeSize t
numNodes (t:ts) = treeSize t + numNodes ts

{-@ reflect logPot @-}
logPot :: Heap a -> Int
logPot [] = 0
logPot ts = log2 (numNodes ts) 

{-@ prop :: h:Heap a -> {numNodes h + 1 == powerOfTwo (len h)} @-}
prop :: Heap a -> ()
prop [] = numNodes [] + 1 
    === powerOfTwo 0 ***QED
prop [t] = undefined -- numNodes [t] + 1 === treeSize t + 1 === 1 + treeListSize subtrees
prop ts = undefined
-- not possible to prove that because no knowledge about tree t


-- potential as len of list
-- TODO change to log n instead length
{-@ measure pot @-}
{-@ pot :: xs:[a] -> {v: Nat | v == (len xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

{-@ invariant {xs:[a] | pot xs == len xs } @-}
invariant = ()

-- potential of tuple
{-@ measure pott @-}
{-@ pott :: x:(a,[a]) -> {v:Int | v == (pot (snd x)) + 1} @-}
pott :: (a,[a]) -> Int
pott (x,xs) = pot xs + 1



-- amortized ti (pot (tval (insTree t ts))) (pot ts) == 2
-- tcost ti + pot (tval (insTree t ts)) - pot ts = 2
-- tcost ti = 2 + pot ts -  pot os  >= 2 + pot ts -  pot ts - 1 = 1

-- tcost ti >= 1 
-- 
--  pot os <= pot ts + 1
--  - pot os >= - pot ts - 1 
-- 
-- pot (tval (insTree t ts)) <= len ts + 1 
-- pot (tval (insTree t ts)) <= len ts + 1 

{-@ reflect insTree @-}
{-@ insTree :: t:BiTree a -> ts:[BiTree a] 
        -> {ti:(Tick {zs:[BiTree a]| len zs <= len ts + 1}) | amortized ti (pot (tval (insTree t ts))) (pot ts) == 2 && pot (tval (insTree t ts)) - pot ts <= 1 } @-}
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
{-@ insert :: x:a -> h:Heap a 
        -> {ti:Tick (Heap a) | tcost ti + pot (tval (insert x h)) - pot h = 2}  @-}
insert :: Ord a => a -> Heap a -> Tick (Heap a)
insert x ts = insTree (singleton x) ts


{-@ inline amortized @-}
amortized :: Tick a -> Int -> Int -> Int  
amortized cost out input = tcost cost + out - input

-- tcost ti + pot (tval ti) - (pot ts1 + pot ts2) <= log n
-- length of list is log n ==> log n = pot (tval ti)
-- O(log n)
{-@ reflect mergeHeap @-}
{-@ mergeHeap :: Ord a => ts1:[BiTree a] -> ts2:[BiTree a] 
        -> {ti:Tick {xs:[BiTree a] | len xs <= len ts1 + len ts2 && pot xs == len xs} | 
                    amortized ti (pot (tval (mergeHeap ts1 ts2))) (pot ts1 + pot ts2) <= pot (tval (mergeHeap ts1 ts2)) &&
                    pot (tval (mergeHeap ts1 ts2)) == len (tval (mergeHeap ts1 ts2)) &&
                    len (tval (mergeHeap ts1 ts2)) <= len ts1 + len ts2 } @-}
mergeHeap :: Ord a => [BiTree a] -> [BiTree a] -> Tick [BiTree a]
mergeHeap ts1 [] = pure ts1
mergeHeap [] ts2 = pure ts2
mergeHeap ts1@(t1:ts1') ts2@(t2:ts2')
    | rank t1 < rank t2 = pure ((:) t1) </> mergeHeap ts1' ts2
    | rank t2 < rank t1 = pure ((:) t2) </> mergeHeap ts1 ts2'
    | otherwise         = abind 2 (length ts1 + length ts2) (mergeHeap ts1' ts2') (insTree (link t1 t2)) 

-- THIS IS TRUSTED CODE ABOUT AMORTISED BIND 
{-@ reflect abind @-}
abind :: Int -> Int -> Tick [a] -> ([a] -> Tick [c]) -> Tick [c]
{-@ abind :: c:Nat -> m:Nat -> x:Tick ({v:[a] | len v <= m - 1}) -> f:(fx:[a] -> {t:Tick {xs:[c] | len xs <= len fx + 1} | amortized t (pot (tval t)) (pot fx) <= c})
                 -> {ti:Tick {xs:[c] | len xs <= m}  | (tcost ti == c + tcost x ) && tval (f (tval x)) == tval ti && pot (tval ti) == len (tval ti) && len (tval ti) <= m } @-}
abind c _ (Tick c1 x) f = Tick (c + c1) y
    where Tick _ y = f x
-- END TRUSTED 


{-@ reflect getRoot @-}
getRoot :: Ord a => BiTree a -> a
getRoot = root

{-@ reflect first @-}
first :: Ord a => (BiTree a, [BiTree a]) -> BiTree a
first (x,xs) = x

{-@ reflect removeMinTree @-}
{-@ removeMinTree :: Ord a => ts:NEHeap a
        -> {ti:Tick {v:(BiTree a, [BiTree a]) | pott v == pot ts} | tcost ti + pott (tval ti) - pot ts <= pot ts && tcost ti <= pot ts} @-}
removeMinTree :: Ord a => Heap a -> Tick (BiTree a, [BiTree a])
removeMinTree [t] = pure (t,[])
removeMinTree h@(t:ts)
    | root t < root t' = Tick (cc + 1) (t,ts)
    | otherwise        = Tick (cc + 1) (t',t:ts')
--    | otherwise = pure (addSnd h t) </> removeMinTree ts -- (t', t:ts')
    where 
      (Tick cc (t', ts')) = removeMinTree ts
-- TODO rewrite without tval/tcost --> access to subformulas

-- pott (tval ti) <= pot ts
-- tcost ti + pott (tval ti) - pot ts <= pot ts &&
{-@ reflect addSnd @-}
{-@ addSnd :: h:NEHeap a -> BiTree a -> {xs:(BiTree a, [BiTree a]) | pott xs = pot h - 1 } -> {v:(BiTree a, [BiTree a]) | pott v == pot h} @-}
addSnd :: Heap a -> BiTree a -> (BiTree a, [BiTree a]) ->(BiTree a, [BiTree a])
addSnd _ y (x,ys) = (x, y:ys)

{-
{-@ reflect addSnd @-}
{-@ addSnd :: ts:[BiTree a] -> t:BiTree a -> {xs:(BiTree a, [BiTree a]) | pott xs == pot (t:ts) - 1} 
        -> {ti:Tick {v:(BiTree a, [BiTree a]) | pott v == pot (t:ts)} | tcost ti = 0} @-}
addSnd :: [BiTree a] -> BiTree a -> (BiTree a, [BiTree a]) -> Tick (BiTree a, [BiTree a])
addSnd _ y (x,ys) = pure (x, y:ys)
-}

{-@ reflect findMin @-}
{-@ findMin :: Ord a => h:NEHeap a 
        -> {ti:Tick a | tcost (findMin h) <= pot h} @-}
findMin :: Ord a => Heap a -> Tick a
findMin ts = RTick.liftM getRoot (RTick.liftM first (removeMinTree ts))

 
-- O(log n)
{-@ reflect deleteMin @-}
{-@ deleteMin :: Ord a => h:NEHeap a -> Tick (Heap a)@-}
deleteMin :: Ord a => Heap a -> Tick (Heap a)
deleteMin ts = let (Node _ x ts1 _, ts2) = tval (removeMinTree ts) in
   deleteMin' ts1 ts2 ts
-- TODO rewrite with RTick library
{-@ reflect deleteMin' @-}
{-@ deleteMin' :: Ord a => ts1:[BiTree a] -> ts2:[BiTree a] 
        -> {h:NEHeap a | pot h == pot ts2 + 1} 
        -> {ti:Tick (v: Heap a) | amortized ti (pot (tval (deleteMin' ts1 ts2 h))) (pot h) <= 2 * (pot ts1 + pot ts2) && (pot (tval (deleteMin' ts1 ts2 h))) <= pot ts1 + pot ts2 } @-}
deleteMin' :: Ord a => [BiTree a] -> [BiTree a] -> Heap a -> Tick (Heap a)
deleteMin' ts1 ts2 h = RTick.step (tcost (removeMinTree h)) (mergeHeap (myreverse ts1) ts2)



{-@ reflect myreverse @-}
{-@ myreverse :: xs:[a] -> {ys:[a] | len xs == len ys } @-}
myreverse :: [a] -> [a]
myreverse l =  rev l []

{-@ reflect rev @-}
{-@ rev :: xs:[a] -> ys:[a] -> {zs:[a] | len zs == len xs + len ys } @-}
rev :: [a] -> [a] -> [a]
rev []     a = a
rev (x:xs) a = rev xs (x:a)