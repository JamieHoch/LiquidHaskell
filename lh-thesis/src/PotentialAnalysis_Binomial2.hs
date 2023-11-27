{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--ple" @-}
--{-@ LIQUID "--no-termination" @-}
{-@ infix : @-}

module PotentialAnalysis_Binomial2 where
import Prelude hiding (length, pure, (<*>), length, head, tail, min)
import Language.Haskell.Liquid.RTick as RTick
import Language.Haskell.Liquid.ProofCombinators
import GHC.Base (undefined)
import Data.Bool (Bool(True, False))

{-@ measure length @-}
{-@ length :: xs:[a] -> {v:Nat | v = length xs} @-}
length :: [a] -> Int
length [] = 0
length (x : xs) = 1 + length xs

{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[BiTree a] 
        -> {v:Nat | (length  xs <= v) && (v = 0 <=> length xs = 0) && (length xs > 0 <=> v > 0)} @-}
treeListSize :: Ord a => [BiTree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = treeSize x + treeListSize xs

{-@ type Pos = {n:Int | n >= 1} @-}
--{-@ type NEHeap a = {h: Heap a | 0 < length (list h)} @-}

{-@
data BiTree [rank] a =
    Node
        { rank :: Nat
        , root :: a
        , subtrees :: {s:[BiTree a] | rank == length s && (length s == 0 || length s > 0 
                    && rank == getRank (head s) + 1 && sorted root s) && ordRank s}
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

{-@ reflect ordRank @-}
ordRank :: [BiTree a] -> Bool
ordRank [] = True
ordRank [t] = True
ordRank (t:t':ts) = rank t == rank t' + 1 && ordRank (t':ts)

{-@ reflect sorted @-}
sorted :: Ord a => a -> [BiTree a] -> Bool
sorted x [] = True
sorted x (t:ts) = x <= root t && sorted x ts

{-@ reflect rankGTList @-}
{-@ rankGTList :: Nat -> [BiTree a] -> Bool @-}
rankGTList :: Int -> [BiTree a] -> Bool
rankGTList r [] = True
rankGTList r (t:ts) = r > rank t && rankGTList r ts

{-@ reflect rankGTListProp @-}
{-@ rankGTListProp :: r:Nat -> {t:BiTree a | r > rank t} 
            -> {ts:[BiTree a] | rankGTList r ts} -> {rankGTList r (t:ts)}  
@-}
rankGTListProp :: Ord a => Int -> BiTree a -> [BiTree a] -> Proof
rankGTListProp r t ts = ()

{-@ reflect rankGTListProp2 @-}
{-@ rankGTListProp2 :: r:Nat -> {ts:[BiTree a] | rankGTList r ts} 
            -> {rankGTList (r+1) ts}  
@-}
rankGTListProp2 :: Ord a => Int -> [BiTree a] -> Proof
rankGTListProp2 r [] = ()
rankGTListProp2 r (t:ts) = rankGTListProp2 r ts ?? ()

{-@ reflect getRank @-}
{-@ getRank :: t:BiTree a -> {v:Nat | v = rank t} @-}
getRank :: BiTree a -> Int
getRank t = rank t

{-@ reflect getRoot @-}
{-@ getRoot :: t:BiTree a -> {v:a | v = root t} @-}
getRoot :: BiTree a -> a
getRoot t = root t

{-@ reflect head @-}
{-@ head :: {t:[a] | length t > 0} -> a @-}
head (t:ts) = t

{-@ reflect tail @-}
{-@ tail :: {t:[a] | length t > 0} -> [a] @-}
tail (t:ts) = ts

--LEBENSRETTER zum Debuggen
{-@ assume :: b:Bool -> {v:Bool | b } @-}
assume :: Bool -> Bool
assume x = undefined

{-@ reflect assert @-}
{-@ assert :: b:{Bool | b } -> {v:Bool | b} @-}
assert :: Bool -> Bool
assert x = x

{-@ reflect ?? @-}
{-@ (??) :: a -> y:b -> {v:b | v == y } @-}
(??) :: a -> b -> b
x ?? y = y

{-
type Heap a = [BiTree a]

heap :: Heap Int 
heap = [bi1, bi2]

bi1, bi2 :: BiTree Int 
bi1 = Node 0 1 [] 1
bi2 = Node 1 1 [] 1
-}
{-@ reflect min @-}
min :: Ord a => a -> a -> a
min x1 x2
    | x1 <= x2 = x1
    | otherwise = x2

{-@ reflect helpSubtr @-}
helpSubtr :: Ord a => BiTree a -> BiTree a -> [BiTree a]
helpSubtr t1 t2
    | root t1 <= root t2 = t2 : subtrees t1
    | otherwise = t1 : subtrees t2

{-@ reflect link @-}
{-@ link :: t1:BiTree a -> {t2:BiTree a | rank t2 = rank t1} 
        -> {v:BiTree a | rank v = rank t1 + 1 
        && treeSize v = treeSize t1 + treeSize t2
        && root v = min (root t1) (root t2)
        && subtrees v = helpSubtr t1 t2} @-}
link :: (Ord a) => BiTree a -> BiTree a -> BiTree a
link t1@(Node r1 x1 ts1 sz1) t2@(Node _ x2 ts2 sz2)
    | x1 <= x2 =
        ordRankProp r1 t2 ts1 ??
        sortedProp t1 t2 ??
        Node (r1 + 1) x1 (t2:ts1) (sz1 + sz2)
    | otherwise =
        ordRankProp r1 t1 ts2 ??
        sortedProp t2 t1 ??
        Node (r1 + 1) x2 (t1:ts2) (sz1 + sz2)

{-@ reflect sortedProp @-}
{-@ sortedProp :: t1:BiTree a -> {t2:BiTree a | root t1 <= root t2} 
            -> {sorted (root t1) (t2:subtrees t1)} @-}
sortedProp :: BiTree a -> BiTree a -> Proof
sortedProp t1@(Node _ x [] _) t2 = ()
sortedProp t1 t2 = ()

{-@ reflect ordRankProp @-}
{-@ ordRankProp :: r:Nat -> {t:BiTree a | r == rank t} 
            -> {ts:[BiTree a] | (r == 0 && length ts == 0 || r == getRank (head ts) + 1) && ordRank ts}
            -> {ordRank (t:ts)} @-}
ordRankProp :: Int -> BiTree a -> [BiTree a] -> Proof
ordRankProp r t [] = ()
ordRankProp r t (t':ts) = ()

{-@ reflect numNodes2 @-}
{-@ numNodes2 :: h:[BiTree a] -> v:Nat @-}
numNodes2 :: [BiTree a]  -> Int
numNodes2 [] = 0
numNodes2 (t:ts) = powerOfTwo (rank t) + numNodes2 ts

{-@
data Heap a =
    Heap 
    {
          list :: [BiTree a]
        , nodes :: {v:Int | v == numNodes2 list}
    }
@-}
-- Do not work since we need to know that v <= treeSize t
--, nodes :: {v:Int | powerOfTwo (length list) <= 2*v}
--, nodes :: {v:Int | powerOfTwo (length list - 1) <= v}
--, nodes :: {v:Int | length list <= log2 v + 1}
data Heap a =
    Heap 
    {
          list :: [BiTree a]
        , nodes :: Int
    }

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
{-@ numNodes :: h:[BiTree a] -> {v:Nat | v == 0 <=> h == []} @-}
numNodes :: [BiTree a]  -> Int
numNodes [] = 0
numNodes [t] = treeSize t
numNodes (t:ts) = treeSize t + numNodes ts

{-@ reflect logPot @-}
logPot :: [BiTree a] -> Int
logPot [] = 0
logPot ts = log2 (numNodes ts) 

{-@ prop :: h:[BiTree a] -> {numNodes h + 1 == powerOfTwo (length h)} @-}
prop :: [BiTree a] -> ()
prop [] = numNodes [] + 1 
    === powerOfTwo 0 *** QED
prop [t] = undefined -- numNodes [t] + 1 === treeSize t + 1 === 1 + treeListSize subtrees
prop ts = undefined
-- not possible to prove that because no knowledge about tree t


-- potential as length of list
-- TODO change to log n instead length
{-@ measure pot @-}
{-@ pot :: xs:[a] -> {v: Nat | v == (length xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

{-@ invariant {xs:[a] | pot xs == length xs } @-}

-- potential of tuple
{-@ measure pott @-}
{-@ pott :: x:(a,[a]) -> {v:Int | v == (pot (snd x)) + 1} @-}
pott :: (a,[a]) -> Int
pott (x,xs) = pot xs + 1

{-@ inline amortized @-}
amortized :: Tick a -> Int -> Int -> Int  
amortized cost out input = tcost cost + out - input

-- amortized ti (pot (tval (insTree t ts))) (pot ts) == 2
-- tcost ti + pot (tval (insTree t ts)) - pot ts = 2
-- tcost ti = 2 + pot ts -  pot os  >= 2 + pot ts -  pot ts - 1 = 1

-- tcost ti >= 1 
-- 
--  pot os <= pot ts + 1
--  - pot os >= - pot ts - 1 
-- 
-- pot (tval (insTree t ts)) <= length ts + 1 
-- pot (tval (insTree t ts)) <= length ts + 1 

{-@ reflect insTree @-}
{-@ insTree :: t:BiTree a -> ts:[BiTree a] 
        -> {ti:(Tick {zs:[BiTree a]| length zs <= length ts + 1}) | amortized ti (pot (tval (insTree t ts))) (pot ts) == 2 && pot (tval (insTree t ts)) - pot ts <= 1 } @-}
insTree :: Ord a => BiTree a -> [BiTree a] -> Tick [BiTree a]
insTree t [] = wait [t]
insTree t ts@(t':ts')
    | rank t < rank t' = wait (t : ts)
    | rank t > rank t' = pure ((:) t') <*> insTree t ts' -- reflect doesn't work with lambda abstraction
    | otherwise = step 1 (insTree (link t t') ts')


{-@ reflect insTreeH @-}
{-@ insTreeH :: t:BiTree a -> ts:Heap a 
        -> {ti:Tick (Heap a) | True}
        / [length (list ts)]
@-}
insTreeH :: Ord a => BiTree a -> Heap a -> Tick (Heap a)
insTreeH t (Heap [] n) = wait (Heap [t] (n + powerOfTwo (rank t)))
insTreeH t (Heap ts@(t':ts') n)
    | rank t < rank t' = 
        wait (Heap (t : ts) (n + powerOfTwo (rank t)))
    | rank t > rank t' =
        pure (addTreeFirst t') <*> insTreeH t (Heap ts' (n - powerOfTwo (rank t')))
    | otherwise = 
        step 1 (insTreeH (link t t') (Heap ts' (n - powerOfTwo (rank t'))))

{-@ reflect addTreeFirst @-}
addTreeFirst :: BiTree a -> Heap a -> Heap a
addTreeFirst t (Heap ts n) =
    Heap (t:ts) (n + powerOfTwo (rank t))

{-@ pow2Prop :: t:BiTree a -> {treeSize t == powerOfTwo (rank t)} @-}
pow2Prop :: Ord a => BiTree a -> Proof
pow2Prop t = () ? pow2Lemma t

{-@ reflect pow2Lemma @-}
{-@ pow2Lemma :: t:BiTree a 
            -> {v:BiTree a | treeSize v == powerOfTwo (rank v) && 
            v == t} @-}
pow2Lemma :: Ord a => BiTree a -> BiTree a
pow2Lemma t@(Node _ _ [] _) = t
pow2Lemma t@(Node r x (t':ts) sz) =
  --(sz == treeSize t' + treeListSize ts) ??
  --(root (residual t) == x) ??
  --(min (root t') x == x) ??
  link (pow2Lemma (residual t)) (pow2Lemma t')

{-@ reflect residual @-}
{-@ residual :: {t:BiTree a | length (subtrees t) > 0} 
            -> {v: BiTree a | rank v == rank t - 1 && root t == root v
            && subtrees v == tail (subtrees t)
            && treeSize v = treeSize t - treeSize (head (subtrees t))}
@-}
residual :: Ord a => BiTree a -> BiTree a
residual (Node _ x [t] sz) = Node 0 x [] (sz - treeSize t)
residual (Node r x (t:ts) sz) = 
    (sz == treeSize t + treeListSize ts) ??
    ordRank ts ??
    --(r-1 == getRank (head ts) + 1) ??
    Node (r - 1) x ts (sz - treeSize t)

{-@ reflect singletonT @-}
{-@ singletonT :: Ord a => a -> BiTree a @-}
singletonT :: Ord a => a -> BiTree a
singletonT x = Node 0 x [] 1

{-@ singletonH :: Ord a => a -> Heap a @-}
singletonH :: Ord a => a -> Heap a
singletonH x = Heap [Node 0 x [] 1] 1
-- Note: length [Node 0 x [] 1] == 1 <= 0 + 1 == log 1 + 1
-- O(1)
{-@ reflect insert @-}
{-@ insert :: x:a -> h:[BiTree a] 
        -> {ti:Tick ([BiTree a]) | tcost ti + pot (tval (insert x h)) - pot h = 2}  @-}
insert :: Ord a => a -> [BiTree a] -> Tick [BiTree a]
insert x ts = insTree (singletonT x) ts

{-
{-@ reflect insertH @-}
{-@ insertH :: x:a -> h:Heap a
        -> {ti:Tick (Heap a) | tcost ti + pot (tval (insert x h)) - pot h = 2}  @-}
insert :: Ord a => a -> Heap a -> Tick (Heap a)
insert x (Heap ts n) = insTree (singletonT x) ts
-}


-- tcost ti + pot (tval ti) - (pot ts1 + pot ts2) <= log n
-- length of list is log n ==> log n = pot (tval ti)
-- O(log n)
{-@ reflect mergeHeap @-}
{-@ mergeHeap :: Ord a => ts1:[BiTree a] -> ts2:[BiTree a] 
        -> {ti:Tick {xs:[BiTree a] | length xs <= length ts1 + length ts2 && pot xs == length xs} | 
                    amortized ti (pot (tval (mergeHeap ts1 ts2))) (pot ts1 + pot ts2) <= pot (tval (mergeHeap ts1 ts2)) &&
                    pot (tval (mergeHeap ts1 ts2)) == length (tval (mergeHeap ts1 ts2)) &&
                    length (tval (mergeHeap ts1 ts2)) <= length ts1 + length ts2 } @-}
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
{-@ abind :: c:Nat -> m:Nat -> x:Tick ({v:[a] | length v <= m - 1}) -> f:(fx:[a] -> {t:Tick {xs:[c] | length xs <= length fx + 1} | amortized t (pot (tval t)) (pot fx) <= c})
                 -> {ti:Tick {xs:[c] | length xs <= m}  | (tcost ti == c + tcost x ) && tval (f (tval x)) == tval ti && pot (tval ti) == length (tval ti) && length (tval ti) <= m } @-}
abind c _ (Tick c1 x) f = Tick (c + c1) y
    where Tick _ y = f x
-- END TRUSTED 

{-@ reflect first @-}
first :: Ord a => (BiTree a, [BiTree a]) -> BiTree a
first (x,xs) = x

{-@ reflect removeMinTree @-}
{-@ removeMinTree :: Ord a => {ts:[BiTree a] | length ts > 0}
        -> {ti:Tick {v:(BiTree a, [BiTree a]) | pott v == pot ts} | tcost ti + pott (tval ti) - pot ts <= pot ts && tcost ti <= pot ts} @-}
removeMinTree :: Ord a => [BiTree a] -> Tick (BiTree a, [BiTree a])
removeMinTree [t] = pure (t,[])
removeMinTree h@(t:ts)
    | root t < root t' = Tick (cc + 1) (t,ts)
    | otherwise        = Tick (cc + 1) (t',t:ts')
--    | otherwise = pure (addSnd h t) </> removeMinTree ts -- (t', t:ts')
    where 
      (Tick cc (t', ts')) = removeMinTree ts
-- TODO rewrite without tval/tcost --> access to subformulas



{-@ removeMinTree' :: Ord a => {ts:[BiTree a] | length ts > 0}
        -> {ti:Tick {v:(BiTree a, [BiTree a]) | pott v == pot ts} |  pott (tval ti) == pot ts && tcost ti <= pot ts && tcost ti + pott (tval ti) - pot ts <= pot ts} @-}
removeMinTree' :: Ord a => [BiTree a] -> Tick (BiTree a, [BiTree a])
removeMinTree' [t]    = pure (t,[])
removeMinTree' (t:ts) = boo (t:ts) (ifTick 0 (removeMinTree' ts) (\(t', ts') -> (root t < root t')) (\(t', ts') -> pure (t,ts)) (\(t', ts') -> pure (t',t:ts')))


{-@ reflect propPott @-}
{-@ propPott :: ts:Int-> i:{v:(BiTree a, [BiTree a]) | pott v == ts } -> {v:Bool | v <=> (pott i == ts) } @-}
propPott :: Int -> (BiTree a, [BiTree a]) -> Bool
propPott ts v = pott v == ts


{-@ valueTickPushProp :: p:(a -> Bool) -> ti:(Tick {v:a | p v})
        -> {to:Tick {v:a | p v}  | to == ti && p (tval to) && tcost to == tcost ti && tval to == tval ti} @-}
valueTickPushProp :: (a -> Bool) -> Tick a -> Tick a
valueTickPushProp _ (Tick c v) = Tick c v  



{-@ boo :: {ts:[BiTree a] | length ts > 0} -> ti:Tick {v:(BiTree a, [BiTree a]) | pott v == pot ts} 
        -> {to:Tick {v:(BiTree a, [BiTree a]) | pott v == pot ts}  | to == ti && pott (tval to) == pot ts && tcost to == tcost ti && tval to == tval ti} @-}
boo :: [BiTree a] -> Tick (BiTree a, [BiTree a]) -> Tick (BiTree a, [BiTree a])
boo _ (Tick c v) = Tick c v  


-- THIS TOO IS TRUSTED LIBRARY CODE 
-- NV: Here the +1 comes because I tick! 
{-@ reflect ifTick @-}
{-@ ifTick :: c:Nat -> t:Tick a -> (a -> Bool) -> tb:(a -> {ti:Tick b | tcost ti <= c}) -> fb:(a -> {ti:Tick b | tcost ti <= c}) 
           -> {to:Tick b | (tcost to <= tcost t + c + 1) && (tval to == tval (tb (tval t)) || tval to == tval (fb (tval t))) } @-}
ifTick :: Int -> Tick a -> (a -> Bool) -> (a -> Tick b) -> (a -> Tick b) -> Tick b
ifTick _ (Tick c v) b t e = RTick.step (c + 1) (if b v then t v else e v)  
-- END OF TRUSTED CODE 

{-@ reflect findMin @-}
{-@ findMin :: Ord a => {ts:[BiTree a] | length ts > 0}
        -> {ti:Tick a | tcost (findMin ts) <= pot ts} @-}
findMin :: Ord a => [BiTree a] -> Tick a
findMin ts = RTick.liftM getRoot (RTick.liftM first (removeMinTree ts))

 
-- O(log n)
{-@ reflect deleteMin @-}
{-@ deleteMin :: Ord a => {ts:[BiTree a] | length ts > 0} -> Tick [BiTree a]@-}
deleteMin :: Ord a => [BiTree a] -> Tick [BiTree a]
deleteMin ts = let (Node _ x ts1 _, ts2) = tval (removeMinTree ts) in
   deleteMin' ts1 ts2 ts
-- TODO rewrite with RTick library

{-@ reflect deleteMin' @-}
{-@ deleteMin' :: Ord a => ts1:[BiTree a] -> ts2:[BiTree a] 
        -> {h:[BiTree a] | length h > 0 && pot h == pot ts2 + 1} 
        -> {ti:Tick (v:[BiTree a]) | amortized ti (pot (tval (deleteMin' ts1 ts2 h))) (pot h) <= 2 * (pot ts1 + pot ts2) && (pot (tval (deleteMin' ts1 ts2 h))) <= pot ts1 + pot ts2 } @-}
deleteMin' :: Ord a => [BiTree a] -> [BiTree a] -> [BiTree a] -> Tick [BiTree a]
deleteMin' ts1 ts2 h = RTick.step (tcost (removeMinTree h)) (mergeHeap (myreverse ts1) ts2)



{-@ reflect myreverse @-}
{-@ myreverse :: xs:[a] -> {ys:[a] | length xs == length ys } @-}
myreverse :: [a] -> [a]
myreverse l =  rev l []

{-@ reflect rev @-}
{-@ rev :: xs:[a] -> ys:[a] -> {zs:[a] | length zs == length xs + length ys } @-}
rev :: [a] -> [a] -> [a]
rev []     a = a
rev (x:xs) a = rev xs (x:a)
