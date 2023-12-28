{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--ple" @-}
{-@ infix : @-}

module MyBinomial 
    ( link
    , insTree
    , insert
    , merge
    , removeMinTree
    , findMin
    , deleteMin
    )
where
import Prelude hiding (length, head, min, last, (++), reverse)
import Language.Haskell.Liquid.ProofCombinators
import GHC.Base (undefined)


{-@ type Pos = {n:Int | n >= 1} @-}
{-@ type NEBiTreeL a = {xs:[BiTree a] | length xs > 0} @-}
{-@ type NEHeap a = {ts:Heap a | length ts > 0} @-}
{-@ type Heap a = {ts:[BiTree a] | ordRankH ts} @-}

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

{-@ measure length @-}
{-@ length :: xs:[a] -> {v:Nat | v = len xs} @-}
length :: [a] -> Int
length [] = 0
length (x : xs) = 1 + length xs

{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[BiTree a]
        -> {v:Nat | (length  xs <= v) && (v = 0 <=> length xs = 0) && (length xs > 0 <=> v > 0)} @-}
treeListSize :: Ord a => [BiTree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = treeSize x + treeListSize xs

{-@ reflect ordRank @-}
ordRank :: [BiTree a] -> Bool
ordRank [] = True
ordRank [t] = True
ordRank (t:t':ts) = rank t == rank t' + 1 && ordRank (t':ts)

{-@ reflect ordRankH @-}
ordRankH :: [BiTree a] -> Bool
ordRankH [] = True
ordRankH [t] = True
ordRankH (t:t':ts) = rank t < rank t' && ordRankH (t':ts)

{-@ reflect sorted @-}
sorted :: Ord a => a -> [BiTree a] -> Bool
sorted x [] = True
sorted x (t:ts) = x <= root t && sorted x ts

{-@ reflect getRank @-}
{-@ getRank :: t:BiTree a -> {v:Nat | v = rank t} @-}
getRank :: BiTree a -> Int
getRank t = rank t

{-@ reflect head @-}
{-@ head :: {t:[a] | length t > 0} -> a @-}
head (t:ts) = t

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {zs:[a] | length zs == length xs + length ys} @-}
(++) :: Eq a => [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

{-@ reflect last @-}
{-@ last :: {t:[a] | length t > 0} -> a @-}
last [t] = t
last (t:ts) = last ts

{-@ reflect begin @-}
{-@ begin :: {ts:[a] | length ts > 0} -> {vs:[a] | length vs == length ts - 1} @-}
begin :: [a] -> [a]
begin [t] = []
begin (t:ts) = t : begin ts

{-@ reflect reverse @-}
{-@ reverse :: ts:[a] -> {vs:[a] | length ts == length vs} @-}
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

{-@ reflect powerOfTwo @-}
{-@ powerOfTwo :: Nat -> Pos @-}
powerOfTwo :: Int -> Int
powerOfTwo 0 = 1
powerOfTwo n = 2 * (powerOfTwo (n - 1))

{-@ reflect log2 @-}
{-@ log2 :: n:Pos -> v:Nat / [n]@-}
log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 (div n 2)

-- nodes ts = sum 2^rank_i
{-@ reflect sumRank @-}
{-@ sumRank :: ts:[BiTree a] -> {v:Nat | v >= length ts} @-}
sumRank :: Ord a => [BiTree a] -> Int
sumRank [] = 0
sumRank (t:ts) = powerOfTwo (rank t) + sumRank ts

--------------------------------------------------------------------
-- TREE AND HEAP OPERATIONS
--------------------------------------------------------------------
{-@ reflect singleton @-}
singleton :: Ord a => a -> BiTree a
singleton x = Node 0 x [] 1


{-@ reflect link @-}
{-@ link :: t1:BiTree a -> {t2:BiTree a | rank t2 = rank t1} 
        -> {v:BiTree a | rank v = rank t1 + 1 
        && treeSize v = treeSize t1 + treeSize t2
        && root v <= (root t1) && root v <= (root t2)} @-}
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


{-@ reflect insTree @-}
{-@ insTree :: t:BiTree a -> ts:Heap a 
            -> {zs:Heap a| length zs > 0 && length zs <= length ts + 1 
            && (rank (head zs) >= rank t || rank (head zs) >= rank (head ts))} @-}
insTree :: (Ord a, Eq a) => BiTree a -> [BiTree a] -> [BiTree a]
insTree t [] = [t]
insTree t [t']
    | rank t < rank t' = t : [t']
    | rank t' < rank t = t' : [t]
    | otherwise = [link t t']
insTree t ts@(t':ts') 
    | rank t < rank t' = t : ts
    | rank t' < rank t =
        ordRankHProp t' (insTree t ts') ??
        t' : insTree t ts'
    | otherwise =
        ordRankHProp t' ts' ??
        insTree (link t t') ts'

{-@ reflect insert @-}
{-@ insert :: a -> Heap a -> Heap a @-}
insert :: Ord a => a -> [BiTree a] -> [BiTree a]
insert x ts = insTree (singleton x) ts


{-@ reflect merge @-}
{-@ merge :: ts1:Heap a -> ts2:Heap a
            -> {zs:Heap a | length zs <= length ts1 + length ts2
               && (length ts1 == 0 || length ts2 == 0 || 
               (length zs > 0 && (rank (head zs) >= rank (head ts1) || rank (head zs) >= rank (head ts2))))
               } @-}
merge :: Ord a => [BiTree a] -> [BiTree a] -> [BiTree a]
merge ts1 [] = ts1
merge [] ts2 = ts2
merge [t1] [t2]
    | rank t1 < rank t2 = t1 : [t2]
    | rank t2 < rank t1 = t2 : [t1]
    | otherwise = [link t1 t2]
merge ts1@(t1:ts1') [t2]
    | rank t1 < rank t2 =
        ordRankHProp t1 (merge ts1' [t2]) ??
        t1 : merge ts1' [t2]
    | rank t2 < rank t1 = t2 : ts1
    | otherwise = insTree (link t1 t2) ts1'
merge ts1@(t1:ts1') ts2@(t2:ts2')
    | rank t1 < rank t2 =
        ordRankHProp t1 (merge ts1' ts2) ??
        t1 : merge ts1' ts2
    | rank t2 < rank t1 =
        ordRankHProp t2 (merge ts1 ts2') ??
        t2 : merge ts1 ts2'
    | otherwise =
        insTree (link t1 t2) (merge ts1' ts2')


{-@ reflect removeMinTree @-}
{-@ removeMinTree :: ts:NEHeap a 
            -> {tup:(t':BiTree a, {ts':Heap a | 
            length ts' == length ts - 1 &&
            (length ts' == 0 || (rank (head ts') >= rank (head ts)))}) |
            (length (snd tup) == 0 || (rank (head (snd tup)) >= rank (head ts)))} @-}
removeMinTree :: Ord a => [BiTree a] -> (BiTree a, [BiTree a])
removeMinTree [t] =
    ordRankH [] ??
    (t,[])
removeMinTree (t:[t'])
    | root t < root t' = (t,[t'])
    | otherwise =
        ordRankH [t] ??
        (t',[t])
removeMinTree (t:ts) =
    let (t', ts') = removeMinTree ts in
    ordRankHProp t ts' ??
    if root t < root t' 
        then
            (t, ts) 
        else
            removeMinTree ts ??
            (t', t:ts')

{-@ reflect findMin @-}
{-@ findMin :: NEHeap a -> a @-}
findMin :: Ord a => [BiTree a] -> a
findMin ts = 
    let (t, _) = removeMinTree ts in root t

{-@ reflect deleteMin @-}
{-@ deleteMin :: NEHeap a -> Heap a @-}
deleteMin :: Ord a => [BiTree a] -> [BiTree a]
deleteMin ts = let (Node _ x ts1 _, ts2) = removeMinTree ts in
    oRtoORHProp ts1 ??
    merge (reverse ts1) ts2


---------------------------------------------------------------
-- LEBENSRETTER zum Debuggen
---------------------------------------------------------------
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

---------------------------------------------------------------
-- PROPERTIES
---------------------------------------------------------------
{-@ reflect ordRankProp @-}
{-@ ordRankProp :: r:Nat -> {t:BiTree a | r == rank t} 
            -> {ts:[BiTree a] | (r == 0 && length ts == 0 || r == rank (head ts) + 1) && ordRank ts}
            -> {ordRank (t:ts)} @-}
ordRankProp :: Int -> BiTree a -> [BiTree a] -> Proof
ordRankProp r t [] = ()
ordRankProp r t (t':ts) = ()

{-@ reflect sortedProp @-}
{-@ sortedProp :: t1:BiTree a -> {t2:BiTree a | root t1 <= root t2} 
            -> {sorted (root t1) (t2:subtrees t1)} @-}
sortedProp :: BiTree a -> BiTree a -> Proof
sortedProp t1@(Node _ x [] _) t2 = ()
sortedProp t1 t2 = ()

{-@ reflect oRtoORHProp @-}
{-@ oRtoORHProp :: {ts:[BiTree a] | ordRank ts} -> {ordRankH (reverse ts)} @-}
oRtoORHProp :: Eq a => [BiTree a] -> Proof
oRtoORHProp [] = ()
oRtoORHProp [t] = ()
oRtoORHProp (t:ts) =
    oRtoORHProp ts ??
    reverseProp ts ??
    ordRankLastProp (reverse ts) t ??
    ()

{-@ reflect ordRankLastProp @-}
{-@ ordRankLastProp :: ts:Heap a -> {t:BiTree a | rank t > rank (last ts)}
        -> {ordRankH (ts ++ [t])} @-}
ordRankLastProp :: Eq a => [BiTree a] -> BiTree a -> Proof
ordRankLastProp [] t = ()
ordRankLastProp [t'] t = ()
ordRankLastProp (t':ts) t =
    ordRankLastProp ts t ??
    ()

{-@ reflect reverseProp @-}
{-@ reverseProp :: ts:NEBiTreeL a 
            -> {rank (head ts) == rank (last (reverse ts))}@-}
reverseProp :: Eq a => [BiTree a] -> Proof
reverseProp [t] = ()
reverseProp (t:ts) =
    lastProp t (reverse ts) ??
    ()

{-@ reflect lastProp @-}
{-@ lastProp :: t:a -> ts:[a] -> {last (ts ++ [t]) == t} @-}
lastProp :: Eq a => a -> [a] -> Proof
lastProp t [] = ()
lastProp t (t':ts) =
    lastProp2 t' (ts ++ [t]) ??
    lastProp t ts ??
    ()

{-@ reflect lastProp2 @-}
{-@ lastProp2 :: t:a -> {ts:[a] | length ts > 0} 
            -> {last (t:ts) == last ts} @-}
lastProp2 :: Eq a => a -> [a] -> Proof
lastProp2 t [t'] = ()
lastProp2 t ts = ()

{-@ reflect ordRankHProp @-}
{-@ ordRankHProp :: t:BiTree a -> ts:Heap a
            -> {(length ts == 0 || rank t < rank (head ts)) = ordRankH (t:ts)} @-}
ordRankHProp :: Ord a => BiTree a -> [BiTree a] -> Proof
ordRankHProp t [] = ()
ordRankHProp t [t'] = ()
ordRankHProp t (t':ts) = ()

{-@ ordRankBegin :: ts:NEHeap a -> {ordRankH (begin ts)} @-}
ordRankBegin :: (Eq a, Ord a) => [BiTree a] -> Proof
ordRankBegin [t] = ()
ordRankBegin (t:[t']) = () 
ordRankBegin (t:ts) =
    ordRankBegin ts ??
    ordRankHProp t (begin ts) ??
    ()

{-@ rankBeginLastProp :: {ts:Heap a | length ts > 1}
            -> {rank (last (begin ts)) < rank (last ts)} @-}
rankBeginLastProp :: Eq a => [BiTree a] -> Proof
rankBeginLastProp (t:[t']) = ()
rankBeginLastProp (t:ts) =
    rankBeginLastProp ts ??
    ()

{-@ sumRankProp :: ts:[BiTree a] -> {treeListSize ts == sumRank ts} @-}
sumRankProp :: Ord a => [BiTree a] -> Proof
sumRankProp [] = ()
sumRankProp (t:ts) =
    pow2Prop t ??
    sumRankProp ts ??
    ()

-- nodes t = 2^rank
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
    Node (r - 1) x ts (sz - treeSize t)

{-@ logPowP :: n:Nat -> {log2 (powerOfTwo n) == n} @-}
logPowP :: Int -> Proof
logPowP 0 = ()
logPowP n = logPowP (n-1) ?? ()

{-@ logAddProp :: x:Pos -> {log2 (2 * powerOfTwo x) = 1 + x} @-}
logAddProp :: Int -> Proof
logAddProp 1 = ()
logAddProp x = logPowP x ?? ()

{-@ logMon :: x:Pos -> {y:Pos | x <= y} -> {log2 x <= log2 y} @-}
logMon :: Int -> Int -> Proof
logMon x 1 = ()
logMon 1 y = (0 <= log2 y) ?? ()
logMon x y =
    logMon (div x 2) (div y 2) ??
    ()

-- firstProp
-- 2^rank_n <= sum 2^rank_i
{-@ rankLeSumProp :: ts:NEBiTreeL a
        -> {powerOfTwo (rank (last ts)) <= sumRank ts} @-}
rankLeSumProp :: Ord a => [BiTree a] -> Proof
rankLeSumProp [t] = ()
rankLeSumProp (t:ts) =
    rankLeSumProp ts ??
    (0 <= powerOfTwo (rank t)) ??
    ()

-- secondProp
-- length ts <= rank + 1
{-@ lenLeRankProp :: {ts:NEBiTreeL a | ordRankH ts}
            -> {length ts <= rank (last ts) + 1} @-}
lenLeRankProp :: Ord a => [BiTree a] -> Proof
lenLeRankProp [t] = (1 <= rank t + 1) ?? ()
lenLeRankProp (t:[t2]) =
    lenLeRankProp [t] ??
    ()
lenLeRankProp ts =
    ordRankBegin ts ??
    lenLeRankProp (begin ts) ??
    rankBeginLastProp ts ??
    ()

-- finalProp
-- length ts <= 1 + log (sum 2^ri)
{-@ lenLeLogProp :: {ts:[BiTree a] | ordRankH ts}
            -> {length ts <= 1 + log2 (treeListSize ts)} @-}
lenLeLogProp :: (Eq a, Ord a) => [BiTree a] -> Proof
lenLeLogProp [] = ()
lenLeLogProp [t] = (1 <= 1 + log2 (treeSize t)) ?? () 
lenLeLogProp ts =
    lenLeRankProp ts ??
    logAddProp (rank (last ts)) ??
    rankLeSumProp ts ??
    logMon (powerOfTwo (rank (last ts))) (sumRank ts) ??
    sumRankProp ts ??
    ()