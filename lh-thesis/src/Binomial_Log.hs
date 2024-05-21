{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix : @-}

module Binomial_Log
    ( link
    , insTree
    , insert
    , merge
    , removeMinTree
    , findMin
    , deleteMin
    )
where
import Prelude hiding (length, pure, head, last, (++), reverse, (<*>), (>>=))
import Language.Haskell.Liquid.RTick as RTick
import Language.Haskell.Liquid.ProofCombinators


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

{-@ reflect getRoot @-}
{-@ getRoot :: t:BiTree a -> {v:a | v = root t} @-}
getRoot :: BiTree a -> a
getRoot t = root t

{-@ reflect head @-}
{-@ head :: {t:[a] | length t > 0} -> a @-}
head (t:ts) = t

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {zs:[a] | length zs == length xs + length ys} @-}
(++) :: Eq a => [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

{-@ reflect first @-}
first :: Ord a => (BiTree a, [BiTree a]) -> BiTree a
first (x,xs) = x

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

{-@ reflect sumRank @-}
{-@ sumRank :: ts:[BiTree a] -> {v:Nat | v >= length ts} @-}
sumRank :: Ord a => [BiTree a] -> Int
sumRank [] = 0
sumRank (t:ts) = powerOfTwo (rank t) + sumRank ts

--------------------------------------------------------------------
-- POTENTIAL FUNCTION
--------------------------------------------------------------------
{-@ reflect pot @-}
{-@ pot :: xs:Heap a -> {v: Nat | v == (length xs)
         && v <= 1 + log2 (treeListSize xs)} 
@-}
pot :: Ord a => [BiTree a] -> Int
pot []     =  0
pot (x:xs) =
    ordRankHProp2 x xs ??
    lenLeLogProp (x:xs) ??
    1 + (pot xs)

{-@ reflect pott @-}
{-@ pott :: tup:(BiTree a, Heap a) -> {v:Nat | v == (pot (snd tup)) + 1} @-}
pott :: Ord a => (BiTree a, [BiTree a]) -> Int
pott (x,xs) = pot xs + 1

{-@ inline amortized @-}
{-@ amortized :: Tick (Heap a) -> Heap a -> Int @-}
amortized :: Ord a => Tick [BiTree a] -> [BiTree a] -> Int
amortized ti input = tcost ti + pot (tval ti) - pot input

{-@ inline amortized2 @-}
{-@ amortized2 :: Tick (Heap a) -> Heap a -> Heap a -> Int @-}
amortized2 :: Ord a => Tick [BiTree a] -> [BiTree a] -> [BiTree a] -> Int
amortized2 ti in1 in2 = tcost ti + pot (tval ti) - pot in1 - pot in2

{-@ inline amortizedTup @-}
{-@ amortizedTup :: Tick (BiTree a, Heap a) -> Heap a -> Int @-}
amortizedTup :: Ord a => Tick (BiTree a, [BiTree a]) -> [BiTree a] -> Int
amortizedTup ti input = tcost ti + pott (tval ti) - pot input

{-@ inline amortizedLog @-}
{-@ amortizedLog :: Tick (NEHeap a) -> Pos -> Int @-}
amortizedLog :: Ord a => Tick [BiTree a] -> Int -> Int
amortizedLog ti input = tcost ti + log2 (treeListSize (tval ti)) - log2 input

{-@ inline amortizedLogTup @-}
{-@ amortizedLogTup :: Tick (BiTree a, Heap a) -> NEHeap a -> Int @-}
amortizedLogTup :: Ord a => Tick (BiTree a, [BiTree a]) -> [BiTree a] -> Int
amortizedLogTup ti input = tcost ti + logPott (tval ti) - log2 (treeListSize input)

{-@ reflect logPott @-}
{-@ logPott :: tup:(BiTree a, Heap a) -> v:Nat @-}
logPott :: Ord a => (BiTree a, [BiTree a]) -> Int
logPott (x,xs) = log2 (treeSize x + treeListSize xs)

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

--------------------------------------------------------------------
-- TREE AND HEAP OPERATIONS
--------------------------------------------------------------------
{-@ reflect singleton @-}
{-@ singleton :: Ord a => a -> BiTree a @-}
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
            -> {ti:Tick ({zs:NEBiTreeL a | (rank (head zs) >= rank t || rank (head zs) >= rank (head ts))}) | 
            ordRankH (tval ti) && 
            amortized ti ts <= 1 &&
            treeListSize (tval ti) == treeListSize ts + treeSize t &&
            log2 (treeListSize (tval ti)) == log2 (treeListSize ts + treeSize t) &&
            (tcost ti) <= 2 + log2 (treeListSize ts) &&
            (tcost ti) <= pot ts + 1 &&
            pot (tval ti) <= pot ts + 1 &&
            amortizedLog ti (treeListSize ts + treeSize t) <= 2 + log2 (treeListSize ts)
            } @-}
insTree :: (Ord a, Eq a) => BiTree a -> [BiTree a] -> Tick [BiTree a]
insTree t [] =
    pure [t]
insTree t [t']
    | rank t < rank t' =
        lenLeLogProp [t'] ?? -- NEW
        pure (t : [t'])
    | rank t' < rank t =
        lenLeLogProp [t'] ?? -- NEW
        pure (t' : [t])
    | otherwise =
        lenLeLogProp [t'] ?? -- NEW
        step 1 (pure [link t t'])
insTree t ts@(t':ts') 
    | rank t < rank t' =
        lenLeLogProp ts ?? -- NEW
        (1 <= pot ts + 1) ??
        pure (t : ts)
    | rank t' < rank t =
        (pot ts <= 1 + log2 (treeListSize ts)) ?? -- NEW
        ordRankHProp t' (tval (insTree t ts')) ??
        pure ((:) t') <*> insTree t ts'
    | otherwise =
        (pot ts <= 1 + log2 (treeListSize ts)) ?? -- NEW
        ordRankHProp t' ts' ??
        step 1 (insTree (link t t') ts')

{-@ reflect insert @-}
{-@ insert :: x:a -> ts:Heap a 
        ->  {ti:Tick ([BiTree a]) | ordRankH (tval ti) &&
        amortized ti ts <= 1 &&
        amortizedLog ti (treeListSize ts + 1) <= 2 + log2 (treeListSize ts)} @-}
insert :: Ord a => a -> [BiTree a] -> Tick [BiTree a]
insert x ts = insTree (singleton x) ts

{-@ reflect merge @-}
{-@ merge :: ts1:Heap a -> ts2:Heap a
            -> {ti:Tick ({zs:[BiTree a] | (length ts1 == 0 || length ts2 == 0 || 
               (length zs > 0 && (rank (head zs) >= rank (head ts1) || rank (head zs) >= rank (head ts2))))
               }) | 
               ordRankH (tval ti) &&
               pot (tval ti) <= pot ts2 + pot ts1 &&
               amortized2 ti ts1 ts2 <= pot ts2 + pot ts1 &&
               treeListSize (tval ti) == treeListSize ts1 + treeListSize ts2 &&
               log2 (treeListSize (tval ti)) == log2 (treeListSize ts1 + treeListSize ts2) &&
               tcost ti <= 2 * (pot ts2 + pot ts1) &&
               pot ts2 <= 1 + log2 (treeListSize ts2) &&
               pot ts1 <= 1 + log2 (treeListSize ts1) &&
               tcost ti <= 2 * (2 + log2 (treeListSize ts2) + log2 (treeListSize ts1)) &&
               amortizedLog ti (treeListSize ts1 + treeListSize ts2) <= 2 * (2 + log2 (treeListSize ts2) + log2 (treeListSize ts1))
                } @-}
-- tcost ti + log2 (treeListSize (tval ti)) - log2 (treeListsize ts1 + treeListsize ts2)
-- amortizedLog ti (treeListSize ts1 + treeListSize ts2)
merge :: Ord a => [BiTree a] -> [BiTree a] -> Tick [BiTree a]
merge ts1 [] = 
     (0 <= pot ts1) ??
     pure ts1
merge [] ts2 = 
    (0 <= pot ts2) ??
    pure ts2
merge [t1] [t2]
    | rank t1 < rank t2 =
        lenLeLogProp [t2] ?? -- NEW
        lenLeLogProp [t1] ?? -- NEW
        wait (t1 : [t2])
    | rank t2 < rank t1 = 
        lenLeLogProp [t2] ?? -- NEW
        lenLeLogProp [t1] ?? -- NEW
        wait (t2 : [t1])
    | otherwise = 
        lenLeLogProp [t2] ?? -- NEW
        lenLeLogProp [t1] ?? -- NEW
        wait [link t1 t2]
merge ts1@(t1:ts1') [t2]
    | rank t1 < rank t2 =
        ordRankHProp t1 (tval (merge ts1' [t2])) ??
        (pot ts1 <= 1 + log2 (treeListSize ts1)) ?? -- NEW
        pure ((:) t1) </> merge ts1' [t2]
    | rank t2 < rank t1 = 
        (0 <= pot ts1) ??
        lenLeLogProp [t2] ?? -- NEW
        lenLeLogProp [t1] ?? -- NEW
        wait (t2 : ts1)
    | otherwise = 
        (tcost (insTree (link t1 t2) ts1') <= pot ts1) ?? -- NEW
        lenLeLogProp [t2] ?? -- NEW
        lenLeLogProp [t1] ?? -- NEW
        insTree (link t1 t2) ts1'
merge ts1@(t1:ts1') ts2@(t2:ts2')
    | rank t1 < rank t2 =
        ordRankHProp t1 (tval (merge ts1' ts2)) ??
        (pot ts2 <= 1 + log2 (treeListSize ts2)) ?? -- NEW
        (pot ts1 <= 1 + log2 (treeListSize ts1)) ?? -- NEW
        pure ((:) t1) </> merge ts1' ts2
    | rank t2 < rank t1 =
        ordRankHProp t2 (tval (merge ts1 ts2')) ??
        (pot ts2 <= 1 + log2 (treeListSize ts2)) ?? -- NEW
        (pot ts1 <= 1 + log2 (treeListSize ts1)) ?? -- NEW
        pure ((:) t2) </> merge ts1 ts2'
    | otherwise =
        -- WE TRUST THIS PART
        let Tick m x = merge ts1' ts2'
            Tick n y = insTree (link t1 t2) x in
        (pot ts2 <= 1 + log2 (treeListSize ts2)) ?? -- NEW
        (pot ts1 <= 1 + log2 (treeListSize ts1)) ?? -- NEW
        Tick (n + m + 1) y
        -- END TRUSTED

{- 
    NOTE: 
    (merge ts1' ts2') >>= (insTree (link t1 t2)) but (>>=) does not inherit types; 
    we would need ordRankH and hence BiTrees and ALL Properties in a separate function
    -> better trust small parts in code than big separate functions 
-}

{-@ reflect removeMinTree @-}
{-@ removeMinTree :: ts:NEHeap a 
            -> {ti:Tick ({tup:(t':BiTree a, {ts':[BiTree a] | 
            length ts' == length ts - 1 &&
            (length ts' == 0 || (rank (head ts') >= rank (head ts)))}) |
            (length (snd tup) == 0 || 
            (rank (head (snd tup)) >= rank (head ts)))}) | 
            ordRankH (snd (tval ti)) &&
            amortizedTup ti ts <= pot ts &&
            tcost ti <= pot ts &&
            tcost ti <= 1 + log2 (treeListSize ts) &&
            (treeSize (fst (tval ti)) + treeListSize (snd (tval ti)) == treeListSize ts) &&
            amortizedLogTup ti ts <= 1 + log2 (treeListSize ts)
            } @-}
removeMinTree :: Ord a => [BiTree a] -> Tick (BiTree a, [BiTree a])
removeMinTree [t] =
    ordRankH [] ??
    lenLeLogProp [t] ?? -- NEW
    pure (t,[])
removeMinTree (t:[t'])
    | root t < root t' = 
        lenLeLogProp (t:[t']) ?? -- NEW
        pure (t,[t'])
    | otherwise =
        ordRankH [t] ??
        lenLeLogProp (t:[t']) ?? -- NEW
        pure (t',[t])
removeMinTree (t:ts)
    -- WE TRUST THIS PART
    | root t < root t' =
        (pot (t:ts) <= 1 + log2 (treeListSize (t:ts))) ?? -- NEW
        Tick (cc + 1) (t,ts)
    | otherwise =
        ordRankHProp t ts' ??
        (pot (t:ts) <= 1 + log2 (treeListSize (t:ts))) ?? -- NEW
        Tick (cc + 1) (t',t:ts')
    where 
      (Tick cc (t', ts')) = removeMinTree ts
    -- END TRUSTED

{-@ findMin :: Ord a => ts:NEHeap a
        -> {ti:Tick a | tcost ti + 1 - pot ts <= 1 &&
        tcost ti + 1 - log2 (treeListSize ts) - 1 <= 1} @-}
findMin :: Ord a => [BiTree a] -> Tick a
findMin ts = (pot ts <= log2 (treeListSize ts) + 1) ??
    RTick.liftM getRoot (RTick.liftM first (removeMinTree ts))

{-@ deleteMin :: ts:NEHeap a -> {ti:Tick [BiTree a] | 
            ordRankH (tval ti) &&
            amortized ti ts <= 2 * (pot (reverse (subtrees (fst (tval (removeMinTree ts))))) + pot (snd (tval (removeMinTree ts)))) 
            && treeListSize ts > treeListSize (tval ti)
            } @-}
-- && treeListSize ts > treeListSize (tval ti)
-- tcost = tcost rem + tcost merge  
-- merge: 2 * (2 + log2 (treeListSize ts2) + log2 (treeListSize ts1))
-- removeMinTree = 1 + log2 (treeListSize ts)
deleteMin :: Ord a => [BiTree a] -> Tick [BiTree a]
deleteMin ts =
    -- WE TRUST THIS PART
    let Tick cc (n@(Node _ x ts1 _), ts2) = removeMinTree ts in
    oRtoORHProp ts1 ??
    assume (treeListSize ts1 == treeListSize (reverse ts1)) ??
    assert (cc <= 1 + log2 (treeListSize ts)) ??
    assert (treeListSize ts1 + treeListSize ts2 < treeListSize ts) ??
    assert (treeListSize ts1 < treeListSize ts) ??
    --assert (tcost (merge (reverse ts1) ts2) <= 2 * (2 + 2*log2 (treeListSize ts))) ??
    step (cc) (merge (reverse ts1) ts2)
    -- END TRUSTED

---------------------------------------------------------------
-- PROPERTIES
---------------------------------------------------------------
{-@ reflect ordRankProp @-}
{-@ ordRankProp :: r:Nat -> {t:BiTree a | r == rank t} 
            -> {ts:[BiTree a] | (r == 0 && length ts == 0 || r == getRank (head ts) + 1) && ordRank ts}
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

{-@ reflect ordRankHProp2 @-}
{-@ ordRankHProp2 :: t:BiTree a -> {ts:[BiTree a] | ordRankH (t:ts)}
            -> {ordRankH ts} @-}
ordRankHProp2 :: Ord a => BiTree a -> [BiTree a] -> Proof
ordRankHProp2 t [] = ()
ordRankHProp2 t ts = ()

{-@ reflect ordRankBegin @-}
{-@ ordRankBegin :: ts:NEHeap a -> {ordRankH (begin ts)} @-}
ordRankBegin :: (Eq a, Ord a) => [BiTree a] -> Proof
ordRankBegin [t] = ()
ordRankBegin (t:[t']) = () 
ordRankBegin (t:ts) =
    ordRankBegin ts ??
    ordRankHProp t (begin ts) ??
    ()

{-@ reflect rankBeginLastProp @-}
{-@ rankBeginLastProp :: {ts:Heap a | length ts > 1}
            -> {rank (last (begin ts)) < rank (last ts)} @-}
rankBeginLastProp :: Eq a => [BiTree a] -> Proof
rankBeginLastProp (t:[t']) = ()
rankBeginLastProp (t:ts) =
    rankBeginLastProp ts ??
    ()

{-@ reflect sumRankProp @-}
{-@ sumRankProp :: ts:[BiTree a] -> {treeListSize ts == sumRank ts} @-}
sumRankProp :: Ord a => [BiTree a] -> Proof
sumRankProp [] = ()
sumRankProp (t:ts) =
    pow2Prop t ??
    sumRankProp ts ??
    ()

{-@ reflect pow2Prop @-}
{-@ pow2Prop :: t:BiTree a -> {treeSize t == powerOfTwo (rank t)} @-}
pow2Prop :: Ord a => BiTree a -> Proof
pow2Prop t = pow2Lemma t ?? ()

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

{-@ reflect logPowP @-}
{-@ logPowP :: n:Nat -> {log2 (powerOfTwo n) == n} @-}
logPowP :: Int -> Proof
logPowP 0 = ()
logPowP n = logPowP (n-1) ?? ()

{-@ logPowP2 :: n:Nat -> {log2 (powerOfTwo n) == n} @-}
logPowP2 :: Int -> Proof
logPowP2 0 = log2 (powerOfTwo 0) === log2 1 === 0 ***QED
logPowP2 n = log2 (powerOfTwo n) 
    === log2 (2 * powerOfTwo (n-1)) 
    === 1 + log2 (powerOfTwo (n-1))  ? logPowP2 (n-1)
    === 1 + (n-1)
    === n
    ***QED

{-@ reflect logAddProp @-}
{-@ logAddProp :: x:Pos -> {log2 (2 * powerOfTwo x) = 1 + x} @-}
logAddProp :: Int -> Proof
logAddProp 1 = ()
logAddProp x = logPowP x ?? ()

{-@ reflect logMon @-}
{-@ logMon :: x:Pos -> {y:Pos | x <= y} -> {log2 x <= log2 y} @-}
logMon :: Int -> Int -> Proof
logMon x 1 = ()
logMon 1 y = (0 <= log2 y) ?? ()
logMon x y =
    logMon (div x 2) (div y 2) ??
    ()

{-@ reflect rankLeSumProp @-}
{-@ rankLeSumProp :: ts:NEBiTreeL a
        -> {powerOfTwo (rank (last ts)) <= sumRank ts} @-}
rankLeSumProp :: Ord a => [BiTree a] -> Proof
rankLeSumProp [t] = ()
rankLeSumProp (t:ts) =
    rankLeSumProp ts ??
    (0 <= powerOfTwo (rank t)) ??
    ()

{-@ reflect lenLeRankProp @-}
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

{-@ reflect lenLeLogProp @-}
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

{-
--------------------------------------------------------------------
-- TRUSTED CODE NV
--------------------------------------------------------------------
-- THIS IS TRUSTED CODE ABOUT AMORTISED BIND 
{-@ reflect abind @-}
{-@ abind :: c:Nat -> m:Nat -> x:Tick ({v:[a] | length v <= m - 1}) -> f:(fx:[a] -> {t:Tick {xs:[c] | length xs <= length fx + 1} | amortized t (pot (tval t)) (pot fx) <= c})
                 -> {ti:Tick {xs:[c] | length xs <= m}  | (tcost ti == c + tcost x ) && tval (f (tval x)) == tval ti && pot (tval ti) == length (tval ti) && length (tval ti) <= m } @-}
abind :: Int -> Int -> Tick [a] -> ([a] -> Tick [c]) -> Tick [c]
abind c _ (Tick c1 x) f = Tick (c + c1) y
    where Tick _ y = f x
-- END TRUSTED

-- THIS TOO IS TRUSTED LIBRARY CODE 
-- NV: Here the +1 comes because I tick! 
{-@ reflect ifTick @-}
{-@ ifTick :: c:Nat -> t:Tick a -> (a -> Bool) -> tb:(a -> {ti:Tick b | tcost ti <= c}) -> fb:(a -> {ti:Tick b | tcost ti <= c}) 
           -> {to:Tick b | (tcost to <= tcost t + c + 1) && (tval to == tval (tb (tval t)) || tval to == tval (fb (tval t))) } @-}
ifTick :: Int -> Tick a -> (a -> Bool) -> (a -> Tick b) -> (a -> Tick b) -> Tick b
ifTick _ (Tick c v) b t e = RTick.step (c + 1) (if b v then t v else e v)  
-- END OF TRUSTED CODE 
-}