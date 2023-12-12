{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--ple" @-}
{-@ infix : @-}

module MyBinomial 
    ( link
    --, insTree
    --, insert
    --, mergeTree
    --, mergeHeap
    --, removeMinTree
    --, findMin
   -- , deleteMin
    )
where
import Prelude hiding (length, head, min, last, (++), reverse, max)
import Language.Haskell.Liquid.ProofCombinators


{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[BiTree a] 
        -> {v:Nat | (length  xs <= v) && (v = 0 <=> length xs = 0) && (length xs > 0 <=> v > 0)} @-}
treeListSize :: Ord a => [BiTree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = treeSize x + treeListSize xs


{-@ type Pos = {n:Int | n >= 1} @-}
{-@ type NEList a = {xs:[a] | 0 < length xs} @-}
{-@ type NEHeap a = {h: Heap a | 0 < length (unheap h)} @-}

{-@ data Heap a = Heap { unheap :: {ts:[BiTree a] | ordRankH ts}} 
@-}
data Heap a = 
    Heap { unheap :: [BiTree a] }

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

{-@ reflect min @-}
min :: Ord a => a -> a -> a
min x1 x2
    | x1 <= x2 = x1
    | otherwise = x2

{-@ reflect link @-}
{-@ link :: t1:BiTree a -> {t2:BiTree a | rank t2 = rank t1} 
        -> {v:BiTree a | rank v = rank t1 + 1 
        && treeSize v = treeSize t1 + treeSize t2
        && root v = min (root t1) (root t2)} @-}
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

{-@ beginLastProp :: {ts:[BiTree a] | length ts > 0} 
            -> {begin ts ++ [last ts] == ts} @-}
beginLastProp :: Ord a => [BiTree a] -> Proof
beginLastProp [t] = ()
beginLastProp (t:ts) =
    beginLastProp ts ??
    () 

{-@ reflect max @-}
max :: Ord a => a -> a -> a
max x1 x2
    | x1 >= x2 = x1
    | otherwise = x2

{-@ reflect maxL @-}
{-@ maxL :: {ts:[BiTree a] | length ts > 0} -> Int @-}
maxL :: [BiTree a] -> Int
maxL [t] = rank t
maxL (t:ts)
    | rank t > maxL ts = rank t
    | otherwise = maxL ts

{-@ reflect minL @-}
{-@ minL :: {ts:[BiTree a] | length ts > 0} -> Int @-}
minL :: [BiTree a] -> Int
minL [t] = rank t
minL (t:ts)
    | rank t < minL ts = rank t
    | otherwise = minL ts


{-@ oRtoORHProp :: {ts:[BiTree a] | ordRank ts} -> {ordRankH (reverse ts)} @-}
oRtoORHProp :: Eq a => [BiTree a] -> Proof
oRtoORHProp [] = ()
oRtoORHProp [t] = ()
oRtoORHProp (t:ts) =
    oRtoORHProp ts ??
    maxLProp2 t ts ??
    maxLPropRev ts ??
    maxLProp1 (reverse ts) t ??
    ()

{-@ maxLProp1 :: {ts:[BiTree a] | ordRankH ts} -> {t:BiTree a | rank t > maxL ts}
        -> {ordRankH (ts ++ [t])} @-}
maxLProp1 :: Eq a => [BiTree a] -> BiTree a -> Proof
maxLProp1 [] t = ()
maxLProp1 [t'] t = ()
maxLProp1 (t':ts) t =
    (rank t > maxL (t':ts)) ??
    ordRankPropH2 t' ts ??
    maxLProp1 ts t ??
    ()

{-@ maxLProp2 :: t:BiTree a -> {ts:[BiTree a] | length ts > 0 && ordRank (t:ts)}
        -> {rank t > maxL ts} @-}
maxLProp2 :: Eq a => BiTree a -> [BiTree a] -> Proof
maxLProp2 t [t2] = ()
maxLProp2 t (t':ts) =
    maxLProp2 t' ts ??
    ()

{-@ maxLPropRev :: {ts:[BiTree a] | length ts > 0} 
            -> {maxL ts == maxL (reverse ts)}@-}
maxLPropRev :: Eq a => [BiTree a] -> Proof
maxLPropRev [t] = ()
maxLPropRev (t:ts) =
    maxLApp (reverse ts) [t] ??
    maxLPropRev ts ??
    (maxL (t:ts) == max (maxL ts) (rank t)) ?? 
    ()

{-@ maxLApp :: {ts1:[BiTree a] | length ts1 > 0} -> {ts2:[BiTree a] | length ts2 > 0}
            -> {maxL (ts1++ts2) == max (maxL ts1) (maxL ts2)}@-}
maxLApp :: Eq a => [BiTree a] -> [BiTree a] ->  Proof
maxLApp [t1] [t2] =
    (maxL (t1:[t2]) == max (rank t1) (rank t2)) ??
    ()
maxLApp [t1] ts = 
    (maxL (t1:ts) == max (rank t1) (maxL ts)) ?? 
    ()
maxLApp (t1:ts1) ts2
    | rank t1 > maxL (ts1++ts2) && maxL ts1 > maxL ts2 =
        maxLApp ts1 ts2 ??
        ()
    | rank t1 > maxL (ts1++ts2) && maxL ts1 < maxL ts2 =
        maxLApp ts1 ts2 ??
        ()
    | rank t1 > maxL (ts1++ts2) && maxL ts1 == maxL ts2 =
        maxLApp ts1 ts2 ??
        ()
    | rank t1 <= maxL (ts1++ts2) && maxL ts1 > maxL ts2 =
        maxLApp ts1 ts2 ??
        () 
    | rank t1 <= maxL (ts1++ts2) && maxL ts1 < maxL ts2 =
        maxLApp ts1 ts2 ??
        (maxL ((t1:ts1)++ts2) == max (maxL (t1:ts1)) (maxL ts2)) ??
        ()
    | rank t1 <= maxL (ts1++ts2) && maxL ts1 == maxL ts2 =
        maxLApp ts1 ts2 ??
        () 
    

{-@ reflect reverse @-}
{-@ reverse :: ts:[a] -> {vs:[a] | length ts == length vs} @-}
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

{-@ reflect rev @-}
rev :: [a] -> [a] -> [a]
rev [] ys = ys
rev (x:xs) ys = rev xs (x:ys)

{-@ reflect ordRankPropH @-}
{-@ ordRankPropH :: t:BiTree a 
            -> {ts:[BiTree a] | ordRankH ts && (length ts == 0 || rank t < getRank (head ts))}
            -> {ordRankH (t:ts)} @-}
ordRankPropH :: Ord a => BiTree a -> [BiTree a] -> Proof
ordRankPropH t [] = ()
ordRankPropH t [t'] = ()
ordRankPropH t (t':ts) = ()

{-@ reflect minLOrdProp @-}
{-@ minLOrdProp :: {ts:[BiTree a] | length ts > 0 && ordRankH ts} 
            -> {minL ts = rank (head ts)} @-}
minLOrdProp :: Eq a => [BiTree a] -> Proof
minLOrdProp [t] = ()
minLOrdProp (t:t':ts) = 
    minLOrdProp (t':ts) ??
    ()

{-@ reflect ordRankPropH2 @-}
{-@ ordRankPropH2 :: t:BiTree a 
            -> {ts:[BiTree a] | ordRankH (t:ts)}
            -> {ordRankH ts} @-}
ordRankPropH2 :: BiTree a -> [BiTree a] -> Proof
ordRankPropH2 t [] = ()
ordRankPropH2 t (t':ts) = ()

-- t:BiTree a -> ts: ordRankH (ts++t) -> ordRankH ts
{-@ ordRankBegin :: {ts:[BiTree a] | ordRankH ts && length ts > 0}
            -> {ordRankH (begin ts)} @-}
ordRankBegin :: (Eq a, Ord a) => [BiTree a] -> Proof
ordRankBegin [t] = ()
ordRankBegin (t:[t']) = () 
ordRankBegin (t:t':ts) =
    ordRankBegin (t':ts) ??
    ordRankH (begin (t':ts)) ??
    ordRankPropH t (begin (t':ts)) ??
    ()

{-@ maxBeginLastProp :: {ts:[BiTree a] | ordRankH ts && length ts > 1}
            -> {maxL (begin ts) < rank (last ts)} @-}
maxBeginLastProp :: Eq a => [BiTree a] -> Proof
maxBeginLastProp (t:[t']) = ()
maxBeginLastProp (t:t':ts) =
    rankMaxLProp t t' ts ??
    maxBeginLastProp (t':ts) ??
    (maxL (begin (t':ts)) < rank (last ts))??
    ()

{-@ lastMaxLProp :: {ts:[BiTree a] | ordRankH ts && length ts > 0}
        -> {maxL ts == rank (last ts)} @-}
lastMaxLProp :: Eq a => [BiTree a] -> Proof
lastMaxLProp [t] = ()
lastMaxLProp (t:t':ts)
    | rank t >= rank t' = ()
    | otherwise =
        rankMaxLProp t t' ts ??
        lastMaxLProp (t':ts) ?? 
        () 

{-@ rankMaxLProp :: t:BiTree a -> {t':BiTree a | rank t < rank t'} -> ts:[BiTree a]
            -> {rank t < maxL (t':ts)} @-}
rankMaxLProp :: Eq a => BiTree a -> BiTree a -> [BiTree a] -> Proof
rankMaxLProp t t' [] = ()
rankMaxLProp t t' ts
    | rank t' > maxL ts = ()
    | otherwise = ()


{-@ reflect insTree @-}
{-@ insTree :: t:BiTree a -> {ts:[BiTree a] | ordRankH ts} 
            -> {zs:[BiTree a]| length zs > 0 && length zs <= length ts + 1 
            && ordRankH zs && minL zs >= minL (t:ts)} @-}
insTree :: Ord a => BiTree a -> [BiTree a] -> [BiTree a]
insTree t [] = [t]
insTree t ts@(t':ts') 
    | rank t < rank t' = t : ts
    | rank t' < rank t =
        (minL ts == rank t') ??
        minLProp t' t ts' ??
        ordRankPropH2 t' ts' ??
        (minL (t' : insTree t ts') >= rank t') ??
        ordMinLProp t' (insTree t ts') ??
        t' : insTree t ts'
    | otherwise =
        ordRankPropH2 t' ts' ??
        minLOrdProp ts ??
        minLProp t' (link t t') ts' ??
        insTree (link t t') ts'

{-@ reflect ordMinLProp @-}
{-@ ordMinLProp :: t:BiTree a 
            -> {ts:[BiTree a] | ordRankH ts && rank t < minL ts} 
            -> {ordRankH (t:ts)} @-}
ordMinLProp :: Eq a => BiTree a -> [BiTree a] -> Proof
ordMinLProp t [] = ()
ordMinLProp t ts =
    ordMinLProp2 t ts ??
    ()

{-@ reflect ordMinLProp2 @-}   
{-@ ordMinLProp2 :: t:BiTree a 
            -> {ts:[BiTree a] | rank t < minL ts} 
            -> {length ts == 0 || rank t < rank (head ts)} @-}
ordMinLProp2 :: Eq a => BiTree a -> [BiTree a] -> Proof
ordMinLProp2 t [] = ()
ordMinLProp2 t (t':ts) =
    (rank t < minL (t':ts)) ??
    (rank t < rank t') ??
    () 

{-@ reflect minLProp @-}
{-@ minLProp :: t':BiTree a -> {t:BiTree a | rank t' < rank t} 
            -> {ts':[BiTree a] | ordRankH (t':ts')} 
            -> {rank t' < minL (t:ts')} @-}
minLProp :: Eq a => BiTree a -> BiTree a -> [BiTree a] -> Proof
minLProp t' t [] = ()
minLProp t' t ts' =
    (length ts' > 0) ??
    minLProp2 t' ts' ??
    assert (rank t' < minL (t:ts')) ??
    ()

{-@ reflect minLProp2 @-}
{-@ minLProp2 :: t:BiTree a -> {ts:[BiTree a] | ordRankH (t:ts)} 
            -> {length ts == 0 || minL ts > rank t} @-}
minLProp2 :: Eq a => BiTree a -> [BiTree a] -> Proof
minLProp2 t [] = ()
minLProp2 t [t'] = ()
minLProp2 t (t':ts) =
    minLProp2 t' ts ??
    ()

{-@ reflect minLProp3 @-}
{-@ minLProp3 :: t:BiTree a -> {t':BiTree a | rank t < rank t'} 
            -> {ts':[BiTree a] | ordRankH (t':ts')} 
            -> {rank t < minL (t':ts')} @-}
minLProp3 :: (Ord a,Eq a) => BiTree a -> BiTree a -> [BiTree a] -> Proof
minLProp3 t t' [] = ()
minLProp3 t t' ts' =
    ordRankPropH t (t':ts') ??
    minLProp2 t (t':ts') ??
     ()

{-@ reflect minLProp4 @-}
{-@ minLProp4 :: t:BiTree a -> {ts:[BiTree a]| length ts > 0} 
            -> {minL (t:ts) == min (rank t) (minL ts) } @-}
minLProp4 :: Eq a => BiTree a -> [BiTree a] -> Proof
minLProp4 t1 [t2]
    | rank t1 < rank t2 = () 
    | otherwise = 
        (minL (t1:[t2]) == min (rank t1) (minL [t2])) ?? 
        ()
minLProp4 t1 ts2@(t2:ts2') =
    minLProp4 t2 ts2' ??
    (minL (t1:ts2) == min (rank t1) (minL ts2)) ?? 
    () 

{-@ measure unlist @-}
{-@ unlist :: {t:[BiTree a]| length t = 1} -> BiTree a @-}
unlist :: [BiTree a] -> BiTree a
unlist [t] = t

{-@ reflect singleton @-}
singleton :: Ord a => a -> BiTree a
singleton x = Node 0 x [] 1

{-@ reflect insert @-}
{-@ insert :: a -> Heap a -> Heap a @-}
insert :: Ord a => a -> Heap a -> Heap a
insert x (Heap ts) = Heap (insTree (singleton x) ts)

{-@ reflect mergeTree @-}
{-@ mergeTree :: {ts1:[BiTree a] | ordRankH ts1} 
            -> {ts2:[BiTree a] | ordRankH ts2}
            -> {zs:[BiTree a] | length zs <= length ts1 + length ts2
               && ordRankH zs
               && (length ts1 == 0 || length ts2 == 0 || 
               (length zs > 0 && minL zs >= min (minL ts1) (minL ts2)))
               } @-}
mergeTree :: Ord a => [BiTree a] -> [BiTree a] -> [BiTree a]
mergeTree [] [] = []
mergeTree ts1 [] = ts1
mergeTree [] ts2 = ts2
mergeTree [t1] [t2]
    | rank t1 < rank t2 = t1 : [t2]
    | rank t2 < rank t1 = t2 : [t1]
    | otherwise = [link t1 t2]
mergeTree [t1] ts2@(t2:ts2')
    | rank t1 < rank t2 =
        ordRankPropH t1 ts2 ??
        minLOrdProp (t1:ts2) ??
        (rank t1 >= min (rank t1) (minL ts2)) ??
        t1 : ts2
    | rank t2 == rank t1 =
        minLProp2 t1 ts2' ??
        (minL (link t1 t2:ts2') >= rank t1) ??
        insTree (link t1 t2) ts2' 
mergeTree ts1@(t1:ts1') [t2]
    | rank t2 < rank t1 =
        ordRankPropH t2 ts1 ??
        minLOrdProp (t2:ts1) ??
        (rank t2 >= min (minL ts1) (rank t2)) ??
        t2 : ts1
    | rank t2 == rank t1 =
        minLProp2 t1 ts1' ??
        (minL (link t1 t2:ts1') >= rank t1) ??
        insTree (link t1 t2) ts1'
mergeTree ts1@(t1:ts1') ts2@(t2:ts2')
    | rank t1 < rank t2 =
        minLProp2 t1 ts1' ??
        minLProp3 t1 t2 ts2' ??
        (rank t1 < min (minL ts1') (minL ts2)) ??
        ordMinLProp t1 (mergeTree ts1' ts2) ??
        minLProp4 t1 (mergeTree ts1' ts2) ??
        t1 : mergeTree ts1' ts2
    | rank t2 < rank t1 =
        minLProp2 t2 ts2' ??
        minLProp3 t2 t1 ts1' ??
        (rank t2 < min (minL ts1) (minL ts2')) ??
        ordMinLProp t2 (mergeTree ts1 ts2') ??
        minLProp4 t2 (mergeTree ts1 ts2') ??
         t2 : mergeTree ts1 ts2'
    | otherwise =
        minLProp4 (link t1 t2) (mergeTree ts1' ts2') ??
        minLProp2 t1 ts1' ??
        minLProp2 t1 ts2' ??
        (rank t1 < min (minL ts1') (minL ts2')) ??
        insTree (link t1 t2) (mergeTree ts1' ts2')

{-@ reflect mergeHeap @-}
mergeHeap :: Ord a => Heap a -> Heap a -> Heap a
mergeHeap (Heap ts1) (Heap ts2) = Heap (mergeTree ts1 ts2)

{-@ removeMinTree :: {ts:[BiTree a] | length ts > 0 && ordRankH ts} 
            -> {tup:(t':BiTree a, {ts':[BiTree a] | 
            length ts' == length ts - 1 &&
            ordRankH ts' && 
            (length ts' == 0 || (minL ts' >= minL ts))}) |
            (length (snd tup) == 0 || (minL (snd tup) >= minL ts))} @-}
removeMinTree :: Ord a => [BiTree a] -> (BiTree a, [BiTree a])
removeMinTree [t] =
    ordRankH [] ??
    (t,[])
removeMinTree (t:[t'])
    | root t < root t' = (t,[t'])
    | otherwise =
        ordRankH [t] ??
        (minL [t] >= minL (t:[t'])) ?? 
        (t',[t])
removeMinTree (t:ts) =
    let (t', ts') = removeMinTree ts in
    minLProp2 t ts ??
    ordMinLProp t ts' ??
    if root t < root t' 
        then
            (minL ts >= minL (t:ts)) ??
            (t, ts) 
        else
            removeMinTree ts ??
            (minL (t:ts') >= minL (t:ts)) ??
            (t', t:ts')

{-@ findMin :: NEHeap a -> a @-}
findMin :: Ord a => Heap a -> a
findMin (Heap ts) = 
    let (t, _) = removeMinTree ts in root t

{-@ deleteMin :: NEHeap a -> Heap a @-}
deleteMin :: Ord a => Heap a -> Heap a
deleteMin (Heap ts) = let (Node _ x ts1 _, ts2) = removeMinTree ts in
    oRtoORHProp ts1 ??
    Heap (mergeTree (reverse ts1) ts2)


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

{-@ sumRankProp :: ts:[BiTree a] -> {treeListSize ts == sumRank ts} @-}
sumRankProp :: Ord a => [BiTree a] -> Proof
sumRankProp [] = ()
sumRankProp (t:ts) =
    pow2Prop t ??
    sumRankProp ts ??
    ()

{-@ logPowP :: n:Nat -> {log2 (powerOfTwo n) == n} @-}
logPowP :: Int -> Proof
logPowP 0 = ()
logPowP n = logPowP (n-1) ?? ()

{-@ logAddProp :: x:Pos -> {log2 (2 * powerOfTwo x) = 1 + x} @-}
logAddProp :: Int -> Proof
logAddProp 1 = ()
logAddProp x = logPowP x ?? ()

-- sum 2^rank_i >= 2^rank_n
-- deprecated
{-@ firstProp :: t:BiTree a -> ts:[BiTree a] -> {sumRank (t:ts) >= powerOfTwo (rank t)} @-}
firstProp :: Ord a => BiTree a -> [BiTree a] -> Proof
firstProp t ts = (sumRank ts >= 0) ?? ()

{-@ firstProp1 :: {ts:[BiTree a] | length ts > 0} 
        -> {powerOfTwo (rank (last ts)) <= sumRank ts} @-}
firstProp1 :: Ord a => [BiTree a] -> Proof
firstProp1 [t] = ()
firstProp1 (t:ts) =
    firstProp1 ts ??
    (0 <= powerOfTwo (rank t)) ??
    ()

{-@ logMon :: x:Pos -> {y:Pos | x <= y} -> {log2 x <= log2 y} @-}
logMon :: Int -> Int -> Proof
logMon x 1 = ()
logMon 1 y = (0 <= log2 y) ?? ()
logMon x y =
    logMon (div x 2) (div y 2) ??
    ()

-- length ts <= rank + 1
{-@ secondProp :: {ts:[BiTree a] | ordRankH ts && length ts > 0} 
            -> {length ts <= maxL ts + 1} @-}
secondProp :: Ord a => [BiTree a] -> Proof
secondProp [t] = (1 <= rank t + 1) ?? ()
secondProp (t:[t2]) =
    secondProp [t] ??
    ()
secondProp ts =
    ordRankBegin ts ??
    secondProp (begin ts) ??
    beginLastProp ts ??
    maxBeginLastProp ts ??
    maxLApp (begin ts) [last ts] ??
    (length ts <= rank (last ts) + 1) ??
    ()

{-@ finalProp :: {ts:[BiTree a] | ordRankH ts} 
            -> {length ts <= 1 + log2 (treeListSize ts)} @-}
finalProp :: (Eq a, Ord a) => [BiTree a] -> Proof
finalProp [] = ()
finalProp [t] = (1 <= 1 + log2 (treeSize t)) ?? () 
finalProp ts =
    lastMaxLProp ts ??
    secondProp ts ??
    logPowP (rank (last ts) + 1) ??
    logAddProp (rank (last ts)) ??
    logPowP (rank (last ts)) ??
    firstProp1 ts ??
    logMon (powerOfTwo (rank (last ts))) (sumRank ts) ??
    sumRankProp ts ??
    ()


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