-- Automatically generate singleton types for data constructors
--{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--exact-data-con" @-}
{-# LANGUAGE FlexibleContexts #-}
--{-@ LIQUID "--no-termination" @-}
{-@ infix : @-}

module PotentialAnalysis_FibHeap where
import Prelude hiding (pure, (++), (<*>), length, head, tail)
import Language.Haskell.Liquid.RTick as RTick
import Language.Haskell.Liquid.ProofCombinators
import GHC.Base (undefined)
import FibHeap_Props


{-@ type Pos = {v:Int | 0 < v} @-}
{-@ type NEFibHeap = {v : FibHeap a | notEmptyFibHeap v} @-}
{-@ type EFibHeap = {v : FibHeap a | not (notEmptyFibHeap v)} @-}
{-@ type AEqFibHeap t v = {b : Bool | rank t == rank v 
      && marked t == marked v && treeSize t == treeSize v 
      && AEqFibHeaps (subtrees t) (subtrees v) } @-}
{-@ type AEqFibHeaps ts vs = {b : Bool | length ts == length vs 
      && (length ts == 0 || (AEqFibHeaps (head ts) (head vs) 
      && AEqFibHeaps (tail ts) (tail vs)) )} @-}

{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[FibTree a] -> {v:Nat | (length  xs <= v) && (v = 0 <=> length xs = 0) && (length xs == 0 || v > 0)} @-}
treeListSize :: Ord a => [FibTree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = treeSize x + treeListSize xs

{-@
data FibTree [rank] a =
    Node
        { rank :: Pos
        , root :: a
        , subtrees :: {s:[FibTree a] | length s == 0 || (equalRank s && getRank (head s) = rank + 1)}
        , marked :: Bool
        , treeSize :: {v:Pos | v = 1 + treeListSize subtrees && v > 0}
        }
@-}

data FibTree a =
    Node
        { rank :: Int -- height of the tree starting from 1
        , root :: a -- the element
        , subtrees :: [FibTree a]
        , marked :: Bool
        , treeSize :: Int -- number of Nodes of the tree
    }

{-@ reflect getRank @-}
{-@ getRank :: t:FibTree a -> {v:Pos | v = rank t} @-}
getRank :: FibTree a -> Int
getRank t = rank t

{-@ reflect head @-}
{-@ head :: {t:[a] | length t > 0} -> a @-}
head (t:ts) = t

{-@ reflect tail @-}
{-@ tail :: {t:[a] | length t > 0} -> [a] @-}
tail (t:ts) = ts
-- , subtrees :: {s:[FibTree a] | equalRank s && rank (head s) = rank + 1}
-- treeSize
{-@ reflect equalRank @-}
{-@ equalRank :: [FibTree a] -> Bool @-}
equalRank :: Ord a => [FibTree a] -> Bool
equalRank [] = True
equalRank [t] = True
equalRank (t:t':ts) = rank t == rank t' && equalRank (t':ts)

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


-- O(1)
{-@ makeHeap :: {t:Tick EFibHeap | tcost t == 0} @-}
makeHeap :: Tick (FibHeap a)
makeHeap = pure E

{-@ predicate Rmin T = root (minTree T) @-}
-- O(1)

{-@ reflect singleton @-}
{-@ singleton :: x:a -> {ti:Tick NEFibHeap | markedNodes (tval ti) == 0 && tcost (singleton x) + poth (tval (singleton x)) - pota x = 1 && poth (tval ti) = 1} @-}
singleton :: a -> Tick (FibHeap a)
singleton x = wait (FH (Node 1 x [] False 1) [] 1 0)

-- O(1)
{-@ reflect link @-}
{-@ link :: t1:FibTree a-> {t2:FibTree a | rank t1 == rank t2} -> {t:Tick (v:FibTree a) | tcost t == 1} @-}
link :: (Ord a) => FibTree a -> FibTree a -> Tick (FibTree a)
link t1@(Node r x1 ts1 _ sz1) t2@(Node _ x2 ts2 _ sz2)
    | x1 <= x2 && length ts1 == 0 =
        wait (Node r x1 [increaseRank t2] False (1 + treeListSize [increaseRank t2]))
    | x1 <= x2 =
        (rank (increaseRank t2) == rank t1 + 1) ??
        (rank (increaseRank t2) == rank (head ts1)) ??
        equalRank ts1 ??
        eqRankProp (increaseRank t2) ts1 ??
        equalRank (increaseRank t2 : ts1) ??
        wait (Node r x1 (increaseRank t2:ts1) False (1 + treeListSize (increaseRank t2:ts1)))
    | length ts2 == 0 =
        wait (Node r x1 [increaseRank t1] False (1 + treeListSize [increaseRank t1]))
    | otherwise =
        (rank (increaseRank t1) == rank t2 + 1) ??
        (rank t2 + 1 == rank (head ts2)) ??
        (rank (increaseRank t1) == rank (head ts2)) ??
        equalRank ts2 ??
        eqRankProp (increaseRank t1) ts2 ??
        wait (Node r x2 (increaseRank t1:ts2) False (1 + treeListSize (increaseRank t1:ts2)))

{-@ reflect eqRankProp @-}
{-@ eqRankProp :: t:FibTree a 
      -> {ts1:[FibTree a] | length ts1 > 0 && equalRank ts1 && rank t == rank (head ts1)} 
      -> {equalRank (t:ts1)} @-}
eqRankProp :: FibTree a -> [FibTree a] -> Proof
eqRankProp t (t':ts) = ()
    --rank t == rank t1 && equalRank (t1:ts1) ***QED

{-@ reflect equalRankProp @-}
{-@ equalRankProp :: t:FibTree a -> {ts:[FibTree a] | equalRank (t:ts)} -> {equalRank ts} @-}
equalRankProp :: Ord a => FibTree a -> [FibTree a] -> Proof
equalRankProp t [] = ()
equalRankProp t [t'] = ()
equalRankProp t (t':ts) = ()

{-@ reflect getRankProp @-}
{-@ getRankProp :: t:FibTree a -> {ts:[FibTree a] | equalRank (t:ts)} 
      -> {r:Int | r == getRank t} -> {length ts == 0 || r == getRank (head ts)} @-}
getRankProp :: Ord a => FibTree a -> [FibTree a] -> Int -> Proof
getRankProp _ [] _ = ()
getRankProp t [t'] r = ()
getRankProp t (t':ts) r = ()

{-@ reflect increaseRank @-}
{-@ increaseRank :: t:FibTree a -> {v:FibTree a | rank v = rank t + 1} / [treeSize t] @-}
increaseRank :: (Ord a) => FibTree a -> FibTree a
increaseRank t@(Node r x [] m sz) = Node (r+1) x [] m sz
increaseRank t@(Node r x ts m sz) = 
  (treeListSize (subtrees t) < treeSize t) ??
  Node (r+1) x (increaseRank' (subtrees t) (r+1)) m (1 + treeListSize (increaseRank' (subtrees t) (r+1)))

{-@ reflect increaseRank' @-}
{-@ increaseRank' :: {ts:[FibTree a] | equalRank ts}
        -> {r:Int | length ts == 0 || r == getRank (head ts)}
        -> {vs:[FibTree a] | length vs == length ts && (length vs == 0
        || (equalRank vs && getRank (head vs) == r + 1))} / [treeListSize ts] @-}
increaseRank' :: (Ord a) => [FibTree a] -> Int -> [FibTree a]
increaseRank' [] _ = []
increaseRank' [t@(Node r x [] m sz)] _ = [Node (r+1) x [] m sz]
increaseRank' [t@(Node r x ts m sz)] _ = 
  (treeListSize (subtrees t) < treeSize t) ??
  [Node (r+1) x (increaseRank' (subtrees t) (r+1)) m (1 + treeListSize (increaseRank' (subtrees t) (r+1)))] 
increaseRank' (t:ts) r =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ??
  (length ts > 0) ??
 -- getRankProp t ts r ??
 -- rankEqProp (head ts) r ??
 -- eqRankProp t ts ??
 -- equalRank ts ??
 -- (rank (increaseRank t) == rank (head ts)) ??
  eqRankProp (increaseRank t) (increaseRank' ts r) ??
 -- equalRank (increaseRank t : increaseRank' ts r) ??
  increaseRank t : increaseRank' ts r

{-@ rankEqProp :: t:FibTree a -> {r:Int | r = rank t} -> {r == getRank t} @-}
rankEqProp :: FibTree a -> Int -> Proof
rankEqProp t r = ()

{-@ assume :: b:Bool -> {v:Bool | b } @-}
assume :: Bool -> Bool
assume x = undefined

{-@ reflect singl @-}
singl :: a -> [a]
singl x = [x]

{-@ reflect ?? @-}
{-@ (??) :: a -> y:b -> {v:b | v == y } @-}
(??) :: a -> b -> b
x ?? y = y

{-@ measure length @-}
length :: [a] -> Int
{-@ length :: xs:[a] -> {v:Nat | v = length xs} @-}
length [] = 0
length (_:xs) = 1 + length xs

{-@ reflect getNodes @-}
getNodes :: FibHeap a -> Int
getNodes E = 0
getNodes h = numNodes h

--{-@ reflect checkPot @-}
checkPot :: Ord a => FibHeap a -> Bool
checkPot h = numNodes h + 1 == 2^length (heapToList h)

{-@ measure poth @-}
{-@ poth :: h:FibHeap a -> {v:Nat | v == 0 && not notEmptyFibHeap h || v == length (trees h) + 1 + 2*markedNodes h}@-}
poth :: FibHeap a -> Int
poth E = 0
poth h = pot (trees h) + 1 + 2*markedNodes h

{-@ reflect pot @-}
{-@ pot :: xs:[a] -> {v: Nat | v = (length xs)} @-}
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
{-@ merge :: h1:(FibHeap a) -> h2:NEFibHeap-> {ti:Tick NEFibHeap | tcost (merge h1 h2) + (poth (tval (merge h1 h2))) - (poth h1 + poth h2) == 1} @-}
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
{-@ findMin :: h:NEFibHeap -> {ti:Tick a | tcost ti + pota (tval ti) - poth h <= 2} @-}
findMin :: (Ord a) => FibHeap a -> Tick a
findMin h = wait (root (minTree h))

-- geht t für ganze liste durch
-- O(log n) && numNod ts + 1 == powerOfTwo (lengthts)
{-@ reflect meld @-}
{-@ meld :: xs:[FibTree a] -> t:FibTree a -> {ti:Tick ({ts:[FibTree a] | length ts > 0 && length ts <= length xs + 1})| tcost (meld xs t) + pot (tval (meld xs t)) - (pot xs) - pota t <= pot xs && pot (tval (meld xs t)) <= pot xs + 1} @-}
meld :: Ord a => [FibTree a] -> FibTree a -> Tick [FibTree a]
meld [] t = pure [t]
meld (x:xs) t
  | rank x == rank t = step 1 (meld xs (tval (link t x)))
  | otherwise = pure ((:) x) <*> meld xs t

-- O(log n)
-- ruft meld mit jedem element auf
-- ACHTUNG! cheat weil kein pointer
{-@ reflect consolidate @-}
{-@ consolidate :: {xs:[FibTree a] | length xs > 0} -> {ti:Tick ({ts:[FibTree a] | length ts > 0 && length ts <= length xs}) | tcost (consolidate xs) + pot (tval (consolidate xs)) - pot xs <= pot xs && tcost (consolidate xs) <= pot xs && pot (tval (consolidate xs)) <= pot xs} @-}
consolidate :: (Ord a) => [FibTree a] -> Tick [FibTree a]
consolidate [x] = wait [x]
consolidate (x:xs) = Tick (1 + tcost (consolidate xs)) (tval (meld (tval (consolidate xs)) x))
--consolidate (x:xs) = RTick.wmap (help x) (consolidate xs)

-- O(length list)
{-@ reflect extractMin @-}
{-@ extractMin :: {ts:[FibTree a] | length ts > 0} -> {ti:Tick (FibTree a, {ts':[FibTree a] | length ts' <= length ts - 1}) | tcost ti + pott (tval ti) - pot ts <= pott (tval ti) && pott (tval ti) <= pot ts && tcost ti <= pot ts } @-}
extractMin :: (Ord a) => [FibTree a] -> Tick (FibTree a, [FibTree a])
extractMin [t] = wait (t, [])
extractMin (t:ts)
  | root t < root t' = Tick (1 + tcost f) (t, ts)
  | otherwise = Tick (1 + tcost f) (t', t:ts')
    where
        (t', ts') = tval f
        f = extractMin ts

-- O(log n)
{-@ deleteMin :: {h:NEFibHeap | not (marked (minTree h)) && numNodes h > 1 || (numNodes h == 1 && subtrees (minTree h) == [] && trees h == [])} -> ti:Tick (FibHeap a) @-}
deleteMin :: (Ord a) => FibHeap a -> Tick (FibHeap a)
deleteMin (FH (Node _ x [] _ _) [] _ _) = pure E
deleteMin h@(FH minTr ts n m) = let (minTr', ts') = tval (extractMin $ tval (consolidate (subtrees minTr ++ ts))) in
   deleteMin' h (minTr', ts')

{-
tcost ti <= pot (subtrees (minTree h)) + pot (trees h) &&
poth h <= pot (trees h) + 1 + 2*markedNodes h && 
poth (tval ti) <= pot ts' + 1 + 2*markedNodes h
-}
{-@ deleteMin' :: (Ord a) => {h:NEFibHeap | numNodes h > 1 && (length (subtrees (minTree h)) + length (trees h) > 0)} 
      -> {k:(FibTree a,[FibTree a])| pott k <= pot (subtrees (minTree h)) + pot (trees h) }
      -> {ti:Tick (FibHeap a) | tcost ti + poth (tval ti) - poth h <= 2 * pot (subtrees (minTree h)) + pot (trees h)} 
@-}
deleteMin' :: (Ord a) => FibHeap a -> (FibTree a ,[FibTree a]) -> Tick (FibHeap a)
deleteMin' h@(FH minTr ts n m) (minTr', ts') =
  Tick (tcost (extractMin $ tval (consolidate (subtrees minTr ++ ts)))) (FH minTr' ts' (n-1) m)

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {zs:[a] | length zs == length xs + length ys && pot zs == pot xs + pot ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)


{- all upcoming functions are just helper functions for DELETE
here delete is a tricky function because we do not have direct access via pointers 
we also ran into some termination issues that can be solved with help of cconst and assertions
-}

{-@ reflect assert @-}
{-@ assert :: b:{Bool | b } -> {v:Bool | b} @-}
assert :: Bool -> Bool
assert x = x

{-@ reflect compareRanks @-}
{-@ compareRanks :: ts:[FibTree a] -> {vs:[FibTree a] | length ts == length vs} -> {v:Bool | v ==> (length ts == 0 || rank (head ts) == rank (head vs))} @-}
compareRanks :: Ord a => [FibTree a] -> [FibTree a] -> Bool
compareRanks [] [] = True
compareRanks (t:ts) (v:vs) = rank t == rank v && compareRanks ts vs

-- returns heap where v is replaced by k
{-@ replace :: {ts:[FibTree a] | equalRank ts} -> a -> a 
        -> {r:Int | length ts == 0 || r == getRank (head ts)}
        -> {vs:[FibTree a] | length vs == length ts 
        && (length vs == 0 || getRank (head vs) == getRank (head ts)) 
        && equalRank vs && almostEq' ts vs} 
        / [treeListSize ts] 
@-}
-- length vs == length ts && (length vs == 0 || (equalRank vs && getRank (head vs) == r + 1))
replace :: Ord a => [FibTree a] -> a -> a -> Int -> [FibTree a]
replace [] v k r = []
replace [t@(Node r x [] mark sz)] v k r'
  | x == v = [Node r k [] mark sz]
  | otherwise = [t]
replace [t@(Node r x ts mark sz)] v k r'
  | x == v =
    almostEqProp t (Node r k ts mark sz) ??
    almostEqtoEqProp t (Node r k ts mark sz) ??
    [Node r k ts mark sz]
  | otherwise =
    equalRank (replace (subtrees t) v k (r+1)) ??
    (getRank (head (replace (subtrees t) v k (r+1))) == r + 1) ??
    almostEq' (subtrees t) (replace (subtrees t) v k (r+1)) ??
    (sz == (1 + treeListSize (replace (subtrees t) v k (r+1)))) ??
    [Node r x (replace (subtrees t) v k (r+1)) mark sz]
replace (t:ts) v k r = (0 < treeListSize ts) ??
      almostEq t (replace' t v k) ??
      almostEq' ts (replace ts v k r) ??
      eqRankProp (replace' t v k) (replace ts v k r) ??
      (replace' t v k : replace ts v k r)

{-@ replace' :: Ord a => t:FibTree a -> a -> a -> {v:FibTree a | almostEq t v} / [treeSize t]@-}
replace' :: Ord a => FibTree a -> a -> a -> FibTree a
replace' t@(Node r x [] mark sz) v k
  | x == v = eqProp t ?? Node r k [] mark sz
  | otherwise = t
replace' t@(Node r x ts mark sz) v k
  | x == v = eqProp t ?? Node r k ts mark sz
  | otherwise =
    (getRank (head (subtrees t)) == r + 1) ??
    almostEq' (subtrees t) (replace (subtrees t) v k (r+1)) ??
    (sz == 1 + treeListSize (replace (subtrees t) v k (r+1))) ??
    almostEq t (Node r x (replace (subtrees t) v k (r+1)) mark sz) ??
    Node r x (replace (subtrees t) v k (r+1)) mark sz

{-@ almostEqProp :: t:FibTree a 
      -> {v:FibTree a | rank t == rank v && subtrees t == subtrees v && marked t == marked v && treeSize t == treeSize v} 
      -> {almostEq t v} @-}
almostEqProp :: Ord a => FibTree a -> FibTree a -> Proof
almostEqProp t v =
  almostEq t v
  ? eqPropTs (subtrees t)
  ***QED

{-@ almostEqtoEqProp :: t:FibTree a 
      -> {v:FibTree a | almostEq t v} 
      -> {almostEq' (singl t) (singl v)} @-}
almostEqtoEqProp :: Ord a => FibTree a -> FibTree a -> Proof
almostEqtoEqProp t v =
  almostEq (head [t]) (head [v]) ??
  almostEq' [t] [v] 
  ***QED

{-@ eqProp :: t:FibTree a -> {almostEq' (subtrees t) (subtrees t)} /[treeSize t] @-}
eqProp :: Ord a => FibTree a -> Proof
eqProp t@(Node r x [] m sz) = ()
eqProp t =
  almostEq' (subtrees t) (subtrees t)
  ? eqPropTs (subtrees t)
  ***QED
  
{-@ eqPropT :: t:FibTree a -> {almostEq t t} / [treeSize t] @-}
eqPropT :: Ord a => FibTree a -> Proof
eqPropT t =
  (treeListSize (subtrees t) < treeSize t) ??
  almostEq t t 
  ? eqPropTs (subtrees t) 
  ***QED

{-@ eqPropTs :: ts:[FibTree a] -> {almostEq' ts ts} / [treeListSize ts] @-}
eqPropTs :: Ord a => [FibTree a] -> Proof
eqPropTs [] = ()
eqPropTs [t] = 
  (treeListSize (subtrees t) < treeSize t) ??
  almostEq t t 
  ? eqPropTs (subtrees t) 
  ***QED
eqPropTs (t:ts) =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ?? 
  almostEq' (t:ts) (t:ts)
  ? eqPropT t
  ? eqPropTs ts 
  ***QED
{-
{-@ eqProp2 :: t:FibTree a -> {v:FibTree a | almostEq t v} -> {almostEq' (singl t) (singl v)} @-}
eqProp2 :: Ord a => FibTree a -> FibTree a -> Proof
eqProp2 t v = 
  almostEq t v 
  === almostEq' (singl t) (singl v)
  ***QED
-}

{-@ reflect almostEq @-}
{-@ almostEq :: t:FibTree a -> v:FibTree a 
      -> {b:Bool | not b || rank t == rank v 
      && marked t == marked v && treeSize t == treeSize v 
      && almostEq' (subtrees t) (subtrees v)} / [treeSize t] @-}
almostEq t v
  | length (subtrees t) == length (subtrees v) =
      (treeListSize (subtrees t) < treeSize t) ??
      rank t == rank v
      && marked t == marked v && treeSize t == treeSize v
      && almostEq' (subtrees t) (subtrees v)
  | otherwise = False

-- equal except for root
{-@ reflect almostEq' @-}
{-@ almostEq' :: ts:[FibTree a] -> vs:[FibTree a] 
      -> {b:Bool | not b || length ts == length vs 
      && (length ts == 0 || (almostEq (head ts) (head vs) 
      && almostEq' (tail ts) (tail vs)
      && treeListSize ts == treeListSize vs))} / [treeListSize ts] 
      @-}
almostEq' :: Ord a => [FibTree a] -> [FibTree a] -> Bool
almostEq' [] [] = True
almostEq' [t] [v]
  | length (subtrees t) == length (subtrees v) =
      (treeListSize (subtrees t) < treeSize t) ??
      rank t == rank v
      && marked t == marked v && treeSize t == treeSize v
      && almostEq' (subtrees t) (subtrees v)
  | otherwise = False
almostEq' (t:ts) (v:vs)
  | length (subtrees t) == length (subtrees v) =
      (treeListSize (t:ts) < treeSize t) ??
      (treeListSize (subtrees t) < treeSize t) ??
      (treeListSize (t:ts) < treeListSize ts) ??
      rank t == rank v
      && marked t == marked v && treeSize t == treeSize v
      && almostEq' (subtrees t) (subtrees v)
      && almostEq' ts vs
  | otherwise = False
almostEq' _ _ = False


-- returns total number of nodes in the tree list
{-@ reflect numNod @-}
{-@ numNod :: Ord a => ts:[FibTree a] -> {v:Int | v >= length ts} / [treeListSize ts] @-}
numNod :: Ord a => [FibTree a] -> Int
numNod [] = 0
numNod [t] = (treeListSize (subtrees t) < treeSize t) ?? (1 + numNod (subtrees t))
numNod (t:ts) =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ??
  ((1 + numNod (subtrees t)) + numNod ts)

{-@ numNod' :: t:FibTree a -> {v:Int | v > 0} / [treeSize t] @-}
numNod' :: Ord a => FibTree a -> Int
numNod' t = (treeListSize (subtrees t) < treeSize t) ?? (1 + numNod (subtrees t))

-- retuns number of marked nodes in the tree list
{-@ markNod :: ts:[FibTree a] -> {v:Int | v >= 0} / [treeListSize ts]@-}
markNod :: Ord a => [FibTree a] -> Int
markNod [] = 0
markNod [t]
  | marked t = (treeListSize (subtrees t) < treeSize t) ?? (1 + markNod (subtrees t))
  | otherwise = (treeListSize (subtrees t) < treeSize t) ?? markNod (subtrees t)
markNod (t:ts) =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ??
  (markNod' t + markNod ts)

{-@ markNod' :: t:FibTree a -> {v:Int | v >= 0} / [treeSize t] @-}
markNod' :: Ord a => FibTree a -> Int
markNod' t
  | marked t = (treeListSize (subtrees t) < treeSize t) ?? (1 + markNod (subtrees t))
  | otherwise = (treeListSize (subtrees t) < treeSize t) ?? markNod (subtrees t)

-- checks if tree t contain element k
{-@ reflect contains @-}
{-@ contains :: t:FibTree a -> FibTree a -> Bool / [treeSize t] @-}
contains :: (Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> Bool
contains t t2 = t == t2 || containsL (subtrees t) t2

{-@ reflect containsL @-}
{-@ containsL :: ts:[FibTree a] -> FibTree a -> Bool / [treeListSize ts] @-}
containsL :: (Eq (FibTree a), Ord a) =>  [FibTree a] -> FibTree a -> Bool
containsL [] _ = False
containsL [t] t2 = (treeListSize (subtrees t) < treeSize t) ?? (root t == root t2 || containsL (subtrees t) t2)
containsL (t:ts) t2 =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ??
  (t == t2 || containsL (subtrees t) t2) || containsL ts t2

{-@ test :: {t:FibTree a | not (subtrees t == [])} -> Bool @-}
test :: Ord a => FibTree a -> Bool
test t = True

-- checks if one of the subtrees of ts contains t2 in the root
{-@ reflect checkSubRoots2 @-}
checkSubRoots2 :: (Eq (FibTree a), Ord a) =>  [FibTree a] -> FibTree a -> Bool
checkSubRoots2 [] _ = False
checkSubRoots2 (t:ts) t2 = t == t2 || checkSubRoots2 ts t2

-- returns parent tree of k
{-@ getParent :: t:FibTree a -> {t2:FibTree a | contains t t2} -> {vs:[FibTree a] | length vs <= 1} / [treeSize t] @-}
getParent ::(Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> [FibTree a]
getParent t t2
  | t == t2 = []
  | checkSubRoots2 (subtrees t) t2 = [t]
  | otherwise =
    (treeListSize (subtrees t) < treeSize t) ??
    getParent' (subtrees t) t2

{-@ getParent' :: ts:[FibTree a] -> t2:FibTree a -> {vs:[FibTree a]| length vs <= 1} / [treeListSize ts] @-}
getParent' :: (Eq (FibTree a), Ord a) =>  [FibTree a] -> FibTree a -> [FibTree a]
getParent' [] _ = []
getParent' [t] t2
  | checkSubRoots2 (subtrees t) t2 = [t]
  | otherwise = (treeListSize (subtrees t) < treeSize t) ?? getParent' (subtrees t) t2
getParent' (t:ts) t2
  | contains t t2 =
    (0 < treeListSize ts) ??
    (treeSize t < treeListSize (t:ts)) ??
    getParent t t2
  | otherwise =
    (0 < treeListSize ts) ??
    (treeSize t < treeListSize (t:ts)) ??
    getParent' ts t2

{-@ getParentMaybe :: Ord a => t:FibTree a -> t2:{FibTree a | contains t t2}
                   -> Maybe ({v:FibTree a | getDepth t v <= getDepth t t2 }) / [treeSize t] @-}
getParentMaybe :: (Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> Maybe (FibTree a)
getParentMaybe t t2
  | root t == root t2 = Nothing
  | checkSubRoots2 (subtrees t) t2 = Just ((getDepth t t <= getDepth t t2) ?? t)
  | otherwise = (treeListSize (subtrees t) < treeSize t) ??
                (getDepth t t2 ?? propPostFixId (subtrees t) ??
                getParentMaybe' t (subtrees t) t2)

{-@ getParentMaybe' :: g:FibTree a -> ts:{[FibTree a] | isPostFix ts (subtrees g)} 
                    -> t2:{FibTree a | contains g t2 && 0 < getDepth g t2} 
                    -> Maybe ({v:FibTree a | getDepth g v <= getDepth g t2 }) 
                    / [treeListSize ts] @-}
getParentMaybe' :: (Eq (FibTree a), Ord a) => FibTree a -> [FibTree a] -> FibTree a -> Maybe (FibTree a)
getParentMaybe' _ [] _ = Nothing
getParentMaybe' g [t] t2
  | g == t = Nothing
  | checkSubRoots2 (subtrees t) t2
  = Just (propParentChildDepth2 g t ?? t)
  | g == t2 = Nothing
  | otherwise
  = (treeListSize (subtrees t) < treeSize t) ??
    containsProp2 g t t2 ??
    (contains t t2) ??
    depthProp2 g t t2 ??
    (0 < getDepth t t2) ??
    propPostFixId (subtrees t) ??
    checkProp g t t2
      (getParentMaybe' t (subtrees t) t2 )
getParentMaybe' g (t:ts) t2
  | g == t = Nothing
  | contains t t2 =
    (0 < treeListSize ts) ??
    (treeSize t < treeListSize (t:ts)) ??
    checkProp2 g t ts t2 (getParentMaybe t t2)
     -- ::  Maybe ({v:FibTree a | getDepth t v <= getDepth t t2 })
  | otherwise =
    (0 < treeListSize ts) ??
    (treeSize t < treeListSize (t:ts)) ??
    postFixProp t ts (subtrees g) ??
    (isPostFix ts (subtrees g)) ??
    getParentMaybe' g ts t2

-- example xs=[1,3] ys=[1,2,3]
{-@ reflect isPostFix @-}
{-@ isPostFix :: xs:[a] -> ys:[a] -> Bool / [length ys] @-}
isPostFix :: Eq a => [a] -> [a] -> Bool
isPostFix (x:xs) (y:ys)
  | x == y    = isPostFix xs ys
  | length xs > length ys = False
  | otherwise = isPostFix (x:xs) ys
isPostFix [] _ = True
isPostFix _ [] = False

propPostFixId :: [a] -> ()
{-@ propPostFixId :: x:[a] -> {isPostFix x x} @-}
propPostFixId [] = ()
propPostFixId (x:xs) = propPostFixId xs


checkProp' :: (Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> FibTree a -> ()
{-@ checkProp' :: g:FibTree a -> t:{FibTree a | isPostFix (singl t) (subtrees g) } 
              -> t2:FibTree a 
              -> {getDepth t t2 == getDepth g t2 + 1 }  @-}
checkProp' g t t2
  | g == t2 = undefined
   -- getDepth g t2 + 1 === 1 === 1 + getDepth' (subtrees g) t ? propPostFixDepth' (subtrees g) t === getDepth t t2 ***QED
  | otherwise = undefined


checkProp :: (Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> FibTree a -> Maybe (FibTree a)  -> Maybe (FibTree a)
{-@ checkProp :: g:FibTree a -> t:{FibTree a |  isPostFix (singl t) (subtrees g) } -> t2:FibTree a 
              -> m:Maybe ({v:FibTree a | getDepth t v <= getDepth t t2  }) 
              -> {v:Maybe ({v:FibTree a | getDepth g v <= getDepth g t2 }) | v == m }  @-}
checkProp _ _ _ Nothing = Nothing
checkProp g t t2 (Just x) = checkProp' g t x ?? checkProp' g t t2  ?? Just x

{-@ containsProp2 :: g:FibTree a -> {t:FibTree a | isPostFix (singl t) (subtrees g)} 
          -> {t2:FibTree a | contains g t2} -> {contains t t2}
@-}
containsProp2 :: FibTree a -> FibTree a -> FibTree a -> ()
containsProp2 = undefined

{-@ depthProp2 :: g:FibTree a -> {t:FibTree a | g /= t && isPostFix (singl t) (subtrees g)}
          -> {t2:FibTree a | 0 < getDepth g t2} -> {0 < getDepth t t2} @-}
depthProp2 :: FibTree a -> FibTree a -> FibTree a -> ()
depthProp2 = undefined


{-@ postFixProp :: t:FibTree a -> ts:[FibTree a] 
        -> {gs:[FibTree a] | isPostFix (t:ts) gs}
        -> {isPostFix ts gs} / [length ts + length gs]@-}
postFixProp :: Eq (FibTree a) => FibTree a -> [FibTree a] -> [FibTree a] -> ()
postFixProp _ [] _ = ()
postFixProp _ _ [] = ()
postFixProp t ts (g:gs)
  | t == g = isPostFix ts gs ? postFixProp2 ts g gs ***QED -- isPostFix ts gs'
  | length ts >= length (g:gs) = ()
  | otherwise = undefined -- isPostFix (t:ts) gs'

{-@ postFixProp2 :: ts:[FibTree a] -> g:FibTree a
        -> {gs:[FibTree a] | isPostFix ts gs}
        -> {isPostFix ts (g:gs)} / [length ts + length gs] @-}
postFixProp2 :: Eq (FibTree a) => [FibTree a] -> FibTree a -> [FibTree a] -> Proof
postFixProp2 [] _ _ = ()
-- postFixProp2 ts g gs = length ts <= length (g:gs) ? (isPostFix ts gs) *** QED
-- postFixProp2 _ _ _ = undefined
postFixProp2 (t:ts) g gs
  | t == g = isPostFix (t:ts) (g:gs) === isPostFix ts gs ? postFixProp t ts gs *** QED
  | length ts >= length (g:gs) = undefined
  | otherwise = undefined

checkProp2 :: FibTree a -> FibTree a -> [FibTree a] -> FibTree a -> Maybe (FibTree a)  -> Maybe (FibTree a)
{-@ checkProp2 :: g:FibTree a -> t:FibTree a -> ts:{[FibTree a] |  isPostFix (t:ts) (subtrees g) } -> t2:FibTree a 
              -> m:Maybe ({v:FibTree a | getDepth t v <= getDepth t t2  }) 
              -> {v:Maybe ({v:FibTree a | getDepth g v <= getDepth g t2 }) | v == m }  @-}
checkProp2 = undefined



-- returns depth of root of t2 which is a subtree of t
{-@ reflect getDepth @-}
{-@ getDepth :: t:FibTree a -> {t2:FibTree a | contains t t2} 
             -> {v:Nat | (v = 0 <=> t == t2) &&  getDepth t t2 >= getDepth t t} / [treeSize t] @-}
getDepth :: (Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> Int
getDepth t t2
  | t == t2 = 0
  | otherwise = 1 + getDepth' (subtrees t) t2

{-@ propParentChildDepth :: t:FibTree a -> a:{FibTree a |  (singl a) == (subtrees t)}
      -> { getDepth t a  <= 1 } @-}
propParentChildDepth :: (Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> ()
propParentChildDepth t a
  | t == a = ()
  | otherwise
  = getDepth t a === 1 + getDepth' (subtrees t) a *** QED

{-@ propParentChildDepth2 :: t:FibTree a -> a:{FibTree a | isPostFix (singl a) (subtrees t)}
      -> { getDepth t a  <= 1 } @-}
propParentChildDepth2 :: (Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> ()
propParentChildDepth2 t a
  | t == a = ()
  | otherwise
  = containsProp t a ?? getDepth t a
  === propPostFixDepth' (subtrees t) a ?? 1 + getDepth' (subtrees t) a *** QED

{-@ propPostFixDepth' :: ts:[FibTree a] -> {a:FibTree a | isPostFix (singl a) ts}
      -> {getDepth' ts a == 0} @-}
propPostFixDepth' :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> ()
propPostFixDepth' [t] a
  | root t == root a = ()
  | otherwise = ()
  *** QED
propPostFixDepth' (t:ts) a
  | root t == root a = ()
  | containsL ts a = propPostFixDepth' ts a ?? ()
  | otherwise = propPostFixRoot ts a ?? ()

{-@ propPostFixRoot :: ts:[FibTree a] -> {a:FibTree a | isPostFix (singl a) ts} 
      ->  {containsL ts a} @-}
propPostFixRoot :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> ()
propPostFixRoot [] _ = ()
propPostFixRoot [t] a
  | t == a = ()
  | otherwise = ()
  *** QED
propPostFixRoot (t:ts) a
  | t == a = ()
  | otherwise = propPostFixRoot ts a ?? ()

{-@ containsProp :: t:FibTree a -> a:{FibTree a | isPostFix (singl a) (subtrees t)}
      -> { contains t a} @-}
containsProp :: (Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> ()
containsProp t a
  | a == t = ()
  | otherwise = containsLProp (subtrees t) a ?? ()

{-@ containsLProp :: ts:[FibTree a] -> a:{FibTree a | isPostFix (singl a) ts}
      -> {containsL ts a}@-}
containsLProp :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> ()
containsLProp [] _ = ()
containsLProp [t] a
  | t == a = ()
  | otherwise = ()
  *** QED
containsLProp (t:ts) a
  | t == a = ()
  | otherwise = containsLProp ts a ?? ()


{-@ reflect getDepth' @-}
{-@ getDepth' :: ts:[FibTree a] -> {t2:FibTree a | containsL ts t2} 
              -> {v:Nat | v >= 0 && getDepth' ts t2 >= getDepth' ts (head ts)} / [treeListSize ts] @-}
getDepth' :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> Int
getDepth' [t] t2
  | root t == root t2 = 0
  | otherwise = (treeListSize (subtrees t) < treeSize t) ??
                (1 + getDepth' (subtrees t) t2)
getDepth' (t:ts) t2
  | root t == root t2 = 0
  | containsL ts t2 =
    (0 < treeListSize ts) ??
    (treeSize t < treeListSize (t:ts)) ??
    getDepth' ts t2
  | otherwise =
    (0 < treeListSize ts) ??
    (treeSize t < treeListSize (t:ts)) ??
    (1 + getDepth' (subtrees t) t2)

-- returns subtree with root k
{-@ getTreeList ::  t:FibTree a -> a -> [FibTree a] / [treeSize t] @-}
getTreeList ::  Ord a => FibTree a -> a -> [FibTree a]
getTreeList t k
  | root t == k = [t]
  | otherwise = (treeListSize (subtrees t) < treeSize t) ?? getTreeList' (subtrees t) k

{-@ getTreeList' :: ts:[FibTree a] -> a -> [FibTree a] / [treeListSize ts] @-}
getTreeList' :: Ord a => [FibTree a] -> a -> [FibTree a]
getTreeList' [] k = []
getTreeList' [t] k
  | root t == k = [t]
  | otherwise = (treeListSize (subtrees t) < treeSize t) ?? getTreeList' (subtrees t) k
getTreeList' (t:ts) k =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ??
  (getTreeList t k ++ getTreeList' ts k)

  {-@ reflect heapToList @-}
{-@ heapToList :: h:FibHeap a -> {vs:[FibTree a] | not notEmptyFibHeap h || length vs > 0} @-}
heapToList :: FibHeap a -> [FibTree a]
heapToList E = []
heapToList h = minTree h : trees h

{-@ listToHeap :: ts:[FibTree a] -> {h:FibHeap a | notEmptyFibHeap h || length ts == 0}  @-}
listToHeap :: Ord a => [FibTree a] -> FibHeap a
listToHeap [] = E
listToHeap ts = FH (fst newH) (snd newH) (numNod ts) (markNod ts)
   where newH = tval (extractMin ts)


{-
-- returns tree with deleted subtree of root k
deleteSubTree :: Ord a => FibTree a -> a -> [FibTree a]
deleteSubTree t k
  | root t == k = []
  | otherwise = [Node (rank t) (root t) subtrs (marked t) (1 + treeListSize subtrs)]
    where subtrs = deleteSubTree' t (subtrees t) k

{-@ deleteSubTree' :: p:FibTree a -> {ts:[FibTree a] | length ts == 0 || getRank (head ts) = rank p - 1} -> a -> {vs:[FibTree a] | length vs == 0 || getRank (head vs) = rank p - 1} / [treeListSize ts] @-}
deleteSubTree' :: Ord a => FibTree a -> [FibTree a] -> a -> [FibTree a]
deleteSubTree' p [] k = []
deleteSubTree' p (t@(Node r x sub mk sz):ts) k
  | x == k = []
  | otherwise = Node r x (deleteSubTree' t sub k) mk (1 + treeListSize (deleteSubTree' t sub k)) : deleteSubTree' t ts k



-- remove x from current position and add it unmarked to root list
{-@ cut :: p:FibTree a -> ts:[FibTree a] -> FibTree a -> {vs:[FibTree a] | length vs > 0} @-}
cut :: Ord a => FibTree a -> [FibTree a] -> FibTree a -> [FibTree a]
cut p ts x = unmarkNode x : deleteSubTree' p ts (root x)

-- unmarks root node
unmarkNode :: Ord a => FibTree a -> FibTree a
unmarkNode t@(Node _ _ _ False _) = t
unmarkNode t@(Node r x ts True sz) = Node r x ts False sz

-- checks if node with root k is unmarked
isUnmarked :: Ord a => [FibTree a] -> a -> Bool
isUnmarked [] k = False
isUnmarked (t@(Node r x sub mk sz):ts) k
  | x == k = mk == False
  | otherwise = isUnmarked sub k || isUnmarked ts k

-- marks node with value k in heap h
{-@ mark' :: ts:[FibTree a] -> a -> {vs:[FibTree a] | length ts > 0 <=> length vs > 0} / [treeListSize ts] @-}
mark' :: Ord a => [FibTree a] -> a -> [FibTree a]
mark' [] _ = []
mark' [Node r x sub mk sz] k
  | x == k = [Node r x sub True sz]
  | otherwise = [Node r x (mark' sub k) mk (1 + treeListSize (mark' sub k))]
mark' (t@(Node r x sub mk sz):ts) k
  | x == k = Node r x sub True sz : ts
  | otherwise = Node r x (mark' sub k) mk (1 + treeListSize (mark' sub k)) : mark' ts k


{-@ cascadingCut :: [FibTree a] -> t:FibTree a -> FibTree a / [getDepth t] @-}
cascadingCut :: Ord a => [FibTree a] -> FibTree a -> FibTree a
cascadingCut ts y
  | getParentMaybe' ts y == Nothing = ts
  | isUnmarked ts (root y) = mark' ts (root y)
  | otherwise =
     --(getDepth' ts (getParentMaybe' ts y)) < getDepth' ts y ??
    cascadingCut (cut ts y) (getParentMaybe' ts y) -- termination (getParent' ts y) < y


----------------------------------------------------------------------------------------
-- without termination
------------------------------------------------------------------------------------
{-@ cascadingCut :: {ts:[FibTree a] | length ts > 0} -> t:FibTree a -> {vs:[FibTree a] | length vs > 0} @-} -- / [getdepth t]
cascadingCut :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> [FibTree a]
cascadingCut ts y
  | length (getParent' ts y) > 0 && isUnmarked ts (root y) = mark' ts (root y)
  | length (getParent' ts y) > 0 = 
 --   (getDepth' ts (head (getParent' ts y)) < getDepth' ts y) ?? 
    cascadingCut (cut ts y) (head (getParent' ts y)) -- termination (getParent' ts y) < y
  | otherwise = ts

{-@ performCuts :: {ts:[FibTree a] | length ts > 0} -> a -> {vs:[FibTree a] | length vs > 0} @-}
performCuts :: (Eq (FibTree a), Ord a) => [FibTree a] -> a -> [FibTree a]
performCuts ts k = if not (null x) && not (null y)
    then if k < root (head y)
        then cascadingCut (cut ts (head x)) (head y)
        else ts
    else ts
    where y = if not (null x) then getParent' ts (head x) else []
          x = getTreeList' ts k

-- O(1) with pointer
-- decreases root of v to k
{-@ decreasekey :: Ord a => NEFibHeap -> v:a -> a -> NEFibHeap @-}
decreasekey :: (Eq (FibTree a), Ord a) => FibHeap a -> a -> a -> FibHeap a
decreasekey h v k = if k < v then listToHeap (performCuts (replace (heapToList h) v k) k) else h

-- deletes note with root v from h
{-@ delete :: NEFibHeap -> a -> FibHeap a @-}
delete :: (Eq (FibTree a), Num a, Ord a) => FibHeap a -> a -> FibHeap a
delete h v = listToHeap (snd (tval (extractMin (heapToList (decreasekey h v 0))))) 
-}
