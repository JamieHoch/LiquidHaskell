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
import Data.Maybe (fromJust, isJust, isNothing)


{-@ type Pos = {v:Int | 0 < v} @-}
{-@ type NEFibHeap = {v : FibHeap a | notEmptyFibHeap v} @-}
{-@ type EFibHeap = {v : FibHeap a | not (notEmptyFibHeap v)} @-}

{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[FibTree a] 
        -> {v:Nat | (length  xs <= v) && (v = 0 <=> length xs = 0) && (length xs == 0 || v > 0)} @-}
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
            , markedNodes :: Nat
            }
@-}
data FibHeap a = E | FH { minTree :: FibTree a
                        , trees :: [FibTree a] --wihout minTree
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
{-@ singleton :: x:a -> {ti:Tick NEFibHeap | markedNodes (tval ti) == 0 && 
        tcost (singleton x) + poth (tval (singleton x)) - pota x = 1 && poth (tval ti) = 1} @-}
singleton :: a -> Tick (FibHeap a)
singleton x = wait (FH (Node 1 x [] False 1) [] 0)

-- O(1)
{-@ reflect link @-}
{-@ link :: t1:FibTree a-> {t2:FibTree a | rank t1 == rank t2} 
        -> {t:Tick (v:FibTree a) | tcost t == 1} @-}
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
  eqRankProp (increaseRank t) (increaseRank' ts r) ??
  increaseRank t : increaseRank' ts r

{-@ reflect singl @-}
singl :: a -> [a]
singl x = [x]

{-@ measure length @-}
length :: [a] -> Int
{-@ length :: xs:[a] -> {v:Nat | v = length xs} @-}
length [] = 0
length (_:xs) = 1 + length xs

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

-- O(1)
{-@ reflect merge @-}
{-@ merge :: h1:(FibHeap a) -> h2:NEFibHeap-> {ti:Tick NEFibHeap | tcost (merge h1 h2) + (poth (tval (merge h1 h2))) - (poth h1 + poth h2) == 1} @-}
merge:: (Ord a) => FibHeap a -> FibHeap a -> Tick (FibHeap a)
merge E h = wait h
merge h1@(FH minTr1 ts1 mark1) h2@(FH minTr2 ts2 mark2)
    | root minTr1 < root minTr2 = wait (FH minTr1 (minTr2:ts2++ts1) (mark1 + mark2))
    | otherwise = wait (FH minTr2 (minTr1:ts1++ts2) (mark1 + mark2))

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
{-@ deleteMin :: {h:NEFibHeap | not (marked (minTree h)) || (subtrees (minTree h) == [] && trees h == [])} -> ti:Tick (FibHeap a) @-}
deleteMin :: (Ord a) => FibHeap a -> Tick (FibHeap a)
deleteMin (FH (Node _ x [] _ _) [] _) = pure E
deleteMin h@(FH minTr ts m) = let (minTr', ts') = tval (extractMin $ tval (consolidate (subtrees minTr ++ ts))) in
   deleteMin' h (minTr', ts')

{-
tcost ti <= pot (subtrees (minTree h)) + pot (trees h) &&
poth h <= pot (trees h) + 1 + 2*markedNodes h && 
poth (tval ti) <= pot ts' + 1 + 2*markedNodes h
-}
{-@ deleteMin' :: (Ord a) => {h:NEFibHeap | (length (subtrees (minTree h)) + length (trees h) > 0)} 
      -> {k:(FibTree a,[FibTree a])| pott k <= pot (subtrees (minTree h)) + pot (trees h) }
      -> {ti:Tick (FibHeap a) | tcost ti + poth (tval ti) - poth h <= 2 * pot (subtrees (minTree h)) + pot (trees h)} 
@-}
deleteMin' :: (Ord a) => FibHeap a -> (FibTree a ,[FibTree a]) -> Tick (FibHeap a)
deleteMin' h@(FH minTr ts m) (minTr', ts') =
  Tick (tcost (extractMin $ tval (consolidate (subtrees minTr ++ ts)))) (FH minTr' ts' m)

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {zs:[a] | length zs == length xs + length ys && pot zs == pot xs + pot ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)


{- all upcoming functions are just helper functions for DELETE
here delete is a tricky function because we do not have direct access via pointers and
because of termination of cascadingCut

LEBENSRETTER zum Debuggen
{-@ assume :: b:Bool -> {v:Bool | b } @-}
assume :: Bool -> Bool
assume x = undefined

{-@ reflect assert @-}
{-@ assert :: b:{Bool | b } -> {v:Bool | b} @-}
assert :: Bool -> Bool
assert x = x
-}

{-@ reflect ?? @-}
{-@ (??) :: a -> y:b -> {v:b | v == y } @-}
(??) :: a -> b -> b
x ?? y = y

-- returns heap where v is replaced by k
{-@ replace :: {ts:[FibTree a] | equalRank ts} -> a -> a
        -> {vs:[FibTree a] | length vs == length ts 
        && (length vs == 0 || getRank (head vs) == getRank (head ts)) 
        && equalRank vs && sameRkSz' ts vs} 
        / [treeListSize ts] 
@-}
replace :: Ord a => [FibTree a] -> a -> a -> [FibTree a]
replace [] _ _ = []
replace [t@(Node r x [] mk sz)] v k
  | x == v = [Node r k [] mk sz]
  | otherwise = [t]
replace [t@(Node r x ts mk sz)] v k
  | x == v =
    rkSzProp' (subtrees t) ??
    [Node r k ts mk sz]
  | otherwise =
    sameRkSz' (subtrees t) (replace (subtrees t) v k) ??
    [Node r x (replace (subtrees t) v k) mk sz]
replace (t:ts) v k = (0 < treeListSize ts) ??
      sameRkSz t (replace' t v k) ??
      sameRkSz' ts (replace ts v k) ??
      eqRankProp (replace' t v k) (replace ts v k) ??
      (replace' t v k : replace ts v k)

{-@ replace' :: Ord a => t:FibTree a -> a -> a -> {v:FibTree a | sameRkSz t v} / [treeSize t]@-}
replace' :: Ord a => FibTree a -> a -> a -> FibTree a
replace' t@(Node r x [] mk sz) v k
  | x == v = rkSzProp t ?? Node r k [] mk sz
  | otherwise = t
replace' t@(Node r x ts mk sz) v k
  | x == v = rkSzProp t ?? Node r k ts mk sz
  | otherwise =
    (getRank (head (subtrees t)) == r + 1) ??
    sameRkSz' (subtrees t) (replace (subtrees t) v k) ??
    Node r x (replace (subtrees t) v k) mk sz

{-@ rkSzProp :: t:FibTree a -> {sameRkSz t t} / [treeSize t] @-}
rkSzProp :: Ord a => FibTree a -> Proof
rkSzProp t =
  (treeListSize (subtrees t) < treeSize t) ??
  sameRkSz t t
  ? rkSzProp' (subtrees t)
  ***QED

{-@ rkSzProp' :: ts:[FibTree a] -> {sameRkSz' ts ts} / [treeListSize ts] @-}
rkSzProp' :: Ord a => [FibTree a] -> Proof
rkSzProp' [] = ()
rkSzProp' [t] =
  (treeListSize (subtrees t) < treeSize t) ??
  sameRkSz t t
  ? rkSzProp' (subtrees t)
  ***QED
rkSzProp' (t:ts) =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ??
  sameRkSz' (t:ts) (t:ts)
  ? rkSzProp t
  ? rkSzProp' ts
  ***QED

{-@ reflect sameRkSz @-}
{-@ sameRkSz :: t:FibTree a -> v:FibTree a 
      -> {b:Bool | not b || rank t == rank v 
      && treeSize t == treeSize v 
      && sameRkSz' (subtrees t) (subtrees v)} / [treeSize t] @-}
sameRkSz t v
  | length (subtrees t) == length (subtrees v) =
      (treeListSize (subtrees t) < treeSize t) ??
      rank t == rank v
      && treeSize t == treeSize v
      && sameRkSz' (subtrees t) (subtrees v)
  | otherwise = False

-- rank and treeSize remains the same
{-@ reflect sameRkSz' @-}
{-@ sameRkSz' :: ts:[FibTree a] -> vs:[FibTree a] 
      -> {b:Bool | not b || length ts == length vs 
      && (length ts == 0 || (sameRkSz (head ts) (head vs) 
      && sameRkSz' (tail ts) (tail vs)
      && treeListSize ts == treeListSize vs))} / [treeListSize ts] 
      @-}
sameRkSz' :: Ord a => [FibTree a] -> [FibTree a] -> Bool
sameRkSz' [] [] = True
sameRkSz' [t] [v]
  | length (subtrees t) == length (subtrees v) =
      (treeListSize (subtrees t) < treeSize t) ??
      rank t == rank v
      && treeSize t == treeSize v
      && sameRkSz' (subtrees t) (subtrees v)
  | otherwise = False
sameRkSz' (t:ts) (v:vs)
  | length (subtrees t) == length (subtrees v) =
      (treeListSize (subtrees t) < treeSize t) ??
      (treeListSize (t:ts) < treeListSize ts) ??
      rank t == rank v
      && treeSize t == treeSize v
      && sameRkSz' (subtrees t) (subtrees v)
      && sameRkSz' ts vs
  | otherwise = False
sameRkSz' _ _ = False

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

{-@ reflect containsK @-}
{-@ containsK :: t:FibTree a -> a -> Bool / [treeSize t] @-}
containsK :: (Ord a) => FibTree a -> a -> Bool
containsK t k = root t == k || containsK' (subtrees t) k

{-@ reflect containsK' @-}
{-@ containsK' :: ts:[FibTree a] -> a -> Bool / [treeListSize ts] @-}
containsK' :: Ord a =>  [FibTree a] -> a -> Bool
containsK' [] _ = False
containsK' [t] k =
  (treeListSize (subtrees t) < treeSize t) ?? 
  (root t == k || containsK' (subtrees t) k)
containsK' (t:ts) k =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ??
  (root t == k || containsK' (subtrees t) k) || containsK' ts k

-- look for parent of t2 in t
{-@ parent3 :: Ord a => t:FibTree a -> t2:FibTree a
                   -> Maybe (v:{FibTree a | rank v < rank t2}) / [treeSize t] @-}
parent3 :: (Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> Maybe (FibTree a)
parent3 t@(Node x r [] mk sz) t2 = Nothing
parent3 t t2
  | t == t2 = Nothing
  | isChildL (subtrees t) t2 = Just t
  | otherwise = (treeListSize (subtrees t) < treeSize t) ??
                parent3' (subtrees t) t2

{-@ parent3' :: {ts:[FibTree a] | equalRank ts} -> t2:FibTree a 
                    -> Maybe (v:{FibTree a | rank v < rank t2}) 
                    / [treeListSize ts] @-}
parent3' :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> Maybe (FibTree a)
parent3' [] _ = Nothing
parent3' [t@(Node x r [] mk sz)] t2 = Nothing
parent3' [t] t2
  | isChildL (subtrees t) t2 = Just t
  | otherwise =
    (treeListSize (subtrees t) < treeSize t) ??
    parent3' (subtrees t) t2
parent3' (t:ts) t2
  | contains t t2 =
    (0 < treeListSize ts) ??
    (treeSize t < treeListSize (t:ts)) ??
    parent3 t t2
  | otherwise =
    (0 < treeListSize ts) ??
    (treeSize t < treeListSize (t:ts)) ??
    parent3' ts t2

{-@ reflect heapToList @-}
{-@ heapToList :: h:FibHeap a -> {vs:[FibTree a] | not notEmptyFibHeap h || length vs > 0} @-}
heapToList :: FibHeap a -> [FibTree a]
heapToList E = []
heapToList h = minTree h : trees h

{-@ listToHeap :: ts:[FibTree a] -> {h:FibHeap a | notEmptyFibHeap h || length ts == 0}  @-}
listToHeap :: Ord a => [FibTree a] -> FibHeap a
listToHeap [] = E
listToHeap ts = FH (fst newH) (snd newH) (markNod ts)
   where newH = tval (extractMin ts)

-- I could store the deleted tree(s) if needed
{-@ deleteSubTree' :: {ts:[FibTree a] | equalRank ts} -> a 
        -> {vs:[FibTree a] | length vs <= length ts && (length vs == 0 || (getRank (head vs) == getRank (head ts)) 
        && equalRank vs)} / [treeListSize ts] @-}
deleteSubTree' :: Ord a => [FibTree a] -> a -> [FibTree a]
deleteSubTree' [] k = []
deleteSubTree' [t@(Node r x [] mk sz)] k
  | x == k = []
  | otherwise = [t]
deleteSubTree' [t@(Node r x ts mk sz)] k
  | x == k = []
  | length (deleteSubTree' ts k) == 0 = [Node r x [] mk 1]
  | otherwise =
    [Node r x sub mk (1 + treeListSize sub)]
    where sub = deleteSubTree' ts k
deleteSubTree' (t@(Node r x ts mk sz):ts') k
  | x == k = ts'
  | length (deleteSubTree' ts' k) == 0 =
    [Node r x sub mk (1 + treeListSize sub)]
  | otherwise =
    eqRankProp (Node r x sub mk (1 + treeListSize sub)) (deleteSubTree' ts' k) ??
    Node r x sub mk (1 + treeListSize sub) : deleteSubTree' ts' k
    where sub = deleteSubTree' ts k

-- remove x from current position and add it unmarked to root list
{-@ cut :: {ts:[FibTree a] | length ts > 0 && equalRank ts} 
        -> FibTree a -> {vs:[FibTree a] | length vs > 0 && equalRank vs} @-}
cut :: Ord a => [FibTree a] -> FibTree a -> [FibTree a]
cut ts x
  | length (deleteSubTree' ts (root x)) == 0 = [buildNewTree 1 (unmarkNode x)]
  | otherwise =
    eqRankProp (buildNewTree (rank (head ts)) (unmarkNode x)) (deleteSubTree' ts (root x)) ??
    buildNewTree (rank (head ts)) (unmarkNode x) : deleteSubTree' ts (root x)

{-@ buildNewTree :: r:Pos -> t:FibTree a 
        -> {v:FibTree a | treeSize t == treeSize v && rank v == r} / [treeSize t] @-}
buildNewTree :: Ord a => Int -> FibTree a -> FibTree a
buildNewTree r (Node _ x [] mk sz) = Node r x [] mk sz
buildNewTree r t@(Node _ x ts mk sz) =
  (treeListSize (subtrees t) < treeSize t) ??
  Node r x (buildNewTree' r ts) mk sz

{-@ buildNewTree' :: r:Pos -> {ts:[FibTree a] | length ts > 0 && equalRank ts}
        -> {vs:[FibTree a] | length vs == length ts && equalRank vs &&
        getRank (head vs) == r + 1 && treeListSize ts == treeListSize vs} / [treeListSize ts] @-}
buildNewTree' :: Ord a => Int -> [FibTree a] -> [FibTree a]
buildNewTree' r [Node _ x [] mk sz] = [Node (r+1) x [] mk sz]
buildNewTree' r [t@(Node _ x ts mk sz)] =
  (treeListSize (subtrees t) < treeSize t) ??
  [Node (r+1) x (buildNewTree' (r+1) ts) mk sz]
buildNewTree' r (t:ts) =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ??
  eqRankProp (buildNewTree (r+1) t) (buildNewTree' r ts) ??
  buildNewTree (r+1) t : buildNewTree' r ts

-- unmarks root node
{-@ unmarkNode :: t:FibTree a -> v:FibTree a @-}
unmarkNode :: Ord a => FibTree a -> FibTree a
unmarkNode t@(Node _ _ _ False _) = t
unmarkNode t@(Node r x ts True sz) = Node r x ts False sz

-- checks if node with root k is unmarked
isUnmarked :: Ord a => [FibTree a] -> a -> Bool
isUnmarked [] k = False
isUnmarked (t@(Node r x sub mk sz):ts) k
  | x == k = not mk
  | otherwise = isUnmarked sub k || isUnmarked ts k

-- marks node with value k in heap h
{-@ mark' :: {ts:[FibTree a] | equalRank ts} -> a 
          -> {vs:[FibTree a] | length vs == length ts 
        && (length vs == 0 || getRank (head vs) == getRank (head ts)) 
        && equalRank vs && sameRkSz' ts vs && treeListSize ts == treeListSize vs} / [treeListSize ts] @-}
mark' :: Ord a => [FibTree a] -> a -> [FibTree a]
mark' [] _ = []
mark' [t@(Node r x [] mk sz)] k
   | x == k = [Node r x [] True sz]
   | otherwise = [t]
mark' [t@(Node r x sub mk sz)] k
  | x == k =
    rkSzProp' (subtrees t) ??
    [Node r x sub True sz]
  | otherwise =
    sameRkSz' (subtrees t) (mark' sub k) ??
    [Node r x (mark' sub k) mk sz]
mark' (t@(Node r x sub mk sz):ts) k
  | x == k =
    rkSzProp t ??
    rkSzProp' ts ??
    sameRkSz' (t:ts) (Node r x sub True sz : ts) ??
    Node r x sub True sz : ts
  | otherwise =
    sameRkSz' ts (mark' ts k) ??
   (sz == 1 + treeListSize (mark' sub k)) ??
    eqRankProp (Node r x (mark' sub k) mk sz) (mark' ts k) ??
    Node r x (mark' sub k) mk sz : mark' ts k

{-@ reflect isChildL @-}
{-@ isChildL :: {ts:[FibTree a] | length ts >= 1 && equalRank ts} -> t:FibTree a -> {v:Bool | v ==> rank (head ts) == rank t} @-}
isChildL :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> Bool
isChildL [t] t2 = t == t2
isChildL (t:ts) t2 = t == t2 || isChildL ts t2

-- NEW TRY: rank (Parent) < rank (Child)
{-@ cascadingCut :: {ts:[FibTree a] | length ts > 0 && equalRank ts} 
        -> t:(FibTree a) -> {vs:[FibTree a] | length vs > 0} / [rank t] @-}
cascadingCut :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> [FibTree a]
cascadingCut ts y
  | isNothing (parent3' ts y) = ts
  | isUnmarked ts (root y) = mark' ts (root y)
  | otherwise =
    (rank (fromJust (parent3' ts y)) < rank y) ??
    cascadingCut (cut ts y) (fromJust (parent3' ts y))

{-@ getTreeMaybe ::  t:FibTree a -> a -> Maybe (FibTree a) / [treeSize t] @-}
getTreeMaybe ::  Ord a => FibTree a -> a -> Maybe (FibTree a)
getTreeMaybe t k
  | root t == k = Just t
  | otherwise =
    (treeListSize (subtrees t) < treeSize t) ?? 
    getTreeMaybe' (subtrees t) k

{-@ getTreeMaybe' :: ts:[FibTree a] -> a -> Maybe (FibTree a) / [treeListSize ts] @-}
getTreeMaybe' :: Ord a => [FibTree a] -> a -> Maybe (FibTree a)
getTreeMaybe' [] k = Nothing 
getTreeMaybe' [t] k
  | root t == k = Just t
  | otherwise =
    (treeListSize (subtrees t) < treeSize t) ?? 
    getTreeMaybe' (subtrees t) k
getTreeMaybe' (t:ts) k
  | containsK t k =
    (0 < treeListSize ts) ??
    (treeSize t < treeListSize (t:ts)) ??
    getTreeMaybe t k
  | otherwise =
    (0 < treeListSize ts) ??
    (treeSize t < treeListSize (t:ts)) ??
    getTreeMaybe' ts k

{-@ performCuts :: {ts:[FibTree a] | length ts > 0 && equalRank ts} -> a 
          -> {vs:[FibTree a] | length vs > 0} @-}
performCuts :: (Eq (FibTree a), Ord a) => [FibTree a] -> a -> [FibTree a]
performCuts ts k
  | isJust x && isJust y = if k < root (fromJust y)
        then cascadingCut (cut ts (fromJust x)) (fromJust y)
        else ts
  | otherwise = ts
    where y = getY x ts
          x = getTreeMaybe' ts k

{-@ getY :: Maybe (FibTree a) -> {ts:[FibTree a] | equalRank ts} -> Maybe (FibTree a)@-}
getY :: (Eq (FibTree a), Ord a) => Maybe (FibTree a) -> [FibTree a] -> Maybe (FibTree a)
getY Nothing _ = Nothing
getY (Just x) ts = parent3' ts x

-- O(1) with pointer
-- decreases root of v to k
{-@ decreasekey :: Ord a => {ts:[FibTree a] | length ts > 0 && equalRank ts} -> v:a -> a -> {vs:[FibTree a] | length vs > 0} @-}
decreasekey :: (Eq (FibTree a), Ord a) => [FibTree a] -> a -> a -> [FibTree a]
decreasekey ts v k
  | k < v = performCuts (replace ts v k) k 
  | otherwise = ts

-- deletes note with root v from h
{-@ delete :: {ts:[FibTree a] | length ts > 0 && equalRank ts} -> a -> [FibTree a] @-}
delete :: (Eq (FibTree a), Num a, Ord a) => [FibTree a] -> a -> [FibTree a]
delete ts v = snd (tval (extractMin (decreasekey ts v 0)))