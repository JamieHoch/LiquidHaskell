{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
--{-@ LIQUID "--no-termination" @-}
{-@ infix : @-}

module PotentialAnalysis_FibHeap where
import Prelude hiding (pure, (++), (<*>), length, head, tail, max)
import Language.Haskell.Liquid.RTick as RTick
import Language.Haskell.Liquid.ProofCombinators
import GHC.Base (undefined)
import Data.Maybe (fromJust, isJust, isNothing)


{-@ type Pos = {v:Int | 0 < v} @-}
{-@ type NEFibTreeL a = {xs:[FibTree a] | length xs > 0} @-}
{-@ type NEFibHeap = {v : FibHeap a | not (emptyFibHeap v)} @-}
{-@ type EFibHeap = {v : FibHeap a | emptyFibHeap v} @-}

{-@
data FibTree [depth] a =
    Node
        { depth :: Pos
        , root :: a
        , subtrees :: {s:[FibTree a] | length s == 0 || (equalDepth s && getDepth (head s) = depth + 1)}
        , marked :: Bool
        , treeSize :: {v:Pos | v = 1 + treeListSize subtrees && v > 0}
        }
@-}

data FibTree a =
    Node
        { depth :: Int -- height of the tree starting from 1
        , root :: a -- the element
        , subtrees :: [FibTree a]
        , marked :: Bool
        , treeSize :: Int -- number of Nodes of the tree
    }

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

{-@ measure length @-}
length :: [a] -> Int
{-@ length :: xs:[a] -> {v:Nat | v = length xs} @-}
length [] = 0
length (_:xs) = 1 + length xs

{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[FibTree a] 
        -> {v:Nat | (length  xs <= v) && (v = 0 <=> length xs = 0) 
        && (length xs > 0 <=> v > 0)} @-}
treeListSize :: Ord a => [FibTree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = treeSize x + treeListSize xs

{-@ reflect getDepth @-}
{-@ getDepth :: t:FibTree a -> {v:Pos | v = depth t} @-}
getDepth :: FibTree a -> Int
getDepth t = depth t

{-@ reflect head @-}
{-@ head :: {t:[a] | length t > 0} -> a @-}
head (t:ts) = t

{-@ reflect tail @-}
{-@ tail :: {t:[a] | length t > 0} -> [a] @-}
tail (t:ts) = ts

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] 
      -> {zs:[a] | length zs == length xs + length ys && pot zs == pot xs + pot ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

{-@ reflect singl @-}
singl :: a -> [a]
singl x = [x]

{-@ reflect equalDepth @-}
{-@ equalDepth :: [FibTree a] -> Bool @-}
equalDepth :: Ord a => [FibTree a] -> Bool
equalDepth [] = True
equalDepth [t] = True
equalDepth (t:t':ts) = depth t == depth t' && equalDepth (t':ts)

{-@ measure emptyFibHeap @-}
emptyFibHeap :: FibHeap a -> Bool
emptyFibHeap E = True
emptyFibHeap _ = False

{-@ reflect increaseDepth @-}
{-@ increaseDepth :: t:FibTree a -> {v:FibTree a | depth v = depth t + 1} / [treeSize t] @-}
increaseDepth :: (Ord a) => FibTree a -> FibTree a
increaseDepth t@(Node r x [] m sz) = Node (r+1) x [] m sz
increaseDepth t@(Node r x ts m sz) =
  (treeListSize (subtrees t) < treeSize t) ??
  Node (r+1) x (increaseDepth' (subtrees t) (r+1)) m (1 + treeListSize (increaseDepth' (subtrees t) (r+1)))

{-@ reflect increaseDepth' @-}
{-@ increaseDepth' :: {ts:[FibTree a] | equalDepth ts}
        -> {r:Int | length ts == 0 || r == getDepth (head ts)}
        -> {vs:[FibTree a] | length vs == length ts && (length vs == 0
        || (equalDepth vs && getDepth (head vs) == r + 1))} / [treeListSize ts] @-}
increaseDepth' :: (Ord a) => [FibTree a] -> Int -> [FibTree a]
increaseDepth' [] _ = []
increaseDepth' [t@(Node r x [] m sz)] _ = [Node (r+1) x [] m sz]
increaseDepth' [t@(Node r x ts m sz)] _ =
  (treeListSize (subtrees t) < treeSize t) ??
  [Node (r+1) x (increaseDepth' (subtrees t) (r+1)) m (1 + treeListSize (increaseDepth' (subtrees t) (r+1)))]
increaseDepth' (t:ts) r =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ??
  eqDepthProp (increaseDepth t) (increaseDepth' ts r) ??
  increaseDepth t : increaseDepth' ts r

{-@ reflect eqDepthProp @-}
{-@ eqDepthProp :: t:FibTree a 
      -> {ts1:NEFibTreeL a | equalDepth ts1 && depth t == depth (head ts1)} 
      -> {equalDepth (t:ts1)} @-}
eqDepthProp :: FibTree a -> [FibTree a] -> Proof
eqDepthProp t (t':ts) = ()

{-@ reflect getDegree' @-}
getDegree' :: [FibTree a] -> Int
getDegree' [] = 0
getDegree' ((Node _ _ ts1 _ _):ts) = max (1 + getDegree' ts1) (getDegree' ts)

{-@ reflect max @-}
max a b 
  | a >= b = a
  | otherwise = b
--------------------------------------------------------------------
-- POTENTIAL FUNCTION
--------------------------------------------------------------------
{-@ measure poth @-}
{-@ poth :: h:FibHeap a 
      -> {v:Nat | v == 0 && emptyFibHeap h 
      || v == length (trees h) + 1 + 2 * markedNodes h} @-}
poth :: FibHeap a -> Int
poth E = 0
poth h = pot (trees h) + 1 + 2 * markedNodes h

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

{-@ inline amortized @-}
{-@ amortized :: Tick (FibHeap a) -> Int -> Int @-}
amortized :: Ord a => Tick (FibHeap a) -> Int -> Int
amortized ti input = tcost ti + poth (tval ti) - input

--------------------------------------------------------------------
-- TREE AND HEAP OPERATIONS
--------------------------------------------------------------------
-- O(1)
{-@ makeHeap :: {ti:Tick EFibHeap | tcost ti == 0} @-}
makeHeap :: Tick (FibHeap a)
makeHeap = pure E

-- O(1)
{-@ reflect singleton @-}
{-@ singleton :: x:a -> NEFibHeap @-}
singleton :: a -> FibHeap a
singleton x = (FH (Node 1 x [] False 1) [] 0)


-- O(1)
{-@ reflect merge @-}
{-@ merge :: h1:(FibHeap a) -> h2:NEFibHeap
      -> {ti:Tick NEFibHeap | 
      amortized ti (poth h1 + poth h2) < 1} @-}
merge:: (Ord a) => FibHeap a -> FibHeap a -> Tick (FibHeap a)
merge E h = pure h
merge h1@(FH minTr1 ts1 mark1) h2@(FH minTr2 ts2 mark2)
    | root minTr1 < root minTr2 = pure (FH minTr1 (minTr2:ts2++ts1) (mark1 + mark2))
    | otherwise = pure (FH minTr2 (minTr1:ts1++ts2) (mark1 + mark2))

-- O(1)
{-@ reflect insert @-}
{-@ insert :: h:FibHeap a -> x:a 
      -> {ti:Tick NEFibHeap | 
      amortized ti (poth h + pota x) < 1}  @-}
insert :: (Ord a) => FibHeap a -> a -> Tick (FibHeap a)
insert h x = merge h (singleton x)

-- O(1)
{-@ reflect findMin @-}
{-@ findMin :: h:NEFibHeap -> {ti:Tick a | 
      tcost ti + pota (tval ti) - poth h <= 2} @-}
findMin :: (Ord a) => FibHeap a -> Tick a
findMin h = wait (root (minTree h))

-- O(1)
{-@ reflect link @-}
{-@ link :: t1:FibTree a-> {t2:FibTree a | depth t1 == depth t2 && getDegree' [t1] == getDegree' [t2]} 
        -> FibTree a @-}
link :: (Ord a) => FibTree a -> FibTree a -> (FibTree a)
link t1@(Node d x1 ts1 _ sz1) t2@(Node _ x2 ts2 _ sz2)
    | x1 <= x2 && length ts1 == 0 =
        (Node d x1 [increaseDepth t2] False (1 + treeListSize [increaseDepth t2]))
    | x1 <= x2 =
        equalDepth ts1 ??
        eqDepthProp (increaseDepth t2) ts1 ??
        equalDepth (increaseDepth t2 : ts1) ??
        (Node d x1 (increaseDepth t2:ts1) False (1 + treeListSize (increaseDepth t2:ts1)))
    | length ts2 == 0 =
        (Node d x1 [increaseDepth t1] False (1 + treeListSize [increaseDepth t1]))
    | otherwise =
        equalDepth ts2 ??
        eqDepthProp (increaseDepth t1) ts2 ??
        (Node d x2 (increaseDepth t1:ts2) False (1 + treeListSize (increaseDepth t1:ts2)))
        
-- geht t für ganze liste durch
{-@ reflect meld @-}
{-@ meld :: xs:[FibTree a] -> t:FibTree a 
      -> {ti:Tick ({ts:NEFibTreeL a | length ts <= length xs + 1}) | 
      tcost ti <= pot xs
      && pot (tval ti) <= pot xs + 1
      } @-}
meld :: Ord a => [FibTree a] -> FibTree a -> Tick [FibTree a]
meld [] t = pure [t]
meld (x:xs) t
  | getDegree' [x] == getDegree' [t] && depth x == depth t =
    step 1 (meld xs (link t x))
  | otherwise =
    (pot (tval (pure ((:) x) <*> meld xs t) ) <= pot (x:xs) + 1) ??
    pure ((:) x) <*> meld xs t

-- O(log n)
-- calls meld with every element
-- ATTENTION! intentional cheat because no pointer
{-@ reflect consolidate @-}
{-@ consolidate :: xs:NEFibTreeL a
      -> {ti:Tick ({ts:NEFibTreeL a | length ts <= length xs}) | 
      tcost ti <= pot xs 
      && pot (tval ti) <= pot xs} @-}
consolidate :: (Ord a) => [FibTree a] -> Tick [FibTree a]
consolidate [x] = wait [x]
consolidate (x:xs) =
  let (Tick c1 y1) = consolidate xs
      (Tick _ y2) = meld y1 x in
  Tick (1 + c1) y2

-- O(length list)
{-@ reflect extractMin @-}
{-@ extractMin :: ts:NEFibTreeL a
      -> {ti:Tick (FibTree a, {ts':[FibTree a] | length ts' <= length ts - 1}) | 
      pott (tval ti) == pot ts && tcost ti <= pot ts && tcost ti <= length ts} @-}
extractMin :: (Ord a) => [FibTree a] -> Tick (FibTree a, [FibTree a])
extractMin [t] = wait (t, [])
extractMin (t:ts)
  | root t < root t' = 
    Tick (1 + tcost f) (t, ts)
  | otherwise = 
    Tick (1 + tcost f) (t', t:ts')
    where
        (t', ts') = tval f
        f = extractMin ts

-- O(log n)
{-@ deleteMin :: {h:NEFibHeap | not (marked (minTree h)) 
      || (subtrees (minTree h) == [] && trees h == [])} 
      -> {ti:Tick (FibHeap a) |
      amortized ti (poth h) <= 2 * pot (subtrees (minTree h)) + pot (trees h)
      &&  (emptyFibHeap (tval ti) || amortized ti (poth h) <= 2 * length (trees (tval ti)) + 1)} @-}
deleteMin :: (Ord a) => FibHeap a -> Tick (FibHeap a)
deleteMin (FH (Node _ x [] _ _) [] _) = pure E
deleteMin h@(FH minTr ts m) = 
  let (Tick cc (minTr', ts')) = extractMin $ tval (consolidate (subtrees minTr ++ ts)) in
    (pott (minTr', ts') <= pot (subtrees (minTree h)) + pot (trees h)) ??
    (pott (minTr', ts') <= pot (trees h) + 1) ??
    assert (cc <= 1 + pot ts') ??
    assert (pott (minTr', ts') == 1 + pot ts') ??
    assert (poth (FH minTr' ts' m) == pot ts' + 1 + 2 * m) ??
    assert (cc + poth (FH minTr' ts' m) - poth h <= pot ts' + 1 + pot ts' - pot ts) ??
    Tick cc (FH minTr' ts' m)

-- O(1) with pointer
-- decreases root of v to k
{-@ decreasekey :: Ord a => {ts:NEFibTreeL a | equalDepth ts} 
      -> v:a -> a -> NEFibTreeL a @-}
decreasekey :: (Eq (FibTree a), Ord a) => [FibTree a] -> a -> a -> [FibTree a]
decreasekey ts v k
  | k < v = performCuts (replace ts v k) k 
  | otherwise = ts

-- deletes node with root v from h
{-@ delete :: {ts:NEFibTreeL a | equalDepth ts} -> a -> [FibTree a] @-}
delete :: (Eq (FibTree a), Num a, Ord a) => [FibTree a] -> a -> [FibTree a]
delete ts v = snd (tval (extractMin (decreasekey ts v 0)))

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
-- HELPER FUNCTIONS OF DELETE
-- delete is a tricky function because we do not have direct access via pointers and
-- because of termination of cascadingCut
---------------------------------------------------------------
-- returns heap where v is replaced by k
{-@ replace :: {ts:[FibTree a] | equalDepth ts} -> a -> a
        -> {vs:[FibTree a] | length vs == length ts 
        && (length vs == 0 || getDepth (head vs) == getDepth (head ts)) 
        && equalDepth vs && sameRkSz' ts vs} 
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
      eqDepthProp (replace' t v k) (replace ts v k) ??
      (replace' t v k : replace ts v k)

{-@ replace' :: Ord a => t:FibTree a -> a -> a -> {v:FibTree a | sameRkSz t v} / [treeSize t]@-}
replace' :: Ord a => FibTree a -> a -> a -> FibTree a
replace' t@(Node r x [] mk sz) v k
  | x == v = rkSzProp t ?? Node r k [] mk sz
  | otherwise = t
replace' t@(Node r x ts mk sz) v k
  | x == v = rkSzProp t ?? Node r k ts mk sz
  | otherwise =
    (getDepth (head (subtrees t)) == r + 1) ??
    sameRkSz' (subtrees t) (replace (subtrees t) v k) ??
    Node r x (replace (subtrees t) v k) mk sz

{-@ rkSzProp :: t:FibTree a -> {sameRkSz t t} / [treeSize t] @-}
rkSzProp :: Ord a => FibTree a -> Proof
rkSzProp t =
  (treeListSize (subtrees t) < treeSize t) ??
  rkSzProp' (subtrees t) ??
  ()

{-@ rkSzProp' :: ts:[FibTree a] -> {sameRkSz' ts ts} / [treeListSize ts] @-}
rkSzProp' :: Ord a => [FibTree a] -> Proof
rkSzProp' [] = ()
rkSzProp' [t] =
  (treeListSize (subtrees t) < treeSize t) ??
  rkSzProp' (subtrees t) ??
  ()
rkSzProp' (t:ts) =
  (0 < treeListSize ts) ??
  (treeSize t < treeListSize (t:ts)) ??
  rkSzProp t ??
  rkSzProp' ts ??
  ()

{-@ reflect sameRkSz @-}
{-@ sameRkSz :: t:FibTree a -> v:FibTree a 
      -> {b:Bool | not b || depth t == depth v 
      && treeSize t == treeSize v 
      && sameRkSz' (subtrees t) (subtrees v)} / [treeSize t] @-}
sameRkSz t v
  | length (subtrees t) == length (subtrees v) =
      (treeListSize (subtrees t) < treeSize t) ??
      depth t == depth v
      && treeSize t == treeSize v
      && sameRkSz' (subtrees t) (subtrees v)
  | otherwise = False

-- depth and treeSize remains the same
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
      depth t == depth v
      && treeSize t == treeSize v
      && sameRkSz' (subtrees t) (subtrees v)
  | otherwise = False
sameRkSz' (t:ts) (v:vs)
  | length (subtrees t) == length (subtrees v) =
      (treeListSize (subtrees t) < treeSize t) ??
      (treeListSize (t:ts) < treeListSize ts) ??
      depth t == depth v
      && treeSize t == treeSize v
      && sameRkSz' (subtrees t) (subtrees v)
      && sameRkSz' ts vs
  | otherwise = False
sameRkSz' _ _ = False

-- checks if tree t contain element k
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
{-@ getParent :: Ord a => t:FibTree a -> t2:FibTree a
                   -> Maybe (v:{FibTree a | depth v < depth t2}) / [treeSize t] @-}
getParent :: (Eq (FibTree a), Ord a) => FibTree a -> FibTree a -> Maybe (FibTree a)
getParent t@(Node x r [] mk sz) t2 = Nothing
getParent t t2
  | t == t2 = Nothing
  | isChildL (subtrees t) t2 = Just t
  | otherwise = getParentL (subtrees t) t2

{-@ getParentL :: {ts:[FibTree a] | equalDepth ts} -> t2:FibTree a 
                    -> Maybe (v:{FibTree a | depth v < depth t2}) 
                    / [treeListSize ts] @-}
getParentL :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> Maybe (FibTree a)
getParentL [] _ = Nothing
getParentL [t@(Node x r [] mk sz)] t2 = Nothing
getParentL [t] t2
  | isChildL (subtrees t) t2 = Just t
  | otherwise =
    getParentL (subtrees t) t2
getParentL (t:ts) t2
  | containsK t (root t2) =
    (0 < treeListSize ts) ??
    getParent t t2
  | otherwise =
    (0 < treeListSize ts) ??
    getParentL ts t2

-- I could store the deleted tree(s) if needed
{-@ deleteSubTree' :: {ts:[FibTree a] | equalDepth ts} -> a 
        -> {vs:[FibTree a] | length vs <= length ts 
        && (length vs == 0 || (getDepth (head vs) == getDepth (head ts)) 
        && equalDepth vs)} / [treeListSize ts] @-}
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
    eqDepthProp (Node r x sub mk (1 + treeListSize sub)) (deleteSubTree' ts' k) ??
    Node r x sub mk (1 + treeListSize sub) : deleteSubTree' ts' k
    where sub = deleteSubTree' ts k

-- remove x from current position and add it unmarked to root list
{-@ cut :: {ts:NEFibTreeL a | equalDepth ts} 
        -> FibTree a -> {vs:NEFibTreeL a | equalDepth vs} @-}
cut :: Ord a => [FibTree a] -> FibTree a -> [FibTree a]
cut ts x
  | length (deleteSubTree' ts (root x)) == 0 = [buildNewTree 1 (unmarkNode x)]
  | otherwise =
    eqDepthProp (buildNewTree (depth (head ts)) (unmarkNode x)) (deleteSubTree' ts (root x)) ??
    buildNewTree (depth (head ts)) (unmarkNode x) : deleteSubTree' ts (root x)

{-@ buildNewTree :: r:Pos -> t:FibTree a 
        -> {v:FibTree a | treeSize t == treeSize v && depth v == r} / [treeSize t] @-}
buildNewTree :: Ord a => Int -> FibTree a -> FibTree a
buildNewTree r (Node _ x [] mk sz) = Node r x [] mk sz
buildNewTree r t@(Node _ x ts mk sz) =
  (treeListSize (subtrees t) < treeSize t) ??
  Node r x (buildNewTree' r ts) mk sz

{-@ buildNewTree' :: r:Pos -> {ts:NEFibTreeL a | equalDepth ts}
        -> {vs:[FibTree a] | length vs == length ts && equalDepth vs &&
        getDepth (head vs) == r + 1 && treeListSize ts == treeListSize vs} / [treeListSize ts] @-}
buildNewTree' :: Ord a => Int -> [FibTree a] -> [FibTree a]
buildNewTree' r [Node _ x [] mk sz] = [Node (r+1) x [] mk sz]
buildNewTree' r [t@(Node _ x ts mk sz)] =
  (treeListSize (subtrees t) < treeSize t) ??
  [Node (r+1) x (buildNewTree' (r+1) ts) mk sz]
buildNewTree' r (t:ts) =
  (0 < treeListSize ts) ??
  eqDepthProp (buildNewTree (r+1) t) (buildNewTree' r ts) ??
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
{-@ mark' :: {ts:[FibTree a] | equalDepth ts} -> a 
          -> {vs:[FibTree a] | length vs == length ts 
        && (length vs == 0 || getDepth (head vs) == getDepth (head ts)) 
        && equalDepth vs && sameRkSz' ts vs && treeListSize ts == treeListSize vs} 
        / [treeListSize ts] @-}
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
    eqDepthProp (Node r x (mark' sub k) mk sz) (mark' ts k) ??
    Node r x (mark' sub k) mk sz : mark' ts k

{-@ reflect isChildL @-}
{-@ isChildL :: {ts:[FibTree a] | length ts >= 1 && equalDepth ts} 
      -> t:FibTree a -> {v:Bool | v ==> depth (head ts) == depth t} @-}
isChildL :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> Bool
isChildL [t] t2 = t == t2
isChildL (t:ts) t2 = t == t2 || isChildL ts t2

-- TERMINATION: depth (Parent) < depth (Child)
{-@ cascadingCut :: {ts:NEFibTreeL a | equalDepth ts} 
        -> t:(FibTree a) -> NEFibTreeL a / [depth t] @-}
cascadingCut :: (Eq (FibTree a), Ord a) => [FibTree a] -> FibTree a -> [FibTree a]
cascadingCut ts y
  | isNothing (getParentL ts y) = ts
  | isUnmarked ts (root y) = mark' ts (root y)
  | otherwise =
    (depth (fromJust (getParentL ts y)) < depth y) ??
    cascadingCut (cut ts y) (fromJust (getParentL ts y))

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

{-@ performCuts :: {ts:NEFibTreeL a | equalDepth ts} -> a 
          -> NEFibTreeL a @-}
performCuts :: (Eq (FibTree a), Ord a) => [FibTree a] -> a -> [FibTree a]
performCuts ts k
  | isJust x && isJust y = if k < root (fromJust y)
        then cascadingCut (cut ts (fromJust x)) (fromJust y)
        else ts
  | otherwise = ts
    where y = getParentMaybe x ts
          x = getTreeMaybe' ts k

{-@ getParentMaybe :: Maybe (FibTree a) -> {ts:[FibTree a] | equalDepth ts} -> Maybe (FibTree a) @-}
getParentMaybe :: (Eq (FibTree a), Ord a) => Maybe (FibTree a) -> [FibTree a] -> Maybe (FibTree a)
getParentMaybe Nothing _ = Nothing
getParentMaybe (Just x) ts = getParentL ts x