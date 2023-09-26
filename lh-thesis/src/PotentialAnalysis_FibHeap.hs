-- Automatically generate singleton types for data constructors
--{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination" @-}

module PotentialAnalysis_FibHeap where
import Prelude hiding (pure, (++), (<*>))
import Language.Haskell.Liquid.RTick as RTick

{-@ type Pos = {v:Int | 0 < v} @-}
{-@ type NEFibHeap = {v : FibHeap a | notEmptyFibHeap v} @-}
{-@ type EFibHeap = {v : FibHeap a | not (notEmptyFibHeap v)} @-}

{-@ reflect treeListSize @-}
{-@ treeListSize :: Ord a => xs:[FibTree a] -> {v:Nat | (len  xs <= v) && (v = 0 <=> len xs = 0) && (len xs == 0 || v > 0)} @-}
treeListSize :: Ord a => [FibTree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = treeSize x + treeListSize xs

{-@
data FibTree [rank] a =
    Node
        { rank :: Nat
        , root :: a
        , subtrees :: [FibTree a]
        , marked :: Bool
        , treeSize :: {v:Pos | v = 1 + treeListSize subtrees && v > 0}
        }
@-}
data FibTree a =
    Node
        { rank :: Int -- depth of the tree
        , root :: a -- the element
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
singleton x = wait (FH (Node 1 x [] False 1) [] 1 0)

-- O(1)
{-@ reflect link @-}
{-@ link :: t1:FibTree a -> {t2:FibTree a | rank t1 == rank t2} -> {t:Tick ({v:FibTree a | rank v == 1 + (rank t1) && (root v == root t1 && root t1 <= root t2 || root v == root t2 && root t2 <= root t1)}) | tcost t == 1} @-}
link :: (Ord a) => FibTree a -> FibTree a -> Tick (FibTree a)
link t1@(Node r x1 ts1 _ sz1) t2@(Node _ x2 ts2 _ sz2)
    | x1 <= x2 = wait (Node (r+1) x1 (t2:ts1) False (sz1 + sz2))
    | otherwise = wait (Node (r+1) x2 (t1:ts2) False (sz1 + sz2))

{-@ measure poth @-}
{-@ poth :: h:FibHeap a -> {v:Nat | v == 0 && not notEmptyFibHeap h || v == len (trees h) + 1 + 2*markedNodes h}@-}
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
{-@ findMin :: h:NEFibHeap -> {ti:Tick a | tcost (findMin h) + pota (tval (findMin h)) - poth h <= 2} @-}
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
{-@ deleteMin' :: (Ord a) => {h:NEFibHeap | numNodes h > 1 && (len (subtrees (minTree h)) + len (trees h) > 0)} -> {k:(FibTree a,[FibTree a])| pott k <= pot (subtrees (minTree h)) + pot (trees h) }-> {ti:Tick (FibHeap a) | tcost ti + poth (tval ti) - poth h <= 2 * pot (subtrees (minTree h)) + pot (trees h)} @-}
deleteMin' :: (Ord a) => FibHeap a -> (FibTree a ,[FibTree a]) -> Tick (FibHeap a)
deleteMin' h@(FH minTr ts n m) (minTr', ts') = Tick (tcost (extractMin $ tval (consolidate (subtrees minTr ++ ts)))) (FH minTr' ts' (n-1) m)

{-@ infix   ++ @-}
{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {zs:[a] | len zs == len xs + len ys && pot zs == pot xs + pot ys} @-}
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)




{- all upcoming functions are just helper functions for DELETE
here delete is a tricky function because we do not have direct access via pointers 
we also ran into some termination issues that can be solved with help of cconst and assertions
-}

{-@ assume :: b:Bool -> {v:Bool | b } @-}
assume :: Bool -> Bool
assume x = undefined

{-@ assert :: b:{Bool | b } -> Bool @-}
assert :: Bool -> Bool
assert x = x

cconst x y = y

-- returns heap where v is replaced by k
{-@ replace :: Ord a => ts:[FibTree a] -> a -> a -> {vs:[FibTree a] | len vs == len ts} / [treeListSize ts] @-}
replace :: Ord a => [FibTree a] -> a -> a -> [FibTree a]
replace [] v k = []
replace [t@(Node r x ts mark sz)] v k = if x == v then [Node r k ts mark sz] else [Node r x (replace (subtrees t) v k) mark (1 + (treeListSize (replace (subtrees t) v k)))]
replace (t:ts) v k = cconst (assert (0 < treeListSize ts)) ( ((replace' t v k) : replace ts v k))

{-@ replace' :: Ord a => t:FibTree a -> a -> a -> FibTree a / [treeSize t]@-}
replace' :: Ord a => FibTree a -> a -> a -> FibTree a
replace' t@(Node r x ts mark sz) v k = if x == v then Node r k ts mark sz else Node r x (replace (subtrees t) v k) mark (1 + (treeListSize (replace (subtrees t) v k)))

-- returns total number of nodes in the tree list
{-@ numNod :: Ord a => ts:[FibTree a] -> {v:Int | v >= len ts} / [treeListSize ts] @-}
numNod :: Ord a => [FibTree a] -> Int
numNod [] = 0
numNod [t] = cconst (assert (treeListSize (subtrees t) < (treeSize t))) (1 + numNod (subtrees t))
numNod (t:ts) = cconst (assert (0 < treeListSize ts)) (cconst (assert ( treeSize t < treeListSize (t:ts))) (numNod' t + numNod ts))

{-@ numNod' :: t:FibTree a -> {v:Int | v > 0} / [treeSize t] @-}
numNod' :: Ord a => FibTree a -> Int
numNod' t = cconst (assert (treeListSize (subtrees t) < treeSize t)) (1 + numNod (subtrees t))

-- retuns number of marked nodes in the tree list
{-@ markNod :: ts:[FibTree a] -> {v:Int | v >= 0} / [treeListSize ts]@-}
markNod :: Ord a => [FibTree a] -> Int
markNod [] = 0
markNod [t] = cconst (assert (treeListSize (subtrees t) < treeSize t)) (if marked t then (1 + markNod (subtrees t)) else markNod (subtrees t))
markNod (t:ts) = cconst (assert (0 < treeListSize ts)) (cconst (assert ( treeSize t < treeListSize (t:ts))) (markNod' t + markNod ts))

{-@ markNod' :: t:FibTree a -> {v:Int | v >= 0} / [treeSize t] @-}
markNod' :: Ord a => FibTree a -> Int
markNod' t = cconst (assert (treeListSize (subtrees t) < treeSize t)) (if marked t then (1 + markNod (subtrees t)) else markNod (subtrees t))

-- checks if tree t contain element k
{-@ contains :: t:FibTree a -> a -> Bool / [treeSize t] @-}
contains :: Ord a => FibTree a -> a -> Bool
contains t k = cconst (assert (treeListSize (subtrees t) < treeSize t)) (root t == k || containsL (subtrees t) k)

{-@ containsL :: ts:[FibTree a] -> a -> Bool / [treeListSize ts] @-}
containsL :: Ord a =>  [FibTree a] -> a -> Bool
containsL [] k = False
containsL [t] k = cconst (assert (treeListSize (subtrees t) < treeSize t)) (root t == k || containsL (subtrees t) k)
containsL (t:ts) k = cconst (assert (0 < treeListSize ts)) (cconst (assert ( treeSize t < treeListSize (t:ts))) (contains t k || containsL ts k))

-- checks if one of the subtrees ts has root k
checkSubRoots :: Ord a => [FibTree a] -> a -> Bool
checkSubRoots [] _ = False
checkSubRoots (t:ts) k = (root t == k) || checkSubRoots ts k

-- returns parent element of k
{-@ getParentVal :: t:FibTree a -> a -> [a] / [treeSize t] @-}
getParentVal :: Ord a => FibTree a -> a -> [a]
getParentVal t k = cconst (assert (treeListSize (subtrees t) < treeSize t)) (if checkSubRoots (subtrees t) k then [root t] else getParentVal' (subtrees t) k)

{-@ getParentVal' ::  ts:[FibTree a] -> a -> [a] / [treeListSize ts] @-}
getParentVal' :: Ord a => [FibTree a] -> a -> [a]
getParentVal' [] _ = []
getParentVal' [t] k = cconst (assert (treeListSize (subtrees t) < treeSize t)) (if checkSubRoots (subtrees t) k then [root t] else getParentVal' (subtrees t) k)
getParentVal' (t:ts) k = cconst (assert (0 < treeListSize ts)) (cconst (assert ( treeSize t < treeListSize (t:ts))) (getParentVal t k ++ getParentVal' ts k))

-- returns parent tree of k
{-@ getParent :: t:FibTree a -> FibTree a -> {vs:[FibTree a] | len vs == 0 || True} / [treeSize t] @-}
getParent :: Ord a => FibTree a -> FibTree a -> [FibTree a]
getParent t t2 = cconst (assert (treeListSize (subtrees t) < treeSize t)) (if checkSubRoots (subtrees t) (root t2) then [t] else getParent' (subtrees t) t2)

{-@ getParent' ::  ts:[FibTree a] -> FibTree a -> vs:[FibTree a] / [treeListSize ts] @-}
getParent' :: Ord a => [FibTree a] -> FibTree a -> [FibTree a]
getParent' [] _ = []
getParent' [t] t2 = cconst (assert (treeListSize (subtrees t) < treeSize t)) (if checkSubRoots (subtrees t) (root t2) then [t] else getParent' (subtrees t) t2)
getParent' (t:ts) t2 = cconst (assert (0 < treeListSize ts)) (cconst (assert ( treeSize t < treeListSize (t:ts))) (getParent t t2 ++ getParent' ts t2))

{-@ getParentList :: t1:FibTree a -> t2:FibTree a -> [FibTree a] / [treeSize t1 - treeSize t2] @-}
getParentList :: Ord a => FibTree a -> FibTree a -> [FibTree a]
getParentList t x = if length p == 0 then p else p -- ++ getParentList t (myhead p)
    where p = getParent t x

{-
parentValList :: Ord a => [FibTree a] -> a -> [a]
parentValList ts x = if length p > 0 then p ++ parentValList ts (head p) else [] -- termination
    where p = getParentVal' ts x
-}

{-@ reflect myhead @-}
{-@ myhead :: Ord a => {v:[FibTree a] | len v > 0} -> FibTree a @-}
myhead :: [FibTree a] -> FibTree a
myhead (x:_) = x

-- returns subtree with root k
{-@ getTreeList ::  t:FibTree a -> a -> [FibTree a] / [treeSize t] @-}
getTreeList ::  Ord a => FibTree a -> a -> [FibTree a]
getTreeList t k = cconst (assert (treeListSize (subtrees t) < treeSize t)) (if root t == k then [t] else getTreeList' (subtrees t) k)

{-@ getTreeList' :: ts:[FibTree a] -> a -> [FibTree a] / [treeListSize ts] @-}
getTreeList' :: Ord a => [FibTree a] -> a -> [FibTree a]
getTreeList' [] k = []
getTreeList' [t] k = cconst (assert (treeListSize (subtrees t) < treeSize t)) (if root t == k then [t] else getTreeList' (subtrees t) k)
getTreeList' (t:ts) k = cconst (assert (0 < treeListSize ts)) (cconst (assert ( treeSize t < treeListSize (t:ts))) (getTreeList t k ++ getTreeList' ts k))

-- returns tree with deleted subtree of root k
deleteSubTree :: Ord a => FibTree a -> a -> [FibTree a]
deleteSubTree t k = if root t == k then [] else [(Node (rank t) (root t) subtrs (marked t) (1 + (treeListSize subtrs)))]
    where subtrs = deleteSubTree' (subtrees t) k

{-@ deleteSubTree' :: ts:[FibTree a] -> a -> vs:[FibTree a] / [treeListSize ts] @-}
deleteSubTree' :: Ord a => [FibTree a] -> a -> [FibTree a]
deleteSubTree' [] k = []
deleteSubTree' ((Node r x sub mk sz):ts) k = if x == k then [] else [Node r x (deleteSubTree' sub k) mk (1 + (treeListSize (deleteSubTree' sub k)))] ++ (deleteSubTree' ts k)


{-@ heapToList :: h:FibHeap a -> {vs:[FibTree a] | not notEmptyFibHeap h || len vs > 0} @-}
heapToList :: Ord a => FibHeap a -> [FibTree a]
heapToList E = []
heapToList h = minTree h : trees h

{-@ listToHeap :: ts:[FibTree a] -> {h:FibHeap a | notEmptyFibHeap h || len ts == 0}  @-}
listToHeap :: Ord a => [FibTree a] -> FibHeap a
listToHeap [] = E
listToHeap ts = FH (fst newH) (snd newH) (numNod ts) (markNod ts)
   where newH = tval (extractMin ts)


{-@ performCuts :: {ts:[FibTree a] | len ts > 0} -> a -> {vs:[FibTree a] | len vs > 0} @-}
performCuts :: Ord a => [FibTree a] -> a -> [FibTree a]
performCuts ts k = if length x > 0 && length y > 0 
    then if k < root (head y) 
        then cascadingCut (cut ts (head x)) (head y) 
        else ts 
    else ts
    where y = if length x > 0 then getParent' ts (head x) else []
          x = getTreeList' ts k

{-@ cascadingCut :: {ts:[FibTree a] | len ts > 0} -> FibTree a -> {vs:[FibTree a] | len vs > 0} @-}
cascadingCut :: Ord a => [FibTree a] -> FibTree a -> [FibTree a]
cascadingCut ts y = if length (getParent' ts y) > 0 && isUnmarked ts (root y) 
        then mark' ts (root y)
        else if length (getParent' ts y) > 0 
        then cascadingCut (cut ts y) (head (getParent' ts y)) -- termination
        else ts

-- remove x from current position and add it unmarked to root list
{-@ cut :: ts:[FibTree a] -> FibTree a -> {vs:[FibTree a] | len vs > 0} @-}
cut :: Ord a => [FibTree a] -> FibTree a -> [FibTree a]
cut ts x = (unmarkNode x) : (deleteSubTree' ts (root x))

-- unmarks root node
unmarkNode :: Ord a => FibTree a -> FibTree a
unmarkNode t@(Node _ _ _ False _) = t
unmarkNode t@(Node r x ts True sz) = Node r x ts False sz

-- checks if node with root k is unmarked
isUnmarked :: Ord a => [FibTree a] -> a -> Bool
isUnmarked [] k = False
isUnmarked (t@(Node r x sub mk sz):ts) k = if x == k then mk == False else (isUnmarked sub k) || (isUnmarked ts k)

-- marks node with value k in heap h
{-@ mark' :: ts:[FibTree a] -> a -> {vs:[FibTree a] | len ts > 0 <=> len vs > 0} / [treeListSize ts] @-}
mark' :: Ord a => [FibTree a] -> a -> [FibTree a]
mark' [] _ = []
mark' [Node r x sub mk sz] k = if x == k then [Node r x sub True sz] else [(Node r x (mark' sub k) mk (1 + (treeListSize (mark' sub k))))]
mark' (t@(Node r x sub mk sz):ts) k = if x == k then ((Node r x sub True sz):ts) else (Node r x (mark' sub k) mk (1 + (treeListSize (mark' sub k)))) : (mark' ts k)

-- O(1) with pointer
-- decreases root of v to k
{-@ decreasekey :: Ord a => NEFibHeap -> v:a -> a -> NEFibHeap @-}
decreasekey :: Ord a => FibHeap a -> a -> a -> FibHeap a
decreasekey h v k = if k < v then listToHeap (performCuts (replace (heapToList h) v k) k) else h

-- deletes note with root v from h
{-@ delete :: NEFibHeap -> a -> FibHeap a @-}
delete :: (Num a, Ord a) => FibHeap a -> a -> FibHeap a
delete h v = listToHeap (snd (tval (extractMin (heapToList (decreasekey h v 0)))))

