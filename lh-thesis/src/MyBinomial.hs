{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}

module MyBinomial 
    ( link
    , insTree
    , insert
    , mergeTree
    , mergeHeap
    , removeMinTree
    , findMin
    , deleteMin
    )
where

{-@ measure treeListSize @-}
{-@ treeListSize :: xs:[BiTree a] -> {v:Nat | (len xs <= v) && (v = 0 <=> len xs = 0)} @-}
treeListSize :: Ord a => [BiTree a] -> Int
treeListSize [] = 0
treeListSize (x:xs) = treeSize x + treeListSize xs

{-@ type Pos = {n:Int | n >= 1} @-}
{-@ type NEList a = {xs:[a] | 0 < len xs} @-}
{-@ type NEHeap a = {h: Heap a | 0 < len (unheap h)} @-}

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

{-@ reflect link @-}
{-@ link :: t1:BiTree a -> {t2:BiTree a | rank t2 = rank t1} -> {v:BiTree a | rank v = rank t1 + 1 && treeSize v = treeSize t1 + treeSize t2} @-}
link :: (Ord a) => BiTree a -> BiTree a -> BiTree a
link t1@(Node r x1 ts1 sz1) t2@(Node _ x2 ts2 sz2)
    | x1 <= x2 =
        Node (r + 1) x1 (t2:ts1) (sz1 + sz2)
    | otherwise =
        Node (r + 1) x2 (t1:ts2) (sz1 + sz2)

{-@ data Heap a = Heap { unheap :: [BiTree a] } @-}
data Heap a = 
    Heap { unheap :: [BiTree a] }

{-@ reflect insTree @-}
{-@ insTree :: t:BiTree a -> ts:[BiTree a] -> {zs:[BiTree a]| len zs <= len ts + 1} @-}
insTree :: Ord a => BiTree a -> [BiTree a] -> [BiTree a]
insTree t [] = [t]
insTree t ts@(t':ts') 
    | rank t < rank t' = t : ts
    | rank t > rank t' = t' : insTree t ts' -- needed
    | otherwise = insTree (link t t') ts'

{-@ measure unlist @-}
{-@ unlist :: {t:[BiTree a]| len t = 1} -> BiTree a @-}
unlist :: [BiTree a] -> BiTree a
unlist [t] = t

{-@ reflect singleton @-}
{-@ singleton :: x:a -> {v: BiTree a | rank v == 0 && root v == x && subtrees v == []} @-}
singleton :: Ord a => a -> BiTree a
singleton x = Node 0 x [] 1

{-@ reflect insert @-}
{-@ insert :: a -> Heap a -> Heap a @-}
insert :: Ord a => a -> Heap a -> Heap a
insert x (Heap ts) = Heap (insTree (singleton x) ts)

{-@ reflect mergeTree @-}
{-@ mergeTree :: ts1:[BiTree a] -> ts2:[BiTree a] -> {zs:[BiTree a] | len zs <= len ts1 + len ts2} @-}
mergeTree :: Ord a => [BiTree a] -> [BiTree a] -> [BiTree a]
mergeTree ts1 [] = ts1
mergeTree [] ts2 = ts2
mergeTree ts1@(t1:ts1') ts2@(t2:ts2')
    | rank t1 < rank t2 = t1 : mergeTree ts1' ts2
    | rank t2 < rank t1 = t2 : mergeTree ts1 ts2'
    | otherwise = insTree (link t1 t2) (mergeTree ts1' ts2')

{-@ reflect mergeHeap @-}
mergeHeap :: Ord a => Heap a -> Heap a -> Heap a
mergeHeap (Heap ts1) (Heap ts2) = Heap (mergeTree ts1 ts2)

{-@ removeMinTree :: NEList (BiTree a) -> (BiTree a, [BiTree a]) @-}
removeMinTree :: Ord a => [BiTree a] -> (BiTree a, [BiTree a])
removeMinTree [t] = (t,[])
removeMinTree (t:ts) =
    let (t', ts') = removeMinTree ts in
    if root t < root t' then (t, ts) else (t', t:ts')

{-@ findMin :: NEHeap a -> a @-}
findMin :: Ord a => Heap a -> a
findMin (Heap ts) = 
    let (t, _) = removeMinTree ts in root t

{-@ deleteMin :: NEHeap a -> Heap a @-}
deleteMin :: Ord a => Heap a -> Heap a
deleteMin (Heap ts) = let (Node _ x ts1 _, ts2) = removeMinTree ts in
   Heap (mergeTree (reverse ts1) ts2)

