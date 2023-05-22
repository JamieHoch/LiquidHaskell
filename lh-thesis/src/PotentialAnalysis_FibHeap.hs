{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--ple" @-}

module PotentialAnalysis_FibHeap where

import Language.Haskell.Liquid.RTick as RTick

{-@ type Pos = {v:Int | 0 < v} @-}
{-@ type NEFibHeap = {v : FibHeap a | notEmptyFibHeap v} @-}
{-@ type EFibHeap = {v : FibHeap a | not (notEmptyFibHeap v)} @-}

{-@
data FibTree [rank] a =
    Node
        { root :: a
        , rank :: Nat
        , subtrees :: [FibTree a]
        , marked :: Bool
        }
@-}
data FibTree a =
    Node 
        { root :: a -- the element
        , rank :: Int -- size of the tree
        , subtrees :: [FibTree a]
        , marked :: Bool
    }

{-@
data FibHeap a =
    E | FH {  minTree :: FibTree a
            , trees :: [FibTree a]
            }
@-}
data FibHeap a = E | FH { minTree :: FibTree a
                        , trees :: [FibTree a] --wihout minTree
                     }

{-@ isMin ::  FibTree a -> [FibTree a] -> Tick Bool @-}
isMin :: (Ord a) => FibTree a -> [FibTree a] -> Tick Bool
isMin t [] = RTick.return True
isMin t (t':ts) = RTick.step 1 (RTick.pure (root t <= root t' && tval (isMin t ts)))

{-@ measure notEmptyFibHeap @-}
notEmptyFibHeap :: FibHeap a -> Bool
notEmptyFibHeap E = False
notEmptyFibHeap _ = True

{-@ makeHeap :: Tick EFibHeap @-}
makeHeap :: Tick (FibHeap a)
makeHeap = RTick.return E

{-@ singleton :: a -> Tick ({v: NEFibHeap | trees v = [] && subtrees (minTree v) = [] && rank (minTree v) = 1}) @-}
singleton :: a -> Tick (FibHeap a)
singleton x = RTick.step 1 (RTick.pure (FH (Node x 1 [] False) []))

{-@ link :: t1:FibTree a -> {t2:FibTree a | rank t1 == rank t2} -> Tick ({v:FibTree a | rank v == 1 + (rank t1)}) @-}
link :: (Ord a) => FibTree a -> FibTree a -> Tick (FibTree a)
link t1@(Node x r c1 _) t2@(Node y _ c2 _)
    | x < y = RTick.return (Node x (r+1) (t2:c1) False)
    | otherwise = RTick.return (Node y (r+1) (t1:c2) False)

-- constant time
{-@ merge :: FibHeap a -> NEFibHeap -> Tick NEFibHeap @-}
merge:: (Ord a) => FibHeap a -> FibHeap a -> Tick (FibHeap a)
merge E h = RTick.return h
merge h1@(FH minTr1 ts1) h2@(FH minTr2 ts2)
    | root minTr1 < root minTr2 = RTick.return (FH minTr1 (minTr2:ts2++ts1))
    | otherwise = RTick.return (FH minTr2 (minTr1:ts1++ts2))

-- constant time
{-@ insert :: FibHeap a -> a -> Tick NEFibHeap @-}
insert :: (Ord a) => FibHeap a -> a -> Tick (FibHeap a)
insert h x = merge h (tval (singleton x))

findMin :: (Ord a) => FibHeap a -> Tick a
findMin h = RTick.return (root . minTree $ h)

{-@ meld :: [FibTree a] -> FibTree a -> Tick ({t:[FibTree a] | len t > 0}) @-}
meld :: Ord a => [FibTree a] -> FibTree a -> Tick [FibTree a]
meld [] t = RTick.return [t]
meld (t':ts) t = if rank t' == rank t then RTick.step 1 (meld ts (tval (link t t')))
                     else RTick.return (t:t':ts)

{-@ meld' :: {t:[FibTree a] | len t > 0} -> [FibTree a] -> Tick ({t:[FibTree a] | len t > 0}) @-}
meld' :: Ord a => [FibTree a] -> [FibTree a] -> Tick [FibTree a]
meld' (t:ts) [] = RTick.return (t:ts)
meld' (t':ts') (t:ts) = if rank t' == rank t 
    then RTick.step 1 (meld' (tval (meld ts' (tval (link t t')))) ts)
    else RTick.step 1 (meld' (t:t':ts') ts)

{-@ consolidate :: {t:[FibTree a] | len t > 0} -> Tick ({t:[FibTree a] | len t > 0}) @-}
consolidate :: (Ord a) => [FibTree a] -> Tick [FibTree a]
consolidate (t:ts) = meld' [t] ts

{-@ extractMin :: {t:[FibTree a] | len t > 0} -> Tick (FibTree a, [FibTree a]) @-}
extractMin :: (Ord a) => [FibTree a] -> Tick (FibTree a, [FibTree a])
extractMin [t] = RTick.return (t, [])
extractMin (t:ts) = 
    let (t', ts') = tval (extractMin ts) in
        if root t < root t' then RTick.step 1 (RTick.pure (t, ts))
        else RTick.step 1 (RTick.pure (t', t:ts'))

{-@ deleteMin :: NEFibHeap -> Tick (FibHeap a) @-}
deleteMin :: (Ord a) => FibHeap a -> Tick (FibHeap a)
deleteMin (FH (Node x _ [] _) []) = RTick.return E
deleteMin h@(FH minTr ts@(x:xs)) = RTick.return (FH minTr' ts') where
    (minTr', ts') = tval (extractMin $ tval (consolidate (subtrees minTr ++ ts)))
deleteMin h@(FH minTr@(Node _ _ subtr@(x:xs) _) ts) = RTick.return (FH minTr' ts') where
    (minTr', ts') = tval (extractMin $ tval (consolidate (subtr ++ ts)))

