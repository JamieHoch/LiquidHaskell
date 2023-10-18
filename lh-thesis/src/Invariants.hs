{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Invariants where 

import Prelude hiding (sum, map)

data Bar a = Bar { bar :: a, baz :: Int }

{-@ data Bar a = Bar { bar :: a, baz :: Int } @-}

type ListOfThings a = [Bar a]

{-@ reflect potential @-}
potential ::ListOfThings a -> Int
potential xs = sum (map baz xs) 

{-@ reflect sum @-}
sum :: Num a => [a] -> a
sum [] = 0
sum (x:xs) =  x + sum xs

{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) =  f x : map f xs

{-@ invariant {v:ListOfThings a | len v == potential v} @-}

{-@ testInvariant :: v:ListOfThings a -> {len v == potential v} @-}
testInvariant :: ListOfThings a -> ()
testInvariant xs = ()