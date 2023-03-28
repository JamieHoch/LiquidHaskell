{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}

module PopPush where

import Prelude hiding (length)
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.RTick as RTick


data List a = Nil | Cons a (List a)

-- push & pop

{-@ measure length @-}
{-@ length :: xs:[a] -> {v: Int | v = (len xs)} @-}
length :: [a] -> Int
length []     = 0
length (x:xs) = 1 + length xs

{-@ measure pot @-}
{-@ pot :: xs:[a] ->  {v: Int | v = (len xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

-- amortised cost 2
{-@ push :: xs:[a] -> x:a -> {t:Tick {ys:[a] | len ys = 1 + (len xs) } | (pot xs) + 2 >= (tcost t) + (pot (tval t))} @-}
push ls a = RTick.wait (a:ls)

-- amortised cost 0
{-@ pop :: k:Nat -> {xs:[a] | k <= (len xs)} -> {t:Tick {ys:[a] | (len ys) = (len xs) - k} | (pot xs) + 2 >= (tcost t) + (pot (tval t))} @-}
pop :: Int -> [a] -> Tick [a]
pop 0 ys     = RTick.return ys     
pop k (x:xs) = RTick.step 1 (pop (k-1) xs)
