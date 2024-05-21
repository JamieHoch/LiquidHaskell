{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}

module PopPush where

import Prelude hiding (length, pure)
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.RTick


-- push & pop
{-@ measure pot @-}
{-@ pot :: xs:[a] ->  {v: Int | v = (len xs)} @-}
pot :: [a] -> Int
pot []     = 0
pot (x:xs) = 1 + (pot xs)

-- amortised cost 2
{-@ push :: ls:[a] -> x:a -> {t:Tick [a] | tcost t + pot (tval t) - pot ls <= 1} @-}
push ls x = pure (x:ls)

-- amortised cost 0
{-@ pop :: k:Nat -> {ls:[a] | k <= (len ls)} -> {t:Tick [a] | (tcost t) + pot (tval t) - pot ls < 1} @-}
pop :: Int -> [a] -> Tick [a]
pop 0 ls     = pure ls     
pop k (x:ls) = step 1 (pop (k-1) ls)
