{-# OPTIONS --sized-types #-}
module BBHeap.Height {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_ hiding (#)
open import Bound.Lower A 
open import Bound.Lower.Order _≤_
open import SNat

# : {b : Bound} → BBHeap b → SNat
# leaf = zero
# (left {l = l} {r = r} _ _) = succ (# l + # r)
# (right {l = l} {r = r} _ _) = succ (# l + # r)

height : {b : Bound} → BBHeap b → SNat
height leaf = zero
height (left {l = l} _ _) = succ (height l)
height (right {l = l} _ _) = succ (height l)

#' : {b : Bound} → BBHeap b → SNat
#' leaf = zero
#' (left {r = r}  _ _) = succ (#' r + #' r)
#' (right {r = r} _ _) = succ (#' r + #' r)

height' : {b : Bound} → BBHeap b → SNat
height' leaf = zero
height' (left {r = r} _ _) = succ (height' r)
height' (right {r = r} _ _) = succ (height' r)


