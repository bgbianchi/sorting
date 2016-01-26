module BBHeap.Complete {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_
open import Bound.Lower A 
open import Bound.Lower.Order _≤_

data Complete {b : Bound} : BBHeap b → Set where
  clf : Complete (leaf {b})
  cnd : {x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x))(l⋘r : l ⋘ r) → l ≃ r → Complete (left b≤x l⋘r)
