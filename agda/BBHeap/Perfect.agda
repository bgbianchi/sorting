module BBHeap.Perfect {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_
open import Bound.Lower A 
open import Bound.Lower.Order _≤_

data Perfect {b : Bound} : BBHeap b → Set where
  plf : Perfect (leaf {b})
  pnd : {x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x))(l⋘r : l ⋘ r) → l ≃ r → Perfect (left b≤x l⋘r)
