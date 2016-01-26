module BBHeap.Compound {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_
open import Bound.Lower A 
open import Bound.Lower.Order _≤_

data Compound {b : Bound} : BBHeap b → Set where
  cl : {x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x))(l⋘r : l ⋘ r) → Compound (left b≤x l⋘r)
  cr : {x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x))(l⋙r : l ⋙ r) → Compound (right b≤x l⋙r)
