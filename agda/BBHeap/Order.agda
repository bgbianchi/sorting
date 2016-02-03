module BBHeap.Order {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_
open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.Nat

_≺_ : {b b' : Bound} → BBHeap b → BBHeap b' → Set 
h ≺ h' = # h <′ # h'

data Acc {b' : Bound}(h' : BBHeap b') : Set where
  acc : (∀ {b} h → (_≺_ {b} {b'} h h') → Acc h) → Acc h'

