
module BHeap {A : Set} (_≤_ : A → A → Set) where

open import Bound _≤_
open import Data.Nat

data BHeap : Bound → Set where
  lf : {b : Bound} 
                   → BHeap b
  nd : {b : Bound}{x : A} 
                   → LeB b (val x) 
                   → (l r : BHeap (val x)) 
                   → BHeap b

# : {b : Bound} → BHeap b → ℕ
# lf = zero
# (nd _ l r) = suc (# l + # r)

_≺_ : {b b' : Bound} → BHeap b → BHeap b' → Set 
h ≺ h' = # h <′ # h'

data Terminates {b' : Bound}(h' : BHeap b') : Set where
  termination-proof : (∀ {b} h → (_≺_ {b} {b'} h h') → Terminates h) → Terminates h'


