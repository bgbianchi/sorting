
module BHeap {A : Set} (_≤_ : A → A → Set) where

open import Bound _≤_
open import Data.Nat
open import Induction.Nat
open import Induction.WellFounded 

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

ii-acc : ∀ {b} {h} → Acc _<′_ (# {b} h) → Terminates h
ii-acc (acc rs) = termination-proof (λ h' #h'<′#h → ii-acc (rs (# h') #h'<′#h))

≺-wf : ∀ {b} h → Terminates {b} h 
≺-wf = λ h → ii-acc (<-well-founded (# h)) 


