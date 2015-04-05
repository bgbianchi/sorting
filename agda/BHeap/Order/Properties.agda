module BHeap.Order.Properties {A : Set}(_≤_ : A → A → Set) where

open import BHeap _≤_
open import BHeap.Order _≤_ renaming (Acc to Accₕ ; acc to accₕ)
open import Data.Nat
open import Induction.Nat
open import Induction.WellFounded 

ii-acc : ∀ {b} {h} → Acc _<′_ (# {b} h) → Accₕ h
ii-acc (acc rs) = accₕ (λ h' #h'<′#h → ii-acc (rs (# h') #h'<′#h))

≺-wf : ∀ {b} h → Accₕ {b} h 
≺-wf = λ h → ii-acc (<-well-founded (# h)) 

