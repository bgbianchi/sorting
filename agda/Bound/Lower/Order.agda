module Bound.Lower.Order {A : Set}(_≤_ : A → A → Set) where

open import Bound.Lower A

data LeB : Bound → Bound → Set where
  lebx : {b : Bound} 
                   → LeB bot b
  lexy : {a b : A} 
                   → a ≤ b 
                   → LeB (val a) (val b)



