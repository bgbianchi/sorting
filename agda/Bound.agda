module Bound {A : Set} (_≤_ : A → A → Set)  where

open import Data.List

data Bound : Set where
  bot : Bound 
  val : A → Bound

data LeB : Bound → Bound → Set where
  lebx : {b : Bound} 
                   → LeB bot b
  lexy : {a b : A} 
                   → a ≤ b 
                   → LeB (val a) (val b)



