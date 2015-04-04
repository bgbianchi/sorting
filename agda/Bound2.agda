module Bound2 {A : Set} (_≤_ : A → A → Set) where

open import Data.List

data Bound : Set where
  bot : Bound 
  val : A → Bound
  top : Bound

data LeB : Bound → Bound → Set where
  lebx : {b : Bound} 
                   → LeB bot b
  lexy : {x y : A} 
                   → x ≤ y 
                   → LeB (val x) (val y)
  lext : {b : Bound} 
                   → LeB b top

lemma-LeB≤ : {x y : A} → LeB (val x) (val y) → x ≤ y
lemma-LeB≤ (lexy x≤y) = x≤y

