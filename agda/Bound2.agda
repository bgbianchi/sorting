module Bound2 {A : Set} 
                 (_≤_ : A → A → Set) 
                 (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)  where

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

transLeB : {a b c : Bound} → LeB a b → LeB b c → LeB a c
transLeB lebx _ = lebx
transLeB _ lext = lext
transLeB (lexy x≤y) (lexy y≤z) = lexy (trans≤ x≤y y≤z) 
