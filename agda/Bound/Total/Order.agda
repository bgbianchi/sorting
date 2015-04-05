module Bound.Total.Order {A : Set}(_≤_ : A → A → Set)  where

open import Bound.Total A

data LeB : Bound → Bound → Set where
  lebx : {b : Bound} 
                   → LeB bot b
  lexy : {x y : A} 
                   → x ≤ y 
                   → LeB (val x) (val y)
  lext : {b : Bound} 
                   → LeB b top
