module OList {A : Set}(_≤_ : A → A → Set) where

open import Data.List
open import Bound.Lower A
open import Bound.Lower.Order _≤_

data OList : Bound → Set where
  onil : {b : Bound} 
                   → OList b
  :< : {b : Bound}{x : A} 
                   → LeB b (val x) 
                   → OList (val x) 
                   → OList b

forget : {b : Bound} → OList b → List A
forget onil = []
forget ( :< {x = x} _  xs) = x ∷ forget xs

