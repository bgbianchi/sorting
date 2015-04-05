{-# OPTIONS --sized-types #-}
module SOList.Lower {A : Set}(_≤_ : A → A → Set)  where

open import Data.List
open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Size

data SOList : {ι : Size} → Bound → Set where
  onil : {ι : Size}{b : Bound} 
                   → SOList {↑ ι} b
  :< : {ι : Size}{b : Bound}{x : A} 
                   → LeB b (val x) 
                   → SOList {ι} (val x) 
                   → SOList {↑ ι} b

forget : {b : Bound} → SOList b → List A
forget onil = []
forget (:< {x = x} _  xs) = x ∷ forget xs



