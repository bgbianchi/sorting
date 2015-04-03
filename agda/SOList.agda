{-# OPTIONS --sized-types #-}
module SOList {A : Set} (_≤_ : A → A → Set)  where

open import Data.List
open import Bound _≤_
open import Size
open import Sorting _≤_

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

lemma-solist-sorted : {ι : Size}{b : Bound} → (xs : SOList {ι} b) →  Sorted (forget xs)
lemma-solist-sorted onil = nils
lemma-solist-sorted (:< {x = x} _ onil) = singls x
lemma-solist-sorted (:< b≤x (:< (lexy x≤y) ys)) = conss x≤y  (lemma-solist-sorted (:< (lexy x≤y) ys))



