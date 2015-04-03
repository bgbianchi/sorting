open import Data.Sum renaming (_⊎_ to _∨_)

module OList {A : Set} (_≤_ : A → A → Set) where

open import Data.List
open import Bound _≤_
open import Sorting _≤_

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

lemma-olist-sorted : {b : Bound} → (xs : OList b) → Sorted (forget xs)
lemma-olist-sorted onil = nils
lemma-olist-sorted (:< {x = x} _ onil) = singls x
lemma-olist-sorted (:< b≤x (:< (lexy x≤y) ys)) = conss x≤y (lemma-olist-sorted (:< (lexy x≤y) ys))


