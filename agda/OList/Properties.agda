module OList.Properties {A : Set}(_≤_ : A → A → Set) where

open import Data.List
open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import List.Sorted _≤_
open import OList _≤_

lemma-olist-sorted : {b : Bound} → (xs : OList b) → Sorted (forget xs)
lemma-olist-sorted onil = nils
lemma-olist-sorted (:< {x = x} _ onil) = singls x
lemma-olist-sorted (:< b≤x (:< (lexy x≤y) ys)) = conss x≤y (lemma-olist-sorted (:< (lexy x≤y) ys))


