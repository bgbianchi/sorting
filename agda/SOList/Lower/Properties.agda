{-# OPTIONS --sized-types #-}
module SOList.Lower.Properties {A : Set}(_≤_ : A → A → Set)  where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Size
open import List.Sorted _≤_
open import SOList.Lower _≤_

lemma-solist-sorted : {ι : Size}{b : Bound} → (xs : SOList {ι} b) →  Sorted (forget xs)
lemma-solist-sorted onil = nils
lemma-solist-sorted (:< {x = x} _ onil) = singls x
lemma-solist-sorted (:< b≤x (:< (lexy x≤y) ys)) = conss x≤y  (lemma-solist-sorted (:< (lexy x≤y) ys))



