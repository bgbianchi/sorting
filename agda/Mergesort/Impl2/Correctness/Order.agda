open import Relation.Binary.Core

module Mergesort.Impl2.Correctness.Order {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Data.List
open import Function using (_∘_)
open import List.Sorted _≤_
open import Mergesort.Impl2 _≤_ tot≤
open import OList _≤_
open import OList.Properties _≤_

theorem-mergesort-sorted : (xs : List A) → Sorted (forget (mergesort xs))
theorem-mergesort-sorted = lemma-olist-sorted  ∘ mergesort
