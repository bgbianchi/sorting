{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module Mergesort.Correctness.Order {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Data.List
open import Function using (_∘_)
open import List.Sorted _≤_
open import Mergesort _≤_ tot≤
open import SList
open import SOList.Lower _≤_
open import SOList.Lower.Properties _≤_

theorem-mergesort-sorted : (xs : List A) → Sorted (forget (mergesort (size A xs)))
theorem-mergesort-sorted = lemma-solist-sorted  ∘ mergesort ∘ (size A)

