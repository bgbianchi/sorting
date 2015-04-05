{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module Quicksort.Correctness.Order {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)
                  (trans≤ : Transitive _≤_)  where

open import Data.List
open import Function using (_∘_)
open import List.Sorted _≤_
open import Quicksort _≤_ tot≤
open import SBList _≤_
open import Size
open import SOList.Total _≤_
open import SOList.Total.Properties _≤_ trans≤

theorem-quickSort-sorted : (xs : List A) → Sorted (forget (quickSort (bound xs)))
theorem-quickSort-sorted = lemma-solist-sorted ∘ quickSort ∘ bound
