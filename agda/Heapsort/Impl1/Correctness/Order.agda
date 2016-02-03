open import Relation.Binary.Core

module Heapsort.Impl1.Correctness.Order {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import Data.List
open import Function using (_∘_)
open import Heapsort.Impl1 _≤_ tot≤ trans≤
open import List.Sorted _≤_
open import OList _≤_
open import OList.Properties _≤_

theorem-heapsort-sorted : (xs : List A) → Sorted (forget (heapsort xs))
theorem-heapsort-sorted = lemma-olist-sorted ∘ heapsort
