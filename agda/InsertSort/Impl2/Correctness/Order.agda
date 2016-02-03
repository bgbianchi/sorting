open import Relation.Binary.Core

module InsertSort.Impl2.Correctness.Order {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Data.List
open import Function using (_∘_)
open import InsertSort.Impl2 _≤_ tot≤
open import List.Sorted _≤_
open import OList _≤_
open import OList.Properties _≤_

theorem-insertSort-sorted : (xs : List A) → Sorted (forget (insertSort xs))
theorem-insertSort-sorted = lemma-olist-sorted ∘ insertSort


