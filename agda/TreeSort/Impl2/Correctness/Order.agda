open import Relation.Binary.Core

module TreeSort.Impl2.Correctness.Order  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_)  where

open import BBSTree _≤_ 
open import BBSTree.Properties _≤_ trans≤
open import Data.List
open import Function using (_∘_)
open import List.Sorted _≤_
open import TreeSort.Impl2 _≤_ tot≤

theorem-treeSort-sorted : (xs : List A) → Sorted (flatten (treeSort xs))
theorem-treeSort-sorted = lemma-bbst-sorted ∘ treeSort




