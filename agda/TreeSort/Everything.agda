open import Relation.Binary.Core

module TreeSort.Everything {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)
                  (trans≤ : Transitive _≤_) where

open import TreeSort.Impl1.Correctness.Order _≤_ tot≤ trans≤
open import TreeSort.Impl1.Correctness.Permutation _≤_ tot≤

open import TreeSort.Impl2.Correctness.Order _≤_ tot≤ trans≤
open import TreeSort.Impl2.Correctness.Permutation _≤_ tot≤
