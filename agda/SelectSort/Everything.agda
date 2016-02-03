open import Relation.Binary.Core

module SelectSort.Everything {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)
                  (trans≤ : Transitive _≤_) where

open import SelectSort.Correctness.Order _≤_ tot≤ trans≤
open import SelectSort.Correctness.Permutation _≤_ tot≤
