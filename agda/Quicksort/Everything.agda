open import Relation.Binary.Core

module Quicksort.Everything {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)
                  (trans≤ : Transitive _≤_) where

open import Quicksort.Correctness.Order _≤_ tot≤ trans≤
open import Quicksort.Correctness.Permutation _≤_ tot≤ 
