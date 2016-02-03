open import Relation.Binary.Core

module BubbleSort.Everything {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)
                  (trans≤ : Transitive _≤_) where

open import BubbleSort.Correctness.Order _≤_ tot≤ trans≤
open import BubbleSort.Correctness.Permutation _≤_ tot≤ 
