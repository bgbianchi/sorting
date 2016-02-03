open import Relation.Binary.Core

module Heapsort.Everything {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)
                  (trans≤ : Transitive _≤_) where

open import Heapsort.Impl1.Correctness.Order _≤_ tot≤ trans≤
open import Heapsort.Impl1.Correctness.Permutation _≤_ tot≤ trans≤

open import Heapsort.Impl2.Correctness.Order _≤_ tot≤ trans≤
open import Heapsort.Impl2.Correctness.Permutation _≤_ tot≤ trans≤
