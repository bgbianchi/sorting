open import Relation.Binary.Core

module Mergesort.Everything {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import Mergesort.Impl1.Correctness.Order _≤_ tot≤
open import Mergesort.Impl1.Correctness.Permutation _≤_ tot≤

open import Mergesort.Impl2.Correctness.Order _≤_ tot≤
open import Mergesort.Impl2.Correctness.Permutation _≤_ tot≤
