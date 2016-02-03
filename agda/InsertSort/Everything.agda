open import Relation.Binary.Core

module InsertSort.Everything {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import InsertSort.Impl1.Correctness.Order _≤_ tot≤
open import InsertSort.Impl1.Correctness.Permutation.Alternative _≤_ tot≤
open import InsertSort.Impl1.Correctness.Permutation.Base _≤_ tot≤

open import InsertSort.Impl2.Correctness.Order _≤_ tot≤
open import InsertSort.Impl2.Correctness.Permutation.Alternative _≤_ tot≤
open import InsertSort.Impl2.Correctness.Permutation.Base _≤_ tot≤
