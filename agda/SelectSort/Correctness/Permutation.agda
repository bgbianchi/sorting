{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module SelectSort.Correctness.Permutation {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_ ) where

open import Data.List
open import Data.Product
open import Data.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Equivalence A
open import Size
open import SList
open import SList.Properties
open import SelectSort _≤_ tot≤

lemma-select∼ : {ι : Size}(x : A) → (xs : SList A {ι}) → unsize A (x ∙ xs) ∼ unsize A (proj₁ (select x xs) ∙ proj₂ (select x xs))
lemma-select∼ x snil = ∼x /head /head ∼[]
lemma-select∼ x (y ∙ ys) 
    with tot≤ x y
... | inj₁ x≤y = ∼x (/tail /head) (/tail /head) (lemma-select∼ x ys)
... | inj₂ y≤x = ∼x /head (/tail /head) (lemma-select∼ y ys)

lemma-selectSort∼ : {ι : Size}(xs : SList A {ι}) → unsize A xs ∼ unsize A (selectSort xs)
lemma-selectSort∼ snil = ∼[]
lemma-selectSort∼ (x ∙ xs) = trans∼ (lemma-select∼ x xs) (∼x /head /head (lemma-selectSort∼ (proj₂ (select x xs))))

theorem-selectSort∼ : (xs : List A) → xs ∼ unsize A (selectSort (size A xs))
theorem-selectSort∼ xs = trans∼ (lemma-unsize-size A xs) (lemma-selectSort∼ (size A xs))

