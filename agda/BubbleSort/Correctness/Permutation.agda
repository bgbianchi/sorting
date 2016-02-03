{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module BubbleSort.Correctness.Permutation {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import BubbleSort _≤_ tot≤
open import Data.Product
open import Data.List
open import Data.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Equivalence A
open import Size
open import SList
open import SList.Properties A
open import SList.Concatenation A

lemma-swap*∼ : {ι : Size}(x : A) → (xs : SList A {ι}) → unsize A (x ∙ xs) ∼ unsize A (proj₂ (swap* x xs) ∙ proj₁ (swap* x xs))
lemma-swap*∼ x snil = ∼x /head /head ∼[]
lemma-swap*∼ x (y ∙ ys) 
    with tot≤ x y
... | inj₁ x≤y = ∼x /head (/tail /head) (lemma-swap*∼ y ys)
... | inj₂ y≤x = ∼x (/tail /head) (/tail /head) (lemma-swap*∼ x ys)

lemma-bubbleSort∼ : {ι : Size}(xs : SList A {ι}) → unsize A xs ∼ unsize A (bubbleSort xs)
lemma-bubbleSort∼ snil = ∼[]
lemma-bubbleSort∼ (x ∙ xs) = trans∼ (lemma-swap*∼ x xs) (trans∼ (lemma-⊕∼ y (lemma-bubbleSort∼ ys)) (lemma-size-unsize y (bubbleSort ys)))
                  where sxxs = swap* x xs
                        ys = proj₁ sxxs
                        y = proj₂ sxxs

theorem-bubbleSort∼ : (xs : List A) → xs ∼ unsize A (bubbleSort (size A xs))
theorem-bubbleSort∼ xs = trans∼ (lemma-unsize-size xs) (lemma-bubbleSort∼ (size A xs))


