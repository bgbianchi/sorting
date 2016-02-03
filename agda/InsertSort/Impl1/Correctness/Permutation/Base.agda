open import Relation.Binary.Core

module InsertSort.Impl1.Correctness.Permutation.Base {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import Data.List
open import Data.Sum
open import InsertSort.Impl1 _≤_ tot≤
open import List.Permutation.Base A

lemma-insert∼/ : (x : A)(xs : List A) → (insert x xs) / x ⟶ xs
lemma-insert∼/ x [] = /head
lemma-insert∼/ x (y ∷ ys) 
    with tot≤ x y
... | inj₁ _ = /head
... | inj₂ _ = /tail (lemma-insert∼/ x ys)

lemma-insert∼ : {xs ys : List A}(x : A) → xs ∼ ys → (x ∷ xs) ∼ insert x ys
lemma-insert∼ {xs} {ys} x xs∼ys = ∼x  /head (lemma-insert∼/ x ys) xs∼ys

theorem-insertSort∼ : (xs : List A) → xs ∼ insertSort xs
theorem-insertSort∼ [] = ∼[]
theorem-insertSort∼ (x ∷ xs) = lemma-insert∼ x (theorem-insertSort∼ xs)
