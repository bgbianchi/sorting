open import Relation.Binary.Core

module InsertSort.Impl1.Correctness.Permutation.Alternative {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import Data.List
open import Data.Sum
open import Function
open import InsertSort.Impl1 _≤_ tot≤
open import List.Permutation.Alternative A renaming (_∼_ to _∼′_)
open import List.Permutation.Alternative.Correctness A 
open import List.Permutation.Base A

lemma-insert∼′ : (x : A)(xs : List A) → (x ∷ xs) ∼′ insert x xs
lemma-insert∼′ x [] = ∼refl
lemma-insert∼′ x (y ∷ ys) 
    with tot≤ x y
... | inj₁ x≤y = ∼refl
... | inj₂ y≤x = ∼trans (∼swap ∼refl) (∼head y (lemma-insert∼′ x ys)) 

lemma-insertSort∼′ : (xs : List A) → xs ∼′ insertSort xs
lemma-insertSort∼′ [] = ∼refl
lemma-insertSort∼′ (x ∷ xs) = ∼trans (∼head x (lemma-insertSort∼′ xs)) (lemma-insert∼′ x (insertSort xs))

theorem-insertSort∼ : (xs : List A) → xs ∼ insertSort xs
theorem-insertSort∼ = lemma-∼′-∼ ∘ lemma-insertSort∼′
