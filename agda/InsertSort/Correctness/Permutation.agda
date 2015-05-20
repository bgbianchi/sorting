open import Relation.Binary.Core

module InsertSort.Correctness.Permutation {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.List
open import Data.Sum
open import Function
open import InsertSort _≤_ tot≤
open import List.Permutation.Alternative A renaming (_∼_ to _∼′_)
open import List.Permutation.Alternative.Correctness A 
open import List.Permutation.Base A
open import OList _≤_

-- Option 1

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

-- Option 2

lemma-forget-insert' : {b : Bound} → (x : A) → (b≤x : LeB b (val x)) → (xs : OList b) → forget (insert' b≤x xs) / x ⟶ forget xs
lemma-forget-insert' x b≤x onil = /head
lemma-forget-insert' x b≤x (:< {x = y} b≤y ys) 
    with tot≤ x y
... | inj₁ x≤y = /head
... | inj₂ y≤x = /tail (lemma-forget-insert' x (lexy y≤x) ys)

theorem-insertSort'∼ : (xs : List A) → xs ∼ forget (insertSort' xs)
theorem-insertSort'∼ [] = ∼[]
theorem-insertSort'∼ (x ∷ xs) = ∼x /head (lemma-forget-insert' x lebx (insertSort' xs)) (theorem-insertSort'∼ xs)

-- Option 3

lemma-insert∼′ : (x : A)(xs : List A) → (x ∷ xs) ∼′ insert x xs
lemma-insert∼′ x [] = ∼refl
lemma-insert∼′ x (y ∷ ys) 
    with tot≤ x y
... | inj₁ x≤y = ∼refl
... | inj₂ y≤x = ∼trans (∼swap ∼refl) (∼head y (lemma-insert∼′ x ys)) 

lemma-insertSort∼′ : (xs : List A) → xs ∼′ insertSort xs
lemma-insertSort∼′ [] = ∼refl
lemma-insertSort∼′ (x ∷ xs) = ∼trans (∼head x (lemma-insertSort∼′ xs)) (lemma-insert∼′ x (insertSort xs))

theorem-insertSort∼' : (xs : List A) → xs ∼ insertSort xs
theorem-insertSort∼' = lemma-∼′-∼ ∘ lemma-insertSort∼′

-- Option 4

lemma-insert'∼′ : {b : Bound}{x : A} → (b≤x : LeB b (val x)) → (xs : OList b) → (x ∷ forget xs) ∼′ forget (insert' b≤x xs)
lemma-insert'∼′ b≤x onil = ∼refl
lemma-insert'∼′ {x = x} b≤x (:< {x = y} b≤y ys) 
    with tot≤ x y
... | inj₁ x≤y = ∼refl
... | inj₂ y≤x = ∼trans (∼swap ∼refl) (∼head y (lemma-insert'∼′ (lexy y≤x) ys)) 

lemma-insertSort'∼′ : (xs : List A) → xs ∼′ forget (insertSort' xs)
lemma-insertSort'∼′ [] = ∼refl
lemma-insertSort'∼′ (x ∷ xs) = ∼trans (∼head x (lemma-insertSort'∼′ xs)) (lemma-insert'∼′ lebx (insertSort' xs))

theorem-insertSort'∼' : (xs : List A) → xs ∼ forget (insertSort' xs)
theorem-insertSort'∼' = lemma-∼′-∼ ∘ lemma-insertSort'∼′
