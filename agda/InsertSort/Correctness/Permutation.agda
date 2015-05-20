open import Relation.Binary.Core

module InsertSort.Correctness.Permutation {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.List
open import Data.Sum
open import InsertSort _≤_ tot≤
open import List.Permutation.Base A
open import OList _≤_

-- Option 1

lemma-insert∼/ : (x : A)(xs : List A) → (insert x xs) / x ⟶ xs
lemma-insert∼/ x [] = /head
lemma-insert∼/ x (y ∷ ys) 
    with tot≤ x y
... | inj₁ _ = /head
... | inj₂ _ = /tail (lemma-insert∼/ x ys)

lemma-insert∼ : (x : A){xs ys : List A} → xs ∼ ys → (x ∷ xs) ∼ (insert x ys)
lemma-insert∼ x {xs} {ys} xs∼ys = ∼x  /head (lemma-insert∼/ x ys) xs∼ys

theorem-insertSort∼ : (xs : List A) → xs ∼ (insertSort xs)
theorem-insertSort∼ [] = ∼[]
theorem-insertSort∼ (x ∷ xs) = lemma-insert∼ x (theorem-insertSort∼ xs)

-- Option 2

lemma-forget-insert' : {b : Bound} → (x : A) → (b≤x : LeB b (val x)) → (xs : OList b) → forget (insert' x b≤x xs) / x ⟶ forget xs
lemma-forget-insert' x b≤x onil = /head
lemma-forget-insert' x b≤x (:< {x = y} b≤y ys) 
    with tot≤ x y
... | inj₁ x≤y = /head
... | inj₂ y≤x = /tail (lemma-forget-insert' x (lexy y≤x) ys)

theorem-insertSort'∼ : (xs : List A) → xs ∼ forget (insertSort' xs)
theorem-insertSort'∼ [] = ∼[]
theorem-insertSort'∼ (x ∷ xs) = ∼x /head (lemma-forget-insert' x lebx (insertSort' xs)) (theorem-insertSort'∼ xs)

