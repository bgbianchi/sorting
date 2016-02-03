open import Relation.Binary.Core

module InsertSort.Impl2.Correctness.Permutation.Alternative {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.List
open import Data.Sum
open import Function
open import InsertSort.Impl2 _≤_ tot≤
open import List.Permutation.Alternative A renaming (_∼_ to _∼′_)
open import List.Permutation.Alternative.Correctness A 
open import List.Permutation.Base A
open import OList _≤_

lemma-insert∼′ : {b : Bound}{x : A}(b≤x : LeB b (val x))(xs : OList b) → (x ∷ forget xs) ∼′ forget (insert b≤x xs)
lemma-insert∼′ b≤x onil = ∼refl
lemma-insert∼′ {x = x} b≤x (:< {x = y} b≤y ys) 
    with tot≤ x y
... | inj₁ x≤y = ∼refl
... | inj₂ y≤x = ∼trans (∼swap ∼refl) (∼head y (lemma-insert∼′ (lexy y≤x) ys)) 

lemma-insertSort∼′ : (xs : List A) → xs ∼′ forget (insertSort xs)
lemma-insertSort∼′ [] = ∼refl
lemma-insertSort∼′ (x ∷ xs) = ∼trans (∼head x (lemma-insertSort∼′ xs)) (lemma-insert∼′ lebx (insertSort xs))

theorem-insertSort∼ : (xs : List A) → xs ∼ forget (insertSort xs)
theorem-insertSort∼ = lemma-∼′-∼ ∘ lemma-insertSort∼′
