{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module SelectSort.Correctness.Order  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)
                  (trans≤ : Transitive _≤_)  where

open import Data.List
open import Data.Product
open import Data.Sum
open import Function using (_∘_)
open import List.Sorted _≤_
open import Order.Total _≤_ tot≤
open import Size
open import SList
open import SList.Order _≤_
open import SList.Order.Properties _≤_
open import SelectSort _≤_ tot≤

lemma-select-≤ : {ι : Size}(x : A) → (xs : SList A {ι}) → proj₁ (select x xs) ≤ x
lemma-select-≤ x snil = refl≤
lemma-select-≤ x (y ∙ ys) 
    with tot≤ x y
... | inj₁ x≤y = lemma-select-≤ x ys
... | inj₂ y≤x = trans≤ (lemma-select-≤ y ys) y≤x

lemma-select-*≤ : {ι : Size}(x : A) → (xs : SList A {ι}) → proj₁ (select x xs) *≤ proj₂ (select x xs)
lemma-select-*≤ x snil = genx
lemma-select-*≤ x (y ∙ ys) 
    with tot≤ x y
... | inj₁ x≤y = gecx (trans≤ (lemma-select-≤ x ys) x≤y) (lemma-select-*≤ x ys)
... | inj₂ y≤x = gecx (trans≤ (lemma-select-≤ y ys) y≤x) (lemma-select-*≤ y ys)

lemma-select-≤-*≤ : {ι : Size}{b x : A}{xs : SList A {ι}} → b ≤ x → b *≤ xs → b ≤ proj₁ (select x xs) × b *≤ proj₂ (select x xs) 
lemma-select-≤-*≤ b≤x genx = b≤x , genx
lemma-select-≤-*≤ {x = x} b≤x (gecx {x = y} b≤y b*≤ys) 
    with tot≤ x y
... | inj₁ x≤y = proj₁ (lemma-select-≤-*≤ b≤x b*≤ys) , gecx (trans≤ b≤x x≤y) (proj₂ (lemma-select-≤-*≤ b≤x b*≤ys))
... | inj₂ y≤x = proj₁ (lemma-select-≤-*≤ b≤y b*≤ys) , gecx (trans≤ b≤y y≤x) (proj₂ (lemma-select-≤-*≤ b≤y b*≤ys))

lemma-selectSort-*≤ : {ι : Size}{x : A}{xs : SList A {ι}} → x *≤ xs → x *≤ selectSort xs
lemma-selectSort-*≤ genx = genx
lemma-selectSort-*≤ (gecx x≤y x*≤ys) 
    with lemma-select-≤-*≤ x≤y x*≤ys
... | (x≤z , x*≤zs) = gecx x≤z (lemma-selectSort-*≤ x*≤zs)

lemma-selectSort-sorted : {ι : Size}(xs : SList A {ι}) → Sorted (unsize A (selectSort xs))
lemma-selectSort-sorted snil = nils
lemma-selectSort-sorted (x ∙ xs) = lemma-slist-sorted (lemma-selectSort-*≤ (lemma-select-*≤ x xs)) (lemma-selectSort-sorted (proj₂ (select x xs)))

theorem-selectSort-sorted : (xs : List A) → Sorted (unsize A (selectSort (size A xs)))
theorem-selectSort-sorted = lemma-selectSort-sorted ∘ (size A)

