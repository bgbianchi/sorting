{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module BubbleSort.Correctness.Order  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BubbleSort _≤_ tot≤
open import Data.Product
open import Data.List
open import Data.Sum
open import Function using (_∘_)
open import List.Sorted _≤_
open import Order.Total _≤_ tot≤
open import Size
open import SList
open import SList.Order _≤_
open import SList.Order.Properties _≤_

lemma-swap*-≤*-≤ : {ι : Size}{x t : A}{xs : SList A {ι}} → x ≤ t → xs ≤* t → proj₁ (swap* x xs) ≤* t × proj₂ (swap* x xs) ≤ t
lemma-swap*-≤*-≤ x≤t lenx = lenx , x≤t
lemma-swap*-≤*-≤ {x = x} x≤t (lecx {x = y} y≤t ys≤*t) 
    with tot≤ x y
... | inj₁ x≤y = lecx x≤t (proj₁ (lemma-swap*-≤*-≤ y≤t ys≤*t)), proj₂ (lemma-swap*-≤*-≤ y≤t ys≤*t)
... | inj₂ y≤x = lecx y≤t (proj₁ (lemma-swap*-≤*-≤ x≤t ys≤*t)), proj₂ (lemma-swap*-≤*-≤ x≤t ys≤*t)

lemma-bubbleSort-≤* : {ι : Size}{t : A}{xs : SList A {ι}} → xs ≤* t → bubbleSort xs ≤* t
lemma-bubbleSort-≤* lenx = lenx
lemma-bubbleSort-≤* (lecx x≤t xs≤*t) 
    with lemma-swap*-≤*-≤ x≤t xs≤*t
... | (zs≤*t , z≤t) = lemma-⊕≤* z≤t (lemma-bubbleSort-≤* zs≤*t)

lemma-swap*-≤ : {ι : Size}(x : A) → (xs : SList A {ι}) → x ≤ proj₂ (swap* x xs)
lemma-swap*-≤ x snil = refl≤
lemma-swap*-≤ x (y ∙ ys) 
    with tot≤ x y
... | inj₁ x≤y = trans≤ x≤y (lemma-swap*-≤ y ys)
... | inj₂ y≤x = lemma-swap*-≤ x ys 

lemma-swap*-≤* : {ι : Size}(x : A) → (xs : SList A {ι}) → proj₁ (swap* x xs) ≤* proj₂ (swap* x xs)
lemma-swap*-≤* x snil = lenx
lemma-swap*-≤* x (y ∙ ys) 
    with tot≤ x y
... | inj₁ x≤y = lecx (trans≤ x≤y (lemma-swap*-≤ y ys)) (lemma-swap*-≤* y ys)
... | inj₂ y≤x = lecx (trans≤ y≤x (lemma-swap*-≤ x ys)) (lemma-swap*-≤* x ys)

lemma-bubbleSort-sorted : {ι : Size}(xs : SList A {ι}) → Sorted (unsize A (bubbleSort xs))
lemma-bubbleSort-sorted snil = nils
lemma-bubbleSort-sorted (x ∙ xs) = lemma-sorted⊕ (lemma-bubbleSort-≤* (lemma-swap*-≤* x xs)) (lemma-bubbleSort-sorted (proj₁ (swap* x xs)))

theorem-bubbleSort-sorted : (xs : List A) → Sorted (unsize A (bubbleSort (size A xs)))
theorem-bubbleSort-sorted = lemma-bubbleSort-sorted ∘ (size A)



