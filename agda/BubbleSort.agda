{-# OPTIONS --sized-types #-}
open import Data.Sum renaming (_⊎_ to _∨_)

module BubbleSort  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : (x y : A) → x ≤ y ∨ y ≤ x) 
                  (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z) where

open import Data.Nat
open import Data.Product
open import Data.List
open import Function using (_∘_)
open import Permutation A
open import Permutation.Equivalence A
open import Size
open import SList
open import SList.Order _≤_
open import Sorting _≤_

swap* : {ι : Size} → A → SList A {ι} → SList A {ι} × A
swap* x snil = (snil , x)
swap* x (y ∙ ys) 
    with tot≤ x y
... | inj₁ x≤y 
     with swap* y ys
swap* x (y ∙ ys) | inj₁ x≤y | (zs , z) = (x ∙ zs , z)
swap* x (y ∙ ys) | inj₂ y≤x 
    with swap* x ys
swap* x (y ∙ ys) | inj₂ y≤x | (zs , z) = (y ∙ zs , z)

bubbleSort : {ι : Size} → SList A {ι} → SList A
bubbleSort snil = snil
bubbleSort (x ∙ xs) 
    with swap* x xs
... | (ys , y) = _⊕_ A (bubbleSort ys) (y ∙ snil)

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

refl≤ : {x : A} → x ≤ x
refl≤ {x} 
    with tot≤ x x
... | inj₁ x≤x = x≤x
... | inj₂ x≤x = x≤x 

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

lemma-swap*∼ : {ι : Size}(x : A) → (xs : SList A {ι}) → unsize A (x ∙ xs) ∼ unsize A (proj₂ (swap* x xs) ∙ proj₁ (swap* x xs))
lemma-swap*∼ x snil = ∼x /head /head ∼[]
lemma-swap*∼ x (y ∙ ys) 
    with tot≤ x y
... | inj₁ x≤y = ∼x /head (/tail /head) (lemma-swap*∼ y ys)
... | inj₂ y≤x = ∼x (/tail /head) (/tail /head) (lemma-swap*∼ x ys)

lemma-bubbleSort∼ : {ι : Size}(xs : SList A {ι}) → unsize A xs ∼ unsize A (bubbleSort xs)
lemma-bubbleSort∼ snil = ∼[]
lemma-bubbleSort∼ (x ∙ xs) = lemma-trans∼ (lemma-swap*∼ x xs) (lemma-trans∼ (lemma-⊕∼ A y (lemma-bubbleSort∼ ys)) (lemma-size-unsize A y (bubbleSort ys)))
                  where sxxs = swap* x xs
                        ys = proj₁ sxxs
                        y = proj₂ sxxs

theorem-bubbleSort∼ : (xs : List A) → xs ∼ unsize A (bubbleSort (size A xs))
theorem-bubbleSort∼ xs = lemma-trans∼ (lemma-unsize-size A xs) (lemma-bubbleSort∼ (size A xs))


