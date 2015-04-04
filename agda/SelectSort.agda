{-# OPTIONS --sized-types #-}
open import Data.Sum renaming (_⊎_ to _∨_)

module SelectSort  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : (x y : A) → x ≤ y ∨ y ≤ x)
                  (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)  where

open import Data.List
open import Data.Product
open import Function using (_∘_)
open import Permutation A
open import Permutation.Equivalence A
open import Size
open import SList
open import SList.Order _≤_
open import Sorting _≤_

select : {ι : Size} → A →  SList A {ι} → A × SList A {ι}
select x snil = (x , snil)
select x (y ∙ ys) with tot≤ x y
... | inj₁ x≤y with select x ys 
select x (y ∙ ys) | inj₁ x≤y  | (z , zs) = (z , y ∙ zs)
select x (y ∙ ys) | inj₂ y≤x with select y ys
select x (y ∙ ys) | inj₂ y≤x | (z , zs) = (z , x ∙ zs) 

selectSort : {ι : Size} → SList A {ι} → SList A {ι}
selectSort snil = snil
selectSort (x ∙ xs) with select x xs
... | (y , ys) = y ∙ (selectSort ys)

refl≤ : {x : A} → x ≤ x
refl≤ {x} with tot≤ x x
... | inj₁ x≤x = x≤x
... | inj₂ x≤x = x≤x 

lemma-select-≤ : {ι : Size}(x : A) → (xs : SList A {ι}) → proj₁ (select x xs) ≤ x
lemma-select-≤ x snil = refl≤
lemma-select-≤ x (y ∙ ys) with tot≤ x y
... | inj₁ x≤y = lemma-select-≤ x ys
... | inj₂ y≤x = trans≤ (lemma-select-≤ y ys) y≤x

lemma-select-*≤ : {ι : Size}(x : A) → (xs : SList A {ι}) → proj₁ (select x xs) *≤ proj₂ (select x xs)
lemma-select-*≤ x snil = genx
lemma-select-*≤ x (y ∙ ys) with tot≤ x y
... | inj₁ x≤y = gecx (trans≤ (lemma-select-≤ x ys) x≤y) (lemma-select-*≤ x ys)
... | inj₂ y≤x = gecx (trans≤ (lemma-select-≤ y ys) y≤x) (lemma-select-*≤ y ys)

lemma-select-≤-*≤ : {ι : Size}{b x : A}{xs : SList A {ι}} → b ≤ x → b *≤ xs → b ≤ proj₁ (select x xs) × b *≤ proj₂ (select x xs) 
lemma-select-≤-*≤ b≤x genx = b≤x , genx
lemma-select-≤-*≤ {x = x} b≤x (gecx {x = y} b≤y b*≤ys) with tot≤ x y
... | inj₁ x≤y = proj₁ (lemma-select-≤-*≤ b≤x b*≤ys) , gecx (trans≤ b≤x x≤y) (proj₂ (lemma-select-≤-*≤ b≤x b*≤ys))
... | inj₂ y≤x = proj₁ (lemma-select-≤-*≤ b≤y b*≤ys) , gecx (trans≤ b≤y y≤x) (proj₂ (lemma-select-≤-*≤ b≤y b*≤ys))

lemma-selectSort-*≤ : {ι : Size}{x : A}{xs : SList A {ι}} → x *≤ xs → x *≤ selectSort xs
lemma-selectSort-*≤ genx = genx
lemma-selectSort-*≤ (gecx x≤y x*≤ys) with lemma-select-≤-*≤ x≤y x*≤ys
... | (x≤z , x*≤zs) = gecx x≤z (lemma-selectSort-*≤ x*≤zs)

lemma-selectSort-sorted : {ι : Size}(xs : SList A {ι}) → Sorted (unsize A (selectSort xs))
lemma-selectSort-sorted snil = nils
lemma-selectSort-sorted (x ∙ xs) = lemma-slist-sorted (lemma-selectSort-*≤ (lemma-select-*≤ x xs)) (lemma-selectSort-sorted (proj₂ (select x xs)))

theorem-selectSort-sorted : (xs : List A) → Sorted (unsize A (selectSort (size A xs)))
theorem-selectSort-sorted = lemma-selectSort-sorted ∘ (size A)

lemma-select∼ : {ι : Size}(x : A) → (xs : SList A {ι}) → unsize A (x ∙ xs) ∼ unsize A (proj₁ (select x xs) ∙ proj₂ (select x xs))
lemma-select∼ x snil = ∼x /head /head ∼[]
lemma-select∼ x (y ∙ ys) with tot≤ x y
... | inj₁ x≤y = ∼x (/tail /head) (/tail /head) (lemma-select∼ x ys)
... | inj₂ y≤x = ∼x /head (/tail /head) (lemma-select∼ y ys)

lemma-selectSort∼ : {ι : Size}(xs : SList A {ι}) → unsize A xs ∼ unsize A (selectSort xs)
lemma-selectSort∼ snil = ∼[]
lemma-selectSort∼ (x ∙ xs) = lemma-trans∼ (lemma-select∼ x xs) (∼x /head /head (lemma-selectSort∼ (proj₂ (select x xs))))

theorem-selectSort∼ : (xs : List A) → xs ∼ unsize A (selectSort (size A xs))
theorem-selectSort∼ xs = lemma-trans∼ (lemma-unsize-size A xs) (lemma-selectSort∼ (size A xs))

