{-# OPTIONS --sized-types #-}
module SList.Order.Properties {A  : Set}(_≤_ : A → A → Set) where

open import List.Sorted _≤_
open import Size
open import SList
open import SList.Order _≤_

lemma-slist-sorted : {ι : Size}{x : A}{xs : SList A {ι}} → x *≤ xs → Sorted (unsize A xs) → Sorted (unsize A (x ∙ xs))
lemma-slist-sorted {x = x} genx nils = singls x
lemma-slist-sorted (gecx x≤y genx) (singls y) = conss x≤y (singls y)
lemma-slist-sorted (gecx x≤y x*≤zys ) syzys = conss x≤y syzys

lemma-sorted⊕ : {ι : Size}{x : A}{xs : SList A {ι}} → xs ≤* x → Sorted (unsize A xs) → Sorted (unsize A (_⊕_ A xs (x ∙ snil)))
lemma-sorted⊕ {x = x} {xs = snil} _ nils = singls x
lemma-sorted⊕ {x = x} {xs = y ∙ snil} (lecx y≤x _) (singls .y)  = conss y≤x (singls x)
lemma-sorted⊕ {xs = y ∙ (z ∙ ys)} (lecx y≤x zys≤*x) (conss y≤z szys) = conss y≤z (lemma-sorted⊕ zys≤*x szys)

lemma-⊕≤* : {ι : Size}{x t : A}{xs : SList A {ι}} → x ≤ t → xs ≤* t → (_⊕_ A xs (x ∙ snil)) ≤* t
lemma-⊕≤* x≤t lenx = lecx x≤t lenx
lemma-⊕≤* x≤t (lecx y≤t ys≤*t) = lecx y≤t (lemma-⊕≤* x≤t ys≤*t)
