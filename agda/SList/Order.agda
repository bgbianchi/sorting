{-# OPTIONS --sized-types #-}
module SList.Order  {A : Set} (_≤_ : A → A → Set) where

open import Size
open import SList
open import Sorting _≤_

data _*≤_ : {ι : Size} → A → SList A {ι} → Set where
  genx : {ι : Size}{b : A} → (_*≤_) {↑ ι} b snil
  gecx : {ι : Size}{b x : A}{xs : SList A {ι}} → b ≤ x → b *≤ xs → b *≤ (x ∙ xs)

lemma-slist-sorted : {ι : Size}{x : A}{xs : SList A {ι}} → x *≤ xs → Sorted (unsize A xs) → Sorted (unsize A (x ∙ xs))
lemma-slist-sorted {x = x} genx nils = singls x
lemma-slist-sorted (gecx x≤y genx) (singls y) = conss x≤y (singls y)
lemma-slist-sorted (gecx x≤y x*≤zys ) syzys = conss x≤y syzys
