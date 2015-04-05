{-# OPTIONS --sized-types #-}
module SList.Order {A : Set}(_≤_ : A → A → Set) where

open import List.Sorted _≤_
open import Size
open import SList

data _*≤_ : {ι : Size} → A → SList A {ι} → Set where
  genx : {ι : Size}{b : A} 
                   → (_*≤_) {↑ ι} b snil
  gecx : {ι : Size}{b x : A}{xs : SList A {ι}} 
                   → b ≤ x 
                   → b *≤ xs 
                   → b *≤ (x ∙ xs)

data _≤*_ : {ι : Size} → SList A {ι} → A → Set where
  lenx : {ι : Size}{t : A} 
                   → (_≤*_) {↑ ι} snil t
  lecx : {ι : Size}{x t : A}{xs : SList A {ι}} 
                   → x ≤ t 
                   → xs ≤* t 
                   → (x ∙ xs) ≤* t


