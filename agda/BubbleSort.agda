{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module BubbleSort  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import Data.List
open import Data.Product
open import Data.Sum
open import Size
open import SList

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
