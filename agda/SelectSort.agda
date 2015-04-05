{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module SelectSort  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import Data.List
open import Data.Product
open import Data.Sum
open import Size
open import SList
open import SList.Order _≤_

select : {ι : Size} → A →  SList A {ι} → A × SList A {ι}
select x snil = (x , snil)
select x (y ∙ ys) 
    with tot≤ x y
... | inj₁ x≤y 
    with select x ys 
select x (y ∙ ys) | inj₁ x≤y  | (z , zs) = (z , y ∙ zs)
select x (y ∙ ys) | inj₂ y≤x 
    with select y ys
select x (y ∙ ys) | inj₂ y≤x | (z , zs) = (z , x ∙ zs) 

selectSort : {ι : Size} → SList A {ι} → SList A {ι}
selectSort snil = snil
selectSort (x ∙ xs) 
    with select x xs
... | (y , ys) = y ∙ (selectSort ys)
