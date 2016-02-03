{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module Mergesort.Impl1 {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Bound.Lower A
open import Bound.Lower.Order  _≤_
open import Data.Product
open import Data.Sum
open import Size
open import SList
open import SOList.Lower _≤_

deal : {ι : Size} → SList A {ι} → SList A {ι} × SList A {ι}
deal snil = (snil , snil) 
deal (x ∙ snil) = (x ∙ snil , snil) 
deal (x ∙ (y ∙ xs)) 
    with deal xs
... | (ys , zs) = (x ∙ ys , y ∙ zs)

merge : {ι ι' : Size}{b : Bound} → SOList {ι} b  → SOList {ι'} b → SOList b
merge onil ys = ys 
merge xs onil = xs 
merge (:< {x = x} b≤x xs)  (:< {x = y} b≤y ys) 
    with tot≤ x y
... | inj₁ x≤y = :< b≤x (merge xs (:< (lexy x≤y) ys))
... | inj₂ y≤x = :< b≤y (merge (:< (lexy y≤x) xs) ys)

mergesort : {ι : Size} → SList A {↑ ι} → SOList bot
mergesort snil = onil
mergesort (x ∙ snil) = :< {x = x} lebx onil
mergesort (x ∙ (y ∙ xs)) 
    with deal xs
... | (ys , zs) = merge (mergesort (x ∙ ys)) (mergesort (y ∙ zs))
