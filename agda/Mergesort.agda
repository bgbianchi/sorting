{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module Mergesort {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Bound.Lower A
open import Bound.Lower.Order  _≤_
open import Data.List
open import Data.Product
open import Data.Sum
open import Function
open import LRTree {A}
open import OList _≤_ 
open import Size
open import SList
open import SOList.Lower _≤_

-- Option 1

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

-- Option 2

mutual 
  merge'' : {b : Bound} → OList b → OList b → OList b
  merge'' onil ys = ys
  merge'' xs onil = xs
  merge'' (:< {x = x} b≤x xs) (:< {x = y} b≤y ys) 
      with tot≤ x y
  ... | inj₁ x≤y  = :< b≤x (merge'' xs (:< (lexy x≤y) ys))
  ... | inj₂ y≤x = :< b≤y (merge''xs (lexy y≤x) xs ys)

  merge''xs : {b : Bound}{x : A} → LeB b (val x) → OList (val x) → OList b → OList b
  merge''xs b≤x xs onil = :< b≤x xs
  merge''xs {x = x} b≤x xs (:< {x = y} b≤y ys) 
      with tot≤ x y
  ... | inj₁ x≤y = :< b≤x (merge'' xs (:< (lexy x≤y) ys))
  ... | inj₂ y≤x = :< b≤y (merge''xs (lexy y≤x) xs ys)

deal' : List A → LRTree
deal' = foldr insert empty

merge' : LRTree → OList bot
merge' empty = onil
merge' (leaf x) = :< (lebx {val x}) onil
merge' (node t l r) = merge'' (merge' l) (merge' r)

mergesort' : List A → OList bot
mergesort' = merge' ∘ deal'
