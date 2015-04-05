{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module Quicksort {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import Bound.Total A
open import Bound.Total.Order _≤_
open import Data.List
open import Data.Product
open import Data.Sum
open import SBList _≤_ 
open import Size
open import SOList.Total _≤_ 

deal : {ι : Size}{b t : Bound}{x : A} → LeB b (val x) → LeB (val x) t → SBList {ι} b t → SBList {ι} b (val x) × SBList {ι} (val x) t
deal b≤x x≤t (nil b≤t) = (nil b≤x , nil x≤t)
deal {x = x} b≤x x≤t (cons y b≤y y≤t ys) 
    with tot≤ x y | deal b≤x x≤t ys
... | inj₁ x≤y | (us , vs) = (us , cons y (lexy x≤y) y≤t vs)
... | inj₂ y≤x | (us , vs) = (cons y b≤y (lexy y≤x) us , vs) 

quickSort : {ι : Size}{b t : Bound} → SBList {ι} b t → SOList b t
quickSort (nil b≤t) = onil b≤t
quickSort (cons x b≤x x≤t xs) 
    with deal b≤x x≤t xs 
... | (ys , zs) = ocons x (quickSort ys) (quickSort zs)

