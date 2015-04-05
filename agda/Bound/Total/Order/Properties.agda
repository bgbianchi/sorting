open import Relation.Binary.Core

module Bound.Total.Order.Properties {A : Set} 
                 (_≤_ : A → A → Set) 
                 (trans≤ : Transitive _≤_)  where

open import Bound.Total A
open import Bound.Total.Order _≤_

lemma-LeB≤ : {x y : A} → LeB (val x) (val y) → x ≤ y
lemma-LeB≤ (lexy x≤y) = x≤y

transLeB : {a b c : Bound} → LeB a b → LeB b c → LeB a c
transLeB lebx _ = lebx
transLeB _ lext = lext
transLeB (lexy x≤y) (lexy y≤z) = lexy (trans≤ x≤y y≤z) 
