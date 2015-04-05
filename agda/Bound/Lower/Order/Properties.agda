open import Relation.Binary.Core

module Bound.Lower.Order.Properties {A : Set} 
                 (_≤_ : A → A → Set) 
                 (trans≤ : Transitive _≤_)  where

open import Bound.Lower A
open import Bound.Lower.Order _≤_

transLeB : {a b c : Bound} → LeB a b → LeB b c → LeB a c
transLeB lebx _ = lebx
transLeB (lexy x≤y) (lexy y≤z) = lexy (trans≤ x≤y y≤z) 
