open import Relation.Binary.Core

module BBHeap.Subtyping {A : Set}
                  (_≤_ : A → A → Set) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_
open import Bound.Lower A 
open import Bound.Lower.Order _≤_
open import Bound.Lower.Order.Properties _≤_ trans≤

subtyping : {b b' : Bound} → LeB b' b → BBHeap b → BBHeap b'
subtyping _ leaf = leaf 
subtyping b'≤b (left b≤x l⋘r) = left (transLeB b'≤b b≤x) l⋘r
subtyping b'≤b (right b≤x l⋙r) = right (transLeB b'≤b b≤x) l⋙r
