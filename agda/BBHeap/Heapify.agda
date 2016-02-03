open import Relation.Binary.Core

module BBHeap.Heapify {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_
open import BBHeap.Insert _≤_ tot≤ trans≤
open import Bound.Lower A 
open import Bound.Lower.Order _≤_  
open import Data.List

heapify : List A → BBHeap bot
heapify [] = leaf
heapify (x ∷ xs) = insert {x = x} lebx (heapify xs) 
