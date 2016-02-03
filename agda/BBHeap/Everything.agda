open import Relation.Binary.Core

module BBHeap.Everything {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)
                  (trans≤ : Transitive _≤_) where

open import BBHeap.Complete.Base _≤_
open import BBHeap.Drop _≤_ tot≤ trans≤
open import BBHeap.DropLast _≤_
open import BBHeap.Heap _≤_
open import BBHeap.Height.Convert _≤_ tot≤
open import BBHeap.Height.Log _≤_ tot≤
open import BBHeap.Last
