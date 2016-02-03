open import Relation.Binary.Core

module BHeap.Everything {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import BHeap.Heap _≤_
open import BHeap.Height _≤_ tot≤
