open import Relation.Binary.Core

module BHeap.Heap {A : Set}(_≤_ : A → A → Set) where

open import BHeap _≤_ 
open import Bound.Lower A
open import BTree.Heap _≤_

lemma-bheap-heap : {b : Bound}(h : BHeap b) → Heap (forget h)
lemma-bheap-heap h = {!!}
