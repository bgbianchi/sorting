module BBHeap.Heap {A : Set}(_≤_ : A → A → Set)  where

open import BBHeap _≤_ hiding (forget)
open import BHeap _≤_
open import BHeap.Heap _≤_
open import BTree.Heap _≤_
open import Bound.Lower A
open import Function using (_∘_)

lemma-bbheap-heap : {b : Bound}(h : BBHeap b) → Heap (forget (relax h))
lemma-bbheap-heap = lemma-bheap-heap ∘ relax

