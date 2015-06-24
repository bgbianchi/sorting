module BHeap.Heap {A : Set}(_≤_ : A → A → Set) where

open import BHeap _≤_ 
open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import BTree.Heap _≤_

lemma-bheap-heap : {b : Bound}(h : BHeap b) → Heap (forget h)
lemma-bheap-heap lf = leaf
lemma-bheap-heap (nd {x = x} _ lf lf) = single x
lemma-bheap-heap (nd _ (nd (lexy x≤y) l r) lf) = left x≤y (lemma-bheap-heap (nd (lexy x≤y) l r))
lemma-bheap-heap (nd _ lf (nd (lexy x≤y) l r)) = right x≤y (lemma-bheap-heap (nd (lexy x≤y) l r))
lemma-bheap-heap (nd _ (nd (lexy x≤y) l r) (nd (lexy x≤y') l' r')) = both x≤y x≤y' (lemma-bheap-heap (nd (lexy x≤y) l r)) (lemma-bheap-heap (nd (lexy x≤y') l' r'))
