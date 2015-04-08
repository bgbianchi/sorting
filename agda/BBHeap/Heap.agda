module BBHeap.Heap {A : Set}(_≤_ : A → A → Set)  where

open import BBHeap _≤_
open import BHeap _≤_ renaming (forget to forget')
open import BHeap.Heap _≤_
open import BTree.Heap _≤_
open import Bound.Lower A
open import Relation.Binary.PropositionalEquality

lemma-forget-forget' : {b : Bound}(h : BBHeap b) → forget h ≡ forget' (relax h) 
lemma-forget-forget' leaf = refl
lemma-forget-forget' (left {l = l} {r = r} _ _) rewrite lemma-forget-forget' l | lemma-forget-forget' r = refl
lemma-forget-forget' (right {l = l} {r = r} _ _) rewrite lemma-forget-forget' l | lemma-forget-forget' r = refl

lemma-bbheap-heap : {b : Bound}(h : BBHeap b) → Heap (forget h)
lemma-bbheap-heap h rewrite lemma-forget-forget' h = lemma-bheap-heap (relax h)
