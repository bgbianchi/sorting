module BBHeap.Complete {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_ 
open import BTree.Complete {A}
open import Bound.Lower A

lemma-bbheap-complete : {b : Bound}(h : BBHeap b) → Complete (forget h)
lemma-bbheap-complete = {!!}
