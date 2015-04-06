module BBHeap.Complete.Base {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_ 
open import BBHeap.Complete.Alternative _≤_ renaming (lemma-bbheap-complete to lemma-bbheap-complete')
open import BTree.Complete.Alternative.Correctness {A} 
open import BTree.Complete.Base {A}
open import Bound.Lower A
open import Function using (_∘_)

lemma-bbheap-complete : {b : Bound}(h : BBHeap b) → Complete (forget h)
lemma-bbheap-complete = lemma-complete'-complete ∘ lemma-bbheap-complete' 
