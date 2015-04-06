module BBHeap.Complete.Alternative {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_ 
open import Bound.Lower A
open import BTree.Equality {A} renaming (_≃_ to _≃'_)
open import BTree.Complete.Alternative {A} renaming (_⋘_ to _⋘'_ ; _⋙_ to _⋙'_ ;  _⋗_ to _⋗'_)

lemma-forget≃ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ≃ r → forget l ≃' forget r
lemma-forget≃ ≃lf = ≃lf
lemma-forget≃ (≃nd {x = x} {x' = x'} _ _ _ _ l≃r l'≃r' l≃l') = ≃nd x x' (lemma-forget≃ l≃r) (lemma-forget≃ l≃l') (lemma-forget≃ l'≃r')

lemma-forget⋗ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋗ r → forget l ⋗' forget r 
lemma-forget⋗ (⋗lf {x = x} _) = ⋗lf x
lemma-forget⋗ (⋗nd {x = x} {x' = x'} _ _ _ _ l≃r l'≃r' l⋗l') = ⋗nd x x' (lemma-forget≃ l≃r) (lemma-forget≃ l'≃r') (lemma-forget⋗ l⋗l')

mutual 
  lemma-forget⋘ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋘ r → forget l ⋘' forget r
  lemma-forget⋘ lf⋘ = lf⋘
  lemma-forget⋘ (ll⋘ {x = x} {x' = x'} _ _ l⋘r l'⋘r' l'≃r' r≃l') = ll⋘ x x' (lemma-forget⋘ l⋘r) (lemma-forget≃ l'≃r') (lemma-forget≃ r≃l')
  lemma-forget⋘ (lr⋘ {x = x} {x' = x'} _ _ l⋙r l'⋘r' l'≃r' l⋗l') = lr⋘ x x' (lemma-forget⋙ l⋙r) (lemma-forget≃ l'≃r') (lemma-forget⋗ l⋗l')

  lemma-forget⋙ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋙ r → forget l ⋙' forget r
  lemma-forget⋙ (⋙lf {x = x} _) = ⋙lf x
  lemma-forget⋙ (⋙rl {x = x} {x' = x'} _ _ l⋘r l≃r l'⋘r' l⋗r') = ⋙rl x x' (lemma-forget≃ l≃r) (lemma-forget⋘ l'⋘r') (lemma-forget⋗ l⋗r')
  lemma-forget⋙ (⋙rr {x = x} {x' = x'} _ _ l⋘r l≃r l'⋙r' l≃l') = ⋙rr x x' (lemma-forget≃ l≃r) (lemma-forget⋙ l'⋙r') (lemma-forget≃ l≃l')

lemma-bbheap-complete : {b : Bound}(h : BBHeap b) → Complete (forget h)
lemma-bbheap-complete leaf = leaf
lemma-bbheap-complete (left {x = x} {l = l} {r = r} _ l⋘r) = left x (lemma-bbheap-complete l) (lemma-bbheap-complete r) (lemma-forget⋘ l⋘r)
lemma-bbheap-complete (right {x = x} {l = l} {r = r} _ l⋙r) = right x  (lemma-bbheap-complete l) (lemma-bbheap-complete r) (lemma-forget⋙ l⋙r)
