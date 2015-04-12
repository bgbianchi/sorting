module PLRTree.Heap.Correctness {A : Set}(_≤_ : A → A → Set) where

open import BTree.Heap _≤_
open import PLRTree {A}
open import PLRTree.Heap _≤_ renaming (Heap to Heap')

lemma-heap'-heap : {t : PLRTree} → Heap' t → Heap (forget t)
lemma-heap'-heap leaf = leaf
lemma-heap'-heap (node {t} {x} (lf≤* .x) (lf≤* .x) _ _) = single x
lemma-heap'-heap (node {t} {x} (lf≤* .x) (nd≤* x≤y  _ _) _ h'r) = right x≤y (lemma-heap'-heap h'r)
lemma-heap'-heap (node {t} {x} (nd≤* x≤y _ _) (lf≤* .x) h'l _) = left x≤y (lemma-heap'-heap h'l)
lemma-heap'-heap (node (nd≤* x≤y _ _) (nd≤* x≤y' _ _) h'l h'r) = both x≤y x≤y' (lemma-heap'-heap h'l) (lemma-heap'-heap h'r) 
