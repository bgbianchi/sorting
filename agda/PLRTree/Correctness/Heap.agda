module PLRTree.Correctness.Heap {A : Set}(_≤_ : A → A → Set) where

open import BTree.Heap _≤_
open import PLRTree {A}
open import PLRTree.Heap _≤_ renaming (Heap to Heap')

lemma-heap'-heap : {t : PLRTree} → Heap' t → Heap (forget t)
lemma-heap'-heap leaf = leaf
lemma-heap'-heap (single x) = single x
lemma-heap'-heap (left x≤y l) = left x≤y (lemma-heap'-heap l) 
lemma-heap'-heap (right x≤y r) =  right x≤y (lemma-heap'-heap r)
lemma-heap'-heap (both x≤y x≤y' l r) = both x≤y x≤y' (lemma-heap'-heap l) (lemma-heap'-heap r)
