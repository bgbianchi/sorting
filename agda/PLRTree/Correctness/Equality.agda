module PLRTree.Correctness.Equality {A : Set} where

open import BTree.Equality {A}
open import PLRTree {A} 
open import PLRTree.Equality {A} renaming (_≃_ to _≃'_)

lemma-≃'-≃ : {l r : PLRTree} → l ≃' r → forget l ≃ forget r
lemma-≃'-≃ ≃lf = ≃lf
lemma-≃'-≃ (≃nd x x' l≃'r l≃'l' l'≃'r') = ≃nd x x' (lemma-≃'-≃ l≃'r) (lemma-≃'-≃ l≃'l') (lemma-≃'-≃ l'≃'r')
