module BTree.Complete.Properties {A : Set} where

open import BTree {A} 
open import BTree.Complete {A} 
open import BTree.Equality {A}
open import BTree.Equality.Properties {A}

lemma-≃-⋗ : {l l' r' : BTree} → l ≃ l' → l' ⋗ r' → l ⋗ r'
lemma-≃-⋗ (≃nd x x' ≃lf ≃lf ≃lf) (⋗lf .x') = ⋗lf x
lemma-≃-⋗ (≃nd {r = r} x x' l≃r l≃l' l'≃r') (⋗nd .x' x'' r' l'' l'⋗r'') = ⋗nd x x'' r l'' (lemma-≃-⋗ l≃l' l'⋗r'')

lemma-⋗-≃ : {l r r' : BTree} → l ⋗ r → r ≃ r' → l ⋗ r'
lemma-⋗-≃ (⋗lf x) ≃lf = ⋗lf x
lemma-⋗-≃ (⋗nd {r' = r'} x x' r l' l⋗r') (≃nd {l' = l''} .x' x'' l'≃r' l'≃l'' l''≃r'') = ⋗nd x x'' r l'' (lemma-⋗-≃ l⋗r' (trans≃ (symm≃ l'≃r') (trans≃ l'≃l'' l''≃r'')))
