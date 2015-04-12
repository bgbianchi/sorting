module BTree.Complete.Alternative.Properties {A : Set} where

open import BTree {A}
open import BTree.Equality {A}
open import BTree.Equality.Properties {A}
open import BTree.Complete.Alternative {A} 
open import Data.Sum renaming (_⊎_ to _∨_)

lemma-⋗-≃ : {t t' t'' : BTree} → t ⋗ t' → t' ≃ t'' → t ⋗ t'' 
lemma-⋗-≃ (⋗lf x) ≃lf = ⋗lf x 
lemma-⋗-≃ (⋗nd x x' l≃r l'≃r' l⋗l') (≃nd .x' x'' _ l''≃r'' l'≃l'') = ⋗nd x x'' l≃r l'≃l'' (lemma-⋗-≃ l⋗l' l''≃r'')

lemma-≃-⋘ : {l r : BTree} → l ≃ r → l ⋘ r
lemma-≃-⋘ ≃lf = lf⋘
lemma-≃-⋘ (≃nd x x' l≃r l≃l' l'≃r') = ll⋘ x x' (lemma-≃-⋘ l≃r) l'≃r' (trans≃ (symm≃ l≃r) l≃l')

lemma-⋗-⋙ : {l r : BTree} → l ⋗ r → l ⋙ r
lemma-⋗-⋙ (⋗lf x) = ⋙lf x
lemma-⋗-⋙ (⋗nd x x' l≃r l'≃r' l⋗l') = ⋙rl x x' l≃r (lemma-≃-⋘ l'≃r') (lemma-⋗-≃ l⋗l' l'≃r')

