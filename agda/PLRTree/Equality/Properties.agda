module PLRTree.Equality.Properties {A : Set} where

open import PLRTree {A}
open import PLRTree.Equality {A}
open import Relation.Binary.Core

sym≃ : Symmetric _≃_
sym≃ ≃lf = ≃lf
sym≃ (≃nd x x' l≃r l'≃r' l≃l') = ≃nd x' x l'≃r' l≃r (sym≃ l≃l')

trans≃ : Transitive _≃_
trans≃ ≃lf t≃t'' = t≃t''
trans≃ (≃nd x x' l≃r l'≃r' l≃l') (≃nd .x' x'' _ l''≃r'' l'≃r'') = ≃nd x x'' l≃r l''≃r'' (trans≃ l≃l' l'≃r'')

lemma-≃-≃ : {t t' : PLRTree} → t ≃ t' → t ≃ t
lemma-≃-≃ ≃lf = ≃lf
lemma-≃-≃ (≃nd x x' l≃r l≃r' l≃l') = ≃nd x x l≃r l≃r (lemma-≃-≃ l≃l')

