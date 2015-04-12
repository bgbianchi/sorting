module PLRTree.Complete.Properties {A : Set} where

open import Data.Empty
open import Data.Sum
open import PLRTree {A} 
open import PLRTree.Complete {A}
open import PLRTree.Equality {A}

lemma-⋗-≃ : {t t' t'' : PLRTree} → t ⋗ t' → t' ≃ t'' → t ⋗ t'' 
lemma-⋗-≃ (⋗lf x) ≃lf = ⋗lf x
lemma-⋗-≃ (⋗nd x x' l≃r l'≃r' l⋗l') (≃nd .x' x'' _ l''≃r'' l'≃l'') = ⋗nd x x'' l≃r l''≃r'' (lemma-⋗-≃ l⋗l' l'≃l'')

lemma-≃-⋗ : {t t' t'' : PLRTree} → t ≃ t' → t ⋗ t'' → t' ⋗ t'' 
lemma-≃-⋗ ≃lf t⋗t'' = t⋗t''
lemma-≃-⋗ (≃nd x x' ≃lf ≃lf ≃lf) (⋗lf .x) = ⋗lf x'
lemma-≃-⋗ (≃nd x _ ≃lf (≃nd _ _ _ _ _) ()) (⋗lf .x) 
lemma-≃-⋗ (≃nd x x' l≃r l'≃r' l≃l') (⋗nd .x x'' _ l''≃r'' l⋗l'') = ⋗nd x' x'' l'≃r' l''≃r'' (lemma-≃-⋗ l≃l' l⋗l'') 

lemma-⋗* : {t t' t'' : PLRTree} → t ⋗ t' → t ⋗ t'' → t' ≃ t'' 
lemma-⋗* (⋗lf x) (⋗lf .x) = ≃lf
lemma-⋗* (⋗lf x) (⋗nd .x _ _ _ ()) 
lemma-⋗* (⋗nd x  _ _ _ ()) (⋗lf .x)
lemma-⋗* (⋗nd x x' l≃r l'≃r' l⋗l') (⋗nd .x x'' _ l''≃r'' l'⋗l'') = ≃nd x' x'' l'≃r' l''≃r'' (lemma-⋗* l⋗l' l'⋗l'')

lemma-*⋗ : {t t' t'' : PLRTree} → t ⋗ t' → t'' ⋗ t' → t ≃ t'' 
lemma-*⋗ (⋗lf x) (⋗lf y) = ≃nd x y ≃lf ≃lf ≃lf
lemma-*⋗ (⋗nd x x' l≃r l'≃r' l⋗l') (⋗nd x'' .x' l''≃r'' _ l''⋗l') = ≃nd x x'' l≃r l''≃r'' (lemma-*⋗ l⋗l' l''⋗l')

lemma-⋗refl-⊥ : {t : PLRTree} → t ⋗ t → ⊥
lemma-⋗refl-⊥ (⋗nd x .x _ _ t⋗t) 
    with lemma-⋗refl-⊥ t⋗t
... | ()

lemma-⋙-⋗ : {t t' t'' : PLRTree} → t ⋙ t' → t ⋗ t'' → t' ⋘ t'' 
lemma-⋙-⋗ (⋙p (⋗lf x)) (⋗lf .x) = p⋘ ≃lf
lemma-⋙-⋗ (⋙p (⋗nd x _ _ _ ())) (⋗lf .x)
lemma-⋙-⋗ (⋙p (⋗lf x)) (⋗nd .x _ _ _ ())
lemma-⋙-⋗ (⋙p (⋗nd x x' l≃r l'≃r' l⋗l')) (⋗nd .x x'' _ l''≃r'' l⋗l'') = p⋘ (≃nd x' x'' l'≃r' l''≃r'' (lemma-⋗* l⋗l' l⋗l''))
lemma-⋙-⋗ (⋙l x _ _ _ ()) (⋗lf .x)
lemma-⋙-⋗ (⋙l x x' l≃r l'⋘r' l⋗r') (⋗nd .x x'' _ l''≃r'' l⋗l'') = l⋘ x' x'' l'⋘r' l''≃r'' (lemma-⋗* l⋗r' l⋗l'')
lemma-⋙-⋗ (⋙r x x' ≃lf (⋙p ()) ≃lf) (⋗lf .x) 
lemma-⋙-⋗ (⋙r x x' ≃lf (⋙l _ _ _ _ _) ()) (⋗lf .x) 
lemma-⋙-⋗ (⋙r x x' ≃lf (⋙r _ _ _ _ _) ()) (⋗lf .x) 
lemma-⋙-⋗ (⋙r x x' l≃r l'⋙r' l≃l') (⋗nd .x x'' _ l''≃r'' l⋗l'') = r⋘ x' x'' l'⋙r' l''≃r'' (lemma-≃-⋗ l≃l' l⋗l'')
