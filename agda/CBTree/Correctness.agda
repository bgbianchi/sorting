module CBTree.Correctness {A : Set} where

open import BTree {A}
open import BTree.Equality {A}
open import BTree.Equality.Properties {A}
open import BTree.Complete {A} renaming (_⋘_ to _⋘'_ ; _⋙_ to _⋙'_ ; _⋗_ to _⋗'_)
open import BTree.Complete.Properties {A} 
open import CBTree {A}
open import Data.Sum renaming (_⊎_ to _∨_)

lemma-⋗-⋗' : {l r : BTree} → l ⋗ r → l ⋗' r
lemma-⋗-⋗' (⋗lf x) = ⋗lf x
lemma-⋗-⋗' (⋗nd {r = r} {l' = l'} x x' _ l'≃r' l⋗l') = ⋗nd x x' r l' (lemma-⋗-≃ (lemma-⋗-⋗' l⋗l') l'≃r')

lemma-⋙-⋗' : {l r : BTree} → l ⋙ r → l ⋗' r
lemma-⋙-⋗' (⋙lf x) = ⋗lf x
lemma-⋙-⋗' (⋙rl {r = r} {l' = l'} x x' l≃r l'⋘r' l⋗r') = ⋗nd x x' r l' (lemma-⋗-⋗' l⋗r')
lemma-⋙-⋗' (⋙rr {r = r} {l' = l'} x x' l≃r l'⋙r' l≃l') = ⋗nd x x' r l' (lemma-≃-⋗ l≃l' (lemma-⋙-⋗' l'⋙r'))

lemma-⋘-⋗' : {l r : BTree} → l ⋘ r → l ≃ r ∨ l ⋗' r
lemma-⋘-⋗' lf⋘ = inj₁ ≃lf
lemma-⋘-⋗' (ll⋘ {r = r} {l' = l'} x x' l⋘r l'≃r' r≃l')
    with lemma-⋘-⋗' l⋘r
... | inj₁ l≃r = inj₁ (≃nd x x' l≃r (trans≃ l≃r r≃l') l'≃r')
... | inj₂ l⋗'r = inj₂ (⋗nd x x' r l' (lemma-⋗-≃ l⋗'r (trans≃ r≃l' l'≃r')))
lemma-⋘-⋗' (lr⋘ {r = r} {l' = l'} x x' l⋙r l'≃r' l⋗l') = inj₂ (⋗nd x x' r l' (lemma-⋗-≃ (lemma-⋗-⋗' l⋗l') l'≃r'))

lemma-⋘-⋘' : {l r : BTree} → l ⋘ r → l ⋘' r
lemma-⋘-⋘' lf⋘ = eq⋘ ≃lf
lemma-⋘-⋘' (ll⋘ {r = r} {l' = l'} x x' l⋘r l'≃r' r≃l') 
    with lemma-⋘-⋗' l⋘r
... | inj₁ l≃r = eq⋘ (≃nd x x' l≃r (trans≃ l≃r r≃l') l'≃r')
... | inj₂ l⋗'r = gt⋘ (np⋗ x l⋗'r) (p≃ x' l'≃r') (⋗nd x x' r l' (lemma-⋗-≃ l⋗'r (trans≃ r≃l' l'≃r')))
lemma-⋘-⋘' (lr⋘ {r = r} {l' = l'} x x' l⋙r l'≃r' l⋗l') = gt⋘ (np⋗ x (lemma-⋙-⋗' l⋙r)) (p≃ x' l'≃r') (⋗nd x x' r l' (lemma-⋗-≃ (lemma-⋗-⋗' l⋗l') l'≃r'))

lemma-⋙-⋙' : {l r : BTree} → l ⋙ r → l ⋙' r
lemma-⋙-⋙' l⋙r = ⋙gt (lemma-⋙-⋗' l⋙r) 

lemma-cbtree-complete : {t : BTree} → CBTree t → Complete t
lemma-cbtree-complete leaf = leaf
lemma-cbtree-complete (left x cl cr l⋘r) = left x (lemma-cbtree-complete cl) (lemma-cbtree-complete cr) (lemma-⋘-⋘' l⋘r)
lemma-cbtree-complete (right x cl cr l⋙r) = right x (lemma-cbtree-complete cl) (lemma-cbtree-complete cr) (lemma-⋙-⋙' l⋙r)

