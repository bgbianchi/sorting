module PLRTree.Correctness.Complete {A : Set} where

open import BTree.Complete.Base {A}
open import PLRTree {A} 
open import PLRTree.Complete {A} renaming (Complete to Complete' ; Perfect to Perfect' ; NearlyPerfect to NearlyPerfect' ; _⋗_ to _⋗'_ ; _⋘_ to _⋘'_ ; _⋙_ to _⋙'_)
open import PLRTree.Correctness.Equality {A}

lemma-perfect'-perfect : {t : PLRTree} → Perfect' t → Perfect (forget t)
lemma-perfect'-perfect plf = plf
lemma-perfect'-perfect (p≃ x l≃'r) = p≃ x (lemma-≃'-≃ l≃'r)

lemma-⋗'-⋗ : {l r : PLRTree} → l ⋗' r → forget l ⋗ forget r
lemma-⋗'-⋗ (⋗lf x) = ⋗lf x
lemma-⋗'-⋗ (⋗nd x x' r l' l⋗'r) = ⋗nd x x' (forget r) (forget l') (lemma-⋗'-⋗ l⋗'r)

lemma-nearlyPerfect'-nearlyPerfect : {t : PLRTree} → NearlyPerfect' t → NearlyPerfect (forget t)
lemma-nearlyPerfect'-nearlyPerfect (npr x l np'r) = npr x (forget l) (lemma-nearlyPerfect'-nearlyPerfect np'r)
lemma-nearlyPerfect'-nearlyPerfect (np⋗ x l⋗'r) = np⋗ x (lemma-⋗'-⋗ l⋗'r)

lemma-⋘'-⋘ : {l r : PLRTree} → l ⋘' r → forget l ⋘ forget r
lemma-⋘'-⋘ (eq⋘ l≃'r) = eq⋘ (lemma-≃'-≃ l≃'r)
lemma-⋘'-⋘ (gt⋘ npl pr l⋗'r) = gt⋘ (lemma-nearlyPerfect'-nearlyPerfect npl) (lemma-perfect'-perfect pr) (lemma-⋗'-⋗ l⋗'r)

lemma-⋙'-⋙ : {l r : PLRTree} → l ⋙' r → forget l ⋙ forget r
lemma-⋙'-⋙ (⋙gt l⋗'r) = ⋙gt (lemma-⋗'-⋗ l⋗'r)

lemma-complete'-complete : {t : PLRTree} → Complete' t → Complete (forget t)
lemma-complete'-complete leaf = leaf
lemma-complete'-complete (left x c'l c'r l⋘'r) = left x (lemma-complete'-complete c'l) (lemma-complete'-complete c'r) (lemma-⋘'-⋘ l⋘'r)
lemma-complete'-complete (right x c'l c'r l⋙'r) = right x (lemma-complete'-complete c'l) (lemma-complete'-complete c'r) (lemma-⋙'-⋙ l⋙'r)
