module PLRTree.Complete.Correctness.Alternative {A : Set} where

open import BTree.Complete.Alternative {A}
open import BTree.Complete.Alternative.Properties {A}
open import PLRTree {A} 
open import PLRTree.Complete {A} renaming (Complete to Complete' ; _⋗_ to _⋗'_ ; _⋘_ to _⋘'_ ; _⋙_ to _⋙'_)
open import PLRTree.Equality.Correctness {A}

lemma-⋗'-⋗ : {l r : PLRTree} → l ⋗' r → forget l ⋗ forget r
lemma-⋗'-⋗ (⋗lf x) = ⋗lf x
lemma-⋗'-⋗ (⋗nd x x' l≃'r l'≃'r' l⋗'l') = ⋗nd x x'  (lemma-≃'-≃ l≃'r) (lemma-≃'-≃ l'≃'r') (lemma-⋗'-⋗ l⋗'l')

mutual
  lemma-⋘'-⋘ : {l r : PLRTree} → l ⋘' r → forget l ⋘ forget r
  lemma-⋘'-⋘ (p⋘ l≃'r) = lemma-≃-⋘ (lemma-≃'-≃ l≃'r)
  lemma-⋘'-⋘ (l⋘ x x' l'⋘'r' l'≃'r' r≃'l') = ll⋘ x x' (lemma-⋘'-⋘ l'⋘'r') (lemma-≃'-≃ l'≃'r') (lemma-≃'-≃ r≃'l')
  lemma-⋘'-⋘ (r⋘ x x' l'⋙'r' l'≃'r' l⋗'l') = lr⋘ x x' (lemma-⋙'-⋙ l'⋙'r') (lemma-≃'-≃ l'≃'r') (lemma-⋗'-⋗ l⋗'l')

  lemma-⋙'-⋙ : {l r : PLRTree} → l ⋙' r → forget l ⋙ forget r
  lemma-⋙'-⋙ (⋙p l⋗'r) = lemma-⋗-⋙ (lemma-⋗'-⋗ l⋗'r)
  lemma-⋙'-⋙ (⋙l x x' l≃'r l'⋘'r' l⋗'r') = ⋙rl x x' (lemma-≃'-≃ l≃'r) (lemma-⋘'-⋘ l'⋘'r') (lemma-⋗'-⋗ l⋗'r')
  lemma-⋙'-⋙ (⋙r x x' l≃'r l'⋙'r' l≃'l') = ⋙rr x x' (lemma-≃'-≃ l≃'r) (lemma-⋙'-⋙ l'⋙'r') (lemma-≃'-≃ l≃'l')

lemma-complete'-complete : {t : PLRTree} → Complete' t → Complete (forget t)
lemma-complete'-complete leaf = leaf
lemma-complete'-complete (perfect x c'l c'r l≃'r) =  left x cl cr l⋘r
                   where cl = lemma-complete'-complete c'l ;
                              cr = lemma-complete'-complete c'r ;
                              l⋘r = lemma-⋘'-⋘ (p⋘ l≃'r)
lemma-complete'-complete (left x c'l c'r l⋘'r) = left x cl cr l⋘r
                   where cl = lemma-complete'-complete c'l ;
                              cr = lemma-complete'-complete c'r ;
                              l⋘r = lemma-⋘'-⋘ l⋘'r
lemma-complete'-complete (right x c'l c'r l⋙'r) = right x cl cr l⋙r
                   where cl = lemma-complete'-complete c'l ;
                              cr = lemma-complete'-complete c'r ;
                              l⋙r = lemma-⋙'-⋙ l⋙'r
                         
