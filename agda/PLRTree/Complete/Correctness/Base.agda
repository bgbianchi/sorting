module PLRTree.Complete.Correctness.Base {A : Set} where

open import BTree.Complete.Base {A}
open import BTree.Complete.Alternative.Correctness {A} renaming (lemma-complete'-complete to lemma-complete''-complete)
open import Function using (_∘_)
open import PLRTree {A} 
open import PLRTree.Complete {A} renaming (Complete to Complete' ; _⋗_ to _⋗'_ ; _⋘_ to _⋘'_ ; _⋙_ to _⋙'_)
open import PLRTree.Complete.Correctness.Alternative {A} renaming (lemma-complete'-complete to lemma-complete'-complete'')
open import PLRTree.Equality.Correctness {A}

lemma-complete'-complete : {t : PLRTree} → Complete' t → Complete (forget t)
lemma-complete'-complete = lemma-complete''-complete ∘ lemma-complete'-complete''
                         
