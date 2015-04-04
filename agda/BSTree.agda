module BSTree  {A : Set} 
               (_≤_ : A → A → Set) 
               (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z) where

open import BTree {A}
open import List.Order _≤_ trans≤
open import Sorting _≤_

data _⊴*_ : A → BTree → Set where
  gelf : {x : A} 
                   → x ⊴* leaf
  gend : {x y : A}{l r : BTree} 
                   → x ≤ y 
                   → x ⊴* l 
                   → x ⊴* (node y l r)

data _*⊴_ : BTree → A → Set where
  lelf : {x : A} 
                   → leaf *⊴ x
  lend : {x y : A}{l r : BTree} 
                   → y ≤ x 
                   → r *⊴ x 
                   → (node y l r) *⊴ x

data BSTree : BTree → Set where
  slf : BSTree leaf
  snd : {x : A}{l r : BTree} 
                   → BSTree l 
                   → BSTree r 
                   → l *⊴ x 
                   → x ⊴* r 
                   → BSTree (node x l r) 

lemma-*⊴-*≤ : {x : A}{t : BTree} → BSTree t → t *⊴ x → flatten t *≤ x
lemma-*⊴-*≤ slf lelf = lenx
lemma-*⊴-*≤ (snd sl sr l≤y y≤r) (lend y≤x r≤x) = lemma-++-*≤ y≤x (lemma-*⊴-*≤ sl l≤y) (lemma-*⊴-*≤ sr r≤x)

lemma-⊴*-≤* : {x : A}{t : BTree} → BSTree t → x ⊴* t → x ≤* flatten t
lemma-⊴*-≤* slf gelf = genx
lemma-⊴*-≤* (snd sl sr l≤y y≤r) (gend x≤y x≤l) = lemma-≤*-++ x≤y (lemma-⊴*-≤* sl x≤l) (lemma-⊴*-≤* sr y≤r)

lemma-bst-sorted : {t : BTree} → BSTree t → Sorted (flatten t)
lemma-bst-sorted slf = nils
lemma-bst-sorted (snd sl sr l≤x x≤r) = lemma-sorted++ (lemma-*⊴-*≤ sl l≤x) (lemma-⊴*-≤* sr x≤r) (lemma-bst-sorted sl) (lemma-bst-sorted sr)



