open import Relation.Binary.Core

module BSTree.Properties  {A : Set} 
               (_≤_ : A → A → Set) 
               (trans≤ : Transitive _≤_) where

open import BTree {A}
open import BSTree _≤_
open import List.Order.Simple _≤_
open import List.Order.Simple.Properties _≤_ trans≤
open import List.Sorted _≤_

lemma-*⊴-*≤ : {x : A}{t : BTree} → BSTree t → t *⊴ x → flatten t *≤ x
lemma-*⊴-*≤ slf lelf = lenx
lemma-*⊴-*≤ (snd sl sr l≤y y≤r) (lend y≤x r≤x) = lemma-++-*≤ y≤x (lemma-*⊴-*≤ sl l≤y) (lemma-*⊴-*≤ sr r≤x)

lemma-⊴*-≤* : {x : A}{t : BTree} → BSTree t → x ⊴* t → x ≤* flatten t
lemma-⊴*-≤* slf gelf = genx
lemma-⊴*-≤* (snd sl sr l≤y y≤r) (gend x≤y x≤l) = lemma-≤*-++ x≤y (lemma-⊴*-≤* sl x≤l) (lemma-⊴*-≤* sr y≤r)

lemma-bst-sorted : {t : BTree} → BSTree t → Sorted (flatten t)
lemma-bst-sorted slf = nils
lemma-bst-sorted (snd sl sr l≤x x≤r) = lemma-sorted++ (lemma-*⊴-*≤ sl l≤x) (lemma-⊴*-≤* sr x≤r) (lemma-bst-sorted sl) (lemma-bst-sorted sr)



