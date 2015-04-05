open import Relation.Binary.Core

module TreeSort.Correctness.Order  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_)  where

open import BBSTree _≤_ renaming (flatten to flatten')
open import BBSTree.Properties _≤_ trans≤
open import Bound.Lower A 
open import Bound.Lower.Order _≤_
open import BSTree _≤_
open import BSTree.Properties _≤_ trans≤
open import BTree {A}
open import Data.List
open import Data.Sum
open import Function using (_∘_)
open import List.Sorted _≤_
open import TreeSort _≤_ tot≤

lemma-insert-*⊴ : {x y : A}{t : BTree} → x ≤ y → t *⊴ y → insert x t *⊴ y
lemma-insert-*⊴ x≤y lelf = lend x≤y lelf
lemma-insert-*⊴ {x = x}{t = node z l r} x≤y (lend z≤y r≤y) 
    with tot≤ x z
... | inj₁ x≤z = lend z≤y r≤y
... | inj₂ z≤x = lend z≤y (lemma-insert-*⊴ x≤y r≤y) 

lemma-insert-⊴* : {x y : A}{t : BTree} → y ≤ x → y ⊴* t → y ⊴* insert x t
lemma-insert-⊴* y≤x gelf = gend y≤x gelf
lemma-insert-⊴* {x = x} {t = node z l r} y≤x (gend y≤z y≤l) 
    with tot≤ x z
... | inj₁ x≤z = gend y≤z (lemma-insert-⊴* y≤x y≤l)
... | inj₂ z≤x = gend y≤z y≤l

lemma-insert-bst : {t : BTree}(x : A) → BSTree t → BSTree (insert x t)
lemma-insert-bst x slf = snd slf slf lelf gelf
lemma-insert-bst x (snd {x = y} sl sr l≤y y≤r) 
    with tot≤ x y
... | inj₁ x≤y = snd (lemma-insert-bst x sl) sr (lemma-insert-*⊴ x≤y l≤y) y≤r
... | inj₂ y≤x = snd sl (lemma-insert-bst x sr) l≤y (lemma-insert-⊴* y≤x y≤r)

lemma-treeSort-bst : (xs : List A) → BSTree (treeSort xs)
lemma-treeSort-bst [] = slf
lemma-treeSort-bst (x ∷ xs) = lemma-insert-bst x (lemma-treeSort-bst xs)

theorem-treeSort-sorted : (xs : List A) → Sorted (flatten (treeSort xs))
theorem-treeSort-sorted = lemma-bst-sorted ∘ lemma-treeSort-bst 

-- Option 2

theorem-treeSort-sorted' : (xs : List A) → Sorted (flatten' (treeSort' xs))
theorem-treeSort-sorted' = lemma-bbst-sorted ∘ treeSort'




