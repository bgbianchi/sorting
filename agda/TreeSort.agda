open import Data.Sum renaming (_⊎_ to _∨_)

module TreeSort  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : (x y : A) → x ≤ y ∨ y ≤ x) 
                  (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)  where

open import BBSTree _≤_ trans≤ renaming (flatten to flatten')
open import Bound2 _≤_
open import BTree {A}
open import BSTree _≤_ trans≤
open import Data.List
open import Permutation A
open import Permutation.Concatenation A
open import Permutation.Equivalence A
open import Sorting _≤_

insert : A → BTree → BTree
insert x leaf = node x leaf leaf
insert x (node y l r) 
    with tot≤ x y
... | inj₁ x≤y = node y (insert x l) r
... | inj₂ y≤x = node y l (insert x r)

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

treeSort : List A → BTree
treeSort [] = leaf
treeSort (x ∷ xs) = insert x (treeSort xs)

lemma-treeSort-bst : (xs : List A) → BSTree (treeSort xs)
lemma-treeSort-bst [] = slf
lemma-treeSort-bst (x ∷ xs) = lemma-insert-bst x (lemma-treeSort-bst xs)

theorem-treeSort-sorted : (xs : List A) → Sorted (flatten (treeSort xs))
theorem-treeSort-sorted xs = lemma-bst-sorted (lemma-treeSort-bst xs)

lemma-++∼ : {x : A}{xs ys : List A} → (x ∷ (xs ++ ys)) ∼ (xs ++ (x ∷ ys))
lemma-++∼ {xs = xs} = ∼x /head (lemma++/l {xs = xs} /head) lemma-refl∼

lemma-flatten∼ : (x : A) → (t : BTree) → (x ∷ flatten t) ∼ flatten (insert x t)
lemma-flatten∼ x leaf = ∼x /head /head ∼[]
lemma-flatten∼ x (node y l r) 
    with tot≤ x y
... | inj₁ x≤y = lemma++∼r (lemma-flatten∼ x l)
... | inj₂ y≤x = lemma-trans∼ (lemma-++∼ {xs = flatten l}) (lemma++∼l {xs = flatten l} (∼x (/tail /head) /head (lemma-flatten∼ x r)))

theorem-treeSort∼ : (xs : List A) → xs ∼ (flatten (treeSort xs))
theorem-treeSort∼ [] = ∼[]
theorem-treeSort∼ (x ∷ xs) = lemma-trans∼ (∼x /head /head (theorem-treeSort∼ xs)) (lemma-flatten∼ x (treeSort xs)) 

--

insert' : {x : A}{b t : Bound} → LeB b (val x) → LeB (val x) t → BBSTree b t → BBSTree b t
insert' b≤x x≤t (bslf _)= bsnd b≤x x≤t (bslf b≤x) (bslf x≤t)
insert' {x = x} b≤x x≤t (bsnd {x = y} b≤y y≤t l r) 
    with tot≤ x y
... | inj₁ x≤y = bsnd b≤y y≤t (insert' b≤x (lexy x≤y) l) r
... | inj₂ y≤x = bsnd b≤y y≤t l (insert' (lexy y≤x) x≤t r)

treeSort' : List A → BBSTree bot top
treeSort' [] = bslf lebx
treeSort' (x ∷ xs) = insert' {x = x} lebx lext (treeSort' xs)

theorem-treeSort-sorted' : (xs : List A) → Sorted (flatten' (treeSort' xs))
theorem-treeSort-sorted' xs = lemma-bbst-sorted (treeSort' xs)

lemma-insert'-/ : {a b : Bound}{x : A}(a≤x : LeB a (val x)) → (x≤b : LeB (val x) b) → (t : BBSTree a b) → (flatten' (insert' a≤x x≤b t)) / x ⟶ (flatten' t) 
lemma-insert'-/ a≤x x≤b (bslf _) = /head
lemma-insert'-/ {x = x} b≤x x≤t (bsnd {x = y} b≤y y≤t l r) 
    with tot≤ x y
... | inj₁ x≤y = lemma++/r (lemma-insert'-/ b≤x (lexy x≤y) l)
... | inj₂ y≤x = lemma++/l {xs = flatten' l} (/tail (lemma-insert'-/ (lexy y≤x) x≤t r))

theorem-treeSort∼' : (xs : List A) → xs ∼ (flatten' (treeSort' xs))
theorem-treeSort∼' [] = ∼[]
theorem-treeSort∼' (x ∷ xs) = ∼x /head (lemma-insert'-/ lebx lext (treeSort' xs)) (theorem-treeSort∼' xs)




