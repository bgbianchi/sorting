open import Relation.Binary.Core

module TreeSort.Correctness.Permutation  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import BBSTree _≤_ renaming (flatten to flatten')
open import Bound.Total A
open import Bound.Total.Order _≤_
open import BTree {A}
open import Data.List
open import Data.Sum
open import List.Permutation A
open import List.Permutation.Concatenation A
open import List.Permutation.Equivalence A
open import TreeSort _≤_ tot≤

-- Option 1

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

-- Option 2

lemma-insert'-/ : {a b : Bound}{x : A}(a≤x : LeB a (val x)) → (x≤b : LeB (val x) b) → (t : BBSTree a b) → (flatten' (insert' a≤x x≤b t)) / x ⟶ (flatten' t) 
lemma-insert'-/ a≤x x≤b (bslf _) = /head
lemma-insert'-/ {x = x} b≤x x≤t (bsnd {x = y} b≤y y≤t l r) 
    with tot≤ x y
... | inj₁ x≤y = lemma++/r (lemma-insert'-/ b≤x (lexy x≤y) l)
... | inj₂ y≤x = lemma++/l {xs = flatten' l} (/tail (lemma-insert'-/ (lexy y≤x) x≤t r))

theorem-treeSort∼' : (xs : List A) → xs ∼ (flatten' (treeSort' xs))
theorem-treeSort∼' [] = ∼[]
theorem-treeSort∼' (x ∷ xs) = ∼x /head (lemma-insert'-/ lebx lext (treeSort' xs)) (theorem-treeSort∼' xs)




