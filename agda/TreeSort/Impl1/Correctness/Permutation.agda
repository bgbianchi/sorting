open import Relation.Binary.Core

module TreeSort.Impl1.Correctness.Permutation  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import BTree {A}
open import Data.List
open import Data.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Concatenation A
open import List.Permutation.Base.Equivalence A
open import TreeSort.Impl1 _≤_ tot≤

lemma-++∼ : {x : A}{xs ys : List A} → (x ∷ (xs ++ ys)) ∼ (xs ++ (x ∷ ys))
lemma-++∼ {xs = xs} = ∼x /head (lemma++/l {xs = xs} /head) refl∼

lemma-flatten∼ : (x : A) → (t : BTree) → (x ∷ flatten t) ∼ flatten (insert x t)
lemma-flatten∼ x leaf = ∼x /head /head ∼[]
lemma-flatten∼ x (node y l r) 
    with tot≤ x y
... | inj₁ x≤y = lemma++∼r (lemma-flatten∼ x l)
... | inj₂ y≤x = trans∼ (lemma-++∼ {xs = flatten l}) (lemma++∼l {xs = flatten l} (∼x (/tail /head) /head (lemma-flatten∼ x r)))

theorem-treeSort∼ : (xs : List A) → xs ∼ (flatten (treeSort xs))
theorem-treeSort∼ [] = ∼[]
theorem-treeSort∼ (x ∷ xs) = trans∼ (∼x /head /head (theorem-treeSort∼ xs)) (lemma-flatten∼ x (treeSort xs)) 




