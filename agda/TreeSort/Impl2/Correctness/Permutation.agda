open import Relation.Binary.Core

module TreeSort.Impl2.Correctness.Permutation  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import BBSTree _≤_ 
open import Bound.Total A
open import Bound.Total.Order _≤_
open import Data.List
open import Data.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Concatenation A
open import TreeSort.Impl2 _≤_ tot≤

lemma-insert-/ : {a b : Bound}{x : A}(a≤x : LeB a (val x))(x≤b : LeB (val x) b)(t : BBSTree a b) → (flatten (insert a≤x x≤b t)) / x ⟶ (flatten t) 
lemma-insert-/ a≤x x≤b (bslf _) = /head
lemma-insert-/ {x = x} b≤x x≤t (bsnd {x = y} b≤y y≤t l r) 
    with tot≤ x y
... | inj₁ x≤y = lemma++/r (lemma-insert-/ b≤x (lexy x≤y) l)
... | inj₂ y≤x = lemma++/l {xs = flatten l} (/tail (lemma-insert-/ (lexy y≤x) x≤t r))

theorem-treeSort∼ : (xs : List A) → xs ∼ (flatten (treeSort xs))
theorem-treeSort∼ [] = ∼[]
theorem-treeSort∼ (x ∷ xs) = ∼x /head (lemma-insert-/ lebx lext (treeSort xs)) (theorem-treeSort∼ xs)




