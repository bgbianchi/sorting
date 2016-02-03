open import Relation.Binary.Core

module Mergesort.Impl2.Correctness.Permutation {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.List
open import Data.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Concatenation A
open import List.Permutation.Base.Equivalence A
open import List.Properties A
open import LRTree {A}
open import Mergesort.Impl2 _≤_ tot≤
open import OList _≤_  

lemma-merge'-empty : {b : Bound}(xs : OList b) → merge' xs (onil {b}) ≡ xs
lemma-merge'-empty onil = refl
lemma-merge'-empty (:< b≤x xs) = refl

mutual
  lemma-merge' : {b : Bound}(xs ys : OList b) → (forget xs ++ forget ys) ∼ forget (merge' xs ys)
  lemma-merge' onil ys = refl∼
  lemma-merge' xs onil rewrite ++id (forget xs) | lemma-merge'-empty xs = refl∼
  lemma-merge' (:< {x = x} b≤x xs) (:< {x = y} b≤y ys) 
      with tot≤ x y
  ... | inj₁ x≤y  = ∼x /head /head (lemma-merge' xs (:< (lexy x≤y) ys))
  ... | inj₂ y≤x = 
                  let f'xxsyf'ys∼yf'xxsf'ys = ∼x (lemma++/ {y} {forget (:< b≤x xs)}) /head refl∼ ;
                       yf'xxsf'ys∼yf'm'xxsys = ∼x /head /head (lemma-merge'xs (lexy y≤x) xs ys)
                  in trans∼ f'xxsyf'ys∼yf'xxsf'ys yf'xxsf'ys∼yf'm'xxsys

  lemma-merge'xs : {b : Bound}{x : A} → (b≤x : LeB b (val x))(xs : OList (val x))(ys : OList b) → (forget (:< b≤x xs) ++ forget ys) ∼ forget (merge'xs b≤x xs ys)
  lemma-merge'xs b≤x xs onil rewrite ++id (forget xs) | lemma-merge'-empty xs = refl∼
  lemma-merge'xs {x = x} b≤x xs (:< {x = y} b≤y ys) 
      with tot≤ x y
  ... | inj₁ x≤y = ∼x /head /head (lemma-merge' xs (:< (lexy x≤y) ys))
  ... | inj₂ y≤x = 
                  let f'xxsyf'ys∼yf'xxsf'ys = ∼x (lemma++/ {y} {forget (:< b≤x xs)}) /head refl∼ ;
                       yf'xxsf'ys∼yf'm'xxsys = ∼x /head /head (lemma-merge'xs (lexy y≤x) xs ys)
                  in trans∼ f'xxsyf'ys∼yf'xxsf'ys yf'xxsf'ys∼yf'm'xxsys

lemma-insert : (x : A)(t : LRTree) → (x ∷ flatten t) ∼ flatten (insert x t)
lemma-insert x empty = ∼x /head /head ∼[]
lemma-insert x (leaf y) = ∼x (/tail /head) /head (∼x /head /head ∼[])
lemma-insert x (node left l r) = lemma++∼r (lemma-insert x l)
lemma-insert x (node right l r) = 
                let xlr∼lxr = ∼x /head (lemma++/ {x} {flatten l}) refl∼ ;
                     lxr∼lrᵢ = lemma++∼l {flatten l} (lemma-insert x r)
                in trans∼ xlr∼lxr lxr∼lrᵢ

lemma-deal : (xs : List A) → xs ∼ flatten (deal xs)
lemma-deal [] = ∼[]
lemma-deal (x ∷ xs) = trans∼ (∼x /head /head (lemma-deal xs)) (lemma-insert x (deal xs))

lemma-merge : (t : LRTree) → flatten t ∼ forget (merge t)
lemma-merge empty = ∼[]
lemma-merge (leaf x) = ∼x /head /head ∼[]
lemma-merge (node t l r) = 
                let flfr∼f'm'lf'm'r = lemma++∼ (lemma-merge l) (lemma-merge r) ;
                     f'm'lf'm'r∼m''m''lm''r = lemma-merge' (merge l) (merge r)
                in trans∼ flfr∼f'm'lf'm'r f'm'lf'm'r∼m''m''lm''r

theorem-mergesort-∼ : (xs : List A) → xs ∼ (forget (mergesort xs))
theorem-mergesort-∼ xs = trans∼ (lemma-deal xs) (lemma-merge (deal xs))
