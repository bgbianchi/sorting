open import Relation.Binary.Core

module BBSTree.Properties  {A : Set} 
                     (_≤_ : A → A → Set)
                     (trans≤ : Transitive _≤_) where

open import BBSTree _≤_
open import Bound.Total A
open import Bound.Total.Order.Properties _≤_ trans≤
open import List.Order.Simple _≤_
open import List.Order.Simple.Properties _≤_ trans≤
open import List.Sorted _≤_

lemma-bbst-*≤ : {b : Bound}(x : A) → (t : BBSTree b (val x)) → flatten t *≤ x
lemma-bbst-*≤ x (bslf _) = lenx
lemma-bbst-*≤ x (bsnd {x = y} b≤y y≤x l r) = lemma-++-*≤ (lemma-LeB≤ y≤x) (lemma-bbst-*≤ y l) (lemma-bbst-*≤ x r)

lemma-bbst-≤* : {b : Bound}(x : A) → (t : BBSTree (val x) b) → x ≤* flatten t
lemma-bbst-≤* x (bslf _) = genx
lemma-bbst-≤* x (bsnd {x = y} x≤y y≤t l r) = lemma-≤*-++ (lemma-LeB≤ x≤y) (lemma-bbst-≤* x l) (lemma-bbst-≤* y r)

lemma-bbst-sorted : {b t : Bound}(t : BBSTree b t) → Sorted (flatten t)
lemma-bbst-sorted (bslf _) = nils
lemma-bbst-sorted (bsnd {x = x} b≤x x≤t l r) = lemma-sorted++ (lemma-bbst-*≤ x l) (lemma-bbst-≤* x r) (lemma-bbst-sorted l) (lemma-bbst-sorted r)
