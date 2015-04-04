module BBSTree  {A : Set} 
                     (_≤_ : A → A → Set)
                     (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z) where

open import Bound2 _≤_ trans≤
open import Data.List
open import List.Order _≤_ trans≤
open import Sorting _≤_

data BBSTree : Bound → Bound → Set where
  bslf : {b t : Bound} 
                   → LeB b t 
                   → BBSTree b t
  bsnd : {x : A}{b t : Bound} 
                   → LeB b (val x) 
                   → LeB (val x) t 
                   → BBSTree b (val x) 
                   → BBSTree (val x) t 
                   → BBSTree b t

flatten : {b t : Bound} → BBSTree b t → List A
flatten (bslf _) = [] 
flatten (bsnd {x = x} b≤x x≤t l r) = flatten l ++ (x ∷ flatten r)

lemma-bbst-*≤ : {b : Bound}(x : A) → (t : BBSTree b (val x)) → flatten t *≤ x
lemma-bbst-*≤ x (bslf _) = lenx
lemma-bbst-*≤ x (bsnd {x = y} b≤y y≤x l r) = lemma-++-*≤ (lemma-LeB≤ y≤x) (lemma-bbst-*≤ y l) (lemma-bbst-*≤ x r)

lemma-bbst-≤* : {b : Bound}(x : A) → (t : BBSTree (val x) b) → x ≤* flatten t
lemma-bbst-≤* x (bslf _) = genx
lemma-bbst-≤* x (bsnd {x = y} x≤y y≤t l r) = lemma-≤*-++ (lemma-LeB≤ x≤y) (lemma-bbst-≤* x l) (lemma-bbst-≤* y r)

lemma-bbst-sorted : {b t : Bound}(t : BBSTree b t) → Sorted (flatten t)
lemma-bbst-sorted (bslf _) = nils
lemma-bbst-sorted (bsnd {x = x} b≤x x≤t l r) = lemma-sorted++ (lemma-bbst-*≤ x l) (lemma-bbst-≤* x r) (lemma-bbst-sorted l) (lemma-bbst-sorted r)
