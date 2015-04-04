module List.Order  {A : Set} 
                     (_≤_ : A → A → Set)
                     (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z) where

open import Data.List
open import Sorting _≤_

data _*≤_ : List A → A → Set where
  lenx : {x : A} → [] *≤ x 
  lecx : {x y : A}{ys : List A} → y ≤ x → ys *≤ x → (y ∷ ys) *≤ x

data _≤*_ : A → List A → Set where
  genx : {x : A} → x ≤* [] 
  gecx : {x y : A}{ys : List A} → x ≤ y → x ≤* ys → x ≤* (y ∷ ys)

lemma-≤-*≤ : {x y : A}{xs : List A} → xs *≤ y → y ≤ x → xs *≤ x
lemma-≤-*≤ lenx y≤x  = lenx
lemma-≤-*≤ (lecx z≤y zs≤y) y≤x = lecx (trans≤ z≤y y≤x) (lemma-≤-*≤ zs≤y y≤x)

lemma-++-*≤ : {x y : A}{xs ys : List A} → y ≤ x → xs *≤ y → ys *≤ x → (xs ++ (y ∷ ys)) *≤ x 
lemma-++-*≤ y≤x lenx ys≤x = lecx y≤x ys≤x
lemma-++-*≤ y≤x (lecx z≤y zs≤y) ys≤x = lecx (trans≤ z≤y y≤x) (lemma-++-*≤ y≤x zs≤y ys≤x)

lemma-≤-≤* : {x y : A}{xs : List A} → x ≤ y → y ≤* xs → x ≤* xs
lemma-≤-≤* x≤y genx = genx
lemma-≤-≤* x≤y (gecx y≤z y≤zs) = gecx (trans≤ x≤y y≤z) (lemma-≤-≤* x≤y y≤zs)

lemma-≤*-++ : {x y : A}{xs ys : List A} → x ≤ y → x ≤* xs → y ≤* ys → x ≤* (xs ++ (y ∷ ys)) 
lemma-≤*-++ x≤y genx y≤ys = gecx x≤y (lemma-≤-≤* x≤y y≤ys)
lemma-≤*-++ x≤y (gecx x≤z x≤zs) y≤ys = gecx x≤z (lemma-≤*-++ x≤y x≤zs y≤ys)

lemma-sorted++ : {x : A}{xs ys : List A} → xs *≤ x → x ≤* ys → Sorted xs → Sorted ys → Sorted (xs ++ (x ∷ ys))
lemma-sorted++ {x = x} lenx genx _ _ = singls x
lemma-sorted++ lenx (gecx u≤y _) _ sys = conss u≤y sys
lemma-sorted++ (lecx x≤u xs≤*u) u*≤ys (singls x) sys = conss x≤u (lemma-sorted++ xs≤*u u*≤ys nils sys)
lemma-sorted++ (lecx x≤u xs≤*u) u*≤ys (conss x≤z sxs) sys = conss x≤z (lemma-sorted++ xs≤*u u*≤ys sxs sys)

