module List.Order.Bounded.Properties {A : Set} 
                   (_≤_ : A → A → Set) 
                   (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)  where

open import Bound.Total A
open import Bound.Total.Order _≤_
open import Bound.Total.Order.Properties _≤_ trans≤
open import Data.List
open import List.Order.Bounded _≤_
open import List.Sorted _≤_

lemma-sorted++ : {x : A}{xs ys : List A} → xs ≤* (val x) → (val x) *≤ ys → Sorted xs → Sorted ys → Sorted (xs ++ (x ∷ ys))
lemma-sorted++ {x = x} lenx genx _ _ = singls x
lemma-sorted++ lenx (gecx u≤y _) _ sys = conss (lemma-LeB≤ u≤y) sys
lemma-sorted++ (lecx x≤u xs≤*u) u*≤ys (singls x) sys = conss (lemma-LeB≤ x≤u) (lemma-sorted++ xs≤*u u*≤ys nils sys)
lemma-sorted++ (lecx x≤u xs≤*u) u*≤ys (conss x≤z sxs) sys = conss x≤z (lemma-sorted++ xs≤*u u*≤ys sxs sys)

lemma-++≤* : {t : Bound}{x : A}{xs ys : List A} → LeB (val x) t → xs ≤* (val x) → ys ≤* t → (xs ++ (x ∷ ys)) ≤* t
lemma-++≤* u≤t lenx ys≤*t = lecx u≤t ys≤*t
lemma-++≤* u≤t (lecx x≤u xs≤*u) ys≤*u = lecx (transLeB x≤u u≤t) (lemma-++≤* u≤t xs≤*u ys≤*u)

lemma-*≤ : {b : Bound}{x : A}{xs : List A} → LeB b (val x) → (val x) *≤ xs → b *≤ xs
lemma-*≤ _ genx = genx
lemma-*≤ b≤u (gecx u≤x u*≤xs) = gecx (transLeB b≤u u≤x) (lemma-*≤ b≤u u*≤xs)

lemma-++*≤ : {b : Bound}{x : A}{xs ys : List A} → LeB b (val x) → b *≤ xs → (val x) *≤ ys → b *≤ (xs ++ (x ∷ ys))
lemma-++*≤ b≤u genx u*≤ys = gecx b≤u (lemma-*≤ b≤u u*≤ys)
lemma-++*≤ b≤u (gecx b≤x b*≤xs) u*≤ys = gecx b≤x (lemma-++*≤ b≤u b*≤xs u*≤ys)
