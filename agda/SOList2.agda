{-# OPTIONS --sized-types #-}
module SOList2 {A : Set} 
               (_≤_ : A → A → Set) 
               (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)  where

open import Bound2 _≤_ trans≤
open import Data.List
open import List.BOrder _≤_ trans≤
open import Size
open import Sorting _≤_

data SOList : {ι : Size} → Bound → Bound → Set where
  onil : {ι : Size}{b t : Bound} 
                   → LeB b t 
                   → SOList {↑ ι} b t
  ocons : {ι : Size}{b t : Bound}(x : A) 
                   → SOList {ι} b (val x) 
                   → SOList {ι} (val x) t 
                   → SOList {↑ ι} b t

forget : {b t : Bound} → SOList b t → List A
forget (onil _) = []
forget (ocons x xs ys) = forget xs ++ (x ∷ forget ys)

lemma-solist≤ : {ι : Size}{b t : Bound} → SOList {ι} b t → LeB b t
lemma-solist≤ (onil b≤t) = b≤t
lemma-solist≤ (ocons x xs ys) = transLeB (lemma-solist≤ xs) (lemma-solist≤ ys)

lemma-solist≤* : {ι : Size}{b : Bound}{x : A} → (xs : SOList {ι} b (val x)) → forget xs ≤* (val x)
lemma-solist≤* (onil _) = lenx
lemma-solist≤* (ocons x xs ys) = lemma-++≤* (lemma-solist≤ ys) (lemma-solist≤* xs) (lemma-solist≤* ys)

lemma-solist*≤ : {ι : Size}{b t : Bound} → (xs : SOList {ι} b t) → b *≤ forget xs
lemma-solist*≤ (onil _) = genx
lemma-solist*≤ (ocons x xs ys) = lemma-++*≤ (lemma-solist≤ xs) (lemma-solist*≤ xs) (lemma-solist*≤ ys)

lemma-solist-sorted : {ι : Size}{b t : Bound}(xs : SOList {ι} b t) → Sorted (forget xs)
lemma-solist-sorted (onil _) = nils
lemma-solist-sorted (ocons x xs ys) = lemma-sorted++ (lemma-solist≤* xs) (lemma-solist*≤ ys) (lemma-solist-sorted xs) (lemma-solist-sorted ys)




