{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module SOList.Total.Properties {A : Set} 
               (_≤_ : A → A → Set) 
               (trans≤ : Transitive _≤_)  where

open import Bound.Total A
open import Bound.Total.Order _≤_ 
open import Bound.Total.Order.Properties _≤_ trans≤
open import List.Order.Bounded _≤_
open import List.Order.Bounded.Properties _≤_ trans≤
open import List.Sorted _≤_
open import Size
open import SOList.Total _≤_

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




