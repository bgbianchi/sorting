module List.Permutation.Concatenation (A : Set) where

open import List.Permutation A
open import List.Permutation.Equivalence A
open import List.Permutation.Preorder A
open import Data.List
open import Data.Product
open import Relation.Binary.PreorderReasoning ∼-preorder
open import Algebra
open import Algebra.Structures

lemma++/r : {x : A}{xs ys xs' : List A} → (xs / x ⟶ xs') → (xs ++ ys) / x ⟶ (xs' ++ ys)
lemma++/r /head = /head
lemma++/r (/tail xs/x⟶xs') = /tail (lemma++/r xs/x⟶xs')

lemma++/l : {y : A}{xs ys ys' : List A} → (ys / y ⟶ ys') → (xs ++ ys) / y ⟶ (xs ++ ys')
lemma++/l {xs = []} ys/y⟶ys' = ys/y⟶ys'
lemma++/l {xs = x ∷ xs} ys/y⟶ys' = /tail (lemma++/l {xs = xs} ys/y⟶ys')

lemma++/ : {y : A}{xs ys : List A} → (xs ++ y ∷ ys) / y ⟶ (xs ++ ys)
lemma++/ {xs = xs} = lemma++/l {xs = xs} /head

lemma++∼r : {xs xs' ys : List A} →  xs ∼ xs' → (xs ++ ys) ∼ (xs' ++ ys)
lemma++∼r {xs} {xs'} {[]} xs∼xs' 
                   rewrite ((proj₂ (IsMonoid.identity (Monoid.isMonoid (monoid A)))) xs) 
                            | ((proj₂ (IsMonoid.identity (Monoid.isMonoid (monoid A)))) xs') = xs∼xs'
lemma++∼r {xs} {xs'} {y ∷ ys} xs∼xs' =  ∼x (lemma++/ {y} {xs} {ys}) (lemma++/ {y} {xs'} {ys}) (lemma++∼r xs∼xs') 

lemma++∼l : {xs ys ys' : List A} →  ys ∼  ys' → (xs ++ ys) ∼ (xs ++ ys')
lemma++∼l {xs = []} ys∼ys' = ys∼ys'
lemma++∼l {xs = x ∷ xs} ys∼ys' = ∼x /head /head (lemma++∼l {xs = xs} ys∼ys')

lemma++∼ : {xs ys xs' ys' : List A} →  xs ∼  xs' →  ys ∼ ys' → (xs ++ ys) ∼ (xs' ++ ys')
lemma++∼ {xs} {ys} {xs'} {ys'} xs∼xs' ys∼ys' 
  = begin
     xs ++ ys
     ∼⟨ lemma++∼r xs∼xs'  ⟩
     xs' ++ ys
     ∼⟨ lemma++∼l {xs = xs'} ys∼ys'  ⟩
     xs' ++ ys'
    ∎
