{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module Mergesort.Correctness.Permutation {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.List
open import Data.Product
open import Data.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Concatenation A
open import List.Permutation.Base.Equivalence A
open import List.Permutation.Pair A
open import List.Permutation.Pair.Properties A
open import List.Properties A
open import LRTree {A}
open import Mergesort _≤_ tot≤
open import OList _≤_ renaming (forget to forget')
open import Relation.Binary.PropositionalEquality 
open import Size
open import SList
open import SList.Properties
open import SOList.Lower _≤_

-- Option 1

lemma-deal : {ι : Size} → (xs : SList A {ι}) → unsize A xs ≈ unsize× A (deal xs)
lemma-deal snil = ≈[]l []
lemma-deal (x ∙ snil) = ≈[]r (x ∷ [])
lemma-deal (x ∙ (y ∙ xs)) 
    with lemma-deal xs
... | xs≈ys,zs = ≈xl (≈xr xs≈ys,zs)

lemma-merge : {ι ι' : Size}{b : Bound}(xs : SOList {ι} b)(ys : SOList {ι'} b) → forget (merge xs ys) ≈ (forget xs , forget ys) 
lemma-merge onil ys = ≈[]l (forget ys)
lemma-merge xs onil 
    with xs
... | onil = ≈[]r []
... | (:< {x = z} b≤z zs) = ≈[]r (z ∷ forget zs)
lemma-merge (:< {x = x} b≤x xs)  (:< {x = y} b≤y ys) 
    with tot≤ x y
... | inj₁ x≤y = ≈xl (lemma-merge xs (:< (lexy x≤y) ys))
... | inj₂ y≤x = ≈xr (lemma-merge (:< (lexy y≤x) xs) ys)

lemma-mergesort : {ι : Size}(xs : SList A {↑ ι}) → unsize A xs ∼ forget (mergesort xs)
lemma-mergesort snil = ∼[]
lemma-mergesort (x ∙ snil) = ∼x /head /head ∼[]
lemma-mergesort (x ∙ (y ∙ xs)) = lemma≈ (≈xl (≈xr (lemma-deal xs))) (lemma-mergesort (x ∙ ys)) (lemma-mergesort (y ∙ zs)) (lemma-merge (mergesort (x ∙ ys)) (mergesort (y ∙ zs)))
                where d = deal xs
                      ys = proj₁ d
                      zs = proj₂ d

theorem-mergesort-∼ : (xs : List A) → xs ∼ (forget (mergesort (size A xs)))
theorem-mergesort-∼ xs = lemma-trans∼ (lemma-unsize-size A xs) (lemma-mergesort (size A xs))

-- Option 2

lemma-merge''-empty : {b : Bound}(xs : OList b) → merge'' xs (onil {b}) ≡ xs
lemma-merge''-empty onil = refl
lemma-merge''-empty (:< b≤x xs) = refl

mutual
  lemma-merge'' : {b : Bound}(xs ys : OList b) → (forget' xs ++ forget' ys) ∼ forget' (merge'' xs ys)
  lemma-merge'' onil ys = lemma-refl∼
  lemma-merge'' xs onil rewrite ++id (forget' xs) | lemma-merge''-empty xs = lemma-refl∼
  lemma-merge'' (:< {x = x} b≤x xs) (:< {x = y} b≤y ys) 
      with tot≤ x y
  ... | inj₁ x≤y  = ∼x /head /head (lemma-merge'' xs (:< (lexy x≤y) ys))
  ... | inj₂ y≤x = 
                  let f'xxsyf'ys∼yf'xxsf'ys = ∼x (lemma++/ {y} {forget' (:< b≤x xs)}) /head lemma-refl∼ ;
                       yf'xxsf'ys∼yf'm'xxsys = ∼x /head /head (lemma-merge''xs (lexy y≤x) xs ys)
                  in lemma-trans∼ f'xxsyf'ys∼yf'xxsf'ys yf'xxsf'ys∼yf'm'xxsys

  lemma-merge''xs : {b : Bound}{x : A} → (b≤x : LeB b (val x)) → (xs : OList (val x)) → (ys : OList b) → (forget' (:< b≤x xs) ++ forget' ys) ∼ forget' (merge''xs b≤x xs ys)
  lemma-merge''xs b≤x xs onil rewrite ++id (forget' xs) | lemma-merge''-empty xs = lemma-refl∼
  lemma-merge''xs {x = x} b≤x xs (:< {x = y} b≤y ys) 
      with tot≤ x y
  ... | inj₁ x≤y = ∼x /head /head (lemma-merge'' xs (:< (lexy x≤y) ys))
  ... | inj₂ y≤x = 
                  let f'xxsyf'ys∼yf'xxsf'ys = ∼x (lemma++/ {y} {forget' (:< b≤x xs)}) /head lemma-refl∼ ;
                       yf'xxsf'ys∼yf'm'xxsys = ∼x /head /head (lemma-merge''xs (lexy y≤x) xs ys)
                  in lemma-trans∼ f'xxsyf'ys∼yf'xxsf'ys yf'xxsf'ys∼yf'm'xxsys

lemma-insert : (x : A)(t : LRTree) → (x ∷ flatten t) ∼ flatten (insert x t)
lemma-insert x empty = ∼x /head /head ∼[]
lemma-insert x (leaf y) = ∼x (/tail /head) /head (∼x /head /head ∼[])
lemma-insert x (node left l r) = lemma++∼r (lemma-insert x l)
lemma-insert x (node right l r) = 
                let xlr∼lxr = ∼x /head (lemma++/ {x} {flatten l}) lemma-refl∼ ;
                     lxr∼lrᵢ = lemma++∼l {flatten l} (lemma-insert x r)
                in lemma-trans∼ xlr∼lxr lxr∼lrᵢ

lemma-deal' : (xs : List A) → xs ∼ flatten (deal' xs)
lemma-deal' [] = ∼[]
lemma-deal' (x ∷ xs) = lemma-trans∼ (∼x /head /head (lemma-deal' xs)) (lemma-insert x (deal' xs))

lemma-merge' : (t : LRTree) → flatten t ∼ forget' (merge' t)
lemma-merge' empty = ∼[]
lemma-merge' (leaf x) = ∼x /head /head ∼[]
lemma-merge' (node t l r) = 
                let flfr∼f'm'lf'm'r = lemma++∼ (lemma-merge' l) (lemma-merge' r) ;
                     f'm'lf'm'r∼m''m''lm''r = lemma-merge'' (merge' l) (merge' r)
                in lemma-trans∼ flfr∼f'm'lf'm'r f'm'lf'm'r∼m''m''lm''r

theorem-mergesort'-∼ : (xs : List A) → xs ∼ (forget' (mergesort' xs))
theorem-mergesort'-∼ xs = lemma-trans∼ (lemma-deal' xs) (lemma-merge' (deal' xs))
