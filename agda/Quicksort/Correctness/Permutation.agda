{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module Quicksort.Correctness.Permutation {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) where

open import Bound.Total A
open import Bound.Total.Order _≤_
open import Data.List
open import Data.Product
open import Data.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Concatenation A
open import List.Permutation.Base.Equivalence A
open import List.Permutation.Pair A
open import List.Permutation.Pair.Properties A
open import Quicksort _≤_ tot≤
open import SBList _≤_
open import SBList.Properties _≤_
open import Size
open import SOList.Total _≤_

lemma-deal : {ι : Size}{b t : Bound}{x : A} → (b≤x : LeB b (val x)) → (x≤t : LeB (val x) t) → (xs : SBList {ι} b t) → unbound xs ≈ unbound× (deal b≤x x≤t xs)
lemma-deal _ _ (nil _) = ≈[]r []
lemma-deal {x = x} b≤x x≤t (cons y b≤y y≤t ys) 
    with tot≤ x y 
... | inj₁ x≤y = ≈xr (lemma-deal b≤x x≤t ys)
... | inj₂ y≤x = ≈xl (lemma-deal b≤x x≤t ys)

lemma-quickSort : {ι : Size}{b t : Bound}(xs : SBList {ι} b t) → unbound xs ∼ forget (quickSort xs)
lemma-quickSort (nil _) = ∼[]
lemma-quickSort (cons x b≤x x≤t xs) =  trans∼ (lemma≈∼ (≈xr (lemma-deal b≤x x≤t xs))) (lemma++∼ (lemma-quickSort ys) (∼x /head /head (lemma-quickSort zs)))
                where yszs = deal b≤x x≤t xs
                      ys = proj₁ yszs
                      zs = proj₂ yszs

theorem-quickSort∼ : (xs : List A) → xs ∼ forget (quickSort (bound xs))
theorem-quickSort∼ xs = trans∼ (lemma-unbound-bound xs) (lemma-quickSort (bound xs))

