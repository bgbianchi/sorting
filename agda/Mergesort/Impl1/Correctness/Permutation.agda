{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module Mergesort.Impl1.Correctness.Permutation {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.List
open import Data.Product
open import Data.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Equivalence A
open import List.Permutation.Pair A
open import List.Permutation.Pair.Properties A
open import Mergesort.Impl1 _≤_ tot≤
open import Size
open import SList
open import SList.Properties
open import SOList.Lower _≤_

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
theorem-mergesort-∼ xs = trans∼ (lemma-unsize-size A xs) (lemma-mergesort (size A xs))
