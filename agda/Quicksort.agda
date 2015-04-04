{-# OPTIONS --sized-types #-}
open import Data.Sum renaming (_⊎_ to _∨_)

module Quicksort {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : (x y : A) → x ≤ y ∨ y ≤ x)
                  (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)  where

open import Bound2 _≤_ trans≤
open import Data.List
open import Data.Product
open import Function using (_∘_)
open import Permutation A
open import Permutation.Concatenation A
open import Permutation.Equivalence A
open import Permutation.Product A
open import SBList _≤_ trans≤
open import Size
open import SOList2 _≤_ trans≤
open import Sorting _≤_

deal : {ι : Size}{b t : Bound}{x : A} → LeB b (val x) → LeB (val x) t → SBList {ι} b t → SBList {ι} b (val x) × SBList {ι} (val x) t
deal b≤x x≤t (nil b≤t) = (nil b≤x , nil x≤t)
deal {x = x} b≤x x≤t (cons y b≤y y≤t ys) 
    with tot≤ x y | deal b≤x x≤t ys
... | inj₁ x≤y | (us , vs) = (us , cons y (lexy x≤y) y≤t vs)
... | inj₂ y≤x | (us , vs) = (cons y b≤y (lexy y≤x) us , vs) 

quickSort : {ι : Size}{b t : Bound} → SBList {ι} b t → SOList b t
quickSort (nil b≤t) = onil b≤t
quickSort (cons x b≤x x≤t xs) 
    with deal b≤x x≤t xs 
... | (ys , zs) = ocons x (quickSort ys) (quickSort zs)

theorem-quickSort-sorted : (xs : List A) → Sorted (forget (quickSort (bound xs)))
theorem-quickSort-sorted = lemma-solist-sorted ∘ quickSort ∘ bound

lemma-deal : {ι : Size}{b t : Bound}{x : A} → (b≤x : LeB b (val x)) → (x≤t : LeB (val x) t) → (xs : SBList {ι} b t) → unbound xs ≈ unbound× (deal b≤x x≤t xs)
lemma-deal _ _ (nil _) = ≈[]r []
lemma-deal {x = x} b≤x x≤t (cons y b≤y y≤t ys) 
    with tot≤ x y 
... | inj₁ x≤y = ≈xr (lemma-deal b≤x x≤t ys)
... | inj₂ y≤x = ≈xl (lemma-deal b≤x x≤t ys)

lemma-quickSort : {ι : Size}{b t : Bound}(xs : SBList {ι} b t) → unbound xs ∼ forget (quickSort xs)
lemma-quickSort (nil _) = ∼[]
lemma-quickSort (cons x b≤x x≤t xs) =  lemma-trans∼ (lemma≈∼ (≈xr (lemma-deal b≤x x≤t xs))) (lemma++∼ (lemma-quickSort ys) (∼x /head /head (lemma-quickSort zs)))
                where yszs = deal b≤x x≤t xs
                      ys = proj₁ yszs
                      zs = proj₂ yszs

theorem-quickSort∼ : (xs : List A) → xs ∼ forget (quickSort (bound xs))
theorem-quickSort∼ xs = lemma-trans∼ (lemma-unbound-bound xs) (lemma-quickSort (bound xs))

