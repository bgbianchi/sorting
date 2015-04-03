{-# OPTIONS --sized-types #-}
open import Data.Sum renaming (_⊎_ to _∨_)

module Mergesort {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : (a b : A) → a ≤ b ∨ b ≤ a)  where

open import Bound _≤_
open import Data.List
open import Data.Product
open import Function using (_∘_)
open import Permutation A
open import Permutation.Product A
open import Permutation.Equivalence A
open import Size
open import SList
open import SOList _≤_
open import Sorting _≤_

deal : {ι : Size} → SList A {ι} → SList A {ι} × SList A {ι}
deal snil = (snil , snil) 
deal (x ∙ snil) = (x ∙ snil , snil) 
deal (x ∙ (y ∙ xs)) 
    with deal xs
... | (ys , zs) = (x ∙ ys , y ∙ zs)

lemma-deal : {ι : Size} → (xs : SList A {ι}) → unsize A xs ≈ unsize× A (deal xs)
lemma-deal snil = ≈[]l []
lemma-deal (x ∙ snil) = ≈[]r (x ∷ [])
lemma-deal (x ∙ (y ∙ xs)) 
    with lemma-deal xs
... | xs≈ys,zs = ≈xl (≈xr xs≈ys,zs)

merge : {ι ι' : Size}{b : Bound} → SOList {ι} b  → SOList {ι'} b → SOList b
merge onil ys = ys 
merge xs onil = xs 
merge (:< {x = x} b≤x xs)  (:< {x = y} b≤y ys) 
    with tot≤ x y
... | inj₁ x≤y = :< b≤x (merge xs (:< (lexy x≤y) ys))
... | inj₂ y≤x = :< b≤y (merge (:< (lexy y≤x) xs) ys)

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

mergesort : {ι : Size} → SList A {↑ ι} → SOList bot
mergesort snil = onil
mergesort (x ∙ snil) = :< {x = x} lebx onil
mergesort (x ∙ (y ∙ xs)) 
    with deal xs
... | (ys , zs) = merge (mergesort (x ∙ ys)) (mergesort (y ∙ zs))

lemma-mergesort : {ι : Size}(xs : SList A {↑ ι}) → unsize A xs ∼ forget (mergesort xs)
lemma-mergesort snil = ∼[]
lemma-mergesort (x ∙ snil) = ∼x /head /head ∼[]
lemma-mergesort (x ∙ (y ∙ xs)) = lemma≈ (≈xl (≈xr (lemma-deal xs))) (lemma-mergesort (x ∙ ys)) (lemma-mergesort (y ∙ zs)) (lemma-merge (mergesort (x ∙ ys)) (mergesort (y ∙ zs)))
                where d = deal xs
                      ys = proj₁ d
                      zs = proj₂ d

theorem-mergesort-sorted : (xs : List A) → Sorted (forget (mergesort (size A xs)))
theorem-mergesort-sorted = lemma-solist-sorted  ∘ mergesort ∘ (size A)

theorem-mergesort-∼ : (xs : List A) → xs ∼ (forget (mergesort (size A xs)))
theorem-mergesort-∼ xs = lemma-trans∼ (lemma-unsize-size A xs) (lemma-mergesort (size A xs))

