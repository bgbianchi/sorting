open import Relation.Binary.Core

module InsertSort.Impl1.Correctness.Order {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Data.List
open import Data.Sum
open import InsertSort.Impl1 _≤_ tot≤
open import List.Sorted _≤_

lemma-insert-sorted : {xs : List A}(x : A) → Sorted xs → Sorted (insert x xs)
lemma-insert-sorted {xs = .[]} x nils = singls x  
lemma-insert-sorted {xs = .([ y ])} x  (singls y) 
    with tot≤ x y
... | inj₁ x≤y  = conss x≤y (singls y)
... | inj₂ y≤x  = conss y≤x (singls x) 
lemma-insert-sorted x (conss {y} {z} {ys} y≤z szys)
    with tot≤ x y 
... | inj₁ x≤y = conss x≤y (conss y≤z szys)
... | inj₂ y≤x 
    with tot≤ x z | lemma-insert-sorted x szys
... | inj₁ x≤z | _ = conss y≤x (conss x≤z szys)
... | inj₂ z≤x | h = conss y≤z h 

theorem-insertSort-sorted : (xs : List A) → Sorted (insertSort xs)
theorem-insertSort-sorted [] = nils
theorem-insertSort-sorted (x ∷ xs) = lemma-insert-sorted x (theorem-insertSort-sorted xs) 


