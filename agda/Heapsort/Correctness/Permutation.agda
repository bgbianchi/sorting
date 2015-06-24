{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module Heapsort.Correctness.Permutation {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import Bound.Lower A
open import Bound.Lower.Order _≤_ 
open import BBHeap _≤_ hiding (forget)
open import BBHeap.Insert _≤_ tot≤ trans≤
open import BHeap _≤_ hiding (forget) renaming (flatten to flatten')
open import BHeap.Order _≤_
open import BHeap.Order.Properties _≤_
open import BHeap.Properties _≤_ 
open import Data.List
open import Data.Nat renaming (_≤_ to _≤ₙ_)
open import Data.Nat.Properties
open import Data.Sum
open import Heapsort _≤_ tot≤ trans≤
open import List.Permutation.Base A
open import List.Permutation.Base.Equivalence A
open import List.Permutation.Base.Concatenation A
open import List.Properties A
open import OList _≤_
open import Order.Total _≤_ tot≤
open import Relation.Binary

open DecTotalOrder decTotalOrder hiding (refl)

lemma-merge-flatten' : {b : Bound}(l r : BHeap b) → flatten' (merge tot≤ l r) ∼ (flatten' l ++ flatten' r)
lemma-merge-flatten' lf r = lemma-refl∼
lemma-merge-flatten' l lf rewrite lemma-merge-lf tot≤ l | ++id (flatten' l) = lemma-refl∼
lemma-merge-flatten' (nd {x = y} b≤x l r) (nd {x = y'} b≤y' l' r') 
    with tot≤ y y'
... | inj₁ y≤y' = lemma++∼r (∼x /head /head (lemma-merge-flatten' l r))
... | inj₂ y'≤y = lemma-trans∼ (lemma++∼l {xs = y' ∷ (y ∷ flatten' l ++ flatten' r)} (lemma-merge-flatten' l' r')) (∼x /head (lemma++/ {xs = y ∷ flatten' l ++ flatten' r}) lemma-refl∼)

lemma-flatten-flatten' : {b : Bound}(h : BHeap b)(accₕ : Acc h) → forget (flatten h accₕ) ∼ flatten' h
lemma-flatten-flatten' lf _ = ∼[]
lemma-flatten-flatten' (nd b≤x l r) (acc rs) = ∼x /head /head (lemma-trans∼ (lemma-flatten-flatten' (merge tot≤ l r) (rs (merge tot≤ l r) (lemma-merge≤′ tot≤ b≤x l r))) (lemma-merge-flatten' l r))

lemma-flatten'-flatten : {b : Bound}(h : BHeap b)(accₕ : Acc h) → (flatten' h) ∼ (forget (flatten h accₕ))
lemma-flatten'-flatten h tₕ = lemma-sym∼ (lemma-flatten-flatten' h tₕ)

lemma-subtyping-flatten' : {b b' : Bound}(b'≤b : LeB b' b)(h : BBHeap b) → (flatten' (relax (subtyping b'≤b h))) ≡ flatten' (relax h)
lemma-subtyping-flatten' b'≤b leaf = refl
lemma-subtyping-flatten' b'≤b (left {l = l} {r = r} b≤x l⋘r) rewrite lemma-subtyping-flatten' b≤x l | lemma-subtyping-flatten' b≤x r = refl
lemma-subtyping-flatten' b'≤b (right {l = l} {r = r} b≤x l⋙r) rewrite lemma-subtyping-flatten' b≤x l | lemma-subtyping-flatten' b≤x r = refl

lemma-insert-flatten' : {b : Bound}{x : A}(b≤x : LeB b (val x))(h : BBHeap b) → (x ∷ flatten' (relax h)) ∼ (flatten' (relax (insert b≤x h)))
lemma-insert-flatten' b≤x leaf = lemma-refl∼
lemma-insert-flatten' {x = x} b≤x (left {x = y} {l = l} {r = r} b≤y l⋘r) 
    with tot≤ x y
... | inj₁ x≤y 
    with lemma-insert⋘ (lexy refl≤) l⋘r
... | inj₁ lᵢ⋘r 
           rewrite lemma-subtyping-flatten' {val y} {val x} (lexy x≤y) (insert {val y} {y} (lexy refl≤) l) 
                     | lemma-subtyping-flatten' {val y} {val x} (lexy x≤y) r 
                     = ∼x /head /head (lemma++∼r (lemma-insert-flatten' (lexy refl≤) l)) 
... | inj₂ lᵢ⋗r 
           rewrite  lemma-subtyping-flatten' {val y} {val x} (lexy x≤y) (insert {val y} {y} (lexy refl≤) l) 
                      | lemma-subtyping-flatten' {val y} {val x} (lexy x≤y) r 
                      = ∼x /head /head (lemma++∼r (lemma-insert-flatten' (lexy refl≤) l))
lemma-insert-flatten' {x = x} b≤x (left {x = y} {l = l} {r = r} b≤y l⋘r) | inj₂ y≤x 
    with lemma-insert⋘ (lexy y≤x) l⋘r
... | inj₁ lᵢ⋘r = ∼x (/tail /head) /head (lemma++∼r (lemma-insert-flatten' (lexy y≤x) l)) 
... | inj₂ lᵢ⋗r = ∼x (/tail /head) /head (lemma++∼r (lemma-insert-flatten' (lexy y≤x) l)) 
lemma-insert-flatten' {x = x} b≤x (right {x = y} {l = l} {r = r} b≤y l⋙r) 
    with tot≤ x y
... | inj₁ x≤y 
    with lemma-insert⋙ (lexy refl≤) l⋙r
... | inj₁ l⋙rᵢ 
           rewrite lemma-subtyping-flatten' {val y} {val x} (lexy x≤y) (insert {val y} {y} (lexy refl≤) r) 
                     | lemma-subtyping-flatten' {val y} {val x} (lexy x≤y) l 
                     = ∼x /head /head (lemma-trans∼ (∼x /head (lemma++/ {xs = flatten' (relax l)}) lemma-refl∼) (lemma++∼l {xs = flatten' (relax l)} (lemma-insert-flatten' (lexy refl≤) r)))
... | inj₂ l≃rᵢ 
           rewrite lemma-subtyping-flatten' {val y} {val x} (lexy x≤y) (insert {val y} {y} (lexy refl≤) r) 
                     | lemma-subtyping-flatten' {val y} {val x} (lexy x≤y) l 
                     = ∼x /head /head (lemma-trans∼ (∼x /head (lemma++/ {xs = flatten' (relax l)}) lemma-refl∼) (lemma++∼l {xs = flatten' (relax l)} (lemma-insert-flatten' (lexy refl≤) r)))
lemma-insert-flatten' {x = x} b≤x (right {x = y} {l = l} {r = r} b≤y l⋙r) | inj₂ y≤x 
    with lemma-insert⋙ (lexy y≤x) l⋙r
... | inj₁ l⋙rᵢ = ∼x (/tail /head) /head (lemma-trans∼ (∼x /head (lemma++/ {xs = flatten' (relax l)}) lemma-refl∼) (lemma++∼l {xs = flatten' (relax l)} (lemma-insert-flatten' (lexy y≤x) r)))
... | inj₂ l≃rᵢ = ∼x (/tail /head) /head (lemma-trans∼ (∼x /head (lemma++/ {xs = flatten' (relax l)}) lemma-refl∼) (lemma++∼l {xs = flatten' (relax l)} (lemma-insert-flatten' (lexy y≤x) r)))

theorem-heapsort∼ : (xs : List A) → xs ∼ forget (heapsort xs)
theorem-heapsort∼ [] = ∼[]
theorem-heapsort∼ (x ∷ xs) = lemma-trans∼ (lemma-trans∼ (∼x /head /head (lemma-trans∼ (theorem-heapsort∼ xs) (lemma-flatten-flatten' h' accₕ'))) (lemma-insert-flatten' lebx h)) (lemma-flatten'-flatten (hᵢ) accₕᵢ)
              where h = heapify xs
                    h' = relax h
                    accₕ' = ≺-wf h'
                    hᵢ = relax (insert lebx h)
                    accₕᵢ = ≺-wf hᵢ
