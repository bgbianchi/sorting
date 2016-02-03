open import Relation.Binary.Core

module Heapsort.Impl2.Correctness.Permutation {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_ hiding (forget) renaming (flatten to flatten')
open import BBHeap.Compound _≤_
open import BBHeap.Drop _≤_ tot≤ trans≤
open import BBHeap.Drop.Properties _≤_ tot≤ trans≤
open import BBHeap.Heapify _≤_ tot≤ trans≤
open import BBHeap.Insert _≤_ tot≤ trans≤
open import BBHeap.Insert.Properties _≤_ tot≤ trans≤
open import BBHeap.Order _≤_
open import BBHeap.Order.Properties _≤_
open import Bound.Lower A
open import Bound.Lower.Order _≤_ 
open import Data.List
open import Heapsort.Impl2 _≤_ tot≤ trans≤
open import List.Permutation.Base A
open import List.Permutation.Base.Equivalence A
open import OList _≤_
open import Order.Total _≤_ tot≤

lemma-flatten-flatten' : {b : Bound}(h : BBHeap b)(accₕ : Acc h) → forget (flatten h accₕ) ∼ flatten' h
lemma-flatten-flatten' leaf _ = ∼[]
lemma-flatten-flatten' (left {l = l} {r = r} b≤x l⋘r) (acc rs) = ∼x /head /head (trans∼ (lemma-flatten-flatten' (drop⋘ b≤x l⋘r) (rs (drop⋘ b≤x l⋘r) (lemma-drop≤′ (cl b≤x l⋘r)))) (lemma-drop⋘∼ b≤x l⋘r))
lemma-flatten-flatten' (right {l = l} {r = r} b≤x l⋙r) (acc rs) = ∼x /head /head (trans∼ (lemma-flatten-flatten' (drop⋙ b≤x l⋙r) (rs (drop⋙ b≤x l⋙r) (lemma-drop≤′ (cr b≤x l⋙r)))) (lemma-drop⋙∼ b≤x l⋙r))

lemma-flatten'-flatten : {b : Bound}(h : BBHeap b)(accₕ : Acc h) → (flatten' h) ∼ (forget (flatten h accₕ))
lemma-flatten'-flatten h tₕ = sym∼ (lemma-flatten-flatten' h tₕ)

theorem-heapsort∼ : (xs : List A) → xs ∼ forget (heapsort xs)
theorem-heapsort∼ [] = ∼[]
theorem-heapsort∼ (x ∷ xs) =
                     let h = heapify xs ;
                          accₕ = ≺-wf h ;
                          hᵢ = insert lebx h ;
                          accₕᵢ = ≺-wf hᵢ ;
                          xs∼fh = theorem-heapsort∼ xs ;
                          fh∼f'h = lemma-flatten-flatten' h accₕ ;
                          xs∼f'h = trans∼ xs∼fh fh∼f'h ;
                          xxs∼xf'h = ∼x /head /head xs∼f'h ;
                          xf'h∼f'hᵢ = lemma-insert∼ lebx h ;
                          xxs∼f'hᵢ = trans∼ xxs∼xf'h xf'h∼f'hᵢ ;
                          f'hᵢ∼fhᵢ = lemma-flatten'-flatten hᵢ accₕᵢ
                      in trans∼ xxs∼f'hᵢ f'hᵢ∼fhᵢ
