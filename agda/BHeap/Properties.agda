module BHeap.Properties {A : Set}(_≤_ : A → A → Set)  where

open import Bound.Lower A
open import Bound.Lower.Order _≤_ 
open import BHeap _≤_ 
open import Data.List
open import Data.Nat 
open import Data.Sum 
open import Nat.Sum
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality 

lemma-merge-lf : {b : Bound}(tot≤ : Total _≤_)(h : BHeap b) → merge tot≤ h lf ≡ h
lemma-merge-lf _ lf = refl
lemma-merge-lf _ (nd b≤x l r) = refl

lemma-merge# : {b : Bound}(tot≤ : Total _≤_)(l r : BHeap b) → # (merge tot≤ l r) ≡ # l + # r
lemma-merge# _ lf r = refl
lemma-merge# tot≤ l lf rewrite lemma-merge-lf tot≤ l | +id (# l) = refl
lemma-merge# tot≤ (nd {x = y} x≤y l r) (nd {x = y'} x≤y' l' r') 
    with tot≤ y y'
... | inj₁ y≤y' rewrite lemma-merge# tot≤ l r = refl
... | inj₂ y'≤y rewrite lemma-merge# tot≤ l' r' | +assoc (# l + # r) (# l' + # r') = refl

lemma-merge≤′ : {b : Bound}{x : A}(tot≤ : Total _≤_)(b≤x : LeB b (val x))(l r : BHeap (val x)) → suc (# (merge tot≤ l r)) ≤′ # (nd b≤x l r)
lemma-merge≤′ tot≤ b≤x l r rewrite lemma-merge# tot≤ l r = ≤′-refl
