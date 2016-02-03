module BHeap.Properties {A : Set}(_≤_ : A → A → Set)  where

open import Bound.Lower A
open import Bound.Lower.Order _≤_ 
open import BHeap _≤_ 
open import Data.List
open import Data.Nat 
open import Data.Sum 
open import Nat.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Concatenation A
open import List.Permutation.Base.Equivalence A
open import List.Properties A
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

lemma-merge∼ : {b : Bound}(tot≤ : Total _≤_)(l r : BHeap b) → flatten (merge tot≤ l r) ∼ (flatten l ++ flatten r)
lemma-merge∼ _ lf r = refl∼
lemma-merge∼ tot≤ l lf rewrite lemma-merge-lf tot≤ l | ++id (flatten l) = refl∼
lemma-merge∼ tot≤ (nd {x = y} b≤x l r) (nd {x = y'} b≤y' l' r') 
    with tot≤ y y'
... | inj₁ y≤y' = lemma++∼r (∼x /head /head (lemma-merge∼ tot≤ l r))
... | inj₂ y'≤y = trans∼ (lemma++∼l {xs = y' ∷ (y ∷ flatten l ++ flatten r)} (lemma-merge∼ tot≤ l' r')) (∼x /head (lemma++/ {xs = y ∷ flatten l ++ flatten r}) refl∼)
