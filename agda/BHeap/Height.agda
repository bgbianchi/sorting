open import Relation.Binary.Core

module BHeap.Height {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : Total _≤_) where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import BHeap _≤_
open import BHeap.Properties _≤_
open import Data.Nat renaming (_≤_ to _≤ₙ_)
open import Data.Nat.Properties
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (trans)

open DecTotalOrder decTotalOrder hiding (refl)

theorem-height-merge : {b : Bound}{x : A}(b≤x : LeB b (val x))(l r : BHeap (val x)) → height (merge tot≤ l r) ≤ₙ height (nd b≤x l r)
theorem-height-merge _ lf r = ≤-step (reflexive refl)
theorem-height-merge _ l lf rewrite lemma-merge-lf tot≤ l 
    with total (height l) zero 
... | inj₁ hl≤0 rewrite antisym hl≤0 z≤n = ≤-step (reflexive refl)
... | inj₂ 0≤hl = ≤-step (reflexive refl)
theorem-height-merge b≤x (nd {x = y} x≤y l r) (nd {x = y'} x≤y' l' r') 
    with tot≤ y y' | total (height (nd x≤y l r)) (height (nd x≤y' l' r')) 
... | inj₁ y≤y' | inj₁ hylr≤hy'l'r' 
    with total (height (merge tot≤ l r)) (height (nd (lexy y≤y') l' r'))
... | inj₁ hmlr≤hy'l'r' = reflexive refl
... | inj₂ hy'l'r'≤hmlr rewrite antisym (trans (theorem-height-merge x≤y l r) hylr≤hy'l'r') hy'l'r'≤hmlr = reflexive refl
theorem-height-merge b≤x (nd {x = y} x≤y l r) (nd {x = y'} x≤y' l' r') | inj₁ y≤y' | inj₂ hy'l'r'≤hylr 
    with total (height (merge tot≤ l r)) (height (nd (lexy y≤y') l' r'))
... | inj₁ hmlr≤hy'l'r' = s≤s hy'l'r'≤hylr
... | inj₂ hy'l'r'≤hmlr = s≤s (theorem-height-merge x≤y l r)
theorem-height-merge b≤x (nd {x = y} x≤y l r) (nd {x = y'} x≤y' l' r') | inj₂ y'≤y | inj₁ hylr≤hy'l'r'  
    with total (height (nd (lexy y'≤y) l r)) (height (merge tot≤ l' r'))
... | inj₁ hylr≤hml'r' = s≤s (theorem-height-merge x≤y' l' r')
... | inj₂ hml'r'≤hylr = s≤s hylr≤hy'l'r'
theorem-height-merge b≤x (nd {x = y} x≤y l r) (nd {x = y'} x≤y' l' r') | inj₂ y'≤y | inj₂ hy'l'r'≤hylr  
    with total (height (nd (lexy y'≤y) l r)) (height (merge tot≤ l' r'))
... | inj₁ hylr≤hml'r' rewrite antisym (trans (theorem-height-merge x≤y' l' r') hy'l'r'≤hylr) hylr≤hml'r' = reflexive refl
... | inj₂ hml'r'≤hylr = reflexive refl
