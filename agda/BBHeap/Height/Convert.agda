{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module BBHeap.Height.Convert {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : Total _≤_)  where

open import Bound.Lower A 
open import Bound.Lower.Order _≤_
open import BBHeap _≤_ 
open import BBHeap.Properties _≤_
open import BBHeap.Height _≤_
open import BHeap _≤_ hiding (forget) renaming (height to heightₙ)
open import Data.List
open import Data.Nat renaming (_≤_ to _≤ₙ_)
open import Data.Nat.Properties
open import Data.Sum
open import Function using (_∘_)
open import OList _≤_
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (trans)
open import SNat 

open DecTotalOrder decTotalOrder hiding (refl)

data _⊳_ : {b b' : Bound} → BHeap b → BHeap b' → Set where
  ⊳leaf : {b b' : Bound} 
                   → lf {b} ⊳ lf {b'}
  ⊳left : {b b' : Bound}{x : A}{l r : BHeap (val x)}{l' : BHeap b'}
                   (b≤x : LeB b (val x)) 
                   → l ⊳ r → l ⊳ l' 
                   → (nd b≤x l r) ⊳ l'
  ⊳both : {b b' : Bound}{x x' : A}{l r : BHeap (val x)}{l' r' : BHeap (val x')}
                   (b≤x : LeB b (val x))
                   (b'≤x' : LeB b' (val x')) 
                   → l ⊳ r 
                   → l ⊳ l' 
                   → l ⊳ r' 
                   → (nd b≤x l r) ⊳ (nd b'≤x' l' r')

lemma-≃-⊳ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ≃ r → relax l ⊳ relax r
lemma-≃-⊳ ≃lf = ⊳leaf
lemma-≃-⊳ (≃nd b≤x b'≤x' _ _ l≃r l'≃r' l≃l') = ⊳both b≤x b'≤x' (lemma-≃-⊳ l≃r) (lemma-≃-⊳ l≃l') (lemma-≃-⊳ (trans≃ l≃l' l'≃r'))

lemma-⋗-⊳ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋗ r → relax l ⊳ relax r
lemma-⋗-⊳ (⋗lf b≤x) = ⊳left b≤x ⊳leaf ⊳leaf
lemma-⋗-⊳ (⋗nd b≤x b'≤x' _ _ l≃r l'≃r' l⋗l') = ⊳both b≤x b'≤x' (lemma-≃-⊳ l≃r) (lemma-⋗-⊳ l⋗l') (lemma-⋗-⊳ (lemma⋗≃ l⋗l' l'≃r'))

lemma-⋙-⊳ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋙ r → relax l ⊳ relax r
lemma-⋙-⊳ (⋙lf b≤x) = ⊳left b≤x ⊳leaf ⊳leaf
lemma-⋙-⊳ (⋙rl b≤x b'≤x' _ l≃r l'⋘r' l⋗r') = ⊳both b≤x b'≤x' (lemma-≃-⊳ l≃r) (lemma-⋙-⊳ (lemma-⋘-⋗ l'⋘r' l⋗r')) (lemma-⋗-⊳ l⋗r')
lemma-⋙-⊳ (⋙rr b≤x b'≤x' _ l≃r l'⋙r' l≃l') =  ⊳both b≤x b'≤x' (lemma-≃-⊳ l≃r) (lemma-≃-⊳ l≃l') (lemma-⋙-⊳ (lemma-≃-⋙ l≃l' l'⋙r'))

lemma-⋘-⊳ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋘ r → relax l ⊳ relax r
lemma-⋘-⊳ lf⋘ = ⊳leaf
lemma-⋘-⊳ (ll⋘ b≤x b'≤x' l⋘r _ l'≃r' r≃l') = ⊳both b≤x b'≤x' (lemma-⋘-⊳ l⋘r) (lemma-⋘-⊳ (lemma-⋘-≃ l⋘r r≃l')) (lemma-⋘-⊳ (lemma-⋘-≃ l⋘r (trans≃ r≃l' l'≃r')))
lemma-⋘-⊳ (lr⋘ b≤x b'≤x' l⋙r _ l'≃r' l⋗l') = ⊳both b≤x b'≤x' (lemma-⋙-⊳ l⋙r) (lemma-⋗-⊳ l⋗l') (lemma-⋗-⊳ (lemma⋗≃ l⋗l' l'≃r'))

lemma-⊳-heightₙ : {b b' : Bound}{l : BHeap b}{r : BHeap b'} → l ⊳ r → heightₙ r ≤ₙ heightₙ l 
lemma-⊳-heightₙ ⊳leaf = z≤n
lemma-⊳-heightₙ (⊳left {l = l} {r = r} b≤x l⊳r l⊳l') 
    with total (heightₙ l) (heightₙ r) 
... | inj₁ hl≤hr rewrite antisym (lemma-⊳-heightₙ l⊳r) hl≤hr = ≤-step (lemma-⊳-heightₙ l⊳l')
... | inj₂ hr≤hl = trans (lemma-⊳-heightₙ l⊳l') (≤-step (reflexive refl))
lemma-⊳-heightₙ (⊳both {l = l} {r = r} {l' = l'} {r' = r'} b≤x b'≤x' l⊳r l⊳l' l⊳r') 
    with total (heightₙ l) (heightₙ r) | total (heightₙ l') (heightₙ r') 
... | inj₁ hl≤hr | inj₁ hl'≤hr' rewrite antisym (lemma-⊳-heightₙ l⊳r) hl≤hr = s≤s (lemma-⊳-heightₙ l⊳r')
... | inj₁ hl≤hr | inj₂ hr'≤hl' rewrite antisym (lemma-⊳-heightₙ l⊳r) hl≤hr = s≤s (lemma-⊳-heightₙ l⊳l')
... | inj₂ hr≤hl | inj₁ hl'≤hr' = s≤s (lemma-⊳-heightₙ l⊳r')
... | inj₂ hr≤hl | inj₂ hr'≤hl' = s≤s (lemma-⊳-heightₙ l⊳l')

theorem-height-relax : {b : Bound}(h : BBHeap b) → toNat (height h) ≡ heightₙ (relax h)
theorem-height-relax leaf = refl
theorem-height-relax (left {l = l} {r = r} _ l⋘r) 
    with total (heightₙ (relax l)) (heightₙ (relax r)) 
... | inj₁ hl≤hr rewrite antisym (lemma-⊳-heightₙ (lemma-⋘-⊳ l⋘r)) hl≤hr | theorem-height-relax l = refl
... | inj₂ hr≤hl rewrite theorem-height-relax l = refl
theorem-height-relax (right {l = l} {r = r} _ l⋙r) 
    with total (heightₙ (relax l)) (heightₙ (relax r)) 
... | inj₁ hl≤hr rewrite antisym (lemma-⊳-heightₙ (lemma-⋙-⊳ l⋙r)) hl≤hr | theorem-height-relax l = refl
... | inj₂ hr≤hl rewrite theorem-height-relax l = refl
