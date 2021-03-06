open import Relation.Binary.Core

module BBHeap.Insert {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_
open import BBHeap.Properties _≤_ 
open import BBHeap.Subtyping.Properties _≤_ trans≤
open import Bound.Lower A 
open import Bound.Lower.Order _≤_  
open import Bound.Lower.Order.Properties _≤_ trans≤
open import Data.Sum renaming (_⊎_ to _∨_)
open import Order.Total _≤_ tot≤

mutual
  insert : {b : Bound}{x : A} → LeB b (val x) → BBHeap b → BBHeap b
  insert b≤x leaf = left b≤x lf⋘
  insert {x = x} b≤x (left {x = y} b≤y l⋘r) 
      with tot≤ x y
  ... | inj₁ x≤y 
      with lemma-insert⋘ (lexy refl≤) l⋘r
  ... | inj₁ lᵢ⋘r = left b≤x (subtyping⋘ (lexy x≤y) (lexy x≤y) lᵢ⋘r)
  ... | inj₂ lᵢ⋗r = right b≤x (subtyping⋙ (lexy x≤y) (lexy x≤y) (lemma⋗ lᵢ⋗r))
  insert {x = x} b≤x (left {x = y} b≤y l⋘r) | inj₂ y≤x 
      with lemma-insert⋘ (lexy y≤x) l⋘r
  ... | inj₁ lᵢ⋘r = left b≤y lᵢ⋘r 
  ... | inj₂ lᵢ⋗r = right b≤y (lemma⋗ lᵢ⋗r)
  insert {x = x} b≤x (right {x = y} b≤y l⋙r) 
      with tot≤ x y
  ... | inj₁ x≤y 
      with lemma-insert⋙ (lexy refl≤) l⋙r
  ... | inj₁ l⋙rᵢ = right b≤x (subtyping⋙ (lexy x≤y) (lexy x≤y) l⋙rᵢ)
  ... | inj₂ l≃rᵢ = left b≤x (subtyping⋘ (lexy x≤y) (lexy x≤y) (lemma≃ l≃rᵢ))
  insert {x = x} b≤x (right {x = y} b≤y l⋙r) | inj₂ y≤x 
      with lemma-insert⋙ (lexy y≤x) l⋙r
  ... | inj₁ l⋙rᵢ = right b≤y l⋙rᵢ 
  ... | inj₂ l≃rᵢ = left b≤y (lemma≃ l≃rᵢ)

  lemma-insert⋘ : {b b' : Bound}{x : A}{h : BBHeap b}{h' : BBHeap b'} → (b≤x : LeB b (val x)) → h ⋘ h' → insert b≤x h ⋘ h' ∨ insert b≤x h ⋗ h'
  lemma-insert⋘ b≤x lf⋘ = inj₂ (⋗lf b≤x)
  lemma-insert⋘ {x = x} b≤x (ll⋘ {x = y} b≤y b'≤y' l⋘r l'⋘r' l'≃r' r≃l') 
      with tot≤ x y
  ... | inj₁ x≤y 
      with lemma-insert⋘ (lexy refl≤) l⋘r
  ... | inj₁ lᵢ⋘r = inj₁ (ll⋘ b≤x b'≤y' (subtyping⋘ (lexy x≤y) (lexy x≤y) lᵢ⋘r) l'⋘r' l'≃r' (subtyping≃l (lexy x≤y) r≃l')) 
  ... | inj₂ lᵢ⋗r = inj₁ (lr⋘ b≤x b'≤y' (subtyping⋙ (lexy x≤y) (lexy x≤y) (lemma⋗ lᵢ⋗r)) l'⋘r' l'≃r' (subtyping⋗l (lexy x≤y) (lemma⋗≃ lᵢ⋗r r≃l')))  
  lemma-insert⋘ {x = x} b≤x (ll⋘ {x = y} b≤y b'≤y' l⋘r l'⋘r' l'≃r' r≃l') | inj₂ y≤x 
      with lemma-insert⋘ (lexy y≤x) l⋘r
  ... | inj₁ lᵢ⋘r = inj₁ (ll⋘ b≤y b'≤y' lᵢ⋘r l'⋘r' l'≃r' r≃l') 
  ... | inj₂ lᵢ⋗r = inj₁ (lr⋘ b≤y b'≤y' (lemma⋗ lᵢ⋗r) l'⋘r' l'≃r' (lemma⋗≃ lᵢ⋗r r≃l'))  
  lemma-insert⋘ {x = x} b≤x (lr⋘ {x = y} b≤y b'≤y' l⋙r l'⋘r' l'≃r' l⋗l') 
      with tot≤ x y
  ... | inj₁ x≤y 
      with lemma-insert⋙ (lexy refl≤) l⋙r
  ... | inj₁ l⋙rᵢ = inj₁ (lr⋘ b≤x b'≤y' (subtyping⋙ (lexy x≤y) (lexy x≤y) l⋙rᵢ) l'⋘r' l'≃r' (subtyping⋗l (lexy x≤y) l⋗l'))
  ... | inj₂ l≃rᵢ = inj₂ (⋗nd b≤x b'≤y' (subtyping⋘ (lexy x≤y) (lexy x≤y) (lemma≃ l≃rᵢ)) l'⋘r' (subtyping≃ (lexy x≤y) (lexy x≤y) l≃rᵢ) l'≃r' (subtyping⋗l (lexy x≤y) l⋗l'))
  lemma-insert⋘ {x = x} b≤x (lr⋘ {x = y} b≤y b'≤y' l⋙r l'⋘r' l'≃r' l⋗l') | inj₂ y≤x 
      with lemma-insert⋙ (lexy y≤x) l⋙r
  ... | inj₁ l⋙rᵢ = inj₁ (lr⋘ b≤y b'≤y' l⋙rᵢ l'⋘r' l'≃r' l⋗l')
  ... | inj₂ l≃rᵢ = inj₂ (⋗nd b≤y b'≤y' (lemma≃ l≃rᵢ) l'⋘r' l≃rᵢ l'≃r' l⋗l')

  lemma-insert⋙ : {b b' : Bound}{x : A}{h : BBHeap b}{h' : BBHeap b'} → (b'≤x : LeB b' (val x)) → h ⋙ h' → h ⋙ insert b'≤x h' ∨ h ≃ insert b'≤x h'
  lemma-insert⋙ {x = x} b'≤x (⋙lf {x = y} b≤y) = inj₂ (≃nd b≤y b'≤x lf⋘ lf⋘ ≃lf ≃lf ≃lf)
  lemma-insert⋙ {x = x} b'≤x (⋙rl {x' = y'} b≤y b'≤y' l⋘r l≃r l'⋘r' l⋗r') 
      with tot≤ x y'
  ... | inj₁ x≤y' 
      with lemma-insert⋘ (lexy refl≤) l'⋘r'
  ... | inj₁ l'ᵢ⋘r' = inj₁ (⋙rl b≤y b'≤x l⋘r l≃r (subtyping⋘ (lexy x≤y') (lexy x≤y') l'ᵢ⋘r') (subtyping⋗r (lexy x≤y') l⋗r'))
  ... | inj₂ l'ᵢ⋗r' = inj₁ (⋙rr b≤y b'≤x l⋘r l≃r (subtyping⋙ (lexy x≤y') (lexy x≤y') (lemma⋗ l'ᵢ⋗r')) (subtyping≃r (lexy x≤y') (lemma⋗⋗ l⋗r' l'ᵢ⋗r')))
  lemma-insert⋙ {x = x} b'≤x (⋙rl {x' = y'} b≤y b'≤y' l⋘r l≃r l'⋘r' l⋗r') | inj₂ y'≤x 
      with lemma-insert⋘ (lexy y'≤x) l'⋘r'
  ... | inj₁ l'ᵢ⋘r' = inj₁ (⋙rl b≤y b'≤y' l⋘r l≃r l'ᵢ⋘r' l⋗r')
  ... | inj₂ l'ᵢ⋗r' = inj₁ (⋙rr b≤y b'≤y' l⋘r l≃r (lemma⋗ l'ᵢ⋗r') (lemma⋗⋗ l⋗r' l'ᵢ⋗r'))
  lemma-insert⋙ {x = x} b'≤x (⋙rr {x' = y'} b≤y b'≤y' l⋘r l≃r l'⋙r' l≃l') 
      with tot≤ x y'
  ... | inj₁ x≤y' 
      with lemma-insert⋙ (lexy refl≤) l'⋙r'
  ... | inj₁ l'⋙r'ᵢ = inj₁ (⋙rr b≤y b'≤x l⋘r l≃r (subtyping⋙ (lexy x≤y') (lexy x≤y') l'⋙r'ᵢ) (subtyping≃r (lexy x≤y') l≃l'))
  ... | inj₂ l'≃r'ᵢ = inj₂ (≃nd b≤y b'≤x l⋘r (subtyping⋘ (lexy x≤y') (lexy x≤y') (lemma≃ l'≃r'ᵢ)) l≃r (subtyping≃ (lexy x≤y') (lexy x≤y') l'≃r'ᵢ) (subtyping≃r (lexy x≤y') l≃l'))
  lemma-insert⋙ {x = x} b'≤x (⋙rr {x' = y'} b≤y b'≤y' l⋘r l≃r l'⋙r' l≃l') | inj₂ y'≤x 
      with lemma-insert⋙ (lexy y'≤x) l'⋙r'
  ... | inj₁ l'⋙r'ᵢ = inj₁ (⋙rr b≤y b'≤y' l⋘r l≃r l'⋙r'ᵢ l≃l')
  ... | inj₂ l'≃r'ᵢ = inj₂ (≃nd b≤y b'≤y' l⋘r (lemma≃ l'≃r'ᵢ) l≃r l'≃r'ᵢ l≃l')
