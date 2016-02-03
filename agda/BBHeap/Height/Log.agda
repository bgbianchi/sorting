{-# OPTIONS --sized-types #-}
open import Relation.Binary.Core

module BBHeap.Height.Log {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : Total _≤_ ) where

open import BBHeap _≤_ hiding (#)
open import BBHeap.Height _≤_ 
open import BBHeap.Properties _≤_
open import Bound.Lower A 
open import Data.Sum renaming (_⊎_ to _∨_)
open import SNat
open import SNat.Log
open import SNat.Order
open import SNat.Order.Properties
open import SNat.Properties
open import SNat.Sum
open import Relation.Binary.PropositionalEquality

lemma-height-≃ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ≃ r → height l ≡ height r
lemma-height-≃ ≃lf = refl
lemma-height-≃ (≃nd _ _ _ _ _ _ l≃l') rewrite lemma-height-≃ l≃l' = refl

lemma-height'-≃ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ≃ r → height' l ≡ height' r
lemma-height'-≃ ≃lf = refl
lemma-height'-≃ (≃nd _ _ _ _ l≃r l'≃r' l≃l') rewrite lemma-height'-≃ (trans≃ (trans≃ (sym≃ l≃r) l≃l') l'≃r') = refl

lemma-height-height'-⋗ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋗ r → height l ≡ succ (height' r)
lemma-height-height'-⋗ (⋗lf _) = refl
lemma-height-height'-⋗ (⋗nd _ _ _ _ _ l'≃r' l⋗l') rewrite lemma-height-height'-⋗ l⋗l' | lemma-height'-≃ l'≃r' = refl

lemma-height-height'-⋘ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋘ r → height l ≡ height' r ∨ height l ≡ succ (height' r)
lemma-height-height'-⋘ lf⋘ = inj₁ refl
lemma-height-height'-⋘ (ll⋘ _ _ l⋘r _ l'≃r' r≃l') 
    with lemma-height-height'-⋘ l⋘r 
... | inj₁ hl≡h'r rewrite hl≡h'r | lemma-height'-≃ (trans≃ r≃l' l'≃r') = inj₁ refl
... | inj₂ hl≡h'r+1 rewrite hl≡h'r+1 | lemma-height'-≃ (trans≃ r≃l' l'≃r') = inj₂ refl
lemma-height-height'-⋘ (lr⋘ _ _ _  _ l'≃r' l⋗l') rewrite lemma-height-height'-⋗ (lemma⋗≃ l⋗l' l'≃r')= inj₂ refl

lemma-height-height'-⋙ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋙ r → height l ≡ height' r ∨ height l ≡ succ (height' r)
lemma-height-height'-⋙ (⋙lf _) = inj₂ refl
lemma-height-height'-⋙ (⋙rl _ _ _ _ _ l⋗r')  rewrite lemma-height-height'-⋗ l⋗r' = inj₂ refl
lemma-height-height'-⋙ (⋙rr _ _ _ _ l'⋙r' l≃l') 
    with lemma-height-height'-⋙ l'⋙r' 
... | inj₁ hl'≡h'r' rewrite lemma-height-≃ l≃l' | hl'≡h'r' = inj₁ refl
... | inj₂ hl'≡h'r'+1  rewrite lemma-height-≃ l≃l' | hl'≡h'r'+1 = inj₂ refl

lemma-height-height' : {b : Bound}(h : BBHeap b) → height h ≡ height' h ∨ height h ≡ succ (height' h)
lemma-height-height' leaf = inj₁ refl
lemma-height-height' (left _ l⋘r) 
    with lemma-height-height'-⋘ l⋘r
... | inj₁ hl≡h'r rewrite hl≡h'r = inj₁ refl
... | inj₂ hl≡h'r+1 rewrite hl≡h'r+1 = inj₂ refl
lemma-height-height' (right _ l⋙r) 
    with lemma-height-height'-⋙ l⋙r
... | inj₁ hl≡h'r rewrite hl≡h'r = inj₁ refl
... | inj₂ hl≡h'r+1 rewrite hl≡h'r+1 = inj₂ refl

lemma-#-≃ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ≃ r → # l ≡ # r
lemma-#-≃ ≃lf = refl
lemma-#-≃ (≃nd _ _ _ _ l≃r l'≃r' l≃l') 
                   rewrite lemma-#-≃ (sym≃ l≃r) 
                            | lemma-#-≃ l≃l' 
                            | lemma-#-≃ l'≃r' = refl
                   
lemma-#-⋗ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋗ r → # l ≡ succ (# r + # r)
lemma-#-⋗ (⋗lf _) = refl
lemma-#-⋗ (⋗nd _ _ _ _ l≃r l'≃r' l⋗l') 
                   rewrite  lemma-#-≃ (sym≃ l≃r) 
                            | lemma-#-⋗ l⋗l' 
                            | lemma-#-≃ l'≃r' = refl

lemma-⋘-# : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋘ r → # r ≤′ # l
lemma-⋘-# lf⋘ = refl≤′
lemma-⋘-# (ll⋘ {r' = r'} _ _ l⋘r _ l'≃r' r≃l') 
                   rewrite lemma-#-≃ r≃l' 
                             | lemma-#-≃ l'≃r' = lemma-s≤′s (+-right-monotony-≤′ (# r') (lemma-≡-≤′ (lemma-#-≃ (sym≃ (trans≃ r≃l' l'≃r'))) (lemma-⋘-# l⋘r))) 
lemma-⋘-# (lr⋘ {r = r} {r' = r'} _ _ _ _ l'≃r' l⋗l') 
                   rewrite lemma-#-⋗ l⋗l' 
                             | lemma-#-≃ l'≃r' = lemma-s≤′s (≤′-step (lemma-m≤′m+n (# r' + # r') (# r)))

lemma-#-⋙ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋙ r → # l ≤′ succ (# r + # r)  
lemma-#-⋙ (⋙lf _) = refl≤′
lemma-#-⋙ (⋙rl {l' = l'}{r' = r'} _ _ _ l≃r l'⋘r' l⋗r') 
                   rewrite lemma-#-≃ (sym≃ l≃r) 
                             | lemma-#-⋗ l⋗r' 
                             | +-assoc-succ (# r' + # r') (# r' + # r') 
                             | +-assoc-succ (# l' + # r') (# l' + # r') = lemma-s≤′s (lemma-s≤′s (lemma-s≤′s (lemma-4m≤′n+m+n+m (lemma-⋘-# l'⋘r'))))
lemma-#-⋙ (⋙rr {l' = l'} {r' = r'} _ _ _ l≃r _ l≃l') 
                   rewrite lemma-#-≃ (sym≃ l≃r) 
                             | lemma-#-≃ l≃l' 
                             | +-assoc-succ (# l' + # r') (# l' + # r') = lemma-s≤′s (≤′-step (≤′-step (lemma-2m≤′m+n+m+n (# l') (# r'))))

mutual
  lemma-⋙-# : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋙ r → # r ≤′ # l
  lemma-⋙-# (⋙lf _) = ≤′-step refl≤′
  lemma-⋙-# (⋙rl {r' = r'} _ _ _ l≃r l'⋘r' l⋗r') 
                   rewrite lemma-#-≃ (sym≃ l≃r) 
                             | lemma-#-⋗ l⋗r' = lemma-s≤′s (trans≤′ (+-right-monotony-≤′ (# r') (lemma-#-⋘ l'⋘r')) (lemma-s≤′s (+-left-monotony-≤′ (# r' + # r') (≤′-step (lemma-n≤′2n (# r'))))))
  lemma-⋙-# (⋙rr {l' = l'} {r' = r'} _ _ _ l≃r l'⋙r' l≃l') 
                   rewrite lemma-#-≃ (sym≃ l≃r) 
                             | lemma-#-≃ l≃l' 
                             | +-comm (# l') (# r') = lemma-s≤′s (+-right-monotony-≤′ (# l') (lemma-⋙-# l'⋙r'))

  lemma-#-⋘ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋘ r → # l ≤′ succ (# r + # r)
  lemma-#-⋘ lf⋘ = ≤′-step refl≤′
  lemma-#-⋘ (ll⋘ {r = r} _ _ l⋘r _ l'≃r' r≃l') 
                   rewrite lemma-#-≃ (sym≃ l'≃r') 
                             | lemma-#-≃ (sym≃ r≃l') 
                             | +-assoc-succ (# r + # r) (# r + # r) 
                             | +-assoc-left (# r + # r) (# r) (# r) = lemma-s≤′s (≤′-step (trans≤′ (+-right-monotony-≤′ (# r) (lemma-#-⋘ l⋘r)) (lemma-s≤′s (lemma-m≤′m+n ((# r + # r) + # r) (# r)))))
  lemma-#-⋘ (lr⋘ {r' = r'} _ _ l⋙r _ l'≃r' l⋗l') 
                   rewrite lemma-#-⋗ l⋗l' 
                             | lemma-#-≃ l'≃r' = lemma-s≤′s (lemma-s≤′s (+-left-monotony-≤′ (# r' + # r') (trans≤′ (lemma-⋙-# l⋙r) (lemma-≡-≤′ (lemma-#-⋗ (lemma⋗≃ l⋗l' l'≃r')) refl≤′)))) 

lemma-#-#' : {b : Bound}(h : BBHeap b) → #' h ≤′ # h
lemma-#-#' leaf = refl≤′
lemma-#-#' (left {r = r} _ l⋘r) = lemma-s≤′s (trans≤′ (lemma-2m≤′2n (lemma-#-#' r)) (+-right-monotony-≤′ (# r) (lemma-⋘-# l⋘r)))
lemma-#-#' (right {r = r} _ l⋙r) = lemma-s≤′s (trans≤′ (lemma-2m≤′2n (lemma-#-#' r)) (+-right-monotony-≤′ (# r) (lemma-⋙-# l⋙r)))

lemma-height'-#' : {b : Bound}(h : BBHeap b) → height' h ≤′ log₂ (#' h + #' h)
lemma-height'-#' leaf = refl≤′
lemma-height'-#' (left {r = r} _ _) = trans≤′ (lemma-s≤′s (trans≤′ (lemma-height'-#' r) (lemma-≤′-log (≤′-step (refl≤′ {#' r + #' r}))))) (lemma-1+logn≤′log2n (#' r + #' r))
lemma-height'-#' (right {r = r} _ _) = trans≤′ (lemma-s≤′s (trans≤′ (lemma-height'-#' r) (lemma-≤′-log (≤′-step (refl≤′ {#' r + #' r}))))) (lemma-1+logn≤′log2n (#' r + #' r))

lemma-height'-# : {b : Bound}(h : BBHeap b) → height' h ≤′ succ (log₂ (# h))
lemma-height'-# h = trans≤′ (trans≤′ (lemma-height'-#' h) (lemma-log2n≤′1+logn (#' h))) (lemma-s≤′s (lemma-≤′-log (lemma-#-#' h)))

theorem-height-# : {b : Bound}(h : BBHeap b) → height h ≤′ succ (succ (log₂ (# h)))
theorem-height-# h 
    with lemma-height-height' h
... | inj₁ hh≡h'h rewrite hh≡h'h = ≤′-step (lemma-height'-# h)
... | inj₂  hh≡h'h+1 rewrite hh≡h'h+1 = lemma-s≤′s (lemma-height'-# h)


