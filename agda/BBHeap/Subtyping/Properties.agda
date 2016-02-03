open import Relation.Binary.Core

module BBHeap.Subtyping.Properties {A : Set}
                  (_≤_ : A → A → Set) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_
open import BBHeap.Subtyping  _≤_ trans≤
open import BBHeap.Properties  _≤_ 
open import Bound.Lower A 
open import Bound.Lower.Order _≤_
open import Bound.Lower.Order.Properties _≤_ trans≤
open import List.Permutation.Base A
open import List.Permutation.Base.Equivalence A

subtyping⋘l : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}(b''≤b : LeB b'' b) → h ⋘ h' → subtyping b''≤b h ⋘ h' 
subtyping⋘l b''≤b lf⋘ = lf⋘ 
subtyping⋘l b''≤b (ll⋘ b≤x b'≤x' l⋘r l'⋘r' l'≃r' r≃l') = ll⋘ (transLeB b''≤b b≤x) b'≤x' l⋘r l'⋘r' l'≃r' r≃l'
subtyping⋘l b''≤b (lr⋘ b≤x b'⋘x' l⋙r l'⋘r' l'≃r' l⋗l') = lr⋘ (transLeB b''≤b b≤x) b'⋘x' l⋙r l'⋘r' l'≃r' l⋗l'

subtyping⋘ : {b b' b'' b''' : Bound}{h : BBHeap b}{h' : BBHeap b'}(b''≤b : LeB b'' b)(b'''≤b' : LeB b''' b') → h ⋘ h' → subtyping b''≤b h ⋘ subtyping b'''≤b' h' 
subtyping⋘ b''≤b b'''≤b' lf⋘ = lf⋘ 
subtyping⋘ b''≤b b'''≤b' (ll⋘ b≤x b'≤x' l⋘r l'⋘r' l'≃r' r≃l') = ll⋘ (transLeB b''≤b b≤x) (transLeB b'''≤b' b'≤x') l⋘r l'⋘r' l'≃r' r≃l'
subtyping⋘ b''≤b b'''≤b' (lr⋘ b≤x b'⋘x' l⋙r l'⋘r' l'≃r' l⋗l') = lr⋘ (transLeB b''≤b b≤x) (transLeB b'''≤b' b'⋘x') l⋙r l'⋘r' l'≃r' l⋗l'

subtyping⋙r : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}(b''≤b' : LeB b'' b') → h ⋙ h' → h ⋙ subtyping b''≤b' h' 
subtyping⋙r b''≤b' (⋙lf b≤x) = ⋙lf b≤x 
subtyping⋙r b''≤b' (⋙rl b≤x b'≤x' l⋘r l≃r l'⋘r' l⋗r') = ⋙rl b≤x (transLeB b''≤b' b'≤x') l⋘r l≃r l'⋘r' l⋗r'
subtyping⋙r b''≤b' (⋙rr b≤x b'⋘x' l⋘r l≃r l'⋙r' l≃l') = ⋙rr b≤x (transLeB b''≤b' b'⋘x') l⋘r l≃r l'⋙r' l≃l'

subtyping⋙ : {b b' b'' b''' : Bound}{h : BBHeap b}{h' : BBHeap b'}(b''≤b : LeB b'' b)(b'''≤b' : LeB b''' b') → h ⋙ h' → subtyping b''≤b h ⋙ subtyping b'''≤b' h' 
subtyping⋙ b''≤b b'''≤b' (⋙lf b≤x) = ⋙lf (transLeB b''≤b b≤x) 
subtyping⋙ b''≤b b'''≤b' (⋙rl b≤x b'≤x' l⋘r l≃r l'⋘r' l⋗r') = ⋙rl (transLeB b''≤b b≤x) (transLeB b'''≤b' b'≤x') l⋘r l≃r l'⋘r' l⋗r'
subtyping⋙ b''≤b b'''≤b' (⋙rr b≤x b'⋘x' l⋘r l≃r l'⋙r' l≃l') = ⋙rr (transLeB b''≤b b≤x) (transLeB b'''≤b' b'⋘x') l⋘r l≃r l'⋙r' l≃l'

subtyping≃r : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}(b''≤b' : LeB b'' b') → h ≃ h' → h ≃ subtyping b''≤b' h' 
subtyping≃r b''≤b' ≃lf = ≃lf
subtyping≃r b''≤b' (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l≃l') = ≃nd b≤x (transLeB b''≤b' b'≤x') l⋘r l'⋘r' l≃r l'≃r' l≃l'

subtyping≃l : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}(b''≤b : LeB b'' b) → h ≃ h' → subtyping b''≤b h ≃ h' 
subtyping≃l b''≤b h≃h' = sym≃ (subtyping≃r b''≤b (sym≃ h≃h'))

subtyping≃ : {b b' b'' b''' : Bound}{h : BBHeap b}{h' : BBHeap b'}(b''≤b : LeB b'' b)(b'''≤b' : LeB b''' b') → h ≃ h' → subtyping b''≤b h ≃ subtyping b'''≤b' h' 
subtyping≃ b''≤b b'''≤b' h≃h' = subtyping≃r b'''≤b' (subtyping≃l b''≤b h≃h')

subtyping⋗r : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}(b''≤b' : LeB b'' b') → h ⋗ h' → h ⋗ subtyping b''≤b' h' 
subtyping⋗r b''≤b' (⋗lf b≤x) = ⋗lf b≤x
subtyping⋗r b''≤b' (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l') = ⋗nd b≤x (transLeB b''≤b' b'≤x') l⋘r l'⋘r' l≃r l'≃r' l⋗l'

subtyping⋗l : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}(b''≤b : LeB b'' b) → h ⋗ h' → subtyping b''≤b h ⋗ h' 
subtyping⋗l b''≤b (⋗lf b≤x) = ⋗lf (transLeB b''≤b b≤x)
subtyping⋗l b''≤b (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l') = ⋗nd (transLeB b''≤b b≤x) b'≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l'

subtyping⋗ : {b b' b'' b''' : Bound}{h : BBHeap b}{h' : BBHeap b'}(b''≤b : LeB b'' b)(b'''≤b' : LeB b''' b') → h ⋗ h' → subtyping b''≤b h ⋗ subtyping b'''≤b' h' 
subtyping⋗ b''≤b b'''≤b' h⋗h' = subtyping⋗r b'''≤b' (subtyping⋗l b''≤b h⋗h')

lemma-subtyping# : {b b' : Bound}(b'≤b : LeB b' b)(h : BBHeap b) → # (subtyping b'≤b h) ≡ # h 
lemma-subtyping# b'≤b leaf = refl
lemma-subtyping# b'≤b (left b≤x l⋘r) = refl
lemma-subtyping# b'≤b (right b≤x l⋙r) = refl

lemma-subtyping≡ : {b b' : Bound}(b'≤b : LeB b' b)(h : BBHeap b) → (flatten (subtyping b'≤b h)) ≡ flatten h
lemma-subtyping≡ b'≤b leaf = refl
lemma-subtyping≡ b'≤b (left {l = l} {r = r} b≤x l⋘r) rewrite lemma-subtyping≡ b≤x l | lemma-subtyping≡ b≤x r = refl
lemma-subtyping≡ b'≤b (right {l = l} {r = r} b≤x l⋙r) rewrite lemma-subtyping≡ b≤x l | lemma-subtyping≡ b≤x r = refl

lemma-subtyping∼ : {b b' : Bound}(b'≤b : LeB b' b)(h : BBHeap b) → flatten (subtyping b'≤b h) ∼ flatten h
lemma-subtyping∼ b'≤b leaf = ∼[]
lemma-subtyping∼ b'≤b (left b≤x l⋘r) = ∼x /head /head refl∼
lemma-subtyping∼ b'≤b (right b≤x l⋙r) = ∼x /head /head refl∼
