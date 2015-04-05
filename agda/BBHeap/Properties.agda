module BBHeap.Properties {A : Set}(_≤_ : A → A → Set) where

open import Bound.Lower A 
open import BBHeap _≤_
open import Relation.Binary.Core

symm≃ : {b b' : Bound}{h : BBHeap b}{h' : BBHeap b'} → h ≃ h' → h' ≃ h
symm≃ ≃lf = ≃lf
symm≃ (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l≃l') = ≃nd b'≤x' b≤x l'⋘r' l⋘r l'≃r' l≃r (symm≃ l≃l')

trans≃ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ≃ h' → h' ≃ h'' → h ≃ h''
trans≃ ≃lf ≃lf = ≃lf
trans≃ (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r _ l≃l') (≃nd .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' _ l''≃r'' l'≃l'') = ≃nd b≤x b''≤x'' l⋘r l''⋘r'' l≃r l''≃r'' (trans≃ l≃l' l'≃l'')

lemma≃ : {b b' : Bound}{h : BBHeap b}{h' : BBHeap b'} → h ≃ h' → h ⋘ h'  
lemma≃ ≃lf = lf⋘
lemma≃ (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l≃l') = ll⋘ b≤x b'≤x' l⋘r l'⋘r' l'≃r' (trans≃ (symm≃ l≃r) l≃l')

lemma⋗≃ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ⋗ h' → h' ≃ h'' → h ⋗ h''  
lemma⋗≃ (⋗lf b≤x) ≃lf = ⋗lf b≤x
lemma⋗≃ (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r _ l⋗l') (≃nd .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' _ l''≃r'' l'≃l'') = ⋗nd b≤x b''≤x'' l⋘r l''⋘r'' l≃r l''≃r'' (lemma⋗≃ l⋗l' l'≃l'')

lemma⋗ : {b b' : Bound}{h : BBHeap b}{h' : BBHeap b'} → h ⋗ h'  → h ⋙ h'  
lemma⋗ (⋗lf b≤x) = ⋙lf b≤x
lemma⋗ (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l') = ⋙rl b≤x b'≤x' l⋘r l≃r l'⋘r' (lemma⋗≃ l⋗l' l'≃r')

lemma⋗⋗ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ⋗ h' → h'' ⋗ h'  → h ≃ h''  
lemma⋗⋗ (⋗lf b≤x) (⋗lf b''≤x'') = ≃nd b≤x b''≤x'' lf⋘ lf⋘ ≃lf ≃lf ≃lf
lemma⋗⋗ (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r _ l⋗l') (⋗nd b''≤x'' .b'≤x' l''⋘r'' .l'⋘r' l''≃r'' _ l''⋗l') = ≃nd b≤x b''≤x'' l⋘r l''⋘r'' l≃r l''≃r'' (lemma⋗⋗ l⋗l' l''⋗l') 

lemma≃⋗ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ≃ h' → h' ⋗ h'' → h ⋗ h''  
lemma≃⋗ (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r _ l≃l') (⋗nd .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' _ l''≃r'' l'⋗l'') = ⋗nd b≤x b''≤x'' l⋘r l''⋘r'' l≃r l''≃r'' (lemma≃⋗ l≃l' l'⋗l'')
lemma≃⋗ (≃nd b≤x b'≤x' lf⋘ lf⋘ ≃lf ≃lf ≃lf) (⋗lf .b'≤x') = ⋗lf b≤x

lemma-⋘-≃ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ⋘ h' → h' ≃ h'' → h ⋘ h''
lemma-⋘-≃ lf⋘ ≃lf = lf⋘
lemma-⋘-≃ (ll⋘ b≤x b'≤x' l⋘r l'⋘r' _ r≃l') (≃nd .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' _ l''≃r'' l'≃l'') = ll⋘ b≤x b''≤x'' l⋘r l''⋘r'' l''≃r'' (trans≃ r≃l' l'≃l'')
lemma-⋘-≃ (lr⋘ b≤x b'≤x' l⋙r l'⋘r' _ l⋗l') (≃nd .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' _ l''≃r'' l'≃l'') = lr⋘ b≤x b''≤x'' l⋙r l''⋘r'' l''≃r'' (lemma⋗≃ l⋗l' l'≃l'')

lemma-≃-⋙ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ≃ h' → h' ⋙ h'' → h ⋙ h''
lemma-≃-⋙ (≃nd b≤x b'≤x' lf⋘ lf⋘ ≃lf ≃lf ≃lf) (⋙lf .b'≤x') = ⋙lf b≤x
lemma-≃-⋙ (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r _ l≃l') (⋙rl .b'≤x' b''≤x'' .l'⋘r' _ l''⋘r'' l'⋗r'') = ⋙rl b≤x b''≤x'' l⋘r l≃r l''⋘r'' (lemma≃⋗ l≃l' l'⋗r'')
lemma-≃-⋙ (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r _ l≃l') (⋙rr .b'≤x' b''≤x'' .l'⋘r' _ l''⋙r'' l'≃l'') = ⋙rr b≤x b''≤x'' l⋘r l≃r l''⋙r'' (trans≃ l≃l' l'≃l'')

lemma-⋘-⋗ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ⋘ h' → h'' ⋗ h' → h'' ⋙ h
lemma-⋘-⋗ lf⋘ (⋗lf b≤x) = ⋙lf b≤x
lemma-⋘-⋗ (ll⋘ b≤x b'≤x' l⋘r l'⋘r' _ r≃l') (⋗nd b''≤x'' .b'≤x' l''⋘r'' .l'⋘r' l''≃r'' _ l''⋗l') = ⋙rl b''≤x'' b≤x l''⋘r'' l''≃r'' l⋘r (lemma⋗≃ l''⋗l' (symm≃ r≃l'))
lemma-⋘-⋗ (lr⋘ b≤x b'≤x' l⋙r l'⋘r' _ l⋗l') (⋗nd b''≤x'' .b'≤x' l''⋘r'' .l'⋘r' l''≃r'' _ l''⋗l') = ⋙rr b''≤x'' b≤x l''⋘r'' l''≃r'' l⋙r (lemma⋗⋗ l''⋗l' l⋗l')


