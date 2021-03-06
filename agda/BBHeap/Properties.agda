module BBHeap.Properties {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_
open import BBHeap.Perfect _≤_
open import Bound.Lower A 
open import Bound.Lower.Order _≤_ 
open import Data.Empty

sym≃ : {b b' : Bound}{h : BBHeap b}{h' : BBHeap b'} → h ≃ h' → h' ≃ h
sym≃ ≃lf = ≃lf
sym≃ (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l≃l') = ≃nd b'≤x' b≤x l'⋘r' l⋘r l'≃r' l≃r (sym≃ l≃l')

trans≃ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ≃ h' → h' ≃ h'' → h ≃ h''
trans≃ ≃lf ≃lf = ≃lf
trans≃ (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r _ l≃l') (≃nd .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' _ l''≃r'' l'≃l'') = ≃nd b≤x b''≤x'' l⋘r l''⋘r'' l≃r l''≃r'' (trans≃ l≃l' l'≃l'')

lemma≃ : {b b' : Bound}{h : BBHeap b}{h' : BBHeap b'} → h ≃ h' → h ⋘ h'  
lemma≃ ≃lf = lf⋘
lemma≃ (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l≃l') = ll⋘ b≤x b'≤x' l⋘r l'⋘r' l'≃r' (trans≃ (sym≃ l≃r) l≃l')

lemma⋗≃ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ⋗ h' → h' ≃ h'' → h ⋗ h''  
lemma⋗≃ (⋗lf b≤x) ≃lf = ⋗lf b≤x
lemma⋗≃ (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r _ l⋗l') (≃nd .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' _ l''≃r'' l'≃l'') = ⋗nd b≤x b''≤x'' l⋘r l''⋘r'' l≃r l''≃r'' (lemma⋗≃ l⋗l' l'≃l'')

lemma⋗ : {b b' : Bound}{h : BBHeap b}{h' : BBHeap b'} → h ⋗ h'  → h ⋙ h'  
lemma⋗ (⋗lf b≤x) = ⋙lf b≤x
lemma⋗ (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l') = ⋙rl b≤x b'≤x' l⋘r l≃r l'⋘r' (lemma⋗≃ l⋗l' l'≃r')

lemma⋗⋗ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ⋗ h' → h'' ⋗ h'  → h ≃ h''  
lemma⋗⋗ (⋗lf b≤x) (⋗lf b''≤x'') = ≃nd b≤x b''≤x'' lf⋘ lf⋘ ≃lf ≃lf ≃lf
lemma⋗⋗ (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r _ l⋗l') (⋗nd b''≤x'' .b'≤x' l''⋘r'' .l'⋘r' l''≃r'' _ l''⋗l') = ≃nd b≤x b''≤x'' l⋘r l''⋘r'' l≃r l''≃r'' (lemma⋗⋗ l⋗l' l''⋗l') 

lemma⋗⋗' : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ⋗ h' → h ⋗ h''  → h' ≃ h''
lemma⋗⋗' (⋗lf b≤x) (⋗nd .b≤x _ .lf⋘ _ _ _ ()) 
lemma⋗⋗' (⋗nd .b≤x _ .lf⋘ _ _ _ ()) (⋗lf b≤x)
lemma⋗⋗' (⋗lf b≤x) (⋗lf .b≤x) = ≃lf
lemma⋗⋗' (⋗nd b≤x b'≤x' l⋘r l'⋘r' _ l'≃r' l⋗l') (⋗nd .b≤x b''≤x'' .l⋘r l''⋘r'' _ l''≃r'' l⋗l'') = ≃nd b'≤x' b''≤x'' l'⋘r' l''⋘r'' l'≃r' l''≃r'' (lemma⋗⋗' l⋗l' l⋗l'')

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
lemma-⋘-⋗ (ll⋘ b≤x b'≤x' l⋘r l'⋘r' _ r≃l') (⋗nd b''≤x'' .b'≤x' l''⋘r'' .l'⋘r' l''≃r'' _ l''⋗l') = ⋙rl b''≤x'' b≤x l''⋘r'' l''≃r'' l⋘r (lemma⋗≃ l''⋗l' (sym≃ r≃l'))
lemma-⋘-⋗ (lr⋘ b≤x b'≤x' l⋙r l'⋘r' _ l⋗l') (⋗nd b''≤x'' .b'≤x' l''⋘r'' .l'⋘r' l''≃r'' _ l''⋗l') = ⋙rr b''≤x'' b≤x l''⋘r'' l''≃r'' l⋙r (lemma⋗⋗ l''⋗l' l⋗l')

lemma-≃-⊥ : {b b' : Bound}{h : BBHeap b}{h' : BBHeap b'} → h ≃ h' → h ⋗ h' → ⊥
lemma-≃-⊥ () (⋗lf _) 
lemma-≃-⊥ (≃nd .b≤x .b'≤x' .l⋘r .l'⋘r' _ _ l≃l') (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l')
    with lemma-≃-⊥ l≃l' l⋗l'
... | ()

lemma-⋘-⊥ : {b b' : Bound}{x x' : A}{l r : BBHeap (val x)}{l' r' : BBHeap (val x')}(b≤x : LeB b (val x))(b'≤x' : LeB b' (val x'))(l⋙r : l ⋙ r)(l'⋘r' : l' ⋘ r') → l ≃ l' → right b≤x l⋙r ⋘ left b'≤x' l'⋘r' → ⊥ 
lemma-⋘-⊥ b≤x b'≤x' l⋙r l'⋘r' l≃l' (lr⋘ .b≤x .b'≤x' .l⋙r .l'⋘r' _ l⋗l')
    with lemma-≃-⊥ l≃l' l⋗l'
... | ()

lemma-perfect : {b b' : Bound}{h : BBHeap b}{h' : BBHeap b'} → h ⋘ h' → Perfect h'
lemma-perfect lf⋘ = plf
lemma-perfect (ll⋘ b≤x b'≤x' l⋘l l'⋘l' l'≃r' r≃l') = pnd b'≤x' l'⋘l' l'≃r'
lemma-perfect (lr⋘ b≤x b'≤x' l⋙r l'⋘l' l'≃r' l⋗l') = pnd b'≤x' l'⋘l' l'≃r'



