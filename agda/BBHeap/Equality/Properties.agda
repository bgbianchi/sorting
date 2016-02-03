open import Relation.Binary.Core

module BBHeap.Equality.Properties {A : Set}(_≤_ : A → A → Set)  where

open import BBHeap _≤_
open import BBHeap.Equality _≤_
open import Bound.Lower A

refl≈ : {b : Bound}{h : BBHeap b} → h ≈ h
refl≈ {b} {leaf} = ≈leaf
refl≈ {b} {left b≤x l⋘r} = ≈left b≤x b≤x l⋘r l⋘r refl≈ refl≈
refl≈ {b} {right b≤x l⋙r} = ≈right b≤x b≤x l⋙r l⋙r refl≈ refl≈

sym≈ : {b b' : Bound}{h : BBHeap b}{h' : BBHeap b'} → h ≈ h' → h' ≈ h
sym≈ ≈leaf = ≈leaf
sym≈ (≈left b≤x b'≤x' l⋘r l'⋘r' l≈l' r≈r') = ≈left b'≤x' b≤x l'⋘r' l⋘r (sym≈ l≈l') (sym≈ r≈r')
sym≈ (≈right b≤x b'≤x' l⋙r l'⋙r' l≈l' r≈r') = ≈right b'≤x' b≤x l'⋙r' l⋙r (sym≈ l≈l') (sym≈ r≈r')

trans≈ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ≈ h' → h' ≈ h'' → h ≈ h''
trans≈ ≈leaf ≈leaf = ≈leaf
trans≈ (≈left b≤x b'≤x' l⋘r l'⋘r' l≈l' r≈r') (≈left .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' l'≈l'' r'≈r'') = ≈left b≤x b''≤x'' l⋘r l''⋘r'' (trans≈ l≈l' l'≈l'') (trans≈ r≈r' r'≈r'')
trans≈ (≈right b≤x b'≤x' l⋙r l'⋙r' l≈l' r≈r') (≈right .b'≤x' b''≤x'' .l'⋙r' l''⋙r'' l'≈l'' r'≈r'') = ≈right b≤x b''≤x'' l⋙r l''⋙r'' (trans≈ l≈l' l'≈l'') (trans≈ r≈r' r'≈r'')

mutual
  lemma≈≃ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ≈ h' → h' ≃ h'' → h ≃ h''
  lemma≈≃ ≈leaf ≃lf = ≃lf
  lemma≈≃ (≈left b≤x b'≤x' l⋘r l'⋘r' l≈l' r≈r') (≃nd .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' l'≃r' l''≃r'' l'≃l'') = ≃nd b≤x b''≤x'' l⋘r l''⋘r'' (lemma≈≃ l≈l' (lemma≃≈ l'≃r' (sym≈ r≈r'))) l''≃r'' (lemma≈≃ l≈l' l'≃l'')

  lemma≃≈ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ≃ h' → h' ≈ h'' → h ≃ h''
  lemma≃≈ ≃lf ≈leaf = ≃lf
  lemma≃≈ (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l≃l') (≈left .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' l'≈l'' r'≈r'') = ≃nd b≤x b''≤x'' l⋘r l''⋘r'' l≃r (lemma≈≃ (sym≈ l'≈l'') (lemma≃≈ l'≃r' r'≈r'')) (lemma≃≈ l≃l' l'≈l'')

lemma≈⋗ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ≈ h' → h' ⋗ h'' → h ⋗ h''
lemma≈⋗ (≈left b≤x .b'≤x' lf⋘ .lf⋘ ≈leaf ≈leaf) (⋗lf b'≤x') = ⋗lf b≤x
lemma≈⋗ (≈left b≤x .b'≤x' l⋘r .l'⋘r' l≈l' r≈r') (⋗nd b'≤x' b''≤x'' l'⋘r' l''⋘r'' l'≃r' l''≃r'' l'⋗l'') = ⋗nd b≤x b''≤x'' l⋘r l''⋘r'' (lemma≈≃ l≈l' (lemma≃≈ l'≃r' (sym≈ r≈r'))) l''≃r'' (lemma≈⋗ l≈l' l'⋗l'')

lemma⋗≈ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ⋗ h' → h' ≈ h'' → h ⋗ h''
lemma⋗≈ (⋗lf b≤x) ≈leaf = ⋗lf b≤x
lemma⋗≈ (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l') (≈left .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' l'≈l'' r'≈r'') = ⋗nd b≤x b''≤x'' l⋘r l''⋘r'' l≃r (lemma≈≃ (sym≈ l'≈l'') (lemma≃≈ l'≃r' r'≈r'')) (lemma⋗≈ l⋗l' l'≈l'')

lemma≈⋘ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ≈ h' → h' ⋘ h'' → h ⋘ h''
lemma≈⋘ ≈leaf lf⋘ = lf⋘
lemma≈⋘ (≈left b≤x b'≤x' l⋘r l'⋘r' l≈l' r≈r') (ll⋘ .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' l''≃r'' r'≃l'') = ll⋘ b≤x b''≤x'' l⋘r l''⋘r'' l''≃r'' (lemma≈≃ r≈r' r'≃l'')
lemma≈⋘ (≈right b≤x b'≤x' l⋙r l'⋙r' l≈l' r≈r') (lr⋘ .b'≤x' b''≤x'' .l'⋙r' l''⋘r'' l''≃r'' l'⋗l'') = lr⋘ b≤x b''≤x'' l⋙r l''⋘r'' l''≃r'' (lemma≈⋗ l≈l' l'⋗l'')

lemma⋘≈ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ⋘ h' → h' ≈ h'' → h ⋘ h''
lemma⋘≈ lf⋘ ≈leaf = lf⋘
lemma⋘≈ (ll⋘ b≤x b'≤x' l⋘r l'⋘r' l'≃r' r≃l') (≈left .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' l'≈l'' r'≈r'') = ll⋘ b≤x b''≤x'' l⋘r l''⋘r'' (lemma≈≃ (sym≈ l'≈l'') (lemma≃≈ l'≃r' r'≈r'')) (lemma≃≈ r≃l' l'≈l'')
lemma⋘≈ (lr⋘ b≤x b'≤x' l⋙r l'⋘r' l'≃r' l⋗l') (≈left .b'≤x' b''≤x'' .l'⋘r' l''⋘r'' l'≈l'' r'≈r'') = lr⋘ b≤x b''≤x'' l⋙r l''⋘r'' (lemma≈≃ (sym≈ l'≈l'') (lemma≃≈ l'≃r' r'≈r'')) (lemma⋗≈ l⋗l' l'≈l'')

lemma≈⋙ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ≈ h' → h' ⋙ h'' → h ⋙ h''
lemma≈⋙ (≈left b≤x b'≤x' lf⋘ lf⋘ ≈leaf ≈leaf) (⋙lf .b'≤x') = ⋙lf b≤x
lemma≈⋙ (≈left b≤x b'≤x' l⋘r l'⋘r' l≈l' r≈r') (⋙rl .b'≤x' b'≤x'' .l'⋘r' l'≃r' l''⋘r'' l'⋗r'') = ⋙rl b≤x b'≤x'' l⋘r (lemma≈≃ l≈l' (lemma≃≈ l'≃r' (sym≈ r≈r'))) l''⋘r'' (lemma≈⋗ l≈l' l'⋗r'')
lemma≈⋙ (≈left b≤x b'≤x' l⋘r l'⋘r' l≈l' r≈r') (⋙rr .b'≤x' b''≤x'' .l'⋘r' l'≃r' l''⋙r'' l'≃l'') = ⋙rr b≤x b''≤x'' l⋘r (lemma≈≃ l≈l' (lemma≃≈ l'≃r' (sym≈ r≈r'))) l''⋙r'' (lemma≈≃ l≈l' l'≃l'')

lemma⋙≈ : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'}{h'' : BBHeap b''} → h ⋙ h' → h' ≈ h'' → h ⋙ h''
lemma⋙≈ (⋙lf b≤x) ≈leaf = ⋙lf b≤x
lemma⋙≈ (⋙rl b≤x b'≤x' l⋘r l≃r l'⋘r' l⋗r') (≈left .b'≤x' b'≤x'' .l'⋘r' l''⋘r'' l'≈l'' r'≈r'') = ⋙rl b≤x b'≤x'' l⋘r l≃r l''⋘r'' (lemma⋗≈ l⋗r' r'≈r'')
lemma⋙≈ (⋙rr b≤x b'≤x' l⋘r l≃r l'⋙r' l≃l') (≈right .b'≤x' b''≤x'' .l'⋙r' l'⋙r'' l'≈l'' r'≈r'') = ⋙rr b≤x b''≤x'' l⋘r l≃r l'⋙r'' (lemma≃≈ l≃l' l'≈l'')
