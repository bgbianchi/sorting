{-# OPTIONS --sized-types #-}
module SNat.Order.Properties where

open import Data.Sum renaming (_⊎_ to _∨_)
open import Relation.Binary.PropositionalEquality
open import Size
open import SNat
open import SNat.Order

tot≤ : {ι ι' : Size} → (m : SNat {ι}) → (n : SNat {ι'}) → m ≤ n ∨ n ≤ m
tot≤ zero n = inj₁ (z≤n n)
tot≤ m zero = inj₂ (z≤n m)
tot≤ (succ m) (succ n) 
   with tot≤ m n
...| inj₁ m≤n = inj₁ (s≤s m≤n)
...| inj₂ n≤m = inj₂ (s≤s n≤m)

refl≤ : {n : SNat} → n ≤ n
refl≤ {n} 
    with tot≤ n n
... | inj₁ n≤n = n≤n
... | inj₂ n≤n = n≤n

trans≤ :  {ι ι' ι'' : Size}{n : SNat {ι}}{n' : SNat {ι'}}{n'' : SNat {ι''}} → n ≤ n' → n' ≤ n'' → n ≤ n''
trans≤ {n'' = n''} (z≤n n') _ = z≤n n''
trans≤ (s≤s n≤n') (s≤s n'≤n'') = s≤s (trans≤ n≤n' n'≤n'')

refl≅ : {n : SNat} → n ≅ n
refl≅ {zero} = z≅z
refl≅ {succ _} = s≅s refl≅

trans≅ :  {ι ι' ι'' : Size}{n : SNat {ι}}{n' : SNat {ι'}}{n'' : SNat {ι''}} → n ≅ n' → n' ≅ n'' → n ≅ n''
trans≅ z≅z z≅z = z≅z
trans≅ (s≅s n≅n') (s≅s n'≅n'') = s≅s (trans≅ n≅n' n'≅n'')

lemma-z≤′n : {ι ι' : Size}(n : SNat {ι}) → zero {ι'} ≤′ n
lemma-z≤′n zero = ≤′-eq z≅z
lemma-z≤′n (succ n) = ≤′-step (lemma-z≤′n n)

lemma-s≤′s : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≤′ n → succ m ≤′ succ n
lemma-s≤′s (≤′-eq m≅n) = ≤′-eq (s≅s m≅n)
lemma-s≤′s (≤′-step m≤′n) = ≤′-step (lemma-s≤′s m≤′n)

lemma-≤-≤′ : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≤ n → m ≤′ n
lemma-≤-≤′ (z≤n n) = lemma-z≤′n n
lemma-≤-≤′ (s≤s m≤n) = lemma-s≤′s (lemma-≤-≤′ m≤n)

lemma-≅-≤ : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≅ n → m ≤ n
lemma-≅-≤ z≅z = z≤n zero
lemma-≅-≤ (s≅s m≅n) = s≤s (lemma-≅-≤ m≅n)
           
lemma-≡-≤′ : {a b c : SNat} → b ≡ a → a ≤′ c → b ≤′ c
lemma-≡-≤′ b≡a a≤′c rewrite b≡a = a≤′c

lemma-n≤sn : {ι : Size}(n : SNat {ι}) → n ≤ succ n
lemma-n≤sn zero = z≤n (succ zero)
lemma-n≤sn (succ n) = s≤s (lemma-n≤sn n)

lemma-≤′-≤ : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≤′ n → m ≤ n
lemma-≤′-≤ (≤′-eq m≅n) = lemma-≅-≤ m≅n
lemma-≤′-≤ (≤′-step {n = n} m≤′n) = trans≤ (lemma-≤′-≤ m≤′n) (lemma-n≤sn n)

refl≤′ : {n : SNat} → n ≤′ n
refl≤′ = lemma-≤-≤′ refl≤

trans≤′ :  {ι ι' ι'' : Size}{n : SNat {ι}}{n' : SNat {ι'}}{n'' : SNat {ι''}} → n ≤′ n' → n' ≤′ n'' → n ≤′ n''
trans≤′ n≤′n' n'≤′n'' = lemma-≤-≤′ (trans≤ (lemma-≤′-≤ n≤′n') (lemma-≤′-≤ n'≤′n''))
