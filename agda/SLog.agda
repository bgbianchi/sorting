{-# OPTIONS --sized-types #-}
module SLog where

open import Data.Sum renaming (_⊎_ to _∨_)
open import Size
open import SNat

log₂ : {ι : Size} → SNat {ι} → SNat {ι} 
log₂ zero = zero
log₂ (succ zero) = zero
log₂ (succ (succ n)) = succ (log₂ (succ (n /2)))

lemma-≅-log : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≅ n → log₂ m ≅ log₂ n
lemma-≅-log z≅z = z≅z
lemma-≅-log (s≅s z≅z) = z≅z
lemma-≅-log (s≅s (s≅s m≅n)) = s≅s (lemma-≅-log (s≅s (lemma-≅-/2 m≅n)))

mutual
  lemma-logn≤′logsn : {ι : Size}(n : SNat {ι}) → log₂ n ≤′ log₂ (succ n)
  lemma-logn≤′logsn zero = ≤′-eq z≅z
  lemma-logn≤′logsn (succ zero) = ≤′-step (≤′-eq z≅z)
  lemma-logn≤′logsn (succ (succ n)) = lemma-s≤′s (lemma-≤′-log (lemma-s≤′s (lemma-n/2≤′sn/2 n)))

  lemma-≤′-log : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≤′ n → log₂ m ≤′ log₂ n
  lemma-≤′-log (≤′-eq m≅n) = ≤′-eq (lemma-≅-log m≅n)
  lemma-≤′-log (≤′-step {n = n} m≤′n) = trans≤′ (lemma-≤′-log m≤′n) (lemma-logn≤′logsn n)

lemma-1+logn≤′log2n : (n : SNat) → succ (log₂ (succ n)) ≤′ log₂ (succ n + succ n)
lemma-1+logn≤′log2n zero = refl≤′
lemma-1+logn≤′log2n (succ n) rewrite +-assoc-succ (succ (succ n)) (succ n) | +-assoc-succ n (succ n) | +-assoc-succ n n = lemma-s≤′s (lemma-≤′-log (lemma-s≤′s (lemma-n+1≤′2n+2/2 n)))

lemma-log2n≤′1+logn : (n : SNat) → log₂ (n + n) ≤′ succ (log₂ n)
lemma-log2n≤′1+logn zero = ≤′-step refl≤′
lemma-log2n≤′1+logn (succ n) rewrite +-assoc-succ (succ n) n = lemma-s≤′s (lemma-≤′-log (lemma-s≤′s (lemma-2n/2≤′n n)))

