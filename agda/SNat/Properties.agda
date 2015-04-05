{-# OPTIONS --sized-types #-}
module SNat.Properties where

open import Size
open import SNat
open import SNat.Order
open import SNat.Order.Properties
open import SNat.Sum

lemma-≅subtyping : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≅ n → m ≅ subtyping n
lemma-≅subtyping z≅z = z≅z
lemma-≅subtyping (s≅s m≅n) = s≅s (lemma-≅subtyping m≅n)

lemma-subtyping≅ : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≅ n → subtyping m ≅ n
lemma-subtyping≅ z≅z = z≅z
lemma-subtyping≅ (s≅s m≅n) = s≅s (lemma-subtyping≅ m≅n)

lemma-subtyping≅subtyping : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≅ n → subtyping m ≅ subtyping n
lemma-subtyping≅subtyping z≅z = z≅z
lemma-subtyping≅subtyping (s≅s m≅n) = s≅s (lemma-subtyping≅subtyping m≅n)

lemma-≤′subtyping : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≤′ n → m ≤′ subtyping n
lemma-≤′subtyping (≤′-eq m≅n) = ≤′-eq (lemma-≅subtyping m≅n)
lemma-≤′subtyping (≤′-step m≤′n) = ≤′-step (lemma-≤′subtyping m≤′n)

lemma-subtyping≤′ : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≤′ n → subtyping m ≤′ n
lemma-subtyping≤′ (≤′-eq m≅n) = ≤′-eq (lemma-subtyping≅ m≅n)
lemma-subtyping≤′ (≤′-step m≤′n) = ≤′-step (lemma-subtyping≤′ m≤′n)

lemma-subtyping≤subtyping : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≤ n → subtyping m ≤ subtyping n
lemma-subtyping≤subtyping (z≤n n) = z≤n (subtyping n)
lemma-subtyping≤subtyping (s≤s m≤n) = s≤s (lemma-subtyping≤subtyping m≤n)

lemma-subtyping≤′subtyping : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≤′ n → subtyping m ≤′ subtyping n
lemma-subtyping≤′subtyping m≤′n = lemma-≤-≤′ (lemma-subtyping≤subtyping (lemma-≤′-≤ m≤′n))

--

lemma-≅-/2 : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≅ n → m /2 ≅ n /2
lemma-≅-/2 z≅z = z≅z
lemma-≅-/2 (s≅s z≅z) = z≅z
lemma-≅-/2 (s≅s (s≅s m≅n)) = s≅s (lemma-subtyping≅subtyping  (lemma-≅-/2 m≅n)) 

lemma-n/2≤′sn/2 : {ι : Size}(n : SNat {ι}) → n /2 ≤′ (succ n) /2
lemma-n/2≤′sn/2 zero = lemma-z≤′n zero
lemma-n/2≤′sn/2 (succ zero) = lemma-z≤′n (succ zero)
lemma-n/2≤′sn/2 (succ (succ n)) = lemma-s≤′s (lemma-subtyping≤′subtyping (lemma-n/2≤′sn/2 n))

--

lemma-m≤′m+n : (m n : SNat) → m ≤′ (m + n)
lemma-m≤′m+n zero n = lemma-z≤′n n
lemma-m≤′m+n (succ m) n = lemma-s≤′s (lemma-m≤′m+n m n)

lemma-2m≤′m+n+m+n : (m n : SNat) → (m + m) ≤′ ((m + n) + (m + n))
lemma-2m≤′m+n+m+n m n rewrite +-assoc-left (m + n) m n | +-comm (m + n) m | +-assoc-left m m n | +-assoc-right (m + m) n n = lemma-m≤′m+n (m + m) (n + n)

lemma-2m≅2n : {m n : SNat} → m ≅ n →  (m + m) ≅ (n + n)
lemma-2m≅2n z≅z = z≅z
lemma-2m≅2n (s≅s {m = m} {n = n} m≅n) rewrite +-assoc-succ m m | +-assoc-succ n n = s≅s (s≅s (lemma-2m≅2n m≅n))

lemma-2m≤′2n : {m n : SNat} → m ≤′ n →  (m + m) ≤′ (n + n)
lemma-2m≤′2n (≤′-eq m≅n) = ≤′-eq (lemma-2m≅2n m≅n)
lemma-2m≤′2n (≤′-step {n = n} m≤′n) rewrite +-assoc-succ n n = ≤′-step (≤′-step (lemma-2m≤′2n m≤′n))

lemma-n≤′2n : (n : SNat) → n ≤′ (n + n)
lemma-n≤′2n n = lemma-m≤′m+n n n

+-right-monotony-≅ : {m n : SNat}(k : SNat) → m ≅ n → (m + k) ≅ (n + k)
+-right-monotony-≅ k z≅z = refl≅
+-right-monotony-≅ k (s≅s m≅n) = s≅s (+-right-monotony-≅ k m≅n)

+-right-monotony-≤′ : {m n : SNat}(k : SNat) → m ≤′ n → (m + k) ≤′ (n + k)
+-right-monotony-≤′ k (≤′-eq m≅n) = ≤′-eq (+-right-monotony-≅ k m≅n)
+-right-monotony-≤′ k (≤′-step m≤′n) = ≤′-step (+-right-monotony-≤′ k m≤′n)

+-left-monotony-≤′ : {m n : SNat}(k : SNat) → m ≤′ n → (k + m) ≤′ (k + n)
+-left-monotony-≤′ {m} {n} k m≤′n rewrite +-comm k m | +-comm k n = +-right-monotony-≤′ k m≤′n

lemma-4m≤′n+m+n+m : {m n : SNat} → m ≤′ n → ((m + m) + (m + m)) ≤′ ((n + m) + (n + m))
lemma-4m≤′n+m+n+m {m} {n} m≤′n rewrite +-comm n m = lemma-2m≤′2n (+-left-monotony-≤′ m m≤′n)

lemma-n≤′2n/2 : (n : SNat) → n ≤′ (n + n) /2
lemma-n≤′2n/2 zero = ≤′-eq z≅z
lemma-n≤′2n/2 (succ n) rewrite +-assoc-succ (succ n) n = lemma-s≤′s (lemma-≤′subtyping (lemma-n≤′2n/2 n))

lemma-2n/2≤′n : (n : SNat) → (n + n) /2 ≤′ n
lemma-2n/2≤′n zero = refl≤′
lemma-2n/2≤′n (succ n) rewrite +-assoc-succ (succ n) n = lemma-s≤′s (lemma-subtyping≤′ (lemma-2n/2≤′n n))

lemma-n+1≤′2n+2/2 : (n : SNat) → succ n ≤′ (succ (succ (n + n))) /2
lemma-n+1≤′2n+2/2 zero = refl≤′
lemma-n+1≤′2n+2/2 (succ n) rewrite +-assoc-succ (succ n) n = lemma-s≤′s (lemma-≤′subtyping (lemma-s≤′s (lemma-≤′subtyping (lemma-n≤′2n/2 n))))
