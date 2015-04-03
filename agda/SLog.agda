{-# OPTIONS --sized-types #-}
module SLog where

open import Data.Sum renaming (_⊎_ to _∨_)
open import Relation.Binary.PropositionalEquality
open import Size
open import SNat

data _≅_ : {ι ι' : Size} → SNat {ι} → SNat {ι'} → Set where
  z≅z : {ι ι' : Size} 
                   → zero {ι} ≅ zero {ι'}
  s≅s : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} 
                   → m ≅ n 
                   → succ m ≅ succ n

trans≅ :  {ι ι' ι'' : Size}{n : SNat {ι}}{n' : SNat {ι'}}{n'' : SNat {ι''}} → n ≅ n' → n' ≅ n'' → n ≅ n''
trans≅ z≅z z≅z = z≅z
trans≅ (s≅s n≅n') (s≅s n'≅n'') = s≅s (trans≅ n≅n' n'≅n'')

data _≤′_ : {ι ι' : Size} → SNat {ι} → SNat {ι'} → Set where
  ≤′-eq : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} 
                   → m ≅ n 
                   → m ≤′ n
  ≤′-step : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} 
                   → m ≤′ n 
                   → m ≤′ succ n

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

trans≤ :  {ι ι' ι'' : Size}{n : SNat {ι}}{n' : SNat {ι'}}{n'' : SNat {ι''}} → n ≤ n' → n' ≤ n'' → n ≤ n''
trans≤ {n'' = n''} (z≤n n') _ = z≤n n''
trans≤ (s≤s n≤n') (s≤s n'≤n'') = s≤s (trans≤ n≤n' n'≤n'')

lemma-≤′-≤ : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≤′ n → m ≤ n
lemma-≤′-≤ (≤′-eq m≅n) = lemma-≅-≤ m≅n
lemma-≤′-≤ (≤′-step {n = n} m≤′n) = trans≤ (lemma-≤′-≤ m≤′n) (lemma-n≤sn n)

trans≤′ :  {ι ι' ι'' : Size}{n : SNat {ι}}{n' : SNat {ι'}}{n'' : SNat {ι''}} → n ≤′ n' → n' ≤′ n'' → n ≤′ n''
trans≤′ n≤′n' n'≤′n'' = lemma-≤-≤′ (trans≤ (lemma-≤′-≤ n≤′n') (lemma-≤′-≤ n'≤′n''))

subtyping : {ι : Size} → SNat {ι} → SNat {↑ ι}
subtyping zero = zero
subtyping (succ n) = succ (subtyping n)

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

_/2 : {ι : Size} → SNat { ι} → SNat {ι}
zero /2 = zero
(succ zero) /2 = zero
(succ (succ n)) /2 = subtyping (succ (n /2))

lemma-≅-/2 : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} → m ≅ n → m /2 ≅ n /2
lemma-≅-/2 z≅z = z≅z
lemma-≅-/2 (s≅s z≅z) = z≅z
lemma-≅-/2 (s≅s (s≅s m≅n)) = s≅s (lemma-subtyping≅subtyping  (lemma-≅-/2 m≅n)) 

lemma-n/2≤′sn/2 : {ι : Size}(n : SNat {ι}) → n /2 ≤′ (succ n) /2
lemma-n/2≤′sn/2 zero = lemma-z≤′n zero
lemma-n/2≤′sn/2 (succ zero) = lemma-z≤′n (succ zero)
lemma-n/2≤′sn/2 (succ (succ n)) = lemma-s≤′s (lemma-subtyping≤′subtyping (lemma-n/2≤′sn/2 n))

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

_+_ : SNat → SNat → SNat
zero + n = n
(succ m) + n = succ (m + n)

+-assoc-succ : (m n : SNat) → m + succ n ≡ succ (m + n)
+-assoc-succ zero n = refl
+-assoc-succ (succ m) n rewrite +-assoc-succ m n = refl

+-assoc-right : (a b c : SNat) → (a + b) + c ≡ a + (b + c)
+-assoc-right zero b c = refl 
+-assoc-right (succ n) b c rewrite +-assoc-right n b c = refl

+-assoc-left : (a b c : SNat) → a + (b + c) ≡ (a + b) + c
+-assoc-left zero b c = refl 
+-assoc-left (succ n) b c rewrite +-assoc-left  n b c = refl

+-id : (n : SNat) → n + zero ≡ n
+-id zero = refl
+-id (succ n) rewrite +-id n = refl

+-comm : (m n : SNat) → m + n ≡ n + m
+-comm zero n rewrite +-id n = refl
+-comm (succ m) n rewrite +-assoc-succ n m | +-comm m n = refl

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

refl≅ : {n : SNat} → n ≅ n
refl≅ {zero} = z≅z
refl≅ {succ _} = s≅s refl≅

refl≤ : {n : SNat} → n ≤ n
refl≤ {n} 
    with tot≤ n n
... | inj₁ n≤n = n≤n
... | inj₂ n≤n = n≤n

refl≤′ : {n : SNat} → n ≤′ n
refl≤′ = lemma-≤-≤′ refl≤

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

lemma-n+1≤′2n+2/2 : (n : SNat) → succ n ≤′ (succ (succ (n + n))) /2
lemma-n+1≤′2n+2/2 zero = refl≤′
lemma-n+1≤′2n+2/2 (succ n) rewrite +-assoc-succ (succ n) n = lemma-s≤′s (lemma-≤′subtyping (lemma-s≤′s (lemma-≤′subtyping (lemma-n≤′2n/2 n))))

lemma-1+logn≤′log2n : (n : SNat) → succ (log₂ (succ n)) ≤′ log₂ (succ n + succ n)
lemma-1+logn≤′log2n zero = refl≤′
lemma-1+logn≤′log2n (succ n) rewrite +-assoc-succ (succ (succ n)) (succ n) | +-assoc-succ n (succ n) | +-assoc-succ n n = lemma-s≤′s (lemma-≤′-log (lemma-s≤′s (lemma-n+1≤′2n+2/2 n)))

lemma-2n/2≤′n : (n : SNat) → (n + n) /2 ≤′ n
lemma-2n/2≤′n zero = refl≤′
lemma-2n/2≤′n (succ n) rewrite +-assoc-succ (succ n) n = lemma-s≤′s (lemma-subtyping≤′ (lemma-2n/2≤′n n))

lemma-log2n≤′1+logn : (n : SNat) → log₂ (n + n) ≤′ succ (log₂ n)
lemma-log2n≤′1+logn zero = ≤′-step refl≤′
lemma-log2n≤′1+logn (succ n) rewrite +-assoc-succ (succ n) n = lemma-s≤′s (lemma-≤′-log (lemma-s≤′s (lemma-2n/2≤′n n)))

