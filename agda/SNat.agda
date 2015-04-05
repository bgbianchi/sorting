{-# OPTIONS --sized-types #-}
module SNat where

open import Data.Nat hiding (_+_)
open import Size

data SNat : {ι : Size} → Set where
  zero : {ι : Size} 
                   → SNat {↑ ι}
  succ : {ι : Size} 
                   → SNat {ι} 
                   → SNat {↑ ι}

subtyping : {ι : Size} → SNat {ι} → SNat {↑ ι}
subtyping zero = zero
subtyping (succ n) = succ (subtyping n)

_/2 : {ι : Size} → SNat { ι} → SNat {ι}
zero /2 = zero
(succ zero) /2 = zero
(succ (succ n)) /2 = subtyping (succ (n /2))

log₂ : {ι : Size} → SNat {ι} → SNat {ι} 
log₂ zero = zero
log₂ (succ zero) = zero
log₂ (succ (succ n)) = succ (log₂ (succ (n /2)))

_+_ : SNat → SNat → SNat
zero + n = n
(succ m) + n = succ (m + n)

toNat : SNat → ℕ
toNat zero = zero
toNat (succ n) = suc (toNat n)
