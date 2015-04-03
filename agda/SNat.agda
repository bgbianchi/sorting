{-# OPTIONS --sized-types #-}
module SNat where

open import Data.Sum renaming (_⊎_ to _∨_)
open import Size

data SNat : {ι : Size} → Set where
  zero : {ι : Size} 
                   → SNat {↑ ι}
  succ : {ι : Size} 
                   → SNat {ι} 
                   → SNat {↑ ι}

sub : {ι : Size} → SNat {ι} → SNat → SNat {ι}
sub zero n = zero
sub m zero = m
sub (succ m) (succ n) = sub m n 

div : {ι : Size} → SNat {ι} → SNat → SNat {ι}
div  zero n = zero
div  (succ m) n = succ (div (sub m n) n)

data _≤_ : {ι ι' : Size} → SNat {ι} → SNat {ι'} → Set where
  z≤n : {ι ι' : Size} 
                   → (n : SNat {ι'}) 
                   →  _≤_ (zero {ι}) n
  s≤s : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} 
                   → m ≤ n 
                   → (succ m) ≤ (succ n)

tot≤ : {ι ι' : Size} → (m : SNat {ι}) → (n : SNat {ι'}) → m ≤ n ∨ n ≤ m
tot≤ zero n = inj₁ (z≤n n)
tot≤ m zero = inj₂ (z≤n m)
tot≤ (succ m) (succ n) 
   with tot≤ m n
...| inj₁ m≤n = inj₁ (s≤s m≤n)
...| inj₂ n≤m = inj₂ (s≤s n≤m)

gcd : {ι ι' : Size} → SNat {ι} → SNat {ι'} → SNat {ι} ∨ SNat {ι'}
gcd zero n  =  inj₂ n
gcd m zero =  inj₁ m
gcd (succ m) (succ n) 
   with tot≤ m n
...| inj₁ m≤n = gcd (succ m) (sub n m)
...| inj₂ n≤m = gcd (sub m n) (succ n)
