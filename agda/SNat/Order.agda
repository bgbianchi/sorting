{-# OPTIONS --sized-types #-}
module SNat.Order where

open import Size
open import SNat

data _≤_ : {ι ι' : Size} → SNat {ι} → SNat {ι'} → Set where
  z≤n : {ι ι' : Size} 
                   → (n : SNat {ι'}) 
                   →  _≤_ (zero {ι}) n
  s≤s : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} 
                   → m ≤ n 
                   → (succ m) ≤ (succ n)

data _≅_ : {ι ι' : Size} → SNat {ι} → SNat {ι'} → Set where
  z≅z : {ι ι' : Size} 
                   → zero {ι} ≅ zero {ι'}
  s≅s : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} 
                   → m ≅ n 
                   → succ m ≅ succ n

data _≤′_ : {ι ι' : Size} → SNat {ι} → SNat {ι'} → Set where
  ≤′-eq : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} 
                   → m ≅ n 
                   → m ≤′ n
  ≤′-step : {ι ι' : Size}{m : SNat {ι}}{n : SNat {ι'}} 
                   → m ≤′ n 
                   → m ≤′ succ n
