{-# OPTIONS --sized-types #-}
module SBList {A : Set}
                  (_≤_ : A → A → Set)  
                  (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z)  where

open import Bound2 _≤_ trans≤
open import Data.List
open import Data.Product
open import Permutation A
open import Size

data SBList : {ι : Size} → Bound → Bound → Set where
  nil : {ι : Size}{b t : Bound} 
                   → LeB b t 
                   → SBList {↑ ι} b t
  cons : {ι : Size}{b t : Bound}
                   (x : A) 
                   → LeB b (val x) 
                   → LeB (val x) t 
                   → SBList {ι} b t 
                   → SBList {↑ ι} b t

bound : List A → SBList bot top
bound [] = nil lebx
bound (x ∷ xs) = cons x lebx lext (bound xs)

unbound : {b t : Bound} → SBList b t → List A
unbound (nil _) = []
unbound (cons x _ _ xs) = x ∷ unbound xs

unbound× : {ι : Size}{b t b' t' : Bound} → SBList {ι} b t × SBList {ι} b' t' → List A × List A
unbound×  (xs , ys) = (unbound xs , unbound ys)

lemma-unbound-bound : (xs : List A) → xs ∼ unbound (bound xs)
lemma-unbound-bound [] = ∼[]
lemma-unbound-bound (x ∷ xs) = ∼x /head /head (lemma-unbound-bound xs)



