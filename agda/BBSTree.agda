module BBSTree  {A : Set}(_≤_ : A → A → Set) where

open import Bound.Total A
open import Bound.Total.Order _≤_
open import Data.List
open import List.Order.Simple _≤_

data BBSTree : Bound → Bound → Set where
  bslf : {b t : Bound} 
                   → LeB b t 
                   → BBSTree b t
  bsnd : {x : A}{b t : Bound} 
                   → LeB b (val x) 
                   → LeB (val x) t 
                   → BBSTree b (val x) 
                   → BBSTree (val x) t 
                   → BBSTree b t

flatten : {b t : Bound} → BBSTree b t → List A
flatten (bslf _) = [] 
flatten (bsnd {x = x} b≤x x≤t l r) = flatten l ++ (x ∷ flatten r)
