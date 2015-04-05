module List.Sorted  {A : Set}(_≤_ : A → A → Set) where

open import Data.List

data Sorted :  List A → Set where
  nils : Sorted []
  singls : (x : A) 
                   → Sorted [ x ]
  conss : {x y : A}{xs : List A} 
                   → x ≤ y 
                   → Sorted (y ∷ xs) 
                   → Sorted (x ∷ y ∷ xs)




