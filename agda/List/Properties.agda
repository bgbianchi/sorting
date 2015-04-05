module List.Properties (A : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality 

++id : (xs : List A) → xs ++ [] ≡ xs
++id [] = refl
++id (x ∷ xs) = cong (_∷_ x) (++id xs)




