module List.Permutation.Pair (A : Set) where

open import List.Permutation A
open import Data.List
open import Data.Product

data _≈_ : List A → List A × List A → Set where
  ≈[]r : (xs : List A) 
                   → xs ≈ (xs , [])
  ≈[]l : (xs : List A) 
                   → xs ≈ ([] , xs)
  ≈xr : {x : A}{xs ys zs : List A} 
                   → xs ≈ (ys , zs) 
                   → (x ∷ xs) ≈ (ys , x ∷ zs)
  ≈xl : {x : A}{xs ys zs : List A} 
                   → xs ≈ (ys , zs) 
                   → (x ∷ xs) ≈ (x ∷ ys , zs)

