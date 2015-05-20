module List.Permutation.Alternative (A : Set) where

open import Data.List

data _∼_ : List A → List A → Set where
  ∼refl : {xs : List A} 
                   → xs ∼ xs
  ∼trans : {xs ys zs : List A} 
                   → xs ∼ ys 
                   → ys ∼ zs 
                   → xs ∼ zs
  ∼x : {xs ys : List A}(x : A) 
                   → xs ∼ ys 
                   → (x ∷ xs) ∼ (x ∷ ys)
  ∼xy : {xs ys : List A}(x y : A) 
                   → (x ∷ y ∷ xs) ∼ ys 
                   → (y ∷ x ∷ xs) ∼ ys

