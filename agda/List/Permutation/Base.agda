module List.Permutation.Base (A : Set) where

open import Data.List

data _/_⟶_ : List A → A → List A → Set where
  /head : {x : A}{xs : List A} 
                   →  (x ∷ xs) / x ⟶ xs
  /tail : {x y : A}{xs ys : List A} 
                   → xs / y ⟶ ys 
                   → (x ∷ xs) / y ⟶ (x ∷ ys)
            
data _∼_ : List A → List A → Set where
  ∼[] : [] ∼ []
  ∼x : {x : A}{xs ys xs' ys' : List A} 
                   → xs / x ⟶ xs' 
                   → ys / x ⟶ ys' 
                   → xs' ∼ ys' 
                   → xs ∼ ys

