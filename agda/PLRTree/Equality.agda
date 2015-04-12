module PLRTree.Equality {A : Set} where

open import PLRTree {A} 

data _≃_ : PLRTree → PLRTree → Set where
  ≃lf : leaf ≃ leaf
  ≃nd : {l r l' r' : PLRTree}
                   (x x' : A) 
                   → l ≃ r 
                   → l' ≃ r'
                   → l ≃ l'  
                   → node perfect x l r ≃ node perfect x' l' r' 
