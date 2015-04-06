module PLRTree.Equality {A : Set} where

open import PLRTree {A} 

data _≃_ : PLRTree → PLRTree → Set where
  ≃lf : leaf ≃ leaf
  ≃nd : {l r l' r' : PLRTree}{t t' : Tag} 
                   (x x' : A) 
                   → l ≃ r 
                   → l ≃ l' 
                   → l' ≃ r' 
                   → node t x l r ≃ node t' x' l' r' 
