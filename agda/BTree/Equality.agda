module BTree.Equality {A : Set} where

open import BTree {A} 

data _≃_ : BTree → BTree → Set where
  ≃lf : leaf ≃ leaf
  ≃nd : {l r l' r' : BTree}
                    (x x' : A) 
                   → l ≃ r 
                   → l ≃ l' 
                   → l' ≃ r' 
                   → node x l r ≃ node x' l' r' 
