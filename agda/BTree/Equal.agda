module BTree.Equal {A : Set} where

open import BTree {A} 

data _≃_ : BTree → BTree → Set where
  ≃leaf : leaf ≃ leaf
  ≃node : {l r l' r' : BTree}
                    (x x' : A) 
                   → l ≃ r 
                   → l ≃ l' 
                   → l' ≃ r' 
                   → node x l r ≃ node x' l' r' 
