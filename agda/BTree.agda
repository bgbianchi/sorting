module BTree {A : Set} where

open import Data.List

data BTree : Set where
  leaf : BTree 
  node : A → BTree → BTree → BTree

flatten : BTree → List A
flatten leaf = []
flatten (node x l r) = (flatten l) ++ (x ∷ flatten r) 


