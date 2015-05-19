module PLRTree {A : Set} where

open import BTree {A} hiding (flatten)
open import Data.List

data Tag : Set where
  perfect : Tag
  left : Tag
  right : Tag

data PLRTree : Set where
  leaf : PLRTree 
  node : Tag → A → PLRTree → PLRTree → PLRTree

forget : PLRTree → BTree
forget leaf = leaf
forget (node _ x l r) = node x (forget l) (forget r)

flatten : PLRTree → List A
flatten leaf = []
flatten (node _ x l r) = x ∷ flatten l ++ flatten r
