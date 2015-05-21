module LRTree {A : Set} where

open import Data.List

data Tag : Set where
  left : Tag
  right : Tag

data LRTree : Set where
  empty : LRTree
  leaf : A → LRTree
  node : Tag → LRTree → LRTree → LRTree

insert : A → LRTree → LRTree
insert x empty = leaf x
insert x (leaf y) = node left (leaf y) (leaf x)
insert x (node left l r) = node right (insert x l) r
insert x (node right l r) = node left l (insert x r)

flatten : LRTree → List A
flatten empty = []
flatten (leaf x) = x ∷ []
flatten (node _ l r) = flatten l ++ flatten r
