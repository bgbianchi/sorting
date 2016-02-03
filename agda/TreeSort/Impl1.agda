open import Relation.Binary.Core

module TreeSort.Impl1  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import BTree {A}
open import Data.List
open import Data.Sum

insert : A → BTree → BTree
insert x leaf = node x leaf leaf
insert x (node y l r) 
    with tot≤ x y
... | inj₁ x≤y = node y (insert x l) r
... | inj₂ y≤x = node y l (insert x r)

treeSort : List A → BTree
treeSort [] = leaf
treeSort (x ∷ xs) = insert x (treeSort xs)




