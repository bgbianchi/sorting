open import Relation.Binary.Core

module TreeSort  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import BBSTree _≤_
open import Bound.Total A 
open import Bound.Total.Order _≤_
open import BTree {A}
open import Data.List
open import Data.Sum

-- Option 1

insert : A → BTree → BTree
insert x leaf = node x leaf leaf
insert x (node y l r) 
    with tot≤ x y
... | inj₁ x≤y = node y (insert x l) r
... | inj₂ y≤x = node y l (insert x r)

treeSort : List A → BTree
treeSort [] = leaf
treeSort (x ∷ xs) = insert x (treeSort xs)

-- Option 2

insert' : {x : A}{b t : Bound} → LeB b (val x) → LeB (val x) t → BBSTree b t → BBSTree b t
insert' b≤x x≤t (bslf _)= bsnd b≤x x≤t (bslf b≤x) (bslf x≤t)
insert' {x = x} b≤x x≤t (bsnd {x = y} b≤y y≤t l r) 
    with tot≤ x y
... | inj₁ x≤y = bsnd b≤y y≤t (insert' b≤x (lexy x≤y) l) r
... | inj₂ y≤x = bsnd b≤y y≤t l (insert' (lexy y≤x) x≤t r)

treeSort' : List A → BBSTree bot top
treeSort' [] = bslf lebx
treeSort' (x ∷ xs) = insert' {x = x} lebx lext (treeSort' xs)




