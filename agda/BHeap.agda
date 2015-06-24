module BHeap {A : Set}(_≤_ : A → A → Set) where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import BTree {A} hiding (flatten)
open import Data.Nat hiding (_≤_)
open import Data.List
open import Data.Sum renaming (_⊎_ to _∨_)
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding (trans)

open DecTotalOrder decTotalOrder hiding (refl ; _≤_)

data BHeap : Bound → Set where
  lf : {b : Bound} 
                   → BHeap b
  nd : {b : Bound}{x : A} 
                   → LeB b (val x) 
                   → (l r : BHeap (val x)) 
                   → BHeap b

forget : {b : Bound} → BHeap b → BTree
forget lf = leaf
forget (nd {x = x} _ l r) = node x (forget l) (forget r)

# : {b : Bound} → BHeap b → ℕ
# lf = zero
# (nd _ l r) = suc (# l + # r)

height : {b : Bound} → BHeap b → ℕ
height lf = zero
height (nd _ l r) 
    with total (height l) (height r) 
... | inj₁ hl≤hr = suc (height r)
... | inj₂ hr≤hl = suc (height l)

merge : {b : Bound} → Total _≤_ → (l r : BHeap b) → BHeap b
merge _ lf r = r
merge _ l lf = l
merge tot≤ (nd {x = x} b≤x l r) (nd {x = x'} b≤x' l' r') 
    with tot≤ x x'
... | inj₁ x≤x' = nd b≤x (merge tot≤ l r) (nd (lexy x≤x') l' r') 
... | inj₂ x'≤x = nd b≤x' (nd (lexy x'≤x) l r) (merge tot≤ l' r')

flatten : {b : Bound}(h : BHeap b) → List A
flatten lf = []
flatten (nd {x = x} b≤x l r) = x ∷ (flatten l ++ flatten r)

