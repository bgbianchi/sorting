module BTree.Heap {A : Set}(_≤_ : A → A → Set) where

open import BTree {A}

data Heap : BTree → Set where
  leaf : Heap leaf
  left : {l r : BTree}{x y : A} 
                   → x ≤ y 
                   → Heap (node y l r) 
                   → Heap (node x (node y l r) leaf)
  right : {l r : BTree}{x y : A} 
                   → x ≤ y 
                   → Heap (node y l r) 
                   → Heap (node x leaf (node y l r))
  both : {l r l' r' : BTree}(x y y' : A) 
                   → x ≤ y 
                   → x ≤ y' 
                   → Heap (node y l r) 
                   → Heap (node y' l' r') 
                   → Heap (node x (node y l r) (node y' l' r'))
