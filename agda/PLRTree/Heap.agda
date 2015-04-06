module PLRTree.Heap {A : Set}(_≤_ : A → A → Set) where

open import PLRTree {A}

data Heap : PLRTree → Set where
  leaf : Heap leaf
  single : {t : Tag}
                   (x : A) 
                   → Heap (node t x leaf leaf)
  left : {l r : PLRTree}{x y : A}{t t' : Tag}
                   → x ≤ y 
                   → Heap (node t y l r) 
                   → Heap (node t' x (node t y l r) leaf)
  right : {l r : PLRTree}{x y : A}{t t' : Tag}
                   → x ≤ y 
                   → Heap (node t y l r) 
                   → Heap (node t' x leaf (node t y l r))
  both : {l r l' r' : PLRTree}{x y y' : A}{t t' t'' : Tag}
                   → x ≤ y 
                   → x ≤ y' 
                   → Heap (node t y l r) 
                   → Heap (node t' y' l' r') 
                   → Heap (node t'' x (node t y l r) (node t' y' l' r'))
