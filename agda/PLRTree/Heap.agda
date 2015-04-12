module PLRTree.Heap {A : Set}(_≤_ : A → A → Set) where

open import PLRTree {A}

data _≤*_ : A → PLRTree → Set where
  lf≤* : (x : A) 
                   → x ≤* leaf
  nd≤* : {t : Tag}{x y : A}{l r : PLRTree}
                   → x ≤ y 
                   → x ≤* l
                   → x ≤* r
                   → x ≤* node t y l r

data Heap : PLRTree → Set where
  leaf : Heap leaf
  node : {t : Tag}{x : A}{l r : PLRTree} 
                   → x ≤* l 
                   → x ≤* r 
                   → Heap l 
                   → Heap r 
                   → Heap (node t x l r) 
