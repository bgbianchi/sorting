module BSTree  {A : Set}(_≤_ : A → A → Set) where

open import BTree {A}

data _⊴*_ : A → BTree → Set where
  gelf : {x : A} 
                   → x ⊴* leaf
  gend : {x y : A}{l r : BTree} 
                   → x ≤ y 
                   → x ⊴* l 
                   → x ⊴* (node y l r)

data _*⊴_ : BTree → A → Set where
  lelf : {x : A} 
                   → leaf *⊴ x
  lend : {x y : A}{l r : BTree} 
                   → y ≤ x 
                   → r *⊴ x 
                   → (node y l r) *⊴ x

data BSTree : BTree → Set where
  slf : BSTree leaf
  snd : {x : A}{l r : BTree} 
                   → BSTree l 
                   → BSTree r 
                   → l *⊴ x 
                   → x ⊴* r 
                   → BSTree (node x l r) 



