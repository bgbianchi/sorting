module BTree.Complete.Base {A : Set} where

open import BTree {A} 
open import BTree.Equality {A}

data Perfect : BTree → Set where
  plf : Perfect leaf
  p≃ : {l r : BTree}
                   (x : A)
                   → l ≃ r
                   → Perfect (node x l r)

data _⋗_ : BTree → BTree → Set where
  ⋗lf : (x : A) 
                   → node x leaf leaf ⋗ leaf
  ⋗nd : {l r' : BTree}
                   (x x' : A)
                   → (r l' : BTree) 
                   → l ⋗ r' 
                   → node x l r ⋗ node x' l' r'

data NearlyPerfect : BTree → Set where
  npr : {r : BTree}
                   (x : A)
                   (l : BTree) 
                   → NearlyPerfect r 
                   → NearlyPerfect (node x l r) 
  np⋗ : {l r : BTree}
                   (x : A)
                   → l ⋗ r
                   → NearlyPerfect (node x l r)

data _⋘_ : BTree → BTree → Set where
  eq⋘ : {l r : BTree} 
                   → l ≃ r 
                   → l ⋘ r
  gt⋘ : {l r : BTree} 
                   → NearlyPerfect l 
                   → Perfect r 
                   → l ⋗ r 
                   → l ⋘ r 

data _⋙_ : BTree → BTree → Set where
  ⋙gt : {l r : BTree} 
                   → l ⋗ r 
                   → l ⋙ r

data Complete : BTree → Set where 
  leaf : Complete leaf
  left : {l r : BTree}
                   (x : A)
                   → Complete l
                   → Complete r
                   → l ⋘ r
                   → Complete (node x l r)
  right : {l r : BTree}
                   (x : A)
                   → Complete l
                   → Complete r
                   → l ⋙ r
                   → Complete (node x l r)
