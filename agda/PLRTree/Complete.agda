module PLRTree.Complete {A : Set} where

open import PLRTree {A} 
open import PLRTree.Equality {A}

data Perfect : PLRTree → Set where
  plf : Perfect leaf
  p≃ : {l r : PLRTree}{t : Tag}
                   (x : A)
                   → l ≃ r
                   → Perfect (node t x l r)

data _⋗_ :  PLRTree → PLRTree → Set where
  ⋗lf : {t : Tag}
                   (x : A) 
                   → node t x leaf leaf ⋗ leaf
  ⋗nd : {l r' : PLRTree}{t t' : Tag}
                   (x x' : A)
                   → (r l' : PLRTree) 
                   → l ⋗ r' 
                   → node t x l r ⋗ node t' x' l' r'

data NearlyPerfect : PLRTree → Set where
  npr : {r : PLRTree}{t : Tag}
                   (x : A)
                   (l : PLRTree) 
                   → NearlyPerfect r 
                   → NearlyPerfect (node t x l r) 
  np⋗ : {l r : PLRTree}{t : Tag}
                   (x : A)
                   → l ⋗ r
                   → NearlyPerfect (node t x l r)

data _⋘_ : PLRTree → PLRTree → Set where
  eq⋘ : {l r : PLRTree} 
                   → l ≃ r 
                   → l ⋘ r
  gt⋘ : {l r : PLRTree} 
                   → NearlyPerfect l 
                   → Perfect r 
                   → l ⋗ r 
                   → l ⋘ r 

data _⋙_ : PLRTree → PLRTree → Set where
  ⋙gt : {l r : PLRTree} 
                   → l ⋗ r 
                   → l ⋙ r

data Complete : PLRTree → Set where 
  leaf : Complete leaf
  left : {l r : PLRTree}{t : Tag}
                   (x : A)
                   → Complete l
                   → Complete r
                   → l ⋘ r
                   → Complete (node t x l r)
  right : {l r : PLRTree}{t : Tag}
                   (x : A)
                   → Complete l
                   → Complete r
                   → l ⋙ r
                   → Complete (node t x l r)
