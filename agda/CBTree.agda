module CBTree {A : Set} where

open import BTree {A}
open import BTree.Equality {A}

data _⋗_ : BTree → BTree → Set where
  ⋗lf : (x : A) 
                → (node x leaf leaf) ⋗ leaf
  ⋗nd : {l r l' r' : BTree}
                → (x x' : A)  
                → l ≃ r
                → l' ≃ r'
                → l ⋗ l'
                → (node x l r) ⋗ (node x' l' r')

mutual
  data _⋘_ : BTree → BTree → Set where
    lf⋘ : leaf ⋘ leaf
    ll⋘ : {l r l' r' : BTree}
                  → (x x' : A)  
                  → (l⋘r : l ⋘ r)
                  → (l'≃r' : l' ≃ r')
                  → r ≃ l'
                  → (node x l r) ⋘ (node x' l' r')
    lr⋘ : {l r l' r' : BTree}
                  → (x x' : A)  
                  → (l⋙r : l ⋙ r)
                  → (l'≃r' : l' ≃ r')
                  → l ⋗ l'
                  → (node x l r) ⋘ (node x' l' r')

  data _⋙_ : BTree → BTree → Set where
    ⋙lf : (x : A)
                  → (node x leaf leaf) ⋙ leaf
    ⋙rl : {l r l' r' : BTree}
                  → (x x' : A) 
                  → (l≃r : l ≃ r)
                  → (l'⋘r' : l' ⋘ r')
                  → l ⋗ r'
                  → (node x l r) ⋙ (node x' l' r')
    ⋙rr : {l r l' r' : BTree}
                  → (x x' : A) 
                  → (l≃r : l ≃ r)
                  → (l'⋙r' : l' ⋙ r')
                  →  l ≃ l'
                  → (node x l r) ⋙ (node x' l' r')

data CBTree : BTree → Set where
  leaf : CBTree leaf
  left : {l r : BTree} 
                 (x : A)
                 → CBTree l
                 → CBTree r
                 → l ⋘ r 
                 → CBTree (node x l r)
  right : {l r : BTree}
                 (x : A)
                 → CBTree l
                 → CBTree r
                 → l ⋙ r 
                 → CBTree (node x l r)

