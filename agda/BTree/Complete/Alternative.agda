module BTree.Complete.Alternative {A : Set} where

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

