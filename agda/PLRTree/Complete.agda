module PLRTree.Complete {A : Set} where

open import PLRTree {A} 
open import PLRTree.Equality {A}

data _⋗_ :  PLRTree → PLRTree → Set where
  ⋗lf : (x : A) 
                   → node perfect x leaf leaf ⋗ leaf
  ⋗nd : {l r l' r' : PLRTree}
                   (x x' : A)
                   → l ≃ r
                   → l' ≃ r'
                   → l ⋗ l'
                   → node perfect x l r ⋗ node perfect x' l' r'

mutual
  data _⋘_ : PLRTree → PLRTree → Set where
    p⋘ : {l r : PLRTree}
                  → l ≃ r
                  → l ⋘ r
    l⋘ : {l r l' r' : PLRTree}
                  → (x x' : A)  
                  → l ⋘ r
                  → l' ≃ r'
                  → r ≃ l'
                  → (node left x l r) ⋘ (node perfect x' l' r')
    r⋘ : {l r l' r' : PLRTree}
                  → (x x' : A)  
                  → l ⋙ r
                  → l' ≃ r'
                  → l ⋗ l'
                  → (node right x l r) ⋘ (node perfect x' l' r')

  data _⋙_ : PLRTree → PLRTree → Set where
    ⋙p : {l r : PLRTree}
                  → l ⋗ r
                  → l ⋙ r
    ⋙l : {l r l' r' : PLRTree}
                  → (x x' : A) 
                  → l ≃ r
                  → l' ⋘ r'
                  → l ⋗ r'
                  → (node perfect x l r) ⋙ (node left x' l' r')
    ⋙r : {l r l' r' : PLRTree}
                  → (x x' : A) 
                  → l ≃ r
                  → l' ⋙ r'
                  → l ≃ l'
                  → (node perfect x l r) ⋙ (node right x' l' r')

data Complete : PLRTree → Set where 
  leaf : Complete leaf
  perfect : {l r : PLRTree}
                   (x : A)
                   → Complete l
                   → Complete r
                   → l ≃ r
                   → Complete (node perfect x l r)
  left : {l r : PLRTree}
                   (x : A)
                   → Complete l
                   → Complete r
                   → l ⋘ r
                   → Complete (node left x l r)
  right : {l r : PLRTree}
                   (x : A)
                   → Complete l
                   → Complete r
                   → l ⋙ r
                   → Complete (node right x l r)
