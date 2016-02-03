module BBHeap {A : Set}(_≤_ : A → A → Set) where

open import BHeap _≤_ hiding (forget ; # ; flatten)
open import Bound.Lower A 
open import Bound.Lower.Order _≤_
open import BTree {A} hiding (flatten)
open import Data.Nat
open import Data.List

mutual
  data BBHeap : Bound → Set where
    leaf : {b : Bound} → BBHeap b
    left : {b : Bound}{x : A}{l r : BBHeap (val x)} 
                   → LeB b (val x) 
                   → l ⋘ r 
                   → BBHeap b
    right : {b : Bound}{x : A}{l r : BBHeap (val x)} 
                   → LeB b (val x) 
                   → l ⋙ r 
                   → BBHeap b

  data _≃_ : {b b' : Bound} → BBHeap b → BBHeap b' → Set where
    ≃lf : {b b' : Bound} → leaf {b} ≃ leaf {b'}
    ≃nd : {b b' : Bound}{x x' : A}{l r : BBHeap (val x)}{l' r' : BBHeap (val x')}
                  → (b≤x : LeB b (val x)) 
                  → (b'≤x' : LeB b' (val x'))
                  → (l⋘r : l ⋘ r)
                  → (l'⋘r' : l' ⋘ r')
                  → l ≃ r 
                  → l' ≃ r'
                  → l ≃ l'
                  → (left b≤x l⋘r) ≃ (left b'≤x' l'⋘r')

  data _⋘_ : {b b' : Bound} → BBHeap b → BBHeap b' → Set where
    lf⋘ : {b b' : Bound}
                  → leaf {b} ⋘ leaf {b'}
    ll⋘ : {b b' : Bound}{x x' : A}{l r : BBHeap (val x)}{l' r' : BBHeap (val x')}
                  → (b≤x : LeB b (val x)) 
                  → (b'≤x' : LeB b' (val x')) 
                  → (l⋘r : l ⋘ r)
                  → (l'⋘r' : l' ⋘ r')
                  → (l'≃r' : l' ≃ r')
                  → r ≃ l'
                  → (left b≤x l⋘r) ⋘ (left b'≤x' l'⋘r')
    lr⋘ : {b b' : Bound}{x x' : A}{l r : BBHeap (val x)}{l' r' : BBHeap (val x')}
                  → (b≤x : LeB b (val x)) 
                  → (b'≤x' : LeB b' (val x')) 
                  → (l⋙r : l ⋙ r)
                  → (l'⋘r' : l' ⋘ r')
                  → (l'≃r' : l' ≃ r')
                  → l ⋗ l'
                  → (right b≤x l⋙r) ⋘ (left b'≤x' l'⋘r')

  data _⋙_ : {b b' : Bound} → BBHeap b → BBHeap b' → Set where
    ⋙lf : {b b' : Bound}{x : A}
                  → (b≤x : LeB b (val x)) 
                  → (left b≤x lf⋘) ⋙ leaf {b'}
    ⋙rl : {b b' : Bound}{x x' : A}{l r : BBHeap (val x)}{l' r' : BBHeap (val x')}
                  → (b≤x : LeB b (val x)) 
                  → (b'≤x' : LeB b' (val x')) 
                  → (l⋘r : l ⋘ r)
                  → (l≃r : l ≃ r)
                  → (l'⋘r' : l' ⋘ r')
                  → l ⋗ r'
                  → (left b≤x l⋘r) ⋙ (left b'≤x' l'⋘r')
    ⋙rr : {b b' : Bound}{x x' : A}{l r : BBHeap (val x)}{l' r' : BBHeap (val x')}
                  → (b≤x : LeB b (val x)) 
                  → (b'≤x' : LeB b' (val x')) 
                  → (l⋘r : l ⋘ r)
                  → (l≃r : l ≃ r)
                  → (l'⋙r' : l' ⋙ r')
                  →  l ≃ l'
                  → (left b≤x l⋘r) ⋙ (right b'≤x' l'⋙r')

  data _⋗_ : {b b' : Bound} → BBHeap b → BBHeap b' → Set where
    ⋗lf : {b b' : Bound}{x : A} 
                  → (b≤x : LeB b (val x)) 
                  → (left b≤x lf⋘) ⋗ (leaf {b'})
    ⋗nd : {b b' : Bound}{x x' : A}{l r : BBHeap (val x)}{l' r' : BBHeap (val x')}
                  → (b≤x : LeB b (val x)) 
                  → (b'≤x' : LeB b' (val x')) 
                  → (l⋘r : l ⋘ r)
                  → (l'⋘r' : l' ⋘ r') 
                  → l ≃ r
                  → l' ≃ r'
                  → l ⋗ l'
                  → (left b≤x l⋘r) ⋗ (left b'≤x' l'⋘r')

# : {b : Bound} → BBHeap b → ℕ
# leaf = zero
# (left {l = l} {r = r} _ _) = suc (# l + # r)
# (right {l = l} {r = r} _ _) = suc (# l + # r)

relax : {b : Bound}(h : BBHeap b) → BHeap b
relax leaf = lf
relax (left {l = l} {r = r} b≤x _) = nd b≤x (relax l) (relax r) 
relax (right {l = l} {r = r} b≤x _) = nd b≤x (relax l) (relax r)

forget : {b : Bound}(h : BBHeap b) → BTree
forget leaf = leaf
forget (left {x = x} {l = l} {r = r} _ _) = node x (forget l) (forget r)
forget (right {x = x} {l = l} {r = r} _ _) = node x (forget l) (forget r)

flatten : {b : Bound} → BBHeap b → List A
flatten leaf = []
flatten (left {x = x} {l = l} {r = r} _ _) = x ∷ flatten l ++ flatten r
flatten (right {x = x} {l = l} {r = r} _ _) = x ∷ flatten l ++ flatten r


