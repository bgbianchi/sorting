module BBHeap.Equality {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_
open import Bound.Lower A 
open import Bound.Lower.Order _≤_

data _≈_ {b b' : Bound} : BBHeap b → BBHeap b' → Set where
  ≈leaf : leaf {b} ≈ leaf {b'}
  ≈left : {x x' : A}{l r : BBHeap (val x)}{l' r' : BBHeap (val x')}
                   (b≤x : LeB b (val x))
                   (b'≤x' : LeB b' (val x'))
                   (l⋘r : l ⋘ r)
                   (l'⋘r' : l' ⋘ r')
                   → l ≈ l'
                   → r ≈ r'
                   → left b≤x l⋘r ≈ left b'≤x' l'⋘r'
  ≈right : {x x' : A}{l r : BBHeap (val x)}{l' r' : BBHeap (val x')}
                   (b≤x : LeB b (val x))
                   (b'≤x' : LeB b' (val x'))
                   (l⋙r : l ⋙ r)
                   (l'⋙r' : l' ⋙ r')
                   → l ≈ l'
                   → r ≈ r'
                   → right b≤x l⋙r ≈ right b'≤x' l'⋙r'
