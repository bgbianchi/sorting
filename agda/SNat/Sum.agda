{-# OPTIONS --sized-types #-}
module SNat.Sum where

open import Relation.Binary.PropositionalEquality
open import Size
open import SNat

+-assoc-succ : (m n : SNat) → m + succ n ≡ succ (m + n)
+-assoc-succ zero n = refl
+-assoc-succ (succ m) n rewrite +-assoc-succ m n = refl

+-assoc-right : (a b c : SNat) → (a + b) + c ≡ a + (b + c)
+-assoc-right zero b c = refl 
+-assoc-right (succ n) b c rewrite +-assoc-right n b c = refl

+-assoc-left : (a b c : SNat) → a + (b + c) ≡ (a + b) + c
+-assoc-left zero b c = refl 
+-assoc-left (succ n) b c rewrite +-assoc-left  n b c = refl

+-id : (n : SNat) → n + zero ≡ n
+-id zero = refl
+-id (succ n) rewrite +-id n = refl

+-comm : (m n : SNat) → m + n ≡ n + m
+-comm zero n rewrite +-id n = refl
+-comm (succ m) n rewrite +-assoc-succ n m | +-comm m n = refl
