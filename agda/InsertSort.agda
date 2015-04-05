open import Relation.Binary.Core

module InsertSort {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.List
open import Data.Sum
open import OList _≤_

-- Option 1

insert : A → List A → List A
insert x [] = [ x ]
insert x (y ∷ ys) 
    with tot≤ x y
... | inj₁ _ = x ∷ y ∷ ys
... | inj₂ _ = y ∷ insert x ys

insertSort : List A → List A
insertSort = foldr insert []

-- Option 2

insert' : { b : Bound} → (x : A) → LeB b (val x) → OList b → OList b
insert' x b≤x onil = :< b≤x onil
insert' x b≤x (:< {x = y} b≤y ys) 
    with tot≤ x y
... | inj₁ x≤y = :< b≤x (:< (lexy x≤y) ys)
... | inj₂ y≤x = :< b≤y (insert' x (lexy y≤x) ys)

insertSort' : List A → OList bot
insertSort' [] = onil
insertSort' (x ∷ xs) = insert' x lebx (insertSort' xs)
