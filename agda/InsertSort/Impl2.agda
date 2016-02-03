open import Relation.Binary.Core

module InsertSort.Impl2 {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.List
open import Data.Sum
open import OList _≤_

insert : {b : Bound}{x : A} → LeB b (val x) → OList b → OList b
insert {b} {x} b≤x onil = :< b≤x onil
insert {b} {x} b≤x (:< {x = y} b≤y ys) 
  with tot≤ x y
... | inj₁ x≤y = :< b≤x (:< (lexy x≤y) ys)
... | inj₂ y≤x = :< b≤y (insert (lexy y≤x) ys)

insertSort : List A → OList bot
insertSort [] = onil
insertSort (x ∷ xs) = insert {bot} {x} lebx (insertSort xs)
