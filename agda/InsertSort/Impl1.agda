open import Relation.Binary.Core

module InsertSort.Impl1 {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.List
open import Data.Sum

insert : A → List A → List A
insert x [] = [ x ]
insert x (y ∷ ys) 
    with tot≤ x y
... | inj₁ _ = x ∷ y ∷ ys
... | inj₂ _ = y ∷ insert x ys

insertSort : List A → List A
insertSort = foldr insert []
