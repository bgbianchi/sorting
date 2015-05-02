open import Relation.Binary.Core

module PLRTree.Order {A : Set} where

open import Data.Nat
open import Data.Sum
open import PLRTree {A}
open import Relation.Binary

open DecTotalOrder decTotalOrder hiding (refl)

height : PLRTree → ℕ
height leaf = zero
height (node t x l r) 
    with total (height l) (height r)
... | inj₁ hl≤hr = suc (height r)
... | inj₂ hr≤hl = suc (height l)

_≺_ : PLRTree → PLRTree → Set 
t ≺ t' = height t <′ height t'
