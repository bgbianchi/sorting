{-# OPTIONS --sized-types #-}
module SBList.Properties {A : Set}(_≤_ : A → A → Set)   where

open import Data.List
open import List.Permutation.Base A
open import SBList _≤_

lemma-unbound-bound : (xs : List A) → xs ∼ unbound (bound xs)
lemma-unbound-bound [] = ∼[]
lemma-unbound-bound (x ∷ xs) = ∼x /head /head (lemma-unbound-bound xs)



