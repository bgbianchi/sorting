{-# OPTIONS --sized-types #-}
module SList.Properties (A : Set) where

open import Data.List
open import List.Permutation.Base A
open import SList 

lemma-unsize-size : (xs : List A) → xs ∼ unsize A (size A xs)
lemma-unsize-size [] = ∼[]
lemma-unsize-size (x ∷ xs) = ∼x /head  /head (lemma-unsize-size xs)



