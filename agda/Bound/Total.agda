module Bound.Total (A : Set) where

open import Data.List

data Bound : Set where
  bot : Bound 
  val : A → Bound
  top : Bound
