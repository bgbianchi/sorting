module Bound.Lower (A : Set) where

data Bound : Set where
  bot : Bound 
  val : A → Bound


