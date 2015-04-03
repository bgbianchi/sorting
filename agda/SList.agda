{-# OPTIONS --sized-types #-}
module SList (A : Set) where

open import Data.List
open import Data.Product
open import Permutation A
open import Size

data SList : {ι : Size} → Set where
  snil : {ι : Size} 
                   → SList {↑ ι}
  _∙_ : {ι : Size}(x : A) 
                   → SList {ι} 
                   → SList {↑ ι}

size : List A → SList
size [] = snil
size (x ∷ xs) = x ∙ (size xs) 

unsize : {ι : Size} → SList {ι} → List A
unsize snil = []
unsize (x ∙ xs) = x ∷ unsize xs

unsize× : {ι : Size} → SList {ι} × SList {ι} → List A × List A
unsize× (xs , ys) = unsize xs , unsize ys

lemma-unsize-size : (xs : List A) → xs ∼ unsize (size xs)
lemma-unsize-size [] = ∼[]
lemma-unsize-size (x ∷ xs) = ∼x /head  /head (lemma-unsize-size xs)




