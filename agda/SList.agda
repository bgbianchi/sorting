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

--

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

--

_⊕_ : SList → SList → SList
snil ⊕ ys = ys
(x ∙ xs) ⊕ ys = x ∙ (xs ⊕ ys)

lemma-⊕-/ : {xs ys : List A}{x y : A} → xs / x ⟶ ys → unsize ((size xs) ⊕ (y ∙ snil)) / x ⟶ unsize ((size ys) ⊕ (y ∙ snil)) 
lemma-⊕-/ /head = /head
lemma-⊕-/ (/tail xs/x⟶xs') = /tail (lemma-⊕-/ xs/x⟶xs')

lemma-⊕∼ : {xs ys : List A}(x : A) → xs ∼ ys → (x ∷ xs) ∼ unsize ((size ys) ⊕ (x ∙ snil))
lemma-⊕∼ x ∼[] = ∼x /head /head ∼[]
lemma-⊕∼ x (∼x xs/x⟶xs' ys/x⟶ys' xs'∼ys') = ∼x (/tail xs/x⟶xs') (lemma-⊕-/ ys/x⟶ys') (lemma-⊕∼ x xs'∼ys')

lemma-size-unsize : {ι : Size}(x : A) → (xs : SList {ι}) → (unsize (size (unsize xs) ⊕ (x ∙ snil))) ∼ unsize (xs ⊕ (x ∙ snil))
lemma-size-unsize x snil = ∼x /head /head ∼[]
lemma-size-unsize x (y ∙ ys) = ∼x /head  /head (lemma-size-unsize x ys)




