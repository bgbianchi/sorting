{-# OPTIONS --sized-types #-}
module SList.Concatenation (A : Set) where

open import Data.List
open import List.Permutation.Base A
open import Size
open import SList

lemma-⊕-/ : {xs ys : List A}{x y : A} → xs / x ⟶ ys → unsize A (_⊕_ A (size A xs) (y ∙ snil)) / x ⟶ unsize A (_⊕_ A (size A ys) (y ∙ snil)) 
lemma-⊕-/ /head = /head
lemma-⊕-/ (/tail xs/x⟶xs') = /tail (lemma-⊕-/ xs/x⟶xs')

lemma-⊕∼ : {xs ys : List A}(x : A) → xs ∼ ys → (x ∷ xs) ∼ unsize A (_⊕_ A (size A ys) (x ∙ snil))
lemma-⊕∼ x ∼[] = ∼x /head /head ∼[]
lemma-⊕∼ x (∼x xs/x⟶xs' ys/x⟶ys' xs'∼ys') = ∼x (/tail xs/x⟶xs') (lemma-⊕-/ ys/x⟶ys') (lemma-⊕∼ x xs'∼ys')

lemma-size-unsize : {ι : Size}(x : A) → (xs : SList A {ι}) → (unsize A (_⊕_ A (size A (unsize A xs)) (x ∙ snil))) ∼ unsize A (_⊕_ A xs (x ∙ snil))
lemma-size-unsize x snil = ∼x /head /head ∼[]
lemma-size-unsize x (y ∙ ys) = ∼x /head  /head (lemma-size-unsize x ys)




