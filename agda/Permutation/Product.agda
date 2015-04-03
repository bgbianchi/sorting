module Permutation.Product (A : Set) where

open import Permutation A
open import Permutation.Equivalence A
open import Permutation.Preorder A
open import Permutation.Concatenation A
open import Data.List
open import Data.Product
open import Relation.Binary.PreorderReasoning ∼-preorder
open import Algebra
open import Algebra.Structures

data _≈_ : List A → List A × List A → Set where
  ≈[]r : (xs : List A) 
                   → xs ≈ (xs , [])
  ≈[]l : (xs : List A) 
                   → xs ≈ ([] , xs)
  ≈xr : {x : A}{xs ys zs : List A} 
                   → xs ≈ (ys , zs) 
                   → (x ∷ xs) ≈ (ys , x ∷ zs)
  ≈xl : {x : A}{xs ys zs : List A} 
                   → xs ≈ (ys , zs) 
                   → (x ∷ xs) ≈ (x ∷ ys , zs)

lemma≈∼ : {xs ys zs : List A} → xs ≈ (ys , zs) → xs ∼ (ys ++ zs)
lemma≈∼ (≈[]l zs) = lemma-refl∼ 
lemma≈∼ (≈[]r ys) rewrite ((proj₂ (IsMonoid.identity (Monoid.isMonoid (monoid A)))) ys) = lemma-refl∼
lemma≈∼ (≈xr {ys = ys} xs∼ys,zs') = ∼x /head (lemma++/l {xs = ys} /head) (lemma≈∼ xs∼ys,zs')
lemma≈∼ (≈xl xs∼ys',zs) = ∼x /head /head (lemma≈∼ xs∼ys',zs)

lemma≈ : {xs ys zs ws ys' zs' : List A} → xs ≈ (ys , zs) → ys ∼ ys' → zs ∼ zs' → ws ≈ (ys' , zs') → xs ∼ ws
lemma≈ {xs} {ys} {zs} {ws} {ys'} {zs'} xs∼ys,zs ys∼ys' zs∼zs' ws∼ys',zs' 
  =  begin
        xs
        ∼⟨ lemma≈∼ xs∼ys,zs  ⟩
        ys ++ zs
        ∼⟨ lemma++∼ ys∼ys' zs∼zs'  ⟩
        ys' ++ zs'
        ∼⟨ lemma-sym∼ (lemma≈∼ ws∼ys',zs')  ⟩
        ws
      ∎
