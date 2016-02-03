module List.Permutation.Pair.Properties (A : Set) where

open import List.Permutation.Base A
open import List.Permutation.Base.Concatenation A
open import List.Permutation.Base.Equivalence A
open import List.Permutation.Base.Preorder A
open import List.Permutation.Pair A
open import Data.List
open import Data.Product
open import Relation.Binary.PreorderReasoning ∼-preorder
open import Algebra
open import Algebra.Structures

lemma≈∼ : {xs ys zs : List A} → xs ≈ (ys , zs) → xs ∼ (ys ++ zs)
lemma≈∼ (≈[]l zs) = refl∼ 
lemma≈∼ (≈[]r ys) rewrite ((proj₂ (IsMonoid.identity (Monoid.isMonoid (monoid A)))) ys) = refl∼
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
        ∼⟨ sym∼ (lemma≈∼ ws∼ys',zs')  ⟩
        ws
      ∎
