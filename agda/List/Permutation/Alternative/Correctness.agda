module List.Permutation.Alternative.Correctness (A : Set) where

open import Data.List
open import List.Permutation.Alternative A renaming (_∼_ to _∼′_)
open import List.Permutation.Base A
open import List.Permutation.Base.Equivalence A

lemma-∼′-∼ : {xs ys : List A} → xs ∼′ ys → xs ∼ ys 
lemma-∼′-∼ ∼refl = lemma-refl∼
lemma-∼′-∼ (∼trans xs∼′ys ys∼′zs) = lemma-trans∼ (lemma-∼′-∼ xs∼′ys) (lemma-∼′-∼ ys∼′zs)
lemma-∼′-∼ (∼head x xs∼′ys) = ∼x /head /head (lemma-∼′-∼ xs∼′ys)
lemma-∼′-∼ (∼swap xyxs∼′ys) = lemma-trans∼ (∼x /head (/tail /head) lemma-refl∼) (lemma-∼′-∼ xyxs∼′ys)
