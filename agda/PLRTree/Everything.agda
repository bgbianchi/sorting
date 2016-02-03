open import Relation.Binary.Core

module PLRTree.Everything {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)
                  (trans≤ : Transitive _≤_) where

open import PLRTree.Complete.Correctness.Base {A}
open import PLRTree.Drop.Complete _≤_ tot≤
open import PLRTree.Drop.Heap _≤_ tot≤ trans≤
open import PLRTree.Drop.Permutation _≤_ tot≤
open import PLRTree.Heap.Correctness _≤_
open import PLRTree.Insert.Complete _≤_ tot≤
open import PLRTree.Insert.Heap _≤_ tot≤ trans≤
open import PLRTree.Insert.Permutation _≤_ tot≤
