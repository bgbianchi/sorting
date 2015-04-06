open import Relation.Binary.Core

module PLRTree.Insert.Heap {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) where

open import PLRTree {A} 
open import PLRTree.Insert _≤_ tot≤
open import PLRTree.Heap _≤_

lemma-insert-heap : {t : PLRTree}(x : A) → Heap t → Heap (insert x t)
lemma-insert-heap x t = {!!}
