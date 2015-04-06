open import Relation.Binary.Core

module PLRTree.Insert.Complete {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) where

open import PLRTree {A} 
open import PLRTree.Insert _≤_ tot≤
open import PLRTree.Complete {A}

lemma-insert-complete : {t : PLRTree}(x : A) → Complete t → Complete (insert x t)
lemma-insert-complete x t = {!!}
