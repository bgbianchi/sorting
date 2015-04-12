open import Relation.Binary.Core

module PLRTree.Heap.Properties {A : Set} 
                     (_≤_ : A → A → Set)
                     (trans≤ : Transitive _≤_) where

open import PLRTree {A} 
open import PLRTree.Heap _≤_

lemma-≤-≤* : {x y : A}{t : PLRTree} → x ≤ y → y ≤* t → x ≤* t  
lemma-≤-≤* {x = x} _ (lf≤* _) = lf≤* x
lemma-≤-≤* x≤y (nd≤* y≤z y≤*l y≤*r) = nd≤* (trans≤ x≤y y≤z) (lemma-≤-≤* x≤y y≤*l) (lemma-≤-≤* x≤y y≤*r)
