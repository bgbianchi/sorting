open import Relation.Binary.Core

module PLRTree.Insert.Heap {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) 
                     (trans≤ : Transitive _≤_) where

open import Data.Sum
open import Order.Total _≤_ tot≤
open import PLRTree {A} 
open import PLRTree.Insert _≤_ tot≤
open import PLRTree.Insert.Properties _≤_ tot≤
open import PLRTree.Heap _≤_
open import PLRTree.Heap.Properties _≤_ trans≤

lemma-insert-≤* : {x y : A}{t : PLRTree} → x ≤ y → x ≤* t → x ≤* insert y t
lemma-insert-≤* {y = y} x≤y (lf≤* x) = nd≤* x≤y (lf≤* x) (lf≤* x)
lemma-insert-≤* {y = y} x≤y (nd≤* {perfect} {x} {z} {l} {r} x≤z x≤*l x≤*r) 
    with tot≤ y z | l | r
... | inj₁ y≤z | leaf | leaf = nd≤* x≤y (nd≤* x≤z x≤*r x≤*r) x≤*r
... | inj₁ y≤z | node _ _ _ _ | leaf = nd≤* x≤y (lemma-insert-≤* x≤z x≤*l) x≤*r
... | inj₁ y≤z | leaf | node _ _ _ _ = nd≤* x≤y (nd≤* x≤z x≤*l x≤*l) x≤*r
... | inj₁ y≤z | node _ _ _ _ | node _ _ _ _ = nd≤* x≤y (lemma-insert-≤* x≤z x≤*l) x≤*r
... | inj₂ z≤y | leaf | leaf = nd≤* x≤z (nd≤* x≤y x≤*r x≤*r) x≤*r
... | inj₂ z≤y | node _ _ _ _ | leaf = nd≤* x≤z (lemma-insert-≤* x≤y x≤*l) x≤*r
... | inj₂ z≤y | leaf | node _ _ _ _ = nd≤* x≤z (nd≤* x≤y x≤*l x≤*l) x≤*r
... | inj₂ z≤y | node _ _ _ _ | node _ _ _ _ = nd≤* x≤z (lemma-insert-≤* x≤y x≤*l) x≤*r
lemma-insert-≤* {y = y} x≤y (nd≤* {left} {x} {z} {l} {r} x≤z x≤*l x≤*r) 
    with tot≤ y z 
... | inj₁ y≤z 
    with insert z l | lemma-insert-≤* (trans≤ x≤y y≤z) x≤*l | lemma-insert-compound z l
... | node perfect z' l' r' | x≤*lᵢ | compound = nd≤* x≤y x≤*lᵢ x≤*r
... | node right z' l' r' | x≤*lᵢ | compound = nd≤* x≤y x≤*lᵢ x≤*r
... | node left z' l' r' | x≤*lᵢ | compound = nd≤* x≤y x≤*lᵢ x≤*r
lemma-insert-≤* {y = y} x≤y (nd≤* {left} {x} {z} {l} {r} x≤z x≤*l x≤*r) | inj₂ z≤y 
    with insert y l  | lemma-insert-≤* x≤y x≤*l | lemma-insert-compound y l
... | node perfect y' l' r' | x≤*lᵢ | compound = nd≤* x≤z x≤*lᵢ x≤*r
... | node right y' l' r' | x≤*lᵢ | compound = nd≤* x≤z x≤*lᵢ x≤*r
... | node left y' l' r' | x≤*lᵢ | compound = nd≤* x≤z x≤*lᵢ x≤*r
lemma-insert-≤* {y = y} x≤y (nd≤* {right} {x} {z} {l} {r} x≤z x≤*l x≤*r) 
    with tot≤ y z 
... | inj₁ y≤z 
    with insert z r | lemma-insert-≤* (trans≤ x≤y y≤z) x≤*r | lemma-insert-compound z r
... | node perfect z' l' r' | x≤*rᵢ | compound = nd≤* x≤y x≤*l x≤*rᵢ
... | node right z' l' r' | x≤*rᵢ | compound = nd≤* x≤y x≤*l x≤*rᵢ
... | node left z' l' r' | x≤*rᵢ | compound = nd≤* x≤y x≤*l x≤*rᵢ
lemma-insert-≤* {y = y} x≤y (nd≤* {right} {x} {z} {l} {r} x≤z x≤*l x≤*r) | inj₂ z≤y 
    with insert y r  | lemma-insert-≤* x≤y x≤*r | lemma-insert-compound y r
... | node perfect y' l' r' | x≤*rᵢ | compound = nd≤* x≤z x≤*l x≤*rᵢ
... | node right y' l' r' | x≤*rᵢ | compound = nd≤* x≤z x≤*l x≤*rᵢ
... | node left y' l' r' | x≤*rᵢ | compound = nd≤* x≤z x≤*l x≤*rᵢ

lemma-insert-≤*' : {x y : A}{t : PLRTree} → x ≤ y → y ≤* t → x ≤* insert y t
lemma-insert-≤*' x≤y y≤*t = lemma-≤-≤* x≤y (lemma-insert-≤* refl≤ y≤*t)

lemma-insert-heap : {t : PLRTree}(x : A) → Heap t → Heap (insert x t)
lemma-insert-heap x leaf = node (lf≤* x) (lf≤* x) leaf leaf
lemma-insert-heap x (node {perfect} {y} {l} {r} y≤*l y≤*r hl hr) 
    with tot≤ x y | l | r
... | inj₁ x≤y | leaf | leaf = node (nd≤* x≤y (lf≤* x) (lf≤* x)) (lf≤* x) (node (lf≤* y) (lf≤* y) leaf leaf) leaf
... | inj₁ x≤y | node _ _ _ _ | leaf = node (lemma-insert-≤*' x≤y y≤*l) (lf≤* x) (lemma-insert-heap y hl) hr
... | inj₁ x≤y | leaf | node _ _ _ _ = node (nd≤* x≤y (lf≤* x) (lf≤* x)) (lemma-≤-≤* x≤y y≤*r) (node y≤*l y≤*l hl hl) hr
... | inj₁ x≤y | node _ _ _ _ | node _ _ _ _ = node (lemma-insert-≤*' x≤y y≤*l) (lemma-≤-≤* x≤y y≤*r) (lemma-insert-heap y hl) hr
... | inj₂ y≤x | leaf | leaf = node (nd≤* y≤x (lf≤* y) (lf≤* y)) (lf≤* y) (node (lf≤* x) (lf≤* x) leaf leaf) leaf
... | inj₂ y≤x | node _ _ _ _ | leaf = node (lemma-insert-≤* y≤x y≤*l) y≤*r (lemma-insert-heap x hl) hr
... | inj₂ y≤x | leaf | node _ _ _ _ = node (nd≤* y≤x y≤*l y≤*l) y≤*r (lemma-insert-heap x hl) hr
... | inj₂ y≤x | node _ _ _ _ | node _ _ _ _ = node (lemma-insert-≤* y≤x y≤*l) y≤*r (lemma-insert-heap x hl) hr
lemma-insert-heap x (node {left} {y} {l} {r} y≤*l y≤*r hl hr) 
    with tot≤ x y 
... | inj₁ x≤y 
    with insert y l | lemma-insert-heap y hl | lemma-insert-≤*' x≤y y≤*l | lemma-insert-compound y l
... | node perfect y' l' r' | hlᵢ | x≤*lᵢ | compound = node x≤*lᵢ (lemma-≤-≤* x≤y y≤*r) hlᵢ hr
... | node right y' l' r' | hlᵢ | x≤*lᵢ | compound = node x≤*lᵢ (lemma-≤-≤* x≤y y≤*r) hlᵢ hr
... | node left y' l' r' | hlᵢ | x≤*lᵢ | compound = node x≤*lᵢ (lemma-≤-≤* x≤y y≤*r) hlᵢ hr
lemma-insert-heap x (node {left} {y} {l} {r} y≤*l y≤*r hl hr) | inj₂ y≤x 
    with insert x l  | lemma-insert-heap x hl | lemma-insert-≤* y≤x y≤*l | lemma-insert-compound x l
... | node perfect y' l' r' | hlᵢ | y≤*lᵢ | compound = node y≤*lᵢ y≤*r hlᵢ hr
... | node right y' l' r' | hlᵢ | y≤*lᵢ | compound = node y≤*lᵢ y≤*r hlᵢ hr
... | node left y' l' r' | hlᵢ | y≤*lᵢ | compound = node y≤*lᵢ y≤*r hlᵢ hr
lemma-insert-heap x (node {right} {y} {l} {r} y≤*l y≤*r hl hr) 
    with tot≤ x y
... | inj₁ x≤y 
    with insert y r | lemma-insert-heap y hr | lemma-insert-≤*' x≤y y≤*r | lemma-insert-compound y r
... | node perfect y' l' r' | hrᵢ | x≤*rᵢ | compound = node (lemma-≤-≤* x≤y y≤*l) x≤*rᵢ hl hrᵢ
... | node right y' l' r' | hrᵢ | x≤*rᵢ | compound = node (lemma-≤-≤* x≤y y≤*l) x≤*rᵢ hl hrᵢ
... | node left y' l' r' | hrᵢ | x≤*rᵢ | compound = node (lemma-≤-≤* x≤y y≤*l) x≤*rᵢ hl hrᵢ
lemma-insert-heap x (node {right} {y} {l} {r} y≤*l y≤*r hl hr) | inj₂ y≤x 
    with insert x r | lemma-insert-heap x hr | lemma-insert-≤* y≤x y≤*r | lemma-insert-compound x r
... | node perfect y' l' r' | hrᵢ | y≤*rᵢ | compound = node y≤*l y≤*rᵢ hl hrᵢ
... | node right y' l' r' | hrᵢ | y≤*rᵢ | compound = node y≤*l y≤*rᵢ hl hrᵢ
... | node left y' l' r' | hrᵢ | y≤*rᵢ | compound = node y≤*l y≤*rᵢ hl hrᵢ
