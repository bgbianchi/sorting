open import Relation.Binary.Core

module PLRTree.DropLast.Heap {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_)  where

open import PLRTree {A} 
open import PLRTree.Drop _≤_ tot≤
open import PLRTree.Heap _≤_

lemma-dropLast-≤* : {x : A}{t : PLRTree} → x ≤* t → x ≤* dropLast t
lemma-dropLast-≤* {x} (lf≤* .x) = lf≤* x
lemma-dropLast-≤* (nd≤* {perfect} {x} {y} {l} {r} x≤y x≤*l x≤*r) 
    with r
... | leaf = x≤*r
... | node _ _ _ _ = nd≤* x≤y x≤*l (lemma-dropLast-≤* x≤*r) 
lemma-dropLast-≤* (nd≤* {left} {x} {y} {l} {r} x≤y x≤*l x≤*r) 
    with l | x≤*l | dropLast l | lemma-dropLast-≤* x≤*l 
... | leaf | _ | _ | _ = lf≤* x 
... | node perfect _ _ _ | _ | node perfect y' l' r' | x≤*dll = nd≤* x≤y x≤*dll x≤*r
... | node perfect _ _ _ | _ | leaf | (lf≤* .x) = nd≤* x≤y (lf≤* x) x≤*r
... | node perfect _ _ _ | _ | node left _ _ _ | x≤*dll = nd≤* x≤y x≤*dll x≤*r
... | node perfect _ _ _ | _ | node right _ _ _ | x≤*dll = nd≤* x≤y x≤*dll x≤*r
... | node left _ _ _ | _ | node perfect y' l' r' | x≤*dll = nd≤* x≤y x≤*dll x≤*r
... | node left _ _ _ | _ | leaf | (lf≤* .x) = nd≤* x≤y (lf≤* x) x≤*r
... | node left _ _ _ | _ | node left _ _ _ | x≤*dll = nd≤* x≤y x≤*dll x≤*r
... | node left _ _ _ | _ | node right _ _ _ | x≤*dll = nd≤* x≤y x≤*dll x≤*r
... | node right _ _ _ | _ | node perfect y' l' r' | x≤*dll = nd≤* x≤y x≤*dll x≤*r
... | node right _ _ _ | _ | leaf | (lf≤* .x) = nd≤* x≤y (lf≤* x) x≤*r
... | node right _ _ _ | _ | node left _ _ _ | x≤*dll = nd≤* x≤y x≤*dll x≤*r
... | node right _ _ _ | _ | node right _ _ _ | x≤*dll = nd≤* x≤y x≤*dll x≤*r
lemma-dropLast-≤* (nd≤* {right} {x} {y} {l} {r} x≤y x≤*l x≤*r) 
    with r
... | leaf = nd≤* x≤y x≤*r x≤*r
... | node perfect y' l' r' = nd≤* x≤y (lemma-dropLast-≤* x≤*l) x≤*r
... | node left _ _ _ = nd≤* x≤y x≤*l  (lemma-dropLast-≤* x≤*r)
... | node right _ _ _ = nd≤* x≤y x≤*l  (lemma-dropLast-≤* x≤*r)

lemma-dropLast-heap : {t : PLRTree} → Heap t → Heap (dropLast t)
lemma-dropLast-heap leaf = leaf
lemma-dropLast-heap (node {perfect} {x} {l} {r} x≤*l x≤*r hl hr) 
    with r
... | leaf = hr
... | node _ _ _ _ = node x≤*l (lemma-dropLast-≤* x≤*r) hl (lemma-dropLast-heap hr)
lemma-dropLast-heap (node {left} {x} {l} {r} x≤*l x≤*r hl hr) 
    with l | x≤*l | hl | dropLast l | lemma-dropLast-≤* x≤*l | lemma-dropLast-heap hl
... | leaf | _ | _ | _ | _ | _ = leaf
... | node perfect _ _ _ |  _ | _ | node perfect y' l' r' | x≤*dll | hdll = node x≤*dll x≤*r hdll hr
... | node perfect _ _ _ |  _ | _ | leaf | (lf≤* .x) | leaf = node (lf≤* x) x≤*r leaf hr
... | node perfect _ _ _ |  _ | _ | node left _ _ _ | x≤*dll | hdll = node x≤*dll x≤*r hdll hr
... | node perfect _ _ _ |  _ | _ | node right _ _ _ | x≤*dll | hdll = node x≤*dll x≤*r hdll hr
... | node left _ _ _ | _ | _ | node perfect y' l' r' | x≤*dll | hdll = node x≤*dll x≤*r hdll hr
... | node left _ _ _  |  _ | _ | leaf | (lf≤* .x) | leaf = node (lf≤* x) x≤*r leaf hr
... | node left _ _ _  |  _ | _ | node left _ _ _ | x≤*dll | hdll = node x≤*dll x≤*r hdll hr
... | node left _ _ _  |  _ | _ | node right _ _ _ | x≤*dll | hdll = node x≤*dll x≤*r hdll hr
... | node right _ _ _ |  _ | _ | node perfect y' l' r' | x≤*dll | hdll = node x≤*dll x≤*r hdll hr
... | node right _ _ _ |  _ | _ | leaf | (lf≤* .x) | leaf = node (lf≤* x) x≤*r leaf hr
... | node right _ _ _ |  _ | _ | node left _ _ _ | x≤*dll | hdll = node x≤*dll x≤*r hdll hr
... | node right _ _ _ |  _ | _ | node right _ _ _ | x≤*dll | hdll = node x≤*dll x≤*r hdll hr
lemma-dropLast-heap (node {right} {x} {l} {r} x≤*l x≤*r hl hr) 
    with r
... | leaf = node x≤*r x≤*r hr hr
... | node perfect y' l' r' = node (lemma-dropLast-≤* x≤*l) x≤*r (lemma-dropLast-heap hl) hr
... | node left _ _ _ = node x≤*l (lemma-dropLast-≤* x≤*r) hl (lemma-dropLast-heap hr)
... | node right _ _ _ = node x≤*l (lemma-dropLast-≤* x≤*r) hl (lemma-dropLast-heap hr)
