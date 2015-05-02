open import Relation.Binary.Core

module PLRTree.Drop.Heap {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) 
                     (trans≤ : Transitive _≤_) where

open import PLRTree {A} 
open import PLRTree.Compound {A} 
open import PLRTree.Drop _≤_ tot≤
open import PLRTree.DropLast.Heap _≤_ tot≤
open import PLRTree.Heap _≤_
open import PLRTree.Order.Properties {A}
open import PLRTree.Push.Heap _≤_ tot≤ trans≤ 

lemma-drop-heap : {t : PLRTree} → Heap t → Heap (drop t)
lemma-drop-heap leaf = leaf
lemma-drop-heap (node {t} {x} (lf≤* .x) (lf≤* .x) leaf leaf) = leaf
lemma-drop-heap (node {t} {x} {r = node t' x' l' r'} (lf≤* .x) (nd≤* x≤x' x≤*l' x≤*r') leaf (node x'≤*l' x'≤*r' hl' hr')) 
    with dropLast (node t x leaf (node t' x' l' r')) | lemma-dropLast-heap (node {t} (lf≤* x) (nd≤* {t'} x≤x' x≤*l' x≤*r') leaf (node x'≤*l' x'≤*r' hl' hr'))  
... | leaf | leaf = leaf
... | node t'' x'' l'' r'' | node x''≤*l'' x''≤*r'' hl'' hr'' =
           let z = last (node t x leaf (node t' x' l' r')) compound 
           in lemma-push-heap t'' z hl'' hr'' (≺-wf (node t'' z l'' r''))
lemma-drop-heap (node {t} {x} {l = node t' x' l' r'} {r} (nd≤* x≤x' x≤*l' x≤*r') x≤*r (node x'≤*l' x'≤*r' hl' hr') hr) 
    with dropLast (node t x (node t' x' l' r') r) | lemma-dropLast-heap (node {t} (nd≤* {t'} x≤x' x≤*l' x≤*r') x≤*r (node x'≤*l' x'≤*r' hl' hr') hr) 
... | leaf | leaf = leaf
... | node t'' x'' l'' r'' | node x''≤*l'' x''≤*r'' hl'' hr'' =
           let z = last (node t x (node t' x' l' r') r) compound 
           in lemma-push-heap t'' z hl'' hr'' (≺-wf (node t'' z l'' r''))
