open import Relation.Binary.Core

module PLRTree.Drop {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) where

open import Data.Sum
open import Induction.WellFounded
open import PLRTree {A}
open import PLRTree.Compound {A}
open import PLRTree.Order {A}
open import PLRTree.Order.Properties {A}
open import Relation.Binary.PropositionalEquality

last : (t : PLRTree) → Compound t → A
last (node perfect x _ r) compound
    with r
... | leaf = x
... | node t' y' l' r' =  last (node t' y' l' r') compound 
last (node left x l _) compound
    with l
... | leaf = x
... | node t' y' l' r' =  last (node t' y' l' r') compound 
last (node right x l r) compound
    with l | r
... | leaf | _ = x
... | node _ y' _ _ | leaf =  y'
... | node t' y' l' r' | node perfect _ _ _ = last (node t' y' l' r') compound 
... | _ | node t' y' l' r' = last (node t' y' l' r') compound 

dropLast : PLRTree → PLRTree
dropLast leaf = leaf
dropLast (node perfect x l r) 
    with r 
... | leaf = leaf
... | node _ _ _ _ = node right x l (dropLast r)
dropLast (node left x l r) 
    with l | dropLast l
... | leaf | _ = leaf
... | node _ _ _ _ | node perfect y' l' r' = node perfect x (node perfect y' l' r') r
... | node _ _ _ _ | t = node left x t r
dropLast (node right x l r)
    with r
... | leaf = node perfect x leaf leaf
... | node perfect y' l' r' = node left x (dropLast l) (node perfect y' l' r')
... | node _ _ _ _ = node right x l (dropLast r) 

push : (t : PLRTree) → Acc _≺_ t → PLRTree
push leaf _ = leaf
push (node t x  leaf _) _ = node t x leaf leaf
push (node t x (node t' x' _ _) leaf) _ 
    with tot≤ x x'
... | inj₁ x≤x' = node t x (node t' x' leaf leaf) leaf
... | inj₂ x'≤x = node t x' (node t' x leaf leaf) leaf
push (node t x (node t' x' l' r') (node t'' x'' l'' r'')) (acc rs)
    with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
... | inj₁ x≤x' | inj₁ x≤x'' | _ = node t x (node t' x' l' r') (node t'' x'' l'' r'')
... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height t'' x x'' l'' r'' = 
           let acc-t''xl''r'' = rs (node t'' x l'' r'') (lemma-≺-right t x (node t' x' l' r') (node t'' x'' l'' r''))
           in node t x'' (node t' x' l' r') (push (node t'' x l'' r'') acc-t''xl''r'')
... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height t' x x' l' r' = 
           let acc-t'xl'r' = rs (node t' x l' r') (lemma-≺-left t x (node t' x' l' r') (node t'' x'' l'' r''))
           in node t x' (push (node t' x l' r') acc-t'xl'r') (node t'' x'' l'' r'')
... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height t' x x' l' r' = 
           let acc-t'xl'r' = rs (node t' x l' r') (lemma-≺-left t x (node t' x' l' r') (node t'' x'' l'' r''))
           in node t x' (push (node t' x l' r') acc-t'xl'r') (node t'' x'' l'' r'')
... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height t'' x x'' l'' r'' = 
           let acc-t''xl''r'' = rs (node t'' x l'' r'') (lemma-≺-right t x (node t' x' l' r') (node t'' x'' l'' r''))
           in node t x'' (node t' x' l' r') (push (node t'' x l'' r'') acc-t''xl''r'')

setRoot : A → PLRTree → PLRTree 
setRoot _ leaf = leaf 
setRoot x (node t _ l r) = node t x l r

drop : PLRTree → PLRTree
drop leaf = leaf
drop (node _ _ leaf leaf) = leaf
drop (node t x l r) = push (setRoot z t') (≺-wf (setRoot z t'))
           where z = last (node t x l r) compound ;
                      t' = dropLast (node t x l r)
