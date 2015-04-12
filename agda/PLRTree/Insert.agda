open import Relation.Binary.Core

module PLRTree.Insert {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) where

open import Data.Sum
open import PLRTree {A}

insert : A → PLRTree → PLRTree
insert x leaf = node perfect x leaf leaf 
insert x (node perfect y l r) 
    with tot≤ x y | l | r
... | inj₁ x≤y | leaf | leaf = node right x (node perfect y leaf leaf) leaf
... | inj₁ x≤y | _ | _ = node left x (insert y l) r  
... | inj₂ y≤x | leaf | leaf = node right y (node perfect x leaf leaf) leaf
... | inj₂ y≤x | _ | _ = node left y (insert x l) r  
insert x (node left y l r)
    with tot≤ x y
... | inj₁ x≤y 
    with insert y l 
... | node perfect y' l' r' = node right x (node perfect y' l' r') r 
... | t = node left x t r 
insert x (node left y l r) | inj₂ y≤x 
    with insert x l
... | node perfect y' l' r' = node right y (node perfect y' l' r') r 
... | t = node left y t r 
insert x (node right y l r)
    with tot≤ x y 
... | inj₁ x≤y 
    with insert y r
... | node perfect y' l' r' = node perfect x l (node perfect y' l' r') 
... | t = node right x l t 
insert x (node right y l r) | inj₂ y≤x 
    with insert x r
... | node perfect y' l' r' = node perfect y l (node perfect y' l' r') 
... | t = node right y l t 
