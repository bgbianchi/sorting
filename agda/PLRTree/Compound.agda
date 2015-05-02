module PLRTree.Compound {A : Set}  where

open import PLRTree {A} 

data Compound : PLRTree → Set where
  compound : {t : Tag}{x : A}{l r : PLRTree} → Compound (node t x l r)
