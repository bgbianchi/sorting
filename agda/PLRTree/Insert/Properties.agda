open import Relation.Binary.Core 

module PLRTree.Insert.Properties {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) where

open import Data.Sum 
open import PLRTree {A} 
open import PLRTree.Insert _≤_ tot≤

data Compound : PLRTree → Set where
  compound : {t : Tag}{x : A}{l r : PLRTree} → Compound (node t x l r)

lemma-insert-compound : (x : A)(t : PLRTree) → Compound (insert x t)
lemma-insert-compound x leaf = compound
lemma-insert-compound x (node perfect y l r) 
    with tot≤ x y | l | r 
... | inj₁ x≤y | leaf | leaf = compound
... | inj₁ x≤y | leaf | node _ _ _ _ = compound
... | inj₁ x≤y | node _ _ _ _ | leaf = compound
... | inj₁ x≤y | node _ _ _ _ | node _ _ _ _ = compound
... | inj₂ y≤x | leaf | leaf = compound
... | inj₂ y≤x | leaf | node _ _ _ _ = compound
... | inj₂ y≤x | node _ _ _ _ | leaf = compound
... | inj₂ y≤x | node _ _ _ _ | node _ _ _ _ = compound
lemma-insert-compound x (node left y l _) 
    with tot≤ x y 
... | inj₁ x≤y 
    with insert y l | lemma-insert-compound y l
... | node perfect _ _ _ | compound = compound
... | node left _ _ _ | compound = compound 
... | node right _ _ _ | compound = compound 
lemma-insert-compound x (node left y l _) | inj₂ y≤x
    with insert x l | lemma-insert-compound x l
... | node perfect _ _ _ | compound = compound
... | node left _ _ _ | compound = compound
... | node right _ _ _ | compound = compound
lemma-insert-compound x (node right y _ r) 
    with tot≤ x y 
... | inj₁ x≤y 
    with insert y r | lemma-insert-compound y r
... | node perfect _ _ _ | compound = compound
... | node left _ _ _ | compound = compound 
... | node right _ _ _ | compound = compound 
lemma-insert-compound x (node right y _ r) | inj₂ y≤x
    with insert x r | lemma-insert-compound x r
... | node perfect _ _ _ | compound = compound
... | node left _ _ _ | compound = compound
... | node right _ _ _ | compound = compound

