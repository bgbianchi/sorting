open import Relation.Binary.Core

module PLRTree.DropLast.Complete {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_)  where

open import Data.Sum renaming (_⊎_ to _∨_)
open import PLRTree {A}  
open import PLRTree.Drop _≤_ tot≤
open import PLRTree.Complete {A}
open import PLRTree.Complete.Properties {A}
open import PLRTree.Compound {A}
open import PLRTree.Equality {A}
open import PLRTree.Equality.Properties {A}

lemma-dropLast-≃ : {l r : PLRTree} → l ≃ r → Compound l → l ⋙ dropLast r
lemma-dropLast-≃ (≃nd x x' ≃lf ≃lf ≃lf) compound = ⋙p (⋗lf x)
lemma-dropLast-≃ (≃nd x x' (≃nd _ _ _ _ _) ≃lf ()) compound 
lemma-dropLast-≃ (≃nd x x' l≃r (≃nd x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (≃nd x₁ .x'₁ l₁≃r₁ _ l₁≃l'₁)) compound = 
               let x'₁l'₁r'₁⋙dl-x'₂l'₂r'₂ = lemma-dropLast-≃ (≃nd x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) compound
               in ⋙r x x' l≃r x'₁l'₁r'₁⋙dl-x'₂l'₂r'₂ (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)

lemma-dropLast-⋗ : {l r : PLRTree} → l ⋗ r → Compound r → dropLast l ⋘ r
lemma-dropLast-⋗ (⋗nd _ _ ≃lf _ ()) compound 
lemma-dropLast-⋗ (⋗nd x x' (≃nd x₁ x₂ ≃lf ≃lf ≃lf) ≃lf (⋗lf .x₁)) compound  = x⋘ x x₁ x'
lemma-dropLast-⋗ (⋗nd _ _ (≃nd x₁ _ ≃lf (≃nd _ _ _ _ _) ()) ≃lf (⋗lf .x₁)) compound  
lemma-dropLast-⋗ (⋗nd x x' (≃nd {l₁} {r₁} x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) l'≃r' (⋗nd .x₁ x'₁ _ l'₁≃r'₁ l₁⋗l'₁)) compound = 
               let x₁l₁r₁⋙dl-x₂l₂r₂ = lemma-dropLast-≃ (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) compound
               in r⋘ x x' x₁l₁r₁⋙dl-x₂l₂r₂ l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)

mutual
  lemma-dropLast-⋘ : {l r : PLRTree} → l ⋘ r → dropLast l ⋘ r ∨ dropLast l ≃ r
  lemma-dropLast-⋘ (x⋘ x _ z) = inj₂ (≃nd x z ≃lf ≃lf ≃lf)
  lemma-dropLast-⋘ (l⋘ x x' (x⋘ x₁ x₂ x₃) x'₁≃x'₂ (≃nd .x₃ x'₁ ≃lf ≃lf ≃lf)) = inj₂ (≃nd x x' (≃nd x₁ x₃ ≃lf ≃lf ≃lf) x'₁≃x'₂ (≃nd x₁ x'₁ ≃lf ≃lf ≃lf))
  lemma-dropLast-⋘ (l⋘ x x' (l⋘ {l₁} {r₁} x₁ x₂ l₁⋘r₁ l₂≃r₂ r₁≃l₂) l'≃r' (≃nd .x₂ x'₁ _ l'₁≃r'₁ l₂≃l'₁)) 
      with dropLast (node left x₁ l₁ r₁) | lemma-dropLast-⋘ (l⋘ x₁ x₂ l₁⋘r₁ l₂≃r₂ r₁≃l₂)
  ... | leaf | inj₁ ()
  ... | node perfect _ _ _ | inj₁ ()
  ... | node left _ _ _ | inj₁ dl-x₁l₁r₁⋘x₂l₂r₂ = inj₁ (l⋘ x x' dl-x₁l₁r₁⋘x₂l₂r₂ l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ l₂≃l'₁))
  ... | node right _ _ _ | inj₁ dl-x₁l₁r₁⋘x₂l₂r₂ = inj₁ (l⋘ x x' dl-x₁l₁r₁⋘x₂l₂r₂ l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ l₂≃l'₁))
  ... | leaf | inj₂ ()
  ... | node perfect x'' l'' r'' | inj₂ (≃nd .x'' .x₂ l''≃r'' _ l''≃l₂) = 
               let l''≃l'₁ = trans≃ l''≃l₂ l₂≃l'₁
               in inj₂ (≃nd x x' (≃nd x'' x₂ l''≃r'' l₂≃r₂ l''≃l₂) l'≃r' (≃nd x'' x'₁ l''≃r'' l'₁≃r'₁ l''≃l'₁))
  ... | node left _ _ _ | inj₂ ()
  ... | node right _ _ _ | inj₂ ()
  lemma-dropLast-⋘ (l⋘ x x' (r⋘ {l₁} {r₁} x₁ x₂ l₁⋙r₁ l₂≃r₂ l₁⋗l₂) l'≃r' (≃nd .x₂ x'₁ _ l'₁≃r'₁ l₂≃l'₁)) 
      with dropLast (node right x₁ l₁ r₁) | lemma-dropLast-⋘ (r⋘ x₁ x₂ l₁⋙r₁ l₂≃r₂ l₁⋗l₂)
  ... | leaf | inj₁ ()
  ... | node perfect _ _ _ | inj₁ ()
  ... | node left _ _ _ | inj₁ dl-x₁l₁r₁⋘x₂l₂r₂ = inj₁ (l⋘ x x' dl-x₁l₁r₁⋘x₂l₂r₂ l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ l₂≃l'₁))
  ... | node right _ _ _ | inj₁ dl-x₁l₁r₁⋘x₂l₂r₂ = inj₁ (l⋘ x x' dl-x₁l₁r₁⋘x₂l₂r₂ l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ l₂≃l'₁))
  ... | leaf | inj₂ ()
  ... | node perfect x'' l'' r'' | inj₂ (≃nd .x'' .x₂ l''≃r'' _ l''≃l₂) = 
               let l''≃l'₁ = trans≃ l''≃l₂ l₂≃l'₁
               in inj₂ (≃nd x x' (≃nd x'' x₂ l''≃r'' l₂≃r₂ l''≃l₂) l'≃r' (≃nd x'' x'₁ l''≃r'' l'₁≃r'₁ l''≃l'₁))
  ... | node left _ _ _ | inj₂ ()
  ... | node right _ _ _ | inj₂ ()
  lemma-dropLast-⋘ (r⋘ x x' (⋙p (⋗lf x₁)) ≃lf (⋗lf .x₁))  = inj₂ (≃nd x x' ≃lf ≃lf ≃lf)
  lemma-dropLast-⋘ (r⋘ _ _ (⋙p (⋗lf x₁)) l'≃r' (⋗nd .x₁ _ _ _ ()))  
  lemma-dropLast-⋘ (r⋘ _ _ (⋙p (⋗nd x₁ _ ≃lf _ ())) ≃lf (⋗lf .x₁))
  lemma-dropLast-⋘ (r⋘ x x' (⋙p (⋗nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁⋗l₂)) l'≃r' (⋗nd .x₁ x'₁ _ l'₁≃r'₁ l₁⋗l'₁)) = 
               let dl-x₁l₁r₁⋘x₂l₂r₂ = lemma-dropLast-⋗ (⋗nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁⋗l₂) compound ;
                    l₂≃l'₁ = lemma-⋗* l₁⋗l₂ l₁⋗l'₁
               in inj₁ (l⋘ x x' dl-x₁l₁r₁⋘x₂l₂r₂ l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ l₂≃l'₁))
  lemma-dropLast-⋘ (r⋘ _ _ (⋙l x₁ _ ≃lf _ ()) ≃lf (⋗lf .x₁)) 
  lemma-dropLast-⋘ (r⋘ x x' (⋙l x₁ x₂ l₁≃r₁ l₂⋘r₂ l₁⋗r₂) l'≃r' (⋗nd .x₁ x'₁ _ l'₁≃r'₁ l₁⋗l'₁)) 
      with lemma-dropLast-⋙ (⋙l x₁ x₂ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
  ... | inj₁ dl-x₁l₁r₁⋘x₂l₂r₂ = inj₁ (r⋘ x x' dl-x₁l₁r₁⋘x₂l₂r₂ l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)) 
  ... | inj₂ () 
  lemma-dropLast-⋘ (r⋘ x x' (⋙r x₁ x₂ ≃lf (⋙p ()) ≃lf) ≃lf (⋗lf .x₁)) 
  lemma-dropLast-⋘ (r⋘ _ _ (⋙r x₁ _ ≃lf (⋙l _ _ _ _ _) ()) ≃lf (⋗lf .x₁)) 
  lemma-dropLast-⋘ (r⋘ _ _ (⋙r x₁ _ ≃lf (⋙r _ _ _ _ _) ()) ≃lf (⋗lf .x₁)) 
  lemma-dropLast-⋘ (r⋘ x x' (⋙r x₁ x₂ l₁≃r₁ l₂⋙r₂ l₁≃l₂) l'≃r' (⋗nd .x₁ x'₁ _ l'₁≃r'₁ l₁⋗l'₁)) 
      with lemma-dropLast-⋙ (⋙r x₁ x₂ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
  ... | inj₁ dl-x₁l₁r₁⋘x₂l₂r₂ = inj₁ (r⋘ x x' dl-x₁l₁r₁⋘x₂l₂r₂ l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)) 
  ... | inj₂ () 

  lemma-dropLast-⋙ : {l r : PLRTree} → l ⋙ r → l ⋙ dropLast r ∨ l ⋗ r
  lemma-dropLast-⋙ (⋙p l⋗r) = inj₂ l⋗r
  lemma-dropLast-⋙ (⋙l x x' l≃r (x⋘ x'₁ x'₂ x'₃) (⋗nd x₁ .x'₃ l₁≃r₁ ≃lf l₁⋗x'₂)) = inj₁ (⋙p (⋗nd x x' l≃r (≃nd x'₁ x'₃ ≃lf ≃lf ≃lf) (⋗nd x₁ x'₁ l₁≃r₁ ≃lf l₁⋗x'₂)))
  lemma-dropLast-⋙ (⋙l x x' l≃r (l⋘ {l'₁} {r'₁} x'₁ x'₂ l'₁⋘r'₁ l'₂≃r'₂ r'₁≃l'₂) (⋗nd x₁ .x'₂ l₁≃r₁ _ l₁⋗l'₂))  
      with dropLast (node left x'₁ l'₁ r'₁) | lemma-dropLast-⋘ (l⋘ x'₁ x'₂ l'₁⋘r'₁ l'₂≃r'₂ r'₁≃l'₂)
  ... | leaf | inj₁ ()
  ... | node perfect _ _ _ | inj₁ ()
  ... | node left _ _ _ | inj₁ dl-x'₁l'₁r'₁⋘x'₂l'₂r'₂ = inj₁ (⋙l x x' l≃r dl-x'₁l'₁r'₁⋘x'₂l'₂r'₂ (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂))
  ... | node right _ _ _ | inj₁ dl-x'₁l'₁r'₁⋘x'₂l'₂r'₂ = inj₁ (⋙l x x' l≃r dl-x'₁l'₁r'₁⋘x'₂l'₂r'₂ (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂))
  ... | leaf | inj₂ ()
  ... | node perfect x'' l'' r'' | inj₂ (≃nd .x'' .x'₂ l''≃r'' _ l''≃l'₂) = 
               let l₁⋗l'' = lemma-⋗-≃ l₁⋗l'₂ (symm≃ l''≃l'₂) 
               in inj₁ (⋙p (⋗nd x x' l≃r (≃nd x'' x'₂ l''≃r'' l'₂≃r'₂ l''≃l'₂) (⋗nd x₁ x'' l₁≃r₁ l''≃r'' l₁⋗l'')))
  ... | node left _ _ _ | inj₂ ()
  ... | node right _ _ _ | inj₂ ()
  lemma-dropLast-⋙ (⋙l x x' l≃r (r⋘ {l'₁} {r'₁} x'₁ x'₂ l'₁⋙r'₁ l'₂≃r'₂ l'₁⋗l'₂) (⋗nd x₁ .x'₂ l₁≃r₁ _ l₁⋗l'₂)) 
      with dropLast (node right x'₁ l'₁ r'₁) | lemma-dropLast-⋘ (r⋘ x'₁ x'₂ l'₁⋙r'₁ l'₂≃r'₂ l'₁⋗l'₂)
  ... | leaf | inj₁ ()
  ... | node perfect _ _ _ | inj₁ ()
  ... | node left _ _ _ | inj₁ dl-x'₁l'₁r'₁⋘x'₂l'₂r'₂ = inj₁ (⋙l x x' l≃r dl-x'₁l'₁r'₁⋘x'₂l'₂r'₂ (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂))
  ... | node right _ _ _ | inj₁ dl-x'₁l'₁r'₁⋘x'₂l'₂r'₂ = inj₁ (⋙l x x' l≃r dl-x'₁l'₁r'₁⋘x'₂l'₂r'₂ (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂))
  ... | leaf | inj₂ ()
  ... | node perfect x'' l'' r'' | inj₂ (≃nd .x'' .x'₂ l''≃r'' _ l''≃l'₂) = 
               let l₁⋗l'' = lemma-⋗-≃ l₁⋗l'₂ (symm≃ l''≃l'₂) 
               in inj₁ (⋙p (⋗nd x x' l≃r (≃nd x'' x'₂ l''≃r'' l'₂≃r'₂ l''≃l'₂) (⋗nd x₁ x'' l₁≃r₁ l''≃r'' l₁⋗l'')))
  ... | node left _ _ _ | inj₂ ()
  ... | node right _ _ _ | inj₂ ()
  lemma-dropLast-⋙ (⋙r x x' l≃r (⋙p ()) ≃lf) 
  lemma-dropLast-⋙ (⋙r x x' l≃r (⋙p (⋗lf x'₁)) (≃nd x₁ .x'₁ ≃lf ≃lf ≃lf)) = inj₁ (⋙p (⋗nd x x' l≃r ≃lf (⋗lf x₁)))
  lemma-dropLast-⋙ (⋙r x x' l≃r (⋙p (⋗nd x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁⋗l'₂)) (≃nd x₁ .x'₁ l₁≃r₁ _ l₁≃l'₁)) = 
               let dl-x'₁l'₁r'₁⋘x'₂l'₂r'₂ =  lemma-dropLast-⋗ (⋗nd x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁⋗l'₂) compound ;
                    l₁⋗l'₂ = lemma-≃-⋗ (symm≃ l₁≃l'₁) l'₁⋗l'₂
               in inj₁ (⋙l x x' l≃r dl-x'₁l'₁r'₁⋘x'₂l'₂r'₂ (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂))
  lemma-dropLast-⋙ (⋙r x x' l≃r (⋙l x'₁ x'₂ l'₁≃r'₁ l'₂⋘r'₂ l'₁⋗r'₂) (≃nd x₁ .x'₁ l₁≃r₁ _ l₁≃l'₁)) 
      with lemma-dropLast-⋙ (⋙l x'₁ x'₂ l'₁≃r'₁ l'₂⋘r'₂ l'₁⋗r'₂)
  ... | inj₁ x'₁l'₁r'₁⋙dl-x'₂l'₂r'₂ = inj₁ (⋙r x x' l≃r x'₁l'₁r'₁⋙dl-x'₂l'₂r'₂ (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁))
  ... | inj₂ ()
  lemma-dropLast-⋙ (⋙r x x' l≃r (⋙r x'₁ x'₂ l'₁≃r'₁ l'₂⋙r'₂ l'₁≃l'₂) (≃nd x₁ .x'₁ l₁≃r₁ _ l₁≃l'₁)) 
      with lemma-dropLast-⋙ (⋙r x'₁ x'₂ l'₁≃r'₁ l'₂⋙r'₂ l'₁≃l'₂)
  ... | inj₁ x'₁l'₁r'₁⋙dl-x'₂l'₂r'₂ = inj₁ (⋙r x x' l≃r x'₁l'₁r'₁⋙dl-x'₂l'₂r'₂ (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁))
  ... | inj₂ ()

lemma-dropLast-complete : {t : PLRTree} → Complete t → Complete (dropLast t)
lemma-dropLast-complete leaf = leaf
lemma-dropLast-complete (perfect {l} {r} x cl cr l≃r) 
     with l | r | l≃r
... | leaf | leaf | ≃lf = leaf
... | node perfect x' l' r' | node perfect x'' l'' r'' | ≃nd .x' .x'' l'≃r' l''≃r'' l'≃l'' = right x cl (lemma-dropLast-complete cr) (lemma-dropLast-≃ (≃nd x' x'' l'≃r' l''≃r'' l'≃l'') compound)
lemma-dropLast-complete (left {l} {r} x cl cr l⋘r)
    with l | r | l⋘r | lemma-dropLast-⋘ l⋘r
... | leaf | _ | () | _ 
... | node perfect x' l' r' | _ | () | _  
... | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | inj₁ ld⋘r  
    with dropLast (node left x' l' r') | ld⋘r | lemma-dropLast-complete cl
... | leaf | () | _
... | node perfect _ _ _ | () | _
... | node left x''' l''' r''' | ld⋘r' | cld = left x cld cr ld⋘r'
... | node right x''' l''' r''' | ld⋘r' | cld = left x cld cr ld⋘r'
lemma-dropLast-complete (left x cl cr l⋘r) | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | inj₂ ld≃r 
    with dropLast (node left x' l' r') | ld≃r | lemma-dropLast-complete cl
... | leaf | () | _
... | node perfect x''' l''' r''' | ld≃r' | cld = perfect x cld cr ld≃r'
... | node left _ _ _ | () | _
... | node right _ _ _ | () | _
lemma-dropLast-complete (left x cl cr l⋘r) | node right x' l' r' | leaf | () | _ 
lemma-dropLast-complete (left x cl cr l⋘r) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | inj₁ () 
lemma-dropLast-complete (left x cl cr l⋘r) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | inj₂ x'≃x''' = 
           perfect x (perfect x' leaf leaf ≃lf) cr x'≃x'''
lemma-dropLast-complete (left x cl cr l⋘r) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l⋙r l''≃r'' l'⋗l'' | inj₁ ld⋘r 
    with dropLast (node right x' l' r') | ld⋘r | lemma-dropLast-complete cl
... | leaf | () | _
... | node perfect _ _ _ | () | _
... | node left x''' l''' r''' | ld⋘r' | cld = left x cld cr ld⋘r'
... | node right x''' l''' r''' | ld⋘r' | cld = left x cld cr ld⋘r'
lemma-dropLast-complete (left x cl cr l⋘r) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l⋙r l''≃r'' l'⋗l'' | inj₂ ld≃r 
    with dropLast (node right x' l' r') | ld≃r | lemma-dropLast-complete cl
... | leaf | () | _
... | node perfect x''' l''' r''' | ld≃r' | cld = perfect x cld cr ld≃r'
... | node left _ _ _ | () | _
... | node right _ _ _ | () | _ 
lemma-dropLast-complete (left x cl cr l⋘r) | node right x' l' r' | node left x'' l'' r'' | () | _ 
lemma-dropLast-complete (left x cl cr l⋘r) | node right x' l' r' | node right x'' l'' r'' | () | _
lemma-dropLast-complete (right {l} {r} x cl cr l⋙r) 
    with l | r | l⋙r
... | leaf | _ | ⋙p ()
... | node perfect x' leaf leaf | leaf | ⋙p (⋗lf .x') = perfect x leaf leaf ≃lf
... | node perfect x' leaf leaf | node left _ _ _ | ⋙p ()
... | node perfect x' leaf leaf | node right _ _ _ | ⋙p ()
... | node perfect x' l' r' | node perfect x'' l'' r'' | ⋙p (⋗nd .x' .x'' l'≃r' l''≃r'' l'⋗l'') = left x (lemma-dropLast-complete cl) cr (lemma-dropLast-⋗ (⋗nd x' x'' l'≃r' l''≃r'' l'⋗l'') compound)
... | node perfect x' l' r' | node left x'' l'' r'' | ⋙l .x' .x'' l'≃r' l''⋘r'' l'⋗r'' 
    with lemma-dropLast-⋙ (⋙l x' x'' l'≃r' l''⋘r'' l'⋗r'')
... | inj₁ l⋙rd = right x cl (lemma-dropLast-complete  cr) l⋙rd
... | inj₂ ()
lemma-dropLast-complete (right x cl cr l⋙r) | node perfect x' l' r' | node right x'' l'' r'' | ⋙r .x' .x'' l'≃r' l''⋙r'' l'≃l'' 
    with lemma-dropLast-⋙ (⋙r x' x'' l'≃r' l''⋙r'' l'≃l'')
... | inj₁ l⋙rd = right x cl (lemma-dropLast-complete cr) l⋙rd
... | inj₂ ()
lemma-dropLast-complete (right x cl cr l⋙r) | node left _ _ _ | _ | ⋙p ()
lemma-dropLast-complete (right x cl cr l⋙r) | node right _ _ _ | _ | ⋙p ()
