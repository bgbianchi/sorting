open import Relation.Binary.Core

module PLRTree.DropLast.Permutation {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) where

open import Data.List 
open import Data.Sum
open import List.Permutation.Base A 
open import List.Permutation.Base.Concatenation A 
open import List.Permutation.Base.Equivalence A 
open import PLRTree {A} 
open import PLRTree.Complete {A} 
open import PLRTree.Compound {A} 
open import PLRTree.Drop _≤_ tot≤
open import PLRTree.DropLast.Complete _≤_ tot≤
open import PLRTree.Equality {A} 

lemma-last-dropLast : {t : Tag}{x : A}{l r : PLRTree} → Complete (node t x l r) → (last (node t x l r) compound ∷ flatten (dropLast (node t x l r))) ∼ flatten (node t x l r) 
lemma-last-dropLast (perfect {l} {r} x cl cr l≃r) 
    with l | r | l≃r
... | leaf | leaf | ≃lf = ∼x /head /head ∼[]
... | node perfect x' l' r' | node perfect x'' l'' r'' | ≃nd .x' .x'' l'≃r' l''≃r'' l'≃l'' = 
                 let _l = node perfect x' l' r' ;
                      _r = node perfect x'' l'' r'' ;
                      zxflfrd∼xflzfrd = ∼x /head (lemma++/ {last _r compound} {x ∷ flatten _l}) lemma-refl∼ ;
                      xflzfrd∼xflfr = lemma++∼l {x ∷ flatten _l} (lemma-last-dropLast cr)
                 in lemma-trans∼ zxflfrd∼xflzfrd xflzfrd∼xflfr
lemma-last-dropLast (left {l} {r} x cl cr l⋘r)
    with l | r | l⋘r | lemma-dropLast-⋘ l⋘r
... | leaf | _ | () | _ 
... | node perfect x' l' r' | _ | () | _  
... | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | inj₁ ld⋘r  
    with dropLast (node left x' l' r') | ld⋘r | lemma-last-dropLast cl
... | leaf | () | _
... | node perfect _ _ _ | () | _
... | node left x''' l''' r''' | ld⋘r' | zfldfr∼flfr = ∼x (/tail /head) /head (lemma++∼r zfldfr∼flfr)
... | node right x''' l''' r''' | ld⋘r' | zfldfr∼flfr  = ∼x (/tail /head) /head (lemma++∼r zfldfr∼flfr)
lemma-last-dropLast (left x cl cr l⋘r) | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | inj₂ ld≃r 
    with dropLast (node left x' l' r') | ld≃r | lemma-last-dropLast cl
... | leaf | () | _
... | node perfect x''' l''' r''' | ld≃r' | zfldfr∼flfr = ∼x (/tail /head) /head (lemma++∼r zfldfr∼flfr)
... | node left _ _ _ | () | _
... | node right _ _ _ | () | _
lemma-last-dropLast (left x cl cr l⋘r) | node right x' l' r' | leaf | () | _ 
lemma-last-dropLast (left x cl cr l⋘r) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | inj₁ () 
lemma-last-dropLast (left x cl cr l⋘r) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | inj₂ x'≃x''' = 
                 ∼x (/tail /head) /head (lemma++∼r (lemma-last-dropLast cl))
lemma-last-dropLast (left x cl cr l⋘r) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l⋙r l''≃r'' l'⋗l'' | inj₁ ld⋘r 
    with dropLast (node right x' l' r') | ld⋘r | lemma-last-dropLast cl
... | leaf | () | _
... | node perfect _ _ _ | () | _
... | node left x''' l''' r''' | ld⋘r' | zfldfr∼flfr = ∼x (/tail /head) /head (lemma++∼r zfldfr∼flfr)
... | node right x''' l''' r''' | ld⋘r' | zfldfr∼flfr = ∼x (/tail /head) /head (lemma++∼r zfldfr∼flfr)
lemma-last-dropLast (left x cl cr l⋘r) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l⋙r l''≃r'' l'⋗l'' | inj₂ ld≃r 
    with dropLast (node right x' l' r') | ld≃r | lemma-last-dropLast cl
... | leaf | () | _
... | node perfect x''' l''' r''' | ld≃r' | zfldfr∼flfr = ∼x (/tail /head) /head (lemma++∼r zfldfr∼flfr)
... | node left _ _ _ | () | _
... | node right _ _ _ | () | _ 
lemma-last-dropLast (left x cl cr l⋘r) | node right x' l' r' | node left x'' l'' r'' | () | _ 
lemma-last-dropLast (left x cl cr l⋘r) | node right x' l' r' | node right x'' l'' r'' | () | _
lemma-last-dropLast (right {l} {r} x cl cr l⋙r) 
    with l | r | l⋙r
... | leaf | _ | ⋙p ()
... | node perfect x' leaf leaf | leaf | ⋙p (⋗lf .x') = ∼x (/tail /head) /head (∼x /head /head ∼[])
... | node perfect x' leaf leaf | node left _ _ _ | ⋙p ()
... | node perfect x' leaf leaf | node right _ _ _ | ⋙p ()
... | node perfect x' l' r' | node perfect x'' l'' r'' | ⋙p (⋗nd .x' .x'' l'≃r' l''≃r'' l'⋗l'') = 
                 ∼x (/tail /head) /head (lemma++∼r (lemma-last-dropLast cl))
... | node perfect x' l' r' | node left x'' l'' r'' | ⋙l .x' .x'' l'≃r' l''⋘r'' l'⋗r'' 
    with lemma-dropLast-⋙ (⋙l x' x'' l'≃r' l''⋘r'' l'⋗r'')
... | inj₁ l⋙rd = 
                 let _l = node perfect x' l' r' ;
                      _r = node left x'' l'' r'' ;
                      zxflfrd∼xflzfrd = ∼x /head (lemma++/ {last _r compound} {x ∷ flatten _l}) lemma-refl∼ ;
                      xflzfrd∼xflfr = lemma++∼l {x ∷ flatten _l} (lemma-last-dropLast cr)
                 in lemma-trans∼ zxflfrd∼xflzfrd xflzfrd∼xflfr
... | inj₂ ()
lemma-last-dropLast (right x cl cr l⋙r) | node perfect x' l' r' | node right x'' l'' r'' | ⋙r .x' .x'' l'≃r' l''⋙r'' l'≃l'' 
    with lemma-dropLast-⋙ (⋙r x' x'' l'≃r' l''⋙r'' l'≃l'')
... | inj₁ l⋙rd = 
                 let _l = node perfect x' l' r' ;
                      _r = node right x'' l'' r'' ;
                      zxflfrd∼xflzfrd = ∼x /head (lemma++/ {last _r compound} {x ∷ flatten _l}) lemma-refl∼ ;
                      xflzfrd∼xflfr = lemma++∼l {x ∷ flatten _l} (lemma-last-dropLast cr)
                 in lemma-trans∼ zxflfrd∼xflzfrd xflzfrd∼xflfr
... | inj₂ ()
lemma-last-dropLast (right x cl cr l⋙r) | node left _ _ _ | _ | ⋙p ()
lemma-last-dropLast (right x cl cr l⋙r) | node right _ _ _ | _ | ⋙p ()

lemma-dropLast-∼ : {t : Tag}{x : A}{l r : PLRTree} → Complete (node t x l r) → flatten (setRoot (last (node t x l r) compound) (dropLast (node t x l r))) ∼ (flatten l ++ flatten r)
lemma-dropLast-∼ (perfect {l} {r} x cl cr l≃r) 
    with l | r | l≃r
... | leaf | leaf | ≃lf = ∼[]
... | node perfect x' l' r' | node perfect x'' l'' r'' | ≃nd .x' .x'' l'≃r' l''≃r'' l'≃l'' =  
                 let _l = node perfect x' l' r' ;
                      _r = node perfect x'' l'' r'' ;
                      zflfrd∼flzfrd = ∼x /head (lemma++/ {last _r compound} {flatten _l}) lemma-refl∼ ;
                      flzfrd∼flfr = lemma++∼l {flatten _l} (lemma-last-dropLast cr)
                 in lemma-trans∼ zflfrd∼flzfrd flzfrd∼flfr
lemma-dropLast-∼ (left {l} {r} x cl cr l⋘r)
    with l | r | l⋘r | lemma-dropLast-⋘ l⋘r
... | leaf | _ | () | _ 
... | node perfect x' l' r' | _ | () | _  
... | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | inj₁ ld⋘r  
    with dropLast (node left x' l' r') | ld⋘r | lemma-last-dropLast cl
... | leaf | () | _
... | node perfect _ _ _ | () | _
... | node left x''' l''' r''' | ld⋘r' | zfld∼fl = lemma++∼r zfld∼fl
... | node right x''' l''' r''' | ld⋘r' | zfld∼fl  = lemma++∼r zfld∼fl
lemma-dropLast-∼ (left x cl cr l⋘r) | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | inj₂ ld≃r 
    with dropLast (node left x' l' r') | ld≃r | lemma-last-dropLast cl
... | leaf | () | _
... | node perfect x''' l''' r''' | ld≃r' | zfld∼fl = lemma++∼r zfld∼fl 
... | node left _ _ _ | () | _
... | node right _ _ _ | () | _
lemma-dropLast-∼ (left x cl cr l⋘r) | node right x' l' r' | leaf | () | _ 
lemma-dropLast-∼ (left x cl cr l⋘r) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | inj₁ () 
lemma-dropLast-∼ (left x cl cr l⋘r) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | inj₂ x'≃x''' = 
                 lemma++∼r (lemma-last-dropLast cl)
lemma-dropLast-∼ (left x cl cr l⋘r) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l⋙r l''≃r'' l'⋗l'' | inj₁ ld⋘r 
    with dropLast (node right x' l' r') | ld⋘r | lemma-last-dropLast cl
... | leaf | () | _
... | node perfect _ _ _ | () | _
... | node left x''' l''' r''' | ld⋘r' | zfld∼fl = lemma++∼r zfld∼fl
... | node right x''' l''' r''' | ld⋘r' | zfld∼fl = lemma++∼r zfld∼fl
lemma-dropLast-∼ (left x cl cr l⋘r) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l⋙r l''≃r'' l'⋗l'' | inj₂ ld≃r 
    with dropLast (node right x' l' r') | ld≃r | lemma-last-dropLast cl
... | leaf | () | _
... | node perfect x''' l''' r''' | ld≃r' | zfld∼fl = lemma++∼r zfld∼fl 
... | node left _ _ _ | () | _
... | node right _ _ _ | () | _ 
lemma-dropLast-∼ (left x cl cr l⋘r) | node right x' l' r' | node left x'' l'' r'' | () | _ 
lemma-dropLast-∼ (left x cl cr l⋘r) | node right x' l' r' | node right x'' l'' r'' | () | _
lemma-dropLast-∼ (right {l} {r} x cl cr l⋙r) 
    with l | r | l⋙r
... | leaf | _ | ⋙p ()
... | node perfect x' leaf leaf | leaf | ⋙p (⋗lf .x') = ∼x /head /head ∼[]
... | node perfect x' leaf leaf | node left _ _ _ | ⋙p ()
... | node perfect x' leaf leaf | node right _ _ _ | ⋙p ()
... | node perfect x' l' r' | node perfect x'' l'' r'' | ⋙p (⋗nd .x' .x'' l'≃r' l''≃r'' l'⋗l'') = lemma++∼r (lemma-last-dropLast cl)
... | node perfect x' l' r' | node left x'' l'' r'' | ⋙l .x' .x'' l'≃r' l''⋘r'' l'⋗r'' 
    with lemma-dropLast-⋙ (⋙l x' x'' l'≃r' l''⋘r'' l'⋗r'')
... | inj₁ l⋙rd = 
                 let _l = node perfect x' l' r' ;
                      _r = node left x'' l'' r'' ;
                      zflfrd∼flzfrd = ∼x /head (lemma++/ {last _r compound} {flatten _l}) lemma-refl∼ ;
                      flzfrd∼flfr = lemma++∼l {flatten _l} (lemma-last-dropLast cr)
                 in lemma-trans∼ zflfrd∼flzfrd flzfrd∼flfr
... | inj₂ ()
lemma-dropLast-∼ (right x cl cr l⋙r) | node perfect x' l' r' | node right x'' l'' r'' | ⋙r .x' .x'' l'≃r' l''⋙r'' l'≃l'' 
    with lemma-dropLast-⋙ (⋙r x' x'' l'≃r' l''⋙r'' l'≃l'')
... | inj₁ l⋙rd =
                 let _l = node perfect x' l' r' ;
                      _r = node right x'' l'' r'' ;
                      zflfrd∼flzfrd = ∼x /head (lemma++/ {last _r compound} {flatten _l}) lemma-refl∼ ;
                      flzfrd∼flfr = lemma++∼l {flatten _l} (lemma-last-dropLast cr)
                 in lemma-trans∼ zflfrd∼flzfrd flzfrd∼flfr
... | inj₂ ()
lemma-dropLast-∼ (right x cl cr l⋙r) | node left _ _ _ | _ | ⋙p ()
lemma-dropLast-∼ (right x cl cr l⋙r) | node right _ _ _ | _ | ⋙p ()

