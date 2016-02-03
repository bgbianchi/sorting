open import Relation.Binary.Core

module PLRTree.Drop.Permutation {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) where

open import Data.List hiding (drop)
open import Data.Sum
open import List.Permutation.Base A 
open import List.Permutation.Base.Equivalence A 
open import PLRTree {A} 
open import PLRTree.Complete {A} 
open import PLRTree.Compound {A} 
open import PLRTree.Drop _≤_ tot≤
open import PLRTree.Drop.Complete _≤_ tot≤
open import PLRTree.DropLast.Complete _≤_ tot≤
open import PLRTree.DropLast.Permutation _≤_ tot≤
open import PLRTree.Equality {A} 
open import PLRTree.Order.Properties {A} 
open import PLRTree.Push.Permutation _≤_ tot≤

lemma-drop-++ : {t : Tag}{x : A}{l r : PLRTree} → Complete (node t x l r) → flatten (drop (node t x l r)) ∼ (flatten l ++ flatten r)
lemma-drop-++ (perfect {leaf} {leaf} x leaf leaf ≃lf) = ∼[]
lemma-drop-++ (perfect {node perfect x' l' r'} {node perfect x'' l'' r''} x cl cr (≃nd .x' .x'' l'≃r' l''≃r'' l'≃l'')) = 
                 let _l = node perfect x' l' r' ;
                      _r = node perfect x'' l'' r'' ;
                      _l≃r = ≃nd x' x'' l'≃r' l''≃r'' l'≃l'' ;
                      cxlr = perfect x cl cr _l≃r ;
                      z = last (node perfect x _l _r) compound ;
                      t' = dropLast (node perfect x _l _r) ;
                      ct' = right x cl (lemma-dropLast-complete cr) (lemma-dropLast-≃ _l≃r compound) 
                 in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))) (lemma-dropLast-∼ cxlr)
lemma-drop-++ (left {l} {r} x cl cr l⋘r) 
    with l | r | l⋘r | lemma-dropLast-⋘ l⋘r
... | leaf | _ | () | _ 
... | node perfect x' l' r' | _ | () | _  
... | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | inj₁ ld⋘r  
    with dropLast (node left x' l' r') | ld⋘r | lemma-dropLast-complete cl | lemma-dropLast-∼ (left x cl cr (l⋘ x' x'' l'⋘r' l''≃r'' r'≃l''))
... | leaf | () | _ | _
... | node perfect _ _ _ | () | _ | _ 
... | node left x''' l''' r''' | ld⋘r' | cld | fzt'∼flfr = 
                 let z = last (node left x (node left x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node left x (node left x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = left x cld cr ld⋘r'
                 in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))) fzt'∼flfr
... | node right x''' l''' r''' | ld⋘r' | cld | fzt'∼flfr = 
                 let z = last (node left x (node left x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node left x (node right x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = left x cld cr ld⋘r'
                 in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))) fzt'∼flfr
lemma-drop-++ (left x cl cr l⋘r) | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | inj₂ ld≃r 
    with dropLast (node left x' l' r') | ld≃r | lemma-dropLast-complete cl | lemma-dropLast-∼ (left x cl cr (l⋘ x' x'' l'⋘r' l''≃r'' r'≃l''))
... | leaf | () | _ | _
... | node perfect x''' l''' r''' | ld≃r' | cld | fzt'∼flfr = 
                 let z = last (node left x (node left x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node perfect x (node perfect x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = perfect x cld cr ld≃r'
                 in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))) fzt'∼flfr
... | node left _ _ _ | () | _ | _
... | node right _ _ _ | () | _ | _
lemma-drop-++ (left x cl cr l⋘r) | node right x' l' r' | leaf | () | _ 
lemma-drop-++ (left x cl cr l⋘r) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | inj₁ () 
lemma-drop-++ (left x cl cr l⋘r) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | inj₂ x'≃x''' =
                 let z = last (node left x (node right x' (node perfect x'' leaf leaf) leaf) (node perfect x''' leaf leaf)) compound ;
                      t' = dropLast (node left x (node right x' (node perfect x'' leaf leaf) leaf) (node perfect x''' leaf leaf)) ;
                      ct' = perfect x (perfect x' leaf leaf ≃lf) cr x'≃x''' ;
                      fzt'∼flfr = lemma-dropLast-∼ (left x cl cr (x⋘ x' x'' x'''))
                 in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t')))  fzt'∼flfr
lemma-drop-++ (left x cl cr l⋘r) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l⋙r l''≃r'' l'⋗l'' | inj₁ ld⋘r 
    with dropLast (node right x' l' r') | ld⋘r | lemma-dropLast-complete cl | lemma-dropLast-∼ (left x cl cr (r⋘ x' x'' l⋙r l''≃r'' l'⋗l''))
... | leaf | () | _ | _
... | node perfect _ _ _ | () | _ | _
... | node left x''' l''' r''' | ld⋘r' | cld | fzt'∼flfr = 
                 let z = last (node left x (node right x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node left x (node left x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = left x cld cr ld⋘r'
                  in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t')))  fzt'∼flfr
... | node right x''' l''' r''' | ld⋘r' | cld | fzt'∼flfr = 
                 let z = last (node left x (node right x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node left x (node right x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = left x cld cr ld⋘r'
                 in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t')))  fzt'∼flfr
lemma-drop-++ (left x cl cr l⋘r) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l⋙r l''≃r'' l'⋗l'' | inj₂ ld≃r 
    with dropLast (node right x' l' r') | ld≃r | lemma-dropLast-complete cl | lemma-dropLast-∼ (left x cl cr (r⋘ x' x'' l⋙r l''≃r'' l'⋗l''))
... | leaf | () | _ | _
... | node perfect x''' l''' r''' | ld≃r' | cld | fzt'∼flfr = 
                 let z = last (node left x (node right x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node perfect x (node perfect x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = perfect x cld cr ld≃r'
                 in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t')))  fzt'∼flfr
... | node left _ _ _ | () | _ | _
... | node right _ _ _ | () | _ | _
lemma-drop-++ (left x cl cr l⋘r) | node right x' l' r' | node left x'' l'' r'' | () | _ 
lemma-drop-++ (left x cl cr l⋘r) | node right x' l' r' | node right x'' l'' r'' | () | _
lemma-drop-++ (right {l} {r} x cl cr l⋙r)  
    with l | r | l⋙r | lemma-dropLast-⋙ l⋙r
... | leaf | leaf | ⋙p () | _
... | node perfect x' leaf leaf | leaf | ⋙p (⋗lf .x') | _ = ∼x /head /head ∼[] 
... | node perfect _ _ (node _ _ _ _) | leaf | ⋙p () | _
... | node perfect _ (node _ _ _ _) _ | leaf | ⋙p () | _
... | node left _ _ _ | leaf | ⋙p () | _
... | node right _ _ _ | leaf | ⋙p () | _
... | leaf | node perfect _ _ _ | ⋙p () | _
... | node perfect x' l' r' | node perfect x'' l'' r'' | ⋙p (⋗nd .x' .x'' l'≃r' l''≃r'' l'⋗l'') | _ =
                 let z = last (node right x (node perfect x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = dropLast (node right x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                      ct' = left x (lemma-dropLast-complete cl) cr (lemma-dropLast-⋗ (⋗nd x' x'' l'≃r' l''≃r'' l'⋗l'') compound) ;
                      fzt'∼flfr = lemma-dropLast-∼ (right x cl cr (⋙p (⋗nd x' x'' l'≃r' l''≃r'' l'⋗l'')))
                 in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t')))  fzt'∼flfr
... | node left _ _ _ | node perfect _ _ _ | ⋙p () | _
... | node right _ _ _ | node perfect _ _ _ | ⋙p () | _
... | leaf | node left _ _ _ | ⋙p () | _
... | node perfect x' l' r' | node left x'' l'' r'' | _l⋙r | inj₁ l⋙rd = 
                 let z = last (node right x (node perfect x' l' r') (node left x'' l'' r'')) compound ;
                      t' = dropLast (node right x (node perfect x' l' r') (node left x'' l'' r'')) ;
                      ct' = right x cl (lemma-dropLast-complete cr) l⋙rd ;
                      fzt'∼flfr = lemma-dropLast-∼ (right x cl cr _l⋙r)
                 in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t')))  fzt'∼flfr
... | node perfect _ _ _ | node left _ _ _ | _  | inj₂ () 
... | node left _ _ _ | node left _ _ _ | ⋙p () | _
... | node right _ _ _ | node left _ _ _ | ⋙p () | _
... | leaf | node right _ _ _ | ⋙p () | _
... | node perfect x' l' r' | node right x'' l'' r'' | _l⋙r | inj₁ l⋙rd = 
                 let z = last (node right x (node perfect x' l' r') (node right x'' l'' r'')) compound ;
                      t' = dropLast (node right x (node perfect x' l' r') (node right x'' l'' r'')) ;
                      ct' = right x cl (lemma-dropLast-complete cr) l⋙rd ;
                      fzt'∼flfr = lemma-dropLast-∼ (right x cl cr _l⋙r)
                 in trans∼ (lemma-push-∼ (lemma-setRoot-complete z ct') (≺-wf (setRoot z t')))  fzt'∼flfr
... | node perfect _ _ _ | node right _ _ _ | _ | inj₂ ()
... | node left _ _ _ | node right _ _ _ | ⋙p () | _ 
... | node right _ _ _ | node right _ _ _ | ⋙p () | _

lemma-drop-∼ : {t : Tag}{x : A}{l r : PLRTree} → Complete (node t x l r) → (x ∷ flatten (drop (node t x l r))) ∼ flatten (node t x l r)
lemma-drop-∼ (perfect x cl cr l≃r) = ∼x /head /head (lemma-drop-++ (perfect x cl cr l≃r))
lemma-drop-∼ (left x cl cr l⋘r) = ∼x /head /head (lemma-drop-++ (left x cl cr l⋘r))
lemma-drop-∼ (right x cl cr l⋙r) = ∼x /head /head (lemma-drop-++ (right x cl cr l⋙r))


