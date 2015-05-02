open import Relation.Binary.Core

module PLRTree.Drop.Complete {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_)  where

open import Data.Sum
open import PLRTree {A}  
open import PLRTree.Complete {A}
open import PLRTree.Compound {A}
open import PLRTree.Drop _≤_ tot≤
open import PLRTree.DropLast.Complete _≤_ tot≤
open import PLRTree.Equality {A}
open import PLRTree.Order.Properties {A}
open import PLRTree.Push.Complete _≤_ tot≤

lemma-setRoot-complete : {t : PLRTree}(x : A) → Complete t → Complete (setRoot x t)
lemma-setRoot-complete x leaf = leaf
lemma-setRoot-complete x (perfect _ cl cr l≃r) = perfect x cl cr l≃r
lemma-setRoot-complete x (left _ cl cr l⋘r) = left x cl cr l⋘r
lemma-setRoot-complete x (right _ cl cr l⋙r) = right x cl cr l⋙r

lemma-drop-complete : {t : PLRTree} → Complete t → Complete (drop t)
lemma-drop-complete leaf = leaf
lemma-drop-complete (perfect _ _ _ ≃lf) = leaf
lemma-drop-complete (perfect {node perfect x' l' r'} {node perfect x'' l'' r''} x (perfect .x' cl' cr' _) (perfect .x'' cl'' cr'' _) (≃nd .x' .x'' l'≃r' l''≃r'' l'≃l'')) = 
                 let z = last (node perfect x (node perfect x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = dropLast (node perfect x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                      ct' = right x (perfect x' cl' cr' l'≃r') (lemma-dropLast-complete (perfect x'' cl'' cr'' l''≃r'')) (lemma-dropLast-≃ (≃nd x' x'' l'≃r' l''≃r'' l'≃l'') compound) 
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
lemma-drop-complete (left {l} {r} x cl cr l⋘r)
    with l | r | l⋘r | lemma-dropLast-⋘ l⋘r
... | leaf | _ | () | _ 
... | node perfect x' l' r' | _ | () | _  
... | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | inj₁ ld⋘r  
    with dropLast (node left x' l' r') | ld⋘r | lemma-dropLast-complete cl
... | leaf | () | _
... | node perfect _ _ _ | () | _
... | node left x''' l''' r''' | ld⋘r' | cld = 
                 let z = last (node left x (node left x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node left x (node left x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = left x cld cr ld⋘r'
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
... | node right x''' l''' r''' | ld⋘r' | cld = 
                 let z = last (node left x (node left x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node left x (node right x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = left x cld cr ld⋘r'
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
lemma-drop-complete (left x cl cr l⋘r) | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | inj₂ ld≃r 
    with dropLast (node left x' l' r') | ld≃r | lemma-dropLast-complete cl
... | leaf | () | _
... | node perfect x''' l''' r''' | ld≃r' | cld = 
                 let z = last (node left x (node left x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node perfect x (node perfect x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = perfect x cld cr ld≃r'
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
... | node left _ _ _ | () | _
... | node right _ _ _ | () | _
lemma-drop-complete (left x cl cr l⋘r) | node right x' l' r' | leaf | () | _ 
lemma-drop-complete (left x cl cr l⋘r) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | inj₁ () 
lemma-drop-complete (left x cl cr l⋘r) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | inj₂ x'≃x''' = 
                 let z = last (node left x (node right x' (node perfect x'' leaf leaf) leaf) (node perfect x''' leaf leaf)) compound ;
                      t' = dropLast (node left x (node right x' (node perfect x'' leaf leaf) leaf) (node perfect x''' leaf leaf)) ;
                      ct' = perfect x (perfect x' leaf leaf ≃lf) cr x'≃x'''
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
lemma-drop-complete (left x cl cr l⋘r) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l⋙r l''≃r'' l'⋗l'' | inj₁ ld⋘r 
    with dropLast (node right x' l' r') | ld⋘r | lemma-dropLast-complete cl
... | leaf | () | _
... | node perfect _ _ _ | () | _
... | node left x''' l''' r''' | ld⋘r' | cld = 
                 let z = last (node left x (node right x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node left x (node left x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = left x cld cr ld⋘r'
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
... | node right x''' l''' r''' | ld⋘r' | cld = 
                 let z = last (node left x (node right x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node left x (node right x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = left x cld cr ld⋘r'
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
lemma-drop-complete (left x cl cr l⋘r) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l⋙r l''≃r'' l'⋗l'' | inj₂ ld≃r 
    with dropLast (node right x' l' r') | ld≃r | lemma-dropLast-complete cl
... | leaf | () | _
... | node perfect x''' l''' r''' | ld≃r' | cld = 
                 let z = last (node left x (node right x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = node perfect x (node perfect x''' l''' r''') (node perfect x'' l'' r'') ;
                      ct' = perfect x cld cr ld≃r'
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
... | node left _ _ _ | () | _
... | node right _ _ _ | () | _ 
lemma-drop-complete (left x cl cr l⋘r) | node right x' l' r' | node left x'' l'' r'' | () | _ 
lemma-drop-complete (left x cl cr l⋘r) | node right x' l' r' | node right x'' l'' r'' | () | _
lemma-drop-complete (right {l} {r} x cl cr l⋙r) 
    with l | r | l⋙r | lemma-dropLast-⋙ l⋙r
... | leaf | leaf | ⋙p () | _
... | node perfect x' leaf leaf | leaf | ⋙p (⋗lf .x') | _ = cl
... | node perfect _ _ (node _ _ _ _) | leaf | ⋙p () | _
... | node perfect _ (node _ _ _ _) _ | leaf | ⋙p () | _
... | node left _ _ _ | leaf | ⋙p () | _
... | node right _ _ _ | leaf | ⋙p () | _
... | leaf | node perfect _ _ _ | ⋙p () | _
... | node perfect x' l' r' | node perfect x'' l'' r'' | ⋙p (⋗nd .x' .x'' l'≃r' l''≃r'' l'⋗l'') | _ = 
                 let z = last (node right x (node perfect x' l' r') (node perfect x'' l'' r'')) compound ;
                      t' = dropLast (node right x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                      ct' = left x (lemma-dropLast-complete cl) cr (lemma-dropLast-⋗ (⋗nd x' x'' l'≃r' l''≃r'' l'⋗l'') compound)
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
... | node left _ _ _ | node perfect _ _ _ | ⋙p () | _
... | node right _ _ _ | node perfect _ _ _ | ⋙p () | _
... | leaf | node left _ _ _ | ⋙p () | _
... | node perfect x' l' r' | node left x'' l'' r'' | _ | inj₁ l⋙rd = 
                 let z = last (node right x (node perfect x' l' r') (node left x'' l'' r'')) compound ;
                      t' = dropLast (node right x (node perfect x' l' r') (node left x'' l'' r'')) ;
                      ct' = right x cl (lemma-dropLast-complete cr) l⋙rd
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
... | node perfect _ _ _ | node left _ _ _ | _  | inj₂ () 
... | node left _ _ _ | node left _ _ _ | ⋙p () | _
... | node right _ _ _ | node left _ _ _ | ⋙p () | _
... | leaf | node right _ _ _ | ⋙p () | _
... | node perfect x' l' r' | node right x'' l'' r'' | _ | inj₁ l⋙rd = 
                 let z = last (node right x (node perfect x' l' r') (node right x'' l'' r'')) compound ;
                      t' = dropLast (node right x (node perfect x' l' r') (node right x'' l'' r'')) ;
                      ct' = right x cl (lemma-dropLast-complete cr) l⋙rd
                 in lemma-push-complete (lemma-setRoot-complete z ct') (≺-wf (setRoot z t'))
... | node perfect _ _ _ | node right _ _ _ | _ | inj₂ ()
... | node left _ _ _ | node right _ _ _ | ⋙p () | _ 
... | node right _ _ _ | node right _ _ _ | ⋙p () | _
