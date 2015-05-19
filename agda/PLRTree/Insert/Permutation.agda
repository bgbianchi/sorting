open import Relation.Binary.Core

module PLRTree.Insert.Permutation {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) where

open import Data.List
open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum
open import List.Permutation A 
open import List.Permutation.Concatenation A 
open import List.Permutation.Equivalence A 
open import PLRTree {A} 
open import PLRTree.Complete {A} 
open import PLRTree.Compound {A} 
open import PLRTree.Insert _≤_ tot≤
open import PLRTree.Insert.Properties _≤_ tot≤

mutual
  lemma-insert-/ : {t : PLRTree}(x : A) → Complete t → ∃ (λ xs → flatten (insert x t) / x ⟶ xs ∧ xs ∼ flatten t)
  lemma-insert-/ x leaf = [] , /head , ∼[]
  lemma-insert-/ x (perfect {l} {r} y cl _ l≃r) 
      with tot≤ x y | l | r | l≃r
  ... | inj₁ x≤y | leaf | leaf | _  = y ∷ [] , /head , lemma-refl∼
  ... | inj₁ x≤y | leaf | node _ _ _ _ | () 
  ... | inj₁ x≤y | node perfect _ _ _ | leaf | ()
  ... | inj₁ x≤y | node perfect y' l' r' | node perfect y'' l'' r'' | _ = 
                  let _l = node perfect y' l' r' ;
                       _r = node perfect y'' l'' r'' ;
                       flᵢfr∼yflfr = lemma++∼r (lemma-insert-∼ y cl)
                  in flatten (insert y _l) ++ flatten _r , /head , flᵢfr∼yflfr 
  ... | inj₁ x≤y | node perfect _ _ _ | node left _ _ _ | ()
  ... | inj₁ x≤y | node perfect _ _ _ | node right _ _ _ | ()
  ... | inj₁ x≤y | node left _ _ _ | _ | () 
  ... | inj₁ x≤y | node right _ _ _ | _ | () 
  ... | inj₂ y≤x | leaf | leaf | _  = y ∷ [] , /tail /head , lemma-refl∼
  ... | inj₂ y≤x | leaf | node _ _ _ _ | ()
  ... | inj₂ y≤x | node perfect _ _ _ | leaf | ()
  ... | inj₂ y≤x | node perfect y' l' r' | node perfect y'' l'' r'' | _  
      with lemma-insert-/ x cl
  ... | xs , flᵢ/x⟶xs , xs∼fl = 
                  let _l = node perfect y' l' r' ;
                       _r = node perfect y'' l'' r'' ;
                       yflᵢfr/x⟶yxsfr = /tail (lemma++/r flᵢ/x⟶xs) ;
                       yflᵢfr∼yxsfr = ∼x /head /head (lemma++∼r xs∼fl)
                  in y ∷  xs ++ flatten _r , yflᵢfr/x⟶yxsfr , yflᵢfr∼yxsfr 
  lemma-insert-/ x (perfect y cl _ l≃r) | inj₂ y≤x | node perfect _ _ _ | node left _ _ _ | ()
  lemma-insert-/ x (perfect y cl _ l≃r) | inj₂ y≤x | node perfect _ _ _ | node right _ _ _ | ()
  lemma-insert-/ x (perfect y cl _ l≃r) | inj₂ y≤x | node left _ _ _ | _ | () 
  lemma-insert-/ x (perfect y cl _ l≃r) | inj₂ y≤x | node right _ _ _ | _ | () 
  lemma-insert-/ x (left {l} {r} y cl _ _) 
      with tot≤ x y
  ... | inj₁ x≤y 
      with insert y l | lemma-insert-∼ y cl | lemma-insert-compound y l
  ... | node perfect y' l' r' | flᵢ∼yfl | compound = 
                  let flᵢfr∼yflfr = lemma++∼r flᵢ∼yfl
                  in flatten (node perfect y' l' r') ++ flatten r , /head , flᵢfr∼yflfr 
  ... | node left y' l' r' | flᵢ∼yfl | compound = 
                  let flᵢfr∼yflfr = lemma++∼r flᵢ∼yfl
                  in flatten (node left y' l' r') ++ flatten r , /head , flᵢfr∼yflfr 
  ... | node right y' l' r' | flᵢ∼yfl | compound = 
                  let flᵢfr∼yflfr = lemma++∼r flᵢ∼yfl
                  in flatten (node right y' l' r') ++ flatten r , /head , flᵢfr∼yflfr 
  lemma-insert-/ x (left {l} {r} y cl _ _) | inj₂ y≤x 
      with insert x l | lemma-insert-/ x cl | lemma-insert-compound x l
  ... | node perfect _ _ _ | xs , flᵢ/x⟶xs , xs∼fl | compound = 
                  let yflᵢfr/x⟶yxsfr = /tail (lemma++/r flᵢ/x⟶xs) ;
                       yflᵢfr∼yxsfr = ∼x /head /head (lemma++∼r xs∼fl)
                  in y ∷  xs ++ flatten r , yflᵢfr/x⟶yxsfr , yflᵢfr∼yxsfr 
  ... | node left _ _ _ | xs , flᵢ/x⟶xs , xs∼fl | compound = 
                  let yflᵢfr/x⟶yxsfr = /tail (lemma++/r flᵢ/x⟶xs) ;
                       yflᵢfr∼yxsfr = ∼x /head /head (lemma++∼r xs∼fl)
                  in y ∷  xs ++ flatten r , yflᵢfr/x⟶yxsfr , yflᵢfr∼yxsfr 
  ... | node right _ _ _ | xs , flᵢ/x⟶xs , xs∼fl | compound = 
                  let yflᵢfr/x⟶yxsfr = /tail (lemma++/r flᵢ/x⟶xs) ;
                       yflᵢfr∼yxsfr = ∼x /head /head (lemma++∼r xs∼fl)
                  in y ∷  xs ++ flatten r , yflᵢfr/x⟶yxsfr , yflᵢfr∼yxsfr 
  lemma-insert-/ x (right {l} {r} y _ cr _) 
    with tot≤ x y 
  ... | inj₁ x≤y 
      with insert y r | lemma-insert-∼ y cr | lemma-insert-compound y r
  ... | node perfect y' l' r' | frᵢ∼yfr | compound =
                  let flfrᵢ∼flyfr = lemma++∼l {flatten l} frᵢ∼yfr ;
                       flyfr∼yflfr = ∼x (lemma++/ {y} {flatten l}) /head lemma-refl∼ ; 
                       flfrᵢ∼yflfr = lemma-trans∼ flfrᵢ∼flyfr flyfr∼yflfr  
                  in flatten l ++ flatten (node perfect y' l' r') , /head , flfrᵢ∼yflfr 
  ... | node left y' l' r' | frᵢ∼yfr | compound = 
                  let flfrᵢ∼flyfr = lemma++∼l {flatten l} frᵢ∼yfr ;
                       flyfr∼yflfr = ∼x (lemma++/ {y} {flatten l}) /head lemma-refl∼ ; 
                       flfrᵢ∼yflfr = lemma-trans∼ flfrᵢ∼flyfr flyfr∼yflfr  
                  in flatten l ++ flatten (node left y' l' r') , /head , flfrᵢ∼yflfr 
  ... | node right y' l' r' | frᵢ∼yfr | compound = 
                  let flfrᵢ∼flyfr = lemma++∼l {flatten l} frᵢ∼yfr ;
                       flyfr∼yflfr = ∼x (lemma++/ {y} {flatten l}) /head lemma-refl∼ ; 
                       flfrᵢ∼yflfr = lemma-trans∼ flfrᵢ∼flyfr flyfr∼yflfr  
                  in flatten l ++ flatten (node right y' l' r') , /head , flfrᵢ∼yflfr 
  lemma-insert-/ x (right {l} {r} y _ cr _) | inj₂ y≤x 
      with insert x r | lemma-insert-/ x cr | lemma-insert-compound x r
  ... | node perfect y' l' r' | xs , frᵢ/x⟶xs , xs∼fr | compound = 
                  let yflfrᵢ/x⟶yflxs = /tail (lemma++/l {x} {flatten l} frᵢ/x⟶xs) ;
                       yflfrᵢ∼yflxs = ∼x /head /head (lemma++∼l {flatten l} xs∼fr)
                  in y ∷  flatten l ++ xs , yflfrᵢ/x⟶yflxs , yflfrᵢ∼yflxs 
  ... | node left y' l' r' | xs , frᵢ/x⟶xs , xs∼fr | compound = 
                  let yflfrᵢ/x⟶yflxs = /tail (lemma++/l {x} {flatten l} frᵢ/x⟶xs) ;
                       yflfrᵢ∼yflxs = ∼x /head /head (lemma++∼l {flatten l} xs∼fr)
                  in y ∷  flatten l ++ xs , yflfrᵢ/x⟶yflxs , yflfrᵢ∼yflxs 
  ... | node right y' l' r' | xs , frᵢ/x⟶xs , xs∼fr | compound = 
                  let yflfrᵢ/x⟶yflxs = /tail (lemma++/l {x} {flatten l} frᵢ/x⟶xs) ;
                       yflfrᵢ∼yflxs = ∼x /head /head (lemma++∼l {flatten l} xs∼fr)
                  in y ∷  flatten l ++ xs , yflfrᵢ/x⟶yflxs , yflfrᵢ∼yflxs 

  lemma-insert-∼ : {t : PLRTree}(x : A) → Complete t → flatten (insert x t) ∼ (x ∷ flatten t)
  lemma-insert-∼ x leaf = ∼x /head /head ∼[]
  lemma-insert-∼ x (perfect {l} {r} y cl _ l≃r) 
      with tot≤ x y | l | r | l≃r
  ... | inj₁ x≤y | leaf | leaf | _  = ∼x /head /head (∼x /head /head ∼[])
  ... | inj₁ x≤y | leaf | node _ _ _ _ | () 
  ... | inj₁ x≤y | node perfect _ _ _ | leaf | ()
  ... | inj₁ x≤y | node perfect _ _ _ | node perfect _ _ _ | _  = 
                  let flᵢfr∼yflfr = lemma++∼r (lemma-insert-∼ y cl)
                  in ∼x /head /head flᵢfr∼yflfr
  ... | inj₁ x≤y | node perfect _ _ _ | node left _ _ _ | ()
  ... | inj₁ x≤y | node perfect _ _ _ | node right _ _ _ | ()
  ... | inj₁ x≤y | node left _ _ _ | _ | () 
  ... | inj₁ x≤y | node right _ _ _ | _ | () 
  ... | inj₂ y≤x | leaf | leaf | _  = ∼x /head (/tail /head) (∼x /head /head ∼[])
  ... | inj₂ y≤x | leaf | node _ _ _ _ | ()
  ... | inj₂ y≤x | node perfect _ _ _ | leaf | ()
  ... | inj₂ y≤x | node perfect _ _ _ | node perfect _ _ _ | _  
      with lemma-insert-/ x cl 
  ... | xs , flᵢ/x⟶xs , xs∼fl =
                  let yflᵢfr/x⟶yxsfr = /tail (lemma++/r flᵢ/x⟶xs) ;
                       yxsfr∼yflfr = ∼x /head /head (lemma++∼r xs∼fl)
                  in ∼x yflᵢfr/x⟶yxsfr /head yxsfr∼yflfr
  lemma-insert-∼ x (perfect y cl _ l≃r) | inj₂ y≤x | node perfect _ _ _ | node left _ _ _ | ()
  lemma-insert-∼ x (perfect y cl _ l≃r) | inj₂ y≤x | node perfect _ _ _ | node right _ _ _ | ()
  lemma-insert-∼ x (perfect y cl _ l≃r) | inj₂ y≤x | node left _ _ _ | _ | () 
  lemma-insert-∼ x (perfect y cl _ l≃r) | inj₂ y≤x | node right _ _ _ | _ | () 
  lemma-insert-∼ x (left {l} {r} y cl _ _) 
      with tot≤ x y
  ... | inj₁ x≤y 
      with insert y l | lemma-insert-∼ y cl | lemma-insert-compound y l
  ... | node perfect _ _ _ | flᵢ∼yfl | compound = 
                  let flᵢfr∼yflfr = lemma++∼r flᵢ∼yfl
                  in ∼x /head /head flᵢfr∼yflfr 
  ... | node left _ _ _ | flᵢ∼yfl | compound = 
                  let flᵢfr∼yflfr = lemma++∼r flᵢ∼yfl
                  in ∼x /head /head flᵢfr∼yflfr 
  ... | node right _ _ _ | flᵢ∼yfl | compound = 
                  let flᵢfr∼yflfr = lemma++∼r flᵢ∼yfl
                  in ∼x /head /head flᵢfr∼yflfr 
  lemma-insert-∼ x (left {l} {r} y cl _ _) | inj₂ y≤x 
      with insert x l | lemma-insert-/ x cl | lemma-insert-compound x l
  ... | node perfect _ _ _ | xs , flᵢ/x⟶xs , xs∼fl | compound = 
                  let yflᵢfr/x⟶yxsfr = /tail (lemma++/r flᵢ/x⟶xs) ;
                       yxsfr∼yflfr = ∼x /head /head (lemma++∼r xs∼fl)
                  in ∼x yflᵢfr/x⟶yxsfr /head yxsfr∼yflfr
  ... | node left _ _ _ | xs , flᵢ/x⟶xs , xs∼fl | compound = 
                  let yflᵢfr/x⟶yxsfr = /tail (lemma++/r flᵢ/x⟶xs) ;
                       yxsfr∼yflfr = ∼x /head /head (lemma++∼r xs∼fl)
                  in ∼x yflᵢfr/x⟶yxsfr /head yxsfr∼yflfr
  ... | node right _ _ _ | xs , flᵢ/x⟶xs , xs∼fl | compound = 
                  let yflᵢfr/x⟶yxsfr = /tail (lemma++/r flᵢ/x⟶xs) ;
                       yxsfr∼yflfr = ∼x /head /head (lemma++∼r xs∼fl)
                  in ∼x yflᵢfr/x⟶yxsfr /head yxsfr∼yflfr
  lemma-insert-∼ x (right {l} {r} y _ cr _) 
      with tot≤ x y 
  ... | inj₁ x≤y 
      with insert y r | lemma-insert-∼ y cr | lemma-insert-compound y r
  ... | node perfect _ _ _ | frᵢ∼yfr | compound = 
                  let flyfr∼yflfr = ∼x (lemma++/ {y} {flatten l}) /head lemma-refl∼ ;
                       flfrᵢ∼flyfr = lemma++∼l {flatten l} frᵢ∼yfr ;
                       flfrᵢ∼yflfr = lemma-trans∼ flfrᵢ∼flyfr flyfr∼yflfr
                  in ∼x /head /head flfrᵢ∼yflfr
  ... | node left _ _ _ | frᵢ∼yfr | compound = 
                  let flyfr∼yflfr = ∼x (lemma++/ {y} {flatten l}) /head lemma-refl∼ ;
                       flfrᵢ∼flyfr = lemma++∼l {flatten l} frᵢ∼yfr ;
                       flfrᵢ∼yflfr = lemma-trans∼ flfrᵢ∼flyfr flyfr∼yflfr
                  in ∼x /head /head flfrᵢ∼yflfr
  ... | node right _ _ _ | frᵢ∼yfr | compound = 
                  let flyfr∼yflfr = ∼x (lemma++/ {y} {flatten l}) /head lemma-refl∼ ;
                       flfrᵢ∼flyfr = lemma++∼l {flatten l} frᵢ∼yfr ;
                       flfrᵢ∼yflfr = lemma-trans∼ flfrᵢ∼flyfr flyfr∼yflfr
                  in ∼x /head /head flfrᵢ∼yflfr
  lemma-insert-∼ x (right {l} {r} y _ cr _) | inj₂ y≤x 
      with insert x r | lemma-insert-/ x cr | lemma-insert-compound x r
  ... | node perfect y' l' r' | xs , frᵢ/x⟶xs , xs∼fr | compound = 
                  let yflfrᵢ/x⟶yflxs = /tail (lemma++/l {x} {flatten l} frᵢ/x⟶xs) ;
                       yflxs∼yflfr = ∼x /head /head (lemma++∼l {flatten l} xs∼fr)
                  in ∼x yflfrᵢ/x⟶yflxs /head yflxs∼yflfr
  ... | node left y' l' r' | xs , frᵢ/x⟶xs , xs∼fr | compound = 
                  let yflfrᵢ/x⟶yflxs = /tail (lemma++/l {x} {flatten l} frᵢ/x⟶xs) ;
                       yflxs∼yflfr = ∼x /head /head (lemma++∼l {flatten l} xs∼fr)
                  in ∼x yflfrᵢ/x⟶yflxs /head yflxs∼yflfr
  ... | node right y' l' r' | xs , frᵢ/x⟶xs , xs∼fr | compound = 
                  let yflfrᵢ/x⟶yflxs = /tail (lemma++/l {x} {flatten l} frᵢ/x⟶xs) ;
                       yflxs∼yflfr = ∼x /head /head (lemma++∼l {flatten l} xs∼fr)
                  in ∼x yflfrᵢ/x⟶yflxs /head yflxs∼yflfr

