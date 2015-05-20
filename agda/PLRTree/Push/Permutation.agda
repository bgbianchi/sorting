open import Relation.Binary.Core

module PLRTree.Push.Permutation {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) where

open import Data.List
open import Data.Sum
open import Induction.WellFounded
open import List.Permutation.Base A 
open import List.Permutation.Base.Concatenation A 
open import List.Permutation.Base.Equivalence A 
open import PLRTree {A} 
open import PLRTree.Complete {A} 
open import PLRTree.Drop _≤_ tot≤
open import PLRTree.Equality {A}
open import PLRTree.Order {A}
open import PLRTree.Order.Properties {A}

lemma-push-∼-≃ : {l r : PLRTree}(x : A) → Complete l → Complete r → l ≃ r → (acc : Acc _≺_ (node perfect x l r)) → flatten (push (node perfect x l r) acc) ∼ flatten (node right x l r)
lemma-push-∼-≃ {l} {r} x cl cr l≃r (acc rs) 
    with l | r | l≃r | cl | cr
... | leaf | leaf | ≃lf | _ | _ = ∼x /head /head ∼[]
... | node perfect x' l' r' | node perfect x'' l'' r'' | ≃nd .x' .x'' l'≃r' l''≃r'' l'≃l'' | perfect .x' cl' cr' _ | perfect .x'' cl'' cr'' _
    with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
... | inj₁ x≤x' | inj₁ x≤x'' | _ = lemma-refl∼
... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let _l = node perfect x' l' r' ;
                  acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right perfect x _l (node perfect x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-≃ x cl'' cr'' l''≃r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr
... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height perfect x x' l' r' = 
             let _r = node perfect x'' l'' r'' ;
                  acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left perfect x (node perfect x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-≃ x cl' cr' l'≃r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height perfect x x' l' r' = 
             let _r = node perfect x'' l'' r'' ;
                  acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left perfect x (node perfect x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-≃ x cl' cr' l'≃r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let _l = node perfect x' l' r' ;
                  acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right perfect x _l (node perfect x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-≃ x cl'' cr'' l''≃r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr

lemma-push-∼-⋗ : {l r : PLRTree}(x : A) → Complete l → Complete r → l ⋗ r → (acc : Acc _≺_ (node right x l r)) → flatten (push (node right x l r) acc) ∼ flatten (node right x l r)
lemma-push-∼-⋗ {l} {r} x cl cr l⋗r (acc rs) 
    with l | r | l⋗r | cl | cr
... | leaf | _ | () | _ | _
... | node perfect x' leaf leaf | leaf | ⋗lf .x' | perfect .x' leaf leaf ≃lf | leaf 
    with tot≤ x x'
... | inj₁ x≤x' = ∼x /head /head (∼x /head /head ∼[])
... | inj₂ x'≤x = ∼x (/tail /head) /head (∼x /head /head ∼[])
lemma-push-∼-⋗ x cl cr l⋗r (acc rs) | node perfect x' l' r' | node perfect x'' l'' r'' | ⋗nd .x' .x'' l'≃r' l''≃r'' l'⋗l'' | perfect .x' cl' cr' _ | perfect .x'' cl'' cr'' _
    with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
... | inj₁ x≤x' | inj₁ x≤x'' | _ = lemma-refl∼
... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let _l = node perfect x' l' r' ;
                  acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right perfect x _l (node perfect x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-≃ x cl'' cr'' l''≃r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr
... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height perfect x x' l' r' =  
             let _r = node perfect x'' l'' r'' ;
                  acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left perfect x (node perfect x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-≃ x cl' cr' l'≃r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height perfect x x' l' r' = 
             let _r = node perfect x'' l'' r'' ;
                  acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left perfect x (node perfect x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-≃ x cl' cr' l'≃r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let _l = node perfect x' l' r' ;
                  acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right perfect x _l (node perfect x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-≃ x cl'' cr'' l''≃r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr

mutual
  lemma-push-∼-⋙ : {l r : PLRTree}(x : A) → Complete l → Complete r → l ⋙ r → (acc : Acc _≺_ (node right x l r)) → flatten (push (node right x l r) acc) ∼ flatten (node right x l r)
  lemma-push-∼-⋙ {l} {r} x cl cr l⋙r (acc rs) 
      with l | r | l⋙r | cl | cr
  ... | leaf | _ | ⋙p () | _ | _
  ... | node perfect x' leaf leaf | leaf | ⋙p (⋗lf .x') | perfect .x' leaf leaf ≃lf | leaf = lemma-push-∼-⋗ x (perfect x' leaf leaf ≃lf) leaf (⋗lf x') (acc rs)
  ... | node perfect x' l' r' | node perfect x'' l'' r'' | ⋙p (⋗nd .x' .x'' l'≃r' l''≃r'' l'⋗l'') | perfect .x' cl' cr' _ | perfect .x'' cl'' cr'' _ = 
             lemma-push-∼-⋗ x (perfect x' cl' cr' l'≃r') (perfect x'' cl'' cr'' l''≃r'') (⋗nd x' x'' l'≃r' l''≃r'' l'⋗l'') (acc rs)
  ... | node perfect x' leaf leaf | node left _ _ _ | ⋙p () | _ | _ 
  ... | node perfect x' leaf leaf | node right _ _ _ | ⋙p () | _ | _
  ... | node perfect x' l' r' | node left x'' l'' r'' | ⋙l .x' .x'' l'≃r' l''⋘r'' l'⋗r'' | perfect .x' cl' cr' _ | left .x'' cl'' cr'' _ 
      with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
  ... | inj₁ x≤x' | inj₁ x≤x'' | _ = lemma-refl∼
  ... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height left x x'' l'' r'' = 
             let _l = node perfect x' l' r' ;
                  acc-xl''r'' = rs (node left x l'' r'') (lemma-≺-right perfect x _l (node left x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-⋘ x cl'' cr'' l''⋘r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr
  ... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height perfect x x' l' r' = 
             let _r = node left x'' l'' r'' ;
                  acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left perfect x (node perfect x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-≃ x cl' cr' l'≃r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height perfect x x' l' r' = 
             let _r = node left x'' l'' r'' ;
                  acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left perfect x (node perfect x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-≃ x cl' cr' l'≃r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height left x x'' l'' r'' = 
             let _l = node perfect x' l' r' ;
                  acc-xl''r'' = rs (node left x l'' r'') (lemma-≺-right perfect x _l (node left x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-⋘ x cl'' cr'' l''⋘r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr
  lemma-push-∼-⋙ x cl cr l⋙r (acc rs)| node perfect x' l' r' | node right x'' l'' r'' | ⋙r .x' .x'' l'≃r' l''⋙r'' l'≃l'' | perfect .x' cl' cr' _ | right .x'' cl'' cr'' _ 
      with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
  ... | inj₁ x≤x' | inj₁ x≤x'' | _ = lemma-refl∼
  ... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height right x x'' l'' r'' = 
             let _l = node perfect x' l' r' ;
                  acc-xl''r'' = rs (node right x l'' r'') (lemma-≺-right perfect x _l (node right x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-⋙ x cl'' cr'' l''⋙r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr
  ... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height perfect x x' l' r' = 
             let _r = node right x'' l'' r'' ;
                  acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left perfect x (node perfect x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-≃ x cl' cr' l'≃r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height perfect x x' l' r' = 
             let _r = node right x'' l'' r'' ;
                  acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left perfect x (node perfect x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-≃ x cl' cr' l'≃r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height right x x'' l'' r'' = 
             let _l = node perfect x' l' r' ;
                  acc-xl''r'' = rs (node right x l'' r'') (lemma-≺-right perfect x _l (node right x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-⋙ x cl'' cr'' l''⋙r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr
  lemma-push-∼-⋙ x cl cr l⋙r (acc rs) | node left _ _ _ | _ | ⋙p () | _ | _
  lemma-push-∼-⋙ x cl cr l⋙r (acc rs) | node right _ _ _ | _ | ⋙p () | _ | _

  lemma-push-∼-⋘ : {l r : PLRTree}(x : A) → Complete l → Complete r → l ⋘ r → (acc : Acc _≺_ (node left x l r)) → flatten (push (node left x l r) acc) ∼ flatten (node left x l r)
  lemma-push-∼-⋘ {l} {r} x cl cr l⋘r (acc rs) 
      with l | r | l⋘r | cl | cr
  ... | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | left .x' cl' cr' _ | perfect .x'' cl'' cr'' _ 
      with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
  ... | inj₁ x≤x' | inj₁ x≤x'' | _ = lemma-refl∼
  ... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let _l = node left x' l' r' ;
                  acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right perfect x _l (node perfect x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-≃ x cl'' cr'' l''≃r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr
  ... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height left x x' l' r' = 
             let _r = node perfect x'' l'' r'' ;
                  acc-xl'r' = rs (node left x l' r') (lemma-≺-left perfect x (node left x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-⋘ x cl' cr' l'⋘r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height left x x' l' r' = 
             let _r = node perfect x'' l'' r'' ;
                  acc-xl'r' = rs (node left x l' r') (lemma-≺-left perfect x (node left x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-⋘ x cl' cr' l'⋘r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let _l = node left x' l' r' ;
                  acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right perfect x _l (node perfect x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-≃ x cl'' cr'' l''≃r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr
  lemma-push-∼-⋘ x cl cr l⋘r (acc rs) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | right .x' (perfect .x'' leaf leaf ≃lf) leaf (⋙p (⋗lf .x'')) | perfect .x''' leaf leaf ≃lf  
      with tot≤ x x' | tot≤ x x''' | tot≤ x' x'''
  ... | inj₁ x≤x' | inj₁ x≤x''' | _ = lemma-refl∼
  ... | inj₁ x≤x' | inj₂ x'''≤x | _ = 
             let _l = node perfect x' (node perfect x'' leaf leaf) leaf ;
                  acc-x = rs (node perfect x leaf leaf) (lemma-≺-right perfect x _l (node perfect x''' leaf leaf)) ;
                  x'''flfpx∼x'''flx = lemma++∼l {x''' ∷ flatten _l} (lemma-push-∼-≃ x leaf leaf ≃lf acc-x) ;
                  flxfr/x'''⟶flx = lemma++/l {x'''} {flatten _l} (/tail /head) ;
                  x'''flx∼flxfr = ∼x /head flxfr/x'''⟶flx lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x'''flx∼xflfr = lemma-trans∼ x'''flx∼flxfr flxfr∼xflfr
             in lemma-trans∼ x'''flfpx∼x'''flx x'''flx∼xflfr
  ... | inj₂ x'≤x | inj₁ x≤x''' | _ = 
             let _r = node perfect x''' leaf leaf ;
                  acc-xx'' = rs (node right x (node perfect x'' leaf leaf) leaf) (lemma-≺-left perfect x (node right x' (node perfect x'' leaf leaf) leaf) _r) ;
                  fpxx''x'''∼xx''x''' = lemma++∼r (lemma-push-∼-⋗ x (perfect x'' leaf leaf ≃lf) leaf (⋗lf x'') acc-xx'') ;
                  x'fpxx''x'''∼x'xx''x''' = ∼x /head /head fpxx''x'''∼xx''x''' ;
                  x'xx''x'''∼xx'x''x''' = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxx''x'''∼x'xx''x''' x'xx''x'''∼xx'x''x'''
  ... | inj₂ x'≤x | inj₂ x'''≤x | inj₁ x'≤x''' = 
             let _r = node perfect x''' leaf leaf ;
                  acc-xx'' = rs (node right x (node perfect x'' leaf leaf) leaf) (lemma-≺-left perfect x (node right x' (node perfect x'' leaf leaf) leaf) _r) ;
                  fpxx''x'''∼xx''x''' = lemma++∼r (lemma-push-∼-⋗ x (perfect x'' leaf leaf ≃lf) leaf (⋗lf x'') acc-xx'') ;
                  x'fpxx''x'''∼x'xx''x''' = ∼x /head /head fpxx''x'''∼xx''x''' ;
                  x'xx''x'''∼xx'x''x''' = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxx''x'''∼x'xx''x''' x'xx''x'''∼xx'x''x'''
  ... | inj₂ x'≤x | inj₂ x'''≤x | inj₂ x'''≤x' = 
             let _l = node perfect x' (node perfect x'' leaf leaf) leaf ;
                  acc-x = rs (node perfect x leaf leaf) (lemma-≺-right perfect x _l (node perfect x''' leaf leaf)) ;
                  x'''flfpx∼x'''flx = lemma++∼l {x''' ∷ flatten _l} (lemma-push-∼-≃ x leaf leaf ≃lf acc-x) ;
                  flxfr/x'''⟶flx = lemma++/l {x'''} {flatten _l} (/tail /head) ;
                  x'''flx∼flxfr = ∼x /head flxfr/x'''⟶flx lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x'''flx∼xflfr = lemma-trans∼ x'''flx∼flxfr flxfr∼xflfr
             in lemma-trans∼ x'''flfpx∼x'''flx x'''flx∼xflfr
  lemma-push-∼-⋘ x cl cr l⋘r (acc rs) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l'⋙r' l''≃r'' l'⋗l'' | right .x' cl' cr' _ | perfect .x'' cl'' cr'' _  
      with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
  ... | inj₁ x≤x' | inj₁ x≤x'' | _ = lemma-refl∼
  ... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let _l = node right x' l' r' ;
                  acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right perfect x _l (node perfect x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-≃ x cl'' cr'' l''≃r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr
  ... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height right x x' l' r' = 
             let _r = node perfect x'' l'' r'' ;
                  acc-xl'r' = rs (node right x l' r') (lemma-≺-left perfect x (node right x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-⋙ x cl' cr' l'⋙r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height right x x' l' r' = 
             let _r = node perfect x'' l'' r'' ;
                  acc-xl'r' = rs (node right x l' r') (lemma-≺-left perfect x (node right x' l' r') _r) ;
                  fpxl'r'fr∼xfl'fr'fr = lemma++∼r (lemma-push-∼-⋙ x cl' cr' l'⋙r' acc-xl'r') ;
                  x'fpxl'r'fr∼x'xfl'fr'fr = ∼x /head /head fpxl'r'fr∼xfl'fr'fr ;
                  x'xfl'fr'fr∼xflfr = ∼x /head (/tail /head) lemma-refl∼
             in lemma-trans∼ x'fpxl'r'fr∼x'xfl'fr'fr x'xfl'fr'fr∼xflfr
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let _l = node right x' l' r' ;
                  acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right perfect x _l (node perfect x'' l'' r'')) ;
                  x''flfpxl''r''∼x''flxfl''fr'' = lemma++∼l {x'' ∷ flatten _l} (lemma-push-∼-≃ x cl'' cr'' l''≃r'' acc-xl''r'') ;
                  flxfr/x''⟶flxfl''fr'' = lemma++/l {x''} {flatten _l} (/tail /head) ;
                  x''flxfl''fr''∼flxfr = ∼x /head flxfr/x''⟶flxfl''fr'' lemma-refl∼ ; 
                  flxfr/x⟶flfr = lemma++/ {x} {flatten _l} ;
                  flxfr∼xflfr = ∼x flxfr/x⟶flfr /head lemma-refl∼ ; 
                  x''flxfl''fr''∼xflfr = lemma-trans∼ x''flxfl''fr''∼flxfr flxfr∼xflfr
             in lemma-trans∼ x''flfpxl''r''∼x''flxfl''fr'' x''flxfl''fr''∼xflfr

lemma-push-∼ : {t : PLRTree} → Complete t → (acc : Acc _≺_ t) → flatten (push t acc) ∼ flatten t
lemma-push-∼ leaf _ = ∼[]
lemma-push-∼ (perfect {l} {r}x cl cr l≃r) (acc rs) = lemma-push-∼-≃ x cl cr l≃r (acc rs)
lemma-push-∼ (left {l} {r}x cl cr l⋘r) (acc rs) = lemma-push-∼-⋘ x cl cr l⋘r (acc rs)
lemma-push-∼ (right {l} {r}x cl cr l⋙r) (acc rs) = lemma-push-∼-⋙ x cl cr l⋙r (acc rs)

