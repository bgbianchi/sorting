open import Relation.Binary.Core

module PLRTree.Push.Complete {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_)  where

open import Data.Sum 
open import Induction.WellFounded
open import PLRTree {A}  
open import PLRTree.Drop _≤_ tot≤
open import PLRTree.Complete {A}
open import PLRTree.Equality {A}
open import PLRTree.Equality.Properties {A}
open import PLRTree.Order {A}
open import PLRTree.Order.Properties {A}

mutual 
  lemma-≃-push : {t t' : PLRTree} → t ≃ t' → (acc : Acc _≺_ t) → t ≃ push t acc
  lemma-≃-push ≃lf _ = ≃lf
  lemma-≃-push (≃nd x x' ≃lf ≃lf ≃lf) _ = ≃nd x x ≃lf ≃lf ≃lf
  lemma-≃-push (≃nd x x' (≃nd {l₁} {r₁} {l₂} {r₂} x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) l'≃r' (≃nd .x₁ x'₁ _ l'₁≃r'₁ l₁≃l'₁)) (acc rs) 
      with tot≤ x x₁ | tot≤ x x₂ | tot≤ x₁ x₂
  ... | inj₁ x≤x₁ | inj₁ x≤x₂ | _ = 
             let l₁≃l₁ = lemma-≃-≃ l₁≃r₁
             in ≃nd x x (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) (≃nd x₁ x₁ l₁≃r₁ l₁≃r₁ l₁≃l₁)
  ... | inj₁ x≤x₁ | inj₂ x₂≤x | _ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  push-xl₁r₁≃x₂l₂r₂ = lemma-≃-push  (sym≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂)) acc-xl₂r₂ ;
                  x₁l₁r₁≃push-xl₂r₂ = trans≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂) push-xl₁r₁≃x₂l₂r₂ ;
                  x₁l₁r₁≃x₁l₁r₁ = lemma-≃-≃ (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂)
             in ≃nd x x₂ (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) x₁l₁r₁≃push-xl₂r₂ x₁l₁r₁≃x₁l₁r₁
  ... | inj₂ x₁≤x | inj₁ x≤x₂ | _ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  push-xl₁r₁≃x₂l₂r₂ = trans≃ (lemma-push-≃ (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁) (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) ;
                  l₁≃l₁ = lemma-≃-≃ l₁≃r₁ ;
                  x₁l₁r₁≃xl₁r₁ = ≃nd x₁ x l₁≃r₁ l₁≃r₁ l₁≃l₁ ;
                  xl₁r₁≃push-xl₁r₁ = lemma-≃-push (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁ ;
                  x₁l₁r₁≃push-xl₁r₁ = trans≃ x₁l₁r₁≃xl₁r₁ xl₁r₁≃push-xl₁r₁
             in ≃nd x x₁ (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) push-xl₁r₁≃x₂l₂r₂ x₁l₁r₁≃push-xl₁r₁ 
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₁ x₁≤x₂ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  push-xl₁r₁≃x₂l₂r₂ = trans≃ (lemma-push-≃ (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁) (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) ;
                  l₁≃l₁ = lemma-≃-≃ l₁≃r₁ ;
                  x₁l₁r₁≃xl₁r₁ = ≃nd x₁ x l₁≃r₁ l₁≃r₁ l₁≃l₁ ;
                  xl₁r₁≃push-xl₁r₁ = lemma-≃-push (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁ ;
                  x₁l₁r₁≃push-xl₁r₁ = trans≃ x₁l₁r₁≃xl₁r₁ xl₁r₁≃push-xl₁r₁
             in ≃nd x x₁ (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) push-xl₁r₁≃x₂l₂r₂ x₁l₁r₁≃push-xl₁r₁ 
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₂ x₂≤x₁ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  push-xl₁r₁≃x₂l₂r₂ = lemma-≃-push  (sym≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂)) acc-xl₂r₂ ;
                  x₁l₁r₁≃push-xl₂r₂ = trans≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂) push-xl₁r₁≃x₂l₂r₂ ;
                  x₁l₁r₁≃x₁l₁r₁ = lemma-≃-≃ (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂)
             in ≃nd x x₂ (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) x₁l₁r₁≃push-xl₂r₂ x₁l₁r₁≃x₁l₁r₁

  lemma-push-≃ : {t t' : PLRTree} → t ≃ t' → (acc : Acc _≺_ t) → push t acc ≃ t
  lemma-push-≃ t≃t' at = sym≃ (lemma-≃-push t≃t' at)

lemma-push-⋗ : {t t' : PLRTree} → t ⋗ t' → (acc : Acc _≺_ t) → push t acc ⋗ t'
lemma-push-⋗ (⋗lf x) _ = ⋗lf x
lemma-push-⋗ (⋗nd _ _ ≃lf _ ()) _
lemma-push-⋗ (⋗nd x x' (≃nd x₁ x₂ ≃lf ≃lf ≃lf) ≃lf (⋗lf .x₁)) (acc rs) 
    with tot≤ x x₁ | tot≤ x x₂ | tot≤ x₁ x₂
... | inj₁ x≤x₁ | inj₁ x≤x₂ | _ = ⋗nd x x' (≃nd x₁ x₂ ≃lf ≃lf ≃lf) ≃lf (⋗lf x₁)
... | inj₁ x≤x₁ | inj₂ x₂≤x | _ = ⋗nd x₂ x' (≃nd x₁ x ≃lf ≃lf ≃lf) ≃lf (⋗lf x₁)
... | inj₂ x₁≤x | inj₁ x≤x₂ | _ = ⋗nd x₁ x' (≃nd x x₂ ≃lf ≃lf ≃lf) ≃lf (⋗lf x)
... | inj₂ x₁≤x | inj₂ x₂≤x | inj₁ x₁≤x₂ = ⋗nd x₁ x' (≃nd x x₂ ≃lf ≃lf ≃lf) ≃lf (⋗lf x)
... | inj₂ x₁≤x | inj₂ x₂≤x | inj₂ x₂≤x₁ = ⋗nd x₂ x' (≃nd x₁ x ≃lf ≃lf ≃lf) ≃lf (⋗lf x₁)
lemma-push-⋗ (⋗nd _ _ (≃nd x₁ _ ≃lf (≃nd _ _ _ _ _) ()) ≃lf (⋗lf .x₁)) _ 
lemma-push-⋗ (⋗nd x x' (≃nd {l₁} {r₁} {l₂} {r₂} x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) l'≃r' (⋗nd .x₁ x'₁ _ l'₁≃r'₁ l₁⋗l'₁)) (acc rs) 
    with tot≤ x x₁ | tot≤ x x₂ | tot≤ x₁ x₂
... | inj₁ x≤x₁ | inj₁ x≤x₂ | _ = ⋗nd x x' (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
... | inj₁ x≤x₁ | inj₂ x₂≤x | _ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
           let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                push-xl₁r₁≃x₂l₂r₂ = lemma-≃-push  (sym≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂)) acc-xl₂r₂ ;
                x₁l₁r₁≃push-xl₂r₂ = trans≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂) push-xl₁r₁≃x₂l₂r₂ 
           in ⋗nd x₂ x' x₁l₁r₁≃push-xl₂r₂ l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
... | inj₂ x₁≤x | inj₁ x≤x₂ | _ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
           let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                push-xl₁r₁≃x₂l₂r₂ = trans≃ (lemma-push-≃ (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁) (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) ;
                push-xl₁r₁⋗x'₁l'₁r'₁ = lemma-push-⋗ (⋗nd x x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-xl₁r₁
           in ⋗nd x₁ x' push-xl₁r₁≃x₂l₂r₂ l'≃r' push-xl₁r₁⋗x'₁l'₁r'₁
... | inj₂ x₁≤x | inj₂ x₂≤x | inj₁ x₁≤x₂ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
           let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                push-xl₁r₁≃x₂l₂r₂ = trans≃ (lemma-push-≃ (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁) (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) ;
                push-xl₁r₁⋗x'₁l'₁r'₁ = lemma-push-⋗ (⋗nd x x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-xl₁r₁
           in ⋗nd x₁ x' push-xl₁r₁≃x₂l₂r₂ l'≃r' push-xl₁r₁⋗x'₁l'₁r'₁
... | inj₂ x₁≤x | inj₂ x₂≤x | inj₂ x₂≤x₁ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
           let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                push-xl₁r₁≃x₂l₂r₂ = lemma-≃-push  (sym≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂)) acc-xl₂r₂ ;
                x₁l₁r₁≃push-xl₂r₂ = trans≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂) push-xl₁r₁≃x₂l₂r₂ 
           in ⋗nd x₂ x' x₁l₁r₁≃push-xl₂r₂ l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)

lemma-⋗-push : {t t' : PLRTree} → t ⋗ t' → (acc : Acc _≺_ t') → t ⋗ push t' acc
lemma-⋗-push (⋗lf x) _ = ⋗lf x
lemma-⋗-push (⋗nd x x' l≃r ≃lf l⋗l') _ = ⋗nd x x' l≃r ≃lf l⋗l'
lemma-⋗-push (⋗nd x x' l≃r (≃nd {l'₁} {r'₁} {l'₂} {r'₂} x'₁ x'₂  l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (⋗nd x₁ .x'₁ l₁≃r₁ _ l₁⋗l'₁)) (acc rs) 
    with tot≤ x' x'₁ | tot≤ x' x'₂ | tot≤ x'₁ x'₂
... | inj₁ x'≤x'₁ | inj₁ x'≤x'₂ | _ = ⋗nd x x' l≃r (≃nd x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
... | inj₁ x'≤x'₁ | inj₂ x'₂≤x' | _ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂ = 
           let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                x'₁l'₁r'₁≃push-x'l'₂r'₂ = trans≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (lemma-≃-push (sym≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂)) acc-x'l'₂r'₂)
           in ⋗nd x x'₂ l≃r x'₁l'₁r'₁≃push-x'l'₂r'₂ (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
... | inj₂ x'₁≤x' | inj₁ x'≤x'₂ | _ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ = 
           let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                push-x'l'₁r'₁≃x'₂l'₂r'₂ = trans≃ (lemma-push-≃ (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) acc-x'l'₁r'₁) (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) ;
                x₁l₁r₁⋗push-x'l'₁r'₁ = lemma-⋗-push (⋗nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-x'l'₁r'₁
           in ⋗nd x x'₁ l≃r push-x'l'₁r'₁≃x'₂l'₂r'₂ x₁l₁r₁⋗push-x'l'₁r'₁
... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₁ x'₁≤x'₂ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ = 
           let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                push-x'l'₁r'₁≃x'₂l'₂r'₂ = trans≃ (lemma-push-≃ (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) acc-x'l'₁r'₁) (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) ;
                x₁l₁r₁⋗push-x'l'₁r'₁ = lemma-⋗-push (⋗nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-x'l'₁r'₁
           in ⋗nd x x'₁ l≃r push-x'l'₁r'₁≃x'₂l'₂r'₂ x₁l₁r₁⋗push-x'l'₁r'₁
... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₂ x'₂≤x'₁ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂ = 
           let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                x'₁l'₁r'₁≃push-x'l'₂r'₂ = trans≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (lemma-≃-push (sym≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂)) acc-x'l'₂r'₂)
           in ⋗nd x x'₂ l≃r x'₁l'₁r'₁≃push-x'l'₂r'₂ (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)

lemma-⋘-push : {t t' : PLRTree} → t ⋘ t' → (acc : Acc _≺_ t') → t ⋘ push t' acc
lemma-⋘-push (x⋘ x y z) _ = x⋘ x y z
lemma-⋘-push (l⋘ _ _ () ≃lf ≃lf) _
lemma-⋘-push (l⋘ x x' l⋘r (≃nd {l'₁} {r'₁} {l'₂} {r'₂} x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (≃nd x₂ .x'₁ l₂≃r₂ _ l₂≃l'₁)) (acc rs) 
    with tot≤ x' x'₁ | tot≤ x' x'₂ | tot≤ x'₁ x'₂
... | inj₁ x'≤x'₁ | inj₁ x'≤x'₂ | _ = l⋘ x x' l⋘r (≃nd x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ l₂≃l'₁)
... | inj₁ x'≤x'₁ | inj₂ x'₂≤x' | _ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂ = 
           let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                x'₁l'₁r'₁≃push-x'l'₂r'₂ = trans≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (lemma-≃-push (sym≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂)) acc-x'l'₂r'₂)
           in l⋘ x x'₂ l⋘r x'₁l'₁r'₁≃push-x'l'₂r'₂ (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ l₂≃l'₁)
... | inj₂ x'₁≤x' | inj₁ x'≤x'₂ | _ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ = 
           let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                push-x'l'₁r'₁≃x'₂l'₂r'₂ = trans≃ (lemma-push-≃ (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) acc-x'l'₁r'₁) (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) ;
                x₂l₂r₂≃push-x'l'₁r'₁ = trans≃ (≃nd x₂ x' l₂≃r₂ l'₁≃r'₁ l₂≃l'₁) (lemma-≃-push (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) acc-x'l'₁r'₁)
           in l⋘ x x'₁ l⋘r push-x'l'₁r'₁≃x'₂l'₂r'₂ x₂l₂r₂≃push-x'l'₁r'₁
... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₁ x'₁≤x'₂ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ = 
           let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                push-x'l'₁r'₁≃x'₂l'₂r'₂ = trans≃ (lemma-push-≃ (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) acc-x'l'₁r'₁) (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) ;
                x₂l₂r₂≃push-x'l'₁r'₁ = trans≃ (≃nd x₂ x' l₂≃r₂ l'₁≃r'₁ l₂≃l'₁) (lemma-≃-push (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) acc-x'l'₁r'₁)
           in l⋘ x x'₁ l⋘r push-x'l'₁r'₁≃x'₂l'₂r'₂ x₂l₂r₂≃push-x'l'₁r'₁
... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₂ x'₂≤x'₁ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂ = 
           let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                x'₁l'₁r'₁≃push-x'l'₂r'₂ = trans≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (lemma-≃-push (sym≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂)) acc-x'l'₂r'₂)
           in l⋘ x x'₂ l⋘r x'₁l'₁r'₁≃push-x'l'₂r'₂ (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ l₂≃l'₁)
lemma-⋘-push (r⋘ x x' l⋙r ≃lf (⋗lf x₁)) _ = r⋘ x x' l⋙r ≃lf (⋗lf x₁)
lemma-⋘-push (r⋘ x x' l⋙r (≃nd {l'₁} {r'₁} {l'₂} {r'₂} x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (⋗nd x₁ .x'₁ l₁≃r₁ _ l₁⋗l'₁)) (acc rs) 
    with tot≤ x' x'₁ | tot≤ x' x'₂ | tot≤ x'₁ x'₂
... | inj₁ x'≤x'₁ | inj₁ x'≤x'₂ | _ = r⋘ x x' l⋙r (≃nd x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
... | inj₁ x'≤x'₁ | inj₂ x'₂≤x' | _ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂ = 
           let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                x'₁l'₁r'₁≃push-x'l'₂r'₂ = trans≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (lemma-≃-push (sym≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂)) acc-x'l'₂r'₂)
           in r⋘ x x'₂ l⋙r  x'₁l'₁r'₁≃push-x'l'₂r'₂ (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
... | inj₂ x'₁≤x' | inj₁ x'≤x'₂ | _ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ = 
           let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                push-x'l'₁r'₁≃x'₂l'₂r'₂ = trans≃ (lemma-push-≃ (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) acc-x'l'₁r'₁) (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) 
           in r⋘ x x'₁ l⋙r push-x'l'₁r'₁≃x'₂l'₂r'₂ (lemma-⋗-push (⋗nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-x'l'₁r'₁)
... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₁ x'₁≤x'₂ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ = 
           let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                push-x'l'₁r'₁≃x'₂l'₂r'₂ = trans≃ (lemma-push-≃ (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂)  acc-x'l'₁r'₁) (≃nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) 
           in r⋘ x x'₁ l⋙r push-x'l'₁r'₁≃x'₂l'₂r'₂ (lemma-⋗-push (⋗nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-x'l'₁r'₁)
... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₂ x'₂≤x'₁ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂ =
           let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right perfect x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                x'₁l'₁r'₁≃push-x'l'₂r'₂ = trans≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂) (lemma-≃-push (sym≃ (≃nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁≃l'₂)) acc-x'l'₂r'₂)
           in r⋘ x x'₂ l⋙r  x'₁l'₁r'₁≃push-x'l'₂r'₂ (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)

lemma-push-⋙ : {t t' : PLRTree} → t ⋙ t' → (acc : Acc _≺_ t) → push t acc ⋙ t'
lemma-push-⋙ (⋙p l⋗r) (acc rs) = ⋙p (lemma-push-⋗ l⋗r (acc rs))
lemma-push-⋙ (⋙l _ _ ≃lf _ ()) _ 
lemma-push-⋙ (⋙l _ _ (≃nd x₁ _ ≃lf _ _) () (⋗lf .x₁)) _
lemma-push-⋙ (⋙l x x' (≃nd {l₁} {r₁} {l₂} {r₂} x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) l'⋘r' (⋗nd .x₁ x₄ _ l₄≃r₄ l₁⋗r₄)) (acc rs) 
    with tot≤ x x₁ | tot≤ x x₂ | tot≤ x₁ x₂
... | inj₁ x≤x₁ | inj₁ x≤x₂ | _ = ⋙l x x' (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) l'⋘r' (⋗nd x₁ x₄ l₁≃r₁ l₄≃r₄ l₁⋗r₄) 
... | inj₁ x≤x₁ | inj₂ x₂≤x | _ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
           let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                x₁l₁r₁≃push-xl₂r₂ = trans≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂) (lemma-≃-push  (sym≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂)) acc-xl₂r₂)
           in ⋙l x₂ x' x₁l₁r₁≃push-xl₂r₂ l'⋘r' (⋗nd x₁ x₄ l₁≃r₁ l₄≃r₄ l₁⋗r₄) 
... | inj₂ x₁≤x | inj₁ x≤x₂ | _ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
           let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                push-xl₁r₁≃x₂l₂r₂ = trans≃ (lemma-push-≃ (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁) (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) 
           in ⋙l x₁ x' push-xl₁r₁≃x₂l₂r₂ l'⋘r' (lemma-push-⋗ (⋗nd x x₄ l₁≃r₁ l₄≃r₄ l₁⋗r₄) acc-xl₁r₁)
... | inj₂ x₁≤x | inj₂ x₂≤x | inj₁ x₁≤x₂ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
           let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                push-xl₁r₁≃x₂l₂r₂ = trans≃ (lemma-push-≃ (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁) (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) 
           in ⋙l x₁ x' push-xl₁r₁≃x₂l₂r₂ l'⋘r' (lemma-push-⋗ (⋗nd x x₄ l₁≃r₁ l₄≃r₄ l₁⋗r₄) acc-xl₁r₁)
... | inj₂ x₁≤x | inj₂ x₂≤x | inj₂ x₂≤x₁ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
           let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                x₁l₁r₁≃push-xl₂r₂ =  trans≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂) (lemma-≃-push  (sym≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂)) acc-xl₂r₂)
           in ⋙l x₂ x' x₁l₁r₁≃push-xl₂r₂ l'⋘r' (⋗nd x₁ x₄ l₁≃r₁ l₄≃r₄ l₁⋗r₄) 
lemma-push-⋙ (⋙r _ _ ≃lf (⋙p ()) ≃lf) _
lemma-push-⋙ (⋙r x x' (≃nd {l₁} {r₁} {l₂} {r₂} x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) l'⋙r' (≃nd .x₁ x₃ _ l₃≃r₃ l₁≃l₃)) (acc rs) 
    with tot≤ x x₁ | tot≤ x x₂ | tot≤ x₁ x₂
... | inj₁ x≤x₁ | inj₁ x≤x₂ | _ = ⋙r x x' (≃nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) l'⋙r' (≃nd x₁ x₃ l₁≃r₁ l₃≃r₃ l₁≃l₃) 
... | inj₁ x≤x₁ | inj₂ x₂≤x | _ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
           let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                x₁l₁r₁≃push-xl₂r₂ = trans≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂) (lemma-≃-push (sym≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂)) acc-xl₂r₂)
           in ⋙r x₂ x' x₁l₁r₁≃push-xl₂r₂ l'⋙r' (≃nd x₁ x₃ l₁≃r₁ l₃≃r₃ l₁≃l₃) 
... | inj₂ x₁≤x | inj₁ x≤x₂ | _ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
           let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                push-xl₁r₁≃x₂l₂r₂ = trans≃ (lemma-push-≃ (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁) (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) ;
                push-xl₁r₁≃x₃l₃r₃ = trans≃ (lemma-push-≃ (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁) (≃nd x x₃ l₁≃r₁ l₃≃r₃ l₁≃l₃) 
           in ⋙r x₁ x' push-xl₁r₁≃x₂l₂r₂ l'⋙r' push-xl₁r₁≃x₃l₃r₃ 
... | inj₂ x₁≤x | inj₂ x₂≤x | inj₁ x₁≤x₂ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
           let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                push-xl₁r₁≃x₂l₂r₂ = trans≃ (lemma-push-≃ (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁) (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) ;
                push-xl₁r₁≃x₃l₃r₃ = trans≃ (lemma-push-≃ (≃nd x x₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) acc-xl₁r₁) (≃nd x x₃ l₁≃r₁ l₃≃r₃ l₁≃l₃) 
           in ⋙r x₁ x' push-xl₁r₁≃x₂l₂r₂ l'⋙r' push-xl₁r₁≃x₃l₃r₃ 
... | inj₂ x₁≤x | inj₂ x₂≤x | inj₂ x₂≤x₁ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
           let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                x₁l₁r₁≃push-xl₂r₂ = trans≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂) (lemma-≃-push (sym≃ (≃nd x₁ x l₁≃r₁ l₂≃r₂ l₁≃l₂)) acc-xl₂r₂)
           in ⋙r x₂ x' x₁l₁r₁≃push-xl₂r₂ l'⋙r' (≃nd x₁ x₃ l₁≃r₁ l₃≃r₃ l₁≃l₃) 

mutual
  lemma-⋙r-push : {l r l' r' : PLRTree}(x x' : A) → l ≃ r → l' ⋙ r' → l ≃ l' → (acc : Acc _≺_ (node right x' l' r')) → (node perfect x l r) ⋙ push (node right x' l' r') acc
  lemma-⋙r-push x x' l≃r (⋙p (⋗lf x'₁)) (≃nd x₁ .x'₁ ≃lf ≃lf ≃lf) (acc rs) 
      with tot≤ x' x'₁
  ... | inj₁ x'≤x'₁ = ⋙r x x' l≃r (⋙p (⋗lf x'₁)) (≃nd x₁ x'₁ ≃lf ≃lf ≃lf)
  ... | inj₂ x'₁≤x' = ⋙r x x'₁ l≃r (⋙p (⋗lf x')) (≃nd x₁ x' ≃lf ≃lf ≃lf)
  lemma-⋙r-push x x' l≃r (⋙p (⋗nd {l'₁} {r'₁} {l'₂} {r'₂} x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁⋗l'₂)) (≃nd x₁ .x'₁ l₁≃r₁ _ l₁≃l'₁) (acc rs) 
        with tot≤ x' x'₁ | tot≤ x' x'₂ | tot≤ x'₁ x'₂
  ... | inj₁ x'≤x'₁ | inj₁ x'≤x'₂ | _ = ⋙r x x' l≃r (⋙p (⋗nd x'₁ x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁⋗l'₂)) (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)
  ... | inj₁ x'≤x'₁ | inj₂ x'₂≤x' | _ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂  =
             let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right right x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  x'₁l'₁r'₁⋗push-x'l'₂r'₂ = lemma-⋗-push (⋗nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁⋗l'₂) acc-x'l'₂r'₂ 
             in ⋙r x x'₂ l≃r (⋙p x'₁l'₁r'₁⋗push-x'l'₂r'₂) (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)
  ... | inj₂ x'₁≤x' | inj₁ x'≤x'₂ | _ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ =
             let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left right x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  push-x'l'₁r'₁⋗x'₂l'₂r'₂ = lemma-push-⋗ (⋗nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁⋗l'₂) acc-x'l'₁r'₁ ;
                  x₁l₁r₁≃push-x'l'₁r'₁ = trans≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁) (lemma-≃-push (sym≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)) acc-x'l'₁r'₁)
             in ⋙r x x'₁ l≃r (⋙p push-x'l'₁r'₁⋗x'₂l'₂r'₂) x₁l₁r₁≃push-x'l'₁r'₁
  ... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₁ x'₁≤x'₂ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ = 
             let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left right x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  push-x'l'₁r'₁⋗x'₂l'₂r'₂ = lemma-push-⋗ (⋗nd x' x'₂ l'₁≃r'₁ l'₂≃r'₂ l'₁⋗l'₂) acc-x'l'₁r'₁ ;
                  x₁l₁r₁≃push-x'l'₁r'₁ = trans≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁) (lemma-≃-push (sym≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)) acc-x'l'₁r'₁)
             in ⋙r x x'₁ l≃r (⋙p push-x'l'₁r'₁⋗x'₂l'₂r'₂) x₁l₁r₁≃push-x'l'₁r'₁
  ... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₂ x'₂≤x'₁ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂ = 
             let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right right x' (node perfect x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  x'₁l'₁r'₁⋗push-x'l'₂r'₂ = lemma-⋗-push (⋗nd x'₁ x' l'₁≃r'₁ l'₂≃r'₂ l'₁⋗l'₂) acc-x'l'₂r'₂ 
             in ⋙r x x'₂ l≃r (⋙p x'₁l'₁r'₁⋗push-x'l'₂r'₂) (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)
  lemma-⋙r-push x x' l≃r (⋙l {l'₁} {r'₁} {l'₂} {r'₂} x'₁ x'₂ l'₁≃r'₁ l'₂⋘r'₂ l'₁⋗r'₂) (≃nd x₁ .x'₁ l₁≃r₁ _ l₁≃l'₁) (acc rs) 
        with tot≤ x' x'₁ | tot≤ x' x'₂ | tot≤ x'₁ x'₂
  ... | inj₁ x'≤x'₁ | inj₁ x'≤x'₂ | _ = ⋙r x x' l≃r (⋙l x'₁ x'₂ l'₁≃r'₁ l'₂⋘r'₂ l'₁⋗r'₂) (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)
  ... | inj₁ x'≤x'₁ | inj₂ x'₂≤x' | _ rewrite lemma-≡-height left x' x'₂ l'₂ r'₂  =
             let acc-x'l'₂r'₂ = rs (node left x' l'₂ r'₂) (lemma-≺-right right x' (node perfect x'₁ l'₁ r'₁) (node left x'₂ l'₂ r'₂)) ;
                  x'₁l'₁r'₁⋙push-x'l'₂r'₂ = lemma-⋙l-push x'₁ x' l'₁≃r'₁ l'₂⋘r'₂ l'₁⋗r'₂ acc-x'l'₂r'₂ 
             in ⋙r x x'₂ l≃r  x'₁l'₁r'₁⋙push-x'l'₂r'₂ (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)
  ... | inj₂ x'₁≤x' | inj₁ x'≤x'₂ | _ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ =
             let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left right x' (node perfect x'₁ l'₁ r'₁) (node left x'₂ l'₂ r'₂)) ; 
                  push-x'l'₁r'₁⋙x'₂l'₂r'₂ = lemma-push-⋙ (⋙l x' x'₂ l'₁≃r'₁ l'₂⋘r'₂ l'₁⋗r'₂) acc-x'l'₁r'₁ ;
                  x₁l₁r₁≃push-x'l'₁r'₁ = trans≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁) (lemma-≃-push (sym≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)) acc-x'l'₁r'₁)
             in ⋙r x x'₁ l≃r push-x'l'₁r'₁⋙x'₂l'₂r'₂ x₁l₁r₁≃push-x'l'₁r'₁
  ... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₁ x'₁≤x'₂ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ = 
             let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left right x' (node perfect x'₁ l'₁ r'₁) (node left x'₂ l'₂ r'₂)) ; 
                  push-x'l'₁r'₁⋙x'₂l'₂r'₂ = lemma-push-⋙ (⋙l x' x'₂ l'₁≃r'₁ l'₂⋘r'₂ l'₁⋗r'₂) acc-x'l'₁r'₁ ;
                  x₁l₁r₁≃push-x'l'₁r'₁ = trans≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁) (lemma-≃-push (sym≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)) acc-x'l'₁r'₁)
             in ⋙r x x'₁ l≃r push-x'l'₁r'₁⋙x'₂l'₂r'₂ x₁l₁r₁≃push-x'l'₁r'₁
  ... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₂ x'₂≤x'₁ rewrite lemma-≡-height left x' x'₂ l'₂ r'₂ = 
             let acc-x'l'₂r'₂ = rs (node left x' l'₂ r'₂) (lemma-≺-right right x' (node perfect x'₁ l'₁ r'₁) (node left x'₂ l'₂ r'₂)) ;
                  x'₁l'₁r'₁⋙push-x'l'₂r'₂ = lemma-⋙l-push x'₁ x' l'₁≃r'₁ l'₂⋘r'₂ l'₁⋗r'₂ acc-x'l'₂r'₂ 
             in ⋙r x x'₂ l≃r  x'₁l'₁r'₁⋙push-x'l'₂r'₂ (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)

  lemma-⋙r-push x x' l≃r (⋙r {l'₁} {r'₁} {l'₂} {r'₂} x'₁ x'₂ l'₁≃r'₁ l'₂⋙r'₂ l'₁≃l'₂) (≃nd x₁ .x'₁ l₁≃r₁ _ l₁≃l'₁) (acc rs) 
        with tot≤ x' x'₁ | tot≤ x' x'₂ | tot≤ x'₁ x'₂
  ... | inj₁ x'≤x'₁ | inj₁ x'≤x'₂ | _ = ⋙r x x' l≃r (⋙r x'₁ x'₂ l'₁≃r'₁ l'₂⋙r'₂ l'₁≃l'₂) (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)
  ... | inj₁ x'≤x'₁ | inj₂ x'₂≤x' | _ rewrite lemma-≡-height right x' x'₂ l'₂ r'₂  =
             let acc-x'l'₂r'₂ = rs (node right x' l'₂ r'₂) (lemma-≺-right right x' (node perfect x'₁ l'₁ r'₁) (node right x'₂ l'₂ r'₂)) ;
                  x'₁l'₁r'₁⋙push-x'l'₂r'₂ = lemma-⋙r-push x'₁ x' l'₁≃r'₁ l'₂⋙r'₂ l'₁≃l'₂ acc-x'l'₂r'₂ 
             in ⋙r x x'₂ l≃r x'₁l'₁r'₁⋙push-x'l'₂r'₂ (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)
  ... | inj₂ x'₁≤x' | inj₁ x'≤x'₂ | _ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ =
             let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left right x' (node perfect x'₁ l'₁ r'₁) (node right x'₂ l'₂ r'₂)) ; 
                  push-x'l'₁r'₁⋙x'₂l'₂r'₂ = lemma-push-⋙ (⋙r x' x'₂ l'₁≃r'₁ l'₂⋙r'₂ l'₁≃l'₂) acc-x'l'₁r'₁ ;
                  x₁l₁r₁≃push-x'l'₁r'₁ = trans≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁) (lemma-≃-push (sym≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)) acc-x'l'₁r'₁)
             in ⋙r x x'₁ l≃r push-x'l'₁r'₁⋙x'₂l'₂r'₂ x₁l₁r₁≃push-x'l'₁r'₁
  ... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₁ x'₁≤x'₂ rewrite lemma-≡-height perfect x' x'₁ l'₁ r'₁ =
             let acc-x'l'₁r'₁ = rs (node perfect x' l'₁ r'₁) (lemma-≺-left right x' (node perfect x'₁ l'₁ r'₁) (node right x'₂ l'₂ r'₂)) ; 
                  push-x'l'₁r'₁⋙x'₂l'₂r'₂ = lemma-push-⋙ (⋙r x' x'₂ l'₁≃r'₁ l'₂⋙r'₂ l'₁≃l'₂) acc-x'l'₁r'₁ ;
                  x₁l₁r₁≃push-x'l'₁r'₁ = trans≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁) (lemma-≃-push (sym≃ (≃nd x₁ x' l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)) acc-x'l'₁r'₁)
             in ⋙r x x'₁ l≃r push-x'l'₁r'₁⋙x'₂l'₂r'₂ x₁l₁r₁≃push-x'l'₁r'₁
  ... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₂ x'₂≤x'₁ rewrite lemma-≡-height right x' x'₂ l'₂ r'₂ =
             let acc-x'l'₂r'₂ = rs (node right x' l'₂ r'₂) (lemma-≺-right right x' (node perfect x'₁ l'₁ r'₁) (node right x'₂ l'₂ r'₂)) ;
                  x'₁l'₁r'₁⋙push-x'l'₂r'₂ = lemma-⋙r-push x'₁ x' l'₁≃r'₁ l'₂⋙r'₂ l'₁≃l'₂ acc-x'l'₂r'₂ 
             in ⋙r x x'₂ l≃r x'₁l'₁r'₁⋙push-x'l'₂r'₂ (≃nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁≃l'₁)

  lemma-push-l⋘ : {l r l' r' : PLRTree}(x x' : A) → l ⋘ r → l' ≃ r' → r ≃ l' → (acc : Acc _≺_ (node left x l r)) → push (node left x l r) acc ⋘ node perfect x' l' r' 
  lemma-push-l⋘ x x' (x⋘ x₁ x₂ x₃) l'≃r' (≃nd .x₃ x'₁ ≃lf ≃lf ≃lf) (acc rs) 
      with tot≤ x x₁ | tot≤ x x₃ | tot≤ x₁ x₃
  ... | inj₁ x≤x₁ | inj₁ x≤x₃ | _ = l⋘ x x' (x⋘ x₁ x₂ x₃) l'≃r' (≃nd x₃ x'₁ ≃lf ≃lf ≃lf)
  ... | inj₁ x≤x₁ | inj₂ x₃≤x | _ = l⋘ x₃ x' (x⋘ x₁ x₂ x) l'≃r' (≃nd x x'₁ ≃lf ≃lf ≃lf)
  ... | inj₂ x₁≤x | inj₁ x≤x₃ | _ 
      with tot≤ x x₂
  ... | inj₁ x≤x₂ = l⋘ x₁ x' (x⋘ x x₂ x₃) l'≃r' (≃nd x₃ x'₁ ≃lf ≃lf ≃lf)
  ... | inj₂ x₂≤x = l⋘ x₁ x' (x⋘ x₂ x x₃) l'≃r' (≃nd x₃ x'₁ ≃lf ≃lf ≃lf)
  lemma-push-l⋘ x x' (x⋘ x₁ x₂ x₃) l'≃r' (≃nd .x₃ x'₁ ≃lf ≃lf ≃lf) (acc rs) | inj₂ x₁≤x | inj₂ x₃≤x | inj₁ x₁≤x₃ 
      with tot≤ x x₂
  ... | inj₁ x≤x₂ = l⋘ x₁ x' (x⋘ x x₂ x₃) l'≃r' (≃nd x₃ x'₁ ≃lf ≃lf ≃lf)
  ... | inj₂ x₂≤x = l⋘ x₁ x' (x⋘ x₂ x x₃) l'≃r' (≃nd x₃ x'₁ ≃lf ≃lf ≃lf)
  lemma-push-l⋘ x x' (x⋘ x₁ x₂ x₃) l'≃r' (≃nd .x₃ x'₁ ≃lf ≃lf ≃lf) (acc rs) | inj₂ x₁≤x | inj₂ x₃≤x | inj₂ x₃≤x₁ = l⋘ x₃ x' (x⋘ x₁ x₂ x) l'≃r' (≃nd x x'₁ ≃lf ≃lf ≃lf)
  lemma-push-l⋘ x x' (l⋘ {l₁} {r₁} {l₂} {r₂} x₁ x₂ l₁⋘r₁ l₂≃r₂ r₁≃l₂) l'≃r' (≃nd .x₂ x'₁ _ l'₁≃r'₁ r₂≃l'₁) (acc rs) 
      with tot≤ x x₁ | tot≤ x x₂ | tot≤ x₁ x₂
  ... | inj₁ x≤x₁ | inj₁ x≤x₂ | _ = l⋘ x x' (l⋘ x₁ x₂ l₁⋘r₁ l₂≃r₂ r₁≃l₂) l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁)
  ... | inj₁ x≤x₁ | inj₂ x₂≤x | _ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right left x (node left x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  x₁l₁r₁⋘push-xl₂r₂ = lemma-⋘-push (l⋘ x₁ x l₁⋘r₁ l₂≃r₂ r₁≃l₂) acc-xl₂r₂ ;
                  push-xl₂r₂≃x'₁l'₁r'₁ = trans≃ (lemma-push-≃ (≃nd x x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁) acc-xl₂r₂) (≃nd x x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁)
             in l⋘ x₂ x' x₁l₁r₁⋘push-xl₂r₂ l'≃r' push-xl₂r₂≃x'₁l'₁r'₁
  ... | inj₂ x₁≤x | inj₁ x≤x₂ | _ rewrite lemma-≡-height left x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node left x l₁ r₁) (lemma-≺-left left x (node left x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  push-xl₁r₁⋘x₂l₂r₂ = lemma-push-l⋘ x x₂ l₁⋘r₁ l₂≃r₂ r₁≃l₂ acc-xl₁r₁ 
             in l⋘ x₁ x' push-xl₁r₁⋘x₂l₂r₂ l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁)
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₁ x₁≤x₂ rewrite lemma-≡-height left x x₁ l₁ r₁ =
             let acc-xl₁r₁ = rs (node left x l₁ r₁) (lemma-≺-left left x (node left x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  push-xl₁r₁⋘x₂l₂r₂ = lemma-push-l⋘ x x₂ l₁⋘r₁ l₂≃r₂ r₁≃l₂ acc-xl₁r₁ 
             in l⋘ x₁ x' push-xl₁r₁⋘x₂l₂r₂ l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁)
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₂ x₂≤x₁ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right left x (node left x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  x₁l₁r₁⋘push-xl₂r₂ = lemma-⋘-push (l⋘ x₁ x l₁⋘r₁ l₂≃r₂ r₁≃l₂) acc-xl₂r₂ ;
                  push-xl₂r₂≃x'₁l'₁r'₁ = trans≃ (lemma-push-≃ (≃nd x x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁) acc-xl₂r₂) (≃nd x x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁)
             in l⋘ x₂ x' x₁l₁r₁⋘push-xl₂r₂ l'≃r' push-xl₂r₂≃x'₁l'₁r'₁
  lemma-push-l⋘ x x' (r⋘ {l₁} {r₁} {l₂} {r₂} x₁ x₂ l₁⋙r₁ l₂≃r₂ l₁⋗l₂) l'≃r' (≃nd .x₂ x'₁ _ l'₁≃r'₁ r₂≃l'₁) (acc rs) 
    with tot≤ x x₁ | tot≤ x x₂ | tot≤ x₁ x₂
  ... | inj₁ x≤x₁ | inj₁ x≤x₂ | _ = l⋘ x x' (r⋘ x₁ x₂ l₁⋙r₁ l₂≃r₂ l₁⋗l₂) l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁)
  ... | inj₁ x≤x₁ | inj₂ x₂≤x | _ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right left x (node right x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  x₁l₁r₁⋘push-xl₂r₂ = lemma-⋘-push (r⋘ x₁ x l₁⋙r₁ l₂≃r₂ l₁⋗l₂) acc-xl₂r₂ ;
                  push-xl₂r₂≃x'₁l'₁r'₁ = trans≃ (lemma-push-≃ (≃nd x x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁) acc-xl₂r₂) (≃nd x x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁)
             in l⋘ x₂ x' x₁l₁r₁⋘push-xl₂r₂ l'≃r' push-xl₂r₂≃x'₁l'₁r'₁
  ... | inj₂ x₁≤x | inj₁ x≤x₂ | _ rewrite lemma-≡-height right x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node right x l₁ r₁) (lemma-≺-left left x (node right x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  push-xl₁r₁⋘x₂l₂r₂ = lemma-push-r⋘ x x₂ l₁⋙r₁ l₂≃r₂ l₁⋗l₂ acc-xl₁r₁ 
             in l⋘ x₁ x' push-xl₁r₁⋘x₂l₂r₂ l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁)
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₁ x₁≤x₂ rewrite lemma-≡-height right x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node right x l₁ r₁) (lemma-≺-left left x (node right x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  push-xl₁r₁⋘x₂l₂r₂ = lemma-push-r⋘ x x₂ l₁⋙r₁ l₂≃r₂ l₁⋗l₂ acc-xl₁r₁ 
             in l⋘ x₁ x' push-xl₁r₁⋘x₂l₂r₂ l'≃r' (≃nd x₂ x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁)
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₂ x₂≤x₁ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right left x (node right x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  x₁l₁r₁⋘push-xl₂r₂ = lemma-⋘-push (r⋘ x₁ x l₁⋙r₁ l₂≃r₂ l₁⋗l₂) acc-xl₂r₂ ;
                  push-xl₂r₂≃x'₁l'₁r'₁ = trans≃ (lemma-push-≃ (≃nd x x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁) acc-xl₂r₂) (≃nd x x'₁ l₂≃r₂ l'₁≃r'₁ r₂≃l'₁)
             in l⋘ x₂ x' x₁l₁r₁⋘push-xl₂r₂ l'≃r' push-xl₂r₂≃x'₁l'₁r'₁

  lemma-push-r⋘ : {l r l' r' : PLRTree}(x x' : A) → l ⋙ r → l' ≃ r' → l ⋗ l' → (acc : Acc _≺_ (node right x l r)) → push (node right x l r) acc ⋘ node perfect x' l' r' 
  lemma-push-r⋘ x x' (⋙p (⋗lf x₁)) ≃lf (⋗lf .x₁) (acc rs) 
      with tot≤ x x₁
  ... | inj₁ x≤x₁ = x⋘ x x₁ x'
  ... | inj₂ x₁≤x = x⋘ x₁ x x'
  lemma-push-r⋘  _ _ (⋙p (⋗lf x₁)) _ (⋗nd .x₁ _ _ _ ()) _
  lemma-push-r⋘ _ _ (⋙p (⋗nd x₁ _ _ _ ())) ≃lf (⋗lf .x₁) _
  lemma-push-r⋘ x x' (⋙p (⋗nd {l₁} {r₁} {l₂} {r₂} x₁ x₂ l₁≃r₁ l₂≃r₂ l₁⋗l₂)) l'≃r' (⋗nd .x₁ x'₁ _ l'₁≃r'₁ l₁⋗l'₁) (acc rs) 
      with tot≤ x x₁ | tot≤ x x₂ | tot≤ x₁ x₂
  ... | inj₁ x≤x₁ | inj₁ x≤x₂ | _ = r⋘ x x' (⋙p (⋗nd x₁ x₂ l₁≃r₁ l₂≃r₂ l₁⋗l₂)) l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
  ... | inj₁ x≤x₁ | inj₂ x₂≤x | _ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  x₁l₁r₁⋗push-xl₂r₂ = lemma-⋗-push (⋗nd x₁ x l₁≃r₁ l₂≃r₂ l₁⋗l₂) acc-xl₂r₂
             in r⋘ x₂ x' (⋙p x₁l₁r₁⋗push-xl₂r₂) l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
  ... | inj₂ x₁≤x | inj₁ x≤x₂ | _ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  push-xl₁r₁⋗x₂l₂r₂ = lemma-push-⋗ (⋗nd x x₂ l₁≃r₁ l₂≃r₂ l₁⋗l₂) acc-xl₁r₁ ;
                  push-xl₁r₁⋗x'₁l'₁r'₁ = lemma-push-⋗ (⋗nd x x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-xl₁r₁
             in r⋘ x₁ x' (⋙p push-xl₁r₁⋗x₂l₂r₂) l'≃r' push-xl₁r₁⋗x'₁l'₁r'₁
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₁ x₁≤x₂ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  push-xl₁r₁⋗x₂l₂r₂ = lemma-push-⋗ (⋗nd x x₂ l₁≃r₁ l₂≃r₂ l₁⋗l₂) acc-xl₁r₁ ;
                  push-xl₁r₁⋗x'₁l'₁r'₁ = lemma-push-⋗ (⋗nd x x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-xl₁r₁
             in r⋘ x₁ x' (⋙p push-xl₁r₁⋗x₂l₂r₂) l'≃r' push-xl₁r₁⋗x'₁l'₁r'₁
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₂ x₂≤x₁ rewrite lemma-≡-height perfect x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node perfect x l₂ r₂) (lemma-≺-right perfect x (node perfect x₁ l₁ r₁) (node perfect x₂ l₂ r₂)) ;
                  x₁l₁r₁⋗push-xl₂r₂ = lemma-⋗-push (⋗nd x₁ x l₁≃r₁ l₂≃r₂ l₁⋗l₂) acc-xl₂r₂
             in r⋘ x₂ x' (⋙p x₁l₁r₁⋗push-xl₂r₂) l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
  lemma-push-r⋘  _ _ (⋙l x₁ _ _ _ ()) _ (⋗lf .x₁) _
  lemma-push-r⋘ x x' (⋙l {l₁} {r₁} {l₂} {r₂} x₁ x₂ l₁≃r₁ l₂⋘r₂ l₁⋗r₂) l'≃r' (⋗nd .x₁ x'₁ _ l'₁≃r'₁ l₁⋗l'₁) (acc rs)  
      with tot≤ x x₁ | tot≤ x x₂ | tot≤ x₁ x₂
  ... | inj₁ x≤x₁ | inj₁ x≤x₂ | _ = r⋘ x x' (⋙l x₁ x₂ l₁≃r₁ l₂⋘r₂ l₁⋗r₂) l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
  ... | inj₁ x≤x₁ | inj₂ x₂≤x | _ rewrite lemma-≡-height left x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node left x l₂ r₂) (lemma-≺-right right x (node perfect x₁ l₁ r₁) (node left x₂ l₂ r₂)) ;
                  x₁l₁r₁⋙push-xl₂r₂ = lemma-⋙l-push x₁ x l₁≃r₁ l₂⋘r₂ l₁⋗r₂ acc-xl₂r₂
             in r⋘ x₂ x' x₁l₁r₁⋙push-xl₂r₂ l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
  ... | inj₂ x₁≤x | inj₁ x≤x₂ | _ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left right x (node perfect x₁ l₁ r₁) (node left x₂ l₂ r₂)) ;
                  push-xl₁r₁⋙x₂l₂r₂ = lemma-push-⋙ (⋙l x x₂ l₁≃r₁ l₂⋘r₂ l₁⋗r₂) acc-xl₁r₁ ;
                  push-xl₁r₁⋗x'₁l'₁r'₁ = lemma-push-⋗ (⋗nd x x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-xl₁r₁
             in r⋘ x₁ x' push-xl₁r₁⋙x₂l₂r₂ l'≃r' push-xl₁r₁⋗x'₁l'₁r'₁
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₁ x₁≤x₂ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left right x (node perfect x₁ l₁ r₁) (node left x₂ l₂ r₂)) ;
                  push-xl₁r₁⋙x₂l₂r₂ = lemma-push-⋙ (⋙l x x₂ l₁≃r₁ l₂⋘r₂ l₁⋗r₂) acc-xl₁r₁ ;
                  push-xl₁r₁⋗x'₁l'₁r'₁ = lemma-push-⋗ (⋗nd x x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-xl₁r₁
             in r⋘ x₁ x' push-xl₁r₁⋙x₂l₂r₂ l'≃r' push-xl₁r₁⋗x'₁l'₁r'₁
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₂ x₂≤x₁ rewrite lemma-≡-height left x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node left x l₂ r₂) (lemma-≺-right right x (node perfect x₁ l₁ r₁) (node left x₂ l₂ r₂)) ;
                  x₁l₁r₁⋙push-xl₂r₂ = lemma-⋙l-push x₁ x l₁≃r₁ l₂⋘r₂ l₁⋗r₂ acc-xl₂r₂
             in r⋘ x₂ x' x₁l₁r₁⋙push-xl₂r₂ l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
  lemma-push-r⋘ _ _ (⋙r x₁ _ ≃lf (⋙p ()) ≃lf) ≃lf (⋗lf .x₁) _
  lemma-push-r⋘ _ _ (⋙r x₁ x₂ ≃lf (⋙l _ _ _ _ _) ()) ≃lf (⋗lf .x₁) _ 
  lemma-push-r⋘ _ _ (⋙r x₁ x₂ ≃lf (⋙r _ _ _ _ _) ()) ≃lf (⋗lf .x₁) _ 
  lemma-push-r⋘ x x' (⋙r {l₁} {r₁} {l₂} {r₂} x₁ x₂ l₁≃r₁ l₂⋙r₂ l₁≃l₂) l'≃r' (⋗nd .x₁ x'₁ _ l'₁≃r'₁ l₁⋗l'₁) (acc rs) 
      with tot≤ x x₁ | tot≤ x x₂ | tot≤ x₁ x₂
  ... | inj₁ x≤x₁ | inj₁ x≤x₂ | _ = r⋘ x x' (⋙r x₁ x₂ l₁≃r₁ l₂⋙r₂ l₁≃l₂) l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) 
  ... | inj₁ x≤x₁ | inj₂ x₂≤x | _ rewrite lemma-≡-height right x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node right x l₂ r₂) (lemma-≺-right right x (node perfect x₁ l₁ r₁) (node right x₂ l₂ r₂)) ;
                  x₁l₁r₁⋙push-xl₂r₂ = lemma-⋙r-push x₁ x l₁≃r₁ l₂⋙r₂ l₁≃l₂ acc-xl₂r₂
             in r⋘ x₂ x' x₁l₁r₁⋙push-xl₂r₂ l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)
  ... | inj₂ x₁≤x | inj₁ x≤x₂ | _ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left right x (node perfect x₁ l₁ r₁) (node right x₂ l₂ r₂)) ;
                  push-xl₁r₁⋙x₂l₂r₂ = lemma-push-⋙ (⋙r x x₂ l₁≃r₁ l₂⋙r₂ l₁≃l₂) acc-xl₁r₁ ;
                  push-xl₁r₁⋗x'₁l'₁r'₁ = lemma-push-⋗ (⋗nd x x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-xl₁r₁
             in r⋘ x₁ x' push-xl₁r₁⋙x₂l₂r₂ l'≃r' push-xl₁r₁⋗x'₁l'₁r'₁
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₁ x₁≤x₂ rewrite lemma-≡-height perfect x x₁ l₁ r₁ = 
             let acc-xl₁r₁ = rs (node perfect x l₁ r₁) (lemma-≺-left right x (node perfect x₁ l₁ r₁) (node right x₂ l₂ r₂)) ;
                  push-xl₁r₁⋙x₂l₂r₂ = lemma-push-⋙ (⋙r x x₂ l₁≃r₁ l₂⋙r₂ l₁≃l₂) acc-xl₁r₁ ;
                  push-xl₁r₁⋗x'₁l'₁r'₁ = lemma-push-⋗ (⋗nd x x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁) acc-xl₁r₁
             in r⋘ x₁ x' push-xl₁r₁⋙x₂l₂r₂ l'≃r' push-xl₁r₁⋗x'₁l'₁r'₁
  ... | inj₂ x₁≤x | inj₂ x₂≤x | inj₂ x₂≤x₁ rewrite lemma-≡-height right x x₂ l₂ r₂ = 
             let acc-xl₂r₂ = rs (node right x l₂ r₂) (lemma-≺-right right x (node perfect x₁ l₁ r₁) (node right x₂ l₂ r₂)) ;
                  x₁l₁r₁⋙push-xl₂r₂ = lemma-⋙r-push x₁ x l₁≃r₁ l₂⋙r₂ l₁≃l₂ acc-xl₂r₂
             in r⋘ x₂ x' x₁l₁r₁⋙push-xl₂r₂ l'≃r' (⋗nd x₁ x'₁ l₁≃r₁ l'₁≃r'₁ l₁⋗l'₁)

  lemma-⋙l-push : {l r l' r' : PLRTree}(x x' : A) → l ≃ r → l' ⋘ r' → l ⋗ r' → (acc : Acc _≺_ (node left x' l' r')) → node perfect x l r ⋙ push (node left x' l' r') acc
  lemma-⋙l-push x x' l≃r (x⋘ x'₁ x'₂ x'₃) (⋗nd x₁ .x'₃ x₂≃x₃ ≃lf (⋗lf x₂)) (acc rs)
      with tot≤ x' x'₁ | tot≤ x' x'₃ | tot≤ x'₁ x'₃
  ... | inj₁ x'≤x'₁ | inj₁ x'≤x'₃ | _ = ⋙l x x' l≃r (x⋘ x'₁ x'₂ x'₃) (⋗nd x₁ x'₃ x₂≃x₃ ≃lf (⋗lf x₂))
  ... | inj₁ x'≤x'₁ | inj₂ x'₃≤x' | _ = ⋙l x x'₃ l≃r (x⋘ x'₁ x'₂ x') (⋗nd x₁ x' x₂≃x₃ ≃lf (⋗lf x₂))
  ... | inj₂ x'₁≤x' | inj₁ x'≤x'₃ | _ 
      with tot≤ x' x'₂
  ... | inj₁ x'≤x'₂ = ⋙l x x'₁ l≃r (x⋘ x' x'₂ x'₃) (⋗nd x₁ x'₃ x₂≃x₃ ≃lf (⋗lf x₂))
  ... | inj₂ x'₂≤x' = ⋙l x x'₁ l≃r (x⋘ x'₂ x' x'₃) (⋗nd x₁ x'₃ x₂≃x₃ ≃lf (⋗lf x₂))
  lemma-⋙l-push x x' l≃r (x⋘ x'₁ x'₂ x'₃) (⋗nd x₁ .x'₃ x₂≃x₃ ≃lf (⋗lf x₂)) (acc rs) | inj₂ x'₁≤x' | inj₂ x'₃≤x' | inj₁ x'₁≤x'₃ 
      with tot≤ x' x'₂
  ... | inj₁ x'≤x'₂ = ⋙l x x'₁ l≃r (x⋘ x' x'₂ x'₃) (⋗nd x₁ x'₃ x₂≃x₃ ≃lf (⋗lf x₂))
  ... | inj₂ x'₂≤x' = ⋙l x x'₁ l≃r (x⋘ x'₂ x' x'₃) (⋗nd x₁ x'₃ x₂≃x₃ ≃lf (⋗lf x₂))
  lemma-⋙l-push x x' l≃r (x⋘ x'₁ x'₂ x'₃) (⋗nd x₁ .x'₃ x₂≃x₃ ≃lf (⋗lf x₂)) (acc rs) | inj₂ x'₁≤x' | inj₂ x'₃≤x' | inj₂ x'₃≤x'₁ =  ⋙l x x'₃ l≃r (x⋘ x'₁ x'₂ x') (⋗nd x₁ x' x₂≃x₃ ≃lf (⋗lf x₂))
  lemma-⋙l-push x x' l≃r (l⋘ {l'₁} {r'₁} {l'₂} {r'₂} x'₁ x'₂ l'₁⋘r'₁ l'₂≃r'₂ r'₁≃l'₂) (⋗nd x₁ .x'₂ l₁≃r₁ _ l₁⋗l'₂) (acc rs)  
      with tot≤ x' x'₁ | tot≤ x' x'₂ | tot≤ x'₁ x'₂
  ... | inj₁ x'≤x'₁ | inj₁ x'≤x'₂ | _ = ⋙l x x' l≃r (l⋘ x'₁ x'₂ l'₁⋘r'₁ l'₂≃r'₂ r'₁≃l'₂) (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂)
  ... | inj₁ x'≤x'₁ | inj₂ x'₂≤x' | _ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂  =
             let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right left x' (node left x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  x'₁l'₁r'₁⋘push-x'l'₂r'₂ = lemma-⋘-push (l⋘ x'₁ x' l'₁⋘r'₁ l'₂≃r'₂ r'₁≃l'₂) acc-x'l'₂r'₂ ;
                  x₁l₁r₁⋗push-x'l'₂r'₂ = lemma-⋗-push (⋗nd x₁ x' l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂) acc-x'l'₂r'₂
             in ⋙l x x'₂ l≃r x'₁l'₁r'₁⋘push-x'l'₂r'₂ x₁l₁r₁⋗push-x'l'₂r'₂ 
  ... | inj₂ x'₁≤x' | inj₁ x'≤x'₂ | _ rewrite lemma-≡-height left x' x'₁ l'₁ r'₁ =
             let acc-x'l'₁r'₁ = rs (node left x' l'₁ r'₁) (lemma-≺-left left x' (node left x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  push-x'l'₁r'₁⋘x'₂l'₂r'₂ = lemma-push-l⋘ x' x'₂ l'₁⋘r'₁ l'₂≃r'₂ r'₁≃l'₂ acc-x'l'₁r'₁
             in ⋙l x x'₁ l≃r push-x'l'₁r'₁⋘x'₂l'₂r'₂ (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂)
  ... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₁ x'₁≤x'₂ rewrite lemma-≡-height left x' x'₁ l'₁ r'₁ = 
             let acc-x'l'₁r'₁ = rs (node left x' l'₁ r'₁) (lemma-≺-left left x' (node left x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  push-x'l'₁r'₁⋘x'₂l'₂r'₂ = lemma-push-l⋘ x' x'₂ l'₁⋘r'₁ l'₂≃r'₂ r'₁≃l'₂ acc-x'l'₁r'₁
             in ⋙l x x'₁ l≃r push-x'l'₁r'₁⋘x'₂l'₂r'₂ (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂)
  ... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₂ x'₂≤x'₁ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂ = 
             let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right left x' (node left x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  x'₁l'₁r'₁⋘push-x'l'₂r'₂ = lemma-⋘-push (l⋘ x'₁ x' l'₁⋘r'₁ l'₂≃r'₂ r'₁≃l'₂) acc-x'l'₂r'₂ ;
                  x₁l₁r₁⋗push-x'l'₂r'₂ = lemma-⋗-push (⋗nd x₁ x' l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂) acc-x'l'₂r'₂
             in ⋙l x x'₂ l≃r x'₁l'₁r'₁⋘push-x'l'₂r'₂ x₁l₁r₁⋗push-x'l'₂r'₂ 
  lemma-⋙l-push x x' l≃r (r⋘ {l'₁} {r'₁} {l'₂} {r'₂} x'₁ x'₂ l'₁⋙r'₁ l'₂≃r'₂ l'₁⋗l'₂) (⋗nd x₁ .x'₂ l₁≃r₁ _ l₁⋗l'₂) (acc rs) 
      with tot≤ x' x'₁ | tot≤ x' x'₂ | tot≤ x'₁ x'₂
  ... | inj₁ x'≤x'₁ | inj₁ x'≤x'₂ | _ = ⋙l x x' l≃r (r⋘ x'₁ x'₂ l'₁⋙r'₁ l'₂≃r'₂ l'₁⋗l'₂) (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂)
  ... | inj₁ x'≤x'₁ | inj₂ x'₂≤x' | _ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂  =
             let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right left x' (node right x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  x'₁l'₁r'₁⋘push-x'l'₂r'₂ = lemma-⋘-push (r⋘ x'₁ x' l'₁⋙r'₁ l'₂≃r'₂ l'₁⋗l'₂) acc-x'l'₂r'₂ ;
                  x₁l₁r₁⋗push-x'l'₂r'₂ = lemma-⋗-push (⋗nd x₁ x' l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂) acc-x'l'₂r'₂
             in ⋙l x x'₂ l≃r x'₁l'₁r'₁⋘push-x'l'₂r'₂ x₁l₁r₁⋗push-x'l'₂r'₂
  ... | inj₂ x'₁≤x' | inj₁ x'≤x'₂ | _ rewrite lemma-≡-height right x' x'₁ l'₁ r'₁ =
             let acc-x'l'₁r'₁ = rs (node right x' l'₁ r'₁) (lemma-≺-left left x' (node right x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  push-x'l'₁r'₁⋘x'₂l'₂r'₂ = lemma-push-r⋘ x' x'₂ l'₁⋙r'₁ l'₂≃r'₂ l'₁⋗l'₂ acc-x'l'₁r'₁
             in ⋙l x x'₁ l≃r push-x'l'₁r'₁⋘x'₂l'₂r'₂ (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂) 
  ... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₁ x'₁≤x'₂ rewrite lemma-≡-height right x' x'₁ l'₁ r'₁ = 
             let acc-x'l'₁r'₁ = rs (node right x' l'₁ r'₁) (lemma-≺-left left x' (node right x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  push-x'l'₁r'₁⋘x'₂l'₂r'₂ = lemma-push-r⋘ x' x'₂ l'₁⋙r'₁ l'₂≃r'₂ l'₁⋗l'₂ acc-x'l'₁r'₁
             in ⋙l x x'₁ l≃r push-x'l'₁r'₁⋘x'₂l'₂r'₂ (⋗nd x₁ x'₂ l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂) 
  ... | inj₂ x'₁≤x' | inj₂ x'₂≤x' | inj₂ x'₂≤x'₁ rewrite lemma-≡-height perfect x' x'₂ l'₂ r'₂ = 
             let acc-x'l'₂r'₂ = rs (node perfect x' l'₂ r'₂) (lemma-≺-right left x' (node right x'₁ l'₁ r'₁) (node perfect x'₂ l'₂ r'₂)) ;
                  x'₁l'₁r'₁⋘push-x'l'₂r'₂ = lemma-⋘-push (r⋘ x'₁ x' l'₁⋙r'₁ l'₂≃r'₂ l'₁⋗l'₂) acc-x'l'₂r'₂ ;
                  x₁l₁r₁⋗push-x'l'₂r'₂ = lemma-⋗-push (⋗nd x₁ x' l₁≃r₁ l'₂≃r'₂ l₁⋗l'₂) acc-x'l'₂r'₂
             in ⋙l x x'₂ l≃r x'₁l'₁r'₁⋘push-x'l'₂r'₂ x₁l₁r₁⋗push-x'l'₂r'₂
 
lemma-⋙-push : {t t' : PLRTree} → t ⋙ t' → (acc : Acc _≺_ t') → t ⋙ push t' acc
lemma-⋙-push (⋙p l⋗r) (acc rs) = ⋙p (lemma-⋗-push l⋗r (acc rs))
lemma-⋙-push (⋙l x x' l≃r l'⋘r' l⋗r') (acc rs) = lemma-⋙l-push x x' l≃r l'⋘r' l⋗r' (acc rs)
lemma-⋙-push (⋙r x x' l≃r l'⋙r' l≃l') (acc rs) = lemma-⋙r-push x x' l≃r l'⋙r' l≃l' (acc rs) 

lemma-push-⋘ : {t t' : PLRTree} → t ⋘ t' → (acc : Acc _≺_ t) → push t acc ⋘ t'
lemma-push-⋘ (x⋘ x y z) _ 
    with tot≤ x y
... | inj₁ x≤y = x⋘ x y z
... | inj₂ y≤x = x⋘ y x z
lemma-push-⋘ (l⋘ x x' l⋘r l'≃r' r≃l') (acc rs) = lemma-push-l⋘ x x' l⋘r l'≃r' r≃l' (acc rs)
lemma-push-⋘ (r⋘ x x' l⋙r l'≃r' l⋗l') (acc rs) = lemma-push-r⋘ x x' l⋙r l'≃r' l⋗l' (acc rs)

lemma-push-complete-≃ : {l r : PLRTree}(x : A) → Complete l → Complete r → l ≃ r → (acc : Acc _≺_ (node perfect x l r)) → Complete (push (node perfect x l r) acc)
lemma-push-complete-≃ {l} {r} x cl cr l≃r (acc rs) 
    with l | r | l≃r | cl | cr
... | leaf | leaf | ≃lf | _ | _ = perfect x leaf leaf ≃lf
... | node perfect x' l' r' | node perfect x'' l'' r'' | ≃nd .x' .x'' l'≃r' l''≃r'' l'≃l'' | perfect .x' cl' cr' _ | perfect .x'' cl'' cr'' _
    with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
... | inj₁ x≤x' | inj₁ x≤x'' | _ = perfect x (perfect x' cl' cr' l'≃r') (perfect x'' cl'' cr'' l''≃r'') (≃nd x' x'' l'≃r' l''≃r'' l'≃l'')
... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height perfect x x'' l'' r'' = 
           let acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right perfect x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                xl''r''≃push-xl''r'' = lemma-≃-push (sym≃ (≃nd x x l'≃r' l''≃r'' l'≃l'')) acc-xl''r'' ;
                x'l'r'≃push-xl''r'' = trans≃ (≃nd x' x l'≃r' l''≃r'' l'≃l'') xl''r''≃push-xl''r''
           in perfect x'' (perfect x' cl' cr' l'≃r') (lemma-push-complete-≃ x cl'' cr'' l''≃r'' acc-xl''r'') x'l'r'≃push-xl''r''
... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height perfect x x' l' r' = 
           let acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left perfect x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                push-xl'r'≃xl'r' = lemma-push-≃ (≃nd x x l'≃r' l''≃r'' l'≃l'') acc-xl'r' ;
                push-xl'r'≃x''l''r'' = trans≃ push-xl'r'≃xl'r' (≃nd x x'' l'≃r' l''≃r'' l'≃l'')
           in perfect x' (lemma-push-complete-≃ x cl' cr' l'≃r' acc-xl'r') (perfect x'' cl'' cr'' l''≃r'') push-xl'r'≃x''l''r''
... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height perfect x x' l' r' = 
           let acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left perfect x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                push-xl'r'≃xl'r' = lemma-push-≃ (≃nd x x l'≃r' l''≃r'' l'≃l'') acc-xl'r' ;
                push-xl'r'≃x''l''r'' = trans≃ push-xl'r'≃xl'r' (≃nd x x'' l'≃r' l''≃r'' l'≃l'')
           in perfect x' (lemma-push-complete-≃ x cl' cr' l'≃r' acc-xl'r') (perfect x'' cl'' cr'' l''≃r'') push-xl'r'≃x''l''r''
... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height perfect x x'' l'' r'' = 
           let acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right perfect x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                xl''r''≃push-xl''r'' = lemma-≃-push (sym≃ (≃nd x x l'≃r' l''≃r'' l'≃l'')) acc-xl''r'' ;
                x'l'r'≃push-xl''r'' = trans≃ (≃nd x' x l'≃r' l''≃r'' l'≃l'') xl''r''≃push-xl''r''
           in perfect x'' (perfect x' cl' cr' l'≃r') (lemma-push-complete-≃ x cl'' cr'' l''≃r'' acc-xl''r'') x'l'r'≃push-xl''r''

lemma-push-complete-⋗ : {l r : PLRTree}(x : A) → Complete l → Complete r → l ⋗ r → (acc : Acc _≺_ (node right x l r)) → Complete (push (node right x l r) acc)
lemma-push-complete-⋗ {l} {r} x cl cr l⋗r (acc rs) 
    with l | r | l⋗r | cl | cr
... | leaf | _ | () | _ | _
... | node perfect x' leaf leaf | leaf | ⋗lf .x' | perfect .x' leaf leaf ≃lf | leaf 
    with tot≤ x x'
... | inj₁ x≤x' = right x (perfect x' leaf leaf ≃lf) leaf (⋙p (⋗lf x')) 
... | inj₂ x'≤x = right x' (perfect x leaf leaf ≃lf) leaf (⋙p (⋗lf x)) 
lemma-push-complete-⋗ x cl cr l⋗r (acc rs) | node perfect x' l' r' | node perfect x'' l'' r'' | ⋗nd .x' .x'' l'≃r' l''≃r'' l'⋗l'' | perfect .x' cl' cr' _ | perfect .x'' cl'' cr'' _
    with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
... | inj₁ x≤x' | inj₁ x≤x'' | _ = right x (perfect x' cl' cr' l'≃r') (perfect x'' cl'' cr'' l''≃r'') (⋙p (⋗nd x' x'' l'≃r' l''≃r'' l'⋗l''))
... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height perfect x x'' l'' r'' = 
           let acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right right x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                x'l'r'⋗push-xl''r'' = lemma-⋗-push (⋗nd x' x l'≃r' l''≃r'' l'⋗l'') acc-xl''r''
           in right x'' (perfect x' cl' cr' l'≃r') (lemma-push-complete-≃ x cl'' cr'' l''≃r'' acc-xl''r'') (⋙p x'l'r'⋗push-xl''r'')
... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height perfect x x' l' r' =  
           let acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left right x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                push-xl'r'⋗x''l''r'' = lemma-push-⋗ (⋗nd x x'' l'≃r' l''≃r'' l'⋗l'') acc-xl'r'
           in right x' (lemma-push-complete-≃ x cl' cr' l'≃r' acc-xl'r') (perfect x'' cl'' cr'' l''≃r'') (⋙p push-xl'r'⋗x''l''r'')
... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height perfect x x' l' r' = 
           let acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left right x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                push-xl'r'⋗x''l''r'' = lemma-push-⋗ (⋗nd x x'' l'≃r' l''≃r'' l'⋗l'') acc-xl'r'
           in right x' (lemma-push-complete-≃ x cl' cr' l'≃r' acc-xl'r') (perfect x'' cl'' cr'' l''≃r'') (⋙p push-xl'r'⋗x''l''r'')
... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height perfect x x'' l'' r'' = 
           let acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right right x (node perfect x' l' r') (node perfect x'' l'' r'')) ;
                x'l'r'⋗push-xl''r'' = lemma-⋗-push (⋗nd x' x l'≃r' l''≃r'' l'⋗l'') acc-xl''r''
           in right x'' (perfect x' cl' cr' l'≃r') (lemma-push-complete-≃ x cl'' cr'' l''≃r'' acc-xl''r'') (⋙p x'l'r'⋗push-xl''r'')

mutual
  lemma-push-complete-⋙ : {l r : PLRTree}(x : A) → Complete l → Complete r → l ⋙ r → (acc : Acc _≺_ (node right x l r)) → Complete (push (node right x l r) acc)
  lemma-push-complete-⋙ {l} {r} x cl cr l⋙r (acc rs) 
      with l | r | l⋙r | cl | cr
  ... | leaf | _ | ⋙p () | _ | _
  ... | node perfect x' leaf leaf | leaf | ⋙p (⋗lf .x') | perfect .x' leaf leaf ≃lf | leaf = 
             lemma-push-complete-⋗ x (perfect x' leaf leaf ≃lf) leaf (⋗lf x') (acc rs) 
  ... | node perfect x' l' r' | node perfect x'' l'' r'' | ⋙p (⋗nd .x' .x'' l'≃r' l''≃r'' l'⋗l'') | perfect .x' cl' cr' _ | perfect .x'' cl'' cr'' _ = 
             lemma-push-complete-⋗ x (perfect x' cl' cr' l'≃r') (perfect x'' cl'' cr'' l''≃r'') (⋗nd x' x'' l'≃r' l''≃r'' l'⋗l'') (acc rs)
  ... | node perfect x' leaf leaf | node left _ _ _ | ⋙p () | _ | _ 
  ... | node perfect x' leaf leaf | node right _ _ _ | ⋙p () | _ | _
  ... | node perfect x' l' r' | node left x'' l'' r'' | ⋙l .x' .x'' l'≃r' l''⋘r'' l'⋗r'' | perfect .x' cl' cr' _ | left .x'' cl'' cr'' _ 
      with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
  ... | inj₁ x≤x' | inj₁ x≤x'' | _ = right x (perfect x' cl' cr' l'≃r') (left x'' cl'' cr'' l''⋘r'') (⋙l x' x'' l'≃r' l''⋘r'' l'⋗r'')
  ... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height left x x'' l'' r'' = 
             let acc-xl''r'' = rs (node left x l'' r'') (lemma-≺-right right x (node perfect x' l' r') (node left x'' l'' r'')) ;
                  x'l'r'⋙push-xl''r'' = lemma-⋙-push (⋙l x' x l'≃r' l''⋘r'' l'⋗r'') acc-xl''r''
             in right x'' (perfect x' cl' cr' l'≃r') (lemma-push-complete-⋘ x cl'' cr'' l''⋘r'' acc-xl''r'') x'l'r'⋙push-xl''r''
  ... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height perfect x x' l' r' = 
             let acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left right x (node perfect x' l' r') (node left x'' l'' r'')) ;
                  push-xl'r'⋙x''l''r'' = lemma-push-⋙ (⋙l x x'' l'≃r' l''⋘r'' l'⋗r'') acc-xl'r'
             in right x' (lemma-push-complete-≃ x cl' cr' l'≃r' acc-xl'r') (left x'' cl'' cr'' l''⋘r'') push-xl'r'⋙x''l''r''
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height perfect x x' l' r' =  
             let acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left right x (node perfect x' l' r') (node left x'' l'' r'')) ;
                  push-xl'r'⋙x''l''r'' = lemma-push-⋙ (⋙l x x'' l'≃r' l''⋘r'' l'⋗r'') acc-xl'r'
             in right x' (lemma-push-complete-≃ x cl' cr' l'≃r' acc-xl'r') (left x'' cl'' cr'' l''⋘r'') push-xl'r'⋙x''l''r''
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height left x x'' l'' r'' =
             let acc-xl''r'' = rs (node left x l'' r'') (lemma-≺-right right x (node perfect x' l' r') (node left x'' l'' r'')) ;
                  x'l'r'⋙push-xl''r'' = lemma-⋙-push (⋙l x' x l'≃r' l''⋘r'' l'⋗r'') acc-xl''r''
             in right x'' (perfect x' cl' cr' l'≃r') (lemma-push-complete-⋘ x cl'' cr'' l''⋘r'' acc-xl''r'') x'l'r'⋙push-xl''r''
  lemma-push-complete-⋙ x cl cr l⋙r (acc rs)| node perfect x' l' r' | node right x'' l'' r'' | ⋙r .x' .x'' l'≃r' l''⋙r'' l'≃l'' | perfect .x' cl' cr' _ | right .x'' cl'' cr'' _ 
      with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
  ... | inj₁ x≤x' | inj₁ x≤x'' | _ = right x (perfect x' cl' cr' l'≃r') (right x'' cl'' cr'' l''⋙r'') (⋙r x' x'' l'≃r' l''⋙r'' l'≃l'')
  ... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height right x x'' l'' r'' = 
             let acc-xl''r'' = rs (node right x l'' r'') (lemma-≺-right right x (node perfect x' l' r') (node right x'' l'' r'')) ;
                  x'l'r'⋙push-xl''r'' = lemma-⋙-push (⋙r x' x l'≃r' l''⋙r'' l'≃l'') acc-xl''r''
             in right x'' (perfect x' cl' cr' l'≃r') (lemma-push-complete-⋙ x cl'' cr'' l''⋙r'' acc-xl''r'') x'l'r'⋙push-xl''r''
  ... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height perfect x x' l' r' = 
             let acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left right x (node perfect x' l' r') (node right x'' l'' r'')) ;
                  push-xl'r'⋙x''l''r'' = lemma-push-⋙ (⋙r x x'' l'≃r' l''⋙r'' l'≃l'') acc-xl'r'
             in right x' (lemma-push-complete-≃ x cl' cr' l'≃r' acc-xl'r') (right x'' cl'' cr'' l''⋙r'') push-xl'r'⋙x''l''r''
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height perfect x x' l' r' = 
             let acc-xl'r' = rs (node perfect x l' r') (lemma-≺-left right x (node perfect x' l' r') (node right x'' l'' r'')) ;
                  push-xl'r'⋙x''l''r'' = lemma-push-⋙ (⋙r x x'' l'≃r' l''⋙r'' l'≃l'') acc-xl'r'
             in right x' (lemma-push-complete-≃ x cl' cr' l'≃r' acc-xl'r') (right x'' cl'' cr'' l''⋙r'') push-xl'r'⋙x''l''r''
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height right x x'' l'' r'' = 
             let acc-xl''r'' = rs (node right x l'' r'') (lemma-≺-right right x (node perfect x' l' r') (node right x'' l'' r'')) ;
                  x'l'r'⋙push-xl''r'' = lemma-⋙-push (⋙r x' x l'≃r' l''⋙r'' l'≃l'') acc-xl''r''
             in right x'' (perfect x' cl' cr' l'≃r') (lemma-push-complete-⋙ x cl'' cr'' l''⋙r'' acc-xl''r'') x'l'r'⋙push-xl''r''
  lemma-push-complete-⋙ x cl cr l⋙r (acc rs) | node left _ _ _ | _ | ⋙p () | _ | _
  lemma-push-complete-⋙ x cl cr l⋙r (acc rs) | node right _ _ _ | _ | ⋙p () | _ | _

  lemma-push-complete-⋘ : {l r : PLRTree}(x : A) → Complete l → Complete r → l ⋘ r → (acc : Acc _≺_ (node left x l r)) → Complete (push (node left x l r) acc)
  lemma-push-complete-⋘ {l} {r} x cl cr l⋘r (acc rs) 
      with l | r | l⋘r | cl | cr
  ... | node left x' l' r' | node perfect x'' l'' r'' | l⋘ .x' .x'' l'⋘r' l''≃r'' r'≃l'' | left .x' cl' cr' _ | perfect .x'' cl'' cr'' _ 
      with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
  ... | inj₁ x≤x' | inj₁ x≤x'' | _ = left x (left x' cl' cr' l'⋘r') (perfect x'' cl'' cr'' l''≃r'') (l⋘ x' x'' l'⋘r' l''≃r'' r'≃l'')
  ... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right left x (node left x' l' r') (node perfect x'' l'' r'')) ;
                  xl''r''≃push-xl''r'' = lemma-≃-push  (≃nd x x l''≃r'' l''≃r'' (lemma-≃-≃ l''≃r'')) acc-xl''r'' ;
                  x''l''r''≃push-xl''r'' = trans≃ (≃nd x'' x l''≃r'' l''≃r'' (lemma-≃-≃ l''≃r'')) xl''r''≃push-xl''r'' ;
                  x'l'r'⋘push-xl''r'' = lemma-⋘-push (l⋘ x' x l'⋘r' l''≃r'' r'≃l'') acc-xl''r'' 
             in left x'' (left x' cl' cr' l'⋘r') (lemma-push-complete-≃ x cl'' cr'' l''≃r'' acc-xl''r'') x'l'r'⋘push-xl''r''
  ... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height left x x' l' r' = 
             let acc-xl'r' = rs (node left x l' r') (lemma-≺-left left x (node left x' l' r') (node perfect x'' l'' r'')) ;
                  push-xl'r'⋘x''l''r'' = lemma-push-⋘ (l⋘ x x'' l'⋘r' l''≃r'' r'≃l'') acc-xl'r' 
             in left x' (lemma-push-complete-⋘ x cl' cr' l'⋘r' acc-xl'r') (perfect x'' cl'' cr'' l''≃r'') push-xl'r'⋘x''l''r''
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height left x x' l' r' = 
             let acc-xl'r' = rs (node left x l' r') (lemma-≺-left left x (node left x' l' r') (node perfect x'' l'' r'')) ;
                  push-xl'r'⋘x''l''r'' = lemma-push-⋘ (l⋘ x x'' l'⋘r' l''≃r'' r'≃l'') acc-xl'r' 
             in left x' (lemma-push-complete-⋘ x cl' cr' l'⋘r' acc-xl'r') (perfect x'' cl'' cr'' l''≃r'') push-xl'r'⋘x''l''r''
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right left x (node left x' l' r') (node perfect x'' l'' r'')) ;
                  xl''r''≃push-xl''r'' = lemma-≃-push  (≃nd x x l''≃r'' l''≃r'' (lemma-≃-≃ l''≃r'')) acc-xl''r'' ;
                  x''l''r''≃push-xl''r'' = trans≃ (≃nd x'' x l''≃r'' l''≃r'' (lemma-≃-≃ l''≃r'')) xl''r''≃push-xl''r'' ;
                  x'l'r'⋘push-xl''r'' = lemma-⋘-push (l⋘ x' x l'⋘r' l''≃r'' r'≃l'') acc-xl''r'' 
             in left x'' (left x' cl' cr' l'⋘r') (lemma-push-complete-≃ x cl'' cr'' l''≃r'' acc-xl''r'') x'l'r'⋘push-xl''r''
  lemma-push-complete-⋘ x cl cr l⋘r (acc rs) | node right x' (node perfect x'' leaf leaf) leaf | node perfect x''' leaf leaf | x⋘ .x' .x'' .x''' | right .x' (perfect .x'' leaf leaf ≃lf) leaf (⋙p (⋗lf .x'')) | perfect .x''' leaf leaf ≃lf  
      with tot≤ x x' | tot≤ x x''' | tot≤ x' x'''
  ... | inj₁ x≤x' | inj₁ x≤x''' | _ = left x (right x' (perfect x'' leaf leaf ≃lf) leaf (⋙p (⋗lf x''))) (perfect x''' leaf leaf ≃lf) (x⋘ x' x'' x''') 
  ... | inj₁ x≤x' | inj₂ x'''≤x | _ = left x''' (right x' (perfect x'' leaf leaf ≃lf) leaf (⋙p (⋗lf x''))) (perfect x leaf leaf ≃lf) (x⋘ x' x'' x) 
  ... | inj₂ x'≤x | inj₁ x≤x''' | _ =
             let acc-xx'' = rs (node right x (node perfect x'' leaf leaf) leaf) (lemma-≺-left left x (node right x' (node perfect x'' leaf leaf) leaf) (node perfect x''' leaf leaf)) ;
                  cdl = lemma-push-complete-⋙ x (perfect x'' leaf leaf ≃lf) leaf (⋙p (⋗lf x'')) acc-xx''
             in left x' cdl (perfect x''' leaf leaf ≃lf) (lemma-push-⋘ (x⋘ x x'' x''') acc-xx'')
  ... | inj₂ x'≤x | inj₂ x'''≤x | inj₁ x'≤x''' = 
             let acc-xx'' = rs (node right x (node perfect x'' leaf leaf) leaf) (lemma-≺-left left x (node right x' (node perfect x'' leaf leaf) leaf) (node perfect x''' leaf leaf)) ;
                  cdl = lemma-push-complete-⋙ x (perfect x'' leaf leaf ≃lf) leaf (⋙p (⋗lf x'')) acc-xx''
             in left x' cdl (perfect x''' leaf leaf ≃lf) (lemma-push-⋘ (x⋘ x x'' x''') acc-xx'')
  ... | inj₂ x'≤x | inj₂ x'''≤x | inj₂ x'''≤x' = left x''' (right x' (perfect x'' leaf leaf ≃lf) leaf (⋙p (⋗lf x''))) (perfect x leaf leaf ≃lf) (x⋘ x' x'' x)
  lemma-push-complete-⋘ x cl cr l⋘r (acc rs) | node right x' l' r' | node perfect x'' l'' r'' | r⋘ .x' .x'' l'⋙r' l''≃r'' l'⋗l'' | right .x' cl' cr' _ | perfect .x'' cl'' cr'' _  
      with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
  ... | inj₁ x≤x' | inj₁ x≤x'' | _ = left x (right x' cl' cr' l'⋙r') (perfect x'' cl'' cr'' l''≃r'') (r⋘ x' x'' l'⋙r' l''≃r'' l'⋗l'')
  ... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right left x (node right x' l' r') (node perfect x'' l'' r'')) ;
                  x'lr'⋘push-xl''r'' = lemma-⋘-push (r⋘ x' x l'⋙r' l''≃r'' l'⋗l'') acc-xl''r''
             in left x'' (right x' cl' cr' l'⋙r') (lemma-push-complete-≃ x cl'' cr'' l''≃r'' acc-xl''r'') x'lr'⋘push-xl''r''
  ... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height right x x' l' r' = 
             let acc-xl'r' = rs (node right x l' r') (lemma-≺-left left x (node right x' l' r') (node perfect x'' l'' r'')) ;
                  push-xl'r'⋘x''l''r'' = lemma-push-⋘ (r⋘ x x'' l'⋙r' l''≃r'' l'⋗l'') acc-xl'r' 
             in left x' (lemma-push-complete-⋙ x cl' cr' l'⋙r' acc-xl'r') (perfect x'' cl'' cr'' l''≃r'') push-xl'r'⋘x''l''r''
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height right x x' l' r' = 
             let acc-xl'r' = rs (node right x l' r') (lemma-≺-left left x (node right x' l' r') (node perfect x'' l'' r'')) ;
                  push-xl'r'⋘x''l''r'' = lemma-push-⋘ (r⋘ x x'' l'⋙r' l''≃r'' l'⋗l'') acc-xl'r' 
             in left x' (lemma-push-complete-⋙ x cl' cr' l'⋙r' acc-xl'r') (perfect x'' cl'' cr'' l''≃r'') push-xl'r'⋘x''l''r''
  ... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height perfect x x'' l'' r'' = 
             let acc-xl''r'' = rs (node perfect x l'' r'') (lemma-≺-right left x (node right x' l' r') (node perfect x'' l'' r'')) ;
                   x'lr'⋘push-xl''r'' = lemma-⋘-push (r⋘ x' x l'⋙r' l''≃r'' l'⋗l'') acc-xl''r''
             in left x'' (right x' cl' cr' l'⋙r') (lemma-push-complete-≃ x cl'' cr'' l''≃r'' acc-xl''r'') x'lr'⋘push-xl''r''

lemma-push-complete : {t : PLRTree} → Complete t → (acc : Acc _≺_ t) → Complete (push t acc)
lemma-push-complete leaf _ = leaf
lemma-push-complete (perfect {l} {r}x cl cr l≃r) (acc rs) = lemma-push-complete-≃ x cl cr l≃r (acc rs)
lemma-push-complete (left {l} {r}x cl cr l⋘r) (acc rs) = lemma-push-complete-⋘ x cl cr l⋘r (acc rs)
lemma-push-complete (right {l} {r}x cl cr l⋙r) (acc rs) = lemma-push-complete-⋙ x cl cr l⋙r (acc rs)
