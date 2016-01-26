module BBHeap.DropLast {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_
open import BBHeap.Compound _≤_
open import BBHeap.Properties _≤_
open import Bound.Lower A 
open import Bound.Lower.Order _≤_
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_)

mutual
  dropLast : {b : Bound} → BBHeap b → BBHeap b
  dropLast leaf = leaf
  dropLast (left b≤x l⋘r)
      with l⋘r | lemma-dropLast⋘ l⋘r
  ... | lf⋘ | _ = leaf
  ... | ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ | inj₁ (≃nd .x≤y₁ .x≤y₂ .l₁⋘r₁ .l₂⋘r₂ l₁≃r₁ _ l₁≃l₂) =
               let l≃r = ≃nd x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂
               in right b≤x (lemma-dropLast≃ l≃r (cl x≤y₁ l₁⋘r₁))
  ... | lr⋘ _ _ _ _ _ _ | inj₁ () 
  ... | _ | inj₂ dl⋘r = left b≤x dl⋘r
  dropLast (right b≤x l⋙r)
      with lemma-dropLast⋙ l⋙r
  ... | inj₁ l⋗r = left b≤x (lemma-dropLast⋗ l⋗r)
  ... | inj₂ l⋙dr = right b≤x l⋙dr

  lemma-dropLast-⊥ : {b : Bound}{l r : BBHeap b} → l ≃ r → dropLast l ⋘ r → Compound l → ⊥
  lemma-dropLast-⊥ () _ (cr _ _)
  lemma-dropLast-⊥ (≃nd b≤x b≤x' l⋘r l'⋘r' l≃r l'≃r' l≃l') dxlr⋘x'l'r' (cl .b≤x .l⋘r)
      with l⋘r | l≃r | l≃l' | l'⋘r' | lemma-dropLast⋘ l⋘r | dxlr⋘x'l'r'
  ... | lf⋘ | ≃lf | _ | _ | _ |  ()
  ... | lr⋘ x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₁≃r₁ l₁⋗l₂ | () | _ | _ | _ | _ 
  ... | ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ | _ | ≃nd .x≤y₁ x'≤y'₁ .l₁⋘r₁ l'₁⋘r'₁ _ l'₁≃r'₁ l₁≃r'₁ | ll⋘ .x'≤y'₁ x'≤y'₂ .l'₁⋘r'₁ l'₂⋘r'₂ l'₂≃r'₂ r'₁≃l'₂ | inj₁ (≃nd .x≤y₁ .x≤y₂ .l₁⋘r₁ .l₂⋘r₂ l₁≃r₁ _ l₁≃l₂) | _dxlr⋘x'l'r' 
      with lemma-dropLast≃ (≃nd x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) (cl x≤y₁ l₁⋘r₁) | _dxlr⋘x'l'r'
  ... | l⋙dr | lr⋘ .b≤x .b≤x' .l⋙dr .(ll⋘ x'≤y'₁ x'≤y'₂ l'₁⋘r'₁ l'₂⋘r'₂ l'₂≃r'₂ r'₁≃l'₂) _ l⋗l'
      with lemma-≃-⊥ (≃nd x≤y₁ x'≤y'₁ l₁⋘r₁ l'₁⋘r'₁ l₁≃r₁ l'₁≃r'₁ l₁≃r'₁) l⋗l'
  ... | ()
  lemma-dropLast-⊥ (≃nd b≤x b≤x' l⋘r l'⋘r' l≃r l'≃r' l≃l') dxlr⋘x'l'r' (cl .b≤x .l⋘r) | ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ | ≃nd .x≤y₁ .x≤y₂ .l₁⋘r₁ .l₂⋘r₂ l₁≃r₁ _ l₁≃l₂ | _ | _ | inj₂ dl⋘r | _
      with lemma-dropLast-⊥ (≃nd x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) dl⋘r (cl x≤y₁ l₁⋘r₁)
  ... | ()
  
  lemma-dropLast≃ : {b : Bound}{l r : BBHeap b} → l ≃ r → Compound l → l ⋙ dropLast r
  lemma-dropLast≃ () (cr _ _) 
  lemma-dropLast≃ (≃nd b≤x b≤x' l⋘r l'⋘r' l≃r l'≃r' l≃l') (cl .b≤x .l⋘r)
      with l'≃r' | l≃l' | l≃r | l⋘r | l'⋘r' | lemma-dropLast⋘ l'⋘r'
  ... | ≃lf | ≃lf | ≃lf | lf⋘ | lf⋘ | _ = ⋙lf b≤x 
  ... | ≃nd x'≤y₁ x'≤y₂ l₁⋘r₁ l₂⋘r₂ _ _ _ | _ | _l≃r | _l⋘r | ll⋘ .x'≤y₁ .x'≤y₂ .l₁⋘r₁ .l₂⋘r₂ l₂≃r₂ _ | inj₁ (≃nd .x'≤y₁ .x'≤y₂ .l₁⋘r₁ .l₂⋘r₂ l₁≃r₁ _ l₁≃l₂) =
                 let l'≃r' = ≃nd x'≤y₁ x'≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂ ;
                      l'⋙dr' = lemma-dropLast≃ l'≃r' (cl x'≤y₁ l₁⋘r₁)
                 in ⋙rr b≤x b≤x' _l⋘r _l≃r l'⋙dr' l≃l'
  ... | ≃nd x'≤y₁ x'≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂ | _l≃l' | _l≃r | _l⋘r | ll⋘ .x'≤y₁ .x'≤y₂ .l₁⋘r₁ .l₂⋘r₂ _ _ | inj₂ dl'⋘r' 
      with lemma-dropLast-⊥ (≃nd x'≤y₁ x'≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) dl'⋘r' (cl x'≤y₁ l₁⋘r₁)
  ... | ()

  lemma-dropLast⋗ : {b : Bound}{l r : BBHeap b} → l ⋗ r → dropLast l ⋘ r
  lemma-dropLast⋗ (⋗lf b≤x) = lf⋘
  lemma-dropLast⋗ (⋗nd b≤x b≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l')
      with l⋘r | l≃r | l⋗l' | lemma-dropLast⋘ l⋘r
  ... | lf⋘ | _ | () | _
  ... | lr⋘ x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₁≃r₁ l₁⋗l₂ | _ | _ | inj₁ () 
  ... | lr⋘ x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₁≃r₁ l₁⋗l₂ | () | _ | inj₂ _ 
  ... | ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ | _ | _ | inj₁ (≃nd .x≤y₁ .x≤y₂ .l₁⋘r₁ .l₂⋘r₂ l₁≃r₁ _ l₁≃l₂) =
                let _l≃r = ≃nd x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂ ;
                     l⋙dr = lemma-dropLast≃ _l≃r (cl x≤y₁ l₁⋘r₁) 
                in lr⋘ b≤x b≤x' l⋙dr l'⋘r' l'≃r' l⋗l'
  ... | ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ _ r₁≃l₂ | ≃nd .x≤y₁ .x≤y₂ .l₁⋘r₁ .l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂ | _ | inj₂ dl⋘r
      with lemma-dropLast-⊥ (≃nd x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂) dl⋘r (cl x≤y₁ l₁⋘r₁)
  ... | ()
  
  lemma-dropLast⋘ : {b : Bound}{l r : BBHeap b} → l ⋘ r → l ≃ r ∨ dropLast l ⋘ r
  lemma-dropLast⋘ lf⋘ = inj₁ ≃lf
  lemma-dropLast⋘ (ll⋘ b≤x b≤x' l⋘r l'⋘r' l'≃r' r≃l')
      with l⋘r | l'⋘r' | r≃l' | lemma-dropLast⋘ l⋘r
  ... | lf⋘ | lf⋘ | ≃lf | _ = inj₁ (≃nd b≤x b≤x' lf⋘ lf⋘ ≃lf ≃lf ≃lf)
  ... | ll⋘ x'≤y₁ x'≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ | _l'⋘r' | _r≃l' | inj₁ l≃r =
               let l≃l' = trans≃ l≃r _r≃l' ;
                    _l⋘r = ll⋘ x'≤y₁ x'≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂
               in inj₁ (≃nd b≤x b≤x' _l⋘r _l'⋘r' l≃r l'≃r' l≃l')
  ... | ll⋘ x'≤y₁ x'≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ | _l'⋘r' | _r≃l' | inj₂ dl⋘r = inj₂ (ll⋘ b≤x b≤x' dl⋘r _l'⋘r' l'≃r' _r≃l')
  ... | lr⋘ x'≤y₁ x'≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ | _l'⋘r' | _r≃l' | inj₁ l≃r =
               let l≃l' = trans≃ l≃r _r≃l' ;
                    _l⋘r = lr⋘ x'≤y₁ x'≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂
               in inj₁ (≃nd b≤x b≤x' _l⋘r _l'⋘r' l≃r l'≃r' l≃l')
  ... | lr⋘ x'≤y₁ x'≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ | _l'⋘r' | _r≃l' | inj₂ dl⋘r = inj₂ (ll⋘ b≤x b≤x' dl⋘r _l'⋘r' l'≃r' _r≃l')
  lemma-dropLast⋘ (lr⋘ b≤x b≤x' l⋙r l'⋘r' l'≃r' l⋗l')
      with lemma-dropLast⋙ l⋙r
  ... | inj₁ l⋗r =
               let dl⋘r = lemma-dropLast⋗ l⋗r ;
                    r≃l' = lemma⋗⋗' l⋗r l⋗l'
               in inj₂ (ll⋘ b≤x b≤x' dl⋘r l'⋘r' l'≃r' r≃l')
  ... | inj₂ l⋙dr = inj₂ (lr⋘ b≤x b≤x' l⋙dr l'⋘r' l'≃r' l⋗l')

  lemma-dropLast⋙ : {b : Bound}{l r : BBHeap b} → l ⋙ r → l ⋗ r ∨ l ⋙ dropLast r
  lemma-dropLast⋙ (⋙lf b≤x) = inj₁ (⋗lf b≤x)
  lemma-dropLast⋙ (⋙rl b≤x b≤x' l⋘r l≃r l'⋘r' l⋗r')
      with l'⋘r' | l≃r | l⋗r' | lemma-dropLast⋘ l'⋘r'
  ... | lf⋘ | ≃nd x≤y _ lf⋘ lf⋘ ≃lf ≃lf ≃lf | ⋗lf .x≤y | _ = inj₁ (⋗nd b≤x b≤x' l⋘r lf⋘ l≃r ≃lf (⋗lf x≤y))
  ... | ll⋘ x'≤y₁ x'≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ | _l≃r | _l⋗r' | inj₁ l'≃r' =
             let l⋗l' = lemma⋗≃ _l⋗r' (sym≃ l'≃r') ;
                  _l'⋘r' = ll⋘ x'≤y₁ x'≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂
             in inj₁ (⋗nd b≤x b≤x' l⋘r _l'⋘r' _l≃r l'≃r' l⋗l')
  ... | ll⋘ x'≤y₁ x'≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ | _l≃r | _l⋗r' | inj₂ dl'⋘r' = inj₂ (⋙rl b≤x b≤x' l⋘r _l≃r dl'⋘r' _l⋗r')
  ... | lr⋘ x'≤y₁ x'≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ | _l≃r | _l⋗r' | inj₁ l'≃r' =
             let l⋗l' = lemma⋗≃ _l⋗r' (sym≃ l'≃r') ;
                  _l'⋘r' = lr⋘ x'≤y₁ x'≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂
             in inj₁ (⋗nd b≤x b≤x' l⋘r _l'⋘r' _l≃r l'≃r' l⋗l')
  ... | lr⋘ x'≤y₁ x'≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ | _l≃r | _l⋗r' | inj₂ dl'⋘r' = inj₂ (⋙rl b≤x b≤x' l⋘r _l≃r dl'⋘r' _l⋗r') 
  lemma-dropLast⋙ (⋙rr b≤x b≤x' l⋘r l≃r l'⋙r' l≃l')
      with lemma-dropLast⋙ l'⋙r'
  ... | inj₁ l'⋗r' =
               let dl'⋘r' = lemma-dropLast⋗ l'⋗r' ;
                    l⋗r' = lemma≃⋗ l≃l' l'⋗r'
               in inj₂ (⋙rl b≤x b≤x' l⋘r l≃r dl'⋘r' l⋗r')
  ... | inj₂ l'⋙dr' = inj₂ (⋙rr b≤x b≤x' l⋘r l≃r l'⋙dr' l≃l')
