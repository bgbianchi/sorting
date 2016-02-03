open import Relation.Binary.Core

module BBHeap.Drop {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_
open import BBHeap.Compound _≤_
open import BBHeap.Equality _≤_
open import BBHeap.Equality.Properties _≤_
open import BBHeap.Subtyping.Properties _≤_ trans≤
open import BBHeap.Perfect _≤_
open import BBHeap.Properties _≤_
open import BBHeap.Push _≤_ tot≤ trans≤
open import Bound.Lower A 
open import Bound.Lower.Order _≤_
open import Bound.Lower.Order.Properties _≤_ trans≤
open import Data.Empty
open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Order.Total _≤_ tot≤ 

root : {b : Bound}{h : BBHeap b}(cₕ : Compound h) → A
root (cl {x = x} _ _) = x
root (cr {x = x} _ _) = x

mutual 
  drop : {b : Bound}{h : BBHeap b}(cₕ : Compound h) → BBHeap (val (root cₕ))
  drop (cl b≤x l⋘r) = drop⋘ b≤x l⋘r
  drop (cr b≤x l⋙r) = drop⋙ b≤x l⋙r

  drop⋘ : {b : Bound}{x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x)) → l ⋘ r → BBHeap (val x)
  drop⋘ b≤x lf⋘ = leaf
  drop⋘ b≤x (ll⋘ {x = y₁} {x' = y₂} x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
      with tot≤ y₁ y₂ | lemma-drop⋘ (cl x≤y₁ l₁⋘r₁) (cl x≤y₂ l₂⋘r₂) (ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
  ... | inj₁ y₁≤y₂ | inj₁ (_ , l⋙dr) = 
                     let pl'≈l' = lemma-push⋘ (lexy y₁≤y₂) (lexy refl≤) l₁⋘r₁ ;
                          l'≈l = ≈left (lexy refl≤) x≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                          pl'≈l = trans≈ pl'≈l' l'≈l ;
                          pl'⋙dr = lemma≈⋙ pl'≈l l⋙dr ;
                          pl'⋙dr' = subtyping⋙r (lexy y₁≤y₂) pl'⋙dr
                     in right x≤y₁ pl'⋙dr'
  ... | inj₁ y₁≤y₂ | inj₂ dl⋘r =
                     let r≈r' = ≈left x≤y₂ (lexy y₁≤y₂) l₂⋘r₂ l₂⋘r₂ refl≈ refl≈ ;
                          dl⋘r' = lemma⋘≈ dl⋘r r≈r'
                     in left x≤y₁ dl⋘r'
  ... | inj₂ y₂≤y₁ | inj₁ (_ , l⋙dr) =
                     let l'≈l = ≈left (lexy y₂≤y₁) x≤y₁ l₁⋘r₁  l₁⋘r₁ refl≈ refl≈ ;
                          l'⋙dr = lemma≈⋙ l'≈l l⋙dr
                     in right x≤y₂ l'⋙dr 
  ... | inj₂ y₂≤y₁ | inj₂ dl⋘r =
                     let pr'≈r' = lemma-push⋘ (lexy y₂≤y₁) (lexy refl≤) l₂⋘r₂ ;
                          r'≈pr' = sym≈ pr'≈r' ;
                          r≈r' = ≈left x≤y₂ (lexy refl≤) l₂⋘r₂ l₂⋘r₂ refl≈ refl≈ ;
                          r≈pr' = trans≈ r≈r' r'≈pr' ;
                          dl⋘pr' = lemma⋘≈ dl⋘r r≈pr' ;
                          dl'⋘pr' = subtyping⋘l (lexy y₂≤y₁) dl⋘pr'
                     in left x≤y₂ dl'⋘pr'
  drop⋘ b≤x (lr⋘ {x = y₁} {x' = y₂} x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
      with tot≤ y₁ y₂ | lemma-drop⋘ (cr x≤y₁ l₁⋙r₁) (cl x≤y₂ l₂⋘r₂) (lr⋘ x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
  ... | _ | inj₁ (() , _)
  ... | inj₁ y₁≤y₂ | inj₂ dl⋘r =
                     let r≈r' = ≈left x≤y₂ (lexy y₁≤y₂) l₂⋘r₂ l₂⋘r₂ refl≈ refl≈ ;
                          dl⋘r' = lemma⋘≈ dl⋘r r≈r'
                     in left x≤y₁ dl⋘r'
  ... | inj₂ y₂≤y₁ | inj₂ dl⋘r =
                     let pr'≈r' = lemma-push⋘ (lexy y₂≤y₁) (lexy refl≤) l₂⋘r₂ ;
                          r'≈pr' = sym≈ pr'≈r' ;
                          r≈r' = ≈left x≤y₂ (lexy refl≤) l₂⋘r₂ l₂⋘r₂ refl≈ refl≈ ;
                          r≈pr' = trans≈ r≈r' r'≈pr' ;
                          dl⋘pr' = lemma⋘≈ dl⋘r r≈pr' ;
                          dl'⋘pr' = subtyping⋘l (lexy y₂≤y₁) dl⋘pr'
                     in left x≤y₂ dl'⋘pr'

  drop⋙ : {b : Bound}{x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x)) → l ⋙ r → BBHeap (val x)
  drop⋙ b≤x (⋙lf x≤y) = left x≤y lf⋘
  drop⋙ b≤x (⋙rl {x = y₁} {x' = y₂} x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
      with tot≤ y₁ y₂ | lemma-drop⋙ (cl x≤y₁ l₁⋘r₁) (cl x≤y₂ l₂⋘r₂) (⋙rl x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
  ... | inj₁ y₁≤y₂ | inj₁ (_ , dl⋘r) =
                       let r≈r' = ≈left x≤y₂ (lexy y₁≤y₂) l₂⋘r₂ l₂⋘r₂ refl≈ refl≈ ;
                            dl⋘r' = lemma⋘≈ dl⋘r r≈r'
                       in left x≤y₁ dl⋘r'
  ... | inj₁ y₁≤y₂ | inj₂ l⋙dr =
                       let l'≈l = ≈left (lexy refl≤) x≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                            pl'≈l' = lemma-push⋘ (lexy y₁≤y₂) (lexy refl≤) l₁⋘r₁ ;
                            pl'≈l = trans≈ pl'≈l' l'≈l ;
                            pl'⋙dr = lemma≈⋙ pl'≈l l⋙dr ;
                            pl'⋙dr' = subtyping⋙r (lexy y₁≤y₂) pl'⋙dr
                       in right x≤y₁ pl'⋙dr'
  ... | inj₂ y₂≤y₁ | inj₁ (_ , dl⋘r) =
                       let pr'≈r' = lemma-push⋘ (lexy y₂≤y₁) (lexy refl≤) l₂⋘r₂ ;
                            r'≈r = ≈left (lexy refl≤) x≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈ ;
                            pr'≈r = trans≈ pr'≈r' r'≈r ;
                            r≈pr' = sym≈ pr'≈r ;
                            dl⋘pr' = lemma⋘≈ dl⋘r r≈pr' ;
                            dl'⋘pr' = subtyping⋘l (lexy y₂≤y₁) dl⋘pr' 
                       in left x≤y₂ dl'⋘pr'
  ... | inj₂ y₂≤y₁ | inj₂ l⋙dr =
                       let l'≈l = ≈left (lexy y₂≤y₁) x≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                            l'⋙dr = lemma≈⋙ l'≈l l⋙dr 
                       in right x≤y₂ l'⋙dr
  drop⋙ b≤x (⋙rr {x = y₁} {x' = y₂} x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
      with tot≤ y₁ y₂ | lemma-drop⋙ (cl x≤y₁ l₁⋘r₁) (cr x≤y₂ l₂⋙r₂) (⋙rr x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
  ... | _ | inj₁ (() , _)
  ... | inj₁ y₁≤y₂ | inj₂ l⋙dr =
                       let l'≈l = ≈left (lexy refl≤) x≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                            pl'≈l' = lemma-push⋘ (lexy y₁≤y₂) (lexy refl≤) l₁⋘r₁ ;
                            pl'≈l = trans≈ pl'≈l' l'≈l ;
                            pl'⋙dr = lemma≈⋙ pl'≈l l⋙dr ;
                            pl'⋙dr' = subtyping⋙r (lexy y₁≤y₂) pl'⋙dr
                       in right x≤y₁ pl'⋙dr'
  ... | inj₂ y₂≤y₁ | inj₂ l⋙dr =
                       let l'≈l = ≈left (lexy y₂≤y₁) x≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                            l'⋙dr = lemma≈⋙ l'≈l l⋙dr 
                       in right x≤y₂ l'⋙dr

  lemma-drop⋘ : {b : Bound}{l r : BBHeap b}(cₗ : Compound l)(cᵣ : Compound r) → l ⋘ r → l ≃ r ∧ l ⋙ drop cᵣ ∨ drop cₗ ⋘ r
  lemma-drop⋘ (cl y≤y₁ lf⋘) (cl y≤y₂ lf⋘) (ll⋘ .y≤y₁ .y≤y₂ .lf⋘ .lf⋘ ≃lf ≃lf) = inj₁ (≃nd y≤y₁ y≤y₂ lf⋘ lf⋘ ≃lf ≃lf ≃lf , ⋙lf y≤y₁)
  lemma-drop⋘ (cl y≤y₁ (ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄)) (cl y≤y₂ lf⋘) (ll⋘ .y≤y₁ .y≤y₂ .(ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄) .lf⋘ _ ()) 
  lemma-drop⋘ (cl y≤y₁ (ll⋘ {x = y₃} {x' = y₄} y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄)) (cl y≤y₂ (ll⋘ {x = y₅} {x' = y₆} y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆)) (ll⋘ {x = y₁} .y≤y₁ .y≤y₂ .(ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄) .(ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆) l₂≃r₂ r₁≃l₂) 
      with tot≤ y₃ y₄ | tot≤ y₅ y₆ | lemma-drop⋘ (cl y₁≤y₃ l₃⋘r₃) (cl y₁≤y₄ l₄⋘r₄) (ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄) | lemma-drop⋘ (cl y₂≤y₅ l₅⋘r₅) (cl y₂≤y₆ l₆⋘r₆) (ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆)
  ... | _ | inj₁ y₅≤y₆ | inj₁ (l₁≃r₁ , _) | inj₁ (_ , l₂⋙dr₂) =
                       let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                            l₂⋘r₂ = ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆ ;
                            l₁≃l₂ = trans≃ l₁≃r₁ r₁≃l₂ ;
                            pl₂'≈l₂' = lemma-push⋘ (lexy y₅≤y₆) (lexy refl≤) l₅⋘r₅ ;
                            l₂'≈l₂ = ≈left (lexy refl≤) y₂≤y₅ l₅⋘r₅ l₅⋘r₅ refl≈ refl≈ ;
                            pl₂'≈l₂ = trans≈ pl₂'≈l₂' l₂'≈l₂ ;
                            pl₂'⋙dr₂ = lemma≈⋙ pl₂'≈l₂ l₂⋙dr₂ ;
                            pl₂'⋙dr₂' = subtyping⋙r (lexy y₅≤y₆) pl₂'⋙dr₂ ;
                            l₂≈pl₂' = sym≈ pl₂'≈l₂ ;
                            l₁≃pl₂' = lemma≃≈ l₁≃l₂ l₂≈pl₂'
                       in inj₁ (≃nd y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂ , ⋙rr y≤y₁ y₂≤y₅ l₁⋘r₁ l₁≃r₁ pl₂'⋙dr₂' l₁≃pl₂')
  ... | _ | inj₂ y₆≤y₅ | inj₁ (l₁≃r₁ , _) | inj₁ (_ , l₂⋙dr₂) =
                       let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                            l₂⋘r₂ = ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆ ;
                            l₁≃l₂ = trans≃ l₁≃r₁ r₁≃l₂ ;
                            l₂'≈l₂ = ≈left (lexy y₆≤y₅) y₂≤y₅ l₅⋘r₅ l₅⋘r₅ refl≈ refl≈ ;
                            l₂'⋙dr₂ = lemma≈⋙ l₂'≈l₂ l₂⋙dr₂ ;
                            l₂≈l₂' = sym≈ l₂'≈l₂ ;
                            l₁≃l₂' = lemma≃≈ l₁≃l₂ l₂≈l₂'
                       in inj₁ (≃nd y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂ , ⋙rr y≤y₁ y₂≤y₆ l₁⋘r₁ l₁≃r₁ l₂'⋙dr₂ l₁≃l₂')
  ... | inj₁ y₃≤y₄ | _ | inj₂ dl₁⋘r₁ | _ =
                       let r₁≈r₁' = ≈left y₁≤y₄ (lexy y₃≤y₄) l₄⋘r₄ l₄⋘r₄ refl≈ refl≈ ;
                            dl₁⋘r₁' = lemma⋘≈ dl₁⋘r₁ r₁≈r₁' ;
                            l₂⋘r₂ = ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆ ;
                            r₁'≈r₁ = sym≈ r₁≈r₁' ;
                            r₁'≃l₂ = lemma≈≃ r₁'≈r₁ r₁≃l₂
                       in inj₂ (ll⋘ y₁≤y₃ y≤y₂ dl₁⋘r₁' l₂⋘r₂ l₂≃r₂ r₁'≃l₂)
  ... | inj₂ y₄≤y₃ | _ | inj₂ dl₁⋘r₁ | _ =
                       let r₁≈r₁' = ≈left y₁≤y₄ (lexy refl≤) l₄⋘r₄ l₄⋘r₄ refl≈ refl≈ ;
                            pr₁'≈r₁' = lemma-push⋘ (lexy y₄≤y₃) (lexy refl≤) l₄⋘r₄ ;
                            dl₁⋘r₁' = lemma⋘≈ dl₁⋘r₁ r₁≈r₁' ;
                            r₁'≈pr₁' = sym≈ pr₁'≈r₁' ;
                            r₁≈pr₁' = trans≈ r₁≈r₁' r₁'≈pr₁' ;
                            dl₁⋘pr₁' = lemma⋘≈ dl₁⋘r₁ r₁≈pr₁' ; 
                            l₂⋘r₂ = ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆ ;
                            dl₁'⋘pr₁' = subtyping⋘l (lexy y₄≤y₃) dl₁⋘pr₁' ;
                            r₁'≈r₁ = sym≈ r₁≈r₁' ;
                            r₁'≃l₂ = lemma≈≃ r₁'≈r₁ r₁≃l₂ ;
                            pr₁'≃l₂ = lemma≈≃ pr₁'≈r₁' r₁'≃l₂
                       in inj₂ (ll⋘ y₁≤y₄ y≤y₂ dl₁'⋘pr₁' l₂⋘r₂ l₂≃r₂ pr₁'≃l₂)
  ... | _ | _ | inj₁ (l₁≃r₁ , l₁⋙dr₁) | inj₂ dl₂⋘r₂
      with lemma-drop-⊥ y₂≤y₅ l₅⋘r₅ (lemma-⋘-≃ dl₂⋘r₂ (sym≃ l₂≃r₂))
  ... | ()
  lemma-drop⋘ (cl y≤y₁ (ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄)) (cl y≤y₂ (lr⋘ y₂≤y₅ y₂≤y₆ l₅⋙r₅ l₆⋘r₆ l₆≃r₆ l₅⋗l₆)) (ll⋘ .y≤y₁ .y≤y₂ .(ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄) .(lr⋘ y₂≤y₅ y₂≤y₆ l₅⋙r₅ l₆⋘r₆ l₆≃r₆ l₅⋗l₆) _ ())
  lemma-drop⋘ (cl y≤y₁ (lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄)) (cl y≤y₂ lf⋘) (ll⋘ .y≤y₁ .y≤y₂ .(lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄) .lf⋘ _ ()) 
  lemma-drop⋘ (cl y≤y₁ (lr⋘ {x = y₃} {x' = y₄} y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄)) (cl y≤y₂ (ll⋘ {x = y₅} {x' = y₆} y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆)) (ll⋘ .y≤y₁ .y≤y₂ .(lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄) .(ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆) l₂≃r₂ r₁≃l₂) 
      with tot≤ y₃ y₄ | tot≤ y₅ y₆ | lemma-drop⋘ (cr y₁≤y₃ l₃⋙r₃) (cl y₁≤y₄ l₄⋘r₄) (lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄) | lemma-drop⋘ (cl y₂≤y₅ l₅⋘r₅) (cl y₂≤y₆ l₆⋘r₆) (ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆)
  ... | _ | inj₁ y₅≤y₆ | inj₁ (l₁≃r₁ , _) | inj₁ (_ , l₂⋙dr₂) =
                       let l₁⋘r₁ = lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄ ;
                            l₂⋘r₂ = ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆ ;
                            l₁≃l₂ = trans≃ l₁≃r₁ r₁≃l₂ ;
                            pl₂'≈l₂' = lemma-push⋘ (lexy y₅≤y₆) (lexy refl≤) l₅⋘r₅ ;
                            l₂'≈l₂ = ≈left (lexy refl≤) y₂≤y₅ l₅⋘r₅ l₅⋘r₅ refl≈ refl≈ ;
                            pl₂'≈l₂ = trans≈ pl₂'≈l₂' l₂'≈l₂ ;
                            pl₂'⋙dr₂ = lemma≈⋙ pl₂'≈l₂ l₂⋙dr₂ ;
                            pl₂'⋙dr₂' = subtyping⋙r (lexy y₅≤y₆) pl₂'⋙dr₂ ;
                            l₂≈pl₂' = sym≈ pl₂'≈l₂ ;
                            l₁≃pl₂' = lemma≃≈ l₁≃l₂ l₂≈pl₂'
                       in inj₁ (≃nd y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂ , ⋙rr y≤y₁ y₂≤y₅ l₁⋘r₁ l₁≃r₁ pl₂'⋙dr₂' l₁≃pl₂')
  ... | _ | inj₂ y₆≤y₅ | inj₁ (l₁≃r₁ , _) | inj₁ (_ , l₂⋙dr₂) =
                       let l₁⋘r₁ = lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄ ;
                            l₂⋘r₂ = ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆ ;
                            l₁≃l₂ = trans≃ l₁≃r₁ r₁≃l₂ ;
                            l₂'≈l₂ = ≈left (lexy y₆≤y₅) y₂≤y₅ l₅⋘r₅ l₅⋘r₅ refl≈ refl≈ ;
                            l₂'⋙dr₂ = lemma≈⋙ l₂'≈l₂ l₂⋙dr₂ ;
                            l₂≈l₂' = sym≈ l₂'≈l₂ ;
                            l₁≃l₂' = lemma≃≈ l₁≃l₂ l₂≈l₂'
                       in inj₁ (≃nd y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁≃l₂ , ⋙rr y≤y₁ y₂≤y₆ l₁⋘r₁ l₁≃r₁ l₂'⋙dr₂ l₁≃l₂')
  ... | inj₁ y₃≤y₄ | _ | inj₂ dl₁⋘r₁ | _ =
                       let r₁≈r₁' = ≈left y₁≤y₄ (lexy y₃≤y₄) l₄⋘r₄ l₄⋘r₄ refl≈ refl≈ ;
                            dl₁⋘r₁' = lemma⋘≈ dl₁⋘r₁ r₁≈r₁' ;
                            l₂⋘r₂ = ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆ ;
                            r₁'≈r₁ = sym≈ r₁≈r₁' ;
                            r₁'≃l₂ = lemma≈≃ r₁'≈r₁ r₁≃l₂
                       in inj₂ (ll⋘ y₁≤y₃ y≤y₂ dl₁⋘r₁' l₂⋘r₂ l₂≃r₂ r₁'≃l₂)
  ... | inj₂ y₄≤y₃ | _ | inj₂ dl₁⋘r₁ | _ =
                       let r₁≈r₁' = ≈left y₁≤y₄ (lexy refl≤) l₄⋘r₄ l₄⋘r₄ refl≈ refl≈ ;
                            pr₁'≈r₁' = lemma-push⋘ (lexy y₄≤y₃) (lexy refl≤) l₄⋘r₄ ;
                            dl₁⋘r₁' = lemma⋘≈ dl₁⋘r₁ r₁≈r₁' ;
                            r₁'≈pr₁' = sym≈ pr₁'≈r₁' ;
                            r₁≈pr₁' = trans≈ r₁≈r₁' r₁'≈pr₁' ;
                            dl₁⋘pr₁' = lemma⋘≈ dl₁⋘r₁ r₁≈pr₁' ; 
                            l₂⋘r₂ = ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆ ;
                            dl₁'⋘pr₁' = subtyping⋘l (lexy y₄≤y₃) dl₁⋘pr₁' ;
                            r₁'≈r₁ = sym≈ r₁≈r₁' ;
                            r₁'≃l₂ = lemma≈≃ r₁'≈r₁ r₁≃l₂ ;
                            pr₁'≃l₂ = lemma≈≃ pr₁'≈r₁' r₁'≃l₂
                       in inj₂ (ll⋘ y₁≤y₄ y≤y₂ dl₁'⋘pr₁' l₂⋘r₂ l₂≃r₂ pr₁'≃l₂)
  ... | _ | _ | inj₁ (l₁≃r₁ , l₁⋙dr₁) | inj₂ dl₂⋘r₂
      with lemma-drop-⊥ y₂≤y₅ l₅⋘r₅ (lemma-⋘-≃ dl₂⋘r₂ (sym≃ l₂≃r₂))
  ... | ()
  lemma-drop⋘ (cl y≤y₁ (lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄)) (cl y≤y₂ (lr⋘ y₂≤y₅ y₂≤y₆ l₅⋙r₅ l₆⋘r₆ l₆≃r₆ l₅⋗l₆)) (ll⋘ .y≤y₁ .y≤y₂ .(lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄) .(lr⋘ y₂≤y₅ y₂≤y₆ l₅⋙r₅ l₆⋘r₆ l₆≃r₆ l₅⋗l₆) () _) 
  lemma-drop⋘ (cr y≤y₁ (⋙lf y₁≤y₃)) (cl y≤y₂ lf⋘) (lr⋘ .y≤y₁ .y≤y₂ .(⋙lf y₁≤y₃) .lf⋘ ≃lf (⋗lf .y₁≤y₃)) = inj₂ (ll⋘ y₁≤y₃ y≤y₂ lf⋘ lf⋘ ≃lf ≃lf)
  lemma-drop⋘ (cr y≤y₁ (⋙lf y₁≤y₃)) (cl y≤y₂ (ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆)) (lr⋘ .y≤y₁ .y≤y₂ .(⋙lf y₁≤y₃) .(ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆) _ (⋗nd .y₁≤y₃ .y₂≤y₅ .lf⋘ .l₅⋘r₅ _ _ ())) 
  lemma-drop⋘ (cr y≤y₁ (⋙lf y₁≤y₃)) (cl y≤y₂ (lr⋘ y₂≤y₅ y₂≤y₆ l₅⋙r₅ l₆⋘r₆ l₆≃r₆ l₅⋗l₆)) (lr⋘ .y≤y₁ .y≤y₂ .(⋙lf y₁≤y₃) .(lr⋘ y₂≤y₅ y₂≤y₆ l₅⋙r₅ l₆⋘r₆ l₆≃r₆ l₅⋗l₆) () _) 
  lemma-drop⋘ (cr y≤y₁ (⋙rl {x = y₃} {x' = y₄} y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₃≃r₃ l₄⋘r₄ l₃⋗r₄)) (cl y≤y₂ l₂⋘r₂) (lr⋘ .y≤y₁ .y≤y₂ .(⋙rl y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₃≃r₃ l₄⋘r₄ l₃⋗r₄) .l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
      with tot≤ y₃ y₄ | lemma-drop⋙ (cl y₁≤y₃ l₃⋘r₃) (cl y₁≤y₄ l₄⋘r₄) (⋙rl y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₃≃r₃ l₄⋘r₄ l₃⋗r₄)
  ... | inj₁ y₃≤y₄ | inj₁ (l₁⋗r₁ , dl₁⋘r₁) =
                       let r₁≈r₁' = ≈left y₁≤y₄ (lexy y₃≤y₄) l₄⋘r₄ l₄⋘r₄ refl≈ refl≈ ;
                            dl₁⋘r₁' = lemma⋘≈ dl₁⋘r₁ r₁≈r₁' ;
                            r₁'≈r₁ = sym≈ r₁≈r₁' ;
                            r₁≃l₂ = lemma⋗⋗' l₁⋗r₁ l₁⋗l₂ ; 
                            r₁'≃l₂ = lemma≈≃ r₁'≈r₁ r₁≃l₂
                       in inj₂ (ll⋘ y₁≤y₃ y≤y₂ dl₁⋘r₁' l₂⋘r₂ l₂≃r₂ r₁'≃l₂)
  ... | inj₁ y₃≤y₄ | inj₂ l₁⋙dr₁ =
                       let l₁'≈l₁ = ≈left (lexy refl≤) y₁≤y₃ l₃⋘r₃ l₃⋘r₃ refl≈ refl≈ ;
                            pl₁'≈l₁' = lemma-push⋘ (lexy y₃≤y₄) (lexy refl≤) l₃⋘r₃ ;
                            pl₁'≈l₁ = trans≈ pl₁'≈l₁' l₁'≈l₁ ;
                            pl₁'⋙dr = lemma≈⋙ pl₁'≈l₁ l₁⋙dr₁ ; 
                            pl₁'⋙dr₁' = subtyping⋙r (lexy y₃≤y₄) pl₁'⋙dr ;
                            pl₁'⋗l₂ = lemma≈⋗ pl₁'≈l₁ l₁⋗l₂
                       in inj₂ (lr⋘ y₁≤y₃ y≤y₂ pl₁'⋙dr₁' l₂⋘r₂ l₂≃r₂ pl₁'⋗l₂)
  ... | inj₂ y₄≤y₃ | inj₁ (l₁⋗r₁ , dl₁⋘r₁) =
                       let r₁'≈r₁ = ≈left (lexy refl≤) y₁≤y₄ l₄⋘r₄ l₄⋘r₄ refl≈ refl≈ ;
                            pr₁'≈r₁' = lemma-push⋘ (lexy y₄≤y₃) (lexy refl≤) l₄⋘r₄ ;
                            r₁'≈pr₁' = sym≈ pr₁'≈r₁' ;
                            pr₁'≈r₁ = trans≈ pr₁'≈r₁' r₁'≈r₁ ;
                            r₁≈pr₁' = sym≈ pr₁'≈r₁ ; 
                            dl₁⋘pr₁' = lemma⋘≈ dl₁⋘r₁ r₁≈pr₁' ;
                            dl₁'⋘pr₁' = subtyping⋘l (lexy y₄≤y₃) dl₁⋘pr₁' ;
                            r₁≃l₂ = lemma⋗⋗' l₁⋗r₁ l₁⋗l₂ ; 
                            pr₁'≃l₂ = lemma≈≃ pr₁'≈r₁ r₁≃l₂ 
                       in inj₂ (ll⋘ y₁≤y₄ y≤y₂ dl₁'⋘pr₁' l₂⋘r₂ l₂≃r₂ pr₁'≃l₂)
  ... | inj₂ y₄≤y₃ | inj₂ l₁⋙dr₁ =
                       let l₁'≈l₁ = ≈left (lexy y₄≤y₃) y₁≤y₃ l₃⋘r₃ l₃⋘r₃ refl≈ refl≈ ;
                            l₁'⋙dr₁ = lemma≈⋙ l₁'≈l₁ l₁⋙dr₁ ;
                            l₁'⋗l₂ = lemma≈⋗ l₁'≈l₁ l₁⋗l₂
                       in inj₂ (lr⋘ y₁≤y₄ y≤y₂ l₁'⋙dr₁ l₂⋘r₂ l₂≃r₂ l₁'⋗l₂)
  lemma-drop⋘ (cr y≤y₁ (⋙rr {x = y₃} {x' = y₄} y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₃≃r₃ l₄⋙r₄ l₃≃l₄)) (cl y≤y₂ l₂⋘r₂) (lr⋘ .y≤y₁ .y≤y₂ .(⋙rr y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₃≃r₃ l₄⋙r₄ l₃≃l₄) .l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
      with tot≤ y₃ y₄ | lemma-drop⋙ (cl y₁≤y₃ l₃⋘r₃) (cr y₁≤y₄ l₄⋙r₄) (⋙rr y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₃≃r₃ l₄⋙r₄ l₃≃l₄)
  ... | _ | inj₁ (() , _) 
  ... | inj₁ y₃≤y₄ | inj₂ l₁⋙dr₁ =
                       let l₁'≈l₁ = ≈left (lexy refl≤) y₁≤y₃ l₃⋘r₃ l₃⋘r₃ refl≈ refl≈ ;
                            pl₁'≈l₁' = lemma-push⋘ (lexy y₃≤y₄) (lexy refl≤) l₃⋘r₃ ;
                            pl₁'≈l₁ = trans≈ pl₁'≈l₁' l₁'≈l₁ ;
                            pl₁'⋙dr = lemma≈⋙ pl₁'≈l₁ l₁⋙dr₁ ; 
                            pl₁'⋙dr₁' = subtyping⋙r (lexy y₃≤y₄) pl₁'⋙dr ;
                            pl₁'⋗l₂ = lemma≈⋗ pl₁'≈l₁ l₁⋗l₂
                       in inj₂ (lr⋘ y₁≤y₃ y≤y₂ pl₁'⋙dr₁' l₂⋘r₂ l₂≃r₂ pl₁'⋗l₂)
  ... | inj₂ y₄≤y₃ | inj₂ l₁⋙dr₁ =
                       let l₁'≈l₁ = ≈left (lexy y₄≤y₃) y₁≤y₃ l₃⋘r₃ l₃⋘r₃ refl≈ refl≈ ;
                            l₁'⋙dr₁ = lemma≈⋙ l₁'≈l₁ l₁⋙dr₁ ;
                            l₁'⋗l₂ = lemma≈⋗ l₁'≈l₁ l₁⋗l₂
                       in inj₂ (lr⋘ y₁≤y₄ y≤y₂ l₁'⋙dr₁ l₂⋘r₂ l₂≃r₂ l₁'⋗l₂)
  
  lemma-drop⋙ : {b : Bound}{l r : BBHeap b}(cₗ : Compound l)(cᵣ : Compound r) → l ⋙ r → l ⋗ r ∧ drop cₗ ⋘ r ∨ l ⋙ drop cᵣ
  lemma-drop⋙ (cl y≤y₁ lf⋘) (cl y≤y₂ l₂⋘r₂) (⋙rl .y≤y₁ .y≤y₂ .lf⋘ _ .l₂⋘r₂ ())
  lemma-drop⋙ (cl y≤y₁ (ll⋘ {x = y₃} {x' = y₄} y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄)) (cl y≤y₂ lf⋘) (⋙rl .y≤y₁ .y≤y₂ .(ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄) l₁≃r₁ .lf⋘ l₁⋗r₂)
      with tot≤ y₃ y₄ | lemma-drop⋘ (cl y₁≤y₃ l₃⋘r₃) (cl y₁≤y₄ l₄⋘r₄) (ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄)
  ... | inj₁ y₃≤y₄ | inj₁ (_ , l₁⋙dr₁) =
                       let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                            l₁⋗l₂ = lemma⋗≃ l₁⋗r₂ ≃lf ;
                            l₁'≈l₁ = ≈left (lexy refl≤) y₁≤y₃  l₃⋘r₃ l₃⋘r₃ refl≈ refl≈ ;
                            pl₁'≈l₁' = lemma-push⋘ (lexy y₃≤y₄) (lexy refl≤) l₃⋘r₃ ;
                            pl₁'≈l₁ = trans≈ pl₁'≈l₁' l₁'≈l₁ ;
                            pl₁'⋙dr₁ = lemma≈⋙ pl₁'≈l₁ l₁⋙dr₁ ;
                            pl₁'⋙dr₁' = subtyping⋙r (lexy y₃≤y₄) pl₁'⋙dr₁ ;
                            pl₁'⋗l₂ = lemma≈⋗ pl₁'≈l₁ l₁⋗l₂
                       in inj₁ (⋗nd y≤y₁ y≤y₂ l₁⋘r₁ lf⋘ l₁≃r₁ ≃lf l₁⋗l₂ , lr⋘ y₁≤y₃ y≤y₂ pl₁'⋙dr₁' lf⋘ ≃lf pl₁'⋗l₂)
  ... | inj₂ y₄≤y₃ | inj₁ (_ , l₁⋙dr₁) =
                       let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                            l₁⋗l₂ = lemma⋗≃ l₁⋗r₂ ≃lf ;
                            l₁'≈l₁ = ≈left (lexy y₄≤y₃) y₁≤y₃ l₃⋘r₃ l₃⋘r₃ refl≈ refl≈ ;
                            l₁'⋙dr₁ = lemma≈⋙ l₁'≈l₁ l₁⋙dr₁ ;
                            l₁'⋗l₂ = lemma≈⋗ l₁'≈l₁ l₁⋗l₂
                       in inj₁ (⋗nd y≤y₁ y≤y₂ l₁⋘r₁ lf⋘ l₁≃r₁ ≃lf l₁⋗l₂ , lr⋘ y₁≤y₄ y≤y₂ l₁'⋙dr₁ lf⋘ ≃lf l₁'⋗l₂)                  
  ... | _ | inj₂ dl₁⋘r₁
      with lemma-drop-⊥ y₁≤y₃ l₃⋘r₃ (lemma-⋘-≃ dl₁⋘r₁ (sym≃ l₁≃r₁))
  ... | ()
  lemma-drop⋙ (cl y≤y₁ (ll⋘ {x = y₃} {x' = y₄} y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄)) (cl y≤y₂ (ll⋘ {x = y₅} {x' = y₆} y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆)) (⋙rl .y≤y₁ .y≤y₂ .(ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄) l₁≃r₁ .(ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆) l₁⋗r₂)
      with tot≤ y₃ y₄ | tot≤ y₅ y₆ | lemma-drop⋘ (cl y₂≤y₅ l₅⋘r₅) (cl y₂≤y₆ l₆⋘r₆) (ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆) | lemma-drop⋘ (cl y₁≤y₃ l₃⋘r₃) (cl y₁≤y₄ l₄⋘r₄)  (ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄)
  ... | inj₁ y₃≤y₄ | _ | inj₁ (l₂≃r₂ , _) | inj₁ (_ , l₁⋙dr₁) =
                       let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                            l₂⋘r₂ = ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆ ;
                            r₂≃l₂ = sym≃ l₂≃r₂ ;
                            l₁⋗l₂ = lemma⋗≃ l₁⋗r₂ r₂≃l₂ ;
                            l₁'≈l₁ = ≈left (lexy refl≤) y₁≤y₃  l₃⋘r₃ l₃⋘r₃ refl≈ refl≈ ;
                            pl₁'≈l₁' = lemma-push⋘ (lexy y₃≤y₄) (lexy refl≤) l₃⋘r₃ ;
                            pl₁'≈l₁ = trans≈ pl₁'≈l₁' l₁'≈l₁ ;
                            pl₁'⋙dr₁ = lemma≈⋙ pl₁'≈l₁ l₁⋙dr₁ ;
                            pl₁'⋙dr₁' = subtyping⋙r (lexy y₃≤y₄) pl₁'⋙dr₁ ;
                            pl₁'⋗l₂ = lemma≈⋗ pl₁'≈l₁ l₁⋗l₂
                       in inj₁ (⋗nd y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁⋗l₂ , lr⋘ y₁≤y₃ y≤y₂ pl₁'⋙dr₁' l₂⋘r₂ l₂≃r₂ pl₁'⋗l₂)
  ... | inj₂ y₄≤y₃ | _ | inj₁ (l₂≃r₂ , _) | inj₁ (_ , l₁⋙dr₁) =
                       let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                            l₂⋘r₂ = ll⋘ y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₆⋘r₆ l₆≃r₆ r₅≃l₆ ;
                            r₂≃l₂ = sym≃ l₂≃r₂ ;
                            l₁⋗l₂ = lemma⋗≃ l₁⋗r₂ r₂≃l₂ ;
                            l₁'≈l₁ = ≈left (lexy y₄≤y₃) y₁≤y₃ l₃⋘r₃ l₃⋘r₃ refl≈ refl≈ ;
                            l₁'⋙dr₁ = lemma≈⋙ l₁'≈l₁ l₁⋙dr₁ ;
                            l₁'⋗l₂ = lemma≈⋗ l₁'≈l₁ l₁⋗l₂
                       in inj₁ (⋗nd y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₁≃r₁ l₂≃r₂ l₁⋗l₂ , lr⋘ y₁≤y₄ y≤y₂ l₁'⋙dr₁ l₂⋘r₂ l₂≃r₂ l₁'⋗l₂)   
  ... | _ | inj₁ y₅≤y₆ | inj₂ dl₂⋘r₂ | _ =
                         let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                              r₂≈r₂' = ≈left y₂≤y₆ (lexy y₅≤y₆) l₆⋘r₆ l₆⋘r₆ refl≈ refl≈ ;
                              dl₂⋘r₂' = lemma⋘≈ dl₂⋘r₂ r₂≈r₂' ;
                              l₁⋗r₂' = lemma⋗≈ l₁⋗r₂ r₂≈r₂'
                         in inj₂ (⋙rl y≤y₁ y₂≤y₅ l₁⋘r₁ l₁≃r₁ dl₂⋘r₂' l₁⋗r₂')
  ... | _ | inj₂ y₆≤y₅ | inj₂ dl₂⋘r₂ | _ =
                         let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                              r₂≈r₂' = ≈left y₂≤y₆ (lexy refl≤) l₆⋘r₆ l₆⋘r₆ refl≈ refl≈ ;
                              pr₂'≈r₂' = lemma-push⋘ (lexy y₆≤y₅) (lexy refl≤) l₆⋘r₆ ;
                              r₂'≈pr₂' = sym≈ pr₂'≈r₂' ;
                              r₂≈pr₂' = trans≈ r₂≈r₂' r₂'≈pr₂';
                              dl₂⋘pr₂' = lemma⋘≈ dl₂⋘r₂ r₂≈pr₂' ;
                              dl₂'⋘pr₂' = subtyping⋘l (lexy y₆≤y₅) dl₂⋘pr₂' ;
                              l₁⋗pr₂' = lemma⋗≈ l₁⋗r₂ r₂≈pr₂'
                         in inj₂ (⋙rl y≤y₁ y₂≤y₆ l₁⋘r₁ l₁≃r₁ dl₂'⋘pr₂' l₁⋗pr₂')
  ... | _ | _ | _ | inj₂ dl₁⋘r₁
      with lemma-drop-⊥ y₁≤y₃ l₃⋘r₃ (lemma-⋘-≃ dl₁⋘r₁ (sym≃ l₁≃r₁))
  ... | ()
  lemma-drop⋙ (cl y≤y₁ (ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄)) (cl y≤y₂ (lr⋘ {x = y₅} {x' = y₆} y₂≤y₅ y₂≤y₆ l₅⋙r₅ l₆⋘r₆ l₆≃r₆ l₅⋗l₆)) (⋙rl .y≤y₁ .y≤y₂ .(ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄) l₁≃r₁ .(lr⋘ y₂≤y₅ y₂≤y₆ l₅⋙r₅ l₆⋘r₆ l₆≃r₆ l₅⋗l₆) l₁⋗r₂)
      with tot≤ y₅ y₆ | lemma-drop⋘ (cr y₂≤y₅ l₅⋙r₅) (cl y₂≤y₆ l₆⋘r₆) (lr⋘ y₂≤y₅ y₂≤y₆ l₅⋙r₅ l₆⋘r₆ l₆≃r₆ l₅⋗l₆)
  ... | _ | inj₁ (() , _)
  ... | inj₁ y₅≤y₆ | inj₂ dl₂⋘r₂ =
                         let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                              r₂≈r₂' = ≈left y₂≤y₆ (lexy y₅≤y₆) l₆⋘r₆ l₆⋘r₆ refl≈ refl≈ ;
                              dl₂⋘r₂' = lemma⋘≈ dl₂⋘r₂ r₂≈r₂' ;
                              l₁⋗r₂' = lemma⋗≈ l₁⋗r₂ r₂≈r₂'
                         in inj₂ (⋙rl y≤y₁ y₂≤y₅ l₁⋘r₁ l₁≃r₁ dl₂⋘r₂' l₁⋗r₂')
  ... | inj₂ y₆≤y₅ | inj₂ dl₂⋘r₂ =
                         let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                              r₂≈r₂' = ≈left y₂≤y₆ (lexy refl≤) l₆⋘r₆ l₆⋘r₆ refl≈ refl≈ ;
                              pr₂'≈r₂' = lemma-push⋘ (lexy y₆≤y₅) (lexy refl≤) l₆⋘r₆ ;
                              r₂'≈pr₂' = sym≈ pr₂'≈r₂' ;
                              r₂≈pr₂' = trans≈ r₂≈r₂' r₂'≈pr₂';
                              dl₂⋘pr₂' = lemma⋘≈ dl₂⋘r₂ r₂≈pr₂' ;
                              dl₂'⋘pr₂' = subtyping⋘l (lexy y₆≤y₅) dl₂⋘pr₂' ;
                              l₁⋗pr₂' = lemma⋗≈ l₁⋗r₂ r₂≈pr₂'
                         in inj₂ (⋙rl y≤y₁ y₂≤y₆ l₁⋘r₁ l₁≃r₁ dl₂'⋘pr₂' l₁⋗pr₂')
  lemma-drop⋙ (cl y≤y₁ (lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄)) (cl y≤y₂ l₂⋘r₂) (⋙rl .y≤y₁ .y≤y₂ .(lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄) () .l₂⋘r₂ _)
  lemma-drop⋙ _ _ (⋙rr _ _ lf⋘ _ (⋙lf _) ())
  lemma-drop⋙ _ _ (⋙rr _ _ lf⋘ _ (⋙rl _ _ _ _ _ _) ()) 
  lemma-drop⋙ _ _ (⋙rr _ _ lf⋘ _ (⋙rr _ _ _ _ _ _) ()) 
  lemma-drop⋙ (cl y≤y₁ (ll⋘ y₁≤y₃ y₁≤y₄ lf⋘ l₄⋘r₄ l₄≃r₄ r₃≃l₄)) (cr y≤y₂ (⋙lf y₂≤y₅)) (⋙rr .y≤y₁ .y≤y₂ .(ll⋘ y₁≤y₃ y₁≤y₄ lf⋘ l₄⋘r₄ l₄≃r₄ r₃≃l₄) l₁≃r₁ .(⋙lf y₂≤y₅) (≃nd .y₁≤y₃ .y₂≤y₅ .lf⋘ .lf⋘ ≃lf ≃lf ≃lf)) = 
                         let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ lf⋘ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                              l₁⋗r₂ = ⋗lf y₁≤y₃
                         in inj₂ (⋙rl y≤y₁ y₂≤y₅ l₁⋘r₁ l₁≃r₁ lf⋘ l₁⋗r₂)
  lemma-drop⋙ _ _ (⋙rr _ _ (ll⋘ y₁≤y₃ _ (ll⋘ _ _ _ _ _ _) _ _ _) _ (⋙lf y₂≤y₅) (≃nd .y₁≤y₃ .y₂≤y₅ .(ll⋘ _ _ _ _ _ _) .lf⋘ _ ≃lf ()))
  lemma-drop⋙ _ _ (⋙rr _ _ (ll⋘ y₁≤y₃ _ (lr⋘ _ _ _ _ _ _) _ _ _) _ (⋙lf y₂≤y₅) (≃nd .y₁≤y₃ .y₂≤y₅ .(lr⋘ _ _ _ _ _ _) .lf⋘ _ ≃lf ()))
  lemma-drop⋙ (cl y≤y₁ (ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄)) (cr y≤y₂ (⋙rl {x = y₅} {x' = y₆} y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₅≃r₅ l₆⋘r₆ l₅⋗r₆)) (⋙rr .y≤y₁ .y≤y₂ .(ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄) l₁≃r₁ .(⋙rl y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₅≃r₅ l₆⋘r₆ l₅⋗r₆) l₁≃l₂) 
      with tot≤ y₅ y₆ | lemma-drop⋙ (cl y₂≤y₅ l₅⋘r₅) (cl y₂≤y₆ l₆⋘r₆) (⋙rl y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₅≃r₅ l₆⋘r₆ l₅⋗r₆)
  ... | inj₁ y₅≤y₆ | inj₁ (l₂⋗r₂ , dl₂⋘r₂) =
                         let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                              r₂≈r₂' = ≈left y₂≤y₆ (lexy y₅≤y₆) l₆⋘r₆ l₆⋘r₆ refl≈ refl≈ ;
                              dl₂⋘r₂' = lemma⋘≈ dl₂⋘r₂ r₂≈r₂' ;
                              l₁⋗r₂ = lemma≃⋗ l₁≃l₂ l₂⋗r₂ ;
                              l₁⋗r₂' = lemma⋗≈ l₁⋗r₂ r₂≈r₂'
                         in inj₂ (⋙rl y≤y₁ y₂≤y₅ l₁⋘r₁ l₁≃r₁ dl₂⋘r₂' l₁⋗r₂')
  ... | inj₁ y₅≤y₆ | inj₂ l₂⋙dr₂ =
                        let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                             l₂'≈l₂ = ≈left (lexy refl≤) y₂≤y₅ l₅⋘r₅ l₅⋘r₅ refl≈ refl≈ ;
                             pl₂'≈l₂' = lemma-push⋘ (lexy y₅≤y₆) (lexy refl≤) l₅⋘r₅ ;
                             pl₂'≈l₂ = trans≈ pl₂'≈l₂' l₂'≈l₂ ;
                             pl₂'⋙dr₂ = lemma≈⋙ pl₂'≈l₂ l₂⋙dr₂ ;
                             l₂≈pl₂' = sym≈ pl₂'≈l₂ ;
                             pl₂'⋙dr₂' = subtyping⋙r (lexy y₅≤y₆) pl₂'⋙dr₂ ;
                             l₁≃pl₂' = lemma≃≈ l₁≃l₂ l₂≈pl₂'
                        in inj₂ (⋙rr y≤y₁ y₂≤y₅ l₁⋘r₁ l₁≃r₁ pl₂'⋙dr₂' l₁≃pl₂')
  ... | inj₂ y₆≤y₅ | inj₁ (l₂⋗r₂ , dl₂⋘r₂) =
                         let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                              r₂'≈r₂ = ≈left (lexy refl≤) y₂≤y₆ l₆⋘r₆ l₆⋘r₆ refl≈ refl≈ ;
                              pr₂'≈r₂' = lemma-push⋘ (lexy y₆≤y₅) (lexy refl≤) l₆⋘r₆ ;
                              pr₂'≈r₂ = trans≈ pr₂'≈r₂' r₂'≈r₂ ;
                              r₂≈pr₂' = sym≈ pr₂'≈r₂ ;
                              dl₂⋘pr₂' = lemma⋘≈ dl₂⋘r₂ r₂≈pr₂' ;
                              dl₂'⋘pr₂' = subtyping⋘l (lexy y₆≤y₅) dl₂⋘pr₂' ;
                              l₁⋗r₂ = lemma≃⋗ l₁≃l₂ l₂⋗r₂ ;
                              l₁⋗pr₂' = lemma⋗≈ l₁⋗r₂ r₂≈pr₂'
                         in inj₂ (⋙rl y≤y₁ y₂≤y₆ l₁⋘r₁ l₁≃r₁ dl₂'⋘pr₂' l₁⋗pr₂')
  ... | inj₂ y₆≤y₅ | inj₂ l₂⋙dr₂ =
                         let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                              l₂'≈l₂ = ≈left (lexy y₆≤y₅) y₂≤y₅ l₅⋘r₅ l₅⋘r₅ refl≈ refl≈ ;
                              l₂'⋙dr₂ = lemma≈⋙ l₂'≈l₂ l₂⋙dr₂ ;
                              l₂≈l₂' = sym≈ l₂'≈l₂ ;
                              l₁≃l₂' = lemma≃≈ l₁≃l₂ l₂≈l₂'
                         in inj₂ (⋙rr y≤y₁ y₂≤y₆ l₁⋘r₁ l₁≃r₁ l₂'⋙dr₂ l₁≃l₂')
  lemma-drop⋙ (cl y≤y₁ (ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄)) (cr y≤y₂ (⋙rr {x = y₅} {x' = y₆} y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₅≃r₅ l₆⋙r₆ l₅≃l₆)) (⋙rr .y≤y₁ .y≤y₂ .(ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄) l₁≃r₁ .(⋙rr y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₅≃r₅ l₆⋙r₆ l₅≃l₆) l₁≃l₂)
      with tot≤ y₅ y₆ | lemma-drop⋙ (cl y₂≤y₅ l₅⋘r₅) (cr y₂≤y₆ l₆⋙r₆) (⋙rr y₂≤y₅ y₂≤y₆ l₅⋘r₅ l₅≃r₅ l₆⋙r₆ l₅≃l₆)
  ... | _ | inj₁ (() , _)
  ... | inj₁ y₅≤y₆ | inj₂ l₂⋙dr₂ =
                        let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                             l₂'≈l₂ = ≈left (lexy refl≤) y₂≤y₅ l₅⋘r₅ l₅⋘r₅ refl≈ refl≈ ;
                             pl₂'≈l₂' = lemma-push⋘ (lexy y₅≤y₆) (lexy refl≤) l₅⋘r₅ ;
                             pl₂'≈l₂ = trans≈ pl₂'≈l₂' l₂'≈l₂ ;
                             pl₂'⋙dr₂ = lemma≈⋙ pl₂'≈l₂ l₂⋙dr₂ ;
                             l₂≈pl₂' = sym≈ pl₂'≈l₂ ;
                             pl₂'⋙dr₂' = subtyping⋙r (lexy y₅≤y₆) pl₂'⋙dr₂ ;
                             l₁≃pl₂' = lemma≃≈ l₁≃l₂ l₂≈pl₂'
                        in inj₂ (⋙rr y≤y₁ y₂≤y₅ l₁⋘r₁ l₁≃r₁ pl₂'⋙dr₂' l₁≃pl₂')
  ... | inj₂ y₆≤y₅ | inj₂ l₂⋙dr₂ =
                         let l₁⋘r₁ = ll⋘ y₁≤y₃ y₁≤y₄ l₃⋘r₃ l₄⋘r₄ l₄≃r₄ r₃≃l₄ ;
                              l₂'≈l₂ = ≈left (lexy y₆≤y₅) y₂≤y₅ l₅⋘r₅ l₅⋘r₅ refl≈ refl≈ ;
                              l₂'⋙dr₂ = lemma≈⋙ l₂'≈l₂ l₂⋙dr₂ ;
                              l₂≈l₂' = sym≈ l₂'≈l₂ ;
                              l₁≃l₂' = lemma≃≈ l₁≃l₂ l₂≈l₂'
                         in inj₂ (⋙rr y≤y₁ y₂≤y₆ l₁⋘r₁ l₁≃r₁ l₂'⋙dr₂ l₁≃l₂')
  lemma-drop⋙ (cl y≤y₁ (lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄)) (cr y≤y₂ l₂⋙r₂) (⋙rr .y≤y₁ .y≤y₂ .(lr⋘ y₁≤y₃ y₁≤y₄ l₃⋙r₃ l₄⋘r₄ l₄≃r₄ l₃⋗l₄) () .l₂⋙r₂ _)

  lemma-drop-⊥ : {b : Bound}{x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x))(l⋘r : l ⋘ r) → drop (cl b≤x l⋘r) ⋘ (left b≤x l⋘r) → ⊥
  lemma-drop-⊥ _ lf⋘ ()
  lemma-drop-⊥ b≤x (ll⋘ {x = y₁} {x' = y₂} x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂) dxlr⋘xlr
      with tot≤ y₁ y₂ | lemma-drop⋘ (cl x≤y₁ l₁⋘r₁) (cl x≤y₂ l₂⋘r₂) (ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂) | dxlr⋘xlr | lemma-perfect dxlr⋘xlr
  ... | inj₁ y₁≤y₂ | inj₁ (l≃r , l⋙dr) | _dxlr⋘xlr | _ =
                         let l⋘r = ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                              pl'≈l' = lemma-push⋘ (lexy y₁≤y₂) (lexy refl≤) l₁⋘r₁ ;
                              l'≈l = ≈left (lexy refl≤) x≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                              pl'≈l = trans≈ pl'≈l' l'≈l ;
                              pl'⋙dr = lemma≈⋙ pl'≈l l⋙dr ;
                              pl'⋙dr' = subtyping⋙r (lexy y₁≤y₂) pl'⋙dr ;
                              r≃l = sym≃ l≃r ;
                              l≃l = trans≃ l≃r r≃l ;
                              pl'≃l = lemma≈≃ pl'≈l l≃l 
                         in lemma-⋘-⊥ x≤y₁ b≤x pl'⋙dr' l⋘r pl'≃l _dxlr⋘xlr
  ... | inj₂ y₂≤y₁ | inj₁ (l≃r , l⋙dr) | _dxlr⋘xlr | _ =
                         let l⋘r = ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                              l'≈l = ≈left (lexy y₂≤y₁) x≤y₁ l₁⋘r₁  l₁⋘r₁ refl≈ refl≈ ;
                              l'⋙dr = lemma≈⋙ l'≈l l⋙dr ;
                              r≃l = sym≃ l≃r ;
                              l≃l = trans≃ l≃r r≃l ;
                              l'≃l = lemma≈≃ l'≈l l≃l 
                         in lemma-⋘-⊥ x≤y₂ b≤x l'⋙dr l⋘r l'≃l _dxlr⋘xlr
  ... | _ | inj₂ dl⋘r | _ | pnd .b≤x .(ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂) l≃r =
                         let r≃l = sym≃ l≃r ;
                              dl⋘l = lemma-⋘-≃ dl⋘r r≃l
                         in lemma-drop-⊥ x≤y₁ l₁⋘r₁ dl⋘l
  lemma-drop-⊥ b≤x (lr⋘ x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗r₂) dxlr⋘xlr
      with lemma-perfect dxlr⋘xlr
  ... | pnd .b≤x .(lr⋘ x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗r₂) () 
