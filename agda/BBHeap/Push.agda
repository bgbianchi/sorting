open import Relation.Binary.Core

module BBHeap.Push {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_
open import BBHeap.Equality _≤_
open import BBHeap.Equality.Properties _≤_
open import Bound.Lower A 
open import Bound.Lower.Order _≤_
open import Bound.Lower.Order.Properties _≤_ trans≤
open import Data.Sum renaming (_⊎_ to _∨_)
open import Order.Total _≤_ tot≤ 

mutual
  push⋘ : {b : Bound}{x y : A}{l r : BBHeap (val y)} → LeB b (val x) → LeB b (val y) → l ⋘ r → BBHeap b  
  push⋘ b≤x _ lf⋘ = left b≤x lf⋘
  push⋘ {x = x} b≤x b≤y (ll⋘ {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ =  left b≤x (ll⋘ (lexy x≤y₁) (lexy (trans≤ x≤y₁ y₁≤y₂)) l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let pl'≈l' = lemma-push⋘ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁ ;
                        l'⋘r' = ll⋘ (lexy refl≤) (lexy y₁≤y₂) l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                        pl'⋘r' = lemma≈⋘ pl'≈l' l'⋘r'
                   in left (transLeB b≤y y≤y₁) pl'⋘r'
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = left b≤x (ll⋘ (lexy (trans≤ x≤y₂ y₂≤y₁)) (lexy x≤y₂) l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let pr'≈r' = lemma-push⋘ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂ ;
                        r'≈pr' = sym≈ pr'≈r' ;
                        l'⋘r' = ll⋘ (lexy y₂≤y₁) (lexy refl≤) l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                        l'⋘pr' = lemma⋘≈ l'⋘r' r'≈pr'
                   in left (transLeB b≤y y≤y₂) l'⋘pr'
  push⋘ {x = x} b≤x b≤y (lr⋘ {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ =  left b≤x (lr⋘ (lexy x≤y₁) (lexy (trans≤ x≤y₁ y₁≤y₂)) l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let pl'≈l' = lemma-push⋙ (lexy y₁≤x) (lexy refl≤) l₁⋙r₁ ;
                        l'⋘r' = lr⋘ (lexy refl≤) (lexy y₁≤y₂) l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ ;
                        pl'⋘r' = lemma≈⋘ pl'≈l' l'⋘r'
                   in left (transLeB b≤y y≤y₁) pl'⋘r'
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = left b≤x (lr⋘ (lexy (trans≤ x≤y₂ y₂≤y₁)) (lexy x≤y₂) l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let pr'≈r' = lemma-push⋘ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂ ;
                        r'≈pr' = sym≈ pr'≈r' ;
                        l'⋘r' = lr⋘ (lexy y₂≤y₁) (lexy refl≤) l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ ;
                        l'⋘pr'  = lemma⋘≈ l'⋘r' r'≈pr'
                   in left (transLeB b≤y y≤y₂) l'⋘pr'

  push⋙ : {b : Bound}{x y : A}{l r : BBHeap (val y)} → LeB b (val x) → LeB b (val y) → l ⋙ r → BBHeap b 
  push⋙ {x = x} b≤x b≤y (⋙lf {x = z} y≤z)
      with tot≤ x z
  ... | inj₁ x≤z = right b≤x (⋙lf (lexy x≤z))
  ... | inj₂ z≤x = right (transLeB b≤y y≤z) (⋙lf (lexy z≤x))
  push⋙ {x = x} b≤x b≤y (⋙rl {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ = right b≤x (⋙rl (lexy x≤y₁) (lexy (trans≤ x≤y₁ y₁≤y₂)) l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let pl'≈l' = lemma-push⋘ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁ ;
                        l'⋙r' = ⋙rl (lexy refl≤) (lexy y₁≤y₂) l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂ ;
                        pl'⋙r' = lemma≈⋙ pl'≈l' l'⋙r'
                   in right (transLeB b≤y y≤y₁) pl'⋙r'
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = right b≤x (⋙rl (lexy (trans≤ x≤y₂ y₂≤y₁)) (lexy x≤y₂) l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let pr'≈r' = lemma-push⋘ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂ ;
                        r'≈pr' = sym≈ pr'≈r' ;
                        l'⋙r' = ⋙rl (lexy y₂≤y₁) (lexy refl≤) l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂ ;
                        l'⋙pr' = lemma⋙≈ l'⋙r' r'≈pr'
                   in right (transLeB b≤y y≤y₂) l'⋙pr'
  push⋙ {x = x} b≤x b≤y (⋙rr {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ = right b≤x (⋙rr (lexy x≤y₁) (lexy (trans≤ x≤y₁ y₁≤y₂)) l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let pl'≈l' = lemma-push⋘ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁ ;
                        l'⋙r' = ⋙rr (lexy refl≤) (lexy y₁≤y₂) l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂ ;
                        pl'⋙r' = lemma≈⋙ pl'≈l' l'⋙r'
                   in right (transLeB b≤y y≤y₁) pl'⋙r'
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = right b≤x (⋙rr (lexy (trans≤ x≤y₂ y₂≤y₁)) (lexy x≤y₂) l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let pr'≈r' = lemma-push⋙ (lexy y₂≤x) (lexy refl≤) l₂⋙r₂ ;
                        r'≈pr' = sym≈ pr'≈r' ;
                        l'⋙r' = ⋙rr (lexy y₂≤y₁) (lexy refl≤) l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂ ;
                        l'⋙pr' = lemma⋙≈ l'⋙r' r'≈pr'
                   in right (transLeB b≤y y≤y₂) l'⋙pr'

  lemma-push⋘ : {b : Bound}{x y : A}{l r : BBHeap (val y)}(b≤x : LeB b (val x))(b≤y : LeB b (val y))(l⋘r : l ⋘ r) → push⋘ b≤x b≤y l⋘r ≈ left b≤y l⋘r
  lemma-push⋘ b≤x b≤y lf⋘ = ≈left b≤x b≤y lf⋘ lf⋘ ≈leaf ≈leaf
  lemma-push⋘ {x = x} b≤x b≤y (ll⋘ {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ =
                   let l⋘r = ll⋘ y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                        x≤y₂ = lexy (trans≤ x≤y₁ y₁≤y₂) ;
                        l'⋘r' = ll⋘ (lexy x≤y₁) x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                        l'≈l = ≈left (lexy x≤y₁) y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                        r'≈r = ≈left x≤y₂ y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈
                   in ≈left b≤x b≤y l'⋘r' l⋘r l'≈l r'≈r  
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let l⋘r = ll⋘ y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                        pl'≈l' = lemma-push⋘ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁ ;
                        l'⋘r' = ll⋘ (lexy refl≤) (lexy y₁≤y₂) l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                        pl'⋘r' = lemma≈⋘ pl'≈l' l'⋘r' ;
                        l'≈l = ≈left (lexy refl≤) y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                        pl'≈l = trans≈ pl'≈l' l'≈l ;
                        r'≈r = ≈left (lexy y₁≤y₂) y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈
                   in ≈left (transLeB b≤y y≤y₁) b≤y pl'⋘r' l⋘r pl'≈l r'≈r 
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = 
                   let l⋘r = ll⋘ y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                        x≤y₁ = lexy (trans≤ x≤y₂ y₂≤y₁) ;
                        l'⋘r' = ll⋘ x≤y₁ (lexy x≤y₂) l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                        r'≈r = ≈left (lexy x≤y₂) y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈ ;
                        l'≈l = ≈left x≤y₁ y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈
                   in ≈left b≤x b≤y l'⋘r' l⋘r l'≈l r'≈r  
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x = 
                   let l⋘r = ll⋘ y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                        pr'≈r' = lemma-push⋘ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂ ;
                        r'≈pr' = sym≈ pr'≈r' ;
                        l'⋘r' = ll⋘ (lexy y₂≤y₁) (lexy refl≤) l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂ ;
                        l'⋘pr' = lemma⋘≈ l'⋘r' r'≈pr' ;
                        r'≈r = ≈left (lexy refl≤) y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈ ;
                        pr'≈r = trans≈ pr'≈r' r'≈r ;
                        l'≈l = ≈left (lexy y₂≤y₁) y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈
                   in ≈left (transLeB b≤y y≤y₂) b≤y l'⋘pr' l⋘r l'≈l pr'≈r
  lemma-push⋘ {x = x} b≤x b≤y (lr⋘ {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ =
                   let l⋘r = lr⋘ y≤y₁ y≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ ;
                        x≤y₂ = lexy (trans≤ x≤y₁ y₁≤y₂) ;
                        l'⋘r' = lr⋘ (lexy x≤y₁) x≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ ;
                        l'≈l = ≈right (lexy x≤y₁) y≤y₁ l₁⋙r₁ l₁⋙r₁ refl≈ refl≈ ;
                        r'≈r = ≈left x≤y₂ y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈
                   in ≈left b≤x b≤y l'⋘r' l⋘r l'≈l r'≈r
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let l⋘r = lr⋘ y≤y₁ y≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ ;
                        pl'≈l' = lemma-push⋙ (lexy y₁≤x) (lexy refl≤) l₁⋙r₁ ;
                        l'⋘r' = lr⋘ (lexy refl≤) (lexy y₁≤y₂) l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ ;
                        pl'⋘r' = lemma≈⋘ pl'≈l' l'⋘r' ;
                        l'≈l = ≈right (lexy refl≤) y≤y₁ l₁⋙r₁ l₁⋙r₁ refl≈ refl≈ ;
                        pl'≈l = trans≈ pl'≈l' l'≈l ;
                        r'≈r = ≈left (lexy y₁≤y₂) y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈
                   in ≈left (transLeB b≤y y≤y₁) b≤y pl'⋘r' l⋘r pl'≈l r'≈r
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ =
                   let l⋘r = lr⋘ y≤y₁ y≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ ;
                        x≤y₁ = lexy (trans≤ x≤y₂ y₂≤y₁) ;
                        l'⋘r' = lr⋘ x≤y₁ (lexy x≤y₂) l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ ;
                        l'≈l = ≈right x≤y₁ y≤y₁ l₁⋙r₁ l₁⋙r₁ refl≈ refl≈ ;
                        r'≈r = ≈left (lexy x≤y₂) y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈
                   in ≈left b≤x b≤y l'⋘r' l⋘r l'≈l r'≈r
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let l⋘r = lr⋘ y≤y₁ y≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ ;
                        pr'≈r' = lemma-push⋘ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂ ;
                        r'≈pr' = sym≈ pr'≈r' ;
                        l'⋘r' = lr⋘ (lexy y₂≤y₁) (lexy refl≤) l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂ ;
                        l'⋘pr'  = lemma⋘≈ l'⋘r' r'≈pr' ;
                        l'≈l = ≈right (lexy y₂≤y₁) y≤y₁ l₁⋙r₁ l₁⋙r₁ refl≈ refl≈ ;
                        r'≈r = ≈left (lexy refl≤) y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈ ;
                        pr'≈r = trans≈ pr'≈r' r'≈r
                   in ≈left (transLeB b≤y y≤y₂) b≤y l'⋘pr' l⋘r l'≈l pr'≈r

  lemma-push⋙ : {b : Bound}{x y : A}{l r : BBHeap (val y)}(b≤x : LeB b (val x))(b≤y : LeB b (val y))(l⋙r : l ⋙ r) → push⋙ b≤x b≤y l⋙r ≈ right b≤y l⋙r
  lemma-push⋙ {x = x} b≤x b≤y (⋙lf {x = z} y≤z)
      with tot≤ x z
  ... | inj₁ x≤z = ≈right b≤x b≤y (⋙lf (lexy x≤z)) (⋙lf y≤z) (≈left (lexy x≤z) y≤z lf⋘ lf⋘ ≈leaf ≈leaf) ≈leaf
  ... | inj₂ z≤x = ≈right (transLeB b≤y y≤z) b≤y (⋙lf (lexy z≤x)) (⋙lf y≤z) (≈left (lexy z≤x) y≤z lf⋘ lf⋘ ≈leaf ≈leaf) ≈leaf
  lemma-push⋙ {x = x} b≤x b≤y (⋙rl {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ =
                   let l⋙r = ⋙rl y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂ ;
                        x≤y₂ = lexy (trans≤ x≤y₁ y₁≤y₂) ;
                        l'⋙r' = ⋙rl (lexy x≤y₁) x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂ ;
                        l'≈l = ≈left (lexy x≤y₁) y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                        r'≈r = ≈left x≤y₂ y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈
                   in ≈right b≤x b≤y l'⋙r' l⋙r l'≈l r'≈r
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let l⋙r = ⋙rl y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂ ;
                        pl'≈l' = lemma-push⋘ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁ ;
                        l'⋙r' = ⋙rl (lexy refl≤) (lexy y₁≤y₂) l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂ ;
                        pl'⋙r' = lemma≈⋙ pl'≈l' l'⋙r' ;
                        l'≈l = ≈left (lexy refl≤) y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                        pl'≈l = trans≈ pl'≈l' l'≈l ;
                        r'≈r = ≈left (lexy y₁≤y₂) y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈
                   in ≈right (transLeB b≤y y≤y₁) b≤y pl'⋙r' l⋙r pl'≈l r'≈r
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ =
                   let l⋙r = ⋙rl y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂ ;
                        x≤y₁ = lexy (trans≤ x≤y₂ y₂≤y₁) ;
                        l'⋙r' = ⋙rl x≤y₁ (lexy x≤y₂) l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂ ;
                        l'≈l = ≈left x≤y₁ y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                        r'≈r = ≈left (lexy x≤y₂) y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈
                   in ≈right b≤x b≤y l'⋙r' l⋙r l'≈l r'≈r
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let l⋙r = ⋙rl y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂ ;
                        pr'≈r' = lemma-push⋘ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂ ;
                        r'≈pr' = sym≈ pr'≈r' ;
                        l'⋙r' = ⋙rl (lexy y₂≤y₁) (lexy refl≤) l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂ ;
                        l'⋙pr' = lemma⋙≈ l'⋙r' r'≈pr' ;
                        l'≈l = ≈left (lexy y₂≤y₁) y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                        r'≈r = ≈left (lexy refl≤) y≤y₂ l₂⋘r₂ l₂⋘r₂ refl≈ refl≈ ;
                        pr'≈r = trans≈ pr'≈r' r'≈r
                   in ≈right (transLeB b≤y y≤y₂) b≤y l'⋙pr' l⋙r l'≈l pr'≈r
  lemma-push⋙ {x = x} b≤x b≤y (⋙rr {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ =
                   let l⋙r = ⋙rr y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂ ;
                        x≤y₂ = lexy (trans≤ x≤y₁ y₁≤y₂) ;
                        l'⋙r' = ⋙rr (lexy x≤y₁) x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂ ;
                        l'≈l = ≈left (lexy x≤y₁) y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                        r'≈r = ≈right x≤y₂ y≤y₂ l₂⋙r₂ l₂⋙r₂ refl≈ refl≈ 
                   in ≈right b≤x b≤y l'⋙r' l⋙r l'≈l r'≈r
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let l⋙r = ⋙rr y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂ ;
                        pl'≈l' = lemma-push⋘ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁ ;
                        l'⋙r' = ⋙rr (lexy refl≤) (lexy y₁≤y₂) l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂ ;
                        pl'⋙r' = lemma≈⋙ pl'≈l' l'⋙r' ;
                        l'≈l = ≈left (lexy refl≤) y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                        pl'≈l = trans≈ pl'≈l' l'≈l ;
                        r'≈r = ≈right (lexy y₁≤y₂) y≤y₂ l₂⋙r₂ l₂⋙r₂ refl≈ refl≈
                   in ≈right (transLeB b≤y y≤y₁) b≤y pl'⋙r' l⋙r pl'≈l r'≈r
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ =
                   let l⋙r = ⋙rr y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂ ;
                        x≤y₁ = lexy (trans≤ x≤y₂ y₂≤y₁) ;
                        l'⋙r' = ⋙rr x≤y₁ (lexy x≤y₂) l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂ ;
                        l'≈l = ≈left x≤y₁ y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                        r'≈r = ≈right (lexy x≤y₂) y≤y₂ l₂⋙r₂ l₂⋙r₂ refl≈ refl≈
                   in ≈right b≤x b≤y l'⋙r' l⋙r l'≈l r'≈r
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let l⋙r = ⋙rr y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂ ;
                        pr'≈r' = lemma-push⋙ (lexy y₂≤x) (lexy refl≤) l₂⋙r₂ ;
                        r'≈pr' = sym≈ pr'≈r' ;
                        l'⋙r' = ⋙rr (lexy y₂≤y₁) (lexy refl≤) l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂ ;
                        l'⋙pr' = lemma⋙≈ l'⋙r' r'≈pr' ;
                        l'≈l = ≈left (lexy y₂≤y₁) y≤y₁ l₁⋘r₁ l₁⋘r₁ refl≈ refl≈ ;
                        r'≈r = ≈right (lexy refl≤) y≤y₂ l₂⋙r₂ l₂⋙r₂ refl≈ refl≈ ;
                        pr'≈r = trans≈ pr'≈r' r'≈r 
                   in ≈right (transLeB b≤y y≤y₂) b≤y l'⋙pr' l⋙r l'≈l pr'≈r

push : {b : Bound}{x : A} → LeB b (val x) → BBHeap b → BBHeap b
push _ leaf = leaf
push b≤x (left b≤y l⋘r) = push⋘ b≤x b≤y l⋘r
push b≤x (right b≤y l⋙r) = push⋙ b≤x b≤y l⋙r
