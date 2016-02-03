open import Relation.Binary.Core

module BBHeap.Push.Properties {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_
open import BBHeap.Equality.Properties _≤_
open import BBHeap.Push _≤_ tot≤ trans≤
open import Bound.Lower A
open import Bound.Lower.Order _≤_
open import Data.Nat
open import Data.List
open import Data.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Concatenation A
open import List.Permutation.Base.Equivalence A
open import Order.Total _≤_ tot≤

mutual
  lemma-push⋘# : {b : Bound}{x y : A}{l r : BBHeap (val y)}(b≤x : LeB b (val x))(b≤y : LeB b (val y))(l⋘r : l ⋘ r) → # (push⋘ b≤x b≤y l⋘r) ≡ suc (# l + # r) 
  lemma-push⋘# b≤x _ lf⋘ = refl
  lemma-push⋘# {x = x} b≤x b≤y (ll⋘ {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ =  refl
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = refl
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _
      with # (push⋘ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁) | lemma-push⋘# (lexy y₁≤x) (lexy refl≤) l₁⋘r₁
  ... | ._ | refl = refl
  lemma-push⋘# b≤x b≤y (ll⋘ y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂) | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x 
      with # (push⋘ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂) | lemma-push⋘# (lexy y₂≤x) (lexy refl≤) l₂⋘r₂
  ... | ._ | refl = refl
  lemma-push⋘# {x = x} b≤x b≤y (lr⋘ {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ = refl
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = refl
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ 
      with # (push⋙ (lexy y₁≤x) (lexy refl≤) l₁⋙r₁) | lemma-push⋙# (lexy y₁≤x) (lexy refl≤) l₁⋙r₁
  ... | ._ | refl = refl
  lemma-push⋘# b≤x b≤y (lr⋘ y≤y₁ y≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂) | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x 
      with # (push⋘ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂) | lemma-push⋘# (lexy y₂≤x) (lexy refl≤) l₂⋘r₂
  ... | ._ | refl = refl

  lemma-push⋙# : {b : Bound}{x y : A}{l r : BBHeap (val y)}(b≤x : LeB b (val x))(b≤y : LeB b (val y))(l⋙r : l ⋙ r) → # (push⋙ b≤x b≤y l⋙r) ≡ suc (# l + # r)
  lemma-push⋙# {x = x} b≤x b≤y (⋙lf {x = z} y≤z)
      with tot≤ x z
  ... | inj₁ x≤z = refl 
  ... | inj₂ z≤x = refl
  lemma-push⋙# {x = x} b≤x b≤y (⋙rl {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ = refl
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = refl
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ 
      with # (push⋘ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁) | lemma-push⋘# (lexy y₁≤x) (lexy refl≤) l₁⋘r₁
  ... | ._ | refl = refl
  lemma-push⋙# b≤x b≤y (⋙rl y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂) | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x
      with # (push⋘ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂) | lemma-push⋘# (lexy y₂≤x) (lexy refl≤) l₂⋘r₂
  ... | ._ | refl = refl
  lemma-push⋙# {x = x} b≤x b≤y (⋙rr {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ = refl
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = refl 
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _
      with # (push⋘ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁) | lemma-push⋘# (lexy y₁≤x) (lexy refl≤) l₁⋘r₁
  ... | ._ | refl = refl
  lemma-push⋙# b≤x b≤y (⋙rr y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂) | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x
      with # (push⋙ (lexy y₂≤x) (lexy refl≤) l₂⋙r₂) | lemma-push⋙# (lexy y₂≤x) (lexy refl≤) l₂⋙r₂
  ... | ._ | refl = refl

lemma-push# : {b : Bound}{x : A}(b≤x : LeB b (val x))(h : BBHeap b) → # (push b≤x h) ≡ # h
lemma-push# b≤x leaf = refl
lemma-push# b≤x (left b≤y l⋘r) = lemma-push⋘# b≤x b≤y l⋘r
lemma-push# b≤x (right b≤y l⋙r) = lemma-push⋙# b≤x b≤y l⋙r

mutual 
  lemma-push⋘∼ : {b : Bound}{x y : A}{l r : BBHeap (val y)}(b≤x : LeB b (val x))(b≤y : LeB b (val y))(l⋘r : l ⋘ r) → flatten (push⋘ b≤x b≤y l⋘r) ∼ (x ∷ (flatten l ++ flatten r))
  lemma-push⋘∼ b≤x _ lf⋘ = ∼x /head /head ∼[] 
  lemma-push⋘∼ {x = x} b≤x b≤y (ll⋘ {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ =  refl∼ 
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let pl'∼xfl₁fr₁ = lemma-push⋘∼ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁ ; 
                        fpl'fr'∼xfl₁fr₁fr' = lemma++∼r pl'∼xfl₁fr₁
                   in ∼x /head (/tail /head) fpl'fr'∼xfl₁fr₁fr'
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = refl∼
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let pr'∼xfl₂fr₂ = lemma-push⋘∼ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂ ;
                        fl' = flatten (left (lexy y₂≤y₁) l₁⋘r₁) ;
                        fl'fpr'∼fl'xfl₂fr₂ = lemma++∼l {xs = fl'} pr'∼xfl₂fr₂ ;
                        xfl'fr'/y₂⟶xfl'fl₂fr₂ = lemma++/l {xs = x ∷ fl'} /head ;
                        fl'xfl₂fr₂/x⟶fl'fl₂fr₂ = lemma++/ {xs = fl'};
                        fl'xfl₂fr₂∼xfl'fl₂fr₂ = ∼x fl'xfl₂fr₂/x⟶fl'fl₂fr₂ /head refl∼ ;
                        fl'fpr'∼xfl'fl₂fr₂ = trans∼ fl'fpr'∼fl'xfl₂fr₂  fl'xfl₂fr₂∼xfl'fl₂fr₂
                   in ∼x /head xfl'fr'/y₂⟶xfl'fl₂fr₂ fl'fpr'∼xfl'fl₂fr₂ 
  lemma-push⋘∼ {x = x} b≤x b≤y (lr⋘ {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ = refl∼
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let pl'∼xfl₁fr₁ = lemma-push⋙∼ (lexy y₁≤x) (lexy refl≤) l₁⋙r₁ ; 
                        fpl'fr'∼xfl₁fr₁fr' = lemma++∼r pl'∼xfl₁fr₁
                   in ∼x /head (/tail /head) fpl'fr'∼xfl₁fr₁fr' 
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = refl∼
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let pr'∼xfl₂fr₂ = lemma-push⋘∼ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂ ;
                        fl' = flatten (right (lexy y₂≤y₁) l₁⋙r₁) ;
                        fl'fpr'∼fl'xfl₂fr₂ = lemma++∼l {xs = fl'} pr'∼xfl₂fr₂ ;
                        xfl'fr'/y₂⟶xfl'fl₂fr₂ = lemma++/l {xs = x ∷ fl'} /head ;
                        fl'xfl₂fr₂/x⟶fl'fl₂fr₂ = lemma++/ {xs = fl'};
                        fl'xfl₂fr₂∼xfl'fl₂fr₂ = ∼x fl'xfl₂fr₂/x⟶fl'fl₂fr₂ /head refl∼ ;
                        fl'fpr'∼xfl'fl₂fr₂ = trans∼ fl'fpr'∼fl'xfl₂fr₂  fl'xfl₂fr₂∼xfl'fl₂fr₂
                   in ∼x /head xfl'fr'/y₂⟶xfl'fl₂fr₂ fl'fpr'∼xfl'fl₂fr₂ 

  lemma-push⋙∼ : {b : Bound}{x y : A}{l r : BBHeap (val y)}(b≤x : LeB b (val x))(b≤y : LeB b (val y))(l⋙r : l ⋙ r) → flatten (push⋙ b≤x b≤y l⋙r) ∼ (x ∷ (flatten l ++ flatten r))
  lemma-push⋙∼ {x = x} b≤x b≤y (⋙lf {x = z} y≤z)
      with tot≤ x z
  ... | inj₁ x≤z = ∼x /head /head (∼x /head /head ∼[]) 
  ... | inj₂ z≤x = ∼x (/tail /head) /head (∼x /head /head ∼[])
  lemma-push⋙∼ {x = x} b≤x b≤y (⋙rl {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ = refl∼
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let pl'∼xfl₁fr₁ = lemma-push⋘∼ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁ ; 
                        fpl'fr'∼xfl₁fr₁fr' = lemma++∼r pl'∼xfl₁fr₁
                   in ∼x /head (/tail /head) fpl'fr'∼xfl₁fr₁fr' 
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = refl∼
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let pr'∼xfl₂fr₂ = lemma-push⋘∼ (lexy y₂≤x) (lexy refl≤) l₂⋘r₂ ;
                        fl' = flatten (left (lexy y₂≤y₁) l₁⋘r₁) ;
                        fl'fpr'∼fl'xfl₂fr₂ = lemma++∼l {xs = fl'} pr'∼xfl₂fr₂ ;
                        xfl'fr'/y₂⟶xfl'fl₂fr₂ = lemma++/l {xs = x ∷ fl'} /head ;
                        fl'xfl₂fr₂/x⟶fl'fl₂fr₂ = lemma++/ {xs = fl'};
                        fl'xfl₂fr₂∼xfl'fl₂fr₂ = ∼x fl'xfl₂fr₂/x⟶fl'fl₂fr₂ /head refl∼ ;
                        fl'fpr'∼xfl'fl₂fr₂ = trans∼ fl'fpr'∼fl'xfl₂fr₂  fl'xfl₂fr₂∼xfl'fl₂fr₂
                   in ∼x /head xfl'fr'/y₂⟶xfl'fl₂fr₂ fl'fpr'∼xfl'fl₂fr₂ 
  lemma-push⋙∼ {x = x} b≤x b≤y (⋙rr {x = y₁} {x' = y₂} y≤y₁ y≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
      with tot≤ y₁ y₂ | tot≤ x y₁ | tot≤ x y₂
  ... | inj₁ y₁≤y₂ | inj₁ x≤y₁ | _ = refl∼
  ... | inj₁ y₁≤y₂ | inj₂ y₁≤x | _ =
                   let pl'∼xfl₁fr₁ = lemma-push⋘∼ (lexy y₁≤x) (lexy refl≤) l₁⋘r₁ ; 
                        fpl'fr'∼xfl₁fr₁fr' = lemma++∼r pl'∼xfl₁fr₁
                   in ∼x /head (/tail /head) fpl'fr'∼xfl₁fr₁fr' 
  ... | inj₂ y₂≤y₁ | _ | inj₁ x≤y₂ = refl∼
  ... | inj₂ y₂≤y₁ | _ | inj₂ y₂≤x =
                   let pr'∼xfl₂fr₂ = lemma-push⋙∼ (lexy y₂≤x) (lexy refl≤) l₂⋙r₂ ;
                        fl' = flatten (left (lexy y₂≤y₁) l₁⋘r₁) ;
                        fl'fpr'∼fl'xfl₂fr₂ = lemma++∼l {xs = fl'} pr'∼xfl₂fr₂ ;
                        xfl'fr'/y₂⟶xfl'fl₂fr₂ = lemma++/l {xs = x ∷ fl'} /head ;
                        fl'xfl₂fr₂/x⟶fl'fl₂fr₂ = lemma++/ {xs = fl'};
                        fl'xfl₂fr₂∼xfl'fl₂fr₂ = ∼x fl'xfl₂fr₂/x⟶fl'fl₂fr₂ /head refl∼ ;
                        fl'fpr'∼xfl'fl₂fr₂ = trans∼ fl'fpr'∼fl'xfl₂fr₂  fl'xfl₂fr₂∼xfl'fl₂fr₂
                   in ∼x /head xfl'fr'/y₂⟶xfl'fl₂fr₂ fl'fpr'∼xfl'fl₂fr₂ 
