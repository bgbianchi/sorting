open import Relation.Binary.Core

module BBHeap.Drop.Properties {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_
open import BBHeap.Compound _≤_
open import BBHeap.Drop _≤_ tot≤ trans≤
open import BBHeap.Equality _≤_
open import BBHeap.Equality.Properties _≤_ 
open import BBHeap.Push _≤_ tot≤ trans≤
open import BBHeap.Push.Properties _≤_ tot≤ trans≤
open import BBHeap.Subtyping _≤_ trans≤
open import BBHeap.Subtyping.Properties _≤_ trans≤
open import Bound.Lower A
open import Bound.Lower.Order _≤_ 
open import Data.Nat
open import Data.List hiding (drop)
open import Data.Sum 
open import Data.Product
open import Nat.Sum
open import List.Permutation.Base A
open import List.Permutation.Base.Concatenation A
open import List.Permutation.Base.Equivalence A
open import Order.Total _≤_ tot≤ 

mutual
  lemma-drop⋘# : {b : Bound}{x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x))(l⋘r : l ⋘ r) → # (drop⋘ b≤x l⋘r) ≡ # l + # r
  lemma-drop⋘# b≤x lf⋘ = refl
  lemma-drop⋘# b≤x (ll⋘ {x = y₁} {x' = y₂} {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
      with tot≤ y₁ y₂ | lemma-drop⋘ (cl x≤y₁ l₁⋘r₁) (cl x≤y₂ l₂⋘r₂) (ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
  ... | inj₁ y₁≤y₂ | inj₁ (_ , l⋙dr)
      with # (drop⋘ x≤y₂ l₂⋘r₂) | lemma-drop⋘# x≤y₂ l₂⋘r₂ | # (push⋘ (lexy y₁≤y₂) (lexy refl≤) l₁⋘r₁) | lemma-push# (lexy y₁≤y₂) (left (lexy refl≤) l₁⋘r₁) | # (subtyping (lexy y₁≤y₂) (drop⋘ x≤y₂ l₂⋘r₂)) | lemma-subtyping# (lexy y₁≤y₂) (drop⋘ x≤y₂ l₂⋘r₂) | # l₁ + # r₁ + suc (# l₂ + # r₂) | +assoc (# l₁ + # r₁) (# l₂ + # r₂) 
  ... | ._ | refl | ._ | refl | ._ | refl | ._ | refl = refl 
  lemma-drop⋘# b≤x (ll⋘ {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂) | inj₁ y₁≤y₂ | inj₂ dl⋘r
      with # (drop⋘ x≤y₁ l₁⋘r₁) | lemma-drop⋘# x≤y₁ l₁⋘r₁
  ... | ._ | refl = refl 
  lemma-drop⋘# b≤x (ll⋘ {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂) | inj₂ y₂≤y₁ | inj₁ (_ , l⋙dr)
      with # (drop⋘ x≤y₂ l₂⋘r₂) | lemma-drop⋘# x≤y₂ l₂⋘r₂ | (# l₁ + # r₁) + suc (# l₂ + # r₂) | +assoc (# l₁ + # r₁) (# l₂ + # r₂)
  ... | ._ | refl | ._ | refl = refl 
  lemma-drop⋘# b≤x (ll⋘ {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂) | inj₂ y₂≤y₁ | inj₂ dl⋘r
      with # (drop⋘ x≤y₁ l₁⋘r₁) | lemma-drop⋘# x≤y₁ l₁⋘r₁ | # (push⋘ (lexy y₂≤y₁) (lexy refl≤) l₂⋘r₂) | lemma-push# (lexy y₂≤y₁) (left (lexy refl≤) l₂⋘r₂) | # (subtyping (lexy y₂≤y₁) (drop⋘ x≤y₁ l₁⋘r₁)) | lemma-subtyping# (lexy y₂≤y₁) (drop⋘ x≤y₁ l₁⋘r₁) 
  ... | ._ | refl | ._ | refl | ._ | refl = refl
  lemma-drop⋘# b≤x (lr⋘ {x = y₁} {x' = y₂} {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
      with tot≤ y₁ y₂ | lemma-drop⋘ (cr x≤y₁ l₁⋙r₁) (cl x≤y₂ l₂⋘r₂) (lr⋘ x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
  ... | _ | inj₁ (() , _)
  ... | inj₁ y₁≤y₂ | inj₂ dl⋘r 
      with # (drop⋙ x≤y₁ l₁⋙r₁) | lemma-drop⋙# x≤y₁ l₁⋙r₁
  ... | ._ | refl = refl 
  lemma-drop⋘# b≤x (lr⋘ {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂) | inj₂ y₂≤y₁ | inj₂ dl⋘r 
      with # (drop⋙ x≤y₁ l₁⋙r₁) | lemma-drop⋙# x≤y₁ l₁⋙r₁ | # (push⋘ (lexy y₂≤y₁) (lexy refl≤) l₂⋘r₂) | lemma-push# (lexy y₂≤y₁) (left (lexy refl≤) l₂⋘r₂) | # (subtyping (lexy y₂≤y₁) (drop⋙ x≤y₁ l₁⋙r₁)) | lemma-subtyping# (lexy y₂≤y₁) (drop⋙ x≤y₁ l₁⋙r₁) 
  ... | ._ | refl | ._ | refl | ._ | refl = refl

  lemma-drop⋙# : {b : Bound}{x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x))(l⋙r : l ⋙ r) → # (drop⋙ b≤x l⋙r) ≡ # l + # r
  lemma-drop⋙# b≤x (⋙lf x≤y) = refl 
  lemma-drop⋙# b≤x (⋙rl {x = y₁} {x' = y₂} {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
      with tot≤ y₁ y₂ | lemma-drop⋙ (cl x≤y₁ l₁⋘r₁) (cl x≤y₂ l₂⋘r₂) (⋙rl x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
  ... | inj₁ y₁≤y₂ | inj₁ (_ , dl⋘r)
      with # (drop⋘ x≤y₁ l₁⋘r₁) | lemma-drop⋘# x≤y₁ l₁⋘r₁
  ... | ._ | refl = refl 
  lemma-drop⋙# b≤x (⋙rl {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂) | inj₁ y₁≤y₂ | inj₂ l⋙dr
      with # (drop⋘ x≤y₂ l₂⋘r₂) | lemma-drop⋘# x≤y₂ l₂⋘r₂ | # (push⋘ (lexy y₁≤y₂) (lexy refl≤) l₁⋘r₁) | lemma-push# (lexy y₁≤y₂) (left (lexy refl≤) l₁⋘r₁) | # (subtyping (lexy y₁≤y₂) (drop⋘ x≤y₂ l₂⋘r₂)) | lemma-subtyping# (lexy y₁≤y₂) (drop⋘ x≤y₂ l₂⋘r₂) | # l₁ + # r₁ + suc (# l₂ + # r₂) | +assoc (# l₁ + # r₁) (# l₂ + # r₂)
  ... | ._ | refl | ._ | refl | ._ | refl | ._ | refl = refl 
  lemma-drop⋙# b≤x (⋙rl x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂) | inj₂ y₂≤y₁ | inj₁ (_ , dl⋘r)
        with # (drop⋘ x≤y₁ l₁⋘r₁) | lemma-drop⋘# x≤y₁ l₁⋘r₁ | # (push⋘ (lexy y₂≤y₁) (lexy refl≤) l₂⋘r₂) | lemma-push# (lexy y₂≤y₁) (left (lexy refl≤) l₂⋘r₂) | # (subtyping (lexy y₂≤y₁) (drop⋘ x≤y₁ l₁⋘r₁)) | lemma-subtyping# (lexy y₂≤y₁) (drop⋘ x≤y₁ l₁⋘r₁) 
  ... | ._ | refl | ._ | refl | ._ | refl = refl
  lemma-drop⋙# b≤x (⋙rl {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂) | inj₂ y₂≤y₁ | inj₂ l⋙dr
      with # (drop⋘ x≤y₂ l₂⋘r₂) | lemma-drop⋘# x≤y₂ l₂⋘r₂ | (# l₁ + # r₁) + suc (# l₂ + # r₂) | +assoc (# l₁ + # r₁) (# l₂ + # r₂)
  ... | ._ | refl | ._ | refl = refl
  lemma-drop⋙# b≤x (⋙rr {x = y₁} {x' = y₂} {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
      with tot≤ y₁ y₂ | lemma-drop⋙ (cl x≤y₁ l₁⋘r₁) (cr x≤y₂ l₂⋙r₂) (⋙rr x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
  ... | _ | inj₁ (() , _)
  ... | inj₁ y₁≤y₂ | inj₂ l⋙dr
      with # (drop⋙ x≤y₂ l₂⋙r₂) | lemma-drop⋙# x≤y₂ l₂⋙r₂ | # (push⋘ (lexy y₁≤y₂) (lexy refl≤) l₁⋘r₁) | lemma-push# (lexy y₁≤y₂) (left (lexy refl≤) l₁⋘r₁) | # (subtyping (lexy y₁≤y₂) (drop⋙ x≤y₂ l₂⋙r₂)) | lemma-subtyping# (lexy y₁≤y₂) (drop⋙ x≤y₂ l₂⋙r₂) | # l₁ + # r₁ + suc (# l₂ + # r₂) | +assoc (# l₁ + # r₁) (# l₂ + # r₂)
  ... | ._ | refl | ._ | refl | ._ | refl | ._ | refl = refl 
  lemma-drop⋙# b≤x (⋙rr {l = l₁} {r = r₁} {l' = l₂} {r' = r₂} x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂) | inj₂ y₂≤y₁ | inj₂ l⋙dr 
      with # (drop⋙ x≤y₂ l₂⋙r₂) | lemma-drop⋙# x≤y₂ l₂⋙r₂ | (# l₁ + # r₁) + suc (# l₂ + # r₂) | +assoc (# l₁ + # r₁) (# l₂ + # r₂)
  ... | ._ | refl | ._ | refl = refl

lemma-drop# : {b : Bound}{h : BBHeap b}(cₕ : Compound h)  → suc (# (drop cₕ)) ≡ # h
lemma-drop# (cl b≤x l⋘r)
    with # (drop (cl b≤x l⋘r)) | lemma-drop⋘# b≤x l⋘r
... | ._ | refl = refl
lemma-drop# (cr b≤x l⋙r)
    with # (drop (cr b≤x l⋙r)) | lemma-drop⋙# b≤x l⋙r
... | ._ | refl = refl

lemma-drop≤′ : {b : Bound}{h : BBHeap b}(cₕ : Compound h) → suc (# (drop cₕ)) ≤′ # h
lemma-drop≤′ cₕ
    with suc (# (drop cₕ)) | lemma-drop# cₕ
... | ._ | refl = ≤′-refl

mutual
  lemma-drop⋘∼ : {b : Bound}{x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x))(l⋘r : l ⋘ r) → flatten (drop⋘ b≤x l⋘r) ∼ (flatten l ++ flatten r)
  lemma-drop⋘∼ b≤x lf⋘ = ∼[] 
  lemma-drop⋘∼ b≤x (ll⋘ {x = y₁} {x' = y₂} {l = l₁} {r = r₁} x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
      with tot≤ y₁ y₂ | lemma-drop⋘ (cl x≤y₁ l₁⋘r₁) (cl x≤y₂ l₂⋘r₂) (ll⋘ x≤y₁ x≤y₂ l₁⋘r₁ l₂⋘r₂ l₂≃r₂ r₁≃l₂)
  ... | inj₁ y₁≤y₂ | inj₁ (_ , l⋙dr) = 
                     let fdr∼fl₂fr₂ = lemma-drop⋘∼ x≤y₂ l₂⋘r₂ ;
                          fdr'∼fdr = lemma-subtyping∼ (lexy y₁≤y₂) (drop⋘ x≤y₂ l₂⋘r₂) ;
                          fdr'∼fl₂fr₂ = trans∼ fdr'∼fdr fdr∼fl₂fr₂ ;
                          fpl'∼y₂fl₁fr₁ = lemma-push⋘∼ (lexy y₁≤y₂) (lexy refl≤) l₁⋘r₁ ;
                          fpl'fdr'∼y₂fl₁fr₁fl₂fr₂ = lemma++∼ fpl'∼y₂fl₁fr₁ fdr'∼fl₂fr₂ ;
                          fl₁fr₁fr/y₂⟶fl₁fr₁fl₂fr₂ = lemma++/ {xs = flatten l₁ ++ flatten r₁} ;
                          y₂fl₁fr₁fl₂fr₂∼fl₁fr₁fr = ∼x /head fl₁fr₁fr/y₂⟶fl₁fr₁fl₂fr₂ refl∼ ;
                          fpl'fdr'∼fl₁fr₁fr = trans∼ fpl'fdr'∼y₂fl₁fr₁fl₂fr₂ y₂fl₁fr₁fl₂fr₂∼fl₁fr₁fr 
                     in ∼x /head /head fpl'fdr'∼fl₁fr₁fr 
  ... | inj₁ y₁≤y₂ | inj₂ dl⋘r =
                     let fdl∼fl₁fr₁ = lemma-drop⋘∼ x≤y₁ l₁⋘r₁ ;
                          fdlfr∼fl₁fr₁fr = lemma++∼r fdl∼fl₁fr₁
                     in ∼x /head /head fdlfr∼fl₁fr₁fr 
  ... | inj₂ y₂≤y₁ | inj₁ (_ , l⋙dr) =
                     let fdr∼fl₂fr₂ = lemma-drop⋘∼ x≤y₂ l₂⋘r₂ ;
                          fl = y₁ ∷ (flatten l₁ ++ flatten r₁) ;
                          flfdr∼flfl₂fr₂ = lemma++∼l {xs = fl} fdr∼fl₂fr₂ ;
                          flfr/y₂⟶flfl₂fr₂ =  lemma++/ {xs = fl} 
                     in ∼x {x = y₂} /head flfr/y₂⟶flfl₂fr₂ flfdr∼flfl₂fr₂ 
  ... | inj₂ y₂≤y₁ | inj₂ dl⋘r =
                     let fdl∼fl₁fr₁ = lemma-drop⋘∼ x≤y₁ l₁⋘r₁ ;
                          fdl'∼fdl = lemma-subtyping∼ (lexy y₂≤y₁) (drop⋘ x≤y₁ l₁⋘r₁) ;
                          fdl'∼fl₁fr₁ = trans∼ fdl'∼fdl fdl∼fl₁fr₁ ;
                          fpr'∼y₁fl₂fr₂ = lemma-push⋘∼ (lexy y₂≤y₁) (lexy refl≤) l₂⋘r₂ ;
                          fdl'fpr'∼fl₁fr₁y₁fl₂fr₂ = lemma++∼ fdl'∼fl₁fr₁ fpr'∼y₁fl₂fr₂ ;
                          flfr/y₂⟶flfl₂fr₂ = lemma++/ {xs = y₁ ∷ (flatten l₁ ++ flatten r₁)} ;
                          fl₁fr₁y₁fl₂fr₂/y₁⟶fl₁fr₁fl₂fr₂ =  lemma++/ {xs = flatten l₁ ++ flatten r₁} ;
                          fl₁fr₁y₁fl₂fr₂∼flfl₂fr₂ = ∼x fl₁fr₁y₁fl₂fr₂/y₁⟶fl₁fr₁fl₂fr₂ /head refl∼ ;
                          fdl'fpr'∼flfl₂fr₂ = trans∼ fdl'fpr'∼fl₁fr₁y₁fl₂fr₂ fl₁fr₁y₁fl₂fr₂∼flfl₂fr₂
                     in ∼x /head flfr/y₂⟶flfl₂fr₂ fdl'fpr'∼flfl₂fr₂ 
  lemma-drop⋘∼ b≤x (lr⋘ {x = y₁} {x' = y₂} {l = l₁} {r = r₁} x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
      with tot≤ y₁ y₂ | lemma-drop⋘ (cr x≤y₁ l₁⋙r₁) (cl x≤y₂ l₂⋘r₂) (lr⋘ x≤y₁ x≤y₂ l₁⋙r₁ l₂⋘r₂ l₂≃r₂ l₁⋗l₂)
  ... | _ | inj₁ (() , _)
  ... | inj₁ y₁≤y₂ | inj₂ dl⋘r =
                     let fdl∼fl₁fr₁ = lemma-drop⋙∼ x≤y₁ l₁⋙r₁ ;
                          fdlfr∼fl₁fr₁fr = lemma++∼r fdl∼fl₁fr₁
                     in ∼x /head /head fdlfr∼fl₁fr₁fr 
  ... | inj₂ y₂≤y₁ | inj₂ dl⋘r =
                     let fdl∼fl₁fr₁ = lemma-drop⋙∼ x≤y₁ l₁⋙r₁ ;
                          fdl'∼fdl = lemma-subtyping∼ (lexy y₂≤y₁) (drop⋙ x≤y₁ l₁⋙r₁) ;
                          fdl'∼fl₁fr₁ = trans∼ fdl'∼fdl fdl∼fl₁fr₁ ;
                          fpr'∼y₁fl₂fr₂ = lemma-push⋘∼ (lexy y₂≤y₁) (lexy refl≤) l₂⋘r₂ ;
                          fdl'fpr'∼fl₁fr₁y₁fl₂fr₂ = lemma++∼ fdl'∼fl₁fr₁ fpr'∼y₁fl₂fr₂ ;
                          flfr/y₂⟶flfl₂fr₂ = lemma++/ {xs = y₁ ∷ (flatten l₁ ++ flatten r₁)} ;
                          fl₁fr₁y₁fl₂fr₂/y₁⟶fl₁fr₁fl₂fr₂ =  lemma++/ {xs = flatten l₁ ++ flatten r₁} ;
                          fl₁fr₁y₁fl₂fr₂∼flfl₂fr₂ = ∼x fl₁fr₁y₁fl₂fr₂/y₁⟶fl₁fr₁fl₂fr₂ /head refl∼ ;
                          fdl'fpr'∼flfl₂fr₂ = trans∼ fdl'fpr'∼fl₁fr₁y₁fl₂fr₂ fl₁fr₁y₁fl₂fr₂∼flfl₂fr₂
                     in ∼x /head flfr/y₂⟶flfl₂fr₂ fdl'fpr'∼flfl₂fr₂ 

  lemma-drop⋙∼ : {b : Bound}{x : A}{l r : BBHeap (val x)}(b≤x : LeB b (val x))(l⋙r : l ⋙ r) → flatten (drop⋙ b≤x l⋙r) ∼ (flatten l ++ flatten r)
  lemma-drop⋙∼ b≤x (⋙lf x≤y) = ∼x /head /head ∼[]
  lemma-drop⋙∼ b≤x (⋙rl {x = y₁} {x' = y₂} {l = l₁} {r = r₁} x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
      with tot≤ y₁ y₂ | lemma-drop⋙ (cl x≤y₁ l₁⋘r₁) (cl x≤y₂ l₂⋘r₂) (⋙rl x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋘r₂ l₁⋗r₂)
  ... | inj₁ y₁≤y₂ | inj₁ (_ , dl⋘r) =
                       let fdl∼fl₁fr₁ = lemma-drop⋘∼ x≤y₁ l₁⋘r₁ ;
                            fdlfr∼fl₁fr₁fr = lemma++∼r fdl∼fl₁fr₁
                       in ∼x /head /head fdlfr∼fl₁fr₁fr 
  ... | inj₁ y₁≤y₂ | inj₂ l⋙dr =
                       let fdr∼fl₂fr₂ = lemma-drop⋘∼ (lexy refl≤) l₂⋘r₂ ;
                            fdr'∼fdr = lemma-subtyping∼ (lexy y₁≤y₂) (drop⋘ x≤y₂ l₂⋘r₂) ;
                            fdr'∼fl₂fr₂ = trans∼ fdr'∼fdr fdr∼fl₂fr₂ ;
                            fpl'∼y₂fl₁fr₁ = lemma-push⋘∼ (lexy y₁≤y₂) (lexy refl≤) l₁⋘r₁ ;
                            fpl'fdr'∼y₂fl₁fr₁fl₂fr₂ = lemma++∼ fpl'∼y₂fl₁fr₁ fdr'∼fl₂fr₂ ;
                            fl₁fr₁fr/y₂⟶fl₁fr₁fl₂fr₂ = lemma++/ {xs = flatten l₁ ++ flatten r₁} ;
                            y₂fl₁fr₁fl₂fr₂∼fl₁fr₁fr = ∼x /head fl₁fr₁fr/y₂⟶fl₁fr₁fl₂fr₂ refl∼ ;
                            fpl'fdr'∼fl₁fr₁fr = trans∼ fpl'fdr'∼y₂fl₁fr₁fl₂fr₂ y₂fl₁fr₁fl₂fr₂∼fl₁fr₁fr 
                       in ∼x /head /head fpl'fdr'∼fl₁fr₁fr 
  ... | inj₂ y₂≤y₁ | inj₁ (_ , dl⋘r) =
                       let fdl∼fl₁fr₁ = lemma-drop⋘∼ x≤y₁ l₁⋘r₁ ;
                            fdl'∼fdl = lemma-subtyping∼ (lexy y₂≤y₁) (drop⋘ x≤y₁ l₁⋘r₁) ;
                            fdl'∼fl₁fr₁ = trans∼ fdl'∼fdl fdl∼fl₁fr₁ ;
                            fpr'∼y₁fl₂fr₂ = lemma-push⋘∼ (lexy y₂≤y₁) (lexy refl≤) l₂⋘r₂ ;
                            fdl'fpr'∼fl₁fr₁y₁fl₂fr₂ = lemma++∼ fdl'∼fl₁fr₁ fpr'∼y₁fl₂fr₂ ;
                            flfr/y₂⟶flfl₂fr₂ = lemma++/ {xs = y₁ ∷ (flatten l₁ ++ flatten r₁)} ;
                            fl₁fr₁y₁fl₂fr₂/y₁⟶fl₁fr₁fl₂fr₂ =  lemma++/ {xs = flatten l₁ ++ flatten r₁} ;
                            fl₁fr₁y₁fl₂fr₂∼flfl₂fr₂ = ∼x fl₁fr₁y₁fl₂fr₂/y₁⟶fl₁fr₁fl₂fr₂ /head refl∼ ;
                            fdl'fpr'∼flfl₂fr₂ = trans∼ fdl'fpr'∼fl₁fr₁y₁fl₂fr₂ fl₁fr₁y₁fl₂fr₂∼flfl₂fr₂
                       in ∼x /head flfr/y₂⟶flfl₂fr₂ fdl'fpr'∼flfl₂fr₂ 
  ... | inj₂ y₂≤y₁ | inj₂ l⋙dr =
                       let fdr∼fl₂fr₂ = lemma-drop⋘∼ x≤y₂ l₂⋘r₂ ;
                            fl = y₁ ∷ (flatten l₁ ++ flatten r₁) ;
                            flfdr∼flfl₂fr₂ = lemma++∼l {xs = fl} fdr∼fl₂fr₂ ;
                            flfr/y₂⟶flfl₂fr₂ =  lemma++/ {xs = fl} 
                       in ∼x {x = y₂} /head flfr/y₂⟶flfl₂fr₂ flfdr∼flfl₂fr₂
  lemma-drop⋙∼ b≤x (⋙rr {x = y₁} {x' = y₂} {l = l₁} {r = r₁} x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
      with tot≤ y₁ y₂ | lemma-drop⋙ (cl x≤y₁ l₁⋘r₁) (cr x≤y₂ l₂⋙r₂) (⋙rr x≤y₁ x≤y₂ l₁⋘r₁ l₁≃r₁ l₂⋙r₂ l₁≃l₂)
  ... | _ | inj₁ (() , _)
  ... | inj₁ y₁≤y₂ | inj₂ l⋙dr =
                       let fdr∼fl₂fr₂ = lemma-drop⋙∼ (lexy refl≤) l₂⋙r₂ ;
                            fdr'∼fdr = lemma-subtyping∼ (lexy y₁≤y₂) (drop⋙ x≤y₂ l₂⋙r₂) ;
                            fdr'∼fl₂fr₂ = trans∼ fdr'∼fdr fdr∼fl₂fr₂ ;
                            fpl'∼y₂fl₁fr₁ = lemma-push⋘∼ (lexy y₁≤y₂) (lexy refl≤) l₁⋘r₁ ;
                            fpl'fdr'∼y₂fl₁fr₁fl₂fr₂ = lemma++∼ fpl'∼y₂fl₁fr₁ fdr'∼fl₂fr₂ ;
                            fl₁fr₁fr/y₂⟶fl₁fr₁fl₂fr₂ = lemma++/ {xs = flatten l₁ ++ flatten r₁} ;
                            y₂fl₁fr₁fl₂fr₂∼fl₁fr₁fr = ∼x /head fl₁fr₁fr/y₂⟶fl₁fr₁fl₂fr₂ refl∼ ;
                            fpl'fdr'∼fl₁fr₁fr = trans∼ fpl'fdr'∼y₂fl₁fr₁fl₂fr₂ y₂fl₁fr₁fl₂fr₂∼fl₁fr₁fr 
                       in ∼x /head /head fpl'fdr'∼fl₁fr₁fr 
  ... | inj₂ y₂≤y₁ | inj₂ l⋙dr =
                       let fdr∼fl₂fr₂ = lemma-drop⋙∼ x≤y₂ l₂⋙r₂ ;
                            fl = y₁ ∷ (flatten l₁ ++ flatten r₁) ;
                            flfdr∼flfl₂fr₂ = lemma++∼l {xs = fl} fdr∼fl₂fr₂ ;
                            flfr/y₂⟶flfl₂fr₂ =  lemma++/ {xs = fl} 
                       in ∼x {x = y₂} /head flfr/y₂⟶flfl₂fr₂ flfdr∼flfl₂fr₂
