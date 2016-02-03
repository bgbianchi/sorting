open import Relation.Binary.Core

module BBHeap.Insert.Properties {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_
open import BBHeap.Insert _≤_ tot≤ trans≤
open import BBHeap.Subtyping.Properties _≤_ trans≤
open import Bound.Lower A
open import Bound.Lower.Order _≤_ 
open import Data.List
open import Data.Sum 
open import List.Permutation.Base A
open import List.Permutation.Base.Concatenation A
open import List.Permutation.Base.Equivalence A
open import Order.Total _≤_ tot≤ 

lemma-insert∼ : {b : Bound}{x : A}(b≤x : LeB b (val x))(h : BBHeap b) → (x ∷ flatten h) ∼ (flatten (insert b≤x h))
lemma-insert∼ b≤x leaf = refl∼
lemma-insert∼ {x = x} b≤x (left {x = y} {l = l} {r = r} b≤y l⋘r) 
    with tot≤ x y
... | inj₁ x≤y 
    with lemma-insert⋘ (lexy refl≤) l⋘r
... | inj₁ lᵢ⋘r 
           rewrite lemma-subtyping≡ {val y} {val x} (lexy x≤y) (insert {val y} {y} (lexy refl≤) l) 
                     | lemma-subtyping≡ {val y} {val x} (lexy x≤y) r 
                     = ∼x /head /head (lemma++∼r (lemma-insert∼ (lexy refl≤) l)) 
... | inj₂ lᵢ⋗r 
           rewrite  lemma-subtyping≡ {val y} {val x} (lexy x≤y) (insert {val y} {y} (lexy refl≤) l) 
                      | lemma-subtyping≡ {val y} {val x} (lexy x≤y) r 
                      = ∼x /head /head (lemma++∼r (lemma-insert∼ (lexy refl≤) l))
lemma-insert∼ {x = x} b≤x (left {x = y} {l = l} {r = r} b≤y l⋘r) | inj₂ y≤x 
    with lemma-insert⋘ (lexy y≤x) l⋘r
... | inj₁ lᵢ⋘r = ∼x (/tail /head) /head (lemma++∼r (lemma-insert∼ (lexy y≤x) l)) 
... | inj₂ lᵢ⋗r = ∼x (/tail /head) /head (lemma++∼r (lemma-insert∼ (lexy y≤x) l)) 
lemma-insert∼ {x = x} b≤x (right {x = y} {l = l} {r = r} b≤y l⋙r) 
    with tot≤ x y
... | inj₁ x≤y 
    with lemma-insert⋙ (lexy refl≤) l⋙r
... | inj₁ l⋙rᵢ 
           rewrite lemma-subtyping≡ {val y} {val x} (lexy x≤y) (insert {val y} {y} (lexy refl≤) r) 
                     | lemma-subtyping≡ {val y} {val x} (lexy x≤y) l 
                     = ∼x /head /head (trans∼ (∼x /head (lemma++/ {xs = flatten l}) refl∼) (lemma++∼l {xs = flatten l} (lemma-insert∼ (lexy refl≤) r)))
... | inj₂ l≃rᵢ 
           rewrite lemma-subtyping≡ {val y} {val x} (lexy x≤y) (insert {val y} {y} (lexy refl≤) r) 
                     | lemma-subtyping≡ {val y} {val x} (lexy x≤y) l 
                     = ∼x /head /head (trans∼ (∼x /head (lemma++/ {xs = flatten l}) refl∼) (lemma++∼l {xs = flatten l} (lemma-insert∼ (lexy refl≤) r)))
lemma-insert∼ {x = x} b≤x (right {x = y} {l = l} {r = r} b≤y l⋙r) | inj₂ y≤x 
    with lemma-insert⋙ (lexy y≤x) l⋙r
... | inj₁ l⋙rᵢ = ∼x (/tail /head) /head (trans∼ (∼x /head (lemma++/ {xs = flatten l}) refl∼) (lemma++∼l {xs = flatten l} (lemma-insert∼ (lexy y≤x) r)))
... | inj₂ l≃rᵢ = ∼x (/tail /head) /head (trans∼ (∼x /head (lemma++/ {xs = flatten l}) refl∼) (lemma++∼l {xs = flatten l} (lemma-insert∼ (lexy y≤x) r)))
