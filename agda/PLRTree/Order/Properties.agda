module PLRTree.Order.Properties {A : Set} where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Function
open import Induction.Nat
open import Induction.WellFounded 
open import PLRTree {A}
open import PLRTree.Order {A}
open import Relation.Binary
open import Relation.Binary.PropositionalEquality 

open DecTotalOrder decTotalOrder hiding (refl)
open Inverse-image {_<_ = _<′_} height

≺-wf : Well-founded (_<′_ on height)
≺-wf = well-founded <-well-founded

lemma-≺-left : (t : Tag)(x : A)(l r : PLRTree) → l ≺ node t x l r
lemma-≺-left t x l r 
    with total (height l) (height r)
... | inj₁ hl≤hr =  s≤′s (≤⇒≤′ hl≤hr)
... | inj₂ hr≤hl = ≤′-refl

lemma-≺-right : (t : Tag)(x : A)(l r : PLRTree) → r ≺ node t x l r
lemma-≺-right t x l r 
    with total (height l) (height r)
... | inj₁ hl≤hr = ≤′-refl 
... | inj₂ hr≤hl = s≤′s (≤⇒≤′ hr≤hl)

lemma-≡-height : (t : Tag)(x y : A)(l r : PLRTree) → height (node t x l r) ≡ height (node t y l r)
lemma-≡-height t x y l r 
    with total (height l) (height r)
... | inj₁ hl≤hr = refl
... | inj₂ hr≤hl = refl
