module List.Permutation.Base.Preorder (A : Set) where

open import List.Permutation.Base A
open import List.Permutation.Base.Equivalence A
open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

∼-preorder : Preorder _ _ _
∼-preorder =  record { 
                Carrier = List A;
                _≈_ = _≡_;
                _∼_ = _∼_;
                isPreorder =  record {
                                  isEquivalence = Relation.Binary.Setoid.isEquivalence (setoid (List A)) ;
                                  reflexive = reflexive-aux;
                                  trans = trans∼
                               }
                }
           where
             reflexive-aux : {i j : List A} → i ≡ j → i ∼ j
             reflexive-aux {i = i} {j = .i} refl = refl∼

