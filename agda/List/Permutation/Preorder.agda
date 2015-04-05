module List.Permutation.Preorder (A : Set) where

open import List.Permutation A
open import List.Permutation.Equivalence A
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
                                  trans = lemma-trans∼
                               }
                }
           where
             reflexive-aux : {i j : List A} → i ≡ j → i ∼ j
             reflexive-aux {i = i} {j = .i} refl = lemma-refl∼

