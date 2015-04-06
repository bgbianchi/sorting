module BTree.Equality.Properties {A : Set} where

open import BTree {A} 
open import BTree.Equality {A}
open import Relation.Binary.Core

trans≃ : Transitive _≃_
trans≃ ≃lf ≃lf = ≃lf
trans≃ (≃nd x x' l≃r l≃l' l'≃r') (≃nd .x' x'' _ l'≃l'' l''≃r'') = ≃nd x x'' l≃r (trans≃ l≃l' l'≃l'')  l''≃r'' 

symm≃ : Symmetric _≃_
symm≃ ≃lf = ≃lf
symm≃ (≃nd x x' l≃r l≃l' l'≃r') = ≃nd x' x l'≃r' (symm≃ l≃l') l≃r
