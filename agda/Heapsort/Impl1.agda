open import Relation.Binary.Core

module Heapsort.Impl1 {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_ hiding (flatten)
open import BBHeap.Heapify _≤_ tot≤ trans≤
open import BHeap _≤_ hiding (flatten)
open import BHeap.Order _≤_ 
open import BHeap.Order.Properties _≤_ 
open import BHeap.Properties _≤_ 
open import Bound.Lower A  
open import Data.List
open import OList _≤_
  
flatten : {b : Bound}(h : BHeap b) → Acc h → OList b
flatten lf _ = onil
flatten (nd {x = x} b≤x l r) (acc rs) = :< b≤x (flatten (merge tot≤ l r) (rs (merge tot≤ l r) (lemma-merge≤′ tot≤ b≤x l r)))

heapsort : List A → OList bot
heapsort xs = flatten (relax (heapify xs)) (≺-wf (relax (heapify xs)))
