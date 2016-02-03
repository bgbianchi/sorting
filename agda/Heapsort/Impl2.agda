open import Relation.Binary.Core

module Heapsort.Impl2 {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : Total _≤_) 
                  (trans≤ : Transitive _≤_) where

open import BBHeap _≤_ hiding (flatten)
open import BBHeap.Compound _≤_
open import BBHeap.Drop _≤_ tot≤ trans≤
open import BBHeap.Drop.Properties _≤_ tot≤ trans≤
open import BBHeap.Heapify _≤_ tot≤ trans≤
open import BBHeap.Order _≤_ 
open import BBHeap.Order.Properties _≤_ 
open import Bound.Lower A 
open import Bound.Lower.Order _≤_  
open import Data.List hiding (drop)
open import OList _≤_

flatten : {b : Bound}(h : BBHeap b) → Acc h → OList b
flatten leaf _ = onil
flatten (left b≤x l⋘r) (acc rs) = :< b≤x (flatten (drop (cl b≤x l⋘r)) (rs (drop (cl b≤x l⋘r)) (lemma-drop≤′ (cl b≤x l⋘r))))
flatten (right b≤x l⋙r) (acc rs) = :< b≤x (flatten (drop (cr b≤x l⋙r)) (rs (drop (cr b≤x l⋙r)) (lemma-drop≤′ (cr b≤x l⋙r))))

heapsort : List A → OList bot
heapsort xs = flatten (heapify xs) (≺-wf (heapify xs))
