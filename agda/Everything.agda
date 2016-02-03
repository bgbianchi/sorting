module Everything where

open import Relation.Binary.Core

postulate A : Set
postulate _≤_ : A → A → Set
postulate tot≤ : Total _≤_
postulate trans≤ : Transitive _≤_

open import BBHeap.Everything _≤_ tot≤ trans≤

open import BHeap.Everything _≤_ tot≤

open import BTree.Complete.Alternative.Correctness {A}

open import BubbleSort.Everything _≤_ tot≤ trans≤

open import Heapsort.Everything _≤_ tot≤ trans≤

open import InsertSort.Everything _≤_ tot≤

open import List.Permutation.Base.Bag A

open import Mergesort.Everything _≤_ tot≤

open import PLRTree.Everything _≤_ tot≤ trans≤

open import Quicksort.Everything _≤_ tot≤ trans≤

open import SelectSort.Everything _≤_ tot≤ trans≤

open import TreeSort.Everything _≤_ tot≤ trans≤
