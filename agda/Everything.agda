module Everything where

open import Relation.Binary.Core

postulate A : Set
postulate _≤_ : A → A → Set
postulate tot≤ : Total _≤_
postulate trans≤ : Transitive _≤_

open import BBHeap.Complete.Base _≤_
open import BBHeap.Heap _≤_
open import BBHeap.Height.Convert _≤_ tot≤
open import BBHeap.Height.Log _≤_ tot≤

open import BHeap.Heap _≤_
open import BHeap.Height _≤_ tot≤

open import BTree.Complete.Alternative.Correctness {A}

open import BubbleSort.Correctness.Order _≤_ tot≤ trans≤
open import BubbleSort.Correctness.Permutation _≤_ tot≤ trans≤

open import Heapsort.Correctness.Order _≤_ tot≤ trans≤
open import Heapsort.Correctness.Permutation _≤_ tot≤ trans≤

open import InsertSort.Correctness.Order _≤_ tot≤
open import InsertSort.Correctness.Permutation _≤_ tot≤

open import Mergesort.Correctness.Order _≤_ tot≤
open import Mergesort.Correctness.Permutation _≤_ tot≤

open import PLRTree.Complete.Correctness.Base {A}
open import PLRTree.Drop.Complete _≤_ tot≤
open import PLRTree.Drop.Heap _≤_ tot≤ trans≤
open import PLRTree.Drop.Permutation _≤_ tot≤
open import PLRTree.Heap.Correctness _≤_
open import PLRTree.Insert.Complete _≤_ tot≤
open import PLRTree.Insert.Heap _≤_ tot≤ trans≤
open import PLRTree.Insert.Permutation _≤_ tot≤

open import Quicksort.Correctness.Order _≤_ tot≤ trans≤
open import Quicksort.Correctness.Permutation _≤_ tot≤ 

open import SelectSort.Correctness.Order _≤_ tot≤ trans≤
open import SelectSort.Correctness.Permutation _≤_ tot≤

open import TreeSort.Correctness.Order _≤_ tot≤ trans≤
open import TreeSort.Correctness.Permutation _≤_ tot≤
