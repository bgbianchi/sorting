module README where

open import Relation.Binary.Core

postulate A : Set
postulate _≤_ : A → A → Set
postulate tot≤ : Total _≤_
postulate trans≤ : Transitive _≤_

import BBHeap.Complete.Base _≤_
import BBHeap.Heap _≤_
import BBHeap.Height.Convert _≤_ tot≤
import BBHeap.Height.Log _≤_ tot≤

import BHeap.Heap _≤_
import BHeap.Height _≤_ tot≤

import BTree.Complete.Alternative.Correctness {A}

import BubbleSort.Correctness.Order _≤_ tot≤ trans≤
import BubbleSort.Correctness.Permutation _≤_ tot≤ trans≤

import Heapsort.Correctness.Order _≤_ tot≤ trans≤
import Heapsort.Correctness.Permutation _≤_ tot≤ trans≤

import InsertSort.Correctness.Order _≤_ tot≤
import InsertSort.Correctness.Permutation _≤_ tot≤

import Mergesort.Correctness.Order _≤_ tot≤
import Mergesort.Correctness.Permutation _≤_ tot≤

import PLRTree.Complete.Correctness.Base {A}
import PLRTree.Drop.Complete _≤_ tot≤
import PLRTree.Drop.Heap _≤_ tot≤ trans≤
import PLRTree.Drop.Permutation _≤_ tot≤
import PLRTree.Heap.Correctness _≤_
import PLRTree.Insert.Complete _≤_ tot≤
import PLRTree.Insert.Heap _≤_ tot≤ trans≤
import PLRTree.Insert.Permutation _≤_ tot≤

import Quicksort.Correctness.Order _≤_ tot≤ trans≤
import Quicksort.Correctness.Permutation _≤_ tot≤ 

import SelectSort.Correctness.Order _≤_ tot≤ trans≤
import SelectSort.Correctness.Permutation _≤_ tot≤

import TreeSort.Correctness.Order _≤_ tot≤ trans≤
import TreeSort.Correctness.Permutation _≤_ tot≤
