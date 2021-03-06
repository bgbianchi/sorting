# Sorting

Formalization of some sorting algorithms in Agda

## Currently formalized algorithms ##
- **Bubble sort**
- **Heapsort**
- **Insertion sort**
- **Mergesort**
- **Quicksort**
- **Selection sort**
- **Tree sort**

## Source files ##
- **agda\BBHeap\Complete\*** - Dependent binary heaps are complete trees
- **agda\BBHeap\Drop.agda** - Root deletion on dependent binary heaps
- **agda\BBHeap\DropLast.agda** - Deletion of the last inserted element on dependent binary heaps
- **agda\BBHeap\Height\*** - Height related proofs for dependent binary heaps
- **agda\BBHeap\Heap.agda** - Dependent binary heaps have the heap property
- **agda\BBHeap\Last.agda** - Getting the last inserted element on dependent binary heaps
- **agda\BBHeap\Push.agda** - Root deletion followed by one insertion on dependent binary heaps
- **agda\BHeap\Heap.agda** - Dependent ordinary heaps have the heap property
- **agda\BHeap\Height.agda** - Height related proofs for dependent ordinary heaps
- **agda\BHeap\Order.agda** - Accesibility for dependent ordinary heaps
- **agda\BTree\Complete\*** - Complete predicates for binary trees 
- **agda\BTree\Heap.agda** - Heap predicate for binary trees 
- **agda\Bound\*** - Many definitions for bounds and order relations for them
- **agda\BubbleSort\*** - Bubble sort implementations and correctness proof
- **agda\Heapsort\*** - Heapsort implementations and correctness proof
- **agda\InsertSort\*** - Insertion sort implementations and correctness proofs
- **agda\List\Permutation\Base.agda** - Permutation relation between ordinary lists
- **agda\List\Sorted.agda** - Order predicate for ordinary lists
- **agda\List\Order\*** - Many order relations between elements and ordinary lists
- **agda\Mergesort\*** - Mergesort implementations and correctness proof
- **agda\PLRTree\Complete\** - Complete tagged trees are complete trees
- **agda\PLRTree\Heap\*** - Tagged trees with the heap property are trees with the heap property
- **agda\PLRTree\Drop\*** - Deletions on tagged heaps produce tagged binary heaps
- **agda\PLRTree\Insert\*** - Inserting into tagged heaps produces tagged binary heaps
- **agda\PLRTree\Complete.agda** - Complete predicate for tagged trees
- **agda\PLRTree\Heap.agda** - Heap predicate for tagged binary trees
- **agda\PLRTree\Drop.agda** - Deletion algorithm for tagged binary heaps
- **agda\PLRTree\Insert.agda** - Insertion algorithm for tagged binary heaps
- **agda\Quicksort\*** - Quicksort implementations and correctness proof
- **agda\SList\Order.agda** - Order relation between elements and sized lists
- **agda\SNat\Order.agda** - Many order relations for sized natural numbers
- **agda\SNat\Log.agda** - Binary logarithms based on sized natural numbers
- **agda\SOList\*** - Many dependent sorted lists with size
- **agda\SelectSort\*** - Selection sort implementations and correctness proof
- **agda\TreeSort\*** - Tree sort implementations and correctness proofs
- **agda\BBHeap.agda** - Dependent binary heaps
- **agda\BBSTree.agda** - Dependent binary search trees
- **agda\BHeap.agda** - Dependent ordinary heaps
- **agda\BSTree.agda** - Binary search preadicate for binary trees
- **agda\BTree.agda** - Binary trees
- **agda\OList.agda** - Dependent sorted lists
- **agda\PLRTree.agda** - Tagged trees for implementing binary heaps
- **agda\SBList.agda** - Bounded lists with size
- **agda\SList.agda** - Sized lists
- **agda\SNat.agda** - Sized natural numbers
- **hs\BHeap** - Binary heaps in Haskell
- **hs\PLRTree** - Complete binary trees in Haskell

## Agda version ##
2.3.2.2

## Standard library version ##
0.7

## Build status ##

[![Build Status](https://secure.travis-ci.org/bgbianchi/sorting.png?branch=master)](http://travis-ci.org/bgbianchi/sorting)
