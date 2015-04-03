open import Data.Sum renaming (_⊎_ to _∨_)

module InsertSort {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : (a b : A) → a ≤ b ∨ b ≤ a)  where

open import Permutation A
open import Sorting _≤_
open import Bound _≤_
open import OList _≤_
open import Data.List
open import Data.Product renaming (_×_ to _∧_)

insert : A → List A → List A
insert x [] = [ x ]
insert x (y ∷ ys) 
    with tot≤ x y
... | inj₁ _ = x ∷ y ∷ ys
... | inj₂ _ = y ∷ insert x ys

insertSort : List A → List A
insertSort = foldr insert []

lemma-insert-sorted : {xs : List A}(x : A) → Sorted xs → Sorted (insert x xs)
lemma-insert-sorted {xs = .[]} x nils = singls x  
lemma-insert-sorted {xs = .([ y ])} x  (singls y) 
    with tot≤ x y
... | inj₁ x≤y  = conss x≤y (singls y)
... | inj₂ y≤x  = conss y≤x (singls x) 
lemma-insert-sorted x (conss {y} {z} {ys} y≤z szys)
    with tot≤ x y 
... | inj₁ x≤y = conss x≤y (conss y≤z szys)
... | inj₂ y≤x 
    with tot≤ x z | lemma-insert-sorted x szys
... | inj₁ x≤z | _ = conss y≤x (conss x≤z szys)
... | inj₂ z≤x | h = conss y≤z h 

theorem-insertSort-sorted : (xs : List A) → Sorted (insertSort xs)
theorem-insertSort-sorted [] = nils
theorem-insertSort-sorted (x ∷ xs) = lemma-insert-sorted x (theorem-insertSort-sorted xs) 

lemma-insert∼/ : (x : A)(xs : List A) → (insert x xs) / x ⟶ xs
lemma-insert∼/ x [] = /head
lemma-insert∼/ x (y ∷ ys) 
    with tot≤ x y
... | inj₁ _ = /head
... | inj₂ _ = /tail (lemma-insert∼/ x ys)

lemma-insert∼ : (x : A){xs ys : List A} → xs ∼ ys → (x ∷ xs) ∼ (insert x ys)
lemma-insert∼ x {xs} {ys} xs∼ys = ∼x  /head (lemma-insert∼/ x ys) xs∼ys

theorem-insertSort∼ : (xs : List A) → xs ∼ (insertSort xs)
theorem-insertSort∼ [] = ∼[]
theorem-insertSort∼ (x ∷ xs) = lemma-insert∼ x (theorem-insertSort∼ xs)

--

theorem-exists-sorting : (xs : List A) → ∃ (λ ys → xs ∼ ys ∧ Sorted ys)
theorem-exists-sorting [] = [] , ∼[] , nils
theorem-exists-sorting (x ∷ xs) 
    with theorem-exists-sorting xs
... | ys , xs∼ys , Sortedxs = insert x ys , lemma-insert∼ x xs∼ys , lemma-insert-sorted x Sortedxs

--

insert' : { b : Bound} → (x : A) → LeB b (val x) → OList b → OList b
insert' x b≤x onil = :< b≤x onil
insert' x b≤x (:< {x = y} b≤y ys) 
    with tot≤ x y
... | inj₁ x≤y = :< b≤x (:< (lexy x≤y) ys)
... | inj₂ y≤x = :< b≤y (insert' x (lexy y≤x) ys)

insertSort' : List A → OList bot
insertSort' [] = onil
insertSort' (x ∷ xs) = insert' x lebx (insertSort' xs)

lemma-forget-insert' : {b : Bound} → (x : A) → (b≤x : LeB b (val x)) → (xs : OList b) → forget (insert' x b≤x xs) / x ⟶ forget xs
lemma-forget-insert' x b≤x onil = /head
lemma-forget-insert' x b≤x (:< {x = y} b≤y ys) 
    with tot≤ x y
... | inj₁ x≤y = /head
... | inj₂ y≤x = /tail (lemma-forget-insert' x (lexy y≤x) ys)

theorem-insertSort'∼ : (xs : List A) → xs ∼ forget (insertSort' xs)
theorem-insertSort'∼ [] = ∼[]
theorem-insertSort'∼ (x ∷ xs) = ∼x /head (lemma-forget-insert' x lebx (insertSort' xs)) (theorem-insertSort'∼ xs)

