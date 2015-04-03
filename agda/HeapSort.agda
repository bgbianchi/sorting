{-# OPTIONS --sized-types #-}
open import Data.Sum renaming (_⊎_ to _∨_)

module HeapSort {A : Set}
                  (_≤_ : A → A → Set) 
                  (tot≤ : (x y : A) → x ≤ y ∨ y ≤ x) 
                  (trans≤ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z) where

open import Bound _≤_ 
open import BBHeap _≤_
open import BBHeap.Height _≤_ hiding (height' ; #)
open import BHeap _≤_
open import Data.List
open import Data.Nat renaming (_≤_ to _≤ₙ_)
open import Data.Nat.Properties
open import Function using (_∘_)
open import Induction.Nat
open import Induction.WellFounded 
open import OList _≤_
open import Permutation A
open import Permutation.Equivalence A
open import Permutation.Concatenation A
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (trans)
open import SNat
open import Sorting _≤_

open DecTotalOrder decTotalOrder hiding (refl)

refl≤ : {x : A} → x ≤ x
refl≤ {x} 
    with tot≤ x x
... | inj₁ x≤x = x≤x
... | inj₂ x≤x = x≤x 

transLeB : {b b' b'' : Bound} → LeB b b' → LeB b' b'' → LeB b b''
transLeB lebx _ = lebx
transLeB (lexy x≤y) (lexy y≤z) = lexy (trans≤ x≤y y≤z)

subtyping : {b b' : Bound} → LeB b' b → BBHeap b → BBHeap b'
subtyping _ leaf = leaf 
subtyping b'≤b (left b≤x l⋘r) = left (transLeB b'≤b b≤x) l⋘r
subtyping b'≤b (right b≤x l⋙r) = right (transLeB b'≤b b≤x) l⋙r

subtyping⋘ : {b b' b'' b''' : Bound}{h : BBHeap b}{h' : BBHeap b'} → (b''≤b : LeB b'' b) → (b'''≤b' : LeB b''' b') → h ⋘ h' → subtyping b''≤b h ⋘ subtyping b'''≤b' h' 
subtyping⋘ b''≤b b'''≤b' lf⋘ = lf⋘ 
subtyping⋘ b''≤b b'''≤b' (ll⋘ b≤x b'≤x' l⋘r l'⋘r' l'≃r' r≃l') = ll⋘ (transLeB b''≤b b≤x) (transLeB b'''≤b' b'≤x') l⋘r l'⋘r' l'≃r' r≃l'
subtyping⋘ b''≤b b'''≤b' (lr⋘ b≤x b'⋘x' l⋙r l'⋘r' l'≃r' l⋗l') = lr⋘ (transLeB b''≤b b≤x) (transLeB b'''≤b' b'⋘x') l⋙r l'⋘r' l'≃r' l⋗l'

subtyping⋙ : {b b' b'' b''' : Bound}{h : BBHeap b}{h' : BBHeap b'} → (b''≤b : LeB b'' b) → (b'''≤b' : LeB b''' b') → h ⋙ h' → subtyping b''≤b h ⋙ subtyping b'''≤b' h' 
subtyping⋙ b''≤b b'''≤b' (⋙lf b≤x) = ⋙lf (transLeB b''≤b b≤x) 
subtyping⋙ b''≤b b'''≤b' (⋙rl b≤x b'≤x' l⋘r l≃r l'⋘r' l⋗r') = ⋙rl (transLeB b''≤b b≤x) (transLeB b'''≤b' b'≤x') l⋘r l≃r l'⋘r' l⋗r'
subtyping⋙ b''≤b b'''≤b' (⋙rr b≤x b'⋘x' l⋘r l≃r l'⋙r' l≃l') = ⋙rr (transLeB b''≤b b≤x) (transLeB b'''≤b' b'⋘x') l⋘r l≃r l'⋙r' l≃l'

subtyping≃r : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'} → (b''≤b' : LeB b'' b') → h ≃ h' → h ≃ subtyping b''≤b' h' 
subtyping≃r b''≤b' ≃lf = ≃lf
subtyping≃r b''≤b' (≃nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l≃l') = ≃nd b≤x (transLeB b''≤b' b'≤x') l⋘r l'⋘r' l≃r l'≃r' l≃l'

subtyping≃l : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'} → (b''≤b : LeB b'' b) → h ≃ h' → subtyping b''≤b h ≃ h' 
subtyping≃l b''≤b h≃h' = symm≃ (subtyping≃r b''≤b (symm≃ h≃h'))

subtyping≃ : {b b' b'' b''' : Bound}{h : BBHeap b}{h' : BBHeap b'} → (b''≤b : LeB b'' b) → (b'''≤b' : LeB b''' b') → h ≃ h' → subtyping b''≤b h ≃ subtyping b'''≤b' h' 
subtyping≃ b''≤b b'''≤b' h≃h' = subtyping≃r b'''≤b' (subtyping≃l b''≤b h≃h')

subtyping⋗r : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'} → (b''≤b' : LeB b'' b') → h ⋗ h' → h ⋗ subtyping b''≤b' h' 
subtyping⋗r b''≤b' (⋗lf b≤x) = ⋗lf b≤x
subtyping⋗r b''≤b' (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l') = ⋗nd b≤x (transLeB b''≤b' b'≤x') l⋘r l'⋘r' l≃r l'≃r' l⋗l'

subtyping⋗l : {b b' b'' : Bound}{h : BBHeap b}{h' : BBHeap b'} → (b''≤b : LeB b'' b) → h ⋗ h' → subtyping b''≤b h ⋗ h' 
subtyping⋗l b''≤b (⋗lf b≤x) = ⋗lf (transLeB b''≤b b≤x)
subtyping⋗l b''≤b (⋗nd b≤x b'≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l') = ⋗nd (transLeB b''≤b b≤x) b'≤x' l⋘r l'⋘r' l≃r l'≃r' l⋗l'

subtyping⋗ : {b b' b'' b''' : Bound}{h : BBHeap b}{h' : BBHeap b'} → (b''≤b : LeB b'' b) → (b'''≤b' : LeB b''' b') → h ⋗ h' → subtyping b''≤b h ⋗ subtyping b'''≤b' h' 
subtyping⋗ b''≤b b'''≤b' h⋗h' = subtyping⋗r b'''≤b' (subtyping⋗l b''≤b h⋗h')

mutual
  insert : {b : Bound}{x : A} → LeB b (val x) → BBHeap b → BBHeap b
  insert b≤x leaf = left b≤x lf⋘
  insert {x = x} b≤x (left {x = y} b≤y l⋘r) 
      with tot≤ x y
  ... | inj₁ x≤y 
      with lemma-insert⋘ (lexy refl≤) l⋘r
  ... | inj₁ lᵢ⋘r = left b≤x (subtyping⋘ (lexy x≤y) (lexy x≤y) lᵢ⋘r)
  ... | inj₂ lᵢ⋗r = right b≤x (subtyping⋙ (lexy x≤y) (lexy x≤y) (lemma⋗ lᵢ⋗r))
  insert {x = x} b≤x (left {x = y} b≤y l⋘r) | inj₂ y≤x 
      with lemma-insert⋘ (lexy y≤x) l⋘r
  ... | inj₁ lᵢ⋘r = left b≤y lᵢ⋘r 
  ... | inj₂ lᵢ⋗r = right b≤y (lemma⋗ lᵢ⋗r)
  insert {x = x} b≤x (right {x = y} b≤y l⋙r) 
      with tot≤ x y
  ... | inj₁ x≤y 
      with lemma-insert⋙ (lexy refl≤) l⋙r
  ... | inj₁ l⋙rᵢ = right b≤x (subtyping⋙ (lexy x≤y) (lexy x≤y) l⋙rᵢ)
  ... | inj₂ l≃rᵢ = left b≤x (subtyping⋘ (lexy x≤y) (lexy x≤y) (lemma≃ l≃rᵢ))
  insert {x = x} b≤x (right {x = y} b≤y l⋙r) | inj₂ y≤x 
      with lemma-insert⋙ (lexy y≤x) l⋙r
  ... | inj₁ l⋙rᵢ = right b≤y l⋙rᵢ 
  ... | inj₂ l≃rᵢ = left b≤y (lemma≃ l≃rᵢ)

  lemma-insert⋘ : {b b' : Bound}{x : A}{h : BBHeap b}{h' : BBHeap b'} → (b≤x : LeB b (val x)) → h ⋘ h' → insert b≤x h ⋘ h' ∨ insert b≤x h ⋗ h'
  lemma-insert⋘ b≤x lf⋘ = inj₂ (⋗lf b≤x)
  lemma-insert⋘ {x = x} b≤x (ll⋘ {x = y} b≤y b'≤y' l⋘r l'⋘r' l'≃r' r≃l') 
      with tot≤ x y
  ... | inj₁ x≤y 
      with lemma-insert⋘ (lexy refl≤) l⋘r
  ... | inj₁ lᵢ⋘r = inj₁ (ll⋘ b≤x b'≤y' (subtyping⋘ (lexy x≤y) (lexy x≤y) lᵢ⋘r) l'⋘r' l'≃r' (subtyping≃l (lexy x≤y) r≃l')) 
  ... | inj₂ lᵢ⋗r = inj₁ (lr⋘ b≤x b'≤y' (subtyping⋙ (lexy x≤y) (lexy x≤y) (lemma⋗ lᵢ⋗r)) l'⋘r' l'≃r' (subtyping⋗l (lexy x≤y) (lemma⋗≃ lᵢ⋗r r≃l')))  
  lemma-insert⋘ {x = x} b≤x (ll⋘ {x = y} b≤y b'≤y' l⋘r l'⋘r' l'≃r' r≃l') | inj₂ y≤x 
      with lemma-insert⋘ (lexy y≤x) l⋘r
  ... | inj₁ lᵢ⋘r = inj₁ (ll⋘ b≤y b'≤y' lᵢ⋘r l'⋘r' l'≃r' r≃l') 
  ... | inj₂ lᵢ⋗r = inj₁ (lr⋘ b≤y b'≤y' (lemma⋗ lᵢ⋗r) l'⋘r' l'≃r' (lemma⋗≃ lᵢ⋗r r≃l'))  
  lemma-insert⋘ {x = x} b≤x (lr⋘ {x = y} b≤y b'≤y' l⋙r l'⋘r' l'≃r' l⋗l') 
      with tot≤ x y
  ... | inj₁ x≤y 
      with lemma-insert⋙ (lexy refl≤) l⋙r
  ... | inj₁ l⋙rᵢ = inj₁ (lr⋘ b≤x b'≤y' (subtyping⋙ (lexy x≤y) (lexy x≤y) l⋙rᵢ) l'⋘r' l'≃r' (subtyping⋗l (lexy x≤y) l⋗l'))
  ... | inj₂ l≃rᵢ = inj₂ (⋗nd b≤x b'≤y' (subtyping⋘ (lexy x≤y) (lexy x≤y) (lemma≃ l≃rᵢ)) l'⋘r' (subtyping≃ (lexy x≤y) (lexy x≤y) l≃rᵢ) l'≃r' (subtyping⋗l (lexy x≤y) l⋗l'))
  lemma-insert⋘ {x = x} b≤x (lr⋘ {x = y} b≤y b'≤y' l⋙r l'⋘r' l'≃r' l⋗l') | inj₂ y≤x 
      with lemma-insert⋙ (lexy y≤x) l⋙r
  ... | inj₁ l⋙rᵢ = inj₁ (lr⋘ b≤y b'≤y' l⋙rᵢ l'⋘r' l'≃r' l⋗l')
  ... | inj₂ l≃rᵢ = inj₂ (⋗nd b≤y b'≤y' (lemma≃ l≃rᵢ) l'⋘r' l≃rᵢ l'≃r' l⋗l')

  lemma-insert⋙ : {b b' : Bound}{x : A}{h : BBHeap b}{h' : BBHeap b'} → (b'≤x : LeB b' (val x)) → h ⋙ h' → h ⋙ insert b'≤x h' ∨ h ≃ insert b'≤x h'
  lemma-insert⋙ {x = x} b'≤x (⋙lf {x = y} b≤y) = inj₂ (≃nd b≤y b'≤x lf⋘ lf⋘ ≃lf ≃lf ≃lf)
  lemma-insert⋙ {x = x} b'≤x (⋙rl {x' = y'} b≤y b'≤y' l⋘r l≃r l'⋘r' l⋗r') 
      with tot≤ x y'
  ... | inj₁ x≤y' 
      with lemma-insert⋘ (lexy refl≤) l'⋘r'
  ... | inj₁ l'ᵢ⋘r' = inj₁ (⋙rl b≤y b'≤x l⋘r l≃r (subtyping⋘ (lexy x≤y') (lexy x≤y') l'ᵢ⋘r') (subtyping⋗r (lexy x≤y') l⋗r'))
  ... | inj₂ l'ᵢ⋗r' = inj₁ (⋙rr b≤y b'≤x l⋘r l≃r (subtyping⋙ (lexy x≤y') (lexy x≤y') (lemma⋗ l'ᵢ⋗r')) (subtyping≃r (lexy x≤y') (lemma⋗⋗ l⋗r' l'ᵢ⋗r')))
  lemma-insert⋙ {x = x} b'≤x (⋙rl {x' = y'} b≤y b'≤y' l⋘r l≃r l'⋘r' l⋗r') | inj₂ y'≤x 
      with lemma-insert⋘ (lexy y'≤x) l'⋘r'
  ... | inj₁ l'ᵢ⋘r' = inj₁ (⋙rl b≤y b'≤y' l⋘r l≃r l'ᵢ⋘r' l⋗r')
  ... | inj₂ l'ᵢ⋗r' = inj₁ (⋙rr b≤y b'≤y' l⋘r l≃r (lemma⋗ l'ᵢ⋗r') (lemma⋗⋗ l⋗r' l'ᵢ⋗r'))
  lemma-insert⋙ {x = x} b'≤x (⋙rr {x' = y'} b≤y b'≤y' l⋘r l≃r l'⋙r' l≃l') 
      with tot≤ x y'
  ... | inj₁ x≤y' 
      with lemma-insert⋙ (lexy refl≤) l'⋙r'
  ... | inj₁ l'⋙r'ᵢ = inj₁ (⋙rr b≤y b'≤x l⋘r l≃r (subtyping⋙ (lexy x≤y') (lexy x≤y') l'⋙r'ᵢ) (subtyping≃r (lexy x≤y') l≃l'))
  ... | inj₂ l'≃r'ᵢ = inj₂ (≃nd b≤y b'≤x l⋘r (subtyping⋘ (lexy x≤y') (lexy x≤y') (lemma≃ l'≃r'ᵢ)) l≃r (subtyping≃ (lexy x≤y') (lexy x≤y') l'≃r'ᵢ) (subtyping≃r (lexy x≤y') l≃l'))
  lemma-insert⋙ {x = x} b'≤x (⋙rr {x' = y'} b≤y b'≤y' l⋘r l≃r l'⋙r' l≃l') | inj₂ y'≤x 
      with lemma-insert⋙ (lexy y'≤x) l'⋙r'
  ... | inj₁ l'⋙r'ᵢ = inj₁ (⋙rr b≤y b'≤y' l⋘r l≃r l'⋙r'ᵢ l≃l')
  ... | inj₂ l'≃r'ᵢ = inj₂ (≃nd b≤y b'≤y' l⋘r (lemma≃ l'≃r'ᵢ) l≃r l'≃r'ᵢ l≃l')

convert : {b : Bound}(h : BBHeap b) → BHeap b
convert leaf = lf
convert (left {l = l} {r = r} b≤x _) = 
                              nd b≤x (convert l) (convert r) 
convert (right {l = l} {r = r} b≤x _) = 
                              nd b≤x (convert l) (convert r) 

+id : (n : ℕ) → n + zero ≡  n
+id zero = refl
+id (suc n) = cong suc (+id n)

+assoc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+assoc zero n = refl
+assoc (suc m) n = cong suc (+assoc m n)

merge : {b : Bound}(l r : BHeap b) → BHeap b
merge lf r = r
merge l lf = l
merge (nd {x = x} b≤x l r) (nd {x = x'} b≤x' l' r') 
    with tot≤ x x'
... | inj₁ x≤x' = nd b≤x (merge l r) (nd (lexy x≤x') l' r') 
... | inj₂ x'≤x = nd b≤x' (nd (lexy x'≤x) l r) (merge l' r')

lemma-merge-lf : {b : Bound}(h : BHeap b) → merge h lf ≡ h
lemma-merge-lf lf = refl
lemma-merge-lf (nd b≤x l r) = refl

lemma-merge# : {b : Bound}(l r : BHeap b) → # (merge l r) ≡ # l + # r
lemma-merge# lf r = refl
lemma-merge# l lf rewrite lemma-merge-lf l | +id (# l) = refl
lemma-merge# (nd {x = y} x≤y l r) (nd {x = y'} x≤y' l' r') 
    with tot≤ y y'
... | inj₁ y≤y' rewrite lemma-merge# l r = refl
... | inj₂ y'≤y rewrite lemma-merge# l' r' | +assoc (# l + # r) (# l' + # r') = refl

lemma-merge≤′ : {b : Bound}{x : A}(b≤x : LeB b (val x))(l r : BHeap (val x)) → suc (# (merge l r)) ≤′ # (nd b≤x l r)
lemma-merge≤′ b≤x l r rewrite lemma-merge# l r = ≤′-refl

ii-acc : ∀ {b} {h} → Acc _<′_ (# {b} h) → Terminates h
ii-acc (acc rs) = termination-proof (λ h' #h'<′#h → ii-acc (rs (# h') #h'<′#h))

≺-wf : ∀ {b} h → Terminates {b} h 
≺-wf = λ h → ii-acc (<-well-founded (# h)) 

flatten : {b : Bound}(h : BHeap b) → Terminates h → OList b
flatten lf _ = onil
flatten (nd {x = x} b≤x l r) (termination-proof rs) = :< x  b≤x (flatten (merge l r) (rs (merge l r) (lemma-merge≤′ b≤x l r)))

heapify : List A → BBHeap bot
heapify [] = leaf
heapify (x ∷ xs) = insert {x = x} lebx (heapify xs) 

heapsort : List A → OList bot
heapsort xs = flatten (convert (heapify xs)) (≺-wf (convert (heapify xs)))

theorem-heapsort-sorted : (xs : List A) → Sorted (forget (heapsort xs))
theorem-heapsort-sorted = lemma-olist-sorted ∘ heapsort

++id : (xs : List A) → xs ++ [] ≡ xs
++id [] = refl
++id (x ∷ xs) = cong (_∷_ x) (++id xs)

flatten' : {b : Bound}(h : BHeap b) → List A
flatten' lf = []
flatten' (nd {x = x} b≤x l r) = x ∷ (flatten' l ++ flatten' r)

lemma-merge-flatten' : {b : Bound}(l r : BHeap b) → flatten' (merge l r) ∼ (flatten' l ++ flatten' r)
lemma-merge-flatten' lf r = lemma-refl∼
lemma-merge-flatten' l lf rewrite lemma-merge-lf l | ++id (flatten' l) = lemma-refl∼
lemma-merge-flatten' (nd {x = y} b≤x l r) (nd {x = y'} b≤y' l' r') 
    with tot≤ y y'
... | inj₁ y≤y' = lemma++∼r (∼x /head /head (lemma-merge-flatten' l r))
... | inj₂ y'≤y = lemma-trans∼ (lemma++∼l {xs = y' ∷ (y ∷ flatten' l ++ flatten' r)} (lemma-merge-flatten' l' r')) (∼x /head (lemma++/ {xs = y ∷ flatten' l ++ flatten' r}) lemma-refl∼)

lemma-flatten-flatten' : {b : Bound}(h : BHeap b)(tₕ : Terminates h) → forget (flatten h tₕ) ∼ flatten' h
lemma-flatten-flatten' lf _ = ∼[]
lemma-flatten-flatten' (nd b≤x l r) (termination-proof rs) = ∼x /head /head (lemma-trans∼ (lemma-flatten-flatten' (merge l r) (rs (merge l r) (lemma-merge≤′ b≤x l r))) (lemma-merge-flatten' l r))

lemma-flatten'-flatten : {b : Bound}(h : BHeap b)(tₕ : Terminates h) → (flatten' h) ∼ (forget (flatten h tₕ))
lemma-flatten'-flatten h tₕ = lemma-sym∼ (lemma-flatten-flatten' h tₕ)

lemma-subtyping-flatten' : {b b' : Bound}(b'≤b : LeB b' b)(h : BBHeap b) → (flatten' (convert (subtyping b'≤b h))) ≡ flatten' (convert h)
lemma-subtyping-flatten' b'≤b leaf = refl
lemma-subtyping-flatten' b'≤b (left {l = l} {r = r} b≤x l⋘r) rewrite lemma-subtyping-flatten' b≤x l | lemma-subtyping-flatten' b≤x r = refl
lemma-subtyping-flatten' b'≤b (right {l = l} {r = r} b≤x l⋙r) rewrite lemma-subtyping-flatten' b≤x l | lemma-subtyping-flatten' b≤x r = refl

lemma-insert-flatten' : {b : Bound}{x : A}(b≤x : LeB b (val x))(h : BBHeap b) → (x ∷ flatten' (convert h)) ∼ (flatten' (convert (insert b≤x h)))
lemma-insert-flatten' b≤x leaf = lemma-refl∼
lemma-insert-flatten' {x = x} b≤x (left {x = y} {l = l} {r = r} b≤y l⋘r) 
    with tot≤ x y
... | inj₁ x≤y 
    with lemma-insert⋘ (lexy refl≤) l⋘r
... | inj₁ lᵢ⋘r rewrite lemma-subtyping-flatten' (lexy x≤y) (insert (lexy refl≤) l) | lemma-subtyping-flatten' (lexy x≤y) r = ∼x /head /head (lemma++∼r (lemma-insert-flatten' (lexy refl≤) l)) 
... | inj₂ lᵢ⋗r rewrite lemma-subtyping-flatten' (lexy x≤y) (insert (lexy refl≤) l) | lemma-subtyping-flatten' (lexy x≤y) r = ∼x /head /head (lemma++∼r (lemma-insert-flatten' (lexy refl≤) l))
lemma-insert-flatten' {x = x} b≤x (left {x = y} {l = l} {r = r} b≤y l⋘r) | inj₂ y≤x 
    with lemma-insert⋘ (lexy y≤x) l⋘r
... | inj₁ lᵢ⋘r = ∼x (/tail /head) /head (lemma++∼r (lemma-insert-flatten' (lexy y≤x) l)) 
... | inj₂ lᵢ⋗r = ∼x (/tail /head) /head (lemma++∼r (lemma-insert-flatten' (lexy y≤x) l)) 
lemma-insert-flatten' {x = x} b≤x (right {x = y} {l = l} {r = r} b≤y l⋙r) 
    with tot≤ x y
... | inj₁ x≤y 
    with lemma-insert⋙ (lexy refl≤) l⋙r
... | inj₁ l⋙rᵢ 
                   rewrite lemma-subtyping-flatten' (lexy x≤y) (insert (lexy refl≤) r) 
                            | lemma-subtyping-flatten' (lexy x≤y) l = ∼x /head /head (lemma-trans∼ (∼x /head (lemma++/ {xs = flatten' (convert l)}) lemma-refl∼) (lemma++∼l {xs = flatten' (convert l)} (lemma-insert-flatten' (lexy refl≤) r)))
... | inj₂ l≃rᵢ 
                   rewrite lemma-subtyping-flatten' (lexy x≤y) (insert (lexy refl≤) r) 
                            | lemma-subtyping-flatten' (lexy x≤y) l = ∼x /head /head (lemma-trans∼ (∼x /head (lemma++/ {xs = flatten' (convert l)}) lemma-refl∼) (lemma++∼l {xs = flatten' (convert l)} (lemma-insert-flatten' (lexy refl≤) r)))
lemma-insert-flatten' {x = x} b≤x (right {x = y} {l = l} {r = r} b≤y l⋙r) | inj₂ y≤x 
    with lemma-insert⋙ (lexy y≤x) l⋙r
... | inj₁ l⋙rᵢ = ∼x (/tail /head) /head (lemma-trans∼ (∼x /head (lemma++/ {xs = flatten' (convert l)}) lemma-refl∼) (lemma++∼l {xs = flatten' (convert l)} (lemma-insert-flatten' (lexy y≤x) r)))
... | inj₂ l≃rᵢ = ∼x (/tail /head) /head (lemma-trans∼ (∼x /head (lemma++/ {xs = flatten' (convert l)}) lemma-refl∼) (lemma++∼l {xs = flatten' (convert l)} (lemma-insert-flatten' (lexy y≤x) r)))

theorem-heapsort∼ : (xs : List A) → xs ∼ forget (heapsort xs)
theorem-heapsort∼ [] = ∼[]
theorem-heapsort∼ (x ∷ xs) = lemma-trans∼ (lemma-trans∼ (∼x /head /head (lemma-trans∼ (theorem-heapsort∼ xs) (lemma-flatten-flatten' h' tₕ'))) (lemma-insert-flatten' lebx h)) (lemma-flatten'-flatten (hᵢ) tₕᵢ)
  where     h = heapify xs
            h' = convert h
            tₕ' = ≺-wf h'
            hᵢ = convert (insert lebx h)
            tₕᵢ = ≺-wf hᵢ

heightₙ : {b : Bound} → BHeap b → ℕ
heightₙ lf = zero
heightₙ (nd _ l r) 
    with total (heightₙ l) (heightₙ r) 
... | inj₁ hl≤hr = suc (heightₙ r)
... | inj₂ hr≤hl = suc (heightₙ l)

toNat : SNat → ℕ
toNat zero = zero
toNat (succ n) = suc (toNat n)

data _⊳_ : {b b' : Bound} → BHeap b → BHeap b' → Set where
  ⊳leaf : {b b' : Bound} 
                   → lf {b} ⊳ lf {b'}
  ⊳left : {b b' : Bound}{x : A}{l r : BHeap (val x)}{l' : BHeap b'}
                   (b≤x : LeB b (val x)) 
                   → l ⊳ r → l ⊳ l' 
                   → (nd b≤x l r) ⊳ l'
  ⊳both : {b b' : Bound}{x x' : A}{l r : BHeap (val x)}{l' r' : BHeap (val x')}
                   (b≤x : LeB b (val x))
                   (b'≤x' : LeB b' (val x')) 
                   → l ⊳ r 
                   → l ⊳ l' 
                   → l ⊳ r' 
                   → (nd b≤x l r) ⊳ (nd b'≤x' l' r')

lemma-≃-⊳ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ≃ r → convert l ⊳ convert r
lemma-≃-⊳ ≃lf = ⊳leaf
lemma-≃-⊳ (≃nd b≤x b'≤x' _ _ l≃r l'≃r' l≃l') = ⊳both b≤x b'≤x' (lemma-≃-⊳ l≃r) (lemma-≃-⊳ l≃l') (lemma-≃-⊳ (trans≃ l≃l' l'≃r'))

lemma-⋗-⊳ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋗ r → convert l ⊳ convert r
lemma-⋗-⊳ (⋗lf b≤x) = ⊳left b≤x ⊳leaf ⊳leaf
lemma-⋗-⊳ (⋗nd b≤x b'≤x' _ _ l≃r l'≃r' l⋗l') = ⊳both b≤x b'≤x' (lemma-≃-⊳ l≃r) (lemma-⋗-⊳ l⋗l') (lemma-⋗-⊳ (lemma⋗≃ l⋗l' l'≃r'))

lemma-⋙-⊳ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋙ r → convert l ⊳ convert r
lemma-⋙-⊳ (⋙lf b≤x) = ⊳left b≤x ⊳leaf ⊳leaf
lemma-⋙-⊳ (⋙rl b≤x b'≤x' _ l≃r l'⋘r' l⋗r') = ⊳both b≤x b'≤x' (lemma-≃-⊳ l≃r) (lemma-⋙-⊳ (lemma-⋘-⋗ l'⋘r' l⋗r')) (lemma-⋗-⊳ l⋗r')
lemma-⋙-⊳ (⋙rr b≤x b'≤x' _ l≃r l'⋙r' l≃l') =  ⊳both b≤x b'≤x' (lemma-≃-⊳ l≃r) (lemma-≃-⊳ l≃l') (lemma-⋙-⊳ (lemma-≃-⋙ l≃l' l'⋙r'))

lemma-⋘-⊳ : {b b' : Bound}{l : BBHeap b}{r : BBHeap b'} → l ⋘ r → convert l ⊳ convert r
lemma-⋘-⊳ lf⋘ = ⊳leaf
lemma-⋘-⊳ (ll⋘ b≤x b'≤x' l⋘r _ l'≃r' r≃l') = ⊳both b≤x b'≤x' (lemma-⋘-⊳ l⋘r) (lemma-⋘-⊳ (lemma-⋘-≃ l⋘r r≃l')) (lemma-⋘-⊳ (lemma-⋘-≃ l⋘r (trans≃ r≃l' l'≃r')))
lemma-⋘-⊳ (lr⋘ b≤x b'≤x' l⋙r _ l'≃r' l⋗l') = ⊳both b≤x b'≤x' (lemma-⋙-⊳ l⋙r) (lemma-⋗-⊳ l⋗l') (lemma-⋗-⊳ (lemma⋗≃ l⋗l' l'≃r'))

lemma-⊳-heightₙ : {b b' : Bound}{l : BHeap b}{r : BHeap b'} → l ⊳ r → heightₙ r ≤ₙ heightₙ l 
lemma-⊳-heightₙ ⊳leaf = z≤n
lemma-⊳-heightₙ (⊳left {l = l} {r = r} b≤x l⊳r l⊳l') 
    with total (heightₙ l) (heightₙ r) 
... | inj₁ hl≤hr rewrite antisym (lemma-⊳-heightₙ l⊳r) hl≤hr = ≤-step (lemma-⊳-heightₙ l⊳l')
... | inj₂ hr≤hl = trans (lemma-⊳-heightₙ l⊳l') (≤-step (reflexive refl))
lemma-⊳-heightₙ (⊳both {l = l} {r = r} {l' = l'} {r' = r'} b≤x b'≤x' l⊳r l⊳l' l⊳r') 
    with total (heightₙ l) (heightₙ r) | total (heightₙ l') (heightₙ r') 
... | inj₁ hl≤hr | inj₁ hl'≤hr' rewrite antisym (lemma-⊳-heightₙ l⊳r) hl≤hr = s≤s (lemma-⊳-heightₙ l⊳r')
... | inj₁ hl≤hr | inj₂ hr'≤hl' rewrite antisym (lemma-⊳-heightₙ l⊳r) hl≤hr = s≤s (lemma-⊳-heightₙ l⊳l')
... | inj₂ hr≤hl | inj₁ hl'≤hr' = s≤s (lemma-⊳-heightₙ l⊳r')
... | inj₂ hr≤hl | inj₂ hr'≤hl' = s≤s (lemma-⊳-heightₙ l⊳l')

theorem-height-convert : {b : Bound}(h : BBHeap b) → toNat (height h) ≡ heightₙ (convert h)
theorem-height-convert leaf = refl
theorem-height-convert (left {l = l} {r = r} _ l⋘r) 
    with total (heightₙ (convert l)) (heightₙ (convert r)) 
... | inj₁ hl≤hr rewrite antisym (lemma-⊳-heightₙ (lemma-⋘-⊳ l⋘r)) hl≤hr | theorem-height-convert l = refl
... | inj₂ hr≤hl rewrite theorem-height-convert l = refl
theorem-height-convert (right {l = l} {r = r} _ l⋙r) 
    with total (heightₙ (convert l)) (heightₙ (convert r)) 
... | inj₁ hl≤hr rewrite antisym (lemma-⊳-heightₙ (lemma-⋙-⊳ l⋙r)) hl≤hr | theorem-height-convert l = refl
... | inj₂ hr≤hl rewrite theorem-height-convert l = refl

theorem-heightₙ-merge : {b : Bound}{x : A}(b≤x : LeB b (val x))(l r : BHeap (val x)) → heightₙ (merge l r) ≤ₙ heightₙ (nd b≤x l r)
theorem-heightₙ-merge _ lf r = ≤-step (reflexive refl)
theorem-heightₙ-merge _ l lf rewrite lemma-merge-lf l 
    with total (heightₙ l) zero 
... | inj₁ hl≤0 rewrite antisym hl≤0 z≤n = ≤-step (reflexive refl)
... | inj₂ 0≤hl = ≤-step (reflexive refl)
theorem-heightₙ-merge b≤x (nd {x = y} x≤y l r) (nd {x = y'} x≤y' l' r') 
    with tot≤ y y' | total (heightₙ (nd x≤y l r)) (heightₙ (nd x≤y' l' r')) 
... | inj₁ y≤y' | inj₁ hylr≤hy'l'r' 
    with total (heightₙ (merge l r)) (heightₙ (nd (lexy y≤y') l' r'))
... | inj₁ hmlr≤hy'l'r' = reflexive refl
... | inj₂ hy'l'r'≤hmlr rewrite antisym (trans (theorem-heightₙ-merge x≤y l r) hylr≤hy'l'r') hy'l'r'≤hmlr = reflexive refl
theorem-heightₙ-merge b≤x (nd {x = y} x≤y l r) (nd {x = y'} x≤y' l' r') | inj₁ y≤y' | inj₂ hy'l'r'≤hylr 
    with total (heightₙ (merge l r)) (heightₙ (nd (lexy y≤y') l' r'))
... | inj₁ hmlr≤hy'l'r' = s≤s hy'l'r'≤hylr
... | inj₂ hy'l'r'≤hmlr = s≤s (theorem-heightₙ-merge x≤y l r)
theorem-heightₙ-merge b≤x (nd {x = y} x≤y l r) (nd {x = y'} x≤y' l' r') | inj₂ y'≤y | inj₁ hylr≤hy'l'r'  
    with total (heightₙ (nd (lexy y'≤y) l r)) (heightₙ (merge l' r'))
... | inj₁ hylr≤hml'r' = s≤s (theorem-heightₙ-merge x≤y' l' r')
... | inj₂ hml'r'≤hylr = s≤s hylr≤hy'l'r'
theorem-heightₙ-merge b≤x (nd {x = y} x≤y l r) (nd {x = y'} x≤y' l' r') | inj₂ y'≤y | inj₂ hy'l'r'≤hylr  
    with total (heightₙ (nd (lexy y'≤y) l r)) (heightₙ (merge l' r'))
... | inj₁ hylr≤hml'r' rewrite antisym (trans (theorem-heightₙ-merge x≤y' l' r') hy'l'r'≤hylr) hylr≤hml'r' = reflexive refl
... | inj₂ hml'r'≤hylr = reflexive refl
