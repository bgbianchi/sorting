module List.Permutation.Base.Bag (A : Set) where

open import Data.List
open import Data.List.Any as Any
open import Data.List.Any.BagAndSetEquality
open import Data.List.Any.Properties
open import Data.Sum renaming (_⊎_ to _∨_)
open import Function
open import Function.Inverse hiding (sym ; _∘_ ; id)
open import Function.Related as Related hiding (_∼[_]_) 
open import List.Permutation.Base A
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P hiding (sym)

open Any.Membership-≡
open EqR ([ bag ]-Equality A)
open Related.EquationalReasoning renaming (_∎ to _□)

infix 4 _≈-bag_

_≈-bag_ : ∀ {a} {A : Set a} → List A → List A → Set a
xs ≈-bag ys = xs ∼[ bag ] ys

sym-≈-bag : {xs ys : List A} → xs ≈-bag ys → ys ≈-bag xs
sym-≈-bag {xs} {ys} xs≈ys {z} = record
  { to         = Inverse.from xs≈ys
  ; from       = Inverse.to xs≈ys
  ; inverse-of = record
    { left-inverse-of  = Inverse.right-inverse-of xs≈ys
    ; right-inverse-of = Inverse.left-inverse-of xs≈ys
    }
  }

refl-≈-bag : {xs : List A} → xs ≈-bag xs
refl-≈-bag {xs} = begin xs ∎

∨↔ : ∀{a b}{A : Set a}{B : Set b} → (A ∨ B) ↔ (B ∨ A)
∨↔ = record
  { to         = P.→-to-⟶ ∨→
  ; from       = P.→-to-⟶ ∨→
  ; inverse-of = record
    { left-inverse-of  = v→∘v→
    ; right-inverse-of = v→∘v→
    }
  }
  where
  ∨→ : ∀{a b}{A : Set a}{B : Set b} → (A ∨ B) → (B ∨ A)
  ∨→ (inj₁ x) = inj₂ x
  ∨→ (inj₂ x) = inj₁ x

  v→∘v→ : ∀{a b}{A : Set a}{B : Set b}(a∨b : A ∨ B) → ∨→ (∨→ a∨b) ≡ a∨b
  v→∘v→ (inj₁ _) = refl
  v→∘v→ (inj₂ _) = refl

xy≈-bag-yx : {x y : A} → x ∷ y ∷ [] ≈-bag y ∷ x ∷ []
xy≈-bag-yx {x} {y} {z} = 
  z ∈ x ∷ y ∷ [] ↔⟨ sym $ ++↔ {xs = x ∷ []} {ys = y ∷ []} ⟩
  (z ∈ x ∷ [] ∨ z ∈ y ∷ []) ↔⟨ ∨↔ ⟩ 
  (z ∈ y ∷ [] ∨ z ∈ x ∷ []) ↔⟨ ++↔ ⟩
  z ∈ y ∷ x ∷ [] □

lemma-/-≈-bag : {y : A}{xs ys : List A} → xs / y ⟶ ys → xs ≈-bag (y ∷ ys)
lemma-/-≈-bag /head = refl-≈-bag 
lemma-/-≈-bag (/tail {x} {y} {xs} {ys} xs/y⟶ys) = begin
  x ∷ xs ≈⟨ ∷-cong refl (lemma-/-≈-bag xs/y⟶ys) ⟩
  x ∷ y ∷ ys ≈⟨ ++-cong xy≈-bag-yx refl-≈-bag ⟩
  y ∷ x ∷ ys ∎

lemma-∼-≈-bag : {xs ys : List A} → xs ∼ ys → xs ≈-bag ys
lemma-∼-≈-bag ∼[] = refl-≈-bag  
lemma-∼-≈-bag (∼x {x} {xs} {ys} {xs'} {ys'} xs/x⟶xs' ys/x⟶ys' xs'∼ys') = begin
  xs ≈⟨ lemma-/-≈-bag xs/x⟶xs' ⟩
  x ∷ xs' ≈⟨ ∷-cong refl (lemma-∼-≈-bag xs'∼ys') ⟩
  x ∷ ys' ≈⟨ sym-≈-bag (lemma-/-≈-bag ys/x⟶ys') ⟩
  ys ∎
  
