module List.Order.Bounded {A : Set}(_≤_ : A → A → Set)  where

open import Bound.Total A
open import Bound.Total.Order _≤_
open import Data.List

data _≤*_ : List A → Bound → Set where
  lenx : {t : Bound} → [] ≤* t
  lecx : {t : Bound}{x : A}{xs : List A} → LeB (val x) t → xs ≤* t → (x ∷ xs) ≤* t

data _*≤_ : Bound → List A → Set where
  genx : {b : Bound} → b *≤ []
  gecx : {b : Bound}{x : A}{xs : List A} → LeB b (val x) → b *≤ xs → b *≤ (x ∷ xs)
