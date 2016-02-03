module Nat.Sum where

open import Data.Nat 
open import Relation.Binary
open import Relation.Binary.PropositionalEquality 

open DecTotalOrder decTotalOrder hiding (refl)

+id : (n : ℕ) → n + zero ≡  n
+id zero = refl
+id (suc n) = cong suc (+id n)

+assoc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+assoc zero n = refl
+assoc (suc m) n = cong suc (+assoc m n)

