open import Relation.Binary.Core

module Order.Total  {A : Set}
                  (_≤_ : A → A → Set)
                  (tot≤ : Total _≤_)  where

open import Data.Sum

refl≤ : {x : A} → x ≤ x
refl≤ {x} 
    with tot≤ x x
... | inj₁ x≤x = x≤x
... | inj₂ x≤x = x≤x 
