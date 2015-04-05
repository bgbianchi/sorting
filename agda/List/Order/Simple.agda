module List.Order.Simple {A : Set}(_≤_ : A → A → Set) where

open import Data.List

data _*≤_ : List A → A → Set where
  lenx : {x : A} 
                   → [] *≤ x 
  lecx : {x y : A}{ys : List A} 
                   → y ≤ x 
                   → ys *≤ x 
                   → (y ∷ ys) *≤ x

data _≤*_ : A → List A → Set where
  genx : {x : A} 
                   → x ≤* [] 
  gecx : {x y : A}{ys : List A} 
                   → x ≤ y 
                   → x ≤* ys 
                   → x ≤* (y ∷ ys)



