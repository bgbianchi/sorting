{-# OPTIONS --sized-types #-}
module SOList.Total {A : Set}(_≤_ : A → A → Set)  where

open import Bound.Total A
open import Bound.Total.Order _≤_ 
open import Data.List
open import Size

data SOList : {ι : Size} → Bound → Bound → Set where
  onil : {ι : Size}{b t : Bound} 
                   → LeB b t 
                   → SOList {↑ ι} b t
  ocons : {ι : Size}{b t : Bound}(x : A) 
                   → SOList {ι} b (val x) 
                   → SOList {ι} (val x) t 
                   → SOList {↑ ι} b t

forget : {b t : Bound} → SOList b t → List A
forget (onil _) = []
forget (ocons x xs ys) = forget xs ++ (x ∷ forget ys)




