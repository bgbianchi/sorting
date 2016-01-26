module BBHeap.Last {A : Set}(_≤_ : A → A → Set) where

open import BBHeap _≤_
open import BBHeap.Compound _≤_
open import BBHeap.DropLast _≤_
open import Bound.Lower A 
open import Data.Sum 

last : {b : Bound}(h : BBHeap b) → Compound h → A
last (left {b} {x} {l} {r} b≤x l⋘r) (cl .b≤x .l⋘r)
    with l | r | l⋘r | lemma-dropLast⋘ l⋘r
... | leaf | leaf | lf⋘ | _ = x
... | left x≤y₁ l₁⋘r₁ | left x≤y₂ l₂⋘r₂ | ll⋘ .x≤y₁ .x≤y₂ .l₁⋘r₁ .l₂⋘r₂ l₂≃r₂ r₁≃l₂ | inj₁ l≃r = last (left x≤y₂ l₂⋘r₂) (cl x≤y₂ l₂⋘r₂)
... | left x≤y₁ l₁⋘r₁ | left x≤y₂ l₂⋘r₂ | ll⋘ .x≤y₁ .x≤y₂ .l₁⋘r₁ .l₂⋘r₂ l₂≃r₂ r₁≃l₂ | inj₂ dl⋘r = last (left x≤y₁ l₁⋘r₁) (cl x≤y₁ l₁⋘r₁)
... | right x≤y₁ l₁⋙r₁ | left x≤y₂ l₂⋘r₂ | lr⋘ .x≤y₁ .x≤y₂ .l₁⋙r₁ .l₂⋘r₂ l₂≃r₂ l₁⋗l₂ | inj₁ ()
... | right x≤y₁ l₁⋙r₁ | left x≤y₂ l₂⋘r₂ | lr⋘ .x≤y₁ .x≤y₂ .l₁⋙r₁ .l₂⋘r₂ l₂≃r₂ l₁⋗l₂ | inj₂ dl⋘r = last (right x≤y₁ l₁⋙r₁) (cr x≤y₁ l₁⋙r₁)
last (right {b} {x} {l} {r} b≤x l⋙r) (cr .b≤x .l⋙r)
    with l | r | l⋙r | lemma-dropLast⋙ l⋙r
... | left x≤y lf⋘ | leaf | ⋙lf {x = y} .x≤y | _ = y
... | left x≤y₁ l₁⋘r₁ | left x≤y₂ l₂⋘r₂ | ⋙rl .x≤y₁ .x≤y₂ .l₁⋘r₁ l₁≃r₁ .l₂⋘r₂ l₁⋗r₂ | inj₁ l⋗r = last (left x≤y₁ l₁⋘r₁) (cl x≤y₁ l₁⋘r₁)
... | left x≤y₁ l₁⋘r₁ | left x≤y₂ l₂⋘r₂ | ⋙rl .x≤y₁ .x≤y₂ .l₁⋘r₁ l₁≃r₁ .l₂⋘r₂ l₁⋗r₂ | inj₂ l⋙dr = last (left x≤y₂ l₂⋘r₂) (cl x≤y₂ l₂⋘r₂)
... | left x≤y₁ l₁⋘r₁ | right x≤y₂ l₂⋙r₂ | ⋙rr .x≤y₁ .x≤y₂ .l₁⋘r₁ l₁≃r₁ .l₂⋙r₂ l₁≃l₂ | inj₁ ()
... | left x≤y₁ l₁⋘r₁ | right x≤y₂ l₂⋙r₂ | ⋙rr .x≤y₁ .x≤y₂ .l₁⋘r₁ l₁≃r₁ .l₂⋙r₂ l₁≃l₂ | inj₂ l⋙dr = last (right x≤y₂ l₂⋙r₂) (cr x≤y₂ l₂⋙r₂)
