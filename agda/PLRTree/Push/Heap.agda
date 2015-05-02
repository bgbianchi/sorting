open import Relation.Binary.Core

module PLRTree.Push.Heap {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) 
                     (trans≤ : Transitive _≤_) where

open import Data.Sum
open import Induction.WellFounded
open import Order.Total _≤_ tot≤
open import PLRTree {A} 
open import PLRTree.Drop _≤_ tot≤
open import PLRTree.Heap _≤_
open import PLRTree.Heap.Properties _≤_ trans≤
open import PLRTree.Order {A}
open import PLRTree.Order.Properties {A}

lemma-push-≤* : {x y : A}{l r : PLRTree}(t : Tag) → x ≤ y → x ≤* l → x ≤* r → (acc : Acc _≺_ (node t y l r)) → x ≤* (push (node t y l r) acc) 
lemma-push-≤* {x} t x≤y (lf≤* .x) x≤*r (acc rs) = nd≤* x≤y (lf≤* x) (lf≤* x)
lemma-push-≤* {x} {y} t x≤y (nd≤* {t'} .{x} {x'} x≤x' x≤*l' x≤*r') (lf≤* .x) (acc rs) 
    with tot≤ y x'
... | inj₁ y≤x' = nd≤* x≤y (nd≤* x≤x' (lf≤* x) (lf≤* x)) (lf≤* x)
... | inj₂ x'≤y = nd≤* x≤x' (nd≤* x≤y (lf≤* x) (lf≤* x)) (lf≤* x)
lemma-push-≤* {x} {y} t x≤y (nd≤* {t'} .{x} {x'} {l'} {r'} x≤x' x≤*l' x≤*r') (nd≤* {t''} .{x} {x''} {l''} {r''} x≤x'' x≤*l'' x≤*r'') (acc rs) 
    with tot≤ y x' | tot≤ y x'' | tot≤ x' x''
... | inj₁ y≤x' | inj₁ y≤x'' | _ = nd≤* x≤y (nd≤* x≤x' x≤*l' x≤*r') (nd≤* x≤x'' x≤*l'' x≤*r'')
... | inj₁ y≤x' | inj₂ x''≤y | _ rewrite lemma-≡-height t'' y x'' l'' r'' =  
           let acc-t''yl''r'' = rs (node t'' y l'' r'') (lemma-≺-right t y (node t' x' l' r') (node t'' x'' l'' r'')) 
           in nd≤* x≤x'' (nd≤* x≤x' x≤*l' x≤*r') (lemma-push-≤* t'' x≤y x≤*l'' x≤*r'' acc-t''yl''r'')
... | inj₂ x'≤y | inj₁ y≤x'' | _ rewrite lemma-≡-height t' y x' l' r' = 
           let acc-t'yl'r' = rs (node t' y l' r') (lemma-≺-left t y (node t' x' l' r') (node t'' x'' l'' r'')) 
           in nd≤* x≤x' (lemma-push-≤* t' x≤y x≤*l' x≤*r' acc-t'yl'r') (nd≤* x≤x'' x≤*l'' x≤*r'') 
... | inj₂ x'≤y | inj₂ x''≤y | inj₁ x'≤x'' rewrite lemma-≡-height t' y x' l' r' = 
           let acc-t'yl'r' = rs (node t' y l' r') (lemma-≺-left t y (node t' x' l' r') (node t'' x'' l'' r'')) 
           in nd≤* x≤x' (lemma-push-≤* t' x≤y x≤*l' x≤*r' acc-t'yl'r') (nd≤* x≤x'' x≤*l'' x≤*r'') 
... | inj₂ x'≤y | inj₂ x''≤y | inj₂ x''≤x' rewrite lemma-≡-height t'' y x'' l'' r'' =
           let acc-t''yl''r'' = rs (node t'' y l'' r'') (lemma-≺-right t y (node t' x' l' r') (node t'' x'' l'' r'')) 
           in nd≤* x≤x'' (nd≤* x≤x' x≤*l' x≤*r') (lemma-push-≤* t'' x≤y x≤*l'' x≤*r'' acc-t''yl''r'')

lemma-push-heap : {l r : PLRTree}(t : Tag)(x : A) → Heap l → Heap r → (acc : Acc _≺_ (node t x l r)) → Heap (push (node t x l r) acc)
lemma-push-heap t x leaf _ _ = node (lf≤* x) (lf≤* x) leaf leaf
lemma-push-heap t x (node {t'} {x'} x'≤*l' x'≤*r' hl' hr') leaf (acc rs) 
    with tot≤ x x'
... | inj₁ x≤x' = node (nd≤* x≤x' (lf≤* x) (lf≤* x)) (lf≤* x) (node (lf≤* x') (lf≤* x') leaf leaf) leaf 
... | inj₂ x'≤x = node (nd≤* x'≤x (lf≤* x') (lf≤* x')) (lf≤* x') (node (lf≤* x) (lf≤* x) leaf leaf) leaf 
lemma-push-heap t x (node {t'} {x'} {l'} {r'} x'≤*l' x'≤*r' hl' hr') (node {t''} {x''} {l''} {r''} x''≤*l'' x''≤*r'' hl'' hr'') (acc rs)
    with tot≤ x x' | tot≤ x x'' | tot≤ x' x''
... | inj₁ x≤x' | inj₁ x≤x'' | _ = 
           let x≤*t'x'l'r' = nd≤* x≤x' (lemma-≤-≤* x≤x' x'≤*l') (lemma-≤-≤* x≤x' x'≤*r') ; 
                x≤*t''x''l''r'' = nd≤* x≤x'' (lemma-≤-≤* x≤x'' x''≤*l'') (lemma-≤-≤* x≤x'' x''≤*r'')
           in node x≤*t'x'l'r' x≤*t''x''l''r'' (node x'≤*l' x'≤*r' hl' hr') (node x''≤*l'' x''≤*r'' hl'' hr'') 
... | inj₁ x≤x' | inj₂ x''≤x | _ rewrite lemma-≡-height t'' x x'' l'' r'' = 
           let acc-t''xl''r'' = rs (node t'' x l'' r'') (lemma-≺-right t x (node t' x' l' r') (node t'' x'' l'' r'')) ;
                x''≤*t'x'l'r' = lemma-≤-≤* x''≤x (nd≤* x≤x' (lemma-≤-≤* x≤x' x'≤*l') (lemma-≤-≤* x≤x' x'≤*r')) ;
                x''≤*push-t''xl''r'' = lemma-push-≤* t'' x''≤x x''≤*l'' x''≤*r'' acc-t''xl''r''
           in node x''≤*t'x'l'r' x''≤*push-t''xl''r'' (node x'≤*l' x'≤*r' hl' hr') (lemma-push-heap t'' x hl'' hr'' acc-t''xl''r'')
... | inj₂ x'≤x | inj₁ x≤x'' | _ rewrite lemma-≡-height t' x x' l' r' = 
           let acc-t'xl'r' = rs (node t' x l' r') (lemma-≺-left t x (node t' x' l' r') (node t'' x'' l'' r'')) ;
                x'≤*t''x''l''r'' = lemma-≤-≤* x'≤x (nd≤* x≤x'' (lemma-≤-≤* x≤x'' x''≤*l'') (lemma-≤-≤* x≤x'' x''≤*r'')) ;
                x'≤*push-t'xl'r' = lemma-push-≤* t' x'≤x x'≤*l' x'≤*r' acc-t'xl'r'
           in node x'≤*push-t'xl'r' x'≤*t''x''l''r'' (lemma-push-heap t' x hl' hr' acc-t'xl'r') (node x''≤*l'' x''≤*r'' hl'' hr'')
... | inj₂ x'≤x | inj₂ x''≤x | inj₁ x'≤x'' rewrite lemma-≡-height t' x x' l' r' = 
           let acc-t'xl'r' = rs (node t' x l' r') (lemma-≺-left t x (node t' x' l' r') (node t'' x'' l'' r'')) ;
                x'≤*t''x''l''r'' = lemma-≤-≤* x'≤x'' (nd≤* refl≤ x''≤*l'' x''≤*r'') ;
                x'≤*push-t'xl'r' = lemma-push-≤* t' x'≤x x'≤*l' x'≤*r' acc-t'xl'r'
           in node x'≤*push-t'xl'r' x'≤*t''x''l''r'' (lemma-push-heap t' x hl' hr' acc-t'xl'r') (node x''≤*l'' x''≤*r'' hl'' hr'')
... | inj₂ x'≤x | inj₂ x''≤x | inj₂ x''≤x' rewrite lemma-≡-height t'' x x'' l'' r'' =
           let acc-t''xl''r'' = rs (node t'' x l'' r'') (lemma-≺-right t x (node t' x' l' r') (node t'' x'' l'' r'')) ;
                x''≤*t'x'l'r' = lemma-≤-≤* x''≤x' (nd≤* refl≤ x'≤*l' x'≤*r') ;
                x''≤*push-t''xl''r'' = lemma-push-≤* t'' x''≤x x''≤*l'' x''≤*r'' acc-t''xl''r''
           in node x''≤*t'x'l'r' x''≤*push-t''xl''r'' (node x'≤*l' x'≤*r' hl' hr') (lemma-push-heap t'' x hl'' hr'' acc-t''xl''r'')
