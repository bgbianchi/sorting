module List.Permutation.Equivalence (A : Set) where

open import List.Permutation A
open import Data.List
open import Data.Product renaming (_×_ to _∧_)

lemma-refl∼ : {xs : List A} → xs ∼ xs
lemma-refl∼ {[]}     = ∼[] 
lemma-refl∼ {x ∷ xs} = ∼x /head /head lemma-refl∼

lemma-sym∼ : {xs ys : List A} → xs ∼ ys → ys ∼ xs
lemma-sym∼ ∼[] = ∼[] 
lemma-sym∼ (∼x xs/x⟶xs' ys/x⟶ys' xs'∼ys') = ∼x ys/x⟶ys' xs/x⟶xs' (lemma-sym∼ xs'∼ys')

lemma// : {x y : A}{xs ys zs : List A} → xs / x ⟶ ys → ys / y ⟶ zs → ∃ (λ ws → xs / y ⟶ ws ∧ ws / x ⟶ zs)
lemma//  (/head {x = x}) (/head {xs = xs}) = x ∷ xs , /tail /head , /head
lemma// (/head {x = x}) (/tail {x = u} {ys = us'} us/y⟶us') = x ∷ u ∷ us' , /tail (/tail us/y⟶us') , /head
lemma// (/tail {xs = us} us/x⟶us') /head = us , /head , us/x⟶us'
lemma// (/tail {x = u} us/x⟶us') (/tail us'/y⟶us'') 
    with lemma// us/x⟶us' us'/y⟶us''
... | ws' , us/y⟶ws' , ws'/x⟶us'' = u ∷ ws' , /tail us/y⟶ws' ,  /tail ws'/x⟶us''

lemma∼/∷ : {x : A}{xs ys : List A} → (x ∷ xs) ∼ ys → ∃ (λ ys' → ys / x ⟶ ys' ∧ xs ∼ ys')
lemma∼/∷  (∼x {ys' = vs'} /head ys/x⟶vs' xs∼vs') = vs' , ys/x⟶vs' , xs∼vs'
lemma∼/∷  (∼x (/tail xs/u⟶us') ys/u⟶vs' x∷us'∼vs') 
    with lemma∼/∷ x∷us'∼vs' 
... | _ , vs'/x⟶zs , us'∼zs 
    with lemma// ys/u⟶vs' vs'/x⟶zs
... | ws , ys/x⟶ws , ws/u⟶zs = ws , ys/x⟶ws , ∼x xs/u⟶us' ws/u⟶zs us'∼zs

lemma∼/ : {x : A}{xs xs' ys : List A} → xs ∼ ys → xs / x  ⟶ xs' → 
                   ∃ (λ ys' → ys / x ⟶ ys' ∧ xs' ∼ ys')
lemma∼/ u∷us∼ys /head = lemma∼/∷ u∷us∼ys
lemma∼/ u∷us∼ys (/tail us/x⟶xs') 
    with lemma∼/∷ u∷us∼ys 
... | _ , ys/u⟶ys' , us∼ys' 
    with lemma∼/ us∼ys' us/x⟶xs'
... | _ , ys'/x⟶vs , xs'∼vs 
    with lemma// ys/u⟶ys' ys'/x⟶vs
... | ws , ys/x⟶ws , ws/u⟶vs = ws , ys/x⟶ws , ∼x /head ws/u⟶vs xs'∼vs

lemma-trans∼ : {xs ys zs : List A} → xs ∼ ys → ys ∼ zs → xs ∼ zs
lemma-trans∼ ∼[] ∼[] = ∼[]
lemma-trans∼ ∼[] (∼x .{xs = []} () zs/x⟶zs' ys'∼zs') 
lemma-trans∼ {zs = zs} (∼x {ys = ys} xs/x⟶xs' ys/x⟶ys' xs'∼ys') ys∼zs 
    with lemma∼/ {xs = ys} ys∼zs ys/x⟶ys'
... | _ , zs/x⟶us , ys'∼us = ∼x xs/x⟶xs' zs/x⟶us (lemma-trans∼ xs'∼ys' ys'∼us)

