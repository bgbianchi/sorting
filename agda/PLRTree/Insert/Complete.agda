open import Relation.Binary.Core 

module PLRTree.Insert.Complete {A : Set} 
                     (_≤_ : A → A → Set)
                     (tot≤ : Total _≤_) where

open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_)
open import PLRTree {A} 
open import PLRTree.Compound {A} 
open import PLRTree.Insert _≤_ tot≤
open import PLRTree.Insert.Properties _≤_ tot≤
open import PLRTree.Complete {A}
open import PLRTree.Complete.Properties {A} 
open import PLRTree.Equality {A}
open import PLRTree.Equality.Properties {A}

lemma-≃-⊥ : {l : PLRTree}(x : A) → l ≃ insert x l → ⊥
lemma-≃-⊥ {leaf} _ ()
lemma-≃-⊥ {node perfect x' l' r'} x l≃lᵢ 
    with tot≤ x x' | l' | r' | l≃lᵢ
... | inj₁ x≤x' | leaf | leaf | ()
... | inj₁ x≤x' | leaf | node _ _ _ _ | () 
... | inj₁ x≤x' | node _ _ _ _ | leaf | ()
... | inj₁ x≤x' | node _ _ _ _ | node _ _ _ _ | ()
... | inj₂ x'≤x | leaf | leaf | () 
... | inj₂ x'≤x | leaf | node _ _ _ _ | () 
... | inj₂ x'≤x | node _ _ _ _ | leaf | () 
... | inj₂ x'≤x | node _ _ _ _ | node _ _ _ _ | () 
lemma-≃-⊥ {node left _ _ _} _ ()
lemma-≃-⊥ {node right _ _ _} _ ()

lemma-⋗-⊥ : {l : PLRTree}(x : A) → l ⋗ insert x l → ⊥
lemma-⋗-⊥ {leaf} _ ()
lemma-⋗-⊥ {node perfect x' l' r'} x l⋗lᵢ 
    with tot≤ x x' | l' | r' | l⋗lᵢ
... | inj₁ x≤x' | leaf | leaf | ()
... | inj₁ x≤x' | leaf | node _ _ _ _ | () 
... | inj₁ x≤x' | node _ _ _ _ | leaf | ()
... | inj₁ x≤x' | node _ _ _ _ | node _ _ _ _ | ()
... | inj₂ x'≤x | leaf | leaf | () 
... | inj₂ x'≤x | leaf | node _ _ _ _ | () 
... | inj₂ x'≤x | node _ _ _ _ | leaf | () 
... | inj₂ x'≤x | node _ _ _ _ | node _ _ _ _ | () 
lemma-⋗-⊥ {node left _ _ _} _ ()
lemma-⋗-⊥ {node right _ _ _} _ ()

lemma-⋙-⊥ : {l r : PLRTree}(x : A) → l ⋙ r → l ⋗ insert x r → ⊥
lemma-⋙-⊥ x (⋙p l⋗r) l⋗rᵢ = lemma-≃-⊥ x (lemma-⋗* l⋗r l⋗rᵢ)
lemma-⋙-⊥ x (⋙l {l' = l''} y' y'' l'≃r' l''⋘r'' l'⋗r'') l⋗rᵢ 
    with tot≤ x y''
... | inj₁ x≤y''
    with insert y'' l'' | lemma-insert-compound y'' l'' | l⋗rᵢ
... | node perfect _ _ _ | compound | () 
... | node left _ _ _ | compound | ()
... | node right _ _ _ | compound | ()
lemma-⋙-⊥ x (⋙l {l' = l''} y' y'' l'≃r' l''⋘r'' l'⋗r'') l⋗rᵢ | inj₂ y''≤x 
    with insert x l'' | lemma-insert-compound x l'' | l⋗rᵢ
... | node perfect _ _ _ | compound | ()
... | node left _ _ _ | compound | ()
... | node right _ _ _ | compound | ()
lemma-⋙-⊥ x (⋙r {r' = r''} y' y'' l'≃r' l''⋙r'' l'≃l'') l⋗rᵢ 
    with tot≤ x y''
... | inj₁ x≤y''
    with insert y'' r'' | lemma-insert-compound y'' r'' | l⋗rᵢ
... | node perfect _ _ _ | compound | ⋗nd .y' .x _ l''≃r''ᵢ l'⋗l'' = lemma-⋗refl-⊥ (lemma-⋗-≃ l'⋗l'' (symm≃ l'≃l'')) 
... | node left _ _ _ | compound | ()
... | node right _ _ _ | compound | ()
lemma-⋙-⊥ x (⋙r {r' = r''} y' y'' l'≃r' l''⋙r'' l'≃l'') l⋗rᵢ | inj₂ y''≤x 
    with insert x r'' | lemma-insert-compound x r'' | l⋗rᵢ
... | node perfect _ _ _ | compound | ⋗nd .y' .y'' _ l''≃r''ᵢ l'⋗l'' = lemma-⋗refl-⊥ (lemma-⋗-≃ l'⋗l'' (symm≃ l'≃l'')) 
... | node left _ _ _ | compound | ()
... | node right _ _ _ | compound | ()

lemma-⋘-⊥ : {l r : PLRTree}(x : A) → l ⋘ r → insert x l ≃ r → ⊥
lemma-⋘-⊥ x (p⋘ l≃r) lᵢ≃r = lemma-≃-⊥ x (trans≃ l≃r (symm≃ lᵢ≃r))
lemma-⋘-⊥ x (l⋘ {l = l'} y' y'' l'⋘r' l''≃r'' r'≃l'') lᵢ≃r 
    with tot≤ x y'
... | inj₁ x≤y'
    with insert y' l' | lemma-insert-compound y' l' | lᵢ≃r
... | node perfect _ _ _ | compound | () 
... | node left _ _ _ | compound | ()
... | node right _ _ _ | compound | ()
lemma-⋘-⊥ x (l⋘ {l = l'} y' y'' l'⋘r' l''≃r'' r'≃l'') lᵢ≃r | inj₂ y'≤x 
    with insert x l' | lemma-insert-compound x l' | lᵢ≃r
... | node perfect _ _ _ | compound | () 
... | node left _ _ _ | compound | ()
... | node right _ _ _ | compound | ()
lemma-⋘-⊥ x (r⋘ {r = r'} y' y'' l'⋙r' l''≃r'' l'⋗l'') lᵢ≃r 
    with tot≤ x y'
... | inj₁ x≤y'
    with insert y' r' | lemma-insert-compound y' r' | lᵢ≃r | lemma-⋙-⊥ y' l'⋙r'
... | node perfect _ _ _ | compound | ≃nd .x .y'' l'≃r'ᵢ _ l'≃l'' | lemma-⋙-⊥' = lemma-⋙-⊥' (lemma-⋗-≃ l'⋗l'' (trans≃ (symm≃ l'≃l'') l'≃r'ᵢ))
... | node left _ _ _ | compound | () | _
... | node right _ _ _ | compound | () | _
lemma-⋘-⊥ x (r⋘ {r = r'} y' y'' l'⋙r' l''≃r'' l'⋗l'') lᵢ≃r | inj₂ y'≤x 
    with insert x r' | lemma-insert-compound x r' | lᵢ≃r | lemma-⋙-⊥ x l'⋙r'
... | node perfect _ _ _ | compound | ≃nd .y' .y'' l'≃r'ᵢ _ l'≃l'' | lemma-⋙-⊥' = lemma-⋙-⊥' (lemma-⋗-≃ l'⋗l'' (trans≃ (symm≃ l'≃l'') l'≃r'ᵢ)) 
... | node left _ _ _ | compound | () | _
... | node right _ _ _ | compound | () | _

lemma-insert-≃ : {l r : PLRTree}{x : A} → Compound l → l ≃ r → insert x l ⋘ r
lemma-insert-≃ {node perfect y l r} {node perfect y' l' r'} {x} compound (≃nd .y .y' l≃r l'≃r' l≃l') 
    with tot≤ x y | l | r | l≃r | l' | l≃l'
... | inj₁ x≤y | leaf | leaf | ≃lf | leaf | ≃lf = r⋘ x y' (⋙p (⋗lf y)) l'≃r' (⋗lf y)
... | inj₁ x≤y | node perfect z₁ _ _ | node perfect z₂ _ _ | ≃nd .z₁ .z₂ l₁≃r₁ l₂≃r₂ l₁≃l₂ | node perfect z₃ _ _ | ≃nd .z₁ .z₃ _ l₃≃r₃ l₁≃l₃ 
                                           = l⋘ x y' (lemma-insert-≃ compound (≃nd z₁ z₂ l₁≃r₁ l₂≃r₂ l₁≃l₂)) l'≃r' (≃nd z₂ z₃ l₂≃r₂ l₃≃r₃ (trans≃ (symm≃ l₁≃l₂) l₁≃l₃))
... | inj₂ y≤x | leaf | leaf | ≃lf | leaf | ≃lf = r⋘ y y' (⋙p (⋗lf x)) l'≃r' (⋗lf x)
... | inj₂ y≤x |  node perfect z₁ _ _ | node perfect z₂ _ _ | ≃nd .z₁ .z₂ l₁≃r₁ l₂≃r₂ l₁≃l₂ | node perfect z₃ _ _ | ≃nd .z₁ .z₃ _ l₃≃r₃ l₁≃l₃ 
                                           = l⋘ y y' (lemma-insert-≃ compound (≃nd z₁ z₂ l₁≃r₁ l₂≃r₂ l₁≃l₂)) l'≃r' (≃nd z₂ z₃ l₂≃r₂ l₃≃r₃ (trans≃ (symm≃ l₁≃l₂) l₁≃l₃))

lemma-insert-⋗' : {l r : PLRTree}(x : A) → l ⋗ r → Compound r → l ⋙ (insert x r) 
lemma-insert-⋗' x (⋗nd {l} {r} {l'} {r'} y y' l≃r l'≃r' l⋗l') compound
    with tot≤ x y' | l' | r' | l'≃r' | l | l⋗l' 
... | inj₁ x≤y' | leaf | leaf | ≃lf | node perfect x₁ leaf leaf | ⋗lf .x₁ = ⋙r y x l≃r (⋙p (⋗lf y')) (≃nd x₁ y' ≃lf ≃lf ≃lf)
... | inj₁ x≤y' | node perfect x₃ l₃ r₃ | node perfect x₄ l₄ r₄ | ≃nd .x₃ .x₄ l₃≃r₃ l₄≃r₄ l₃≃l₄ | node perfect x₁ l₁ r₁ | ⋗nd .x₁ .x₃ l₁≃r₁ _ l₁⋗l₃ 
    with tot≤ y' x₃ | l₃ | r₃ | l₃≃r₃ | l₁ | l₁⋗l₃
... | inj₁ y'≤x₃ | leaf | leaf | ≃lf | node perfect x'₁ leaf leaf | ⋗lf .x'₁ 
    with l₄ | l₃≃l₄
... | leaf | ≃lf = 
                let _l'ᵢ⋘r' = r⋘ y' x₄ (⋙p (⋗lf x₃)) l₄≃r₄ (⋗lf x₃) ;
                     _l⋗r' = lemma-⋗-≃ (⋗nd x₁ y' l₁≃r₁ ≃lf (⋗lf x'₁)) (≃nd y' x₄ ≃lf l₄≃r₄ ≃lf)
                in ⋙l y x l≃r _l'ᵢ⋘r' _l⋗r' 
lemma-insert-⋗' x (⋗nd y y' l≃r _ _) compound | inj₁ x≤y' | node perfect x₃ _ _ | node perfect x₄ _ _ | ≃nd .x₃ .x₄ _ l₄≃r₄ l₃≃l₄ | node perfect x₁ _ _ | ⋗nd .x₁ .x₃ l₁≃r₁ _ _ | inj₁ y'≤x₃ | node perfect x'₅ _ _ | node perfect x'₆ _ _ | ≃nd .x'₅ .x'₆  l'₅≃r'₅ l'₆≃r'₆ l'₅≃l'₆ | node perfect x'₁ _ _ | ⋗nd .x'₁ .x'₅ l'₁≃r'₁ _ l'₁⋗l'₅ = 
                let _l₁⋗l₃ = ⋗nd x'₁ x'₅ l'₁≃r'₁ l'₅≃r'₅ l'₁⋗l'₅ ;
                     _l₃≃r₃ = ≃nd x'₅ x'₆ l'₅≃r'₅ l'₆≃r'₆ l'₅≃l'₆ ;
                     _l₃ᵢ⋘r₃ = lemma-⋙-⋗ (lemma-insert-⋗' x₃  _l₁⋗l₃ compound) (lemma-⋗-≃ _l₁⋗l₃ _l₃≃r₃) ;
                     _l'ᵢ⋘r' = l⋘ y' x₄ _l₃ᵢ⋘r₃  l₄≃r₄ (trans≃ (symm≃ _l₃≃r₃) l₃≃l₄) ;
                     _l⋗r' = lemma-⋗-≃ (⋗nd x₁ x₃ l₁≃r₁ _l₃≃r₃ _l₁⋗l₃) (≃nd x₃ x₄ _l₃≃r₃ l₄≃r₄ l₃≃l₄)
                in ⋙l y x l≃r _l'ᵢ⋘r' _l⋗r'
lemma-insert-⋗' x (⋗nd y y' l≃r _ _) compound | inj₁ x≤y' | node perfect x₃ _ _ | node perfect x₄ l₄ _ | ≃nd .x₃ .x₄ _ l₄≃r₄ l₃≃l₄ | node perfect x₁ _ _ | ⋗nd .x₁ .x₃ l₁≃r₁ _ l₁⋗l₃ | inj₂ x₃≤y' | leaf | leaf | ≃lf | node perfect x'₁ leaf leaf | ⋗lf .x'₁
    with l₄ | l₃≃l₄
... | leaf | ≃lf = 
                let _l'ᵢ⋘r' = r⋘ x₃ x₄ (⋙p (⋗lf y')) l₄≃r₄ (⋗lf y') ;
                     _l⋗r' = lemma-⋗-≃ (⋗nd x₁ x₃ l₁≃r₁ ≃lf (⋗lf x'₁)) (≃nd x₃ x₄ ≃lf l₄≃r₄ ≃lf)
                in ⋙l y x l≃r _l'ᵢ⋘r' _l⋗r' 
lemma-insert-⋗' x (⋗nd y y' l≃r _ _) compound | inj₁ x≤y' | node perfect x₃ _ _ | node perfect x₄ _ _ | ≃nd .x₃ .x₄ l₃≃r₃ l₄≃r₄ l₃≃l₄ | node perfect x₁ _ _ | ⋗nd .x₁ .x₃ l₁≃r₁ _ l₁⋗l₃ | inj₂ x₃≤y' | node perfect x'₅ _ _ | node perfect x'₆ _ _ | ≃nd .x'₅ .x'₆ l'₅≃r'₅ l'₆≃r'₆ l'₅≃l'₆ | node perfect x'₁ _ _ | ⋗nd .x'₁ .x'₅ l'₁≃r'₁ _ l'₁⋗l'₅ = 
                let _l₁⋗l₃ = ⋗nd x'₁ x'₅ l'₁≃r'₁ l'₅≃r'₅ l'₁⋗l'₅ ;
                     _l₃≃r₃ = ≃nd x'₅ x'₆ l'₅≃r'₅ l'₆≃r'₆ l'₅≃l'₆ ;
                     _l₃ᵢ⋘r₃ = lemma-⋙-⋗ (lemma-insert-⋗' y'  _l₁⋗l₃ compound) (lemma-⋗-≃ _l₁⋗l₃ _l₃≃r₃) ;
                     _l'ᵢ⋘r' = l⋘ x₃ x₄ _l₃ᵢ⋘r₃  l₄≃r₄ (trans≃ (symm≃ _l₃≃r₃) l₃≃l₄) ;
                     _l⋗r' = lemma-⋗-≃ (⋗nd x₁ x₃ l₁≃r₁ _l₃≃r₃ _l₁⋗l₃) (≃nd x₃ x₄ _l₃≃r₃ l₄≃r₄ l₃≃l₄)
                in ⋙l y x l≃r _l'ᵢ⋘r' _l⋗r'
lemma-insert-⋗' x (⋗nd y y' l≃r l'≃r' l⋗l') compound | inj₂ y'≤x | leaf | leaf | ≃lf | node perfect x₁ leaf leaf | ⋗lf .x₁ = ⋙r y y' l≃r (⋙p (⋗lf x)) (≃nd x₁ x ≃lf ≃lf ≃lf)
lemma-insert-⋗' x (⋗nd y y' l≃r _ _) compound | inj₂ y'≤x | node perfect x₃ l₃ r₃ | node perfect x₄ l₄ _ | ≃nd .x₃ .x₄ l₃≃r₃ l₄≃r₄ l₃≃l₄ | node perfect x₁ l₁ _ | ⋗nd .x₁ .x₃ l₁≃r₁ _ l₁⋗l₃ 
    with tot≤ x x₃ | l₃ | r₃ | l₃≃r₃ | l₁ | l₁⋗l₃
... | inj₁ x≤x₃ | leaf | leaf | ≃lf | node perfect x'₁ leaf leaf | ⋗lf .x'₁ 
    with l₄ | l₃≃l₄
... | leaf | ≃lf = 
                let _l'ᵢ⋘r' = r⋘ x x₄ (⋙p (⋗lf x₃)) l₄≃r₄ (⋗lf x₃) ;
                     _l⋗r' = lemma-⋗-≃ (⋗nd x₁ x l₁≃r₁ ≃lf (⋗lf x'₁)) (≃nd x x₄ ≃lf l₄≃r₄ ≃lf)
                in ⋙l y y' l≃r _l'ᵢ⋘r' _l⋗r' 
lemma-insert-⋗' x (⋗nd y y' l≃r _ _) compound | inj₂ y'≤x | node perfect x₃ _ _ | node perfect x₄ _ _ | ≃nd .x₃ .x₄ _ l₄≃r₄ l₃≃l₄ | node perfect x₁ _ _ | ⋗nd .x₁ .x₃ l₁≃r₁ _ _ | inj₁ x≤x₃ | node perfect x'₅ _ _ | node perfect x'₆ _ _ | ≃nd .x'₅ .x'₆  l'₅≃r'₅ l'₆≃r'₆ l'₅≃l'₆ | node perfect x'₁ _ _ | ⋗nd .x'₁ .x'₅ l'₁≃r'₁ _ l'₁⋗l'₅ = 
                let _l₁⋗l₃ = ⋗nd x'₁ x'₅ l'₁≃r'₁ l'₅≃r'₅ l'₁⋗l'₅ ;
                     _l₃≃r₃ = ≃nd x'₅ x'₆ l'₅≃r'₅ l'₆≃r'₆ l'₅≃l'₆ ;
                     _l₃ᵢ⋘r₃ = lemma-⋙-⋗ (lemma-insert-⋗' x₃  _l₁⋗l₃ compound) (lemma-⋗-≃ _l₁⋗l₃ _l₃≃r₃) ;
                     _l'ᵢ⋘r' = l⋘ x x₄ _l₃ᵢ⋘r₃ l₄≃r₄ (trans≃ (symm≃ _l₃≃r₃) l₃≃l₄) ;
                     _l⋗r' = lemma-⋗-≃ (⋗nd x₁ x₃ l₁≃r₁ _l₃≃r₃ _l₁⋗l₃) (≃nd x₃ x₄ _l₃≃r₃ l₄≃r₄ l₃≃l₄) 
                in ⋙l y y' l≃r _l'ᵢ⋘r' _l⋗r'
lemma-insert-⋗' x (⋗nd y y' l≃r _ _) compound | inj₂ y'≤x | node perfect x₃ _ _ | node perfect x₄ l₄ _ | ≃nd .x₃ .x₄ _ l₄≃r₄ l₃≃l₄ | node perfect x₁ _ _ | ⋗nd .x₁ .x₃ l₁≃r₁ _ _ | inj₂ x₃≤x | leaf | leaf | ≃lf | node perfect x'₁ leaf leaf | ⋗lf .x'₁
    with l₄ | l₃≃l₄
... | leaf | ≃lf = 
                let _l'ᵢ⋘r' = r⋘ x₃ x₄ (⋙p (⋗lf x)) l₄≃r₄ (⋗lf x) ;
                     _l⋗r' = lemma-⋗-≃ (⋗nd x₁ x₃ l₁≃r₁ ≃lf (⋗lf x'₁)) (≃nd x₃ x₄ ≃lf l₄≃r₄ ≃lf)
                in ⋙l y y' l≃r _l'ᵢ⋘r' _l⋗r' 
lemma-insert-⋗' x (⋗nd y y' l≃r _ _) compound | inj₂ y'≤x | node perfect x₃ _ _ | node perfect x₄ _ _ | ≃nd .x₃ .x₄ _ l₄≃r₄ l₃≃l₄ | node perfect x₁ _ _ | ⋗nd .x₁ .x₃ l₁≃r₁ _ _ | inj₂ x₃≤x | node perfect x'₅ _ _ | node perfect x'₆ _ _ | ≃nd .x'₅ .x'₆ l'₅≃r'₅ l'₆≃r'₆ l'₅≃l'₆ | node perfect x'₁ _ _ | ⋗nd .x'₁ .x'₅ l'₁≃r'₁ _ l'₁⋗l'₅ = 
                let _l₁⋗l₃ = ⋗nd x'₁ x'₅ l'₁≃r'₁ l'₅≃r'₅ l'₁⋗l'₅ ;
                     _l₃≃r₃ = ≃nd x'₅ x'₆ l'₅≃r'₅ l'₆≃r'₆ l'₅≃l'₆ ;
                     _l₃ᵢ⋘r₃ = lemma-⋙-⋗ (lemma-insert-⋗' x  _l₁⋗l₃ compound) (lemma-⋗-≃ _l₁⋗l₃ _l₃≃r₃) ;
                     _l'ᵢ⋘r' = l⋘ x₃ x₄ _l₃ᵢ⋘r₃  l₄≃r₄ (trans≃ (symm≃ _l₃≃r₃) l₃≃l₄) ;
                     _l⋗r' = lemma-⋗-≃ (⋗nd x₁ x₃ l₁≃r₁ _l₃≃r₃ _l₁⋗l₃) (≃nd x₃ x₄ _l₃≃r₃ l₄≃r₄ l₃≃l₄)
                in ⋙l y y' l≃r _l'ᵢ⋘r' _l⋗r'

lemma-insert-⋗ : {l r : PLRTree}(x : A) → l ⋗ r → l ⋙ (insert x r) ∨ l ≃ (insert x r)
lemma-insert-⋗ x (⋗lf y) = inj₂ (≃nd y x ≃lf ≃lf ≃lf)
lemma-insert-⋗ x (⋗nd y y' l≃r l'≃r' l⋗l') = inj₁ (lemma-insert-⋗' x (⋗nd y y' l≃r l'≃r' l⋗l') compound)

mutual
  lemma-insert-⋘ : {l r : PLRTree}(x : A) → l ⋘ r → (insert x l) ⋘ r ∨ (insert x l) ⋗ r
  lemma-insert-⋘ x (p⋘ ≃lf) = inj₂ (⋗lf x)
  lemma-insert-⋘ x (p⋘ (≃nd y y' l≃r l'≃r' l≃l')) = inj₁ (lemma-insert-≃ compound (≃nd y y' l≃r l'≃r' l≃l'))
  lemma-insert-⋘ x (l⋘ {l = l} y y' l⋘r l'≃r' r≃l') 
      with tot≤ x y
  ... | inj₁ x≤y 
      with insert y l | lemma-insert-compound y l | lemma-insert-⋘ y l⋘r |  lemma-⋘-⊥ y l⋘r
  ... | node left _ _ _ | compound | inj₁ lᵢ⋘r | _ = inj₁ (l⋘ x y' lᵢ⋘r l'≃r' r≃l')
  ... | node left _ _ _ | compound | inj₂ () | _ 
  ... | node right _ _ _ | compound | inj₁ lᵢ⋙r | _ = inj₁ (l⋘ x y' lᵢ⋙r l'≃r' r≃l')
  ... | node right _ _ _ | compound | inj₂ () | _
  ... | node perfect _ _ _ | compound | inj₂ lᵢ⋗r | _ = inj₁ (r⋘ x y' (⋙p lᵢ⋗r) l'≃r' (lemma-⋗-≃ lᵢ⋗r r≃l'))
  ... | node perfect _ _ _ | compound | inj₁ (p⋘ lᵢ≃r) | lemma-⋘-⊥'
      with lemma-⋘-⊥' lᵢ≃r 
  ... | ()
  lemma-insert-⋘ x (l⋘ {l = l} y y' l⋘r l'≃r' r≃l') | inj₂ y≤x 
      with insert x l | lemma-insert-compound x l | lemma-insert-⋘ x l⋘r |  lemma-⋘-⊥ x l⋘r
  ... | node left _ _ _ | compound | inj₁ lᵢ⋘r | _ = inj₁ (l⋘ y y' lᵢ⋘r l'≃r' r≃l')
  ... | node left _ _ _ | compound | inj₂ () | _ 
  ... | node right _ _ _ | compound | inj₁ lᵢ⋘r | _ = inj₁ (l⋘ y y' lᵢ⋘r l'≃r' r≃l')
  ... | node right _ _ _ | compound | inj₂ () | _
  ... | node perfect _ _ _ | compound | inj₂ lᵢ⋗r | _ = inj₁ (r⋘ y y' (⋙p lᵢ⋗r) l'≃r' (lemma-⋗-≃ lᵢ⋗r r≃l'))
  ... | node perfect _ _ _ | compound | inj₁ (p⋘ lᵢ≃r) | lemma-⋘-⊥'
      with lemma-⋘-⊥' lᵢ≃r 
  ... | ()
  lemma-insert-⋘ x (r⋘ {r = r} y y' l⋙r l'≃r' l⋗l') 
      with tot≤ x y
  ... | inj₁ x≤y 
      with insert y r | lemma-insert-compound y r | lemma-insert-⋙ y l⋙r |  lemma-⋙-⊥ y l⋙r
  ... | node left _ _ _ | compound | inj₁ l⋙rᵢ | _ = inj₁ (r⋘ x y' l⋙rᵢ l'≃r' l⋗l')
  ... | node left _ _ _ | compound | inj₂ () | _ 
  ... | node right _ _ _ | compound | inj₁ l⋙rᵢ | _ = inj₁ (r⋘ x y' l⋙rᵢ l'≃r' l⋗l')
  ... | node right _ _ _ | compound | inj₂ () | _
  ... | node perfect _ _ _ | compound | inj₂ l≃rᵢ | _ = inj₂ (⋗nd x y' l≃rᵢ l'≃r' l⋗l')
  ... | node perfect _ _ _ | compound | inj₁ (⋙p l⋗rᵢ) | lemma-⋙-⊥'
      with lemma-⋙-⊥' l⋗rᵢ 
  ... | ()
  lemma-insert-⋘ x (r⋘ {r = r} y y' l⋙r l'≃r' l⋗l') | inj₂ y'≤x 
      with insert x r | lemma-insert-compound x r | lemma-insert-⋙ x l⋙r |  lemma-⋙-⊥ x l⋙r
  ... | node left _ _ _ | compound | inj₁ l⋙rᵢ | _ = inj₁ (r⋘ y y' l⋙rᵢ l'≃r' l⋗l')
  ... | node left _ _ _ | compound | inj₂ () | _ 
  ... | node right _ _ _ | compound | inj₁ l⋙rᵢ | _ = inj₁ (r⋘ y y' l⋙rᵢ l'≃r' l⋗l')
  ... | node right _ _ _ | compound | inj₂ () | _
  ... | node perfect _ _ _ | compound | inj₂ l≃rᵢ | _ = inj₂ (⋗nd y y' l≃rᵢ l'≃r' l⋗l')
  ... | node perfect _ _ _ | compound | inj₁ (⋙p l⋗rᵢ) | lemma-⋙-⊥'
      with lemma-⋙-⊥' l⋗rᵢ 
  ... | ()

  lemma-insert-⋙ : {l r : PLRTree}(x : A) → l ⋙ r → l ⋙ (insert x r) ∨ l ≃ (insert x r)
  lemma-insert-⋙ x (⋙p l⋗r) = lemma-insert-⋗ x l⋗r
  lemma-insert-⋙ x (⋙l {l' = l'} y y' l≃r l'⋘r' l⋗r') 
      with tot≤ x y'
  ... | inj₁ x≤y' 
      with insert y' l' | lemma-insert-compound y' l' | lemma-insert-⋘ y' l'⋘r' |  lemma-⋘-⊥ y' l'⋘r'
  ... | node left _ _ _ | compound | inj₁ l'ᵢ⋘r' | _ = inj₁ (⋙l y x l≃r l'ᵢ⋘r' l⋗r')
  ... | node left _ _ _ | compound | inj₂ () | _ 
  ... | node right _ _ _ | compound | inj₁ l'ᵢ⋙r' | _ = inj₁ (⋙l y x l≃r l'ᵢ⋙r' l⋗r')
  ... | node right _ _ _ | compound | inj₂ () | _
  ... | node perfect _ _ _ | compound | inj₂ l'ᵢ⋗r' | _ = inj₁ (⋙r y x l≃r (⋙p l'ᵢ⋗r') (lemma-*⋗ l⋗r' l'ᵢ⋗r'))
  ... | node perfect _ _ _ | compound | inj₁ (p⋘ l'ᵢ≃r') | lemma-⋘-⊥'
      with lemma-⋘-⊥' l'ᵢ≃r' 
  ... | ()
  lemma-insert-⋙ x (⋙l {l' = l'} y y' l≃r l'⋘r' l⋗r') | inj₂ y'≤x 
      with insert x l' | lemma-insert-compound x l' | lemma-insert-⋘ x l'⋘r' | lemma-⋘-⊥ x l'⋘r'
  ... | node left _ _ _ | compound | inj₁ l'ᵢ⋘r' | _ = inj₁ (⋙l y y' l≃r l'ᵢ⋘r' l⋗r')
  ... | node left _ _ _ | compound | inj₂ () | _ 
  ... | node right _ _ _ | compound | inj₁ l'ᵢ⋘r' | _ = inj₁ (⋙l y y' l≃r l'ᵢ⋘r' l⋗r')
  ... | node right _ _ _ | compound | inj₂ () | _
  ... | node perfect _ _ _ | compound | inj₂ l'ᵢ⋗r' | _ = inj₁ (⋙r y y' l≃r (⋙p l'ᵢ⋗r') (lemma-*⋗ l⋗r' l'ᵢ⋗r'))
  ... | node perfect _ _ _ | compound | inj₁ (p⋘ l'ᵢ≃r') | lemma-⋘-⊥'
      with lemma-⋘-⊥' l'ᵢ≃r' 
  ... | ()
  lemma-insert-⋙ x (⋙r {r' = r'} y y' l≃r l'⋙r' l≃l') 
      with tot≤ x y'
  ... | inj₁ x≤y' 
      with insert y' r' | lemma-insert-compound y' r' | lemma-insert-⋙ y' l'⋙r' |  lemma-⋙-⊥ y' l'⋙r'
  ... | node left _ _ _ | compound | inj₁ l'⋙r'ᵢ | _ = inj₁ (⋙r y x l≃r l'⋙r'ᵢ l≃l')
  ... | node left _ _ _ | compound | inj₂ () | _ 
  ... | node right _ _ _ | compound | inj₁ l'⋙r'ᵢ | _ = inj₁ (⋙r y x l≃r l'⋙r'ᵢ l≃l')
  ... | node right _ _ _ | compound | inj₂ () | _
  ... | node perfect _ _ _ | compound | inj₂ l'≃r'ᵢ | _ = inj₂ (≃nd y x l≃r l'≃r'ᵢ l≃l') 
  ... | node perfect _ _ _ | compound | inj₁ (⋙p l'⋗r'ᵢ) | lemma-⋙-⊥'
      with lemma-⋙-⊥' l'⋗r'ᵢ 
  ... | ()
  lemma-insert-⋙ x (⋙r {r' = r'} y y' l≃r l'⋙r' l≃l') | inj₂ y'≤x 
      with insert x r' | lemma-insert-compound x r' | lemma-insert-⋙ x l'⋙r' |  lemma-⋙-⊥ x l'⋙r'
  ... | node left _ _ _ | compound | inj₁ l'⋙r'ᵢ | _ = inj₁ (⋙r y y' l≃r l'⋙r'ᵢ l≃l')
  ... | node left _ _ _ | compound | inj₂ () | _ 
  ... | node right _ _ _ | compound | inj₁ l'⋙r'ᵢ | _ = inj₁ (⋙r y y' l≃r l'⋙r'ᵢ l≃l')
  ... | node right _ _ _ | compound | inj₂ () | _
  ... | node perfect _ _ _ | compound | inj₂ l'≃r'ᵢ | _ = inj₂ (≃nd y y' l≃r l'≃r'ᵢ l≃l') 
  ... | node perfect _ _ _ | compound | inj₁ (⋙p l'⋗r'ᵢ) | lemma-⋙-⊥'
      with lemma-⋙-⊥' l'⋗r'ᵢ 
  ... | ()

lemma-insert-complete : {t : PLRTree}(x : A) → Complete t → Complete (insert x t)
lemma-insert-complete x leaf = perfect x leaf leaf ≃lf
lemma-insert-complete x (perfect {l} {r} y cl cr l≃r) 
    with tot≤ x y | l | r | l≃r | lemma-insert-complete y cl | lemma-insert-complete x cl
... | inj₁ x≤y | leaf | leaf | ≃lf | _ | _ = right x (perfect y cr cr ≃lf) cr (⋙p (⋗lf y))
... | inj₁ x≤y | node perfect z' _ _ | node perfect z'' _ _ | ≃nd .z' .z'' l'≃r' l''≃r'' l'≃l'' | clᵢ | _ = left x clᵢ cr (lemma-insert-≃ compound (≃nd z' z'' l'≃r' l''≃r'' l'≃l''))
... | inj₂ y≤x | leaf | leaf | ≃lf | _ | _ = right y (perfect x cr cr ≃lf) cr (⋙p (⋗lf x))
... | inj₂ y≤x | node perfect z' _ _ | node perfect z'' _ _ | ≃nd .z' .z'' l'≃r' l''≃r'' l'≃l'' | _ | clᵢ = left y clᵢ cr (lemma-insert-≃ compound (≃nd z' z'' l'≃r' l''≃r'' l'≃l''))
lemma-insert-complete x (left {l} {r} y cl cr l⋘r)  
    with tot≤ x y 
... | inj₁ x≤y 
    with insert y l | lemma-insert-complete y cl | lemma-insert-⋘ y l⋘r | lemma-insert-compound y l | lemma-⋘-⊥ y l⋘r
... | node left _ _ _ | clᵢ | inj₁ lᵢ⋘r | compound | _ = left x clᵢ cr lᵢ⋘r
... | node right _ _ _ | clᵢ | inj₁ lᵢ⋘r | compound | _ = left x clᵢ cr lᵢ⋘r
... | node left _ _ _ | _ | inj₂ () | compound | _
... | node right _ _ _ | _ | inj₂ () | compound | _ 
... | node perfect _ _ _ | clᵢ | inj₂ lᵢ⋗r | compound | _ = right x clᵢ cr (⋙p lᵢ⋗r) 
... | node perfect x' l' r' | perfect .x' cl' cr' l'≃r' | inj₁ (p⋘ lᵢ≃r) | compound | lemma-⋘-⊥'
    with lemma-⋘-⊥' lᵢ≃r
... | ()
lemma-insert-complete x (left {l} {r} y cl cr l⋘r) | inj₂ y≤x
    with insert x l |  lemma-insert-complete x cl | lemma-insert-⋘ x l⋘r | lemma-insert-compound x l | lemma-⋘-⊥ x l⋘r
... | node left _ _ _ | clᵢ | inj₁ lᵢ⋘r | compound | _ = left y clᵢ cr lᵢ⋘r
... | node right _ _ _ | clᵢ | inj₁ lᵢ⋘r | compound | _ = left y clᵢ cr lᵢ⋘r
... | node left _ _ _ | _ | inj₂ () | compound | _
... | node right _ _ _ | _ | inj₂ () | compound | _
... | node perfect _ _ _ | clᵢ | inj₂ lᵢ⋗r | compound | _ = right y clᵢ cr (⋙p lᵢ⋗r) 
... | node perfect x' l' r' | perfect .x' cl' cr' l'≃r' | inj₁ (p⋘ lᵢ≃r) | compound | lemma-⋘-⊥'
    with lemma-⋘-⊥' lᵢ≃r
... | ()
lemma-insert-complete x (right {l} {r} y cl cr l⋙r)  
    with tot≤ x y 
... | inj₁ x≤y 
    with insert y r | lemma-insert-complete y cr | lemma-insert-⋙ y l⋙r | lemma-insert-compound y r | lemma-⋙-⊥ y l⋙r
... | node left _ _ _ | crᵢ | inj₁ l⋙rᵢ | compound | _ = right x cl crᵢ l⋙rᵢ
... | node right _ _ _ | crᵢ | inj₁ l⋙rᵢ | compound | _ = right x cl crᵢ l⋙rᵢ
... | node left _ _ _ | _ | inj₂ () | compound | _
... | node right _ _ _ | _ | inj₂ () | compound | _ 
... | node perfect _ _ _ | crᵢ | inj₂ l≃rᵢ | compound | _ = perfect x cl crᵢ l≃rᵢ
... | node perfect x'' l'' r'' | perfect .x'' cl'' cr'' l''≃r'' | inj₁ (⋙p l⋗rᵢ) | compound |  lemma-⋙-⊥'
    with lemma-⋙-⊥' l⋗rᵢ
... | ()
lemma-insert-complete x (right {l} {r} y cl cr l⋙r) | inj₂ y≤x
    with insert x r |  lemma-insert-complete x cr | lemma-insert-⋙ x l⋙r | lemma-insert-compound x r | lemma-⋙-⊥ x l⋙r
... | node left _ _ _ | crᵢ | inj₁ l⋙rᵢ | compound | _ = right y cl crᵢ l⋙rᵢ
... | node right _ _ _ | crᵢ | inj₁ l⋙rᵢ | compound | _ = right y cl crᵢ l⋙rᵢ
... | node left _ _ _ | _ | inj₂ () | compound | _ 
... | node right _ _ _ | _ | inj₂ () | compound | _ 
... | node perfect _ _ _ | crᵢ | inj₂ l≃rᵢ | compound | _ = perfect y cl crᵢ l≃rᵢ
... | node perfect x'' l'' r'' | perfect .x'' cl'' cr'' l''≃r'' | inj₁ (⋙p l⋗rᵢ) | compound | lemma-⋙-⊥'
    with lemma-⋙-⊥' l⋗rᵢ
... | ()

