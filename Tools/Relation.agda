------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

module Tools.Relation where

open import Relation.Binary public
  using ( Rel; _Preserves₂_⟶_⟶_
        ; Decidable; Reflexive; Symmetric; Transitive; Antisymmetric
        ; DecSetoid; Poset; Preorder; Setoid
        ; IsEquivalence; IsPartialOrder; IsPreorder
        )
open import Relation.Nullary public
  using (¬_; Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable public
  using (decidable-stable)

open import Tools.Level
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

private variable
  a p r       : Level
  A           : Set _
  R R₁ R₂     : A → A → Set _
  x x′ y y′ z : A

-- If A and B are logically equivalent, then so are Dec A and Dec B.

map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → (B → A) → Dec A → Dec B
map f g (yes p) = yes (f p)
map f g (no ¬p) = no (λ x → ¬p (g x))

-- A variant of Dec.

Dec-∀ : {A : Set a} → (A → Set p) → A → Set (a ⊔ p)
Dec-∀ P x = P x ⊎ (∀ x → ¬ P x)

-- One can convert from Dec to Dec-∀.

Dec→Dec-∀ : Dec A → Dec-∀ (λ (_ : ⊤) → A) tt
Dec→Dec-∀ (yes a) = inj₁ a
Dec→Dec-∀ (no ¬A) = inj₂ (λ _ → ¬A)

-- A symmetric, transitive closure of the relation.

data Symmetric-transitive-closure {A : Set a} (R : A → A → Set r) :
       A → A → Set (a ⊔ r) where
  injˢᵗ   : R x y → Symmetric-transitive-closure R x y
  symˢᵗ   : Symmetric-transitive-closure R x y →
            Symmetric-transitive-closure R y x
  transˢᵗ : Symmetric-transitive-closure R x y →
            Symmetric-transitive-closure R y z →
            Symmetric-transitive-closure R x z

opaque

  -- An eliminator for Symmetric-transitive-closure.

  Symmetric-transitive-closure-elim :
    (∀ {x y} → R₂ x y → R₂ y x) →
    (∀ {x y z} → R₂ x y → R₂ y z → R₂ x z) →
    (∀ {x y} → R₁ x y → R₂ x y) →
    Symmetric-transitive-closure R₁ x y →
    R₂ x y
  Symmetric-transitive-closure-elim s t i = λ where
    (injˢᵗ x)       → i x
    (symˢᵗ c)       → s (Symmetric-transitive-closure-elim s t i c)
    (transˢᵗ c₁ c₂) →
      t (Symmetric-transitive-closure-elim s t i c₁)
        (Symmetric-transitive-closure-elim s t i c₂)

opaque

  -- A map function for Symmetric-transitive-closure.

  Symmetric-transitive-closure-map :
    (∀ {x y} → R₁ x y → R₂ x y) →
    Symmetric-transitive-closure R₁ x y →
    Symmetric-transitive-closure R₂ x y
  Symmetric-transitive-closure-map f =
    Symmetric-transitive-closure-elim symˢᵗ transˢᵗ (λ x → injˢᵗ (f x))

-- Some "cast" lemmas.

module
  Symmetric-transitive-closure-cast
    (l : ∀ {y} → R x y → R x′ y)
    (r : ∀ {y} → R y x → R y x′)
    where

  opaque mutual

    -- A cast lemma for Symmetric-transitive-closure.

    castˡ :
      Symmetric-transitive-closure R x y →
      Symmetric-transitive-closure R x′ y
    castˡ = λ where
      (injˢᵗ x)       → injˢᵗ (l x)
      (symˢᵗ c)       → symˢᵗ (castʳ c)
      (transˢᵗ c₁ c₂) → transˢᵗ (castˡ c₁) c₂

    -- A cast lemma for Symmetric-transitive-closure.

    castʳ :
      Symmetric-transitive-closure R y x →
      Symmetric-transitive-closure R y x′
    castʳ = λ where
      (injˢᵗ x)       → injˢᵗ (r x)
      (symˢᵗ c)       → symˢᵗ (castˡ c)
      (transˢᵗ c₁ c₂) → transˢᵗ c₁ (castʳ c₂)
