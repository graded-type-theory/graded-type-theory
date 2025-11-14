------------------------------------------------------------------------
-- Relations
------------------------------------------------------------------------

module Tools.Relation where

open import Relation.Binary public
  using ( Rel; _Preserves₂_⟶_⟶_
        ; Decidable; Reflexive; Symmetric; Transitive
        ; DecSetoid; Poset; Preorder; Setoid
        ; IsEquivalence; IsPartialOrder; IsPreorder
        )
open import Relation.Nullary public
  using (¬_; Dec; yes; no; ¬?)

open import Tools.Level
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

private variable
  a p : Level
  A   : Set _

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
