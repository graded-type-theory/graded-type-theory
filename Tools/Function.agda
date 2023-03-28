module Tools.Function where

open import Function.Base
  using (case_of_; flip; _$_)
  renaming (id to idᶠ; _∘_ to _∘→_)
  public

open import Tools.Level
open import Tools.Product

private variable
  a b   : Level
  A B C : Set _

-- Function composition (simply typed variant)
_∘ᶠ_ : ∀ {ℓ} → {A B C : Set ℓ} → (B → C) → (A → B) → A → C
_∘ᶠ_ f g a = f (g a)

-- Logical equivalence.

infix 3 _⇔_

_⇔_ : Set a → Set b → Set (a ⊔ b)
A ⇔ B = (A → B) × (B → A)

-- Composition of logical equivalences.

infixr 9 _∘⇔_

_∘⇔_ : B ⇔ C → A ⇔ B → A ⇔ C
(f₁ , f₂) ∘⇔ (g₁ , g₂) = f₁ ∘→ g₁ , g₂ ∘→ f₂
