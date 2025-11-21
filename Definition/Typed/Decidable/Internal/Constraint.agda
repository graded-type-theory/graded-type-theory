------------------------------------------------------------------------
-- Definitions related to constraints used by
-- Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal.Constraint
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR

open import Definition.Typed.Decidable.Internal.Equality TR
open import Definition.Typed.Decidable.Internal.Term TR
open import Definition.Typed.Variant

import Tools.Level as L
open import Tools.Maybe
open import Tools.PropositionalEquality

private variable
  c : Constants

-- The semantics of a constraint.

⟦_⟧ᶜ : Constraint c → Contexts c → Set a
⟦ k-allowed                 ⟧ᶜ _ = K-allowed
⟦ level-allowed             ⟧ᶜ _ = L.Lift _ Level-allowed
⟦ level-is-small            ⟧ᶜ _ = L.Lift _ Level-is-small
⟦ opacity-allowed           ⟧ᶜ _ = Opacity-allowed
⟦ unfolding-mode-transitive ⟧ᶜ _ = L.Lift _
                                     (unfolding-mode ≡ transitive)
⟦ box-cong-allowed s        ⟧ᶜ γ = []-cong-allowed (⟦ s ⟧ˢ γ)
⟦ unit-allowed s            ⟧ᶜ γ = Unit-allowed (⟦ s ⟧ˢ γ)
⟦ unit-with-η s             ⟧ᶜ γ = L.Lift _ (Unit-with-η (⟦ s ⟧ˢ γ))
⟦ πσ-allowed b p q          ⟧ᶜ γ =
  ΠΣ-allowed (⟦ b ⟧ᵇᵐ γ) (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ)

-- An equality test for constraints.

infix 4 _≟ᶜ_

_≟ᶜ_ : (C₁ C₂ : Constraint c) → Maybe (C₁ ≡ C₂)
k-allowed ≟ᶜ k-allowed =
  just refl
level-allowed ≟ᶜ level-allowed =
  just refl
level-is-small ≟ᶜ level-is-small =
  just refl
opacity-allowed ≟ᶜ opacity-allowed =
  just refl
unfolding-mode-transitive ≟ᶜ unfolding-mode-transitive =
  just refl
box-cong-allowed s₁ ≟ᶜ box-cong-allowed s₂ =
  cong box-cong-allowed <$> s₁ ≟ˢ s₂
unit-allowed s₁ ≟ᶜ unit-allowed s₂ =
  cong unit-allowed <$> s₁ ≟ˢ s₂
unit-with-η s₁ ≟ᶜ unit-with-η s₂ =
  cong unit-with-η <$> s₁ ≟ˢ s₂
πσ-allowed b₁ p₁ q₁ ≟ᶜ πσ-allowed b₂ p₂ q₂ =
  cong₃ πσ-allowed <$> b₁ ≟ᵇᵐ b₂ ⊛ p₁ ≟ᵍ p₂ ⊛ q₁ ≟ᵍ q₂
_ ≟ᶜ _ =
  nothing
