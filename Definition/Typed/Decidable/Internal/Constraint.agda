------------------------------------------------------------------------
-- Definitions related to constraints used by
-- Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Decidable.Internal.Constraint
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR hiding (no-equality-reflection)

open import Definition.Typed.Decidable.Internal.Equality 𝐌 TR
open import Definition.Typed.Decidable.Internal.Term 𝐌 TR
open import Definition.Typed.Variant

open import Tools.Bool
open import Tools.Function
import Tools.Level as L
open import Tools.List
open import Tools.Maybe
open import Tools.PropositionalEquality

private variable
  c : Constants

-- The semantics of a nullary constraint.

⟦_⟧ᶜ⁰ : Constraint⁰ → Set a
⟦ k-allowed                 ⟧ᶜ⁰ = K-allowed
⟦ level-allowed             ⟧ᶜ⁰ = L.Lift _ Level-allowed
⟦ level-is-small            ⟧ᶜ⁰ = L.Lift _ Level-is-small
⟦ no-equality-reflection    ⟧ᶜ⁰ = No-equality-reflection
⟦ opacity-allowed           ⟧ᶜ⁰ = Opacity-allowed
⟦ unfolding-mode-transitive ⟧ᶜ⁰ = L.Lift _
                                     (unfolding-mode ≡ transitive)

-- The semantics of a non-nullary constraint.

⟦_⟧ᶜ⁺ : Constraint⁺ c → Contexts c → Set a
⟦ box-cong-allowed s        ⟧ᶜ⁺ γ = []-cong-allowed (⟦ s ⟧ˢ γ)
⟦ unit-allowed s            ⟧ᶜ⁺ γ = Unit-allowed (⟦ s ⟧ˢ γ)
⟦ unit-with-η s             ⟧ᶜ⁺ γ = L.Lift _ (Unit-with-η (⟦ s ⟧ˢ γ))
⟦ πσ-allowed b p q          ⟧ᶜ⁺ γ =
  ΠΣ-allowed (⟦ b ⟧ᵇᵐ γ) (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ)

-- The semantics of a constraint.

⟦_⟧ᶜ : Constraint c → Contexts c → Set a
⟦ constr⁰ C ⟧ᶜ _ = ⟦ C ⟧ᶜ⁰
⟦ constr⁺ C ⟧ᶜ γ = ⟦ C ⟧ᶜ⁺ γ

-- Is the given nullary constraint satisfied?

satisfied?⁰ : Constraint⁰ → Contexts c → Bool
satisfied?⁰ k-allowed γ =
  γ .constraints⁰ .k-allowed?
satisfied?⁰ level-allowed γ =
  γ .constraints⁰ .level-allowed?
satisfied?⁰ level-is-small γ =
  γ .constraints⁰ .level-is-small?
satisfied?⁰ no-equality-reflection γ =
  γ .constraints⁰ .no-equality-reflection?
satisfied?⁰ opacity-allowed γ =
  γ .constraints⁰ .opacity-allowed?
satisfied?⁰ unfolding-mode-transitive γ =
  γ .constraints⁰ .unfolding-mode-transitive?

-- An equality test for non-nullary constraints.

infix 4 _≟ᶜ_

_≟ᶜ_ : (C₁ C₂ : Constraint⁺ c) → Maybe (C₁ ≡ C₂)
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

-- Is the given non-nullary constraint satisfied?

satisfied?⁺ : Constraint⁺ c → Contexts c → Bool
satisfied?⁺ C γ with member? _≟ᶜ_ C (γ .constraints⁺)
… | just _  = true
… | nothing = false

-- Is the given constraint satisfied?

satisfied? : Constraint c → Contexts c → Bool
satisfied? (constr⁰ C) = satisfied?⁰ C
satisfied? (constr⁺ C) = satisfied?⁺ C

-- All nullary constraints.

all-nullary-constraints : List Constraint⁰
all-nullary-constraints =
  k-allowed L.∷
  level-allowed L.∷
  level-is-small L.∷
  no-equality-reflection L.∷
  opacity-allowed L.∷
  unfolding-mode-transitive L.∷
  L.[]

-- All nullary constraints that are satisfied.

constraints⁰-as-list : Contexts c → List (Constraint c)
constraints⁰-as-list γ =
  L.map constr⁰
    (L.filterᵇ (flip satisfied?⁰ γ) all-nullary-constraints)

-- All constraints that are satisfied.

constraints : Contexts c → List (Constraint c)
constraints γ =
  constraints⁰-as-list γ L.++
  L.map constr⁺ (γ .constraints⁺)
