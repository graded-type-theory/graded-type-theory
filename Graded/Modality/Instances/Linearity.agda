------------------------------------------------------------------------
-- A modality for linear types.
------------------------------------------------------------------------

open import Tools.Bool

open import Graded.Modality.Instances.Zero-one-many false as 𝟘𝟙ω

open import Graded.Mode.Restrictions

module Graded.Modality.Instances.Linearity
  (mrs : Mode-restrictions)
  where

open Mode-restrictions mrs

open 𝟘𝟙ω renaming (Zero-one-many to Linearity) public

open import Graded.Modality Linearity
open import Graded.FullReduction.Assumptions
import Graded.Modality.Properties

open import Definition.Typed.Restrictions Linearity

open import Tools.Empty
open import Tools.Function
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Unit

private variable
  rs : Type-restrictions

-- A "linear types" modality.

linearityModality : Modality
linearityModality = zero-one-many-greatest mrs

open Graded.Modality.Properties linearityModality

-- An instance of Type-restrictions is suitable for the full reduction
-- theorem if
-- * Unit-restriction does not hold,
-- * Σₚ-restriction 𝟘 p does not hold, and
-- * Σₚ-restriction ω p does not hold.

Suitable-for-full-reduction :
  Type-restrictions → Set
Suitable-for-full-reduction rs =
  ¬ Unit-restriction ×
  (∀ p → ¬ Σₚ-restriction 𝟘 p) ×
  (∀ p → ¬ Σₚ-restriction ω p)
  where
  open Type-restrictions rs

-- Given an instance of Type-restrictions one can create a "suitable"
-- instance.

suitable-for-full-reduction :
  Type-restrictions → ∃ Suitable-for-full-reduction
suitable-for-full-reduction rs =
    record rs
      { Unit-restriction = ⊥
      ; ΠΣ-restriction   = λ b p q →
          ΠΣ-restriction b p q × p ≢ 𝟘 × p ≢ ω
      }
  , idᶠ
  , (λ _ → (_$ refl) ∘→ proj₁ ∘→ proj₂)
  , (λ _ → (_$ refl) ∘→ proj₂ ∘→ proj₂)
  where
  open Type-restrictions rs

-- The full reduction assumptions hold for linearityModality and any
-- "suitable" Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction rs →
  Full-reduction-assumptions linearityModality rs
full-reduction-assumptions (¬Unit , ¬𝟘 , ¬ω) = record
  { ≤𝟘           = ⊥-elim ∘→ ¬Unit
  ; ·-increasing = λ where
      {p = 𝟘}         ok → ⊥-elim (¬𝟘 _ ok)
      {p = ω}         ok → ⊥-elim (¬ω _ ok)
      {p = 𝟙} {r = q} _  → begin
        q      ≡˘⟨ ·-identityˡ _ ⟩
        𝟙 · q  ∎
  ; ⌞⌟≡𝟙ᵐ→≤𝟙 = λ where
      {p = 𝟘} ok   → ⊥-elim (¬𝟘 _ ok)
      {p = ω} ok   → ⊥-elim (¬ω _ ok)
      {p = 𝟙} _  _ → begin
        𝟙  ≡⟨⟩
        𝟙  ∎
  }
  where
  open Modality linearityModality using (·-identityˡ)
  open Tools.Reasoning.PartialOrder ≤-poset
