------------------------------------------------------------------------
-- A modality for linear types.
------------------------------------------------------------------------

open import Tools.Bool

open import Definition.Modality.Instances.Zero-one-many false as 𝟘𝟙ω

open import Definition.Modality.Restrictions Zero-one-many

module Definition.Modality.Instances.Linearity
  (restrictions : Restrictions)
  where

open 𝟘𝟙ω renaming (Zero-one-many to Linearity) public

open import Definition.Modality Linearity
open import Definition.Modality.FullReduction.Assumptions
import Definition.Modality.Properties

open import Definition.Typed.Restrictions Linearity

open import Tools.Empty
import Tools.Reasoning.PartialOrder
open import Tools.Unit

-- A "linear types" modality.

linearityModality : Modality
linearityModality = zero-one-many-greatest restrictions

open Definition.Modality.Properties linearityModality

-- Type restrictions that disallow the following types:
-- * Unit types with η-equality.
-- * Σ-types with η-equality for which the first component's quantity
--   is 𝟘 or ω.

linearity-restrictions : Type-restrictions
linearity-restrictions = record
  { Unit-restriction = ⊥
  ; Σₚ-restriction   = λ where
      𝟘 → ⊥
      ω → ⊥
      𝟙 → ⊤
  }

-- The full reduction assumptions hold for linearityModality and
-- linearity-restrictions.

full-reduction-assumptions :
  Full-reduction-assumptions linearityModality linearity-restrictions
full-reduction-assumptions = record
  { ≤𝟘           = λ ()
  ; ·-increasing = λ where
      {p = 𝟘}         ()
      {p = ω}         ()
      {p = 𝟙} {q = q} _  → begin
        q      ≡˘⟨ ·-identityˡ _ ⟩
        𝟙 · q  ∎
  ; ⌞⌟≡𝟙ᵐ→≤𝟙 = λ where
      {p = 𝟘} ()
      {p = ω} ()
      {p = 𝟙} _  _ → begin
        𝟙  ≡⟨⟩
        𝟙  ∎
  }
  where
  open Modality linearityModality using (·-identityˡ)
  open Tools.Reasoning.PartialOrder ≤-poset
