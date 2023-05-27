------------------------------------------------------------------------
-- A modality for affine types.
------------------------------------------------------------------------

open import Tools.Bool

open import Definition.Modality.Instances.Zero-one-many true as 𝟘𝟙ω

open import Definition.Modality.Restrictions Zero-one-many

module Definition.Modality.Instances.Affine
  (restrictions : Restrictions)
  where

open Restrictions restrictions

open 𝟘𝟙ω renaming (Zero-one-many to Affine) public

open import Definition.Modality Affine
open import Definition.Modality.FullReduction.Assumptions
import Definition.Modality.Properties

import Definition.Mode

open import Definition.Typed.Restrictions Affine

open import Tools.Empty
open import Tools.Function
open import Tools.Nullary
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Unit

private variable
  p : Affine

-- An "affine types" modality.

affineModality : Modality
affineModality = zero-one-many-greatest restrictions

-- 𝟘 is the largest element.

≤𝟘 : p ≤ 𝟘
≤𝟘 {p = 𝟘} = refl
≤𝟘 {p = 𝟙} = refl
≤𝟘 {p = ω} = refl

-- Type restrictions that disallow the following types:
-- * Σ-types with η-equality for which the first component's quantity
--   is ω.
-- * If 𝟘ᵐ is not allowed: Σ-types with η-equality for which the first
--   component's quantity is 𝟘.

affine-restrictions : Type-restrictions
affine-restrictions = record
  { Unit-restriction = ⊤
  ; Σₚ-restriction   = λ where
      ω → ⊥
      𝟙 → ⊤
      𝟘 → T 𝟘ᵐ-allowed
  }

-- The full reduction assumptions hold for affineModality and
-- affine-restrictions.

full-reduction-assumptions :
  Full-reduction-assumptions affineModality affine-restrictions
full-reduction-assumptions = record
  { ≤𝟘           = λ _ → ≤𝟘
  ; ·-increasing = λ where
      {p = ω}         ()
      {p = 𝟙} {q = q} _  → begin
        q      ≡˘⟨ ·-identityˡ _ ⟩
        𝟙 · q  ∎
      {p = 𝟘} {q = q} _ → begin
        q      ≤⟨ ≤𝟘 ⟩
        𝟘 · q  ∎
  ; ⌞⌟≡𝟙ᵐ→≤𝟙 = λ where
      {p = ω} ()
      {p = 𝟙} _  _ → begin
        𝟙  ≡⟨⟩
        𝟙  ∎
      {p = 𝟘} ok →
        ⌞ 𝟘 ⌟ ≡ 𝟙ᵐ      →⟨ (λ hyp ok → ⌞⌟≡𝟙ᵐ→≉𝟘 ok hyp refl) ⟩
        ¬ T 𝟘ᵐ-allowed  →⟨ _$ ok ⟩
        ⊥               →⟨ ⊥-elim ⟩
        𝟘 ≤ 𝟙           □
  }
  where
  open Definition.Modality.Properties affineModality
  open Definition.Mode affineModality
  open Modality affineModality using (·-identityˡ)
  open Tools.Reasoning.PartialOrder ≤-poset
