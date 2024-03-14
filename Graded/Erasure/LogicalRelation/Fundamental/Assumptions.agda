------------------------------------------------------------------------
-- Assumptions used to state some theorems in
-- Graded.Erasure.LogicalRelation.Fundamental elsewhere for consequences
-- of the fundamental lemma.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Erasure.LogicalRelation.Fundamental.Assumptions
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions UR

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR

open import Graded.Mode 𝕄
open import Graded.Restrictions 𝕄

open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Sum

private variable
  k : Nat

-- A cut-down variant of Fundamental-assumptions (which is defined
-- below).

record Fundamental-assumptions⁻ (Δ : Con Term k) : Set a where
  no-eta-equality
  field
    -- If erased matches are allowed for emptyrec when the mode is 𝟙ᵐ,
    -- then the context is consistent.
    consistent : Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ
    -- Erased matches are not allowed unless the context is empty.
    closed-or-no-erased-matches : No-erased-matches TR UR ⊎ k ≡ 0

-- The fundamental lemma is proved under the assumption that a given
-- context Δ satisfies the following assumptions.

record Fundamental-assumptions (Δ : Con Term k) : Set a where
  no-eta-equality
  field
    -- The context is well-formed.
    well-formed : ⊢ Δ
    -- Other assumptions.
    other-assumptions : Fundamental-assumptions⁻ Δ

  open Fundamental-assumptions⁻ other-assumptions public

-- Fundamental-assumptions⁻ holds unconditionally for empty contexts.

fundamental-assumptions⁻₀ : Fundamental-assumptions⁻ ε
fundamental-assumptions⁻₀ = record
  { consistent                  = λ _ →
                                    inhabited-consistent
                                      (_⊢ˢ_∷_.id {σ = idSubst})
  ; closed-or-no-erased-matches = inj₂ refl
  }

-- Fundamental-assumptions holds unconditionally for empty contexts.

fundamental-assumptions₀ : Fundamental-assumptions ε
fundamental-assumptions₀ = record
  { well-formed       = ε
  ; other-assumptions = fundamental-assumptions⁻₀
  }
