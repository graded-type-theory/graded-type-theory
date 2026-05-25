------------------------------------------------------------------------
-- Assumptions used to state some theorems in
-- Graded.Erasure.LogicalRelation.Fundamental elsewhere for consequences
-- of the fundamental lemma.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one

module Graded.Erasure.LogicalRelation.Fundamental.Assumptions
  {a} {M : Set a}
  {𝕄 : Modality M}
  {variant : Mode-variant 𝕄}
  (open Graded.Mode.Instances.Zero-one variant)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Untyped M
open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR

open import Graded.Usage UR
open import Graded.Restrictions.Zero-one 𝕄 variant

open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Relation
open import Tools.Sum as ⊎

private variable
  k kᵈ : Nat
  ∇    : DCon (Term 0) _

-- A cut-down variant of Fundamental-assumptions (which is defined
-- below).

record Fundamental-assumptions⁻ (Δ : Cons kᵈ k) : Set a where
  no-eta-equality
  field
    -- Every transparent definition in Δ is well-resourced.
    well-resourced : ▸[ 𝟙ᵐ ] (Δ .defs)
    -- If erased matches are allowed for emptyrec when the mode is 𝟙ᵐ,
    -- then the contexts in Δ are consistent.
    consistent : Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ
    -- Erased matches are not allowed unless the variable context is
    -- empty and higher quotient constructors are not allowed.
    closed-or-no-erased-matches :
      No-erased-matches TR UR ⊎
      Empty-con (Δ .vars) × ¬ Higher-quotient-constructors-neutral
    instance
      -- No-equality-reflection holds or the variable context is
      -- empty.
      ⦃ no-equality-reflection-or-empty ⦄ :
        No-equality-reflection or-empty Δ .vars

-- The fundamental lemma is proved under the assumption that a given
-- context pair Δ satisfies the following assumptions.

record Fundamental-assumptions (Δ : Cons kᵈ k) : Set a where
  no-eta-equality
  field
    -- The context is well-formed.
    well-formed : ⊢ Δ
    -- Other assumptions.
    other-assumptions : Fundamental-assumptions⁻ Δ

  open Fundamental-assumptions⁻ other-assumptions public

-- Fundamental-assumptions⁻ holds for an empty variable context if the
-- definition context is well-formed and well-resourced, and either
-- erased matches are disallowed or higher quotient constructors are
-- not neutral.

fundamental-assumptions⁻₀ :
  No-erased-matches TR UR ⊎ ¬ Higher-quotient-constructors-neutral →
  » ∇ → ▸[ 𝟙ᵐ ] ∇ → Fundamental-assumptions⁻ (∇ » ε)
fundamental-assumptions⁻₀ ok ≫∇ ▸∇ = record
  { well-resourced =
      ▸∇
  ; consistent =
      λ _ → inhabited-consistent (⊢ˢʷ∷-idSubst (ε ≫∇))
  ; closed-or-no-erased-matches =
      ⊎.map idᶠ (ε ,_) ok
  ; no-equality-reflection-or-empty =
      ε
  }

-- Fundamental-assumptions holds for an empty variable context if the
-- definition context is well-formed and well-resourced, and either
-- erased matches are disallowed or higher quotient constructors are
-- not neutral.

fundamental-assumptions₀ :
  No-erased-matches TR UR ⊎ ¬ Higher-quotient-constructors-neutral →
  » ∇ → ▸[ 𝟙ᵐ ] ∇ → Fundamental-assumptions (∇ » ε)
fundamental-assumptions₀ ok ≫∇ ▸∇ = record
  { well-formed       = ε ≫∇
  ; other-assumptions = fundamental-assumptions⁻₀ ok ≫∇ ▸∇
  }
