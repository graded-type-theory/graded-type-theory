------------------------------------------------------------------------
-- Assumptions used to state some theorems in
-- Graded.Erasure.LogicalRelation.Fundamental elsewhere for consequences
-- of the fundamental lemma.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Graded.Erasure.LogicalRelation.Fundamental.Assumptions
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  ⦃ eqrel : EqRelSet TR ⦄
  where

open EqRelSet eqrel
open Modality 𝕄
open Usage-restrictions UR

open import Definition.Untyped M
open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR

open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Restrictions 𝕄

open import Tools.Nat
open import Tools.Sum

private variable
  k kᵈ : Nat
  ∇    : DCon (Term 0) _

-- A cut-down variant of Fundamental-assumptions (which is defined
-- below).

record Fundamental-assumptions⁻ (Δ : Cons kᵈ k) : Set a where
  no-eta-equality
  field
    -- Every definition in Δ is well-resourced.
    well-resourced : ▸[ 𝟙ᵐ ] (Δ .defs)
    -- If erased matches are allowed for emptyrec when the mode is 𝟙ᵐ,
    -- then the contexts in Δ are consistent.
    consistent : Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Δ
    -- Erased matches are not allowed unless the variable context is
    -- empty.
    closed-or-no-erased-matches :
      No-erased-matches TR UR ⊎ Empty-con (Δ .vars)
    instance
      -- Var-included holds or the variable context is empty.
      ⦃ inc ⦄ : Var-included or-empty Δ .vars

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
-- definition context is well-formed and well-resourced.

fundamental-assumptions⁻₀ :
  » ∇ → ▸[ 𝟙ᵐ ] ∇ → Fundamental-assumptions⁻ (∇ » ε)
fundamental-assumptions⁻₀ ≫∇ ▸∇ = record
  { well-resourced              = ▸∇
  ; consistent                  = λ _ →
                                    inhabited-consistent
                                      (⊢ˢʷ∷-idSubst (ε ≫∇))
  ; closed-or-no-erased-matches = inj₂ ε
  ; inc                         = ε
  }

-- Fundamental-assumptions holds for an empty variable context if the
-- definition context is well-formed and well-resourced.

fundamental-assumptions₀ :
  » ∇ → ▸[ 𝟙ᵐ ] ∇ → Fundamental-assumptions (∇ » ε)
fundamental-assumptions₀ ≫∇ ▸∇ = record
  { well-formed       = ε ≫∇
  ; other-assumptions = fundamental-assumptions⁻₀ ≫∇ ▸∇
  }
