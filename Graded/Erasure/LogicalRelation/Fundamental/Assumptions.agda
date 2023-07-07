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
  (𝕄 : Modality M)
  (TR : Type-restrictions M)
  (UR : Usage-restrictions M)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed TR
open import Definition.Typed.Consequences.Canonicity TR

open import Graded.Restrictions

open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Sum

-- The fundamental lemma is proven under the following assumptions.

record Fundamental-assumptions : Set a where
  no-eta-equality
  field
    {k} : Nat
    {Δ} : Con Term k
    -- The context is well-formed
    ⊢Δ : ⊢ Δ
    -- The context is consistent
    consistent : ∀ {t} → Δ ⊢ t ∷ Empty → ⊥
    -- Erased matches are not allowed unless the context is empty
    closed-or-no-erased-matches : No-erased-matches 𝕄 UR ⊎ k ≡ 0

-- The assumptions hold unconditionally for empty contexts.

Fundamental-assumptions₀ : Fundamental-assumptions
Fundamental-assumptions₀ = record
  { ⊢Δ = ε
  ; consistent = ¬Empty
  ; closed-or-no-erased-matches = inj₂ refl
  }
