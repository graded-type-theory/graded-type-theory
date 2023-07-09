------------------------------------------------------------------------
-- A non-interference result.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
import Definition.Untyped
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions
open import Tools.Nat using (Nat)

module Graded.Erasure.Consequences.Non-interference
  {a} {M : Set a}
  (open Definition.Untyped M hiding (_∷_))
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (TR : Type-restrictions M)
  (UR : Usage-restrictions M)
  (𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet)
  {k : Nat}
  {Δ : Con Term k}
  (FA : Fundamental-assumptions 𝕄 TR UR Δ)
  {{eqrel : EqRelSet TR}}
  where

open Fundamental-assumptions FA

open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Fundamental TR
  using (fundamentalSubst)
open import Definition.LogicalRelation.Substitution TR
import Definition.LogicalRelation.Substitution.Irrelevance TR as IS
open import Definition.LogicalRelation.Substitution.Introductions.Nat TR

open import Graded.Context 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Modality.Properties.Has-well-behaved-zero
  semiring-with-meet-and-star 𝟘-well-behaved
open import Graded.Mode 𝕄

import Graded.Erasure.Target as T
open import Graded.Erasure.Extraction 𝕄 is-𝟘?
open import Graded.Erasure.LogicalRelation 𝕄 TR is-𝟘? ⊢Δ
open import Graded.Erasure.LogicalRelation.Fundamental
  𝕄 TR UR 𝟘-well-behaved
open import Graded.Erasure.LogicalRelation.Irrelevance 𝕄 TR is-𝟘? ⊢Δ
open import Graded.Erasure.LogicalRelation.Subsumption 𝕄 TR is-𝟘? ⊢Δ

open import Tools.Product

-- A simple non-interference property.

non-interference : ∀ {m} {Γ : Con Term m} {t : Term m} {γ : Conₘ m}
                   (⊢t : Γ ⊢ t ∷ ℕ) (▸t : γ ▸[ 𝟙ᵐ ] t) →
                   ∀ {σ σ′}
                   (⊢σ : Δ ⊢ˢ σ ∷ Γ) →
                   ∃₂ λ [Γ] [σ] →
                   σ ®⟨ ¹ ⟩ σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ / [Γ] / [σ] →
                   t [ σ ] ® erase t T.[ σ′ ] ∷ℕ
non-interference ⊢t ▸t ⊢σ =
  let [Γ] , [ℕ] , ⊩ʳt = fundamental FA ⊢t ▸t
      ⊢Γ = wfTerm ⊢t
      [Γ]′ , [σ]′ = fundamentalSubst ⊢Γ ⊢Δ ⊢σ
      [σ] = IS.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]′
      [σℕ] = proj₁ (unwrap [ℕ] ⊢Δ [σ])
      [σℕ]′ = proj₁ (unwrap {l = ¹} (ℕᵛ [Γ]) ⊢Δ [σ])
  in  [Γ] , [σ] , λ σ®σ′ →
    let t®t′ = ⊩ʳt [σ] σ®σ′
        t®t′∷ℕ = irrelevanceTerm [σℕ] [σℕ]′ (t®t′ ◀≢𝟘 𝟙≢𝟘)
    in  t®t′∷ℕ
