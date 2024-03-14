------------------------------------------------------------------------
-- A non-interference result.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
import Definition.Untyped
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions
open import Graded.Erasure.Target as T using (Strictness)
open import Tools.Nat using (Nat)

module Graded.Erasure.Consequences.Non-interference
  {a} {M : Set a}
  (open Definition.Untyped M hiding (_∷_))
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  {k : Nat}
  {Δ : Con Term k}
  (FA : Fundamental-assumptions TR UR Δ)
  {str : Strictness}
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
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation.Assumptions TR

private

  as : Assumptions
  as = record { ⊢Δ = well-formed; str = str }

open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Fundamental TR UR
open import Graded.Erasure.LogicalRelation.Irrelevance as
open import Graded.Erasure.LogicalRelation.Subsumption as

open Fundamental FA

open import Tools.Product

-- A simple non-interference property.
--
-- Note that some assumptions are given as module parameters.

non-interference : ∀ {m} {Γ : Con Term m} {t : Term m} {γ : Conₘ m}
                   (⊢t : Γ ⊢ t ∷ ℕ) (▸t : γ ▸[ 𝟙ᵐ ] t) →
                   ∀ {σ σ′}
                   (⊢σ : Δ ⊢ˢ σ ∷ Γ) →
                   ∃₂ λ [Γ] [σ] →
                   σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ / [Γ] / [σ] →
                   t [ σ ] ® erase str t T.[ σ′ ] ∷ℕ
non-interference ⊢t ▸t ⊢σ =
  let [Γ] , [ℕ] , ⊩ʳt = fundamental ⊢t ▸t
      ⊢Γ = wfTerm ⊢t
      [Γ]′ , [σ]′ = fundamentalSubst ⊢Γ well-formed ⊢σ
      [σ] = IS.irrelevanceSubst [Γ]′ [Γ] well-formed well-formed [σ]′
      [σℕ] = proj₁ (unwrap [ℕ] well-formed [σ])
      [σℕ]′ = proj₁ (unwrap {l = ¹} (ℕᵛ [Γ]) well-formed [σ])
  in  [Γ] , [σ] , λ σ®σ′ →
    let t®t′ = ⊩ʳt [σ] σ®σ′
        t®t′∷ℕ = irrelevanceTerm [σℕ] [σℕ]′ (t®t′ ◀≢𝟘 non-trivial)
    in  t®t′∷ℕ
