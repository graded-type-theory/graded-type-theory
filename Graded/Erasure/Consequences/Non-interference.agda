------------------------------------------------------------------------
-- A non-interference result.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
import Definition.Untyped
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions
open import Graded.Erasure.Target as T using (Strictness)
open import Tools.Nat using (Nat)

module Graded.Erasure.Consequences.Non-interference
  {a} {M : Set a}
  (open Definition.Untyped M)
  {𝕄 : Modality M}
  {variant : Mode-variant 𝕄}
  (open Modality 𝕄)
  (open Graded.Mode.Instances.Zero-one variant)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M 𝕄 ⦄
  ⦃ eqrel : EqRelSet TR ⦄
  {kᵈ k : Nat}
  {∇ : DCon (Term 0) kᵈ}
  {Δ : Con Term k}
  (FA : Fundamental-assumptions TR UR (glassify ∇ » Δ))
  {str : Strictness}
  where

open Fundamental-assumptions FA

open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR

open import Graded.Context 𝕄
open import Graded.Usage UR
open import Graded.Modality.Properties 𝕄

open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation.Assumptions TR
open import Graded.Erasure.LogicalRelation.Fundamental TR UR

private

  as : Assumptions
  as = assumptions well-formed str ⇒*-is-reduction-relation

open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Hidden variant as

open Fundamental FA

open import Tools.Function

private variable
  Γ : Con Term _
  t : Term _
  γ : Conₘ _

-- A simple non-interference property.
--
-- Note that some assumptions are given as module parameters.

non-interference :
  glassify ∇ » Γ ⊢ t ∷ ℕ → γ ▸[ 𝟙ᵐ ] t →
  ∀ {σ σ′} →
  glassify ∇ » Δ ⊢ˢʷ σ ∷ Γ →
  σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ →
  t [ σ ] ® erase str t T.[ σ′ ] ∷ℕ
non-interference {Γ} {t} {γ} ⊢t ▸t {σ} {σ′} ⊢σ σ®σ′ =
                                                                 $⟨ fundamental ⊢t ▸t ⟩

  γ ▸ Γ ⊩ʳ t ∷[ 𝟙ᵐ ] ℕ                                           ⇔⟨ ▸⊩ʳ∷⇔ ⟩→

  (∀ {σ σ′} → glassify ∇ » Δ ⊢ˢʷ σ ∷ Γ → σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ →
   t [ σ ] ® erase str t T.[ σ′ ] ∷ ℕ ◂ 𝟙)                       →⟨ (λ hyp → hyp ⊢σ σ®σ′) ⟩

  t [ σ ] ® erase str t T.[ σ′ ] ∷ ℕ ◂ 𝟙                         →⟨ ®∷→®∷◂ω non-trivial ⟩

  t [ σ ] ® erase str t T.[ σ′ ] ∷ ℕ                             ⇔⟨ ®∷ℕ⇔ ⟩→

  t [ σ ] ® erase str t T.[ σ′ ] ∷ℕ                              □
