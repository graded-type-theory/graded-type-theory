------------------------------------------------------------------------
-- A non-interference result.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

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
  using (fundamental-⊩ˢ∷)
open import Definition.LogicalRelation.Hidden TR

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
open import Graded.Erasure.LogicalRelation.Hidden as
open import Graded.Erasure.LogicalRelation.Fundamental TR UR

open Fundamental FA

open import Tools.Function
open import Tools.Product

private variable
  Γ : Con Term _
  t : Term _
  γ : Conₘ _

-- A simple non-interference property.
--
-- Note that some assumptions are given as module parameters.

non-interference :
  Γ ⊢ t ∷ ℕ → γ ▸[ 𝟙ᵐ ] t →
  ∀ {σ σ′} →
  Δ ⊢ˢ σ ∷ Γ →
  σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ →
  t [ σ ] ® erase str t T.[ σ′ ] ∷ℕ
non-interference {Γ} {t} {γ} ⊢t ▸t {σ} {σ′} ⊢σ σ®σ′ =
                                                   $⟨ fundamental-⊩ʳ∷ ⊢t ▸t ⟩

  γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ 𝟙ᵐ ] ℕ                        →⟨ proj₂ ∘→ ▸⊩ʳ∷⇔ .proj₁ ⟩

  (∀ {σ σ′} → Δ ⊩ˢ σ ∷ Γ → σ ® σ′ ∷[ 𝟙ᵐ ] Γ ◂ γ →
   t [ σ ] ®⟨ ¹ ⟩ erase str t T.[ σ′ ] ∷ ℕ ◂ 𝟙)    →⟨ (λ hyp → hyp (fundamental-⊩ˢ∷ well-formed (wfTerm ⊢t) ⊢σ) σ®σ′) ⟩

  t [ σ ] ®⟨ ¹ ⟩ erase str t T.[ σ′ ] ∷ ℕ ◂ 𝟙      →⟨ ®∷→®∷◂ω non-trivial ⟩

  t [ σ ] ®⟨ ¹ ⟩ erase str t T.[ σ′ ] ∷ ℕ          ⇔⟨ ®∷ℕ⇔ ⟩→

  t [ σ ] ® erase str t T.[ σ′ ] ∷ℕ                □
