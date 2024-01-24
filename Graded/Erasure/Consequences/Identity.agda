------------------------------------------------------------------------
-- Some consequences of the fundamental lemma that are related to
-- identity types
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Erasure.Consequences.Identity
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR

open import Definition.Typed TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Properties TR
open import Definition.Untyped M hiding (_∷_)

open import Graded.Context 𝕄
open import Graded.Derived.Erased.Eta.Typed TR
import Graded.Derived.Erased.Untyped 𝕄 as Erased
open import Graded.Derived.Erased.Eta.Usage 𝕄 UR
import Graded.Erasure.LogicalRelation TR as L
open import Graded.Erasure.LogicalRelation.Fundamental TR UR
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions TR UR
import Graded.Erasure.LogicalRelation.Hidden TR as H
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR

open import Tools.Bool using (T)
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ           : Con Term _
  γ₁ γ₂ γ₃ γ₄ : Conₘ _
  A t u v     : Term _
  s           : Strength

opaque

  -- If the modality's zero is well-behaved, the type Id A t u is
  -- inhabited in a context that satisfies Fundamental-assumptions⁻,
  -- and the witness of inhabitance is a term that is well-resourced
  -- with respect to 𝟘ᶜ, then t is definitionally equal to u.

  Id→≡ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    Fundamental-assumptions⁻ Γ →
    Γ ⊢ v ∷ Id A t u →
    𝟘ᶜ ▸[ 𝟙ᵐ ] v →
    Γ ⊢ t ≡ u ∷ A
  Id→≡ ok ⊢v ▸v =
    case ®-Id $
         Fundamental.fundamentalErased-𝟙ᵐ
           (record
              { well-formed       = wfTerm ⊢v
              ; other-assumptions = ok
              })
           ⊢v ▸v of λ {
      (rflᵣ v⇒rfl _) →
    inversion-rfl-Id
      (syntacticEqTerm (subset*Term v⇒rfl) .proj₂ .proj₂) }
    where
    open Fundamental-assumptions⁻ ok
    open H is-𝟘? (wfTerm ⊢v)
    open L is-𝟘? (wfTerm ⊢v)

opaque

  -- A variant of the previous lemma: If the modality's zero is
  -- well-behaved, []-cong is allowed, the type Id A t u is inhabited
  -- in a context that satisfies Fundamental-assumptions⁻, and the
  -- witness of inhabitance as well as the terms A, t and u are
  -- well-resourced with respect to any context and the mode 𝟘ᵐ?, then
  -- t is definitionally equal to u.
  --
  -- Note that if []-cong is allowed, then (at the time of writing)
  -- Fundamental-assumptions⁻ only holds for the empty context.

  Id→≡′ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    []-cong-allowed s →
    Fundamental-assumptions⁻ Γ →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ▸[ 𝟘ᵐ? ] u →
    γ₄ ▸[ 𝟘ᵐ? ] v →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ t ≡ u ∷ A
  Id→≡′ {s} {Γ} {A} {t} {u} {v} []-cong-ok ok ▸A ▸t ▸u ▸v =
    Γ ⊢ v ∷ Id A t u                                       →⟨ []-congⱼ′ []-cong-ok ⟩
    Γ ⊢ []-cong _ A t u v ∷ Id (Erased A) ([ t ]) ([ u ])  →⟨ flip (Id→≡ ok) ([]-congₘ ▸A ▸t ▸u ▸v) ⟩
    Γ ⊢ ([ t ]) ≡ ([ u ]) ∷ Erased A                       →⟨ proj₁ ∘→ proj₂ ∘→ prod-cong⁻¹ ⟩
    Γ ⊢ t ≡ u ∷ A                                          □
    where
    open Erased s

opaque

  -- Another variant of Id→≡.
  --
  -- Note that if []-cong is allowed, then (at the time of writing)
  -- Fundamental-assumptions⁻ only holds for the empty context.

  Id→≡″ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    []-cong-allowed s →
    Fundamental-assumptions⁻ Γ →
    γ₁ ▸[ 𝟘ᵐ ] A →
    γ₂ ▸[ 𝟘ᵐ ] t →
    γ₃ ▸[ 𝟘ᵐ ] u →
    γ₄ ▸[ 𝟘ᵐ ] v →
    Γ ⊢ v ∷ Erased.Erased 𝕤 (Id A t u) →
    Γ ⊢ t ≡ u ∷ A
  Id→≡″ {Γ} {A} {t} {u} {v} []-cong-ok ok ▸A ▸t ▸u ▸v =
    Γ ⊢ v ∷ Erased (Id A t u)  →⟨ erasedⱼ ⟩
    Γ ⊢ erased v ∷ Id A t u    →⟨ Id→≡′ []-cong-ok ok
                                    (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t)
                                    (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸u) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) $ ▸erased ▸v) ⟩
    Γ ⊢ t ≡ u ∷ A              □
    where
    open import Graded.Derived.Erased.Eta.Untyped 𝕄
