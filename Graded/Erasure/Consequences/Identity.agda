------------------------------------------------------------------------
-- Some consequences of the fundamental lemma that are related to
-- identity types
------------------------------------------------------------------------

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
open Usage-restrictions UR

open import Definition.Typed TR
open import Definition.Typed.Consequences.Admissible TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Syntactic TR
open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Derived.Erased.Usage 𝕄 UR
import Graded.Erasure.LogicalRelation as L
open import Graded.Erasure.LogicalRelation.Assumptions TR
open import Graded.Erasure.LogicalRelation.Fundamental TR UR
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions TR UR
import Graded.Erasure.LogicalRelation.Hidden as H
import Graded.Erasure.Target as T
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR

open import Tools.Bool using (T)
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder

private variable
  Γ           : Con Term _
  γ₁ γ₂ γ₃ γ₄ : Conₘ _
  A t u v     : Term _
  s s₁ s₂     : Strength

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
    case ®∷Id⇔ .proj₁ $
         Fundamental.fundamentalErased-𝟙ᵐ
           (record
              { well-formed       = wfTerm ⊢v
              ; other-assumptions = ok
              })
           ⊢v ▸v of λ {
      (_ , rflᵣ v⇒rfl _) →
    inversion-rfl-Id
      (syntacticEqTerm (subset*Term v⇒rfl) .proj₂ .proj₂) }
    where
    open Fundamental-assumptions⁻ ok

    as : Assumptions
    as = record { ⊢Δ = wfTerm ⊢v; str = T.non-strict }

    open H as
    open L as

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
    []-cong-allowed-mode s 𝟙ᵐ →
    Fundamental-assumptions⁻ Γ →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ▸[ 𝟘ᵐ? ] u →
    γ₄ ▸[ 𝟘ᵐ? ] v →
    Γ ⊢ v ∷ Id A t u →
    Γ ⊢ t ≡ u ∷ A
  Id→≡′ {s} {Γ} {A} {t} {u} {v} []-cong-ok []-cong-ok′ ok ▸A ▸t ▸u ▸v =
    Γ ⊢ v ∷ Id A t u                                       →⟨ []-congⱼ′ []-cong-ok ⟩
    Γ ⊢ []-cong _ A t u v ∷ Id (Erased A) ([ t ]) ([ u ])  →⟨ flip (Id→≡ ok) ([]-congₘ ▸A ▸t ▸u ▸v []-cong-ok′) ⟩
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
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    []-cong-allowed s₁ →
    []-cong-allowed-mode s₁ 𝟙ᵐ →
    (s₂ PE.≡ 𝕨 → Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) 𝟘 𝟘) →
    Fundamental-assumptions⁻ Γ →
    γ₁ ▸[ 𝟘ᵐ ] A →
    γ₂ ▸[ 𝟘ᵐ ] t →
    γ₃ ▸[ 𝟘ᵐ ] u →
    γ₄ ▸[ 𝟘ᵐ ] v →
    Γ ⊢ v ∷ Erased.Erased s₂ (Id A t u) →
    Γ ⊢ t ≡ u ∷ A
  Id→≡″
    {s₂} {Γ} {A} {γ₂} {t} {γ₃} {u} {v} ⦃ ok ⦄
    []-cong-ok []-cong-ok′ P-ok as ▸A ▸t ▸u ▸v =
    Γ ⊢ v ∷ Erased (Id A t u)           →⟨ erasedⱼ ⟩
    Γ ⊢ erased (Id A t u) v ∷ Id A t u  →⟨ Id→≡′ ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄ []-cong-ok []-cong-ok′ as
                                             (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A) (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t)
                                             (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸u)
                                             (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) $
                                              ▸erased s₂ ▸v
                                                (λ _ →
                                                     _
                                                   , Idₘ-generalised (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A) ▸t ▸u
                                                       (λ _ → begin
                                                          γ₂ +ᶜ γ₃  ≤⟨ +ᶜ-monotone (▸-𝟘ᵐ ▸t) (▸-𝟘ᵐ ▸u) ⟩
                                                          𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityˡ _ ⟩
                                                          𝟘ᶜ        ∎)
                                                       (λ _ → ≤ᶜ-refl))
                                                P-ok) ⟩
    Γ ⊢ t ≡ u ∷ A                       □
    where
    open Erased s₂
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
