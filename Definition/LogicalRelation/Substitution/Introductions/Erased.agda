------------------------------------------------------------------------
-- Validity for Erased and [_]
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality
open import Tools.Product

module Definition.LogicalRelation.Substitution.Introductions.Erased
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- Erased is assumed to be allowed.
  {s}
  (Erased-ok@(Unit-ok , Σ-ok) : Erased-allowed s)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Pi R
open import Definition.LogicalRelation.Substitution.Introductions.Prod R
open import Definition.LogicalRelation.Substitution.Introductions.Unit R
open import Definition.LogicalRelation.Substitution.Reflexivity R
import Definition.LogicalRelation.Weakening R as W
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Untyped M hiding (_∷_)

open import Graded.Derived.Erased.Typed.Primitive R Erased-ok
open import Graded.Derived.Erased.Untyped 𝕄 s

open import Tools.Function

private variable
  Γ           : Con Term _
  A A₁ A₂ t u : Term _
  l           : TypeLevel
  ⊩Γ          : ⊩ᵛ _
  ⊩A          : _ ⊩⟨ _ ⟩ _
  ⊩ᵛA ⊩ᵛA₁    : _ ⊩ᵛ⟨ _ ⟩ _ / _

opaque

  -- Reducibility for Erased.

  ⊩Erased : Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ Erased A
  ⊩Erased {Γ} {A} ⊩A =
    Σᵣ′ _
      Unit!
      (idRed:*: (Erasedⱼ ⊢A))
      ⊢A
      (Unitⱼ ⊢ΓA Unit-ok)
      (≅-ΠΣ-cong ⊢A (escapeEq ⊩A (reflEq ⊩A))
         (≅-Unitrefl ⊢ΓA Unit-ok) Σ-ok)
      (λ ρ∷⊇ ⊢Δ → W.wk ρ∷⊇ ⊢Δ ⊩A)
      (λ _ ⊢Δ _ → Unitᵣ
         (record
            { ⇒*-Unit = idRed:*: (Unitⱼ ⊢Δ Unit-ok)
            ; ok      = Unit-ok
            }))
      (λ ρ∷⊇ ⊢Δ ⊩x ⊩y x≡y → id (Unitⱼ ⊢Δ Unit-ok))
      Σ-ok
    where
    ⊢A : Γ ⊢ A
    ⊢A = escape ⊩A

    ⊢ΓA : ⊢ Γ ∙ A
    ⊢ΓA = wf ⊢A ∙ ⊢A

opaque

  -- Validity of Erased.

  Erasedᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ →
    Γ ⊩ᵛ⟨ l ⟩ Erased A / ⊩Γ
  Erasedᵛ ⊩A = Σᵛ _ ⊩A (Unitᵛ (_ ∙ ⊩A) Unit-ok) Σ-ok

opaque
  unfolding Erasedᵛ

  -- Validity of equality preservation for Erased.

  Erased-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A₂ / ⊩Γ →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ / ⊩Γ / ⊩ᵛA₁ →
    Γ ⊩ᵛ⟨ l ⟩ Erased A₁ ≡ Erased A₂ / ⊩Γ / Erasedᵛ ⊩ᵛA₁
  Erased-congᵛ {l} {⊩ᵛA₁} ⊩A₂ ⊩A₁≡A₂ =
    Σ-congᵛ
      _
      ⊩ᵛA₁
      (Unitᵛ _ _)
      ⊩A₂
      (Unitᵛ _ Unit-ok)
      ⊩A₁≡A₂
      (λ {k Δ σ} →
         reflᵛ {l = l} _ (Unitᵛ (_ ∙ ⊩ᵛA₁) Unit-ok)
           {k = k} {Δ = Δ} {σ = σ})
      Σ-ok

opaque

  -- Reducibility for [_].

  ⊩[] :
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ [ t ] ∷ Erased A / ⊩Erased ⊩A
  ⊩[] {Γ} {l} {A} {⊩A} ⊩t =
    prod″
      ⊩A
      ⊩t
      ⊩Unit′
      ⊩star
      (⊩Erased ⊩A)
      where
      ⊢Γ : ⊢ Γ
      ⊢Γ = wf (escape ⊩A)

      ⊢star : Γ ⊢ star s ∷ Unit s
      ⊢star = starⱼ ⊢Γ Unit-ok

      ⊩Unit′ : Γ ⊩⟨ l ⟩ Unit s
      ⊩Unit′ = Unitᵣ record
        { ⇒*-Unit = idRed:*: (Unitⱼ ⊢Γ Unit-ok)
        ; ok      = Unit-ok
        }

      ⊩star : Γ ⊩⟨ l ⟩ star s ∷ Unit s / ⊩Unit′
      ⊩star = record
        { n    = _
        ; d    = idRedTerm:*: ⊢star
        ; n≡n  = ≅ₜ-starrefl ⊢Γ Unit-ok
        ; prop = starᵣ
        }

opaque
  unfolding Erasedᵛ

  -- Validity of [_].

  []ᵛ :
    {⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ} →
    ∀ t →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A →
    Γ ⊩ᵛ⟨ l ⟩ [ t ] ∷ Erased A / ⊩Γ / Erasedᵛ ⊩A
  []ᵛ {l} {⊩A} t ⊩t =
    prodᵛ {t = t} {u = star!} _ _
      (Unitᵛ (_ ∙ ⊩A) Unit-ok)
      ⊩t
      (starᵛ {l = l} _ Unit-ok) Σ-ok

opaque

  -- An equality preservation lemma for [_].

  ⊩[]≡[] :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ u ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ [ t ] ≡ [ u ] ∷ Erased A / ⊩Erased ⊩A
  ⊩[]≡[] {Γ} {l} {A} ⊩A ⊩t ⊩u ⊩t≡u =
    prod-cong″
      ⊩A
      ⊩t
      ⊩u
      ⊩t≡u
      ⊩Unit′
      ⊩star
      ⊩star
      (reflEqTerm ⊩Unit′ ⊩star)
      (⊩Erased ⊩A)
      where
      ⊢Γ : ⊢ Γ
      ⊢Γ = wf (escape ⊩A)

      ⊢star : Γ ⊢ star s ∷ Unit s
      ⊢star = starⱼ ⊢Γ Unit-ok

      ⊩Unit′ : Γ ⊩⟨ l ⟩ Unit s
      ⊩Unit′ = Unitᵣ record
        { ⇒*-Unit = idRed:*: (Unitⱼ ⊢Γ Unit-ok)
        ; ok      = Unit-ok
        }

      ⊩star : Γ ⊩⟨ l ⟩ star s ∷ Unit s / ⊩Unit′
      ⊩star = record
        { n    = _
        ; d    = idRedTerm:*: ⊢star
        ; n≡n  = ≅ₜ-starrefl ⊢Γ Unit-ok
        ; prop = starᵣ
        }

opaque
  unfolding Erasedᵛ

  -- Validity of equality preservation for [_].

  []-congᵛ :
    ∀ t u →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩ᵛA →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A / ⊩Γ / ⊩ᵛA →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / ⊩Γ / ⊩ᵛA →
    Γ ⊩ᵛ⟨ l ⟩ [ t ] ≡ [ u ] ∷ Erased A / ⊩Γ / Erasedᵛ ⊩ᵛA
  []-congᵛ {Γ} {l} {⊩Γ} {⊩ᵛA} t u ⊩t ⊩u ⊩t≡u =
    prod-congᵛ
      {t = t}
      {t′ = u}
      {u = star!}
      {u′ = star!}
      ⊩Γ
      ⊩ᵛA
      (Unitᵛ (_ ∙ ⊩ᵛA) Unit-ok)
      ⊩t
      ⊩u
      ⊩t≡u
      ⊩star
      ⊩star
      (reflᵗᵛ {t = star!} {l = l} ⊩Γ (Unitᵛ ⊩Γ Unit-ok) ⊩star)
      Σ-ok
    where
    ⊩star : Γ ⊩ᵛ⟨ l ⟩ star s ∷ Unit s / ⊩Γ / Unitᵛ ⊩Γ Unit-ok
    ⊩star = starᵛ {l = l} ⊩Γ Unit-ok
