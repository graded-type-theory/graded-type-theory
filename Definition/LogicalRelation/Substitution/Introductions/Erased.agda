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
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution.Introductions.Prod R
open import Definition.LogicalRelation.Substitution.Introductions.Unit R
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

opaque

  -- Reducibility for Erased.

  ⊩Erased : Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ Erased A
  ⊩Erased {Γ} {A} ⊩A =
    𝕨′ _
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
  unfolding ⊩Erased _⊩⟨_⟩_≡_

  -- Reducibility of equality between applications of Erased.

  ⊩Erased≡Erased :
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩⟨ l ⟩ Erased A₁ ≡ Erased A₂
  ⊩Erased≡Erased (⊩A₁ , ⊩A₂ , A₁≡A₂) =
    case escape ⊩A₁ of λ
      ⊢A₁ →
    ⊩≡-intro (⊩Erased ⊩A₁) (⊩Erased ⊩A₂) $
    B₌ _ _
      (id (Erasedⱼ (escape ⊩A₂)))
      (≅-ΠΣ-cong ⊢A₁ (escapeEq ⊩A₁ A₁≡A₂)
         (≅-Unitrefl (⊢→⊢∙ ⊢A₁) Unit-ok) Σ-ok)
      (λ _ _ → W.wkEq _ _ ⊩A₁ A₁≡A₂)
      (λ _ ⊢Δ _ → id (Unitⱼ ⊢Δ Unit-ok))

opaque

  -- Validity of Erased.

  Erasedᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ Erased A
  Erasedᵛ ⊩A =
    case ⊩ᵛ⇔′ .proj₁ ⊩A of λ
      (⊩Γ , ⊩A , A≡A) →
    ⊩ᵛ⇔′ .proj₂ (⊩Γ , ⊩Erased ∘→ ⊩A , ⊩Erased≡Erased ∘→ A≡A)

opaque

  -- Validity of equality preservation for Erased.

  Erased-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l ⟩ Erased A₁ ≡ Erased A₂
  Erased-congᵛ A₁≡A₂ =
    case ⊩ᵛ≡⇔′ .proj₁ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂ , A₁≡A₂) →
    ⊩ᵛ≡⇔′ .proj₂ (Erasedᵛ ⊩A₁ , Erasedᵛ ⊩A₂ , ⊩Erased≡Erased ∘→ A₁≡A₂)

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Reducibility for [_].

  ⊩[] :
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ [ t ] ∷ Erased A
  ⊩[] (⊩A , ⊩t) =
    case ⊩star (wf (escape ⊩A)) Unit-ok of λ
      (⊩Unit , ⊩star) →
    ⊩∷-intro (⊩Erased ⊩A) $
    prod″ ⊩A ⊩t ⊩Unit ⊩star (⊩Erased ⊩A)

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- Reducibility of equality between applications of [_].

  ⊩[]≡[] :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ [ t ] ≡ [ u ] ∷ Erased A
  ⊩[]≡[] (⊩A , ⊩t , ⊩u , t≡u) =
    case ⊩star (wf (escape ⊩A)) Unit-ok of λ
      (⊩Unit , ⊩star) →
    ⊩≡∷-intro
      (⊩Erased ⊩A)
      (⊩[] (⊩A , ⊩t))
      (⊩[] (⊩A , ⊩u))
      (prod-cong″ ⊩A ⊩t ⊩u t≡u ⊩Unit ⊩star ⊩star
         (reflEqTerm ⊩Unit ⊩star) (⊩Erased ⊩A))

opaque

  -- Validity of [_].

  []ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ [ t ] ∷ Erased A
  []ᵛ ⊩t =
    case ⊩ᵛ∷⇔′ .proj₁ ⊩t of λ
      (⊩A , ⊩t , t≡t) →
    ⊩ᵛ∷⇔′ .proj₂ (Erasedᵛ ⊩A , ⊩[] ∘→ ⊩t , ⊩[]≡[] ∘→ t≡t)

opaque

  -- Validity of equality preservation for [_].

  []-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ [ t ] ≡ [ u ] ∷ Erased A
  []-congᵛ t≡u =
    case ⊩ᵛ≡∷⇔′ .proj₁ t≡u of λ
      (⊩t , ⊩u , t≡u) →
    ⊩ᵛ≡∷⇔′ .proj₂ ([]ᵛ ⊩t , []ᵛ ⊩u , ⊩[]≡[] ∘→ t≡u)
