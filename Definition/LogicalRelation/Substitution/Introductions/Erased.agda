------------------------------------------------------------------------
-- Validity for Erased and [_]
------------------------------------------------------------------------

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

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Substitution R
open import
  Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma R
open import
  Definition.LogicalRelation.Substitution.Introductions.Sigma R
open import Definition.LogicalRelation.Substitution.Introductions.Unit R
open import Definition.Typed.Properties R
open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Graded.Derived.Erased.Untyped 𝕄 s

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  Γ           : Con Term _
  A A₁ A₂ t u : Term _
  l           : Universe-level

opaque

  -- Reducibility for Erased.

  ⊩Erased : Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ Erased A
  ⊩Erased ⊩A =
    ⊩ΠΣ⇔ .proj₂
      ( Σ-ok
      , wf (escape-⊩ ⊩A)
      , λ ρ⊇ ⊢Δ →
            wk-⊩ ρ⊇ ⊢Δ ⊩A
          , λ _ → refl-⊩≡ $ emb-⊩ 0≤ᵘ $ ⊩Unit ⊢Δ Unit-ok
      )

opaque

  -- Reducibility of equality between applications of Erased.

  ⊩Erased≡Erased :
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩⟨ l ⟩ Erased A₁ ≡ Erased A₂
  ⊩Erased≡Erased A₁≡A₂ =
    case wf-⊩≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    ⊩ΠΣ≡ΠΣ⇔ .proj₂
      ( ⊩Erased ⊩A₁
      , ⊩Erased ⊩A₂
      , PE.refl , PE.refl , PE.refl
      , λ ρ⊇ ⊢Δ →
            wk-⊩≡ ρ⊇ ⊢Δ A₁≡A₂
          , λ _ → refl-⊩≡ $ emb-⊩ 0≤ᵘ $ ⊩Unit ⊢Δ Unit-ok
      )

opaque

  -- Validity of equality preservation for Erased.

  Erased-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l ⟩ Erased A₁ ≡ Erased A₂
  Erased-congᵛ A₁≡A₂ =
    case ⊩ᵛ≡⇔ .proj₁ A₁≡A₂ of λ
      (⊩Γ , A₁≡A₂) →
    ⊩ᵛ≡⇔ .proj₂ (⊩Γ , ⊩Erased≡Erased ∘→ A₁≡A₂)

opaque

  -- Validity of Erased.

  Erasedᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ Erased A
  Erasedᵛ = ⊩ᵛ⇔⊩ᵛ≡ .proj₂ ∘→ Erased-congᵛ ∘→ ⊩ᵛ⇔⊩ᵛ≡ .proj₁

opaque

  -- Reducibility of equality between applications of [_].

  ⊩[]≡[] :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ [ t ] ≡ [ u ] ∷ Erased A
  ⊩[]≡[] {l} t≡u =
    case wf-⊩∷ (wf-⊩≡∷ t≡u .proj₁) of λ
      ⊩A →
    ⊩prod≡prod (⊩Erased ⊩A) t≡u
      (refl-⊩≡∷ (⊩star (wf (escape-⊩ ⊩A)) Unit-ok))

opaque

  -- Reducibility for [_].

  ⊩[] :
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ [ t ] ∷ Erased A
  ⊩[] = ⊩∷⇔⊩≡∷ .proj₂ ∘→ ⊩[]≡[] ∘→ ⊩∷⇔⊩≡∷ .proj₁

opaque

  -- Validity of equality preservation for [_].

  []-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ [ t ] ≡ [ u ] ∷ Erased A
  []-congᵛ t≡u =
    case ⊩ᵛ≡∷⇔ .proj₁ t≡u of λ
      (⊩A , t≡u) →
    ⊩ᵛ≡∷⇔ .proj₂ (Erasedᵛ ⊩A , ⊩[]≡[] ∘→ t≡u)

opaque

  -- Validity of [_].

  []ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ [ t ] ∷ Erased A
  []ᵛ = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ []-congᵛ ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁
