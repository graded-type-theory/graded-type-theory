------------------------------------------------------------------------
-- Stability of algorithmic equality.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Stability
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Properties R
import Definition.Typed.Weakening R as W
open import Definition.Conversion R
open import Definition.Conversion.Soundness R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Stability R

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ Δ : Con Term n

mutual
  -- Stability of algorithmic equality of neutrals.
  stability~↑ : ∀ {k l A}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↑ A
              → Δ ⊢ k ~ l ↑ A
  stability~↑ Γ≡Δ (var-refl x x≡y) =
    var-refl (stabilityTerm Γ≡Δ x) x≡y
  stability~↑ Γ≡Δ (app-cong k~l x) =
    app-cong (stability~↓ Γ≡Δ k~l) (stabilityConv↑Term Γ≡Δ x)
  stability~↑ Γ≡Δ (fst-cong p~r) =
    fst-cong (stability~↓ Γ≡Δ p~r)
  stability~↑ Γ≡Δ (snd-cong p~r) =
    snd-cong (stability~↓ Γ≡Δ p~r)
  stability~↑ Γ≡Δ (natrec-cong x₁ x₂ x₃ k~l) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        ⊢F = proj₁ (syntacticEq (soundnessConv↑ x₁))
    in natrec-cong (stabilityConv↑ (Γ≡Δ ∙ (refl (ℕⱼ ⊢Γ))) x₁)
                   (stabilityConv↑Term Γ≡Δ x₂)
                   ((stabilityConv↑Term (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ) ∙ refl ⊢F) x₃))
                   (stability~↓ Γ≡Δ k~l)
  stability~↑ Γ≡Δ (prodrec-cong x x₁ x₂) =
    let ⊢Σ , _ = syntacticEqTerm (soundness~↓ x₁)
        ⊢F , ⊢G = syntacticΣ ⊢Σ
    in  prodrec-cong (stabilityConv↑ (Γ≡Δ ∙ refl ⊢Σ) x)
          (stability~↓ Γ≡Δ x₁)
          (stabilityConv↑Term (Γ≡Δ ∙ refl ⊢F ∙ refl ⊢G) x₂)
  stability~↑ Γ≡Δ (emptyrec-cong x₁ k~l) =
    emptyrec-cong (stabilityConv↑ Γ≡Δ x₁)
                  (stability~↓ Γ≡Δ k~l)
  stability~↑ Γ≡Δ (unitrec-cong x x₁ x₂) =
    let k≡l = soundness~↓ x₁
        ⊢Unit = proj₁ (syntacticEqTerm k≡l)
    in  unitrec-cong (stabilityConv↑ (Γ≡Δ ∙ refl ⊢Unit) x)
                     (stability~↓ Γ≡Δ x₁) (stabilityConv↑Term Γ≡Δ x₂)
  stability~↑ Γ≡Δ (J-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁~w₂ ≡Id) =
    case syntacticEq (soundnessConv↑ A₁≡A₂) .proj₁ of λ {
      ⊢A₁ →
    case wf ⊢A₁ ∙ ⊢A₁ of λ {
      ⊢Γ∙A₁ →
    case syntacticEqTerm (soundnessConv↑Term t₁≡t₂) .proj₂ .proj₁ of λ {
      ⊢t₁ →
    J-cong (stabilityConv↑ Γ≡Δ A₁≡A₂) (stabilityConv↑Term Γ≡Δ t₁≡t₂)
      (stabilityConv↑
         (Γ≡Δ ∙ refl ⊢A₁ ∙
          refl
            (Idⱼ (W.wkTerm (W.step W.id) ⊢Γ∙A₁ ⊢t₁) (var ⊢Γ∙A₁ here)))
         B₁≡B₂)
      (stabilityConv↑Term Γ≡Δ u₁≡u₂) (stabilityConv↑Term Γ≡Δ v₁≡v₂)
      (stability~↓ Γ≡Δ w₁~w₂) (stabilityEq Γ≡Δ ≡Id) }}}
  stability~↑ Γ≡Δ (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    case syntacticEqTerm (soundnessConv↑Term t₁≡t₂) .proj₂ .proj₁ of λ {
      ⊢t₁ →
    K-cong (stabilityConv↑ Γ≡Δ A₁≡A₂) (stabilityConv↑Term Γ≡Δ t₁≡t₂)
      (stabilityConv↑ (Γ≡Δ ∙ refl (Idⱼ ⊢t₁ ⊢t₁)) B₁≡B₂)
      (stabilityConv↑Term Γ≡Δ u₁≡u₂) (stability~↓ Γ≡Δ v₁~v₂)
      (stabilityEq Γ≡Δ ≡Id) ok }
  stability~↑ Γ≡Δ ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁~v₂ ≡Id ok) =
    []-cong-cong (stabilityConv↑ Γ≡Δ A₁≡A₂)
      (stabilityConv↑Term Γ≡Δ t₁≡t₂) (stabilityConv↑Term Γ≡Δ u₁≡u₂)
      (stability~↓ Γ≡Δ v₁~v₂) (stabilityEq Γ≡Δ ≡Id) ok

  -- Stability of algorithmic equality of neutrals of types in WHNF.
  stability~↓ : ∀ {k l A}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↓ A
              → Δ ⊢ k ~ l ↓ A
  stability~↓ Γ≡Δ ([~] A D whnfA k~l) =
    [~] A (stabilityRed* Γ≡Δ D) whnfA (stability~↑ Γ≡Δ k~l)

  -- Stability of algorithmic equality of types.
  stabilityConv↑ : ∀ {A B}
                 → ⊢ Γ ≡ Δ
                 → Γ ⊢ A [conv↑] B
                 → Δ ⊢ A [conv↑] B
  stabilityConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    [↑] A′ B′ (stabilityRed* Γ≡Δ D) (stabilityRed* Γ≡Δ D′) whnfA′ whnfB′
        (stabilityConv↓ Γ≡Δ A′<>B′)

  -- Stability of algorithmic equality of types in WHNF.
  stabilityConv↓ : ∀ {A B}
                 → ⊢ Γ ≡ Δ
                 → Γ ⊢ A [conv↓] B
                 → Δ ⊢ A [conv↓] B
  stabilityConv↓ Γ≡Δ (U-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  U-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (ℕ-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  ℕ-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (Empty-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Empty-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (Unit-refl x ok) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Unit-refl ⊢Δ ok
  stabilityConv↓ Γ≡Δ (ne x) =
    ne (stability~↓ Γ≡Δ x)
  stabilityConv↓ Γ≡Δ (ΠΣ-cong F A<>B A<>B₁ ok) =
    ΠΣ-cong (stability Γ≡Δ F) (stabilityConv↑ Γ≡Δ A<>B)
      (stabilityConv↑ (Γ≡Δ ∙ refl F) A<>B₁) ok
  stabilityConv↓ Γ≡Δ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (stabilityConv↑ Γ≡Δ A₁≡A₂) (stabilityConv↑Term Γ≡Δ t₁≡t₂)
      (stabilityConv↑Term Γ≡Δ u₁≡u₂)

  -- Stability of algorithmic equality of terms.
  stabilityConv↑Term : ∀ {t u A}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↑] u ∷ A
                     → Δ ⊢ t [conv↑] u ∷ A
  stabilityConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    [↑]ₜ B t′ u′ (stabilityRed* Γ≡Δ D) (stabilityRed*Term Γ≡Δ d)
                 (stabilityRed*Term Γ≡Δ d′) whnfB whnft′ whnfu′
                 (stabilityConv↓Term Γ≡Δ t<>u)

  -- Stability of algorithmic equality of terms in WHNF.
  stabilityConv↓Term : ∀ {t u A}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↓] u ∷ A
                     → Δ ⊢ t [conv↓] u ∷ A
  stabilityConv↓Term Γ≡Δ (ℕ-ins x) =
    ℕ-ins (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Empty-ins x) =
    Empty-ins (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Unit-ins x) =
    Unit-ins (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Σʷ-ins x x₁ x₂) =
    Σʷ-ins (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stability~↓ Γ≡Δ x₂)
  stabilityConv↓Term Γ≡Δ (ne-ins t u neN x) =
    ne-ins (stabilityTerm Γ≡Δ t) (stabilityTerm Γ≡Δ u) neN (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (univ x x₁ x₂) =
    univ (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stabilityConv↓ Γ≡Δ x₂)
  stabilityConv↓Term Γ≡Δ (zero-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  stabilityConv↓Term Γ≡Δ (starʷ-refl x ok) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  starʷ-refl ⊢Δ ok
  stabilityConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (stabilityConv↑Term Γ≡Δ t<>u)
  stabilityConv↓Term Γ≡Δ (prod-cong x x₁ x₂ x₃ ok) =
    prod-cong (stability Γ≡Δ x) (stability (Γ≡Δ ∙ refl x) x₁)
      (stabilityConv↑Term Γ≡Δ x₂) (stabilityConv↑Term Γ≡Δ x₃) ok
  stabilityConv↓Term Γ≡Δ (η-eq x x₁ y y₁ t<>u) =
    let ⊢F , ⊢G = syntacticΠ (syntacticTerm x)
    in  η-eq (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)
             y y₁ (stabilityConv↑Term (Γ≡Δ ∙ (refl ⊢F)) t<>u)
  stabilityConv↓Term Γ≡Δ (Σ-η ⊢p ⊢r pProd rProd fstConv sndConv) =
    Σ-η (stabilityTerm Γ≡Δ ⊢p) (stabilityTerm Γ≡Δ ⊢r)
        pProd rProd
        (stabilityConv↑Term Γ≡Δ fstConv) (stabilityConv↑Term Γ≡Δ sndConv)
  stabilityConv↓Term Γ≡Δ (η-unit [t] [u] tUnit uUnit) =
    let [t] = stabilityTerm Γ≡Δ [t]
        [u] = stabilityTerm Γ≡Δ [u]
    in  η-unit [t] [u] tUnit uUnit
  stabilityConv↓Term Γ≡Δ (Id-ins ⊢v₁ v₁~v₂) =
    Id-ins (stabilityTerm Γ≡Δ ⊢v₁) (stability~↓ Γ≡Δ v₁~v₂)
  stabilityConv↓Term Γ≡Δ (rfl-refl t≡u) =
    rfl-refl (stabilityEqTerm Γ≡Δ t≡u)
