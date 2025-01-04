------------------------------------------------------------------------
-- Typing and equality rules related to OK
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
import Graded.Modality.Dedicated-nr

module Definition.Typed.Properties.Admissible.Bool.OK
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Graded.Modality.Dedicated-nr 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that there is a dedicated nr function.
  ⦃ has-nr : Dedicated-nr ⦄
  -- It is assumed that weak unit types are allowed.
  (Unitʷ-ok : Unitʷ-allowed)
  where

open Modality 𝕄

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Nat R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Syntactic R

open import Definition.Untyped M
open import Definition.Untyped.Bool 𝕄
open import Definition.Untyped.Nat 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ       : Con Term _
  t t₁ t₂ : Term _

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-cong-U :
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ →
    Γ ⊢ OK t₁ ≡ OK t₂ ∷ U zeroᵘ
  OK-cong-U {Γ} t₁≡t₂ =
    natcase-cong (refl (Uⱼ (zeroᵘⱼ (∙ ⊢ℕ₁))))
      (refl (Unitⱼ (zeroᵘⱼ ⊢Γ) Unitʷ-ok))
      (refl $
       ⊢natcase (Uⱼ (zeroᵘⱼ (∙ ⊢ℕ₂))) (Unitⱼ (zeroᵘⱼ (∙ ⊢ℕ₁)) Unitʷ-ok) (Emptyⱼ (∙ ⊢ℕ₂))
         (var₀ ⊢ℕ₁))
      t₁≡t₂
    where
    ⊢Γ : ⊢ Γ
    ⊢Γ = wfEqTerm t₁≡t₂

    ⊢ℕ₁ : Γ ⊢ ℕ
    ⊢ℕ₁ = ℕⱼ ⊢Γ

    ⊢ℕ₂ : Γ ∙ ℕ ⊢ ℕ
    ⊢ℕ₂ = ℕⱼ (∙ ⊢ℕ₁)

opaque

  -- An equality rule for OK.

  OK-cong :
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ →
    Γ ⊢ OK t₁ ≡ OK t₂
  OK-cong = univ ∘→ OK-cong-U

opaque

  -- A typing rule for OK.

  ⊢OK∷U :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ OK t ∷ U zeroᵘ
  ⊢OK∷U ⊢t =
    syntacticEqTerm (OK-cong-U (refl ⊢t)) .proj₂ .proj₁

opaque

  -- A typing rule for OK.

  ⊢OK :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ OK t
  ⊢OK = univ ∘→ ⊢OK∷U

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-0≡ :
    ⊢ Γ →
    Γ ⊢ OK zero ≡ Unitʷ zeroᵘ
  OK-0≡ ⊢Γ =
    OK zero                                              ≡⟨⟩⊢

    natcase OKᵍ 𝟘 (U zeroᵘ) (Unitʷ zeroᵘ)
      (natcase 𝟘 𝟘 (U zeroᵘ) (Unitʷ zeroᵘ) Empty (var x0)) zero  ≡⟨ univ $
                                                            natcase-zero-≡ (Uⱼ (zeroᵘⱼ (⊢Γ ∙[ ℕⱼ ]))) (Unitⱼ (zeroᵘⱼ ⊢Γ) Unitʷ-ok) $
                                                            ⊢natcase (Uⱼ (zeroᵘⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ]))) (Unitⱼ (zeroᵘⱼ (⊢Γ ∙[ ℕⱼ ])) Unitʷ-ok)
                                                              (Emptyⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ])) (var₀ (ℕⱼ ⊢Γ)) ⟩⊢∎
    Unitʷ zeroᵘ                                              ∎

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-1≡ :
    ⊢ Γ →
    Γ ⊢ OK (suc zero) ≡ Unitʷ zeroᵘ
  OK-1≡ ⊢Γ =
    OK (suc zero)                                              ≡⟨⟩⊢

    natcase OKᵍ 𝟘 (U zeroᵘ) (Unitʷ zeroᵘ)
      (natcase 𝟘 𝟘 (U zeroᵘ) (Unitʷ zeroᵘ) Empty (var x0)) (suc zero)  ≡⟨ PE.subst (_⊢_≡_ _ _) natcase-[] $
                                                                  _⊢_≡_.univ $
                                                                  natcase-suc-≡ (Uⱼ (zeroᵘⱼ (⊢Γ ∙[ ℕⱼ ]))) (Unitⱼ (zeroᵘⱼ ⊢Γ) Unitʷ-ok)
                                                                    (⊢natcase (Uⱼ (zeroᵘⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ]))) (Unitⱼ (zeroᵘⱼ (⊢Γ ∙[ ℕⱼ ])) Unitʷ-ok)
                                                                       (Emptyⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ])) (var₀ (ℕⱼ ⊢Γ)))
                                                                    (zeroⱼ ⊢Γ) ⟩⊢

    natcase 𝟘 𝟘 (U zeroᵘ) (Unitʷ zeroᵘ) Empty zero                     ≡⟨ univ $
                                                                  natcase-zero-≡ (Uⱼ (zeroᵘⱼ (⊢Γ ∙[ ℕⱼ ]))) (Unitⱼ (zeroᵘⱼ ⊢Γ) Unitʷ-ok)
                                                                    (Emptyⱼ (⊢Γ ∙[ ℕⱼ ])) ⟩⊢∎
    Unitʷ zeroᵘ                                                    ∎

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-2+≡ :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ OK (suc (suc t)) ≡ Empty
  OK-2+≡ {Γ} {t} ⊢t =
    OK (suc (suc t))                                              ≡⟨⟩⊢

    natcase OKᵍ 𝟘 (U zeroᵘ) (Unitʷ zeroᵘ)
      (natcase 𝟘 𝟘 (U zeroᵘ) (Unitʷ zeroᵘ) Empty (var x0)) (suc (suc t))  ≡⟨ PE.subst (_⊢_≡_ _ _) natcase-[] $
                                                                     _⊢_≡_.univ $
                                                                     natcase-suc-≡ (Uⱼ (zeroᵘⱼ (∙ ⊢ℕ₁))) (Unitⱼ (zeroᵘⱼ ⊢Γ) Unitʷ-ok)
                                                                       (⊢natcase (Uⱼ (zeroᵘⱼ (∙ ⊢ℕ₂))) (Unitⱼ (zeroᵘⱼ (∙ ⊢ℕ₁)) Unitʷ-ok)
                                                                          (Emptyⱼ (∙ ⊢ℕ₂)) (var₀ ⊢ℕ₁))
                                                                       (sucⱼ ⊢t) ⟩⊢

    natcase 𝟘 𝟘 (U zeroᵘ) (Unitʷ zeroᵘ) Empty (suc t)                     ≡⟨ univ $
                                                                     natcase-suc-≡ (Uⱼ (zeroᵘⱼ (∙ ⊢ℕ₁))) (Unitⱼ (zeroᵘⱼ ⊢Γ) Unitʷ-ok) (Emptyⱼ (∙ ⊢ℕ₁)) ⊢t ⟩⊢∎
    Empty                                                         ∎
    where
    ⊢Γ : ⊢ Γ
    ⊢Γ = wfTerm ⊢t

    ⊢ℕ₁ : Γ ⊢ ℕ
    ⊢ℕ₁ = ℕⱼ ⊢Γ

    ⊢ℕ₂ : Γ ∙ ℕ ⊢ ℕ
    ⊢ℕ₂ = ℕⱼ (∙ ⊢ℕ₁)
