------------------------------------------------------------------------
-- Typing and equality rules related to OK
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Bool.OK
  {a} {M : Set a}
  {𝕄 : Modality M}
  (OKᵍ : M)
  (R : Type-restrictions 𝕄)
  (open Modality 𝕄)
  (open Type-restrictions R)
  -- It is assumed that weak unit types are allowed.
  (Unitʷ-ok : Unitʷ-allowed)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Nat R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Syntactic R

open import Definition.Untyped M
open import Definition.Untyped.Bool.OK 𝕄 OKᵍ
open import Definition.Untyped.Nat 𝕄

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ       : Cons _ _
  t t₁ t₂ : Term _

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-cong-U :
    Γ ⊢ t₁ ≡ t₂ ∷ ℕ →
    Γ ⊢ OK t₁ ≡ OK t₂ ∷ U 0
  OK-cong-U {Γ} t₁≡t₂ =
    natcase-cong (refl (Uⱼ (∙ ⊢ℕ₁)))
      (refl (Unitⱼ ⊢Γ Unitʷ-ok))
      (refl $
       ⊢natcase (Uⱼ (∙ ⊢ℕ₂)) (Unitⱼ (∙ ⊢ℕ₁) Unitʷ-ok) (Emptyⱼ (∙ ⊢ℕ₂))
         (var₀ ⊢ℕ₁))
      t₁≡t₂
    where
    ⊢Γ : ⊢ Γ
    ⊢Γ = wfEqTerm t₁≡t₂

    ⊢ℕ₁ : Γ ⊢ ℕ
    ⊢ℕ₁ = ℕⱼ ⊢Γ

    ⊢ℕ₂ : Γ »∙ ℕ ⊢ ℕ
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
    Γ ⊢ OK t ∷ U 0
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
    Γ ⊢ OK zero ≡ Unitʷ 0
  OK-0≡ ⊢Γ =
    OK zero                                              ≡⟨⟩⊢

    natcase OKᵍ 𝟘 (U 0) (Unitʷ 0)
      (natcase 𝟘 𝟘 (U 0) (Unitʷ 0) Empty (var x0)) zero  ≡⟨ univ $
                                                            natcase-zero-≡ (Uⱼ (⊢Γ ∙[ ℕⱼ ])) (Unitⱼ ⊢Γ Unitʷ-ok) $
                                                            ⊢natcase (Uⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ])) (Unitⱼ (⊢Γ ∙[ ℕⱼ ]) Unitʷ-ok)
                                                              (Emptyⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ])) (var₀ (ℕⱼ ⊢Γ)) ⟩⊢∎
    Unitʷ 0                                              ∎

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-1≡ :
    ⊢ Γ →
    Γ ⊢ OK (suc zero) ≡ Unitʷ 0
  OK-1≡ ⊢Γ =
    OK (suc zero)                                              ≡⟨⟩⊢

    natcase OKᵍ 𝟘 (U 0) (Unitʷ 0)
      (natcase 𝟘 𝟘 (U 0) (Unitʷ 0) Empty (var x0)) (suc zero)  ≡⟨ PE.subst (_⊢_≡_ _ _) natcase-[] $
                                                                  _⊢_≡_.univ $
                                                                  natcase-suc-≡ (Uⱼ (⊢Γ ∙[ ℕⱼ ])) (Unitⱼ ⊢Γ Unitʷ-ok)
                                                                    (⊢natcase (Uⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ])) (Unitⱼ (⊢Γ ∙[ ℕⱼ ]) Unitʷ-ok)
                                                                       (Emptyⱼ (⊢Γ ∙[ ℕⱼ ] ∙[ ℕⱼ ])) (var₀ (ℕⱼ ⊢Γ)))
                                                                    (zeroⱼ ⊢Γ) ⟩⊢

    natcase 𝟘 𝟘 (U 0) (Unitʷ 0) Empty zero                     ≡⟨ univ $
                                                                  natcase-zero-≡ (Uⱼ (⊢Γ ∙[ ℕⱼ ])) (Unitⱼ ⊢Γ Unitʷ-ok)
                                                                    (Emptyⱼ (⊢Γ ∙[ ℕⱼ ])) ⟩⊢∎
    Unitʷ 0                                                    ∎

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-2+≡ :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ OK (suc (suc t)) ≡ Empty
  OK-2+≡ {Γ} {t} ⊢t =
    OK (suc (suc t))                                              ≡⟨⟩⊢

    natcase OKᵍ 𝟘 (U 0) (Unitʷ 0)
      (natcase 𝟘 𝟘 (U 0) (Unitʷ 0) Empty (var x0)) (suc (suc t))  ≡⟨ PE.subst (_⊢_≡_ _ _) natcase-[] $
                                                                     _⊢_≡_.univ $
                                                                     natcase-suc-≡ (Uⱼ (∙ ⊢ℕ₁)) (Unitⱼ ⊢Γ Unitʷ-ok)
                                                                       (⊢natcase (Uⱼ (∙ ⊢ℕ₂)) (Unitⱼ (∙ ⊢ℕ₁) Unitʷ-ok)
                                                                          (Emptyⱼ (∙ ⊢ℕ₂)) (var₀ ⊢ℕ₁))
                                                                       (sucⱼ ⊢t) ⟩⊢

    natcase 𝟘 𝟘 (U 0) (Unitʷ 0) Empty (suc t)                     ≡⟨ univ $
                                                                     natcase-suc-≡ (Uⱼ (∙ ⊢ℕ₁)) (Unitⱼ ⊢Γ Unitʷ-ok) (Emptyⱼ (∙ ⊢ℕ₁)) ⊢t ⟩⊢∎
    Empty                                                         ∎
    where
    ⊢Γ : ⊢ Γ
    ⊢Γ = wfTerm ⊢t

    ⊢ℕ₁ : Γ ⊢ ℕ
    ⊢ℕ₁ = ℕⱼ ⊢Γ

    ⊢ℕ₂ : Γ »∙ ℕ ⊢ ℕ
    ⊢ℕ₂ = ℕⱼ (∙ ⊢ℕ₁)
