------------------------------------------------------------------------
-- Typing and equality rules related to OK
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Properties.Admissible.Bool.OK
  {a} {M : Set a}
  {𝕄 : Modality M}
  (OKᵍ : M)
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- It is assumed that weak unit types are allowed.
  (Unitʷ-ok : Unitʷ-allowed)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Nat R
open import Definition.Typed.Properties.Admissible.U.Primitive R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Term R
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
    Γ ⊢ OK t₁ ≡ OK t₂ ∷ U₀
  OK-cong-U {Γ} t₁≡t₂ =
    natcase-cong (refl (⊢U₀ (∙ ⊢ℕ₁)))
      (refl (Unitⱼ ⊢Γ Unitʷ-ok))
      (refl $
       ⊢natcase (⊢U₀ (∙ ⊢ℕ₂)) (Unitⱼ (∙ ⊢ℕ₁) Unitʷ-ok)
         (Emptyⱼ (∙ ⊢ℕ₂)) (var₀ ⊢ℕ₁))
      t₁≡t₂
    where
    ⊢Γ : ⊢ Γ
    ⊢Γ = wfEqTerm t₁≡t₂

    ⊢ℕ₁ : Γ ⊢ ℕ
    ⊢ℕ₁ = ⊢ℕ ⊢Γ

    ⊢ℕ₂ : Γ »∙ ℕ ⊢ ℕ
    ⊢ℕ₂ = ⊢ℕ (∙ ⊢ℕ₁)

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
    Γ ⊢ OK t ∷ U₀
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

  OK-0≡∷U :
    ⊢ Γ →
    Γ ⊢ OK zero ≡ Unitʷ ∷ U₀
  OK-0≡∷U ⊢Γ =
    OK zero                                       ≡⟨⟩⊢

    natcase OKᵍ 𝟘 U₀ Unitʷ
      (natcase 𝟘 𝟘 U₀ Unitʷ Empty (var x0)) zero  ≡⟨ natcase-zero-≡ (⊢U₀ (⊢Γ ∙[ ⊢ℕ ])) (Unitⱼ ⊢Γ Unitʷ-ok) $
                                                     ⊢natcase (⊢U₀ (⊢Γ ∙[ ⊢ℕ ] ∙[ ⊢ℕ ])) (Unitⱼ (⊢Γ ∙[ ⊢ℕ ]) Unitʷ-ok)
                                                       (Emptyⱼ (⊢Γ ∙[ ⊢ℕ ] ∙[ ⊢ℕ ])) (var₀ (⊢ℕ ⊢Γ)) ⟩⊢∎
    Unitʷ                                         ∎

opaque

  -- An equality rule for OK.

  OK-0≡ :
    ⊢ Γ →
    Γ ⊢ OK zero ≡ Unitʷ
  OK-0≡ ⊢Γ = univ (OK-0≡∷U ⊢Γ)

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-1≡∷U :
    ⊢ Γ →
    Γ ⊢ OK (suc zero) ≡ Unitʷ ∷ U₀
  OK-1≡∷U ⊢Γ =
    OK (suc zero)                                       ≡⟨⟩⊢

    natcase OKᵍ 𝟘 U₀ Unitʷ
      (natcase 𝟘 𝟘 U₀ Unitʷ Empty (var x0)) (suc zero)  ≡⟨ PE.subst (flip (_⊢_≡_∷_ _ _) _) natcase-[] $
                                                           natcase-suc-≡ (⊢U₀ (⊢Γ ∙[ ⊢ℕ ])) (Unitⱼ ⊢Γ Unitʷ-ok)
                                                             (⊢natcase (⊢U₀ (⊢Γ ∙[ ⊢ℕ ] ∙[ ⊢ℕ ])) (Unitⱼ (⊢Γ ∙[ ⊢ℕ ]) Unitʷ-ok)
                                                                 (Emptyⱼ (⊢Γ ∙[ ⊢ℕ ] ∙[ ⊢ℕ ])) (var₀ (⊢ℕ ⊢Γ)))
                                                             (zeroⱼ ⊢Γ) ⟩⊢

    natcase 𝟘 𝟘 U₀ Unitʷ Empty zero                     ≡⟨ natcase-zero-≡ (⊢U₀ (⊢Γ ∙[ ⊢ℕ ])) (Unitⱼ ⊢Γ Unitʷ-ok) (Emptyⱼ (⊢Γ ∙[ ⊢ℕ ])) ⟩⊢∎

    Unitʷ                                               ∎

opaque

  -- An equality rule for OK.

  OK-1≡ :
    ⊢ Γ →
    Γ ⊢ OK (suc zero) ≡ Unitʷ
  OK-1≡ ⊢Γ = univ (OK-1≡∷U ⊢Γ)

opaque
  unfolding OK

  -- An equality rule for OK.

  OK-2+≡∷U :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ OK (suc (suc t)) ≡ Empty ∷ U₀
  OK-2+≡∷U {Γ} {t} ⊢t =
    OK (suc (suc t))                                       ≡⟨⟩⊢

    natcase OKᵍ 𝟘 U₀ Unitʷ
      (natcase 𝟘 𝟘 U₀ Unitʷ Empty (var x0)) (suc (suc t))  ≡⟨ PE.subst (flip (_⊢_≡_∷_ _ _) _) natcase-[] $
                                                              natcase-suc-≡ (⊢U₀ (∙ ⊢ℕ₁)) (Unitⱼ ⊢Γ Unitʷ-ok)
                                                                (⊢natcase (⊢U₀ (∙ ⊢ℕ₂)) (Unitⱼ (∙ ⊢ℕ₁) Unitʷ-ok)
                                                                  (Emptyⱼ (∙ ⊢ℕ₂)) (var₀ ⊢ℕ₁))
                                                                (sucⱼ ⊢t) ⟩⊢

    natcase 𝟘 𝟘 U₀ Unitʷ Empty (suc t)                     ≡⟨ natcase-suc-≡ (⊢U₀ (∙ ⊢ℕ₁)) (Unitⱼ ⊢Γ Unitʷ-ok) (Emptyⱼ (∙ ⊢ℕ₁)) ⊢t ⟩⊢∎

    Empty                                                  ∎
    where
    ⊢Γ : ⊢ Γ
    ⊢Γ = wfTerm ⊢t

    ⊢ℕ₁ : Γ ⊢ ℕ
    ⊢ℕ₁ = ⊢ℕ ⊢Γ

    ⊢ℕ₂ : Γ »∙ ℕ ⊢ ℕ
    ⊢ℕ₂ = ⊢ℕ (∙ ⊢ℕ₁)

opaque

  -- An equality rule for OK.

  OK-2+≡ :
    Γ ⊢ t ∷ ℕ →
    Γ ⊢ OK (suc (suc t)) ≡ Empty
  OK-2+≡ ⊢t = univ (OK-2+≡∷U ⊢t)
