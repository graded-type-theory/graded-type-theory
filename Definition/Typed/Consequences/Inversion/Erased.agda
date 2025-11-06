------------------------------------------------------------------------
-- Lemmas related to inversion for typing for Erased
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
open import Definition.Untyped.NotParametrised using (Strength)

module Definition.Typed.Consequences.Inversion.Erased
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  (s : Strength)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R

open import Definition.Untyped M
open import Definition.Untyped.Erased 𝕄 s

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private variable
  Γ     : Con Term _
  A l t : Term _

opaque
  unfolding Erased [_]

  -- An inversion lemma for [_].
  --
  -- See also
  -- Definition.Typed.Properties.Admissible.Erased.inversion-[].

  inversion-[]′ :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ [ t ] ∷ Erased l A →
    Γ ⊢ t ∷ A × Erased-allowed s
  inversion-[]′ ⊢[] =
    case inversion-prod ⊢[] of λ
      (_ , _ , _ , _ , _ , ⊢t , ⊢lift-star , Erased-l-A≡ΠΣ , Σˢ-ok) →
    case ΠΣ-injectivity Erased-l-A≡ΠΣ of λ {
      (A≡B , _ , _ , PE.refl , _) →
    let _ , _ , ⊢star , _ = inversion-lift ⊢lift-star
        _ , Unit-ok       = inversion-star ⊢star
    in
    conv ⊢t (sym A≡B) , (Unit-ok , Σˢ-ok) }

opaque
  unfolding [_]

  -- If Erased is allowed, then a certain form of inversion for [_]
  -- does not hold.

  ¬-inversion-[]′ :
    Erased-allowed s →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ [ t ] ∷ A →
       ∃₃ λ B q l →
         Γ ⊢ t ∷ B × Γ ⊢ A ≡ Σ⟨ s ⟩ 𝟘 , q ▷ B ▹ Lift l (Unit s))
  ¬-inversion-[]′ (Unit-ok , Σ-ok) inversion-[] = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ : Term 0
    t′ = zero

    A′ : Term 0
    A′ =
      Σ 𝟘 , 𝟘 ▷ ℕ ▹
      natrec 𝟙 𝟙 𝟙 (U zeroᵘ) (Lift zeroᵘ (Unit s)) ℕ (var x0)

    ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ∙ ⊢ℕ ε

    ⊢Γ′∙ℕ∙ℕ : ⊢ Γ′ ∙ ℕ ∙ ℕ
    ⊢Γ′∙ℕ∙ℕ = ∙ ⊢ℕ ⊢Γ′∙ℕ

    ⊢Γ′∙ℕ∙U : ⊢ Γ′ ∙ ℕ ∙ U zeroᵘ
    ⊢Γ′∙ℕ∙U = ∙ ⊢U₀ ⊢Γ′∙ℕ

    ⊢Lift-Unit : ε ⊢ Lift zeroᵘ (Unit s) ∷ U zeroᵘ
    ⊢Lift-Unit =
      conv (Liftⱼ′ (⊢zeroᵘ ε) (Unitⱼ ε Unit-ok))
        (U-cong-⊢≡ (supᵘₗ-zeroˡ (⊢zeroᵘ ε)))

    ⊢[t′] : Γ′ ⊢ [ t′ ] ∷ A′
    ⊢[t′] = prodⱼ
      (_⊢_.univ $
       natrecⱼ (wkTerm₁ (⊢ℕ ε) ⊢Lift-Unit) (ℕⱼ (∙ ⊢U₀ ⊢Γ′∙ℕ∙ℕ))
         (var ⊢Γ′∙ℕ here))
      (zeroⱼ ε)
      (conv (liftⱼ′ (⊢zeroᵘ ε) (starⱼ ε Unit-ok))
         (_⊢_≡_.sym $ univ (natrec-zero ⊢Lift-Unit (ℕⱼ ⊢Γ′∙ℕ∙U))))
      Σ-ok

    ℕ≡Lift : ∃ λ l → Γ′ ⊢ ℕ ≡ Lift l (Unit s)
    ℕ≡Lift =
      let _ , _ , _ , _ , A′≡        = inversion-[] ⊢[t′]
          _ , ≡Lift-Unit , _ , _ , _ = ΠΣ-injectivity ⦃ ok = ε ⦄ A′≡
      in
      _ ,
      trans
        (_⊢_≡_.sym $ _⊢_≡_.univ $
         natrec-suc ⊢Lift-Unit (ℕⱼ ⊢Γ′∙ℕ∙U) (zeroⱼ ε))
        (≡Lift-Unit (refl (sucⱼ (zeroⱼ ε))))

    bad : ⊥
    bad = Lift≢ℕ ⦃ ok = ε ⦄ (sym (ℕ≡Lift .proj₂))

opaque
  unfolding Erased

  -- If Erased is allowed, then another form of inversion for [] also
  -- does not hold.

  ¬-inversion-[] :
    Erased-allowed s →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ [ t ] ∷ A →
       ∃₂ λ B l → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Erased l B)
  ¬-inversion-[] Erased-ok inversion-[] =
    ¬-inversion-[]′ Erased-ok λ ⊢[] →
    let B , l , ⊢t , A≡ = inversion-[] ⊢[] in
    B , 𝟘 , wk1 l , ⊢t , A≡
