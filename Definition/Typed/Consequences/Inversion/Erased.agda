------------------------------------------------------------------------
-- Lemmas related to inversion for typing for Erased
------------------------------------------------------------------------

open import Configuration-types
import Graded.Modality
open import Definition.Untyped.NotParametrised using (Strength)

module Definition.Typed.Consequences.Inversion.Erased
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (TC : Type-configuration 𝕄)
  (s : Strength)
  where

open Modality 𝕄
open Type-configuration TC

open import Definition.Typed TC
open import Definition.Typed.Consequences.Inequality TC
open import Definition.Typed.Consequences.Injectivity TC
open import Definition.Typed.Inversion TC
open import Definition.Typed.Properties TC
open import Definition.Typed.Substitution TC
open import Definition.Typed.Weakening TC

open import Definition.Untyped M
open import Definition.Untyped.Erased 𝕄 s

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private variable
  Γ   : Cons _ _
  A t : Term _
  l   : Lvl _

opaque
  unfolding Erased [_]

  -- An inversion lemma for [_].
  --
  -- See also
  -- Definition.Typed.Properties.Admissible.Erased.inversion-[].

  inversion-[]′ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
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
    ¬ (∀ {m n} {Γ : Cons m n} {t A : Term n} →
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
    A′ = Σ 𝟘 , 𝟘 ▷ ℕ ▹ natrec 𝟙 𝟙 𝟙 U₀ (Lift zeroᵘₗ (Unit s)) ℕ (var x0)

    ⊢Γ′∙ℕ : ε »⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ∙ ⊢ℕ εε

    ⊢Γ′∙ℕ∙ℕ : ε »⊢ Γ′ ∙ ℕ ∙ ℕ
    ⊢Γ′∙ℕ∙ℕ = ∙ ⊢ℕ ⊢Γ′∙ℕ

    ⊢Γ′∙ℕ∙U : ε »⊢ Γ′ ∙ ℕ ∙ U₀
    ⊢Γ′∙ℕ∙U = ∙ ⊢U₀ ⊢Γ′∙ℕ

    ⊢Lift-Unit : ε » ε ⊢ Lift zeroᵘₗ (Unit s) ∷ U₀
    ⊢Lift-Unit =
      conv (Liftⱼ′ (⊢zeroᵘ εε) (Unitⱼ εε Unit-ok))
        (U-cong-⊢≡ (supᵘₗ-zeroˡ (⊢zeroᵘ εε)))

    ⊢[t′] : ε » Γ′ ⊢ [ t′ ] ∷ A′
    ⊢[t′] = prodⱼ
      (_⊢_.univ $
       natrecⱼ (wk₁ (⊢ℕ εε) ⊢Lift-Unit) (ℕⱼ (∙ ⊢U₀ ⊢Γ′∙ℕ∙ℕ))
         (var ⊢Γ′∙ℕ here))
      (zeroⱼ εε)
      (conv (liftⱼ′ (⊢zeroᵘ εε) (starⱼ εε Unit-ok))
         (_⊢_≡_.sym $ univ (natrec-zero ⊢Lift-Unit (ℕⱼ ⊢Γ′∙ℕ∙U))))
      Σ-ok

    ℕ≡Lift : ∃ λ l → ε » Γ′ ⊢ ℕ ≡ Lift l (Unit s)
    ℕ≡Lift =
      let _ , _ , _ , _ , A′≡        = inversion-[] ⊢[t′]
          _ , ≡Lift-Unit , _ , _ , _ = ΠΣ-injectivity ⦃ ok = ε ⦄ A′≡
      in
      _ ,
      trans
        (_⊢_≡_.sym $ _⊢_≡_.univ $
         natrec-suc ⊢Lift-Unit (ℕⱼ ⊢Γ′∙ℕ∙U) (zeroⱼ εε))
        (≡Lift-Unit (refl (sucⱼ (zeroⱼ εε))))

    bad : ⊥
    bad = Lift≢ℕ ⦃ ok = ε ⦄ (sym (ℕ≡Lift .proj₂))

opaque
  unfolding Erased

  -- If Erased is allowed, then another form of inversion for [] also
  -- does not hold.

  ¬-inversion-[] :
    Erased-allowed s →
    ¬ (∀ {m n} {Γ : Cons m n} {t A : Term n} →
       Γ ⊢ [ t ] ∷ A →
       ∃₂ λ B l → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Erased l B)
  ¬-inversion-[] Erased-ok inversion-[] =
    ¬-inversion-[]′ Erased-ok λ ⊢[] →
    let B , l , ⊢t , A≡ = inversion-[] ⊢[] in
    B , 𝟘 , wk1 l , ⊢t , A≡
