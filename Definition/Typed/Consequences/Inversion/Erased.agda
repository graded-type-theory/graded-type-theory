------------------------------------------------------------------------
-- Some inversion lemmas related to typing and Erased
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
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R

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

opaque

  -- An inversion lemma for [_].
  --
  -- See also Definition.Typed.Inversion.inversion-[].

  inversion-[]′ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ [ t ] ∷ Erased A →
    Γ ⊢ t ∷ A × Erased-allowed s
  inversion-[]′ ⊢[] =
    case inversion-[] ⊢[] of λ {
      (_ , _ , _ , ⊢t , Erased-ok , Erased-A≡ , _) →
    case ΠΣ-injectivity Erased-A≡ of λ {
      (A≡ , _ , _ , PE.refl , _) →
    conv ⊢t (_⊢_≡_.sym A≡) , Erased-ok }}

opaque

  -- If Erased is allowed, then a certain form of inversion for [_]
  -- does not hold.

  ¬-inversion-[]′ :
    Erased-allowed s →
    ¬ (∀ {m n} {Γ : Cons m n} {t A : Term n} →
       Γ ⊢ [ t ] ∷ A →
       ∃₂ λ B q → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Σ⟨ s ⟩ 𝟘 , q ▷ B ▹ Unit s 0)
  ¬-inversion-[]′ (Unit-ok , Σ-ok) inversion-[] = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ : Term 0
    t′ = zero

    A′ : Term 0
    A′ = Σ 𝟘 , 𝟘 ▷ ℕ ▹ natrec 𝟙 𝟙 𝟙 (U 0) Unit! ℕ (var x0)

    ⊢Γ′∙ℕ : ε »⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ∙ ℕⱼ εε

    ⊢Γ′∙ℕ∙ℕ : ε »⊢ Γ′ ∙ ℕ ∙ ℕ
    ⊢Γ′∙ℕ∙ℕ = ∙ ℕⱼ ⊢Γ′∙ℕ

    ⊢Γ′∙ℕ∙U : ε »⊢ Γ′ ∙ ℕ ∙ U 0
    ⊢Γ′∙ℕ∙U = ∙ Uⱼ ⊢Γ′∙ℕ

    ⊢[t′] : ε » Γ′ ⊢ [ t′ ] ∷ A′
    ⊢[t′] = prodⱼ
      (univ (natrecⱼ
               (Unitⱼ ⊢Γ′∙ℕ Unit-ok)
               (ℕⱼ (∙ Uⱼ ⊢Γ′∙ℕ∙ℕ))
               (var ⊢Γ′∙ℕ here)))
      (zeroⱼ εε)
      (conv (starⱼ εε Unit-ok)
         (_⊢_≡_.sym $
          univ (natrec-zero (Unitⱼ εε Unit-ok) (ℕⱼ ⊢Γ′∙ℕ∙U))))
      Σ-ok

    ℕ≡Unit : ε » Γ′ ⊢ ℕ ≡ Unit s 0
    ℕ≡Unit =
      case inversion-[] ⊢[t′] of
        λ (_ , _ , _ , A′≡) →
      case ΠΣ-injectivity ⦃ ok = ε ⦄ A′≡ of
        λ (_ , ≡Unit , _ , _ , _) →
      trans
        (_⊢_≡_.sym $ _⊢_≡_.univ $
         natrec-suc (Unitⱼ εε Unit-ok) (ℕⱼ ⊢Γ′∙ℕ∙U) (zeroⱼ εε))
        (≡Unit (refl (sucⱼ (zeroⱼ εε))))

    bad : ⊥
    bad = ℕ≢Unitⱼ ⦃ ok = ε ⦄ ℕ≡Unit

opaque

  -- If Erased is allowed, then another form of inversion for [] also
  -- does not hold.

  ¬-inversion-[] :
    Erased-allowed s →
    ¬ (∀ {m n} {Γ : Cons m n} {t A : Term n} →
       Γ ⊢ [ t ] ∷ A →
       ∃ λ B → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Erased B)
  ¬-inversion-[] Erased-ok inversion-[] =
    ¬-inversion-[]′ Erased-ok λ ⊢[] →
    case inversion-[] ⊢[] of λ {
      (B , ⊢t , A≡) →
    B , 𝟘 , ⊢t , A≡ }
