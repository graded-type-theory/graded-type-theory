------------------------------------------------------------------------
-- Lemmas related to inversion for typing for the strong variant of
-- Erased
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality

module Definition.Typed.Consequences.Inversion.Erased.Eta
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M as U
open import Definition.Untyped.Erased 𝕄 𝕤 hiding (erased)
open import Definition.Untyped.Erased.Eta 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

open import Definition.Typed.Consequences.Inversion.Erased R 𝕤 public

opaque
  unfolding erased

  -- If Erased is allowed, then a certain form of inversion for erased
  -- does not hold.

  ¬-inversion-erased′ :
    Erasedˢ-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ erased t ∷ A →
       ∃₂ λ q l → Γ ⊢ t ∷ Σˢ 𝟘 , q ▷ A ▹ Lift l Unitˢ)
  ¬-inversion-erased′ (Unit-ok , Σˢ-ok) inversion-erased = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ : Term 0
    t′ = prodˢ 𝟘 zero zero

    A′ : Term 0
    A′ = ℕ

    ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ∙ ⊢ℕ ε

    ⊢t′₁ : Γ′ ⊢ t′ ∷ Σˢ 𝟘 , 𝟘 ▷ ℕ ▹ ℕ
    ⊢t′₁ = prodⱼ (⊢ℕ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) Σˢ-ok

    ⊢erased-t′ : Γ′ ⊢ erased t′ ∷ A′
    ⊢erased-t′ = fstⱼ (⊢ℕ ⊢Γ′∙ℕ) ⊢t′₁

    erased-t′≡zero : Γ′ ⊢ erased t′ ≡ zero ∷ A′
    erased-t′≡zero =
      Σ-β₁ (⊢ℕ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) PE.refl Σˢ-ok

    ⊢t′₂ : ∃₂ λ q l → Γ′ ⊢ t′ ∷ Σˢ 𝟘 , q ▷ A′ ▹ Lift l Unitˢ
    ⊢t′₂ = inversion-erased ⊢erased-t′

    ⊢snd-t′ : ∃ λ l → Γ′ ⊢ snd 𝟘 t′ ∷ Lift l Unitˢ
    ⊢snd-t′ =
      let _ , _ , ⊢t′        = ⊢t′₂
          _ , ⊢Lift-Unit , _ = inversion-ΠΣ (wf-⊢∷ ⊢t′)
      in
      _ , sndⱼ ⊢Lift-Unit ⊢t′

    ℕ≡Lift : ∃ λ l → Γ′ ⊢ ℕ ≡ Lift l Unitˢ
    ℕ≡Lift =
      case inversion-snd (⊢snd-t′ .proj₂) of
        λ (_ , _ , _ , _ , _ , ⊢t′ , Unit≡) →
      case inversion-prod ⊢t′ of
        λ (_ , _ , _ , _ , _ , ⊢zero , ⊢zero′ , Σ≡Σ , _) →
      case ΠΣ-injectivity ⦃ ok = ε ⦄ Σ≡Σ of
        λ (F≡F′ , G≡G′ , _ , _ , _) →
      case inversion-zero ⊢zero of
        λ ≡ℕ →
      case inversion-zero ⊢zero′ of
        λ ≡ℕ′ →
      _ ,
      (_⊢_≡_.sym $
         trans Unit≡ $
         trans (G≡G′ (conv erased-t′≡zero (_⊢_≡_.sym (trans F≡F′ ≡ℕ))))
           ≡ℕ′)

    bad : ⊥
    bad = Lift≢ℕ ⦃ ok = ε ⦄ (sym (ℕ≡Lift .proj₂))

opaque
  unfolding Erased

  -- If Erased is allowed, then another form of inversion for erased
  -- also does not hold.

  ¬-inversion-erased :
    Erasedˢ-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ erased t ∷ A →
       ∃ λ l → Γ ⊢ t ∷ Erased l A)
  ¬-inversion-erased Erased-ok inversion-erased =
    ¬-inversion-erased′ Erased-ok λ ⊢erased →
    _ , _ , inversion-erased ⊢erased .proj₂
