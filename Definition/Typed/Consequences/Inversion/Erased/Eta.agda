------------------------------------------------------------------------
-- Some inversion lemmas related to typing and the strong variant of
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
open import Definition.Typed.Substitution R

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

  -- If Erased is allowed, then a certain form of inversion for erased
  -- does not hold.

  ¬-inversion-erased′ :
    Erasedˢ-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ erased t ∷ A →
       ∃₂ λ q l → Γ ⊢ t ∷ Σˢ 𝟘 , q ▷ A ▹ Unitˢ l)
  ¬-inversion-erased′ (Unit-ok , Σˢ-ok) inversion-erased = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ : Term 0
    t′ = prodˢ 𝟘 zero zero

    A′ : Term 0
    A′ = ℕ

    ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ∙ ℕⱼ ε

    ⊢t′₁ : Γ′ ⊢ t′ ∷ Σˢ 𝟘 , 𝟘 ▷ ℕ ▹ ℕ
    ⊢t′₁ = prodⱼ (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) Σˢ-ok

    ⊢erased-t′ : Γ′ ⊢ erased t′ ∷ A′
    ⊢erased-t′ = fstⱼ (ℕⱼ ⊢Γ′∙ℕ) ⊢t′₁

    erased-t′≡zero : Γ′ ⊢ erased t′ ≡ zero ∷ A′
    erased-t′≡zero =
      Σ-β₁ (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) PE.refl Σˢ-ok

    ⊢t′₂ : ∃₂ λ q l → Γ′ ⊢ t′ ∷ Σˢ 𝟘 , q ▷ A′ ▹ Unitˢ l
    ⊢t′₂ = inversion-erased ⊢erased-t′

    ⊢snd-t′ : ∃ λ l → Γ′ ⊢ snd 𝟘 t′ ∷ Unitˢ l
    ⊢snd-t′ = _ , sndⱼ (Unitⱼ ⊢Γ′∙ℕ Unit-ok) (⊢t′₂ .proj₂ .proj₂)

    ℕ≡Unit : ∃ λ l → Γ′ ⊢ ℕ ≡ Unitˢ l
    ℕ≡Unit =
      case ⊢snd-t′ of λ
        (l , ⊢snd-t′) →
      case inversion-snd ⊢snd-t′ of
        λ (_ , _ , _ , _ , _ , ⊢t′ , Unit≡) →
      case inversion-prod ⊢t′ of
        λ (_ , _ , _ , _ , _ , ⊢zero , ⊢zero′ , Σ≡Σ , _) →
      case ΠΣ-injectivity ⦃ ok = ε ⦄ Σ≡Σ of
        λ (F≡F′ , G≡G′ , _ , _ , _) →
      case inversion-zero ⊢zero of
        λ ≡ℕ →
      case inversion-zero ⊢zero′ of
        λ ≡ℕ′ →
        l
      , (_⊢_≡_.sym $
         trans Unit≡ $
         trans (G≡G′ (conv erased-t′≡zero (_⊢_≡_.sym (trans F≡F′ ≡ℕ))))
           ≡ℕ′)

    bad : ⊥
    bad = ℕ≢Unitⱼ ⦃ ok = ε ⦄ (ℕ≡Unit .proj₂)

opaque

  -- If Erased is allowed, then another form of inversion for erased
  -- also does not hold.

  ¬-inversion-erased :
    Erasedˢ-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ erased t ∷ A →
       Γ ⊢ t ∷ Erased A)
  ¬-inversion-erased Erased-ok inversion-erased =
    ¬-inversion-erased′ Erased-ok λ ⊢erased →
    _ , _ , inversion-erased ⊢erased
