------------------------------------------------------------------------
-- Some inversion lemmas related to typing and Erased with η-equality.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality

module Graded.Derived.Erased.Eta.Typed.Inversion
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
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Substitution R

open import Definition.Untyped M as U hiding (_∷_)
open import Graded.Derived.Erased.Eta.Untyped 𝕄
open import Graded.Derived.Erased.Untyped 𝕄 𝕤 hiding (erased)

open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

open import Graded.Derived.Erased.Typed.Inversion R 𝕤 public

private variable
  Γ     : Con Term _
  A B t : Term _

opaque

  -- An inversion lemma for erased.
  --
  -- TODO: Make it possible to replace the conclusion with
  --
  --   Γ ⊢ t ∷ Erased A × Erased-allowed?

  inversion-erased :
    Γ ⊢ erased t ∷ A →
    ∃₂ λ q B → Γ ⊢ t ∷ Σˢ 𝟘 , q ▷ A ▹ B × Σˢ-allowed 𝟘 q
  inversion-erased ⊢erased =
    case inversion-fst ⊢erased of λ {
      (_ , C , q , ⊢B , ⊢C , ⊢t , ≡B) →
    case ⊢∷ΠΣ→ΠΣ-allowed ⊢t of λ {
      Σˢ-ok →
      q
    , C
    , conv ⊢t (ΠΣ-cong ⊢B (_⊢_≡_.sym ≡B) (refl ⊢C) Σˢ-ok)
    , Σˢ-ok }}

opaque

  -- If Erased is allowed, then a certain form of inversion for erased
  -- does not hold.

  ¬-inversion-erased′ :
    Erasedˢ-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ erased t ∷ A →
       ∃ λ q → Γ ⊢ t ∷ Σˢ 𝟘 , q ▷ A ▹ Unitˢ)
  ¬-inversion-erased′ (Unit-ok , Σˢ-ok) inversion-erased = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ : Term 0
    t′ = prodˢ 𝟘 zero zero

    A′ : Term 0
    A′ = ℕ

    ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ε ∙ ℕⱼ ε

    ⊢t′₁ : Γ′ ⊢ t′ ∷ Σˢ 𝟘 , 𝟘 ▷ ℕ ▹ ℕ
    ⊢t′₁ = prodⱼ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) Σˢ-ok

    ⊢erased-t′ : Γ′ ⊢ erased t′ ∷ A′
    ⊢erased-t′ = fstⱼ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) ⊢t′₁

    erased-t′≡zero : Γ′ ⊢ erased t′ ≡ zero ∷ A′
    erased-t′≡zero =
      Σ-β₁ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) PE.refl Σˢ-ok

    ⊢t′₂ : ∃ λ q → Γ′ ⊢ t′ ∷ Σˢ 𝟘 , q ▷ A′ ▹ Unitˢ
    ⊢t′₂ = inversion-erased ⊢erased-t′

    ⊢snd-t′ : Γ′ ⊢ snd 𝟘 t′ ∷ Unitˢ
    ⊢snd-t′ = sndⱼ (ℕⱼ ε) (Unitⱼ ⊢Γ′∙ℕ Unit-ok) (⊢t′₂ .proj₂)

    ℕ≡Unit : Γ′ ⊢ ℕ ≡ Unitˢ
    ℕ≡Unit =
      case inversion-snd ⊢snd-t′ of
        λ (_ , _ , _ , _ , _ , ⊢t′ , Unit≡) →
      case inversion-prod ⊢t′ of
        λ (_ , _ , _ , _ , _ , ⊢zero , ⊢zero′ , Σ≡Σ , _) →
      case Σ-injectivity Σ≡Σ of
        λ (F≡F′ , G≡G′ , _ , _ , _) →
      case inversion-zero ⊢zero of
        λ ≡ℕ →
      case inversion-zero ⊢zero′ of
        λ ≡ℕ′ →
      _⊢_≡_.sym $
      _⊢_≡_.trans Unit≡ $
      trans (substTypeEq G≡G′ $
         conv erased-t′≡zero (_⊢_≡_.sym (trans F≡F′ ≡ℕ)))
      ≡ℕ′

    bad : ⊥
    bad = ℕ≢Unitⱼ ℕ≡Unit

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
    _ , inversion-erased ⊢erased
