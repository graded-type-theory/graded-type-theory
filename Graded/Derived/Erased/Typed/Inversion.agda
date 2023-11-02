------------------------------------------------------------------------
-- Some inversion lemmas related to typing and Erased
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality

module Graded.Derived.Erased.Typed.Inversion
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Type-restrictions M)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Substitution R

open import Definition.Untyped M as U hiding (_∷_)

open import Graded.Derived.Erased.Untyped 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private variable
  Γ     : Con Term _
  A B t : Term _

-- The type Erased A is only allowed if Erased-allowed holds.

Erased-allowed : Set a
Erased-allowed = Unit-allowed × Σₚ-allowed 𝟘 𝟘

opaque

  -- An inversion lemma for Erased.

  inversion-Erased-∷ :
    Γ ⊢ Erased A ∷ B →
    Γ ⊢ A ∷ U × Erased-allowed × Γ ⊢ B ≡ U
  inversion-Erased-∷ ⊢Erased =
    case inversion-ΠΣ-U ⊢Erased of λ {
      (⊢A , ⊢Unit , B≡ , Σₚ-ok) →
    ⊢A , (inversion-Unit (univ ⊢Unit) , Σₚ-ok) , B≡ }

opaque

  -- Another inversion lemma for Erased.

  inversion-Erased : Γ ⊢ Erased A → Γ ⊢ A × Erased-allowed
  inversion-Erased ⊢Erased =
    case inversion-ΠΣ ⊢Erased of λ {
      (⊢A , ⊢Unit , Σₚ-ok) →
    ⊢A , inversion-Unit ⊢Unit , Σₚ-ok }

opaque

  -- An inversion lemma for [_].
  --
  -- TODO: Make it possible to replace the conclusion with
  --
  --   ∃ λ B → Γ ⊢ t ∷ B × Erased-allowed × Γ ⊢ A ≡ Erased B?

  inversion-[] :
    Γ ⊢ [ t ] ∷ A →
    ∃₃ λ B q C →
       Γ ⊢ t ∷ B ×
       (Unit-allowed × Σₚ-allowed 𝟘 q) ×
       Γ ⊢ A ≡ Σₚ 𝟘 , q ▷ B ▹ C ×
       Γ ⊢ C U.[ t ]₀ ≡ Unit
  inversion-[] ⊢[] =
    case inversion-prod ⊢[] of λ {
      (B , C , q , ⊢B , _ , ⊢t , ⊢star , A≡ , Σₚ-ok) →
    case inversion-star ⊢star of λ {
      (≡Unit , Unit-ok) →
    B , q , C , ⊢t , (Unit-ok , Σₚ-ok) , A≡ , ≡Unit }}

opaque

  -- Another inversion lemma for [_].

  inversion-[]′ :
    Γ ⊢ [ t ] ∷ Erased A →
    Γ ⊢ t ∷ A × Erased-allowed
  inversion-[]′ ⊢[] =
    case inversion-[] ⊢[] of λ {
      (_ , _ , _ , ⊢t , Erased-ok , Erased-A≡ , _) →
    case Σ-injectivity Erased-A≡ of λ {
      (A≡ , _ , _ , PE.refl , _) →
    conv ⊢t (_⊢_≡_.sym A≡) , Erased-ok }}

opaque

  -- If Erased is allowed, then a certain form of inversion for [_]
  -- does not hold.

  ¬-inversion-[]′ :
    Erased-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ [ t ] ∷ A →
       ∃₂ λ B q → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Σₚ 𝟘 , q ▷ B ▹ Unit)
  ¬-inversion-[]′ (Unit-ok , Σₚ-ok) inversion-[] = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ : Term 0
    t′ = zero

    A′ : Term 0
    A′ = Σₚ 𝟘 , 𝟘 ▷ ℕ ▹ natrec 𝟙 𝟙 𝟙 U Unit ℕ (var x0)

    ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ε ∙ ℕⱼ ε

    ⊢Γ′∙ℕ∙ℕ : ⊢ Γ′ ∙ ℕ ∙ ℕ
    ⊢Γ′∙ℕ∙ℕ = ⊢Γ′∙ℕ ∙ ℕⱼ ⊢Γ′∙ℕ

    ⊢Γ′∙ℕ∙U : ⊢ Γ′ ∙ ℕ ∙ U
    ⊢Γ′∙ℕ∙U = ⊢Γ′∙ℕ ∙ Uⱼ ⊢Γ′∙ℕ

    ⊢[t′] : Γ′ ⊢ [ t′ ] ∷ A′
    ⊢[t′] = prodⱼ
      (ℕⱼ ε)
      (univ (natrecⱼ
               (Uⱼ ⊢Γ′∙ℕ∙ℕ)
               (Unitⱼ ⊢Γ′∙ℕ Unit-ok)
               (ℕⱼ (⊢Γ′∙ℕ∙ℕ ∙ Uⱼ ⊢Γ′∙ℕ∙ℕ))
               (var ⊢Γ′∙ℕ here)))
      (zeroⱼ ε)
      (conv (starⱼ ε Unit-ok)
         (_⊢_≡_.sym $
          univ (natrec-zero (Uⱼ ⊢Γ′∙ℕ) (Unitⱼ ε Unit-ok) (ℕⱼ ⊢Γ′∙ℕ∙U))))
      Σₚ-ok

    ℕ≡Unit : Γ′ ⊢ ℕ ≡ Unit
    ℕ≡Unit =
      case inversion-[] ⊢[t′] of
        λ (_ , _ , _ , A′≡) →
      case Σ-injectivity A′≡ of
        λ (_ , ≡Unit , _ , _ , _) →
      trans
        (_⊢_≡_.sym $ _⊢_≡_.univ $
         natrec-suc (Uⱼ ⊢Γ′∙ℕ) (Unitⱼ ε Unit-ok) (ℕⱼ ⊢Γ′∙ℕ∙U) (zeroⱼ ε))
        (substTypeEq ≡Unit (refl (sucⱼ (zeroⱼ ε))))

    bad : ⊥
    bad = ℕ≢Unitⱼ ℕ≡Unit

opaque

  -- If Erased is allowed, then another form of inversion for [] also
  -- does not hold.

  ¬-inversion-[] :
    Erased-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ [ t ] ∷ A →
       ∃ λ B → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Erased B)
  ¬-inversion-[] Erased-ok inversion-[] =
    ¬-inversion-[]′ Erased-ok λ ⊢[] →
    case inversion-[] ⊢[] of λ {
      (B , ⊢t , A≡) →
    B , 𝟘 , ⊢t , A≡ }

opaque

  -- An inversion lemma for erased.
  --
  -- TODO: Make it possible to replace the conclusion with
  --
  --   Γ ⊢ t ∷ Erased A × Erased-allowed?

  inversion-erased :
    Γ ⊢ erased t ∷ A →
    ∃₂ λ q B → Γ ⊢ t ∷ Σₚ 𝟘 , q ▷ A ▹ B × Σₚ-allowed 𝟘 q
  inversion-erased ⊢erased =
    case inversion-fst ⊢erased of λ {
      (_ , C , q , ⊢B , ⊢C , ⊢t , ≡B) →
    case ⊢∷ΠΣ→ΠΣ-allowed ⊢t of λ {
      Σₚ-ok →
      q
    , C
    , conv ⊢t (ΠΣ-cong ⊢B (_⊢_≡_.sym ≡B) (refl ⊢C) Σₚ-ok)
    , Σₚ-ok }}

opaque

  -- If Erased is allowed, then a certain form of inversion for erased
  -- does not hold.

  ¬-inversion-erased′ :
    Erased-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ erased t ∷ A →
       ∃ λ q → Γ ⊢ t ∷ Σₚ 𝟘 , q ▷ A ▹ Unit)
  ¬-inversion-erased′ (Unit-ok , Σₚ-ok) inversion-erased = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ : Term 0
    t′ = prodₚ 𝟘 zero zero

    A′ : Term 0
    A′ = ℕ

    ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ε ∙ ℕⱼ ε

    ⊢t′₁ : Γ′ ⊢ t′ ∷ Σₚ 𝟘 , 𝟘 ▷ ℕ ▹ ℕ
    ⊢t′₁ = prodⱼ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) Σₚ-ok

    ⊢erased-t′ : Γ′ ⊢ erased t′ ∷ A′
    ⊢erased-t′ = fstⱼ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) ⊢t′₁

    erased-t′≡zero : Γ′ ⊢ erased t′ ≡ zero ∷ A′
    erased-t′≡zero =
      Σ-β₁ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) PE.refl Σₚ-ok

    ⊢t′₂ : ∃ λ q → Γ′ ⊢ t′ ∷ Σₚ 𝟘 , q ▷ A′ ▹ Unit
    ⊢t′₂ = inversion-erased ⊢erased-t′

    ⊢snd-t′ : Γ′ ⊢ snd 𝟘 t′ ∷ Unit
    ⊢snd-t′ = sndⱼ (ℕⱼ ε) (Unitⱼ ⊢Γ′∙ℕ Unit-ok) (⊢t′₂ .proj₂)

    ℕ≡Unit : Γ′ ⊢ ℕ ≡ Unit
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
      trans
        (substTypeEq G≡G′ $
         conv erased-t′≡zero (_⊢_≡_.sym (trans F≡F′ ≡ℕ)))
      ≡ℕ′

    bad : ⊥
    bad = ℕ≢Unitⱼ ℕ≡Unit

opaque

  -- If Erased is allowed, then another form of inversion for erased
  -- also does not hold.

  ¬-inversion-erased :
    Erased-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ erased t ∷ A →
       Γ ⊢ t ∷ Erased A)
  ¬-inversion-erased Erased-ok inversion-erased =
    ¬-inversion-erased′ Erased-ok λ ⊢erased →
    _ , inversion-erased ⊢erased
