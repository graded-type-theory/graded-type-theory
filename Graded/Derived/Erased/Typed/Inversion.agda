------------------------------------------------------------------------
-- Some inversion lemmas related to typing and Erased
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
open import Definition.Untyped.NotParametrised using (Strength)

module Graded.Derived.Erased.Typed.Inversion
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
open import Definition.Typed.Substitution R

open import Definition.Untyped M as U
open import Definition.Untyped.Properties M

open import Graded.Derived.Erased.Untyped 𝕄 s

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private variable
  Γ     : Con Term _
  A B t : Term _

opaque

  -- An inversion lemma for Erased.

  inversion-Erased-∷ :
    Γ ⊢ Erased A ∷ B →
    ∃₂ λ l₁ l₂ → l₁ ≤ᵘ l₂ ×
      Γ ⊢ A ∷ U l₁ × Erased-allowed s × Γ ⊢ B ≡ U l₂
  inversion-Erased-∷ ⊢Erased =
    case inversion-ΠΣ-U ⊢Erased of λ {
      (_ , _ , ⊢A , ⊢Unit , B≡ , Σˢ-ok) →
    _ , _ , ≤ᵘ⊔ᵘʳ , ⊢A , (inversion-Unit (univ ⊢Unit) , Σˢ-ok) , B≡ }

opaque

  -- Another inversion lemma for Erased.

  inversion-Erased : Γ ⊢ Erased A → Γ ⊢ A × Erased-allowed s
  inversion-Erased ⊢Erased =
    case inversion-ΠΣ ⊢Erased of λ {
      (⊢A , ⊢Unit , Σˢ-ok) →
    ⊢A , inversion-Unit ⊢Unit , Σˢ-ok }

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
       (Unit-allowed s × Σ-allowed s 𝟘 q) ×
       Γ ⊢ A ≡ Σ⟨ s ⟩ 𝟘 , q ▷ B ▹ C ×
       Γ ⊢ C U.[ t ]₀ ≡ Unit s 0
  inversion-[] ⊢[] =
    case inversion-prod ⊢[] of λ {
      (B , C , q , ⊢B , _ , ⊢t , ⊢star , A≡ , Σˢ-ok) →
    case inversion-star ⊢star of λ {
      (≡Unit , Unit-ok) →
    B , q , C , ⊢t , (Unit-ok , Σˢ-ok) , A≡ , ≡Unit }}

opaque

  -- Another inversion lemma for [_].

  inversion-[]′ :
    Γ ⊢ [ t ] ∷ Erased A →
    Γ ⊢ t ∷ A × Erased-allowed s
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
    Erased-allowed s →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
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

    ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ∙ ℕⱼ ε

    ⊢Γ′∙ℕ∙ℕ : ⊢ Γ′ ∙ ℕ ∙ ℕ
    ⊢Γ′∙ℕ∙ℕ = ∙ ℕⱼ ⊢Γ′∙ℕ

    ⊢Γ′∙ℕ∙U : ⊢ Γ′ ∙ ℕ ∙ U 0
    ⊢Γ′∙ℕ∙U = ∙ Uⱼ ⊢Γ′∙ℕ

    ⊢[t′] : Γ′ ⊢ [ t′ ] ∷ A′
    ⊢[t′] = prodⱼ
      (univ (natrecⱼ
               (Unitⱼ ⊢Γ′∙ℕ Unit-ok)
               (ℕⱼ (∙ Uⱼ ⊢Γ′∙ℕ∙ℕ))
               (var ⊢Γ′∙ℕ here)))
      (zeroⱼ ε)
      (conv (starⱼ ε Unit-ok)
         (_⊢_≡_.sym $
          univ (natrec-zero (Unitⱼ ε Unit-ok) (ℕⱼ ⊢Γ′∙ℕ∙U))))
      Σ-ok

    ℕ≡Unit : Γ′ ⊢ ℕ ≡ Unit s 0
    ℕ≡Unit =
      case inversion-[] ⊢[t′] of
        λ (_ , _ , _ , A′≡) →
      case Σ-injectivity A′≡ of
        λ (_ , ≡Unit , _ , _ , _) →
      trans
        (_⊢_≡_.sym $ _⊢_≡_.univ $
         natrec-suc (Unitⱼ ε Unit-ok) (ℕⱼ ⊢Γ′∙ℕ∙U) (zeroⱼ ε))
        (substTypeEq ≡Unit (refl (sucⱼ (zeroⱼ ε))))

    bad : ⊥
    bad = ℕ≢Unitⱼ ℕ≡Unit

opaque

  -- If Erased is allowed, then another form of inversion for [] also
  -- does not hold.

  ¬-inversion-[] :
    Erased-allowed s →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ [ t ] ∷ A →
       ∃ λ B → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Erased B)
  ¬-inversion-[] Erased-ok inversion-[] =
    ¬-inversion-[]′ Erased-ok λ ⊢[] →
    case inversion-[] ⊢[] of λ {
      (B , ⊢t , A≡) →
    B , 𝟘 , ⊢t , A≡ }
