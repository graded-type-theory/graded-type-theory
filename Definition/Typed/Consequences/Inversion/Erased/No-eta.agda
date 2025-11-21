------------------------------------------------------------------------
-- Lemmas related to inversion for typing for the weak variant of
-- Erased
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality

module Definition.Typed.Consequences.Inversion.Erased.No-eta
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R

open import Definition.Untyped M as U
open import Definition.Untyped.Erased 𝕄 𝕨 hiding (erased)
open import Definition.Untyped.Erased.No-eta 𝕄
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

open import Definition.Typed.Consequences.Inversion.Erased R 𝕨 public

opaque
  unfolding erased fst⟨_⟩

  -- If Erased is allowed, then a certain form of inversion for erased
  -- does not hold.

  ¬-inversion-erased′ :
    Erasedʷ-allowed →
    ¬ (∀ {m n} {Γ : Cons m n} {t A : Term n} →
       Γ ⊢ erased A t ∷ A →
       ∃₂ λ q l → Γ ⊢ t ∷ Σʷ 𝟘 , q ▷ A ▹ Lift l Unitʷ)
  ¬-inversion-erased′ (Unit-ok , Σʷ-ok) inversion-erased = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ : Term 0
    t′ = prodʷ 𝟘 zero zero

    A′ : Term 0
    A′ = ℕ

    ⊢Γ′∙ℕ : ε »⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ∙ ⊢ℕ εε

    ⊢t′₁ : ε » Γ′ ⊢ t′ ∷ Σʷ 𝟘 , 𝟘 ▷ ℕ ▹ ℕ
    ⊢t′₁ = prodⱼ (⊢ℕ ⊢Γ′∙ℕ) (zeroⱼ εε) (zeroⱼ εε) Σʷ-ok

    ⊢erased-t′ : ε » Γ′ ⊢ erased A′ t′ ∷ A′
    ⊢erased-t′ = fstʷⱼ ⊢t′₁

    erased-t′≡zero : ε » Γ′ ⊢ erased A′ t′ ≡ zero ∷ A′
    erased-t′≡zero = fstʷ-β-≡ (⊢ℕ ⊢Γ′∙ℕ) (zeroⱼ εε) (zeroⱼ εε) Σʷ-ok

    ⊢t′₂ : ∃₂ λ q l → ε » Γ′ ⊢ t′ ∷ Σʷ 𝟘 , q ▷ A′ ▹ Lift l Unitʷ
    ⊢t′₂ = inversion-erased ⊢erased-t′

    ⊢snd-t′ :
      ∃₂ λ l₁ l₂ →
        ε » Γ′ ⊢ sndʷ 𝟘 (⊢t′₂ .proj₁) A′ (Lift l₁ Unitʷ) t′ ∷
        Lift l₂ Unitʷ
    ⊢snd-t′ =
      let _ , l , ⊢t′ = ⊢t′₂ in
      l , _ , sndʷⱼ ⊢t′

    ℕ≡Lift : ∃ λ l → ε » Γ′ ⊢ ℕ ≡ Lift l Unitʷ
    ℕ≡Lift =
      case inversion-prodrec (⊢snd-t′ .proj₂ .proj₂) of
        λ (F , G , _ , _ , _ , _ , ⊢t′ , ⊢x₀ , Unit≡) →
      case inversion-var ⊢x₀ of λ {
        (Q , here , Unit≡′) →
      case inversion-prod ⊢t′ of
        λ (F′ , G′ , _ , _ , _ , ⊢zero , ⊢zero′ , Σ≡Σ , _) →
      case ΠΣ-injectivity ⦃ ok = ε ⦄ Σ≡Σ of
        λ (F≡F′ , G≡G′ , _ , _ , _) →
      case inversion-zero ⊢zero of
        λ ≡ℕ →
      case inversion-zero ⊢zero′ of
        λ ≡ℕ′ →
      case conv ⊢zero (sym F≡F′) of
        λ ⊢zero″ →
      case G≡G′ (refl ⊢zero″)  of
        λ G₀≡G′₀ →
      let ⊢σ : ε » Γ′ ⊢ˢʷ consSubst (sgSubst zero) zero ∷ (Γ′ ∙ F ∙ G)
          ⊢σ = →⊢ˢʷ∷∙
                 (→⊢ˢʷ∷∙ (⊢ˢʷ∷-idSubst εε) $
                  PE.subst (_⊢_∷_ _ _) (PE.sym (subst-id F)) ⊢zero″)
                 (conv ⊢zero′ (sym G₀≡G′₀))
      in
      case PE.subst (_⊢_≡_ _ _)
             (wk1-tail G)
             (subst-⊢≡ Unit≡′ (refl-⊢ˢʷ≡∷ ⊢σ)) of λ
        Unit≡″ →
      _ , sym (trans Unit≡″ (trans G₀≡G′₀ ≡ℕ′)) }

    bad : ⊥
    bad = Lift≢ℕ ⦃ ok = ε ⦄ (sym (ℕ≡Lift .proj₂))

opaque
  unfolding Erased

  -- If Erased is allowed, then another form of inversion for erased
  -- also does not hold.

  ¬-inversion-erased :
    Erasedʷ-allowed →
    ¬ (∀ {m n} {Γ : Cons m n} {t A : Term n} →
       Γ ⊢ erased A t ∷ A →
       ∃ λ l → Γ ⊢ t ∷ Erased l A)
  ¬-inversion-erased Erased-ok inversion-erased =
    ¬-inversion-erased′ Erased-ok λ ⊢erased →
    _ , _ , inversion-erased ⊢erased .proj₂
