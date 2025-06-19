------------------------------------------------------------------------
-- Some inversion lemmas related to typing and the weak variant of
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

  -- If Erased is allowed, then a certain form of inversion for erased
  -- does not hold.

  ¬-inversion-erased′ :
    Erasedʷ-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ erased A t ∷ A →
       ∃₂ λ q u → Γ ⊢ t ∷ Σʷ 𝟘 , q ▷ A ▹ Unitʷ (wk1 u))
  ¬-inversion-erased′ (Unit-ok , Σʷ-ok) inversion-erased = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ : Term 0
    t′ = prodʷ 𝟘 zero zero

    A′ : Term 0
    A′ = ℕ

    ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ∙ ℕⱼ ε

    ⊢t′₁ : Γ′ ⊢ t′ ∷ Σʷ 𝟘 , 𝟘 ▷ ℕ ▹ ℕ
    ⊢t′₁ = prodⱼ (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) Σʷ-ok

    ⊢erased-t′ : Γ′ ⊢ erased A′ t′ ∷ A′
    ⊢erased-t′ = fstʷⱼ ⊢t′₁

    erased-t′≡zero : Γ′ ⊢ erased A′ t′ ≡ zero ∷ A′
    erased-t′≡zero = fstʷ-β-≡ (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) Σʷ-ok

    ⊢t′₂ : ∃₂ λ q u → Γ′ ⊢ t′ ∷ Σʷ 𝟘 , q ▷ A′ ▹ Unitʷ (wk1 u)
    ⊢t′₂ = inversion-erased ⊢erased-t′

    ⊢snd-t′ :
      ∃ λ u → Γ′ ⊢ sndʷ 𝟘 (⊢t′₂ .proj₁) A′ (Unitʷ (wk1 u)) t′ ∷ Unitʷ u
    ⊢snd-t′ =
      let _ , u , ⊢t′ = ⊢t′₂ in
      u , PE.subst (_⊢_∷_ _ _) (wk1-sgSubst _ _) (sndʷⱼ ⊢t′)

    ℕ≡Unit : ∃ λ l → Γ′ ⊢ ℕ ≡ Unitʷ l
    ℕ≡Unit =
      let u , ⊢snd-t′ = ⊢snd-t′ in
      case inversion-prodrec ⊢snd-t′ of
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
      let ⊢σ : Γ′ ⊢ˢʷ consSubst (sgSubst zero) zero ∷ (Γ′ ∙ F ∙ G)
          ⊢σ = →⊢ˢʷ∷∙
                 (→⊢ˢʷ∷∙ (⊢ˢʷ∷-idSubst ε) $
                  PE.subst (_⊢_∷_ _ _) (PE.sym (subst-id F)) ⊢zero″)
                 (conv ⊢zero′ (sym G₀≡G′₀))
      in
      case PE.subst₂ (_⊢_≡_ _)
             (PE.cong Unitʷ
                (wk1 u [ fstʷ 𝟘 (wk1 A′) (var x0) ]↑
                   [ prodʷ 𝟘 (var x1) (var x0) ]↑² [ zero , zero ]₁₀      ≡⟨ PE.cong _[ _ , _ ]₁₀ $ PE.cong _[ _ ]↑² $ wk1-[][]↑ {t = u} 1 ⟩

                 wk1 u [ prodʷ 𝟘 (var x1) (var x0) ]↑² [ zero , zero ]₁₀  ≡⟨ PE.cong _[ _ , _ ]₁₀ $ wk1-[][]↑ {t = u} 2 ⟩

                 wk[ 2 ] u [ zero , zero ]₁₀                              ≡⟨ wk2-[,] ⟩

                 u                                                        ∎))
             (wk1-tail G)
             (subst-⊢≡ Unit≡′ (refl-⊢ˢʷ≡∷ ⊢σ)) of λ
        Unit≡″ →
      u , sym (trans Unit≡″ (trans G₀≡G′₀ ≡ℕ′)) }

    bad : ⊥
    bad = ℕ≢Unitⱼ ⦃ ok = ε ⦄ (ℕ≡Unit .proj₂)

opaque

  -- If Erased is allowed, then another form of inversion for erased
  -- also does not hold.

  ¬-inversion-erased :
    Erasedʷ-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ erased A t ∷ A →
       Γ ⊢ t ∷ Erased A)
  ¬-inversion-erased Erased-ok inversion-erased =
    ¬-inversion-erased′ Erased-ok λ ⊢erased →
    _ , _ , inversion-erased ⊢erased
