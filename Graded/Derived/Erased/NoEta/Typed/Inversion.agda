------------------------------------------------------------------------
-- Some inversion lemmas related to typing and the weak variant of
-- Erased
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality

module Graded.Derived.Erased.NoEta.Typed.Inversion
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.DerivedRules.Sigma R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R

open import Definition.Untyped M as U
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
open import Graded.Derived.Erased.NoEta.Untyped 𝕄
open import Graded.Derived.Erased.Untyped 𝕄 𝕨 hiding (erased)

open import Tools.Empty
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

open import Graded.Derived.Erased.Typed.Inversion R 𝕨 public

private variable
  Γ       : Con Term _
  A B C t : Term _

opaque

  -- An inversion lemma for erased.
  --
  -- TODO: Make it possible to replace the conclusion with
  --
  --   Γ ⊢ t ∷ Erased A × Erased-allowed?

  inversion-erased :
    Γ ⊢ erased C t ∷ A →
    ∃₂ λ q B → Γ ⊢ t ∷ Σʷ 𝟘 , q ▷ A ▹ B × Σʷ-allowed 𝟘 q
  inversion-erased {C = C} {t} ⊢erased =
    case inversion-fstʷ ⊢erased of λ
      (q , B , ⊢t , A≡C) →
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ
      (_ , ⊢B , Σ-ok) →
    q , B , conv ⊢t (ΠΣ-cong (sym A≡C) (refl ⊢B) Σ-ok) , Σ-ok


opaque

  -- If Erased is allowed, then a certain form of inversion for erased
  -- does not hold.

  ¬-inversion-erased′ :
    Erasedʷ-allowed →
    ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
       Γ ⊢ erased A t ∷ A →
       ∃₂ λ q l → Γ ⊢ t ∷ Σʷ 𝟘 , q ▷ A ▹ Unitʷ l)
  ¬-inversion-erased′ (Unit-ok , Σʷ-ok) inversion-erased = bad
    where
    Γ′ : Con Term 0
    Γ′ = ε

    t′ : Term 0
    t′ = prodʷ 𝟘 zero zero

    A′ : Term 0
    A′ = ℕ

    ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
    ⊢Γ′∙ℕ = ε ∙ ℕⱼ ε

    ⊢t′₁ : Γ′ ⊢ t′ ∷ Σʷ 𝟘 , 𝟘 ▷ ℕ ▹ ℕ
    ⊢t′₁ = prodⱼ (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) Σʷ-ok

    ⊢erased-t′ : Γ′ ⊢ erased A′ t′ ∷ A′
    ⊢erased-t′ = fstʷⱼ ⊢t′₁

    erased-t′≡zero : Γ′ ⊢ erased A′ t′ ≡ zero ∷ A′
    erased-t′≡zero = fstʷ-β-≡ (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) Σʷ-ok

    ⊢t′₂ : ∃₂ λ q l → Γ′ ⊢ t′ ∷ Σʷ 𝟘 , q ▷ A′ ▹ Unitʷ l
    ⊢t′₂ = inversion-erased ⊢erased-t′

    ⊢snd-t′ :
      ∃ λ l → Γ′ ⊢ sndʷ 𝟘 (⊢t′₂ .proj₁) A′ (Unitʷ l) t′ ∷ Unitʷ l
    ⊢snd-t′ = _ , sndʷⱼ (⊢t′₂ .proj₂ .proj₂)

    ℕ≡Unit : ∃ λ l → Γ′ ⊢ ℕ ≡ Unitʷ l
    ℕ≡Unit =
      let l , ⊢snd-t′ = ⊢snd-t′ in
      case inversion-prodrec ⊢snd-t′ of
        λ (F , G , _ , _ , _ , _ , ⊢t′ , ⊢x₀ , Unit≡) →
      case inversion-var ⊢x₀ of λ {
        (Q , here , Unit≡′) →
      case inversion-prod ⊢t′ of
        λ (F′ , G′ , _ , _ , _ , ⊢zero , ⊢zero′ , Σ≡Σ , _) →
      case Σ-injectivity Σ≡Σ of
        λ (F≡F′ , G≡G′ , _ , _ , _) →
      case inversion-zero ⊢zero of
        λ ≡ℕ →
      case inversion-zero ⊢zero′ of
        λ ≡ℕ′ →
      case conv ⊢zero (sym F≡F′) of
        λ ⊢zero″ →
      case substTypeEq G≡G′ (refl ⊢zero″)  of
        λ G₀≡G′₀ →
      let ⊢σ : Γ′ ⊢ˢ consSubst (sgSubst zero) zero ∷ (Γ′ ∙ F ∙ G)
          ⊢σ = (idSubst′ ε , PE.subst (Γ′ ⊢ zero ∷_) (PE.sym (subst-id F)) ⊢zero″)
                , conv ⊢zero′ (sym G₀≡G′₀)
      in case PE.subst (_⊢_≡_ _ _) (wk1-tail G)
               (substitutionEq Unit≡′ (substRefl ⊢σ) ε) of
        λ Unit≡″ →
      l , sym (trans Unit≡″ (trans G₀≡G′₀ ≡ℕ′)) }

    bad : ⊥
    bad = ℕ≢Unitⱼ (ℕ≡Unit .proj₂)

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
