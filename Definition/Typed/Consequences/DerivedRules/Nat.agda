------------------------------------------------------------------------
-- Derived rules related to the natural number type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.DerivedRules.Nat
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Weakening R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    Γ : Con Term _
    A A′ A₁ A₂ n n′ s s′ t t₁ t₂ u u₁ u₂ v v₁ v₂ z z′ : Term _
    p q r : M

opaque

  -- Congruence of the type of the successor case in natrec.
  sucCong : ∀ {F G} → Γ ∙ ℕ ⊢ F ≡ G
          → Γ ∙ ℕ ∙ F ⊢ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑²
  sucCong F≡G with wfEq F≡G
  sucCong F≡G | ⊢Γ ∙ ⊢ℕ =
    let ⊢F , ⊢G = syntacticEq F≡G
    in subst↑²TypeEq F≡G (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ ∙ ⊢F) (there here))))

opaque

  sucCong′ : ∀ {F G} → Γ ∙ ℕ ⊢ F ≡ G
          → Γ ∙ ℕ ∙ G ⊢ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑²
  sucCong′ F≡G with wfEq F≡G
  sucCong′ F≡G | ⊢Γ ∙ ⊢ℕ =
    let ⊢F , ⊢G = syntacticEq F≡G
    in subst↑²TypeEq F≡G (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ ∙ ⊢G) (there here))))

opaque

  -- A variant of natrec-cong.

  natrec-cong′ : Γ ∙ ℕ     ⊢ A ≡ A′
               → Γ         ⊢ z ≡ z′ ∷ A [ zero ]₀
               → Γ ∙ ℕ ∙ A ⊢ s ≡ s′ ∷ A [ suc (var x1) ]↑²
               → Γ         ⊢ n ≡ n′ ∷ ℕ
               → Γ         ⊢ natrec p q r A z s n ≡
                             natrec p q r A′ z′ s′ n′ ∷
                             A [ n ]₀
  natrec-cong′ A≡A′ z≡z′ s≡s′ n≡n′ =
    natrec-cong (syntacticEq A≡A′ .proj₁) A≡A′ z≡z′ s≡s′ n≡n′

------------------------------------------------------------------------
-- Lemmas related to natcase

opaque
  unfolding natcase

  -- A typing rule for natcase.

  ⊢natcase :
    Γ ∙ ℕ ⊢ A →
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ⊢ u ∷ A [ suc (var x0) ]↑ →
    Γ ⊢ v ∷ ℕ →
    Γ ⊢ natcase p q A t u v ∷ A [ v ]₀
  ⊢natcase {A} ⊢A ⊢t ⊢u ⊢v =
    natrecⱼ ⊢A ⊢t
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ [wk1]↑² A) $
       wkTerm₁ ⊢A ⊢u)
      ⊢v

opaque
  unfolding natcase

  -- A reduction rule for natcase.

  natcase-zero-⇒ :
    Γ ∙ ℕ ⊢ A →
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ⊢ u ∷ A [ suc (var x0) ]↑ →
    Γ ⊢ natcase p q A t u zero ⇒ t ∷ A [ zero ]₀
  natcase-zero-⇒ {A} ⊢A ⊢t ⊢u =
    natrec-zero ⊢A ⊢t
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ [wk1]↑² A) $
       wkTerm₁ ⊢A ⊢u)

opaque

  -- An equality rule for natcase.

  natcase-zero-≡ :
    Γ ∙ ℕ ⊢ A →
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ⊢ u ∷ A [ suc (var x0) ]↑ →
    Γ ⊢ natcase p q A t u zero ≡ t ∷ A [ zero ]₀
  natcase-zero-≡ ⊢A ⊢t ⊢u =
    subsetTerm (natcase-zero-⇒ ⊢A ⊢t ⊢u)

opaque
  unfolding natcase

  -- Another reduction rule for natcase.

  natcase-suc-⇒ :
    Γ ∙ ℕ ⊢ A →
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ⊢ u ∷ A [ suc (var x0) ]↑ →
    Γ ⊢ v ∷ ℕ →
    Γ ⊢ natcase p q A t u (suc v) ⇒ u [ v ]₀ ∷ A [ suc v ]₀
  natcase-suc-⇒ {A} {u} ⊢A ⊢t ⊢u ⊢v =
    PE.subst (flip (_⊢_⇒_∷_ _ _) _) (subst-wk u) $
    natrec-suc ⊢A ⊢t
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ [wk1]↑² A) $
       wkTerm₁ ⊢A ⊢u)
      ⊢v

opaque

  -- Another equality rule for natcase.

  natcase-suc-≡ :
    Γ ∙ ℕ ⊢ A →
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ⊢ u ∷ A [ suc (var x0) ]↑ →
    Γ ⊢ v ∷ ℕ →
    Γ ⊢ natcase p q A t u (suc v) ≡ u [ v ]₀ ∷ A [ suc v ]₀
  natcase-suc-≡ ⊢A ⊢t ⊢u ⊢v =
    subsetTerm (natcase-suc-⇒ ⊢A ⊢t ⊢u ⊢v)

opaque
  unfolding natcase

  -- Yet another reduction rule for natcase.

  natcase-subst :
    Γ ∙ ℕ ⊢ A →
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ⊢ u ∷ A [ suc (var x0) ]↑ →
    Γ ⊢ v₁ ⇒ v₂ ∷ ℕ →
    Γ ⊢ natcase p q A t u v₁ ⇒ natcase p q A t u v₂ ∷ A [ v₁ ]₀
  natcase-subst {A} ⊢A ⊢t ⊢u v₁⇒v₂ =
    natrec-subst ⊢A ⊢t
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ [wk1]↑² A) $
       wkTerm₁ ⊢A ⊢u)
      v₁⇒v₂

opaque
  unfolding natcase

  -- Yet another equality rule for natcase.

  natcase-cong :
    Γ ∙ ℕ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
    Γ ∙ ℕ ⊢ u₁ ≡ u₂ ∷ A₁ [ suc (var x0) ]↑ →
    Γ ⊢ v₁ ≡ v₂ ∷ ℕ →
    Γ ⊢ natcase p q A₁ t₁ u₁ v₁ ≡ natcase p q A₂ t₂ u₂ v₂ ∷ A₁ [ v₁ ]₀
  natcase-cong {A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    case syntacticEq A₁≡A₂ of λ
      (⊢A₁ , _) →
    natrec-cong ⊢A₁ A₁≡A₂ t₁≡t₂
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ [wk1]↑² A₁) $
       wkEqTerm₁ ⊢A₁ u₁≡u₂)
      v₁≡v₂
