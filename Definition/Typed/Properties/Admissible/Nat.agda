------------------------------------------------------------------------
-- Admissible rules related to the natural number type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Nat
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Untyped.Nat 𝕄
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Equality R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Syntactic R
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
  sucCong F≡G =
    let ⊢F , ⊢G = syntacticEq F≡G
    in subst↑²TypeEq F≡G (refl (sucⱼ (var (∙ ⊢F) (there here))))

opaque

  sucCong′ : ∀ {F G} → Γ ∙ ℕ ⊢ F ≡ G
          → Γ ∙ ℕ ∙ G ⊢ F [ suc (var x1) ]↑² ≡ G [ suc (var x1) ]↑²
  sucCong′ F≡G =
    let ⊢F , ⊢G = syntacticEq F≡G
    in subst↑²TypeEq F≡G (refl (sucⱼ (var (∙ ⊢G) (there here))))

opaque

  -- A variant of natrec-subst for _⊢_⇒*_∷_.

  natrec-subst* :
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊢ v₁ ⇒* v₂ ∷ ℕ →
    Γ ⊢ natrec p q r A t u v₁ ⇒* natrec p q r A t u v₂ ∷ A [ v₁ ]₀
  natrec-subst* {t} {A} {u} {v₁} {v₂} {p} {q} {r} ⊢t ⊢u = λ where
    (id ⊢v₁)                     → id (natrecⱼ ⊢t ⊢u ⊢v₁)
    (_⇨_ {t′ = v₃} v₁⇒v₃ v₃⇒*v₂) →
      natrec p q r A t u v₁ ∷ A [ v₁ ]₀  ⇒⟨ natrec-subst ⊢t ⊢u v₁⇒v₃ ⟩∷
                                         ˘⟨ substTypeEq (refl (⊢∙→⊢ (wfTerm ⊢u)))
                                              (sym′ (subsetTerm v₁⇒v₃)) ⟩⇒
      natrec p q r A t u v₃ ∷ A [ v₃ ]₀  ⇒*⟨ natrec-subst* ⊢t ⊢u v₃⇒*v₂ ⟩∎∷
      natrec p q r A t u v₂              ∎

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
    natrecⱼ ⊢t
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
    natrec-zero ⊢t
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
    natrec-suc ⊢t
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
    natrec-subst ⊢t
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
    natrec-cong A₁≡A₂ t₁≡t₂
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ [wk1]↑² A₁) $
       wkEqTerm₁ ⊢A₁ u₁≡u₂)
      v₁≡v₂

------------------------------------------------------------------------
-- Lemmas related to strict-const

opaque
  unfolding strict-const

  -- An equality rule for strict-const.

  strict-const-cong :
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ ℕ →
    Γ ⊢ strict-const A₁ t₁ u₁ ≡ strict-const A₂ t₂ u₂ ∷ A₁
  strict-const-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    let A₁≡A₂′ = wkEq₁ (syntacticEqTerm u₁≡u₂ .proj₁) A₁≡A₂ in
    PE.subst (_⊢_≡_∷_ _ _ _) (wk1-sgSubst _ _) $
    natrec-cong A₁≡A₂′
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ wk1-sgSubst _ _) t₁≡t₂)
      (_⊢_≡_∷_.refl $
       PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-[][]↑ 2) $
       var₀ (syntacticEq A₁≡A₂′ .proj₁))
      u₁≡u₂

opaque
  unfolding strict-const

  -- A reduction rule for strict-const.

  strict-const-subst :
    Γ ⊢ t ∷ A →
    Γ ⊢ u₁ ⇒ u₂ ∷ ℕ →
    Γ ⊢ strict-const A t u₁ ⇒ strict-const A t u₂ ∷ A
  strict-const-subst ⊢t u₁⇒u₂ =
    let ⊢A = wk₁ (ℕⱼ (wfTerm ⊢t)) (syntacticTerm ⊢t) in
    PE.subst (_⊢_⇒_∷_ _ _ _) (wk1-sgSubst _ _) $
    natrec-subst
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-sgSubst _ _) ⊢t)
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-[][]↑ 2) $
       var₀ ⊢A)
      u₁⇒u₂

opaque

  -- A typing rule for strict-const.

  ⊢strict-const :
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ ℕ →
    Γ ⊢ strict-const A t u ∷ A
  ⊢strict-const ⊢t ⊢u =
    syntacticEqTerm
      (strict-const-cong
         (refl (syntacticTerm ⊢t)) (refl ⊢t) (refl ⊢u))
      .proj₂ .proj₁

opaque
  unfolding strict-const

  -- A reduction rule for strict-const.

  strict-const-zero-⇒ :
    Γ ⊢ t ∷ A →
    Γ ⊢ strict-const A t zero ⇒ t ∷ A
  strict-const-zero-⇒ ⊢t =
    let ⊢A = wk₁ (ℕⱼ (wfTerm ⊢t)) (syntacticTerm ⊢t) in
    PE.subst (_⊢_⇒_∷_ _ _ _) (wk1-sgSubst _ _) $
    natrec-zero
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-sgSubst _ _) ⊢t)
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-[][]↑ 2) $
       var₀ ⊢A)

opaque

  -- An equality rule for strict-const.

  strict-const-zero-≡ :
    Γ ⊢ t ∷ A →
    Γ ⊢ strict-const A t zero ≡ t ∷ A
  strict-const-zero-≡ ⊢t =
    subsetTerm (strict-const-zero-⇒ ⊢t)

opaque
  unfolding strict-const

  -- A reduction rule for strict-const.

  strict-const-suc-⇒ :
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ ℕ →
    Γ ⊢ strict-const A t (suc u) ⇒ strict-const A t u ∷ A
  strict-const-suc-⇒ ⊢t ⊢u =
    let ⊢A = wk₁ (syntacticTerm ⊢u) (syntacticTerm ⊢t) in
    PE.subst (_⊢_⇒_∷_ _ _ _) (wk1-sgSubst _ _) $
    natrec-suc
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-sgSubst _ _) ⊢t)
      (PE.subst (_⊢_∷_ _ _) (PE.sym $ wk1-[][]↑ 2) $
       var₀ ⊢A)
      ⊢u

opaque

  -- An equality rule for strict-const.

  strict-const-suc-≡ :
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ ℕ →
    Γ ⊢ strict-const A t (suc u) ≡ strict-const A t u ∷ A
  strict-const-suc-≡ ⊢t ⊢u =
    subsetTerm (strict-const-suc-⇒ ⊢t ⊢u)
