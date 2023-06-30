------------------------------------------------------------------------
-- Stability of typing and reduction.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Consequences.Stability
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Consequences.Substitution R

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ Δ : Con Term n

-- Equality of contexts.
data ⊢_≡_ : (Γ Δ : Con Term n) → Set a where
  ε : ⊢ ε ≡ ε
  _∙_ : ∀ {A B} → ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B → ⊢ Γ ∙ A ≡ Δ ∙ B


mutual
  -- Syntactic validity and conversion substitution of a context equality.
  contextConvSubst : ⊢ Γ ≡ Δ → ⊢ Γ × ⊢ Δ × Δ ⊢ˢ idSubst ∷ Γ
  contextConvSubst ε = ε , ε , id
  contextConvSubst (_∙_ {Γ = Γ} {Δ} {A} {B} Γ≡Δ A≡B) =
    let ⊢Γ , ⊢Δ , [σ] = contextConvSubst Γ≡Δ
        ⊢A , ⊢B = syntacticEq A≡B
        Δ⊢B = stability Γ≡Δ ⊢B
    in  ⊢Γ ∙ ⊢A , ⊢Δ ∙ Δ⊢B
        , (wk1Subst′ ⊢Γ ⊢Δ Δ⊢B [σ]
        , conv (var (⊢Δ ∙ Δ⊢B) here)
               (PE.subst (λ x → _ ⊢ _ ≡ x)
                         (wk1-tailId A)
                         (wkEq (step id) (⊢Δ ∙ Δ⊢B) (stabilityEq Γ≡Δ (sym A≡B)))))

  -- Stability of types under equal contexts.
  stability : ∀ {A} → ⊢ Γ ≡ Δ → Γ ⊢ A → Δ ⊢ A
  stability Γ≡Δ A =
    let ⊢Γ , ⊢Δ , σ = contextConvSubst Γ≡Δ
        q = substitution A σ ⊢Δ
    in  PE.subst (λ x → _ ⊢ x) (subst-id _) q

  -- Stability of type equality.
  stabilityEq : ∀ {A B} → ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B → Δ ⊢ A ≡ B
  stabilityEq Γ≡Δ A≡B =
    let ⊢Γ , ⊢Δ , σ = contextConvSubst Γ≡Δ
        q = substitutionEq A≡B (substRefl σ) ⊢Δ
    in  PE.subst₂ (λ x y → _ ⊢ x ≡ y) (subst-id _) (subst-id _) q

-- Reflexivity of context equality.
reflConEq : ⊢ Γ → ⊢ Γ ≡ Γ
reflConEq ε = ε
reflConEq (⊢Γ ∙ ⊢A) = reflConEq ⊢Γ ∙ refl ⊢A

-- Symmetry of context equality.
symConEq : ⊢ Γ ≡ Δ → ⊢ Δ ≡ Γ
symConEq ε = ε
symConEq (Γ≡Δ ∙ A≡B) = symConEq Γ≡Δ ∙ stabilityEq Γ≡Δ (sym A≡B)


-- Stability of terms.
stabilityTerm : ∀ {t A} → ⊢ Γ ≡ Δ → Γ ⊢ t ∷ A → Δ ⊢ t ∷ A
stabilityTerm Γ≡Δ t =
  let ⊢Γ , ⊢Δ , σ = contextConvSubst Γ≡Δ
      q = substitutionTerm t σ ⊢Δ
  in  PE.subst₂ (λ x y → _ ⊢ x ∷ y) (subst-id _) (subst-id _) q

-- Stability of term reduction.
stabilityRedTerm : ∀ {t u A} → ⊢ Γ ≡ Δ → Γ ⊢ t ⇒ u ∷ A → Δ ⊢ t ⇒ u ∷ A
stabilityRedTerm Γ≡Δ (conv d x) =
  conv (stabilityRedTerm Γ≡Δ d) (stabilityEq Γ≡Δ x)
stabilityRedTerm Γ≡Δ (app-subst d x) =
  app-subst (stabilityRedTerm Γ≡Δ d) (stabilityTerm Γ≡Δ x)
stabilityRedTerm Γ≡Δ (fst-subst ⊢F ⊢G t⇒) =
  fst-subst (stability Γ≡Δ ⊢F)
            (stability (Γ≡Δ ∙ refl ⊢F) ⊢G)
            (stabilityRedTerm Γ≡Δ t⇒)
stabilityRedTerm Γ≡Δ (snd-subst ⊢F ⊢G t⇒) =
  snd-subst (stability Γ≡Δ ⊢F)
            (stability (Γ≡Δ ∙ refl ⊢F) ⊢G)
            (stabilityRedTerm Γ≡Δ t⇒)
stabilityRedTerm Γ≡Δ (Σ-β₁ ⊢F ⊢G ⊢t ⊢u p≡p′ ok) =
  Σ-β₁ (stability Γ≡Δ ⊢F)
       (stability (Γ≡Δ ∙ refl ⊢F) ⊢G)
       (stabilityTerm Γ≡Δ ⊢t)
       (stabilityTerm Γ≡Δ ⊢u)
       p≡p′ ok
stabilityRedTerm Γ≡Δ (Σ-β₂ ⊢F ⊢G ⊢t ⊢u p≡p′ ok) =
  Σ-β₂ (stability Γ≡Δ ⊢F)
       (stability (Γ≡Δ ∙ refl ⊢F) ⊢G)
       (stabilityTerm Γ≡Δ ⊢t)
       (stabilityTerm Γ≡Δ ⊢u)
       p≡p′ ok
stabilityRedTerm Γ≡Δ (β-red x x₁ x₂ x₃ x₄ ok) =
  β-red (stability Γ≡Δ x) (stability (Γ≡Δ ∙ refl x) x₁)
        (stabilityTerm (Γ≡Δ ∙ refl x) x₂) (stabilityTerm Γ≡Δ x₃) x₄ ok
stabilityRedTerm Γ≡Δ (natrec-subst x x₁ x₂ d) =
  let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
  in  natrec-subst (stability (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ)) x) (stabilityTerm Γ≡Δ x₁)
                   ((stabilityTerm (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ) ∙ refl x) x₂)) (stabilityRedTerm Γ≡Δ d)
stabilityRedTerm Γ≡Δ (natrec-zero x x₁ x₂) =
  let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
  in  natrec-zero (stability (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ)) x) (stabilityTerm Γ≡Δ x₁)
                  (stabilityTerm (Γ≡Δ ∙ (refl (ℕⱼ ⊢Γ)) ∙ (refl x)) x₂)
stabilityRedTerm Γ≡Δ (natrec-suc x x₁ x₂ x₃) =
  let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
  in  natrec-suc (stability (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ)) x)
                 (stabilityTerm Γ≡Δ x₁)
                 (stabilityTerm (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ) ∙ refl x) x₂)
                 (stabilityTerm Γ≡Δ x₃)
stabilityRedTerm Γ≡Δ (prodrec-subst x x₁ x₂ x₃ d ok) =
  prodrec-subst (stability Γ≡Δ x) (stability (Γ≡Δ ∙ (refl x)) x₁)
                (stability (Γ≡Δ ∙ refl (ΠΣⱼ x x₁ ok)) x₂)
                (stabilityTerm (Γ≡Δ ∙ refl x ∙ refl x₁) x₃)
                (stabilityRedTerm Γ≡Δ d) ok
stabilityRedTerm Γ≡Δ (prodrec-β x x₁ x₂ x₃ x₄ x₅ x₆ ok) =
  prodrec-β (stability Γ≡Δ x) (stability (Γ≡Δ ∙ refl x) x₁)
            (stability (Γ≡Δ ∙ refl (ΠΣⱼ x x₁ ok)) x₂)
            (stabilityTerm Γ≡Δ x₃) (stabilityTerm Γ≡Δ x₄)
            (stabilityTerm (Γ≡Δ ∙ refl x ∙ refl x₁) x₅)
            x₆ ok
stabilityRedTerm Γ≡Δ (Emptyrec-subst x d) =
  Emptyrec-subst (stability Γ≡Δ x) (stabilityRedTerm Γ≡Δ d)

-- Stability of type reductions.
stabilityRed : ∀ {A B} → ⊢ Γ ≡ Δ → Γ ⊢ A ⇒ B → Δ ⊢ A ⇒ B
stabilityRed Γ≡Δ (univ x) = univ (stabilityRedTerm Γ≡Δ x)

-- Stability of type reduction closures.
stabilityRed* : ∀ {A B} → ⊢ Γ ≡ Δ → Γ ⊢ A ⇒* B → Δ ⊢ A ⇒* B
stabilityRed* Γ≡Δ (id x) = id (stability Γ≡Δ x)
stabilityRed* Γ≡Δ (x ⇨ D) = stabilityRed Γ≡Δ x ⇨ stabilityRed* Γ≡Δ D

-- Stability of term reduction closures.
stabilityRed*Term : ∀ {t u A} → ⊢ Γ ≡ Δ → Γ ⊢ t ⇒* u ∷ A → Δ ⊢ t ⇒* u ∷ A
stabilityRed*Term Γ≡Δ (id x) = id (stabilityTerm Γ≡Δ x)
stabilityRed*Term Γ≡Δ (x ⇨ d) = stabilityRedTerm Γ≡Δ x ⇨ stabilityRed*Term Γ≡Δ d
