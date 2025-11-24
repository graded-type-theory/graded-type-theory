------------------------------------------------------------------------
-- Stability
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Stability
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Identity.Primitive R
open import Definition.Typed.Properties.Admissible.Nat R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Well-formed R
import Definition.Typed.Stability.Primitive R as S
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Well-formed R
open import Definition.Typed.Weakening R

open import Definition.Untyped M

open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ

private variable
  n               : Nat
  Γ Δ Η           : Con Term _
  A B l l₁ l₂ t u : Term _
  σ σ₁ σ₂         : Subst _ _

-- Equality of contexts.

infixl 24 _∙_

data ⊢_≡_ : (_ _ : Con Term n) → Set a where
  ε   : ⊢ ε ≡ ε
  _∙_ : ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B → ⊢ Γ ∙ A ≡ Δ ∙ B

private opaque

  -- A variant of S._∙⟨_∣_⟩.

  _∙⟨_⟩′ : S.⊢ Γ ≡ Δ → Γ ⊢ A ≡ B → S.⊢ Γ ∙ A ≡ Δ ∙ B
  Γ≡Δ ∙⟨ A≡B ⟩′ =
    Γ≡Δ
      S.∙⟨ S.stability-⊢ Γ≡Δ (wf-⊢≡ A≡B .proj₂)
         ∣ S.stability-⊢≡ Γ≡Δ A≡B
         ⟩

private opaque

  -- Symmetry for S.⊢_≡_.

  symConEq′ : S.⊢ Γ ≡ Δ → S.⊢ Δ ≡ Γ
  symConEq′ S.ε                  = S.ε
  symConEq′ (Γ≡Δ S.∙⟨ _ ∣ A≡B ⟩) = symConEq′ Γ≡Δ ∙⟨ sym A≡B ⟩′

private opaque

  -- ⊢ Γ ≡ Δ is logically equivalent to S.⊢ Γ ≡ Δ.

  ⊢≡⇔⊢≡ : ⊢ Γ ≡ Δ ⇔ S.⊢ Γ ≡ Δ
  ⊢≡⇔⊢≡ = to , from
    where
    to : ⊢ Γ ≡ Δ → S.⊢ Γ ≡ Δ
    to ε           = S.ε
    to (Γ≡Δ ∙ A≡B) = to Γ≡Δ ∙⟨ A≡B ⟩′

    from : S.⊢ Γ ≡ Δ → ⊢ Γ ≡ Δ
    from S.ε                  = ε
    from (Γ≡Δ S.∙⟨ _ ∣ A≡B ⟩) =
      from Γ≡Δ ∙ S.stability-⊢≡ (symConEq′ Γ≡Δ) A≡B

opaque

  -- Reflexivity for ⊢_≡_.

  reflConEq : ⊢ Γ → ⊢ Γ ≡ Γ
  reflConEq = ⊢≡⇔⊢≡ .proj₂ ∘→ S.reflConEq

opaque

  -- Symmetry for ⊢_≡_.

  symConEq : ⊢ Γ ≡ Δ → ⊢ Δ ≡ Γ
  symConEq = ⊢≡⇔⊢≡ .proj₂ ∘→ symConEq′ ∘→ ⊢≡⇔⊢≡ .proj₁

opaque

  -- A variant of _∙_.

  refl-∙ : Γ ⊢ A ≡ B → ⊢ Γ ∙ A ≡ Γ ∙ B
  refl-∙ A≡B = reflConEq (wfEq A≡B) ∙ A≡B

opaque

  -- A well-formedness lemma for ⊢_≡_.

  wf-⊢≡ˡ : ⊢ Γ ≡ Δ → ⊢ Γ
  wf-⊢≡ˡ ε           = ε
  wf-⊢≡ˡ (Γ≡Δ ∙ A≡B) = ∙ wf-⊢≡ A≡B .proj₁

opaque

  -- Stability for _⊢_.

  stability : ⊢ Γ ≡ Δ → Γ ⊢ A → Δ ⊢ A
  stability = S.stability-⊢ ∘→ ⊢≡⇔⊢≡ .proj₁

opaque

  -- Stability for _⊢_≡_.

  stabilityEq : ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B → Δ ⊢ A ≡ B
  stabilityEq = S.stability-⊢≡ ∘→ ⊢≡⇔⊢≡ .proj₁

opaque

  -- Stability for _⊢_∷_.

  stabilityTerm : ⊢ Γ ≡ Δ → Γ ⊢ t ∷ A → Δ ⊢ t ∷ A
  stabilityTerm = S.stability-⊢∷ ∘→ ⊢≡⇔⊢≡ .proj₁

opaque

  -- Stability for _⊢_∷Level.

  stabilityLevel : ⊢ Γ ≡ Δ → Γ ⊢ l ∷Level → Δ ⊢ l ∷Level
  stabilityLevel = S.stability-⊢∷L ∘→ ⊢≡⇔⊢≡ .proj₁

opaque

  -- Stability for _⊢_≡_∷_.

  stabilityEqTerm : ⊢ Γ ≡ Δ → Γ ⊢ t ≡ u ∷ A → Δ ⊢ t ≡ u ∷ A
  stabilityEqTerm = S.stability-⊢≡∷ ∘→ ⊢≡⇔⊢≡ .proj₁

opaque

  -- Stability for _⊢_≡_∷Level.

  stabilityEqLevel : ⊢ Γ ≡ Δ → Γ ⊢ l₁ ≡ l₂ ∷Level → Δ ⊢ l₁ ≡ l₂ ∷Level
  stabilityEqLevel = S.stability-⊢≡∷L ∘→ ⊢≡⇔⊢≡ .proj₁

opaque

  -- Stability for _⊢ˢ_∷_.

  stability-⊢ˢ∷ˡ : ⊢ Δ ≡ Η → Δ ⊢ˢ σ ∷ Γ → Η ⊢ˢ σ ∷ Γ
  stability-⊢ˢ∷ˡ _   id        = id
  stability-⊢ˢ∷ˡ Δ≡Η (⊢σ , ⊢t) =
    stability-⊢ˢ∷ˡ Δ≡Η ⊢σ , stabilityTerm Δ≡Η ⊢t

opaque

  -- Stability for _⊢ˢ_∷_.

  stability-⊢ˢʷ∷ˡ : ⊢ Δ ≡ Η → Δ ⊢ˢʷ σ ∷ Γ → Η ⊢ˢʷ σ ∷ Γ
  stability-⊢ˢʷ∷ˡ Δ≡Η =
    ⊢ˢʷ∷⇔ .proj₂ ∘→
    Σ.map (λ _ → S.wf-⊢≡ʳ (⊢≡⇔⊢≡ .proj₁ Δ≡Η)) (stability-⊢ˢ∷ˡ Δ≡Η) ∘→
    ⊢ˢʷ∷⇔ .proj₁

opaque

  -- A well-formedness lemma for ⊢_≡_.

  contextConvSubst : ⊢ Γ ≡ Δ → ⊢ Γ × ⊢ Δ × Δ ⊢ˢʷ idSubst ∷ Γ
  contextConvSubst Γ≡Δ =
    let ⊢Γ  = wf-⊢≡ˡ Γ≡Δ
        ⊢id = stability-⊢ˢʷ∷ˡ Γ≡Δ (⊢ˢʷ∷-idSubst ⊢Γ)
    in
    ⊢Γ , wf-⊢ˢʷ∷ ⊢id , ⊢id

opaque

  -- Stability for _⊢ˢ_∷_.

  stability-⊢ˢ∷ʳ : ⊢ Γ ≡ Δ → Η ⊢ˢ σ ∷ Γ → Η ⊢ˢ σ ∷ Δ
  stability-⊢ˢ∷ʳ ε           ⊢σ        = ⊢σ
  stability-⊢ˢ∷ʳ (Γ≡Δ ∙ A≡B) (⊢σ , ⊢t) =
    stability-⊢ˢ∷ʳ Γ≡Δ ⊢σ ,
    conv ⊢t (subst-⊢≡ A≡B (refl-⊢ˢʷ≡∷ (⊢ˢʷ∷⇔ .proj₂ (wfTerm ⊢t , ⊢σ))))

opaque

  -- Stability for _⊢ˢʷ_∷_.

  stability-⊢ˢʷ∷ʳ : ⊢ Γ ≡ Δ → Η ⊢ˢʷ σ ∷ Γ → Η ⊢ˢʷ σ ∷ Δ
  stability-⊢ˢʷ∷ʳ Γ≡Δ =
    ⊢ˢʷ∷⇔ .proj₂ ∘→
    Σ.map idᶠ (stability-⊢ˢ∷ʳ Γ≡Δ) ∘→
    ⊢ˢʷ∷⇔ .proj₁

opaque

  -- Stability for _⊢ˢ_≡_∷_.

  stability-⊢ˢ≡∷ˡ : ⊢ Δ ≡ Η → Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → Η ⊢ˢ σ₁ ≡ σ₂ ∷ Γ
  stability-⊢ˢ≡∷ˡ _   id              = id
  stability-⊢ˢ≡∷ˡ Δ≡Η (σ₁≡σ₂ , t₁≡t₂) =
    stability-⊢ˢ≡∷ˡ Δ≡Η σ₁≡σ₂ , stabilityEqTerm Δ≡Η t₁≡t₂

opaque

  -- Stability for _⊢ˢʷ_≡_∷_.

  stability-⊢ˢʷ≡∷ˡ : ⊢ Δ ≡ Η → Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ
  stability-⊢ˢʷ≡∷ˡ Δ≡Η =
    ⊢ˢʷ≡∷⇔ .proj₂ ∘→
    Σ.map (λ _ → contextConvSubst Δ≡Η .proj₂ .proj₁)
      (Σ.map (stability-⊢ˢ∷ˡ Δ≡Η) $ Σ.map (stability-⊢ˢ∷ˡ Δ≡Η) $
       stability-⊢ˢ≡∷ˡ Δ≡Η) ∘→
    ⊢ˢʷ≡∷⇔ .proj₁

opaque

  -- Stability for _⊢ˢ_≡_∷_.

  stability-⊢ˢ≡∷ʳ : ⊢ Γ ≡ Δ → Η ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → Η ⊢ˢ σ₁ ≡ σ₂ ∷ Δ
  stability-⊢ˢ≡∷ʳ ε           σ₁≡σ₂           = σ₁≡σ₂
  stability-⊢ˢ≡∷ʳ (Γ≡Δ ∙ A≡B) (σ₁≡σ₂ , t₁≡t₂) =
    let ⊢σ₁ , _ = wf-⊢ˢ≡∷ (wfEq A≡B) σ₁≡σ₂
        ⊢σ₁     = ⊢ˢʷ∷⇔ .proj₂ (wfEqTerm t₁≡t₂ , ⊢σ₁)
    in
    stability-⊢ˢ≡∷ʳ Γ≡Δ σ₁≡σ₂ ,
    conv t₁≡t₂ (subst-⊢≡ A≡B (refl-⊢ˢʷ≡∷ ⊢σ₁))

opaque

  -- Stability for _⊢ˢʷ_≡_∷_.

  stability-⊢ˢʷ≡∷ʳ : ⊢ Γ ≡ Δ → Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ
  stability-⊢ˢʷ≡∷ʳ Γ≡Δ =
    ⊢ˢʷ≡∷⇔ .proj₂ ∘→
    Σ.map idᶠ
      (Σ.map (stability-⊢ˢ∷ʳ Γ≡Δ) $ Σ.map (stability-⊢ˢ∷ʳ Γ≡Δ) $
       stability-⊢ˢ≡∷ʳ Γ≡Δ) ∘→
    ⊢ˢʷ≡∷⇔ .proj₁

opaque

  -- Stability for _⊢_⇒_∷_.

  stabilityRedTerm : ⊢ Γ ≡ Δ → Γ ⊢ t ⇒ u ∷ A → Δ ⊢ t ⇒ u ∷ A
  stabilityRedTerm Γ≡Δ (conv d x) =
    conv (stabilityRedTerm Γ≡Δ d) (stabilityEq Γ≡Δ x)
  stabilityRedTerm Γ≡Δ (supᵘ-zeroˡ ⊢l) =
    supᵘ-zeroˡ (stabilityTerm Γ≡Δ ⊢l)
  stabilityRedTerm Γ≡Δ (supᵘ-zeroʳ ⊢l) =
    supᵘ-zeroʳ (stabilityTerm Γ≡Δ ⊢l)
  stabilityRedTerm Γ≡Δ (supᵘ-sucᵘ ⊢l₁ ⊢l₂) =
    supᵘ-sucᵘ (stabilityTerm Γ≡Δ ⊢l₁) (stabilityTerm Γ≡Δ ⊢l₂)
  stabilityRedTerm Γ≡Δ (supᵘ-substˡ t⇒t′ ⊢u) =
    supᵘ-substˡ (stabilityRedTerm Γ≡Δ t⇒t′) (stabilityTerm Γ≡Δ ⊢u)
  stabilityRedTerm Γ≡Δ (supᵘ-substʳ ⊢t u⇒u′) =
    supᵘ-substʳ (stabilityTerm Γ≡Δ ⊢t) (stabilityRedTerm Γ≡Δ u⇒u′)
  stabilityRedTerm Γ≡Δ (lower-subst x) =
    lower-subst (stabilityRedTerm Γ≡Δ x)
  stabilityRedTerm Γ≡Δ (Lift-β x₁ x₂) =
    Lift-β (stability Γ≡Δ x₁) (stabilityTerm Γ≡Δ x₂)
  stabilityRedTerm Γ≡Δ (app-subst d x) =
    app-subst (stabilityRedTerm Γ≡Δ d) (stabilityTerm Γ≡Δ x)
  stabilityRedTerm Γ≡Δ (fst-subst ⊢G t⇒) =
    fst-subst (stability (Γ≡Δ ∙ refl (⊢∙→⊢ (wf ⊢G))) ⊢G)
              (stabilityRedTerm Γ≡Δ t⇒)
  stabilityRedTerm Γ≡Δ (snd-subst ⊢G t⇒) =
    snd-subst (stability (Γ≡Δ ∙ refl (⊢∙→⊢ (wf ⊢G))) ⊢G)
              (stabilityRedTerm Γ≡Δ t⇒)
  stabilityRedTerm Γ≡Δ (Σ-β₁ ⊢G ⊢t ⊢u p≡p′ ok) =
    Σ-β₁ (stability (Γ≡Δ ∙ refl (⊢∙→⊢ (wf ⊢G))) ⊢G)
         (stabilityTerm Γ≡Δ ⊢t)
         (stabilityTerm Γ≡Δ ⊢u)
         p≡p′ ok
  stabilityRedTerm Γ≡Δ (Σ-β₂ ⊢G ⊢t ⊢u p≡p′ ok) =
    Σ-β₂ (stability (Γ≡Δ ∙ refl (⊢∙→⊢ (wf ⊢G))) ⊢G)
         (stabilityTerm Γ≡Δ ⊢t)
         (stabilityTerm Γ≡Δ ⊢u)
         p≡p′ ok
  stabilityRedTerm Γ≡Δ (β-red x₁ x₂ x₃ x₄ ok) =
    let x = ⊢∙→⊢ (wf x₁) in
    β-red (stability (Γ≡Δ ∙ refl x) x₁)
          (stabilityTerm (Γ≡Δ ∙ refl x) x₂) (stabilityTerm Γ≡Δ x₃) x₄ ok
  stabilityRedTerm Γ≡Δ (natrec-subst x₁ x₂ d) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ in
    natrec-subst (stabilityTerm Γ≡Δ x₁)
      (stabilityTerm (Γ≡Δ ∙ refl (⊢ℕ ⊢Γ) ∙ refl (⊢∙→⊢ (wfTerm x₂))) x₂)
      (stabilityRedTerm Γ≡Δ d)
  stabilityRedTerm Γ≡Δ (natrec-zero x₁ x₂) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ in
    natrec-zero (stabilityTerm Γ≡Δ x₁)
      (stabilityTerm (Γ≡Δ ∙ refl (⊢ℕ ⊢Γ) ∙ refl (⊢∙→⊢ (wfTerm x₂))) x₂)
  stabilityRedTerm Γ≡Δ (natrec-suc x₁ x₂ x₃) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ in
    natrec-suc (stabilityTerm Γ≡Δ x₁)
      (stabilityTerm (Γ≡Δ ∙ refl (⊢ℕ ⊢Γ) ∙ refl (⊢∙→⊢ (wfTerm x₂))) x₂)
      (stabilityTerm Γ≡Δ x₃)
  stabilityRedTerm Γ≡Δ (prodrec-subst x₂ x₃ d ok) =
    let x₁ = ⊢∙→⊢ (wfTerm x₃)
        x  = ⊢∙→⊢ (wf x₁)
    in
    prodrec-subst (stability (Γ≡Δ ∙ refl (ΠΣⱼ x₁ ok)) x₂)
      (stabilityTerm (Γ≡Δ ∙ refl x ∙ refl x₁) x₃)
      (stabilityRedTerm Γ≡Δ d) ok
  stabilityRedTerm Γ≡Δ (prodrec-β x₂ x₃ x₄ x₅ x₆ ok) =
    let x₁ = ⊢∙→⊢ (wfTerm x₅)
        x  = ⊢∙→⊢ (wf x₁)
    in
    prodrec-β (stability (Γ≡Δ ∙ refl (ΠΣⱼ x₁ ok)) x₂)
      (stabilityTerm Γ≡Δ x₃) (stabilityTerm Γ≡Δ x₄)
      (stabilityTerm (Γ≡Δ ∙ refl x ∙ refl x₁) x₅) x₆ ok
  stabilityRedTerm Γ≡Δ (emptyrec-subst x d) =
    emptyrec-subst (stability Γ≡Δ x) (stabilityRedTerm Γ≡Δ d)
  stabilityRedTerm Γ≡Δ (unitrec-subst x x₁ x₂ x₃ not-ok) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in  unitrec-subst (stability (Γ≡Δ ∙ refl (univ (Unitⱼ ⊢Γ x₃))) x)
          (stabilityTerm Γ≡Δ x₁) (stabilityRedTerm Γ≡Δ x₂) x₃ not-ok
  stabilityRedTerm Γ≡Δ (unitrec-β x x₁ x₂ not-ok) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in  unitrec-β (stability (Γ≡Δ ∙ refl (univ (Unitⱼ ⊢Γ x₂))) x)
                  (stabilityTerm Γ≡Δ x₁) x₂ not-ok
  stabilityRedTerm Γ≡Δ (unitrec-β-η ⊢A ⊢t ⊢u ok₁ ok₂) =
    case contextConvSubst Γ≡Δ of λ
      (⊢Γ , _) →
    unitrec-β-η (stability (Γ≡Δ ∙ refl (univ (Unitⱼ ⊢Γ ok₁))) ⊢A)
      (stabilityTerm Γ≡Δ ⊢t) (stabilityTerm Γ≡Δ ⊢u) ok₁ ok₂
  stabilityRedTerm Γ≡Δ (J-subst ⊢t ⊢B ⊢u ⊢v w₁⇒w₂) =
    let ⊢A = ⊢∙→⊢ (wf (⊢∙→⊢ (wf ⊢B))) in
    J-subst (stabilityTerm Γ≡Δ ⊢t)
      (stability (Γ≡Δ ∙ refl ⊢A ∙ refl (Idⱼ′ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A)))
         ⊢B)
      (stabilityTerm Γ≡Δ ⊢u) (stabilityTerm Γ≡Δ ⊢v)
      (stabilityRedTerm Γ≡Δ w₁⇒w₂)
  stabilityRedTerm Γ≡Δ (K-subst ⊢B ⊢u v₁⇒v₂ ok) =
    let _ , (⊢t , _) , _ = inversion-Id-⊢ (⊢∙→⊢ (wf ⊢B)) in
    K-subst
      (stability (Γ≡Δ ∙ refl (Idⱼ′ ⊢t ⊢t)) ⊢B) (stabilityTerm Γ≡Δ ⊢u)
      (stabilityRedTerm Γ≡Δ v₁⇒v₂) ok
  stabilityRedTerm Γ≡Δ ([]-cong-subst ⊢l ⊢A ⊢t ⊢u v₁⇒v₂ ok) =
    []-cong-subst (stabilityLevel Γ≡Δ ⊢l) (stability Γ≡Δ ⊢A)
      (stabilityTerm Γ≡Δ ⊢t) (stabilityTerm Γ≡Δ ⊢u)
      (stabilityRedTerm Γ≡Δ v₁⇒v₂) ok
  stabilityRedTerm Γ≡Δ (J-β ⊢t ⊢t′ t≡t′ ⊢B ⊢B[t,rfl]≡B[t′,rfl] ⊢u) =
    let ⊢A = ⊢∙→⊢ (wf (⊢∙→⊢ (wf ⊢B))) in
    J-β (stabilityTerm Γ≡Δ ⊢t) (stabilityTerm Γ≡Δ ⊢t′)
      (stabilityEqTerm Γ≡Δ t≡t′)
      (stability (Γ≡Δ ∙ refl ⊢A ∙ refl (Idⱼ′ (wkTerm₁ ⊢A ⊢t) (var₀ ⊢A)))
         ⊢B)
      (stabilityEq Γ≡Δ ⊢B[t,rfl]≡B[t′,rfl]) (stabilityTerm Γ≡Δ ⊢u)
  stabilityRedTerm Γ≡Δ (K-β ⊢B ⊢u ok) =
    let _ , (⊢t , _) , _ = inversion-Id-⊢ (⊢∙→⊢ (wf ⊢B)) in
    K-β (stability (Γ≡Δ ∙ refl (Idⱼ′ ⊢t ⊢t)) ⊢B)
      (stabilityTerm Γ≡Δ ⊢u) ok
  stabilityRedTerm Γ≡Δ ([]-cong-β ⊢l ⊢A ⊢t ⊢t′ t≡t′ ok) =
    []-cong-β (stabilityLevel Γ≡Δ ⊢l) (stability Γ≡Δ ⊢A)
      (stabilityTerm Γ≡Δ ⊢t) (stabilityTerm Γ≡Δ ⊢t′)
      (stabilityEqTerm Γ≡Δ t≡t′) ok

opaque

  -- Stability for _⊢_⇒_.

  stabilityRed : ⊢ Γ ≡ Δ → Γ ⊢ A ⇒ B → Δ ⊢ A ⇒ B
  stabilityRed Γ≡Δ (univ x) = univ (stabilityRedTerm Γ≡Δ x)

opaque

  -- Stability for _⊢_⇒*_.

  stabilityRed* : ⊢ Γ ≡ Δ → Γ ⊢ A ⇒* B → Δ ⊢ A ⇒* B
  stabilityRed* Γ≡Δ (id x) = id (stability Γ≡Δ x)
  stabilityRed* Γ≡Δ (x ⇨ D) = stabilityRed Γ≡Δ x ⇨ stabilityRed* Γ≡Δ D

opaque

  -- Stability for _⊢_⇒*_∷_.

  stabilityRed*Term : ⊢ Γ ≡ Δ → Γ ⊢ t ⇒* u ∷ A → Δ ⊢ t ⇒* u ∷ A
  stabilityRed*Term Γ≡Δ (id x) = id (stabilityTerm Γ≡Δ x)
  stabilityRed*Term Γ≡Δ (x ⇨ d) =
    stabilityRedTerm Γ≡Δ x ⇨ stabilityRed*Term Γ≡Δ d

opaque

  -- Stability for _⊢_↘_.

  stabilityRed↘ : ⊢ Γ ≡ Δ → Γ ⊢ A ↘ B → Δ ⊢ A ↘ B
  stabilityRed↘ Γ≡Δ = Σ.map (stabilityRed* Γ≡Δ) idᶠ

opaque

  -- Stability for _⊢_↘_∷_.

  stabilityRed↘Term : ⊢ Γ ≡ Δ → Γ ⊢ t ↘ u ∷ A → Δ ⊢ t ↘ u ∷ A
  stabilityRed↘Term Γ≡Δ = Σ.map (stabilityRed*Term Γ≡Δ) idᶠ
