------------------------------------------------------------------------
-- The logical relation for validity
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Properties R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as TW using (_∷_⊇_)

open import Definition.Untyped M
open import Definition.Untyped.Neutral M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Unit

private variable
  m n                                                   : Nat
  Γ Δ Η                                                 : Con Term _
  A A₁ A₂ B B₁ B₂ C C₁ C₂ D E t t₁ t₂ u u₁ u₂ v v₁ v₂ w : Term _
  σ σ₁ σ₂ σ₃                                            : Subst _ _
  ρ                                                     : Wk _ _
  l l′ l″ l‴                                            : TypeLevel

------------------------------------------------------------------------
-- The type formers

opaque mutual

  -- Valid contexts.

  infix 4 ⊩ᵛ_

  ⊩ᵛ_ : Con Term n → Set a
  ⊩ᵛ ε       = Lift _ ⊤
  ⊩ᵛ (Γ ∙ A) = ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A

  -- Valid types.

  infix 4 _⊩ᵛ⟨_⟩_

  _⊩ᵛ⟨_⟩_ : Con Term n → TypeLevel → Term n → Set a
  _⊩ᵛ⟨_⟩_ {n} Γ l A =
    ⊩ᵛ Γ ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ A [ σ₂ ])

  -- Valid substitution equality.

  infix 4 _⊩ˢ_≡_∷_

  _⊩ˢ_≡_∷_ : Con Term m → Subst m n → Subst m n → Con Term n → Set a
  Δ ⊩ˢ _  ≡ _  ∷ ε     = ⊢ Δ
  Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A =
    (∃ λ l →
     (Γ ⊩ᵛ⟨ l ⟩ A) ×
     Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ

opaque

  -- Valid terms.

  infix 4 _⊩ᵛ⟨_⟩_∷_

  _⊩ᵛ⟨_⟩_∷_ : Con Term n → TypeLevel → Term n → Term n → Set a
  _⊩ᵛ⟨_⟩_∷_ {n} Γ l t A =
    Γ ⊩ᵛ⟨ l ⟩ A ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ])

opaque

  -- Valid substitutions.

  infix 4 _⊩ˢ_∷_

  _⊩ˢ_∷_ : Con Term m → Subst m n → Con Term n → Set a
  Δ ⊩ˢ _ ∷ ε     = ⊢ Δ
  Δ ⊩ˢ σ ∷ Γ ∙ A =
    (∃ λ l → (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    Δ ⊩ˢ tail σ ∷ Γ

opaque

  -- Valid term equality.

  infix 4 _⊩ᵛ⟨_⟩_≡_∷_

  _⊩ᵛ⟨_⟩_≡_∷_ :
    Con Term n → TypeLevel → Term n → Term n → Term n → Set a
  _⊩ᵛ⟨_⟩_≡_∷_ {n} Γ l t u A =
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A ×
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A ×
    (∀ {m Δ} {σ : Subst m n} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ])

opaque

  -- Valid type equality.

  infix 4 _⊩ᵛ⟨_⟩_≡_

  _⊩ᵛ⟨_⟩_≡_ : Con Term n → TypeLevel → Term n → Term n → Set a
  _⊩ᵛ⟨_⟩_≡_ {n} Γ l A B =
    Γ ⊩ᵛ⟨ l ⟩ A ×
    Γ ⊩ᵛ⟨ l ⟩ B ×
    (∀ {m Δ} {σ : Subst m n} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ])

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding ⊩ᵛ_

  -- A characterisation lemma for ⊩ᵛ_.

  ⊩ᵛε⇔ : ⊩ᵛ ε ⇔ ⊤
  ⊩ᵛε⇔ = _

opaque
  unfolding ⊩ᵛ_

  -- A characterisation lemma for ⊩ᵛ_.

  ⊩ᵛ∙⇔ : ⊩ᵛ Γ ∙ A ⇔ ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A
  ⊩ᵛ∙⇔ = id⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ⇔ :
    Γ ⊩ᵛ⟨ l ⟩ A ⇔
    (⊩ᵛ Γ ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ A [ σ₂ ]))
  ⊩ᵛ⇔ = id⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡⇔ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B ⇔
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     Γ ⊩ᵛ⟨ l ⟩ B ×
     (∀ {m Δ} {σ : Subst m n} →
      Δ ⊩ˢ σ ∷ Γ →
      Δ ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ]))
  ⊩ᵛ≡⇔ = id⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷⇔ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A ⇔
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ∷⇔ = id⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷⇔ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⇔
    (Γ ⊩ᵛ⟨ l ⟩ t ∷ A ×
     Γ ⊩ᵛ⟨ l ⟩ u ∷ A ×
     (∀ {m Δ} {σ : Subst m n} →
      Δ ⊩ˢ σ ∷ Γ →
      Δ ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ]))
  ⊩ᵛ≡∷⇔ = id⇔

opaque
  unfolding _⊩ˢ_∷_

  -- A characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷ε⇔ : Δ ⊩ˢ σ ∷ ε ⇔ ⊢ Δ
  ⊩ˢ∷ε⇔ = id⇔

opaque
  unfolding _⊩ˢ_∷_

  -- A characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷∙⇔ :
    Δ ⊩ˢ σ ∷ Γ ∙ A ⇔
    ((∃ λ l → (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
     Δ ⊩ˢ tail σ ∷ Γ)
  ⊩ˢ∷∙⇔ = id⇔

opaque
  unfolding _⊩ˢ_≡_∷_

  -- A characterisation lemma for _⊩ˢ_≡_∷_.

  ⊩ˢ≡∷ε⇔ : Δ ⊩ˢ σ₁ ≡ σ₂ ∷ ε ⇔ ⊢ Δ
  ⊩ˢ≡∷ε⇔ = id⇔

opaque
  unfolding _⊩ˢ_≡_∷_

  -- A characterisation lemma for _⊩ˢ_≡_∷_.

  ⊩ˢ≡∷∙⇔ :
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A ⇔
    ((∃ λ l →
      (Γ ⊩ᵛ⟨ l ⟩ A) ×
      Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
     Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ)
  ⊩ˢ≡∷∙⇔ = id⇔

------------------------------------------------------------------------
-- An introduction lemma

opaque

  -- An introduction lemma for ⊩ᵛ_.

  ⊩ᵛ-∙-intro : Γ ⊩ᵛ⟨ l ⟩ A → ⊩ᵛ Γ ∙ A
  ⊩ᵛ-∙-intro ⊩A = ⊩ᵛ∙⇔ .proj₂ (_ , ⊩A)

------------------------------------------------------------------------
-- Reflexivity and some related lemmas

opaque

  -- Reflexivity for _⊩ˢ_≡_∷_.

  refl-⊩ˢ≡∷ :
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩ˢ σ ≡ σ ∷ Γ
  refl-⊩ˢ≡∷ {Δ} {σ} {Γ = ε} =
    Δ ⊩ˢ σ ∷ ε      ⇔⟨ ⊩ˢ∷ε⇔ ⟩→
    ⊢ Δ             ⇔˘⟨ ⊩ˢ≡∷ε⇔ ⟩→
    Δ ⊩ˢ σ ≡ σ ∷ ε  □
  refl-⊩ˢ≡∷ {Δ} {σ} {Γ = Γ ∙ A} =
    Δ ⊩ˢ σ ∷ Γ ∙ A                                               ⇔⟨ ⊩ˢ∷∙⇔ ⟩→

    ((∃ λ l → (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
     Δ ⊩ˢ tail σ ∷ Γ)                                            →⟨ Σ.map (Σ.map idᶠ (Σ.map idᶠ refl-⊩≡∷)) refl-⊩ˢ≡∷ ⟩

    ((∃ λ l →
      (Γ ⊩ᵛ⟨ l ⟩ A) ×
      Δ ⊩⟨ l ⟩ head σ ≡ head σ ∷ A [ tail σ ]) ×
     Δ ⊩ˢ tail σ ≡ tail σ ∷ Γ)                                   ⇔˘⟨ ⊩ˢ≡∷∙⇔ ⟩→

    Δ ⊩ˢ σ ≡ σ ∷ Γ ∙ A                                           □

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩[] :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ A [ σ ]
  ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A =
    ⊩⇔⊩≡ .proj₂ ∘→ ⊩ᵛ⇔ .proj₁ ⊩A .proj₂ ∘→ refl-⊩ˢ≡∷

opaque

  -- Reflexivity for _⊩ᵛ⟨_⟩_≡_.

  refl-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ A
  refl-⊩ᵛ≡ ⊩A =
    ⊩ᵛ≡⇔ .proj₂ (⊩A , ⊩A , refl-⊩≡ ∘→ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ t [ σ ] ∷ A [ σ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ ∘→ refl-⊩ˢ≡∷

opaque

  -- Reflexivity for _⊩ᵛ⟨_⟩_≡_∷_.

  refl-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ t ∷ A
  refl-⊩ᵛ≡∷ ⊩t =
    ⊩ᵛ≡∷⇔ .proj₂ (⊩t , ⊩t , refl-⊩≡∷ ∘→ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t)

------------------------------------------------------------------------
-- Symmetry

opaque

  -- Symmetry for _⊩ᵛ⟨_⟩_≡_.

  sym-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l ⟩ B ≡ A
  sym-⊩ᵛ≡ A≡B =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (⊩A , ⊩B , A≡B) →
    ⊩ᵛ≡⇔ .proj₂ (⊩B , ⊩A , sym-⊩≡ ∘→ A≡B)

opaque

  -- Symmetry for _⊩ᵛ⟨_⟩_≡_∷_.

  sym-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ u ≡ t ∷ A
  sym-⊩ᵛ≡∷ t≡u =
    case ⊩ᵛ≡∷⇔ .proj₁ t≡u of λ
      (⊩t , ⊩u , t≡u) →
    ⊩ᵛ≡∷⇔ .proj₂ (⊩u , ⊩t , sym-⊩≡∷ ∘→ t≡u)

opaque

  -- Symmetry for _⊩ˢ_≡_∷_.

  sym-⊩ˢ≡∷ :
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩ˢ σ₂ ≡ σ₁ ∷ Γ
  sym-⊩ˢ≡∷ {Γ = ε} =
    ⊩ˢ≡∷ε⇔ .proj₂ ∘→ ⊩ˢ≡∷ε⇔ .proj₁
  sym-⊩ˢ≡∷ {Γ = _ ∙ _} = λ σ₁≡σ₂ →
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((l , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
    case conv-⊩≡∷ (⊩ᵛ⇔ .proj₁ ⊩A .proj₂ σ₁₊≡σ₂₊) $
         sym-⊩≡∷ σ₁₀≡σ₂₀ of λ
      σ₂₀≡σ₁₀ →
    ⊩ˢ≡∷∙⇔ .proj₂ ((l , ⊩A , σ₂₀≡σ₁₀) , sym-⊩ˢ≡∷ σ₁₊≡σ₂₊)

------------------------------------------------------------------------
-- Well-formedness lemmas

opaque

  -- A well-formedness lemma for ⊩ᵛ_.

  wf-⊩ᵛ-∙ : ⊩ᵛ Γ ∙ A → ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A
  wf-⊩ᵛ-∙ = ⊩ᵛ∙⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_.

  wf-⊩ᵛ : Γ ⊩ᵛ⟨ l ⟩ A → ⊩ᵛ Γ
  wf-⊩ᵛ = proj₁ ∘→ ⊩ᵛ⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_.

  wf-∙-⊩ᵛ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    ∃ λ l′ → Γ ⊩ᵛ⟨ l′ ⟩ A
  wf-∙-⊩ᵛ = wf-⊩ᵛ-∙ ∘→ wf-⊩ᵛ

opaque

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_∷_.

  wf-⊩ᵛ∷ : Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ ⊩ᵛ⟨ l ⟩ A
  wf-⊩ᵛ∷ = proj₁ ∘→ ⊩ᵛ∷⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ˢ_∷_.

  wf-⊩ˢ∷ : Δ ⊩ˢ σ ∷ Γ → ⊩ᵛ Γ
  wf-⊩ˢ∷ {Γ = ε}     = λ _ → ⊩ᵛε⇔ .proj₂ _
  wf-⊩ˢ∷ {Γ = _ ∙ _} =
    ⊩ᵛ∙⇔ .proj₂ ∘→ Σ.map idᶠ proj₁ ∘→ proj₁ ∘→ ⊩ˢ∷∙⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_≡_.

  wf-⊩ᵛ≡ : Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ⊩ᵛ⟨ l ⟩ A × Γ ⊩ᵛ⟨ l ⟩ B
  wf-⊩ᵛ≡ = Σ.map idᶠ proj₁ ∘→ ⊩ᵛ≡⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  wf-⊩ᵛ≡∷ : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A → Γ ⊩ᵛ⟨ l ⟩ t ∷ A × Γ ⊩ᵛ⟨ l ⟩ u ∷ A
  wf-⊩ᵛ≡∷ = Σ.map idᶠ proj₁ ∘→ ⊩ᵛ≡∷⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ˢ_≡_∷_.

  wf-⊩ˢ≡∷ : Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩ˢ σ₁ ∷ Γ × Δ ⊩ˢ σ₂ ∷ Γ
  wf-⊩ˢ≡∷ {Γ = ε} σ₁≡σ₂ =
    case ⊩ˢ≡∷ε⇔ .proj₁ σ₁≡σ₂ of λ
      ⊢Δ →
    ⊩ˢ∷ε⇔ .proj₂ ⊢Δ , ⊩ˢ∷ε⇔ .proj₂ ⊢Δ
  wf-⊩ˢ≡∷ {Γ = _ ∙ _} σ₁≡σ₂ =
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((l , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
    case wf-⊩≡∷ σ₁₀≡σ₂₀ of λ
      (⊩σ₁₀ , ⊩σ₂₀) →
    case conv-⊩∷ (⊩ᵛ⇔ .proj₁ ⊩A .proj₂ σ₁₊≡σ₂₊) ⊩σ₂₀ of λ
      ⊩σ₂₀ →
    case wf-⊩ˢ≡∷ σ₁₊≡σ₂₊ of λ
      (⊩σ₁₊ , ⊩σ₂₊) →
      ⊩ˢ∷∙⇔ .proj₂ ((l , ⊩A , ⊩σ₁₀) , ⊩σ₁₊)
    , ⊩ˢ∷∙⇔ .proj₂ ((l , ⊩A , ⊩σ₂₀) , ⊩σ₂₊)

------------------------------------------------------------------------
-- More characterisation lemmas

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ⇔⊩ᵛ≡ : (Γ ⊩ᵛ⟨ l ⟩ A) ⇔ Γ ⊩ᵛ⟨ l ⟩ A ≡ A
  ⊩ᵛ⇔⊩ᵛ≡ = refl-⊩ᵛ≡ , proj₁ ∘→ wf-⊩ᵛ≡

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷⇔⊩ᵛ≡∷ : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ⇔ Γ ⊩ᵛ⟨ l ⟩ t ≡ t ∷ A
  ⊩ᵛ∷⇔⊩ᵛ≡∷ = refl-⊩ᵛ≡∷ , proj₁ ∘→ wf-⊩ᵛ≡∷

opaque

  -- A characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷⇔⊩ˢ≡∷ : Δ ⊩ˢ σ ∷ Γ ⇔ Δ ⊩ˢ σ ≡ σ ∷ Γ
  ⊩ˢ∷⇔⊩ˢ≡∷ = refl-⊩ˢ≡∷ , proj₁ ∘→ wf-⊩ˢ≡∷

opaque

  -- A variant of ⊩ᵛ≡⇔.

  ⊩ᵛ≡⇔′ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B ⇔
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     Γ ⊩ᵛ⟨ l ⟩ B ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ]))
  ⊩ᵛ≡⇔′ {n} {Γ} {l} {A} {B} =
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B                 ⇔⟨ ⊩ᵛ≡⇔ ⟩

    Γ ⊩ᵛ⟨ l ⟩ A ×
    Γ ⊩ᵛ⟨ l ⟩ B ×
    (∀ {m Δ} {σ : Subst m n} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ])    ⇔⟨ (Σ-cong-⇔ λ ⊩A → Σ-cong-⇔ λ _ →
                                          (λ hyp {m = _} {Δ = _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
      A [ σ₁ ]                                 ≡⟨ ⊩ᵛ⇔ .proj₁ ⊩A .proj₂ σ₁≡σ₂ ⟩⊩
      A [ σ₂ ]                                 ≡⟨ hyp (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₂) ⟩⊩∎
      B [ σ₂ ]                                 ∎)
                                        , (λ hyp {_ _ _} ⊩σ →
                                             hyp (refl-⊩ˢ≡∷ ⊩σ))) ⟩
    Γ ⊩ᵛ⟨ l ⟩ A ×
    Γ ⊩ᵛ⟨ l ⟩ B ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ])  □⇔

opaque

  -- A variant of ⊩ᵛ≡∷⇔.

  ⊩ᵛ≡∷⇔′ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⇔
    (Γ ⊩ᵛ⟨ l ⟩ t ∷ A ×
     Γ ⊩ᵛ⟨ l ⟩ u ∷ A ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ≡∷⇔′ {n} {Γ} {l} {t} {u} {A} =
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A                        ⇔⟨ ⊩ᵛ≡∷⇔ ⟩

    Γ ⊩ᵛ⟨ l ⟩ t ∷ A ×
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A ×
    (∀ {m Δ} {σ : Subst m n} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ])     ⇔⟨ (Σ-cong-⇔ λ ⊩t → Σ-cong-⇔ λ _ →
                                                     (λ hyp {m = _} {Δ = _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
      t [ σ₁ ]                                            ≡⟨ ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂ ⟩⊩∷
      t [ σ₂ ]                                            ≡⟨ conv-⊩≡∷
                                                               (⊩ᵛ⇔ .proj₁ (wf-⊩ᵛ∷ ⊩t) .proj₂ (sym-⊩ˢ≡∷ σ₁≡σ₂))
                                                               (hyp (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₂)) ⟩⊩∷∎
      u [ σ₂ ]                                            ∎)
                                                   , (λ hyp {_ _ _} ⊩σ →
                                                        hyp (refl-⊩ˢ≡∷ ⊩σ))) ⟩
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A ×
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ])  □⇔

opaque

  -- A variant of ⊩ˢ∷∙⇔.

  ⊩ˢ∷∙⇔′ :
    Δ ⊩ˢ σ ∷ Γ ∙ A ⇔
    ((∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A) ×
     (∃ λ l → Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
     Δ ⊩ˢ tail σ ∷ Γ)
  ⊩ˢ∷∙⇔′ {Δ} {σ} {Γ} {A} =
    Δ ⊩ˢ σ ∷ Γ ∙ A                                              ⇔⟨ ⊩ˢ∷∙⇔ ⟩

    (∃ λ l → (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    Δ ⊩ˢ tail σ ∷ Γ
                                                                ⇔⟨ (λ ((l , ⊩A , ⊩head) , ⊩tail) →
                                                                      (l , ⊩A) , (l , ⊩head) , ⊩tail)
                                                                 , (λ ((l₁ , ⊩A) , (_ , ⊩head) , ⊩tail) →
                                                                      (l₁ , ⊩A , level-⊩∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩tail) ⊩head) , ⊩tail)
                                                                 ⟩
    (∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A) ×
    (∃ λ l → Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    Δ ⊩ˢ tail σ ∷ Γ                                             □⇔

opaque

  -- A variant of ⊩ˢ≡∷∙⇔.

  ⊩ˢ≡∷∙⇔′ :
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A ⇔
    ((∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A) ×
     (∃ λ l → Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
     Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ)
  ⊩ˢ≡∷∙⇔′ {Δ} {σ₁} {σ₂} {Γ} {A} =
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A                                            ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩

    (∃ λ l →
     (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                      ⇔⟨ (λ ((l , ⊩A , head≡head) , tail≡tail) →
                                                                          (l , ⊩A) , (l , head≡head) , tail≡tail)
                                                                     , (λ ((l₁ , ⊩A) , (_ , head≡head) , tail≡tail) →
                                                                            ( l₁ , ⊩A
                                                                            , level-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A (wf-⊩ˢ≡∷ tail≡tail .proj₁))
                                                                                head≡head
                                                                            )
                                                                          , tail≡tail)
                                                                     ⟩
    (∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A) ×
    (∃ λ l → Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                      □⇔

------------------------------------------------------------------------
-- Changing type levels

opaque

  -- Changing type levels for _⊩ᵛ⟨_⟩_∷_.

  level-⊩ᵛ∷ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A
  level-⊩ᵛ∷ ⊩A ⊩t =
    case ⊩ᵛ∷⇔ .proj₁ ⊩t of λ
      (_ , t≡t) →
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩A
      , λ σ₁≡σ₂ →
          level-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) $
          t≡t σ₁≡σ₂
      )

opaque

  -- Changing type levels for _⊩ᵛ⟨_⟩_≡_.

  level-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B
  level-⊩ᵛ≡ ⊩A ⊩B A≡B =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (_ , _ , A≡B) →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩A , ⊩B
      , λ ⊩σ →
          level-⊩≡ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ) (⊩ᵛ→⊩ˢ∷→⊩[] ⊩B ⊩σ) $
          A≡B ⊩σ
      )

opaque

  -- Changing type levels for _⊩ᵛ⟨_⟩_≡_∷_.

  level-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A
  level-⊩ᵛ≡∷ ⊩A t≡u =
    case ⊩ᵛ≡∷⇔ .proj₁ t≡u of λ
      (⊩t , ⊩u , t≡u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( level-⊩ᵛ∷ ⊩A ⊩t
      , level-⊩ᵛ∷ ⊩A ⊩u
      , λ ⊩σ →
          level-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ) $
          t≡u ⊩σ
      )

------------------------------------------------------------------------
-- Transitivity

opaque

  -- Transitivity for _⊩ᵛ⟨_⟩_≡_.

  trans-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l ⟩ B ≡ C →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ C
  trans-⊩ᵛ≡ A≡B B≡C =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (⊩A , _ , A≡B) →
    case ⊩ᵛ≡⇔ .proj₁ B≡C of λ
      (_ , ⊩C , B≡C) →
    ⊩ᵛ≡⇔ .proj₂ (⊩A , ⊩C , λ ⊩σ → trans-⊩≡ (A≡B ⊩σ) (B≡C ⊩σ))

opaque

  -- Transitivity for _⊩ᵛ⟨_⟩_≡_∷_.

  trans-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ u ≡ v ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ v ∷ A
  trans-⊩ᵛ≡∷ t≡u u≡v =
    case ⊩ᵛ≡∷⇔ .proj₁ u≡v of λ
      (_ , ⊩v , u≡v) →
    case ⊩ᵛ≡∷⇔ .proj₁ $ level-⊩ᵛ≡∷ (wf-⊩ᵛ∷ ⊩v) t≡u of λ
      (⊩t , _ , t≡u) →
    ⊩ᵛ≡∷⇔ .proj₂ (⊩t , ⊩v , λ ⊩σ → trans-⊩≡∷ (t≡u ⊩σ) (u≡v ⊩σ))

opaque

  -- Transitivity for _⊩ˢ_≡_∷_.

  trans-⊩ˢ≡ :
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩ˢ σ₂ ≡ σ₃ ∷ Γ →
    Δ ⊩ˢ σ₁ ≡ σ₃ ∷ Γ
  trans-⊩ˢ≡ {Γ = ε} σ₁≡σ₂ _ =
    ⊩ˢ≡∷ε⇔ .proj₂ $ ⊩ˢ≡∷ε⇔ .proj₁ σ₁≡σ₂
  trans-⊩ˢ≡ {Γ = _ ∙ _} σ₁≡σ₂ σ₂≡σ₃ =
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((l , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₂≡σ₃ of λ
      ((l , ⊩A , σ₂₀≡σ₃₀) , σ₂₊≡σ₃₊) →
    case conv-⊩≡∷ (⊩ᵛ⇔ .proj₁ ⊩A .proj₂ $ sym-⊩ˢ≡∷ σ₁₊≡σ₂₊) σ₂₀≡σ₃₀ of λ
      σ₂₀≡σ₃₀ →
    ⊩ˢ≡∷∙⇔ .proj₂
      ( (l , ⊩A , trans-⊩≡∷ σ₁₀≡σ₂₀ σ₂₀≡σ₃₀)
      , trans-⊩ˢ≡ σ₁₊≡σ₂₊ σ₂₊≡σ₃₊
      )

------------------------------------------------------------------------
-- Conversion

opaque

  -- Conversion for one of the contexts for _⊩ˢ_≡_∷_.

  conv-⊩ˢ≡∷-∙ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ B
  conv-⊩ˢ≡∷-∙ {Γ} {A} {B} {Δ} {σ₁} {σ₂} A≡B =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (_ , ⊩B , A≡B) →

    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A                                            ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

    (∃ λ l →
     (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                      →⟨ (λ ((_ , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                            (_ , ⊩B , conv-⊩≡∷ (A≡B $ wf-⊩ˢ≡∷ σ₁₊≡σ₂₊ .proj₁) σ₁₀≡σ₂₀)
                                                                          , σ₁₊≡σ₂₊) ⟩
    (∃ λ l →
     (Γ ⊩ᵛ⟨ l ⟩ B) × Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                      ⇔˘⟨ ⊩ˢ≡∷∙⇔ ⟩→

    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ B                                            □

opaque

  -- Conversion for one of the contexts for _⊩ˢ_∷_.

  conv-⊩ˢ∷-∙ : Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Δ ⊩ˢ σ ∷ Γ ∙ A → Δ ⊩ˢ σ ∷ Γ ∙ B
  conv-⊩ˢ∷-∙ A≡B =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ conv-⊩ˢ≡∷-∙ A≡B ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- Conversion for the context for _⊩ᵛ⟨_⟩_.

  conv-∙-⊩ᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ C →
    Γ ∙ B ⊩ᵛ⟨ l ⟩ C
  conv-∙-⊩ᵛ {Γ} {A} {B} {l} {C} A≡B ⊩C =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (⊩A , ⊩B , A≡B) →
    ⊩ᵛ⇔ .proj₂
      ( ⊩ᵛ-∙-intro ⊩B
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ B                            ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

          (∃ λ l →
           (Γ ⊩ᵛ⟨ l ⟩ B) ×
           Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B [ tail σ₁ ]) ×
          Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                      →⟨ (λ ((_ , _ , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                  (_ , ⊩A , conv-⊩≡∷ (sym-⊩≡ $ A≡B $ wf-⊩ˢ≡∷ σ₁₊≡σ₂₊ .proj₁) σ₁₀≡σ₂₀)
                                                                , σ₁₊≡σ₂₊) ⟩
          (∃ λ l →
           (Γ ⊩ᵛ⟨ l ⟩ A) ×
           Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
          Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                      ⇔˘⟨ ⊩ˢ≡∷∙⇔ ⟩→

          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A                            →⟨ ⊩ᵛ⇔ .proj₁ ⊩C .proj₂ ⟩

          Δ ⊩⟨ l ⟩ C [ σ₁ ] ≡ C [ σ₂ ]                    □
      )

opaque

  -- Another kind of conversion for the context for _⊩ᵛ⟨_⟩_.

  conv-∙∙-⊩ᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l″ ⟩ B₁ ≡ B₂ →
    Γ ∙ A₁ ∙ B₁ ⊩ᵛ⟨ l ⟩ C →
    Γ ∙ A₂ ∙ B₂ ⊩ᵛ⟨ l ⟩ C
  conv-∙∙-⊩ᵛ {Γ} {A₁} {A₂} {B₁} {B₂} {l} {C} A₁≡A₂ B₁≡B₂ ⊩C =
    case sym-⊩ᵛ≡ A₁≡A₂ of λ
      A₂≡A₁ →
    case ⊩ᵛ≡⇔ .proj₁ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂ , B₁≡B₂) →
    ⊩ᵛ⇔ .proj₂
      ( ⊩ᵛ-∙-intro (conv-∙-⊩ᵛ A₁≡A₂ ⊩B₂)
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A₂ ∙ B₂                       ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

          (∃ λ l →
           (Γ ∙ A₂ ⊩ᵛ⟨ l ⟩ B₂) ×
           Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B₂ [ tail σ₁ ]) ×
          Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ ∙ A₂                  →⟨ ((λ ((_ , _ , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                   ( _ , ⊩B₁
                                                                   , conv-⊩≡∷
                                                                       (sym-⊩≡ $ B₁≡B₂ $
                                                                        conv-⊩ˢ∷-∙ A₂≡A₁ $ wf-⊩ˢ≡∷ σ₁₊≡σ₂₊ .proj₁)
                                                                       σ₁₀≡σ₂₀
                                                                   )
                                                                 , conv-⊩ˢ≡∷-∙ A₂≡A₁ σ₁₊≡σ₂₊)) ⟩
          (∃ λ l →
           (Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁) ×
           Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B₁ [ tail σ₁ ]) ×
          Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ ∙ A₁                  ⇔˘⟨ ⊩ˢ≡∷∙⇔ ⟩→

          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A₁ ∙ B₁                       →⟨ ⊩ᵛ⇔ .proj₁ ⊩C .proj₂ ⟩

          Δ ⊩⟨ l ⟩ C [ σ₁ ] ≡ C [ σ₂ ]                     □
      )

opaque

  -- Conversion for _⊩ᵛ⟨_⟩_∷_.

  conv-⊩ᵛ∷ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ B
  conv-⊩ᵛ∷ A≡B ⊩t =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (_ , ⊩B , A≡B) →
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩B
      , λ σ₁≡σ₂ →
          conv-⊩≡∷ (A≡B $ wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) $
          ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂
      )

opaque

  -- Conversion for the context for _⊩ᵛ⟨_⟩_∷_.

  conv-∙-⊩ᵛ∷ :
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ C →
    Γ ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C
  conv-∙-⊩ᵛ∷ A≡B ⊩t =
    case ⊩ᵛ∷⇔ .proj₁ ⊩t of λ
      (⊩C , t≡t) →
    ⊩ᵛ∷⇔ .proj₂
      ( conv-∙-⊩ᵛ A≡B ⊩C
      , t≡t ∘→ conv-⊩ˢ≡∷-∙ (sym-⊩ᵛ≡ A≡B)
      )

opaque

  -- Conversion for _⊩ᵛ⟨_⟩_≡_∷_.

  conv-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ B
  conv-⊩ᵛ≡∷ A≡B t≡u =
    case ⊩ᵛ≡∷⇔ .proj₁ t≡u of λ
      (⊩t , ⊩u , t≡u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( conv-⊩ᵛ∷ A≡B ⊩t
      , conv-⊩ᵛ∷ A≡B ⊩u
      , λ ⊩σ →
          conv-⊩≡∷ (⊩ᵛ≡⇔ .proj₁ A≡B .proj₂ .proj₂ ⊩σ) $
          t≡u ⊩σ
      )

------------------------------------------------------------------------
-- Expansion

opaque

  -- An expansion lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷-⇐ :
    (∀ {m Δ} {σ : Subst m n} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊢ t [ σ ] ⇒ u [ σ ] ∷ A [ σ ]) →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A
  ⊩ᵛ∷-⇐ {n} {Γ} {t} {u} {A} {l} t⇒u ⊩u =
    case ⊩ᵛ∷⇔ .proj₁ ⊩u of λ
      (⊩A , u≡u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ∷⇔ .proj₂
          ( ⊩A
          , λ {_} {_} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
              case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
                (⊩σ₁ , ⊩σ₂) →
              t [ σ₁ ]             ≡⟨ lemma ⊩σ₁ ⟩⊩∷
              u [ σ₁ ] ∷ A [ σ₁ ]  ≡⟨ u≡u σ₁≡σ₂ ⟩⊩∷∷
                                    ⟨ ⊩ᵛ⇔ .proj₁ ⊩A .proj₂ σ₁≡σ₂ ⟩⊩∷
              u [ σ₂ ] ∷ A [ σ₂ ]  ≡˘⟨ lemma ⊩σ₂ ⟩⊩∷∎∷
              t [ σ₂ ]             ∎
          )
      , ⊩u
      , lemma
      )
    where
    lemma :
      ∀ {m Δ} {σ : Subst m n} →
      Δ ⊩ˢ σ ∷ Γ → Δ ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ]
    lemma ⊩σ =
      case ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ of λ
        ⊩u[σ] →
      ⊩∷-⇐* (t⇒u ⊩σ ⇨ id (escape-⊩∷ ⊩u[σ])) ⊩u[σ]

------------------------------------------------------------------------
-- Some lemmas related to _⊩ˢ_∷_ and _⊩ˢ_≡_∷_

opaque

  -- A cast lemma for _⊩ˢ_∷_.

  cast-⊩ˢ∷ :
    ((x : Fin n) → σ₁ x PE.≡ σ₂ x) →
    Δ ⊩ˢ σ₁ ∷ Γ → Δ ⊩ˢ σ₂ ∷ Γ
  cast-⊩ˢ∷ {Γ = ε} _ ⊩σ₁ =
    ⊩ˢ∷ε⇔ .proj₂ $ ⊩ˢ∷ε⇔ .proj₁ ⊩σ₁
  cast-⊩ˢ∷ {Γ = _ ∙ A} σ₁≡σ₂ ⊩σ₁ =
    case ⊩ˢ∷∙⇔ .proj₁ ⊩σ₁ of λ
      ((_ , ⊩A , ⊩σ₁₀) , ⊩σ₁₊) →
    case σ₁≡σ₂ ∘→ (_+1) of λ
      σ₁₊≡σ₂₊ →
    ⊩ˢ∷∙⇔ .proj₂
      ( ( _ , ⊩A
        , PE.subst₂ (_⊩⟨_⟩_∷_ _ _) (σ₁≡σ₂ x0)
            (substVar-to-subst σ₁₊≡σ₂₊ A) ⊩σ₁₀
        )
      , cast-⊩ˢ∷ σ₁₊≡σ₂₊ ⊩σ₁₊
      )

opaque

  -- A lemma related to _•ₛ_.

  ⊩ˢ≡∷-•ₛ :
    ⊢ Η →
    ρ ∷ Η ⊇ Δ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Η ⊩ˢ ρ •ₛ σ₁ ≡ ρ •ₛ σ₂ ∷ Γ
  ⊩ˢ≡∷-•ₛ {Γ = ε} ⊢Η _ _ =
    ⊩ˢ≡∷ε⇔ .proj₂ ⊢Η
  ⊩ˢ≡∷-•ₛ {Γ = _ ∙ A} ⊢Η ρ⊇ σ₁≡σ₂ =
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((_ , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
    ⊩ˢ≡∷∙⇔ .proj₂
      ( ( _ , ⊩A
        , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A)
            (wk-⊩≡∷ ρ⊇ ⊢Η σ₁₀≡σ₂₀)
        )
      , ⊩ˢ≡∷-•ₛ ⊢Η ρ⊇ σ₁₊≡σ₂₊
      )

opaque

  -- A lemma related to _•ₛ_.

  ⊩ˢ∷-•ₛ :
    ⊢ Η →
    ρ ∷ Η ⊇ Δ →
    Δ ⊩ˢ σ ∷ Γ →
    Η ⊩ˢ ρ •ₛ σ ∷ Γ
  ⊩ˢ∷-•ₛ ⊢Η ρ⊇ =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-•ₛ ⊢Η ρ⊇ ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A lemma related to _ₛ•_.

  ⊩ˢ≡∷-ₛ• :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Γ → Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    Η ⊩ˢ σ₁ ₛ• ρ ≡ σ₂ ₛ• ρ ∷ Γ
  ⊩ˢ≡∷-ₛ• TW.id _ σ₁≡σ₂ =
    σ₁≡σ₂
  ⊩ˢ≡∷-ₛ• (TW.step ρ⊇) ⊩Γ σ₁≡σ₂ =
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((_ , ⊩A , head≡head) , tail≡tail) →
    ⊩ˢ≡∷-ₛ• ρ⊇ ⊩Γ tail≡tail
  ⊩ˢ≡∷-ₛ• (TW.lift {A} ρ⊇) ⊩Γ∙A σ₁≡σ₂ =
    case wf-⊩ᵛ-∙ ⊩Γ∙A of λ
      (_ , ⊩A) →
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((_ , _ , head≡head) , tail≡tail) →
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( (_ , ⊩A)
      , (_ , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (subst-wk A) head≡head)
      , ⊩ˢ≡∷-ₛ• ρ⊇ (wf-⊩ᵛ ⊩A) tail≡tail
      )

opaque

  -- A lemma related to _ₛ•_.

  ⊩ˢ∷-ₛ• : ρ ∷ Δ ⊇ Γ → ⊩ᵛ Γ → Η ⊩ˢ σ ∷ Δ → Η ⊩ˢ σ ₛ• ρ ∷ Γ
  ⊩ˢ∷-ₛ• ρ⊇ ⊩Γ =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-ₛ• ρ⊇ ⊩Γ ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A lemma related to wk1Subst.

  ⊩ˢ≡∷-wk1Subst :
    Δ ⊢ A →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A ⊩ˢ wk1Subst σ₁ ≡ wk1Subst σ₂ ∷ Γ
  ⊩ˢ≡∷-wk1Subst ⊢A = ⊩ˢ≡∷-•ₛ (⊢→⊢∙ ⊢A) (TW.step TW.id)

opaque

  -- A lemma related to wk1Subst.

  ⊩ˢ∷-wk1Subst :
    Δ ⊢ A →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A ⊩ˢ wk1Subst σ ∷ Γ
  ⊩ˢ∷-wk1Subst ⊢A =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-wk1Subst ⊢A ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A lemma related to liftSubst.

  ⊩ˢ≡∷-liftSubst :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ⊩ˢ liftSubst σ₁ ≡ liftSubst σ₂ ∷ Γ ∙ A
  ⊩ˢ≡∷-liftSubst {A} ⊩A σ₁≡σ₂ =
    case escape-⊩ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) of λ
      ⊢A[σ₁] →
    case ⊩ˢ≡∷-wk1Subst ⊢A[σ₁] σ₁≡σ₂ of λ
      σ₁⇑₊≡σ₂⇑₊ →
    case var (⊢→⊢∙ ⊢A[σ₁])
           (PE.subst₂ (_∷_∈_ _) (PE.sym $ wk1Subst-wk1 A) PE.refl
              here) of λ
      ⊢0 →
    ⊩ˢ≡∷∙⇔ .proj₂
      ( ( _ , ⊩A
        , neutral-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ wf-⊩ˢ≡∷ σ₁⇑₊≡σ₂⇑₊ .proj₁)
            (var _) (var _) ⊢0 ⊢0 (~-var ⊢0)
        )
      , σ₁⇑₊≡σ₂⇑₊
      )

opaque

  -- A lemma related to liftSubst.

  ⊩ˢ∷-liftSubst :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊩ˢ liftSubst σ ∷ Γ ∙ A
  ⊩ˢ∷-liftSubst ⊩A =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-liftSubst ⊩A ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A variant of ⊩ˢ≡∷-liftSubst.

  ⊩ˢ≡∷-liftSubst′ :
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A₁ [ σ₁ ] ⊩ˢ liftSubst σ₁ ≡ liftSubst σ₂ ∷ Γ ∙ A₂
  ⊩ˢ≡∷-liftSubst′ {A₁} {A₂} {σ₁} A₁≡A₂ σ₁≡σ₂ =
    conv-⊩ˢ≡∷-∙ A₁≡A₂ $
    ⊩ˢ≡∷-liftSubst (wf-⊩ᵛ≡ A₁≡A₂ .proj₁) σ₁≡σ₂

opaque

  -- A variant of ⊩ˢ∷-liftSubst.

  ⊩ˢ∷-liftSubst′ :
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A₁ [ σ ] ⊩ˢ liftSubst σ ∷ Γ ∙ A₂
  ⊩ˢ∷-liftSubst′ A₁≡A₂ =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-liftSubst′ A₁≡A₂ ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A lemma related to idSubst.

  ⊩ˢ∷-idSubst :
    ⊩ᵛ Γ →
    Γ ⊩ˢ idSubst ∷ Γ
  ⊩ˢ∷-idSubst {Γ = ε} _ =
    ⊩ˢ∷ε⇔ .proj₂ ε
  ⊩ˢ∷-idSubst {Γ = _ ∙ _} ⊩Γ∙A =
    case ⊩ᵛ∙⇔ .proj₁ ⊩Γ∙A .proj₂ of λ
      ⊩A →
    PE.subst₃ _⊩ˢ_∷_ (PE.cong (_∙_ _) $ subst-id _) PE.refl PE.refl $
    cast-⊩ˢ∷ subst-lift-id $
    ⊩ˢ∷-liftSubst (⊩ᵛ∙⇔ .proj₁ ⊩Γ∙A .proj₂)
      (⊩ˢ∷-idSubst (⊩ᵛ⇔ .proj₁ ⊩A .proj₁))

opaque

  -- A lemma related to sgSubst.

  ⊩ˢ≡∷-sgSubst :
    Γ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩ˢ sgSubst t ≡ sgSubst u ∷ Γ ∙ A
  ⊩ˢ≡∷-sgSubst ⊩A t≡u =
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( (_ , ⊩A)
      , (_ , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ subst-id _) t≡u)
      , refl-⊩ˢ≡∷ (⊩ˢ∷-idSubst (wf-⊩ᵛ ⊩A))
      )

opaque

  -- A lemma related to sgSubst.

  ⊩ˢ∷-sgSubst :
    Γ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩ˢ sgSubst t ∷ Γ ∙ A
  ⊩ˢ∷-sgSubst ⊩A =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-sgSubst ⊩A ∘→ ⊩∷⇔⊩≡∷ .proj₁

------------------------------------------------------------------------
-- Reducibility from validity

opaque

  -- If there is a valid equality between A and B, then there is a
  -- reducible equality between A and B.

  ⊩ᵛ≡→⊩≡ : Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B
  ⊩ᵛ≡→⊩≡ {Γ} {l} {A} {B} =
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B                            ⇔⟨ ⊩ᵛ≡⇔ ⟩→

    (Γ ⊩ᵛ⟨ l ⟩ A) ×
    (Γ ⊩ᵛ⟨ l ⟩ B) ×
    (∀ {m} {Δ : Con Term m} {σ} →
     Δ ⊩ˢ σ ∷ Γ → Δ ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ])  →⟨ (λ (⊩A , _ , A≡B) → A≡B $ ⊩ˢ∷-idSubst $ wf-⊩ᵛ ⊩A) ⟩

    Γ ⊩⟨ l ⟩ A [ idSubst ] ≡ B [ idSubst ]     ≡⟨ PE.cong₂ (_⊩⟨_⟩_≡_ _ _) (subst-id _) (subst-id _) ⟩→

    Γ ⊩⟨ l ⟩ A ≡ B                             □

opaque

  -- If A is valid, then A is reducible.

  ⊩ᵛ→⊩ : Γ ⊩ᵛ⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A
  ⊩ᵛ→⊩ = ⊩⇔⊩≡ .proj₂ ∘→ ⊩ᵛ≡→⊩≡ ∘→ ⊩ᵛ⇔⊩ᵛ≡ .proj₁

opaque

  -- If there is a valid equality between t and u, then there is a
  -- reducible equality between t and u.

  ⊩ᵛ≡∷→⊩≡∷ : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩ᵛ≡∷→⊩≡∷ {Γ} {l} {t} {u} {A} =
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A                                     ⇔⟨ ⊩ᵛ≡∷⇔ ⟩→

    (Γ ⊩ᵛ⟨ l ⟩ t ∷ A) ×
    (Γ ⊩ᵛ⟨ l ⟩ u ∷ A) ×
    (∀ {m} {Δ : Con Term m} {σ} →
     Δ ⊩ˢ σ ∷ Γ → Δ ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ])     →⟨ (λ (⊩t , _ , t≡u) → t≡u $ ⊩ˢ∷-idSubst $ wf-⊩ᵛ $ wf-⊩ᵛ∷ ⊩t) ⟩

    Γ ⊩⟨ l ⟩ t [ idSubst ] ≡ u [ idSubst ] ∷ A [ idSubst ]  ≡⟨ PE.cong₃ (_⊩⟨_⟩_≡_∷_ _ _)
                                                                 (subst-id _) (subst-id _) (subst-id _) ⟩→

    Γ ⊩⟨ l ⟩ t ≡ u ∷ A                                      □

opaque

  -- If t is valid, then t is reducible.

  ⊩ᵛ∷→⊩∷ : Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ∷ A
  ⊩ᵛ∷→⊩∷ = ⊩∷⇔⊩≡∷ .proj₂ ∘→ ⊩ᵛ≡∷→⊩≡∷ ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

------------------------------------------------------------------------
-- Escape lemmas

opaque

  -- An escape lemma for _⊩ᵛ⟨_⟩_.

  escape-⊩ᵛ : Γ ⊩ᵛ⟨ l ⟩ A → Γ ⊢ A
  escape-⊩ᵛ = escape-⊩ ∘→ ⊩ᵛ→⊩

opaque

  -- An escape lemma for ⊩ᵛ_.

  escape-⊩ᵛ′ : ⊩ᵛ Γ → ⊢ Γ
  escape-⊩ᵛ′ {Γ = ε}     = λ _ → ε
  escape-⊩ᵛ′ {Γ = _ ∙ _} = ⊢→⊢∙ ∘→ escape-⊩ᵛ ∘→ proj₂ ∘→ ⊩ᵛ∙⇔ .proj₁

opaque

  -- An escape lemma for _⊩ᵛ⟨_⟩_≡_.

  escape-⊩ᵛ≡ : Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ⊢ A ≅ B
  escape-⊩ᵛ≡ = escape-⊩≡ ∘→ ⊩ᵛ≡→⊩≡

opaque

  -- An escape lemma for _⊩ᵛ⟨_⟩_∷_.

  escape-⊩ᵛ∷ : Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ ⊢ t ∷ A
  escape-⊩ᵛ∷ = escape-⊩∷ ∘→ ⊩ᵛ∷→⊩∷

opaque

  -- An escape lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  escape-⊩ᵛ≡∷ : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A → Γ ⊢ t ≅ u ∷ A
  escape-⊩ᵛ≡∷ = escape-⊩≡∷ ∘→ ⊩ᵛ≡∷→⊩≡∷

opaque

  -- An escape lemma for _⊩ˢ_∷_.

  escape-⊩ˢ∷ : Δ ⊩ˢ σ ∷ Γ → ⊢ Δ × Δ ⊢ˢ σ ∷ Γ
  escape-⊩ˢ∷ {Δ} {σ} {Γ = ε} =
    Δ ⊩ˢ σ ∷ ε        ⇔⟨ ⊩ˢ∷ε⇔ ⟩→
    ⊢ Δ               →⟨ _, id ⟩
    ⊢ Δ × Δ ⊢ˢ σ ∷ ε  □
  escape-⊩ˢ∷ {Δ} {σ} {Γ = Γ ∙ A} =
    Δ ⊩ˢ σ ∷ Γ ∙ A                                              ⇔⟨ ⊩ˢ∷∙⇔ ⟩→

    (∃ λ l → (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    Δ ⊩ˢ tail σ ∷ Γ                                             →⟨ (λ ((_ , _ , ⊩σ₀) , ⊩σ₊) →
                                                                      escape-⊩∷ ⊩σ₀ , escape-⊩ˢ∷ ⊩σ₊) ⟩

    Δ ⊢ head σ ∷ A [ tail σ ] × ⊢ Δ × Δ ⊢ˢ tail σ ∷ Γ           →⟨ (λ (⊢σ₀ , ⊢Δ , ⊢σ₊) → ⊢Δ , (⊢σ₊ , ⊢σ₀)) ⟩

    ⊢ Δ × Δ ⊢ˢ σ ∷ Γ ∙ A                                        □

opaque

  -- An escape lemma for _⊩ˢ_≡_∷_.

  escape-⊩ˢ≡∷ : Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → ⊢ Δ × Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ
  escape-⊩ˢ≡∷ {Δ} {σ₁} {σ₂} {Γ = ε} =
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ ε        ⇔⟨ ⊩ˢ≡∷ε⇔ ⟩→
    ⊢ Δ                     →⟨ _, id ⟩
    ⊢ Δ × Δ ⊢ˢ σ₁ ≡ σ₂ ∷ ε  □
  escape-⊩ˢ≡∷ {Δ} {σ₁} {σ₂} {Γ = Γ ∙ A} =
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A                                            ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

    (∃ λ l →
     (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                      →⟨ (λ ((_ , _ , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                          ≅ₜ-eq (escape-⊩≡∷ σ₁₀≡σ₂₀) , escape-⊩ˢ≡∷ σ₁₊≡σ₂₊) ⟩
    Δ ⊢ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ] ×
    ⊢ Δ × Δ ⊢ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                →⟨ (λ (σ₁₀≡σ₂₀ , ⊢Δ , σ₁₊≡σ₂₊) → ⊢Δ , (σ₁₊≡σ₂₊ , σ₁₀≡σ₂₀)) ⟩

    ⊢ Δ × Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A                                      □

------------------------------------------------------------------------
-- Embedding

opaque

  -- Embedding for _⊩ᵛ⟨_⟩_.

  emb-⊩ᵛ :
    l ≤ l′ →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ A
  emb-⊩ᵛ l≤l′ ⊩A =
    case ⊩ᵛ⇔ .proj₁ ⊩A of λ
      (⊩Γ , A≡A) →
    ⊩ᵛ⇔ .proj₂ (⊩Γ , emb-⊩≡ l≤l′ ∘→ A≡A)

opaque

  -- Embedding for _⊩ᵛ⟨_⟩_∷_.

  emb-⊩ᵛ∷ :
    l ≤ l′ →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A
  emb-⊩ᵛ∷ l≤l′ ⊩t =
    level-⊩ᵛ∷ (emb-⊩ᵛ l≤l′ (wf-⊩ᵛ∷ ⊩t)) ⊩t

------------------------------------------------------------------------
-- Weakening

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_.

  wk-⊩ᵛ : ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ⟨ l ⟩ A → Δ ⊩ᵛ⟨ l ⟩ wk ρ A
  wk-⊩ᵛ {ρ} {A} ρ⊇ ⊩Δ ⊩A =
    ⊩ᵛ⇔ .proj₂
      ( ⊩Δ
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          wk ρ A [ σ₁ ]  ≡⟨ subst-wk A ⟩⊩≡
          A [ σ₁ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡⇔′ .proj₁ (refl-⊩ᵛ≡ ⊩A) .proj₂ .proj₂ $
                            ⊩ˢ≡∷-ₛ• ρ⊇ (wf-⊩ᵛ ⊩A) σ₁≡σ₂ ⟩⊩∎≡
          A [ σ₂ ₛ• ρ ]  ≡˘⟨ subst-wk A ⟩
          wk ρ A [ σ₂ ]  ∎
      )

opaque

  -- Single-step weakening for _⊩ᵛ⟨_⟩_.

  wk1-⊩ᵛ : Γ ⊩ᵛ⟨ l′ ⟩ B → Γ ⊩ᵛ⟨ l ⟩ A → Γ ∙ B ⊩ᵛ⟨ l ⟩ wk1 A
  wk1-⊩ᵛ ⊩B =
    wk-⊩ᵛ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩B)

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_∷_.

  wk-⊩ᵛ∷ :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Δ ⊩ᵛ⟨ l ⟩ wk ρ t ∷ wk ρ A
  wk-⊩ᵛ∷ {ρ} {t} {A} ρ⊇ ⊩Δ ⊩t =
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩A →
    ⊩ᵛ∷⇔ .proj₂
      ( wk-⊩ᵛ ρ⊇ ⊩Δ ⊩A
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          wk ρ t [ σ₁ ] ∷ wk ρ A [ σ₁ ]  ≡⟨ subst-wk t ⟩⊩∷∷≡
                                          ⟨ subst-wk A ⟩⊩∷≡
          t [ σ₁ ₛ• ρ ] ∷ A [ σ₁ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡∷⇔′ .proj₁ (refl-⊩ᵛ≡∷ ⊩t) .proj₂ .proj₂ $
                                            ⊩ˢ≡∷-ₛ• ρ⊇ (wf-⊩ᵛ ⊩A) σ₁≡σ₂ ⟩⊩∷∎∷≡
          t [ σ₂ ₛ• ρ ]                  ≡˘⟨ subst-wk t ⟩
          wk ρ t [ σ₂ ]                  ∎
      )

opaque

  -- Single-step weakening for _⊩ᵛ⟨_⟩_∷_.

  wk1-⊩ᵛ∷ : Γ ⊩ᵛ⟨ l′ ⟩ B → Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ ∙ B ⊩ᵛ⟨ l ⟩ wk1 t ∷ wk1 A
  wk1-⊩ᵛ∷ ⊩B =
    wk-⊩ᵛ∷ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩B)

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_≡_.

  wk-⊩ᵛ≡ :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Δ ⊩ᵛ⟨ l ⟩ wk ρ A ≡ wk ρ B
  wk-⊩ᵛ≡ {ρ} {A} {B} ρ⊇ ⊩Δ A≡B =
    case wf-⊩ᵛ≡ A≡B of λ
      (⊩A , ⊩B) →
    ⊩ᵛ≡⇔ .proj₂
      ( wk-⊩ᵛ ρ⊇ ⊩Δ ⊩A
      , wk-⊩ᵛ ρ⊇ ⊩Δ ⊩B
      , λ {_ _} {σ = σ} ⊩σ →
          wk ρ A [ σ ]  ≡⟨ subst-wk A ⟩⊩≡
          A [ σ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡⇔ .proj₁ A≡B .proj₂ .proj₂ $
                           ⊩ˢ∷-ₛ• ρ⊇ (wf-⊩ᵛ ⊩A) ⊩σ ⟩⊩∎≡
          B [ σ ₛ• ρ ]  ≡˘⟨ subst-wk B ⟩
          wk ρ B [ σ ]  ∎
      )

opaque

  -- Single-step weakening for _⊩ᵛ⟨_⟩_≡_.

  wk1-⊩ᵛ≡ : Γ ⊩ᵛ⟨ l′ ⟩ C → Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ∙ C ⊩ᵛ⟨ l ⟩ wk1 A ≡ wk1 B
  wk1-⊩ᵛ≡ ⊩C =
    wk-⊩ᵛ≡ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩C)

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  wk-⊩ᵛ≡∷ :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Δ ⊩ᵛ⟨ l ⟩ wk ρ t ≡ wk ρ u ∷ wk ρ A
  wk-⊩ᵛ≡∷ {ρ} {t} {u} {A} ρ⊇ ⊩Δ t≡u =
    case wf-⊩ᵛ≡∷ t≡u of λ
      (⊩t , ⊩u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( wk-⊩ᵛ∷ ρ⊇ ⊩Δ ⊩t
      , wk-⊩ᵛ∷ ρ⊇ ⊩Δ ⊩u
      , λ {_ _} {σ = σ} ⊩σ →
          wk ρ t [ σ ] ∷ wk ρ A [ σ ]  ≡⟨ subst-wk t ⟩⊩∷∷≡
                                        ⟨ subst-wk A ⟩⊩∷≡
          t [ σ ₛ• ρ ] ∷ A [ σ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂ .proj₂ $
                                          ⊩ˢ∷-ₛ• ρ⊇ (wf-⊩ᵛ $ wf-⊩ᵛ∷ ⊩t) ⊩σ ⟩⊩∷∎∷≡
          u [ σ ₛ• ρ ]                 ≡˘⟨ subst-wk u ⟩
          wk ρ u [ σ ]                 ∎
      )

opaque

  -- Single-step weakening for _⊩ᵛ⟨_⟩_≡_∷_.

  wk1-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l′ ⟩ B → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Γ ∙ B ⊩ᵛ⟨ l ⟩ wk1 t ≡ wk1 u ∷ wk1 A
  wk1-⊩ᵛ≡∷ ⊩B =
    wk-⊩ᵛ≡∷ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩B)

------------------------------------------------------------------------
-- Substitution lemmas

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ B [ t ]₀
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ {B} ⊩B ⊩t =
    case ⊩ᵛ⇔ .proj₁ ⊩B of λ
      (⊩Γ∙A , B≡B) →
    case ⊩ᵛ∙⇔ .proj₁ ⊩Γ∙A of λ
      (_ , ⊩A) →
    ⊩ᵛ⇔ .proj₂
      ( ⊩ᵛ⇔ .proj₁ ⊩A .proj₁
      , λ σ₁≡σ₂ →
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (substConsId B) (substConsId B) $
          B≡B $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( (_ , ⊩A)
            , (_ , ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂)
            , σ₁≡σ₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B ≡ C →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ B [ t ]₀ ≡ C [ u ]₀
  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ {B} {C} {t} {u} B≡C t≡u =
    case ⊩ᵛ≡⇔ .proj₁ B≡C of λ
      (⊩B , ⊩C , B≡C) →
    case ⊩ᵛ≡∷⇔ .proj₁ t≡u of λ
      (⊩t , ⊩u , t≡u) →
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩A →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B ⊩t
      , ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩C ⊩u
      , λ {_ _} {σ = σ} ⊩σ →
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (substConsId B) (substConsId C)
            (B [ consSubst σ (t [ σ ]) ]  ≡⟨ ⊩ᵛ⇔ .proj₁ ⊩B .proj₂ $
                                             ⊩ˢ≡∷∙⇔ .proj₂ ((_ , ⊩A , t≡u ⊩σ) , refl-⊩ˢ≡∷ ⊩σ) ⟩⊩
             B [ consSubst σ (u [ σ ]) ]  ≡⟨ B≡C $
                                             ⊩ˢ∷∙⇔ .proj₂ ((_ , ⊩A , ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ) , ⊩σ) ⟩⊩∎
             C [ consSubst σ (u [ σ ]) ]  ∎)
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t [ u ]₀ ∷ B [ u ]₀
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ {t} {B} ⊩t ⊩u =
    case ⊩ᵛ∷⇔ .proj₁ ⊩t of λ
      (⊩B , t≡t) →
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B ⊩u
      , λ σ₁≡σ₂ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
            (substConsId t) (substConsId t) (substConsId B) $
          t≡t $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ ⊩B
            , (_ , ⊩ᵛ∷⇔ .proj₁ ⊩u .proj₂ σ₁≡σ₂)
            , σ₁≡σ₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ B [ t ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ C [ t , u ]₁₀
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ {B} {C} ⊩C ⊩t ⊩u =
    case ⊩ᵛ⇔ .proj₁ ⊩C of λ
      (⊩Γ∙A∙B , C≡C) →
    case ⊩ᵛ∙⇔ .proj₁ ⊩Γ∙A∙B of λ
      (_ , ⊩B) →
    case wf-∙-⊩ᵛ ⊩B of λ
      (_ , ⊩A) →
    ⊩ᵛ⇔ .proj₂
      ( ⊩ᵛ⇔ .proj₁ ⊩A .proj₁
      , λ σ₁≡σ₂ →
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
            (PE.sym $ [,]-[]-fusion C) (PE.sym $ [,]-[]-fusion C) $
          C≡C $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( (_ , ⊩B)
            , ( _
              , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ substConsId B)
                  (⊩ᵛ∷⇔ .proj₁ ⊩u .proj₂ σ₁≡σ₂))
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( (_ , ⊩A)
                , (_ , ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂)
                , σ₁≡σ₂
                )
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ C₁ [ t₁ , u₁ ]₁₀ ≡ C₂ [ t₂ , u₂ ]₁₀
  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀
    {B} {C₁} {C₂} {t₁} {t₂} {u₁} {u₂} C₁≡C₂ t₁≡t₂ u₁≡u₂ =
    case ⊩ᵛ≡⇔ .proj₁ C₁≡C₂ of λ
      (⊩C₁ , ⊩C₂ , C₁≡C₂) →
    case wf-∙-⊩ᵛ ⊩C₁ of λ
      (_ , ⊩B) →
    case wf-∙-⊩ᵛ ⊩B of λ
      (_ , ⊩A) →
    case ⊩ᵛ≡∷⇔ .proj₁ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂ , u₁≡u₂) →
    case conv-⊩ᵛ∷ (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩B) t₁≡t₂) ⊩u₂ of λ
      ⊩u₂ →
    case ⊩ᵛ≡∷⇔ .proj₁ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂ , t₁≡t₂) →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ ⊩C₁ ⊩t₁ ⊩u₁
      , ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ ⊩C₂ ⊩t₂ ⊩u₂
      , λ {_ _} {σ = σ} ⊩σ →
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
            (PE.sym $ [,]-[]-fusion C₁) (PE.sym $ [,]-[]-fusion C₂)
            (C₁ [ consSubst (consSubst σ (t₁ [ σ ])) (u₁ [ σ ]) ]  ≡⟨ ⊩ᵛ⇔ .proj₁ ⊩C₁ .proj₂ $
                                                                      ⊩ˢ≡∷∙⇔′ .proj₂
                                                                        ( (_ , ⊩B)
                                                                        , ( _
                                                                          , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ substConsId B)
                                                                              (u₁≡u₂ ⊩σ)
                                                                          )
                                                                        , ⊩ˢ≡∷∙⇔′ .proj₂ ((_ , ⊩A) , (_ , t₁≡t₂ ⊩σ) , refl-⊩ˢ≡∷ ⊩σ)
                                                                        ) ⟩⊩
             C₁ [ consSubst (consSubst σ (t₂ [ σ ])) (u₂ [ σ ]) ]  ≡⟨ C₁≡C₂ $
                                                                      ⊩ˢ∷∙⇔ .proj₂
                                                                        ( ( _ , ⊩B
                                                                          , PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ substConsId B)
                                                                              (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₂ ⊩σ)
                                                                          )
                                                                        , ⊩ˢ∷∙⇔′ .proj₂ ((_ , ⊩A) , (_ , ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ) , ⊩σ)
                                                                        ) ⟩⊩∎
             C₂ [ consSubst (consSubst σ (t₂ [ σ ])) (u₂ [ σ ]) ]  ∎)
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l″ ⟩ v ∷ B [ u ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ t [ u , v ]₁₀ ∷ C [ u , v ]₁₀
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ {B} {t} {C} ⊩t ⊩u ⊩v =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ ⊩t) of λ
      (_ , ⊩B) →
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ (wf-⊩ᵛ∷ ⊩t) ⊩u ⊩v
      , λ σ₁≡σ₂ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ [,]-[]-fusion t)
            (PE.sym $ [,]-[]-fusion t) (PE.sym $ [,]-[]-fusion C) $
          ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( (_ , ⊩B)
            , ( _
              , (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                   (PE.sym $ substConsId B) $
                 ⊩ᵛ∷⇔ .proj₁ ⊩v .proj₂ σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( wf-∙-⊩ᵛ ⊩B
                , (_ , ⊩ᵛ∷⇔ .proj₁ ⊩u .proj₂ σ₁≡σ₂)
                , σ₁≡σ₂
                )
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    Γ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ v₁ ≡ v₂ ∷ B [ u₁ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ t₁ [ u₁ , v₁ ]₁₀ ≡ t₂ [ u₂ , v₂ ]₁₀ ∷ C [ u₁ , v₁ ]₁₀
  ⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀∷ {B} {t₁} {t₂} {C} t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case wf-⊩ᵛ∷ ⊩t₁ of λ
      ⊩C →
    case wf-∙-⊩ᵛ ⊩C of λ
      (_ , ⊩B) →
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case wf-⊩ᵛ≡∷ v₁≡v₂ of λ
      (⊩v₁ , ⊩v₂) →
    case conv-⊩ᵛ∷ (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩B) u₁≡u₂) ⊩v₂ of λ
      ⊩v₂ →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ ⊩t₁ ⊩u₁ ⊩v₁
      , conv-⊩ᵛ∷
          (sym-⊩ᵛ≡ $
           ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ (refl-⊩ᵛ≡ ⊩C) u₁≡u₂ v₁≡v₂)
          (⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ ⊩t₂ ⊩u₂ ⊩v₂)
      , λ ⊩σ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ [,]-[]-fusion t₁)
            (PE.sym $ [,]-[]-fusion t₂) (PE.sym $ [,]-[]-fusion C) $
          ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( (_ , ⊩B)
            , ( _
              , (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                   (PE.sym $ substConsId B) $
                 ⊩ᵛ≡∷⇔ .proj₁ v₁≡v₂ .proj₂ .proj₂ ⊩σ)
              )
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( wf-∙-⊩ᵛ ⊩B
                , (_ , ⊩ᵛ≡∷⇔ .proj₁ u₁≡u₂ .proj₂ .proj₂ ⊩σ)
                , refl-⊩ˢ≡∷ ⊩σ
                )
            )

      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ D →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l′ ⟩ t ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l ⟩ D [ t ]↑²
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² {A} {D} ⊩D ⊩t =
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
      , λ σ₁≡σ₂ →
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (substComp↑² D _) (substComp↑² D _) $
          ⊩ᵛ⇔ .proj₁ ⊩D .proj₂ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ ⊩D
            , ( _
              , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk2-tail A)
                  (⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔ .proj₁ (⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ .proj₂) .proj₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ D ≡ E →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l′ ⟩ t ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l ⟩ D [ t ]↑² ≡ E [ t ]↑²
  ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² {A} {D} {E} D≡E ⊩t =
    case ⊩ᵛ≡⇔ .proj₁ D≡E of λ
      (⊩D , ⊩E , D≡E) →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² ⊩D ⊩t
      , ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² ⊩E ⊩t
      , λ ⊩σ →
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (substComp↑² D _) (substComp↑² E _) $
          D≡E $
          ⊩ˢ∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ ⊩D
            , ( _
              , PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk2-tail A)
                  (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ)
              )
            , ⊩ˢ∷∙⇔ .proj₁ (⊩ˢ∷∙⇔ .proj₁ ⊩σ .proj₂) .proj₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ D →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l′ ⟩ u ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l ⟩ t [ u ]↑² ∷ D [ u ]↑²
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ {A} {t} {D} ⊩t ⊩u =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² (wf-⊩ᵛ∷ ⊩t) ⊩u
      , λ σ₁≡σ₂ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (substComp↑² t _) (substComp↑² t _)
            (substComp↑² D _) $
          ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
            , ( _
              , (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk2-tail A) $
                 ⊩ᵛ≡∷⇔′ .proj₁ (refl-⊩ᵛ≡∷ ⊩u) .proj₂ .proj₂ σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔ .proj₁ (⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ .proj₂) .proj₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ≡ u ∷ D →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l′ ⟩ v ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l ⟩ t [ v ]↑² ≡ u [ v ]↑² ∷ D [ v ]↑²
  ⊩ᵛ≡∷→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²∷ {A} {t} {u} {D} t≡u ⊩v =
    case wf-⊩ᵛ≡∷ t≡u of λ
      (⊩t , ⊩u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ ⊩t ⊩v
      , ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ ⊩u ⊩v
      , λ ⊩σ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (substComp↑² t _) (substComp↑² u _)
            (substComp↑² D _) $
          ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂ .proj₂ $
          ⊩ˢ∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
            , ( _
              , (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk2-tail A) $
                 ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩v ⊩σ)
              )
            , ⊩ˢ∷∙⇔ .proj₁ (⊩ˢ∷∙⇔ .proj₁ ⊩σ .proj₂) .proj₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B ≡ C →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ B [ t ]₀ ≡ C [ u ]₀
  ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ B≡C t≡u =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B≡C .proj₁) of λ
      (_ , ⊩A) →
    ⊩ᵛ≡⇔′ .proj₁ B≡C .proj₂ .proj₂
      (⊩ˢ≡∷-sgSubst ⊩A (level-⊩≡∷ (⊩ᵛ→⊩ ⊩A) t≡u))

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩[]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ B [ t ]₀
  ⊩ᵛ→⊩∷→⊩[]₀ ⊩B ⊩t =
    ⊩⇔⊩≡ .proj₂ $ ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ≡ u ∷ B →
    Γ ⊩⟨ l′ ⟩ v ≡ w ∷ A →
    Γ ⊩⟨ l ⟩ t [ v ]₀ ≡ u [ w ]₀ ∷ B [ v ]₀
  ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ t≡u v≡w =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u .proj₁)) of λ
      (_ , ⊩A) →
    ⊩ᵛ≡∷⇔′ .proj₁ t≡u .proj₂ .proj₂
      (⊩ˢ≡∷-sgSubst ⊩A (level-⊩≡∷ (⊩ᵛ→⊩ ⊩A) v≡w))

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩[]₀∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Γ ⊩⟨ l′ ⟩ u ∷ A →
    Γ ⊩⟨ l ⟩ t [ u ]₀ ∷ B [ u ]₀
  ⊩ᵛ∷→⊩∷→⊩[]₀∷ ⊩t ⊩u =
    ⊩∷⇔⊩≡∷ .proj₂ $ ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l ⟩ B₁ [ consSubst σ₁ t₁ ] ≡ B₂ [ consSubst σ₂ t₂ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] B₁≡B₂ σ₁≡σ₂ t₁≡t₂ =
    ⊩ᵛ≡⇔′ .proj₁ B₁≡B₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷∙⇔′ .proj₂ (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁) , (_ , t₁≡t₂) , σ₁≡σ₂)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[,] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    Δ ⊩⟨ l ⟩ B [ consSubst σ t ]
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[,] ⊩B ⊩σ ⊩t =
    ⊩⇔⊩≡ .proj₂ $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ) (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l ⟩ t₁ [ consSubst σ₁ u₁ ] ≡ t₂ [ consSubst σ₂ u₂ ] ∷
      B [ consSubst σ₁ u₁ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ t₁≡t₂ σ₁≡σ₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷∙⇔′ .proj₂
      (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁) , (_ , u₁≡u₂) , σ₁≡σ₂)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[,]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    Δ ⊩⟨ l ⟩ t [ consSubst σ u ] ∷ B [ consSubst σ u ]
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[,]∷ ⊩t ⊩σ ⊩u =
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ⊩⟨ l ⟩ B₁ [ σ₁ ⇑ ] ≡ B₂ [ σ₂ ⇑ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] B₁≡B₂ σ₁≡σ₂ =
    ⊩ᵛ≡⇔′ .proj₁ B₁≡B₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁) .proj₂) σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩[⇑] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊩⟨ l ⟩ B [ σ ⇑ ]
  ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ =
    ⊩⇔⊩≡ .proj₂ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ] ≡ t₂ [ σ₂ ⇑ ] ∷ B [ σ₁ ⇑ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ t₁≡t₂ σ₁≡σ₂ =
    ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) .proj₂)
      σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊩⟨ l ⟩ t [ σ ⇑ ] ∷ B [ σ ⇑ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ ⊩t ⊩σ =
    ⊩∷⇔⊩≡∷ .proj₂ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ∙ B [ σ₁ ⇑ ] ⊩⟨ l ⟩ C₁ [ σ₁ ⇑ ⇑ ] ≡ C₂ [ σ₂ ⇑ ⇑ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] C₁≡C₂ σ₁≡σ₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ≡ C₁≡C₂ .proj₁) of λ
      (_ , ⊩B) →
    ⊩ᵛ≡⇔′ .proj₁ C₁≡C₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst ⊩B $ ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ ⊩B .proj₂) σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ∙ B [ σ ⇑ ] ⊩⟨ l ⟩ C [ σ ⇑ ⇑ ]
  ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] ⊩C ⊩σ =
    ⊩⇔⊩≡ .proj₂ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] (refl-⊩ᵛ≡ ⊩C) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ∙ B [ σ₁ ⇑ ] ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ⇑ ] ≡ t₂ [ σ₂ ⇑ ⇑ ] ∷
      C [ σ₁ ⇑ ⇑ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ t₁≡t₂ σ₁≡σ₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) of λ
      (_ , ⊩B) →
    ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst ⊩B $ ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ ⊩B .proj₂) σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ∙ B [ σ ⇑ ] ⊩⟨ l ⟩ t [ σ ⇑ ⇑ ] ∷ C [ σ ⇑ ⇑ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ ⊩t ⊩σ =
    ⊩∷⇔⊩≡∷ .proj₂ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l ⟩ B₁ [ σ₁ ⇑ ] [ t₁ ]₀ ≡ B₂ [ σ₂ ⇑ ] [ t₂ ]₀
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ {B₁} {B₂} B₁≡B₂ σ₁≡σ₂ t₁≡t₂ =
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ singleSubstComp _ _ B₁)
      (PE.sym $ singleSubstComp _ _ B₂) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] B₁≡B₂ σ₁≡σ₂ t₁≡t₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    Δ ⊩⟨ l ⟩ B [ σ ⇑ ] [ t ]₀
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ ⊩B ⊩σ ⊩t =
    ⊩⇔⊩≡ .proj₂ $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ] [ u₁ ]₀ ≡ t₂ [ σ₂ ⇑ ] [ u₂ ]₀ ∷
      B [ σ₁ ⇑ ] [ u₁ ]₀
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ {t₁} {t₂} {B} t₁≡t₂ σ₁≡σ₂ u₁≡u₂ =
    PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
      (PE.sym $ singleSubstComp _ _ t₁)
      (PE.sym $ singleSubstComp _ _ t₂)
      (PE.sym $ singleSubstComp _ _ B) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ t₁≡t₂ σ₁≡σ₂ u₁≡u₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[⇑][]₀∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    Δ ⊩⟨ l ⟩ t [ σ ⇑ ] [ u ]₀ ∷ B [ σ ⇑ ] [ u ]₀
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[⇑][]₀∷ ⊩t ⊩σ ⊩u =
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Δ ⊩⟨ l′ ⟩ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ B₁ [ t₁ ]₀ [ σ₁ ] ≡ B₂ [ t₂ ]₀ [ σ₂ ]
  ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] {B₁} {B₂} B₁≡B₂ t₁[σ₁]≡t₂[σ₂] σ₁≡σ₂ =
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ singleSubstLift B₁ _)
      (PE.sym $ singleSubstLift B₂ _) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ B₁≡B₂ σ₁≡σ₂ t₁[σ₁]≡t₂[σ₂]

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩ˢ∷→⊩[]₀[] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩⟨ l′ ⟩ t [ σ ] ∷ A [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ B [ t ]₀ [ σ ]
  ⊩ᵛ→⊩∷→⊩ˢ∷→⊩[]₀[] {t} ⊩B ⊩t[σ] ⊩σ =
    ⊩⇔⊩≡ .proj₂ $
    ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] {t₂ = t} (refl-⊩ᵛ≡ ⊩B) (refl-⊩≡∷ ⊩t[σ])
      (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Δ ⊩⟨ l′ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ t₁ [ u₁ ]₀ [ σ₁ ] ≡ t₂ [ u₂ ]₀ [ σ₂ ] ∷ B [ u₁ ]₀ [ σ₁ ]
  ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ {t₁} {t₂} {B} t₁≡t₂ σ₁≡σ₂ u₁[σ₁]≡u₂[σ₂] =
    PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ singleSubstLift t₁ _)
      (PE.sym $ singleSubstLift t₂ _) (PE.sym $ singleSubstLift B _) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ t₁≡t₂ u₁[σ₁]≡u₂[σ₂] σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩ˢ∷→⊩[]₀[]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Δ ⊩⟨ l′ ⟩ u [ σ ] ∷ A [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ t [ u ]₀ [ σ ] ∷ B [ u ]₀ [ σ ]
  ⊩ᵛ∷→⊩∷→⊩ˢ∷→⊩[]₀[]∷ {u} ⊩t ⊩u[σ] ⊩σ =
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ {u₂ = u} (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩≡∷ ⊩u[σ])
      (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ u₁ ≡ u₂ ∷ B [ σ₁ ⇑ ] [ t₁ ]₀ →
    Δ ⊩⟨ l ⟩ C₁ [ σ₁ ⇑ ⇑ ] [ t₁ , u₁ ]₁₀ ≡ C₂ [ σ₂ ⇑ ⇑ ] [ t₂ , u₂ ]₁₀
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀
    {B} {C₁} {C₂} C₁≡C₂ σ₁≡σ₂ t₁≡t₂ u₁≡u₂ =
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ doubleSubstComp C₁ _ _ _)
      (PE.sym $ doubleSubstComp C₂ _ _ _) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] C₁≡C₂
      (⊩ˢ≡∷∙⇔′ .proj₂
         ( wf-∙-⊩ᵛ (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ C₁≡C₂ .proj₁) .proj₂)
         , (_ , t₁≡t₂)
         , σ₁≡σ₂
         )) $
    PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstComp _ _ B) u₁≡u₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑⇑][]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ u ∷ B [ σ ⇑ ] [ t ]₀ →
    Δ ⊩⟨ l ⟩ C [ σ ⇑ ⇑ ] [ t , u ]₁₀
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑⇑][]₁₀ ⊩C ⊩σ ⊩t ⊩u =
    ⊩⇔⊩≡ .proj₂ $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩C) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩t) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ v₁ ≡ v₂ ∷ B [ σ₁ ⇑ ] [ u₁ ]₀ →
    Δ ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ⇑ ] [ u₁ , v₁ ]₁₀ ≡ t₂ [ σ₂ ⇑ ⇑ ] [ u₂ , v₂ ]₁₀ ∷
      C [ σ₁ ⇑ ⇑ ] [ u₁ , v₁ ]₁₀
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷
    {B} {t₁} {t₂} {C} t₁≡t₂ σ₁≡σ₂ u₁≡u₂ v₁≡v₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) of λ
      (_ , ⊩B) →
    PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
      (PE.sym $ doubleSubstComp t₁ _ _ _)
      (PE.sym $ doubleSubstComp t₂ _ _ _)
      (PE.sym $ doubleSubstComp C _ _ _) $
    ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( (_ , ⊩B)
      , ( _
        , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstComp _ _ B) v₁≡v₂
        )
      , ⊩ˢ≡∷∙⇔′ .proj₂ (wf-∙-⊩ᵛ ⊩B , (_ , u₁≡u₂) , σ₁≡σ₂)
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩∷→⊩[⇑⇑][]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ v ∷ B [ σ ⇑ ] [ u ]₀ →
    Δ ⊩⟨ l ⟩ t [ σ ⇑ ⇑ ] [ u , v ]₁₀ ∷ C [ σ ⇑ ⇑ ] [ u , v ]₁₀
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩∷→⊩[⇑⇑][]₁₀∷ ⊩t ⊩σ ⊩u ⊩v =
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩u) (refl-⊩≡∷ ⊩v)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[] :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    Δ ⊩⟨ l′ ⟩ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ B [ t₁ ]₀ [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ C₁ [ t₁ , u₁ ]₁₀ [ σ₁ ] ≡ C₂ [ t₂ , u₂ ]₁₀ [ σ₂ ]
  ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]
    {B} {C₁} {C₂} C₁≡C₂ t₁[σ₁]≡t₂[σ₂] u₁[σ₁]≡u₂[σ₂] σ₁≡σ₂ =
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ [,]-[]-commute C₁)
      (PE.sym $ [,]-[]-commute C₂) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ C₁≡C₂ σ₁≡σ₂ t₁[σ₁]≡t₂[σ₂]
      (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B _)
         u₁[σ₁]≡u₂[σ₂])

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[] :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    Δ ⊩⟨ l′ ⟩ t [ σ ] ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ u [ σ ] ∷ B [ t ]₀ [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ C [ t , u ]₁₀ [ σ ]
  ⊩ᵛ→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[] {t} {u} ⊩C ⊩t[σ] ⊩u[σ] ⊩σ =
    ⊩⇔⊩≡ .proj₂ $
    ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[] {t₂ = t} {u₂ = u} (refl-⊩ᵛ≡ ⊩C)
      (refl-⊩≡∷ ⊩t[σ]) (refl-⊩≡∷ ⊩u[σ]) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    Δ ⊩⟨ l′ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ v₁ [ σ₁ ] ≡ v₂ [ σ₂ ] ∷ B [ u₁ ]₀ [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ t₁ [ u₁ , v₁ ]₁₀ [ σ₁ ] ≡ t₂ [ u₂ , v₂ ]₁₀ [ σ₂ ] ∷
      C [ u₁ , v₁ ]₁₀ [ σ₁ ]
  ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷
    {B} {t₁} {t₂} {C} t₁≡t₂ u₁[σ₁]≡u₂[σ₂] v₁[σ₁]≡v₂[σ₂] σ₁≡σ₂ =
    PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ [,]-[]-commute t₁)
      (PE.sym $ [,]-[]-commute t₂) (PE.sym $ [,]-[]-commute C) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ t₁≡t₂ σ₁≡σ₂ u₁[σ₁]≡u₂[σ₂]
      (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B _)
         v₁[σ₁]≡v₂[σ₂])

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[]∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    Δ ⊩⟨ l′ ⟩ u [ σ ] ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ v [ σ ] ∷ B [ u ]₀ [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ t [ u , v ]₁₀ [ σ ] ∷ C [ u , v ]₁₀ [ σ ]
  ⊩ᵛ∷→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[]∷ {u} {v} ⊩t ⊩u[σ] ⊩v[σ] ⊩σ =
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷ {u₂ = u} {v₂ = v} (refl-⊩ᵛ≡∷ ⊩t)
      (refl-⊩≡∷ ⊩u[σ]) (refl-⊩≡∷ ⊩v[σ]) (refl-⊩ˢ≡∷ ⊩σ)
