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

open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Hidden R {{eqrel}}
open import Definition.LogicalRelation.Properties R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as TW using (_∷_⊇_; _∷ʷ_⊇_)

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
  l l′ l″ l‴                                            : Universe-level

------------------------------------------------------------------------
-- The type formers

opaque mutual

  -- Valid contexts.

  infix 4 ⊩ᵛ_

  ⊩ᵛ_ : Con Term n → Set a
  ⊩ᵛ ε       = Lift _ ⊤
  ⊩ᵛ (Γ ∙ A) = Γ ⊩ᵛ A

  -- Valid types.

  infix 4 _⊩ᵛ_

  _⊩ᵛ_ : Con Term n → Term n → Set a
  Γ ⊩ᵛ A = Γ ⊩ᵛ A ≡ A

  -- Valid type equality.

  infix 4 _⊩ᵛ_≡_

  _⊩ᵛ_≡_ : Con Term n → Term n → Term n → Set a
  _⊩ᵛ_≡_ {n} Γ A B =
    ⊩ᵛ Γ ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     ∃ λ l → Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ])

  -- Valid substitution equality.

  infix 4 _⊩ˢ_≡_∷_

  _⊩ˢ_≡_∷_ : Con Term m → Subst m n → Subst m n → Con Term n → Set a
  Δ ⊩ˢ _  ≡ _  ∷ ε     = ⊢ Δ
  Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A =
    (∃ λ l →
     (Γ ⊩ᵛ A) ×
     Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ

opaque

  -- Valid substitutions.

  infix 4 _⊩ˢ_∷_

  _⊩ˢ_∷_ : Con Term m → Subst m n → Con Term n → Set a
  Δ ⊩ˢ σ ∷ Γ = Δ ⊩ˢ σ ≡ σ ∷ Γ

opaque

  -- Valid term equality.

  infix 4 _⊩ᵛ_≡_∷_

  _⊩ᵛ_≡_∷_ :
    Con Term n → Term n → Term n → Term n → Set a
  _⊩ᵛ_≡_∷_ {n} Γ t u A =
    Γ ⊩ᵛ A ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → ∃ λ l → Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ])

opaque

  -- Valid terms.

  infix 4 _⊩ᵛ_∷_

  _⊩ᵛ_∷_ : Con Term n → Term n → Term n → Set a
  Γ ⊩ᵛ t ∷ A = Γ ⊩ᵛ t ≡ t ∷ A

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

  ⊩ᵛ∙⇔ : ⊩ᵛ Γ ∙ A ⇔ Γ ⊩ᵛ A
  ⊩ᵛ∙⇔ = id⇔

opaque
  unfolding _⊩ᵛ_

  -- A characterisation lemma for _⊩ᵛ_.

  ⊩ᵛ⇔⊩ᵛ≡ : (Γ ⊩ᵛ A) ⇔ Γ ⊩ᵛ A ≡ A
  ⊩ᵛ⇔⊩ᵛ≡ = id⇔

opaque
  unfolding _⊩ᵛ_ _⊩ᵛ_≡_

  -- A characterisation lemma for _⊩ᵛ_.

  ⊩ᵛ⇔ :
    Γ ⊩ᵛ A ⇔
    (⊩ᵛ Γ ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → ∃ λ l → Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ A [ σ₂ ]))
  ⊩ᵛ⇔ = id⇔

opaque
  unfolding _⊩ᵛ_≡_

  -- A characterisation lemma for _⊩ᵛ_≡_.

  ⊩ᵛ≡⇔ :
    Γ ⊩ᵛ A ≡ B ⇔
    (⊩ᵛ Γ ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → ∃ λ l → Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ]))
  ⊩ᵛ≡⇔ = id⇔

opaque
  unfolding _⊩ᵛ_∷_

  -- A characterisation lemma for _⊩ᵛ_∷_.

  ⊩ᵛ∷⇔⊩ᵛ≡∷ : Γ ⊩ᵛ t ∷ A ⇔ Γ ⊩ᵛ t ≡ t ∷ A
  ⊩ᵛ∷⇔⊩ᵛ≡∷ = id⇔

opaque
  unfolding _⊩ᵛ_∷_ _⊩ᵛ_≡_∷_

  -- A characterisation lemma for _⊩ᵛ_∷_.

  ⊩ᵛ∷⇔ :
    Γ ⊩ᵛ t ∷ A ⇔
    (Γ ⊩ᵛ A ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      ∃ λ l → Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ∷⇔ = id⇔

opaque
  unfolding _⊩ᵛ_≡_∷_

  -- A characterisation lemma for _⊩ᵛ_≡_∷_.

  ⊩ᵛ≡∷⇔ :
    Γ ⊩ᵛ t ≡ u ∷ A ⇔
    (Γ ⊩ᵛ A ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      ∃ λ l → Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ≡∷⇔ = id⇔


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
      (Γ ⊩ᵛ A) ×
      Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
     Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ)
  ⊩ˢ≡∷∙⇔ = id⇔

opaque
  unfolding _⊩ˢ_∷_

  -- A characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷⇔⊩ˢ≡∷ : Δ ⊩ˢ σ ∷ Γ ⇔ Δ ⊩ˢ σ ≡ σ ∷ Γ
  ⊩ˢ∷⇔⊩ˢ≡∷ = id⇔

opaque

  -- A characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷ε⇔ : Δ ⊩ˢ σ ∷ ε ⇔ ⊢ Δ
  ⊩ˢ∷ε⇔ {Δ} {σ} =
    Δ ⊩ˢ σ ∷ ε      ⇔⟨ ⊩ˢ∷⇔⊩ˢ≡∷ ⟩
    Δ ⊩ˢ σ ≡ σ ∷ ε  ⇔⟨ ⊩ˢ≡∷ε⇔ ⟩
    ⊢ Δ             □⇔

opaque

  -- A characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷∙⇔ :
    Δ ⊩ˢ σ ∷ Γ ∙ A ⇔
    ((∃ λ l → (Γ ⊩ᵛ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
     Δ ⊩ˢ tail σ ∷ Γ)
  ⊩ˢ∷∙⇔ {Δ} {σ} {Γ} {A} =
    Δ ⊩ˢ σ ∷ Γ ∙ A                                              ⇔⟨ ⊩ˢ∷⇔⊩ˢ≡∷ ⟩

    Δ ⊩ˢ σ ≡ σ ∷ Γ ∙ A                                          ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩

    (∃ λ l →
     (Γ ⊩ᵛ A) ×
     Δ ⊩⟨ l ⟩ head σ ≡ head σ ∷ A [ tail σ ]) ×
    Δ ⊩ˢ tail σ ≡ tail σ ∷ Γ                                    ⇔˘⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → ⊩∷⇔⊩≡∷)
                                                                      ×-cong-⇔
                                                                    ⊩ˢ∷⇔⊩ˢ≡∷ ⟩
    (∃ λ l → (Γ ⊩ᵛ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    Δ ⊩ˢ tail σ ∷ Γ                                             □⇔

------------------------------------------------------------------------
-- An introduction lemma

opaque

  -- An introduction lemma for ⊩ᵛ_.

  ⊩ᵛ-∙-intro : Γ ⊩ᵛ A → ⊩ᵛ Γ ∙ A
  ⊩ᵛ-∙-intro = ⊩ᵛ∙⇔ .proj₂

opaque

  ⊩ᵛ-const-intro :
    (⊩ᵛ Γ ×
      (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ A [ σ₂ ]))
    → Γ ⊩ᵛ A
  ⊩ᵛ-const-intro (⊩Γ , f) = ⊩ᵛ⇔ .proj₂ (⊩Γ , λ s → _ , f s)

opaque

  ⊩ᵛ∷-const-intro :
    (Γ ⊩ᵛ A ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]))
    → Γ ⊩ᵛ t ∷ A
  ⊩ᵛ∷-const-intro (⊩A , f) = ⊩ᵛ∷⇔ .proj₂ (⊩A , λ s → _ , f s)

------------------------------------------------------------------------
-- Reflexivity

opaque

  -- Reflexivity for _⊩ˢ_≡_∷_.

  refl-⊩ˢ≡∷ :
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩ˢ σ ≡ σ ∷ Γ
  refl-⊩ˢ≡∷ = ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- Reflexivity for _⊩ᵛ_≡_.

  refl-⊩ᵛ≡ :
    Γ ⊩ᵛ A →
    Γ ⊩ᵛ A ≡ A
  refl-⊩ᵛ≡ = ⊩ᵛ⇔⊩ᵛ≡ .proj₁

opaque

  -- Reflexivity for _⊩ᵛ_≡_∷_.

  refl-⊩ᵛ≡∷ :
    Γ ⊩ᵛ t ∷ A →
    Γ ⊩ᵛ t ≡ t ∷ A
  refl-⊩ᵛ≡∷ = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

------------------------------------------------------------------------
-- Some substitution lemmas

opaque

<<<<<<< HEAD
  -- A substitution lemma for _⊩ᵛ_ and _⊩⟨_⟩_.
=======
  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A≡B = ⊩ᵛ≡⇔ .proj₁ A≡B .proj₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.
>>>>>>> master

  ⊩ᵛ→⊩ˢ∷→⊩[] :
    Γ ⊩ᵛ A →
    Δ ⊩ˢ σ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ A [ σ ]
  ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A =
    Σ.map idᶠ (⊩⇔⊩≡ .proj₂) ∘→ ⊩ᵛ⇔ .proj₁ ⊩A .proj₂ ∘→ refl-⊩ˢ≡∷

opaque

<<<<<<< HEAD
  -- A substitution lemma for _⊩ᵛ_∷_ and _⊩⟨_⟩_∷_.
=======
  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u = ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.
>>>>>>> master

  ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ :
    Γ ⊩ᵛ t ∷ A →
    Δ ⊩ˢ σ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ t [ σ ] ∷ A [ σ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t =
    Σ.map idᶠ (⊩∷⇔⊩≡∷ .proj₂) ∘→ ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ ∘→ refl-⊩ˢ≡∷

------------------------------------------------------------------------
-- Symmetry

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
    case conv-⊩≡∷ (⊩ᵛ⇔ .proj₁ ⊩A .proj₂ σ₁₊≡σ₂₊ .proj₂) $
         sym-⊩≡∷ σ₁₀≡σ₂₀ of λ
      σ₂₀≡σ₁₀ →
    ⊩ˢ≡∷∙⇔ .proj₂ ((_ , ⊩A , σ₂₀≡σ₁₀) , sym-⊩ˢ≡∷ σ₁₊≡σ₂₊)

opaque

  -- Symmetry for _⊩ᵛ_≡_.

  sym-⊩ᵛ≡ :
    Γ ⊩ᵛ A ≡ B →
    Γ ⊩ᵛ B ≡ A
  sym-⊩ᵛ≡ A≡B =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (⊩Γ , A≡B) →
    ⊩ᵛ≡⇔ .proj₂ (⊩Γ , Σ.map idᶠ sym-⊩≡ ∘→ A≡B ∘→ sym-⊩ˢ≡∷)

opaque

  -- Symmetry for _⊩ᵛ_≡_∷_.

  sym-⊩ᵛ≡∷ :
    Γ ⊩ᵛ t ≡ u ∷ A →
    Γ ⊩ᵛ u ≡ t ∷ A
  sym-⊩ᵛ≡∷ t≡u =
    case ⊩ᵛ≡∷⇔ .proj₁ t≡u of λ
      (⊩A , t≡u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩A
      , λ σ₁≡σ₂ → _ ,
        conv-⊩≡∷ (sym-⊩≡ (⊩ᵛ⇔ .proj₁ ⊩A .proj₂ σ₁≡σ₂ .proj₂))
          (sym-⊩≡∷ (t≡u (sym-⊩ˢ≡∷ σ₁≡σ₂) .proj₂)))

------------------------------------------------------------------------
-- One transitivity lemma

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
    case conv-⊩≡∷ (⊩ᵛ⇔ .proj₁ ⊩A .proj₂ (sym-⊩ˢ≡∷ σ₁₊≡σ₂₊) .proj₂) σ₂₀≡σ₃₀ of λ
      σ₂₀≡σ₃₀ →
    ⊩ˢ≡∷∙⇔ .proj₂
      ( (_ , ⊩A , trans-⊩≡∷ σ₁₀≡σ₂₀ σ₂₀≡σ₃₀)
      , trans-⊩ˢ≡ σ₁₊≡σ₂₊ σ₂₊≡σ₃₊
      )

------------------------------------------------------------------------
-- Some well-formedness lemmas

opaque

  -- A well-formedness lemma for ⊩ᵛ_.

  wf-⊩ᵛ-∙ : ⊩ᵛ Γ ∙ A → Γ ⊩ᵛ A
  wf-⊩ᵛ-∙ = ⊩ᵛ∙⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ᵛ_.

  wf-⊩ᵛ : Γ ⊩ᵛ A → ⊩ᵛ Γ
  wf-⊩ᵛ = proj₁ ∘→ ⊩ᵛ⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ᵛ_.

  wf-∙-⊩ᵛ : Γ ∙ A ⊩ᵛ B → Γ ⊩ᵛ A
  wf-∙-⊩ᵛ = wf-⊩ᵛ-∙ ∘→ wf-⊩ᵛ

opaque

  -- A well-formedness lemma for _⊩ᵛ_∷_.

  wf-⊩ᵛ∷ : Γ ⊩ᵛ t ∷ A → Γ ⊩ᵛ A
  wf-⊩ᵛ∷ = proj₁ ∘→ ⊩ᵛ∷⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ˢ_∷_.

  wf-⊩ˢ∷ : Δ ⊩ˢ σ ∷ Γ → ⊩ᵛ Γ
  wf-⊩ˢ∷ {Γ = ε}     = λ _ → ⊩ᵛε⇔ .proj₂ _
  wf-⊩ˢ∷ {Γ = _ ∙ _} =
    ⊩ᵛ∙⇔ .proj₂ ∘→ proj₁ ∘→ proj₂ ∘→ proj₁ ∘→ ⊩ˢ∷∙⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ˢ_≡_∷_.

  wf-⊩ˢ≡∷ : Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩ˢ σ₁ ∷ Γ × Δ ⊩ˢ σ₂ ∷ Γ
  wf-⊩ˢ≡∷ σ₁≡σ₂ =
      ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ (trans-⊩ˢ≡ σ₁≡σ₂ (sym-⊩ˢ≡∷ σ₁≡σ₂))
    , ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ (trans-⊩ˢ≡ (sym-⊩ˢ≡∷ σ₁≡σ₂) σ₁≡σ₂)

------------------------------------------------------------------------
-- Changing type levels

opaque

  -- Changing type levels for _⊩ᵛ_≡_.

  level-⊩ᵛ≡ :
    Γ ⊩ᵛ A →
    Γ ⊩ᵛ B →
    Γ ⊩ᵛ A ≡ B →
    Γ ⊩ᵛ A ≡ B
  level-⊩ᵛ≡ ⊩A ⊩B A≡B = A≡B

opaque

  -- Changing type levels for _⊩ᵛ_≡_∷_.

  level-⊩ᵛ≡∷ :
<<<<<<< HEAD
    Γ ⊩ᵛ A →
    Γ ⊩ᵛ t ≡ u ∷ A →
    Γ ⊩ᵛ t ≡ u ∷ A
  level-⊩ᵛ≡∷ ⊩A t≡u = t≡u
=======
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A
  level-⊩ᵛ≡∷ ⊩A t≡u =
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩A
      , λ σ₁≡σ₂ →
          level-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) $
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u σ₁≡σ₂
      )
>>>>>>> master

opaque

  -- Changing type levels for _⊩ᵛ_∷_.

  level-⊩ᵛ∷ :
    Γ ⊩ᵛ A →
    Γ ⊩ᵛ t ∷ A →
    Γ ⊩ᵛ t ∷ A
  level-⊩ᵛ∷ ⊩A = idᶠ

------------------------------------------------------------------------
-- More transitivity lemmas

opaque
  unfolding refl-⊩ˢ≡∷ ⊩ˢ∷⇔⊩ˢ≡∷ wf-⊩ˢ≡∷ trans-⊩ˢ≡ sym-⊩ˢ≡∷

  -- Transitivity for _⊩ᵛ_≡_.

  trans-⊩ᵛ≡ :
    Γ ⊩ᵛ A ≡ B →
    Γ ⊩ᵛ B ≡ C →
    Γ ⊩ᵛ A ≡ C
  trans-⊩ᵛ≡ {A} {B} {C} A≡B B≡C =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (⊩Γ , A≡B) →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩Γ
<<<<<<< HEAD
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ → _ ,
        trans′-⊩≡
          (A≡B (refl-⊩ˢ≡∷ (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)) .proj₂)
          (B≡C σ₁≡σ₂ .proj₂)
=======
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          A [ σ₁ ]  ≡⟨ A≡B $ refl-⊩ˢ≡∷ (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) ⟩⊩
          B [ σ₁ ]  ≡⟨ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B≡C σ₁≡σ₂ ⟩⊩∎
          C [ σ₂ ]  ∎
>>>>>>> master
      )

opaque

  -- Transitivity for _⊩ᵛ_≡_∷_.

  trans-⊩ᵛ≡∷ :
    Γ ⊩ᵛ t ≡ u ∷ A →
    Γ ⊩ᵛ u ≡ v ∷ A →
    Γ ⊩ᵛ t ≡ v ∷ A
  trans-⊩ᵛ≡∷ {t} {u} {v} t≡u u≡v =
    case ⊩ᵛ≡∷⇔ .proj₁ u≡v of λ
      (⊩A , u≡v) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩A
<<<<<<< HEAD
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ → _ , (
          t [ σ₁ ]  ≡⟨ t≡u (refl-⊩ˢ≡∷ (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)) .proj₂ ⟩⊩∷
          u [ σ₁ ]  ≡⟨ u≡v σ₁≡σ₂ .proj₂ ⟩⊩∷∎
          v [ σ₂ ]  ∎)
=======
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          t [ σ₁ ]  ≡⟨ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (level-⊩ᵛ≡∷ ⊩A t≡u) $
                       refl-⊩ˢ≡∷ (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) ⟩⊩∷
          u [ σ₁ ]  ≡⟨ u≡v σ₁≡σ₂ ⟩⊩∷∎
          v [ σ₂ ]  ∎
>>>>>>> master
      )

------------------------------------------------------------------------
-- More well-formedness lemmas

opaque

  -- A well-formedness lemma for _⊩ᵛ_≡_.

  wf-⊩ᵛ≡ : Γ ⊩ᵛ A ≡ B → Γ ⊩ᵛ A × Γ ⊩ᵛ B
  wf-⊩ᵛ≡ A≡B =
      ⊩ᵛ⇔⊩ᵛ≡ .proj₂ (trans-⊩ᵛ≡ A≡B (sym-⊩ᵛ≡ A≡B))
    , ⊩ᵛ⇔⊩ᵛ≡ .proj₂ (trans-⊩ᵛ≡ (sym-⊩ᵛ≡ A≡B) A≡B)

opaque

  -- A well-formedness lemma for _⊩ᵛ_≡_∷_.

  wf-⊩ᵛ≡∷ : Γ ⊩ᵛ t ≡ u ∷ A → Γ ⊩ᵛ t ∷ A × Γ ⊩ᵛ u ∷ A
  wf-⊩ᵛ≡∷ t≡u =
      ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (trans-⊩ᵛ≡∷ t≡u (sym-⊩ᵛ≡∷ t≡u))
    , ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (trans-⊩ᵛ≡∷ (sym-⊩ᵛ≡∷ t≡u) t≡u)

------------------------------------------------------------------------
-- More characterisation lemmas

opaque

  -- A variant of ⊩ᵛ≡⇔.

  ⊩ᵛ≡⇔′ :
    Γ ⊩ᵛ A ≡ B ⇔
    (Γ ⊩ᵛ A ×
     Γ ⊩ᵛ B ×
     (∀ {m Δ} {σ : Subst m n} →
      Δ ⊩ˢ σ ∷ Γ →
      ∃ λ l → Δ ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ]))
  ⊩ᵛ≡⇔′ {A} {B} =
      (λ A≡B →
         case wf-⊩ᵛ≡ A≡B of λ
           (⊩A , ⊩B) →
         ⊩A , ⊩B , λ {_ _ _} → ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A≡B ∘→ refl-⊩ˢ≡∷)
    , (λ (⊩A , _ , A≡B) →
         ⊩ᵛ≡⇔ .proj₂
           ( wf-⊩ᵛ ⊩A
           , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ → _ ,
               trans′-⊩≡
                (⊩ᵛ⇔ .proj₁ ⊩A .proj₂ σ₁≡σ₂ .proj₂)
                (A≡B (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₂) .proj₂)))

opaque

  -- A variant of ⊩ᵛ≡⇔.

  ⊩ᵛ≡⇔″ :
    Γ ⊩ᵛ A ≡ B ⇔
    (Γ ⊩ᵛ A ×
     Γ ⊩ᵛ B ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      ∃ λ l → Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ]))
  ⊩ᵛ≡⇔″ =
      (λ A≡B →
         case wf-⊩ᵛ≡ A≡B of λ
           (⊩A , ⊩B) →
         ⊩A , ⊩B , λ {_ _ _ _} → ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A≡B)
    , (λ (⊩A , _ , A≡B) →
         ⊩ᵛ≡⇔ .proj₂ (wf-⊩ᵛ ⊩A , A≡B))

opaque

  -- A variant of ⊩ᵛ≡∷⇔.

  ⊩ᵛ≡∷⇔′ :
    Γ ⊩ᵛ t ≡ u ∷ A ⇔
    (Γ ⊩ᵛ t ∷ A ×
     Γ ⊩ᵛ u ∷ A ×
     (∀ {m Δ} {σ : Subst m n} →
      Δ ⊩ˢ σ ∷ Γ →
      ∃ λ l → Δ ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ]))
  ⊩ᵛ≡∷⇔′ {t} {u} =
      (λ t≡u →
         case wf-⊩ᵛ≡∷ t≡u of λ
           (⊩t , ⊩u) →
         ⊩t , ⊩u , λ {_ _ _} → ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u ∘→ refl-⊩ˢ≡∷)
    , (λ (_ , ⊩u , t≡u) →
         ⊩ᵛ≡∷⇔ .proj₂
           ( wf-⊩ᵛ∷ ⊩u
           , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ → _ , (
               t [ σ₁ ]  ≡⟨ t≡u (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) .proj₂ ⟩⊩∷
               u [ σ₁ ]  ≡⟨ ⊩ᵛ∷⇔ .proj₁ ⊩u .proj₂ σ₁≡σ₂ .proj₂ ⟩⊩∷∎
               u [ σ₂ ]  ∎)
           ))

opaque

  -- A variant of ⊩ᵛ≡∷⇔.

  ⊩ᵛ≡∷⇔″ :
    Γ ⊩ᵛ t ≡ u ∷ A ⇔
    (Γ ⊩ᵛ t ∷ A ×
     Γ ⊩ᵛ u ∷ A ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      ∃ λ l → Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ≡∷⇔″ =
      (λ t≡u →
         case wf-⊩ᵛ≡∷ t≡u of λ
           (⊩t , ⊩u) →
         ⊩t , ⊩u , λ {_ _ _ _} → ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u)
    , (λ (⊩t , _ , t≡u) →
         ⊩ᵛ≡∷⇔ .proj₂ (wf-⊩ᵛ∷ ⊩t , t≡u))

opaque

  -- A variant of ⊩ˢ∷∙⇔.

  ⊩ˢ∷∙⇔′ :
    Δ ⊩ˢ σ ∷ Γ ∙ A ⇔
    ((Γ ⊩ᵛ A) ×
     (∃ λ l → Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
     Δ ⊩ˢ tail σ ∷ Γ)
  ⊩ˢ∷∙⇔′ {Δ} {σ} {Γ} {A} =
    Δ ⊩ˢ σ ∷ Γ ∙ A                                              ⇔⟨ ⊩ˢ∷∙⇔ ⟩

    (∃ λ l → (Γ ⊩ᵛ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    Δ ⊩ˢ tail σ ∷ Γ
                                                                ⇔⟨ (λ ((l , ⊩A , ⊩head) , ⊩tail) →
                                                                      ⊩A , (l , ⊩head) , ⊩tail)
                                                                 , (λ (⊩A , (l , ⊩head) , ⊩tail) →
                                                                      (_ , ⊩A , level-⊩∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩tail .proj₂) ⊩head) , ⊩tail)
                                                                 ⟩
    (Γ ⊩ᵛ A) ×
    (∃ λ l → Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    Δ ⊩ˢ tail σ ∷ Γ                                             □⇔

opaque

  -- A variant of ⊩ˢ≡∷∙⇔.

  ⊩ˢ≡∷∙⇔′ :
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A ⇔
    ((Γ ⊩ᵛ A) ×
     (∃ λ l → Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
     Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ)
  ⊩ˢ≡∷∙⇔′ {Δ} {σ₁} {σ₂} {Γ} {A} =
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A                                            ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩

    (∃ λ l →
     (Γ ⊩ᵛ A) × Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                      ⇔⟨ (λ ((l , ⊩A , head≡head) , tail≡tail) →
                                                                          ⊩A , (l , head≡head) , tail≡tail)
                                                                     , (λ (⊩A , (l , head≡head) , tail≡tail) →
                                                                            ( _ , ⊩A
                                                                            , level-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A (wf-⊩ˢ≡∷ tail≡tail .proj₁) .proj₂)
                                                                                head≡head
                                                                            )
                                                                          , tail≡tail)
                                                                     ⟩
    (Γ ⊩ᵛ A) ×
    (∃ λ l → Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                      □⇔

------------------------------------------------------------------------
-- Conversion

opaque

  -- Conversion for one of the contexts for _⊩ˢ_≡_∷_.

  conv-⊩ˢ≡∷-∙ :
    Γ ⊩ᵛ A ≡ B → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ B
  conv-⊩ˢ≡∷-∙ {Γ} {A} {B} {Δ} {σ₁} {σ₂} A≡B =
    case ⊩ᵛ≡⇔′ .proj₁ A≡B of λ
      (_ , ⊩B , A≡B) →

    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A                                            ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

    (∃ λ l →
     (Γ ⊩ᵛ A) × Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                      →⟨ (λ ((_ , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                            (_ , ⊩B , conv-⊩≡∷ (A≡B (wf-⊩ˢ≡∷ σ₁₊≡σ₂₊ .proj₁) .proj₂) σ₁₀≡σ₂₀)
                                                                          , σ₁₊≡σ₂₊) ⟩
    (∃ λ l →
     (Γ ⊩ᵛ B) × Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                      ⇔˘⟨ ⊩ˢ≡∷∙⇔ ⟩→

    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ B                                            □

opaque

  -- Conversion for one of the contexts for _⊩ˢ_∷_.

  conv-⊩ˢ∷-∙ : Γ ⊩ᵛ A ≡ B → Δ ⊩ˢ σ ∷ Γ ∙ A → Δ ⊩ˢ σ ∷ Γ ∙ B
  conv-⊩ˢ∷-∙ A≡B =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ conv-⊩ˢ≡∷-∙ A≡B ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- Conversion for the context for _⊩ᵛ_.

  conv-∙-⊩ᵛ :
    Γ ⊩ᵛ A ≡ B →
    Γ ∙ A ⊩ᵛ C →
    Γ ∙ B ⊩ᵛ C
  conv-∙-⊩ᵛ {Γ} {A} {B} {C} A≡B ⊩C =
    case ⊩ᵛ≡⇔′ .proj₁ A≡B of λ
      (⊩A , ⊩B , A≡B) →
    ⊩ᵛ⇔ .proj₂
      ( ⊩ᵛ-∙-intro ⊩B
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ B                            ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

          (∃ λ l →
           (Γ ⊩ᵛ B) ×
           Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B [ tail σ₁ ]) ×
          Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                      →⟨ (λ ((_ , _ , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                  (_ , ⊩A , conv-⊩≡∷ (sym-⊩≡ $ A≡B (wf-⊩ˢ≡∷ σ₁₊≡σ₂₊ .proj₁) .proj₂) σ₁₀≡σ₂₀)
                                                                , σ₁₊≡σ₂₊) ⟩
          (∃ λ l →
           (Γ ⊩ᵛ A) ×
           Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
          Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                      ⇔˘⟨ ⊩ˢ≡∷∙⇔ ⟩→

          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A                            →⟨ ⊩ᵛ⇔ .proj₁ ⊩C .proj₂ ⟩

          (∃ λ l → Δ ⊩⟨ l ⟩ C [ σ₁ ] ≡ C [ σ₂ ])          □
      )

opaque

  -- Another kind of conversion for the context for _⊩ᵛ_.

  conv-∙∙-⊩ᵛ :
    Γ ⊩ᵛ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ B₁ ≡ B₂ →
    Γ ∙ A₁ ∙ B₁ ⊩ᵛ C →
    Γ ∙ A₂ ∙ B₂ ⊩ᵛ C
  conv-∙∙-⊩ᵛ {Γ} {A₁} {A₂} {B₁} {B₂} {C} A₁≡A₂ B₁≡B₂ ⊩C =
    case sym-⊩ᵛ≡ A₁≡A₂ of λ
      A₂≡A₁ →
    case ⊩ᵛ≡⇔′ .proj₁ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂ , B₁≡B₂) →
    ⊩ᵛ⇔ .proj₂
      ( ⊩ᵛ-∙-intro (conv-∙-⊩ᵛ A₁≡A₂ ⊩B₂)
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A₂ ∙ B₂                       ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

          (∃ λ l →
           (Γ ∙ A₂ ⊩ᵛ B₂) ×
           Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B₂ [ tail σ₁ ]) ×
          Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ ∙ A₂                  →⟨ ((λ ((_ , _ , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                   ( _ , ⊩B₁
                                                                   , conv-⊩≡∷
                                                                       (sym-⊩≡ $ B₁≡B₂ (
                                                                        conv-⊩ˢ∷-∙ A₂≡A₁ $ wf-⊩ˢ≡∷ σ₁₊≡σ₂₊ .proj₁) .proj₂)
                                                                       σ₁₀≡σ₂₀
                                                                   )
                                                                 , conv-⊩ˢ≡∷-∙ A₂≡A₁ σ₁₊≡σ₂₊)) ⟩
          (∃ λ l →
           (Γ ∙ A₁ ⊩ᵛ B₁) ×
           Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B₁ [ tail σ₁ ]) ×
          Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ ∙ A₁                  ⇔˘⟨ ⊩ˢ≡∷∙⇔ ⟩→

          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A₁ ∙ B₁                       →⟨ ⊩ᵛ⇔ .proj₁ ⊩C .proj₂ ⟩

          (∃ λ l → Δ ⊩⟨ l ⟩ C [ σ₁ ] ≡ C [ σ₂ ])           □
      )

opaque

  -- Conversion for _⊩ᵛ_≡_∷_.

  conv-⊩ᵛ≡∷ :
    Γ ⊩ᵛ A ≡ B →
    Γ ⊩ᵛ t ≡ u ∷ A →
    Γ ⊩ᵛ t ≡ u ∷ B
  conv-⊩ᵛ≡∷ A≡B t≡u =
    case ⊩ᵛ≡⇔′ .proj₁ A≡B of λ
      (_ , ⊩B , A≡B) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩B
<<<<<<< HEAD
      , λ σ₁≡σ₂ → _ , (
          conv-⊩≡∷ (A≡B (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) .proj₂) $
          ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂ σ₁≡σ₂ .proj₂)
=======
      , λ σ₁≡σ₂ →
          conv-⊩≡∷ (A≡B $ wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) $
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u σ₁≡σ₂
>>>>>>> master
      )

opaque

  -- Conversion for _⊩ᵛ_∷_.

  conv-⊩ᵛ∷ :
    Γ ⊩ᵛ A ≡ B →
    Γ ⊩ᵛ t ∷ A →
    Γ ⊩ᵛ t ∷ B
  conv-⊩ᵛ∷ A≡B =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ conv-⊩ᵛ≡∷ A≡B ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

opaque

  -- Conversion for the context for _⊩ᵛ_∷_.

  conv-∙-⊩ᵛ∷ :
    Γ ⊩ᵛ A ≡ B →
    Γ ∙ A ⊩ᵛ t ∷ C →
    Γ ∙ B ⊩ᵛ t ∷ C
  conv-∙-⊩ᵛ∷ A≡B ⊩t =
    case ⊩ᵛ∷⇔ .proj₁ ⊩t of λ
      (⊩C , t≡t) →
    ⊩ᵛ∷⇔ .proj₂
      ( conv-∙-⊩ᵛ A≡B ⊩C
      , t≡t ∘→ conv-⊩ˢ≡∷-∙ (sym-⊩ᵛ≡ A≡B)
      )

------------------------------------------------------------------------
-- Expansion

opaque

  -- An expansion lemma for _⊩ᵛ_∷_.

  ⊩ᵛ∷-⇐ :
    (∀ {m Δ} {σ : Subst m n} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊢ t [ σ ] ⇒ u [ σ ] ∷ A [ σ ]) →
    Γ ⊩ᵛ u ∷ A →
    Γ ⊩ᵛ t ≡ u ∷ A
  ⊩ᵛ∷-⇐ {t} {u} t⇒u ⊩u =
    case ⊩ᵛ∷⇔ .proj₁ ⊩u of λ
      (⊩A , u≡u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩A
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
            (⊩σ₁ , _) →
<<<<<<< HEAD
          case ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ₁ .proj₂ of λ
            ⊩u[σ₁] → _ , (
          t [ σ₁ ]  ≡⟨ ⊩∷-⇐* (t⇒u ⊩σ₁ ⇨ id (escape-⊩∷ ⊩u[σ₁])) ⊩u[σ₁] ⟩⊩∷
          u [ σ₁ ]  ≡⟨ u≡u σ₁≡σ₂ .proj₂ ⟩⊩∷∎
          u [ σ₂ ]  ∎)
=======
          t [ σ₁ ]  ≡⟨ ⊩∷-⇐* (redMany (t⇒u ⊩σ₁)) (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ₁) ⟩⊩∷
          u [ σ₁ ]  ≡⟨ u≡u σ₁≡σ₂ ⟩⊩∷∎
          u [ σ₂ ]  ∎
>>>>>>> master
      )

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
    ρ ∷ʷ Η ⊇ Δ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Η ⊩ˢ ρ •ₛ σ₁ ≡ ρ •ₛ σ₂ ∷ Γ
  ⊩ˢ≡∷-•ₛ {Γ = ε} ρ⊇ _ =
    ⊩ˢ≡∷ε⇔ .proj₂ (TW.wf-∷ʷ⊇ ρ⊇)
  ⊩ˢ≡∷-•ₛ {Γ = _ ∙ A} ρ⊇ σ₁≡σ₂ =
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((_ , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
    ⊩ˢ≡∷∙⇔ .proj₂
      ( ( _ , ⊩A
        , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A)
            (wk-⊩≡∷ ρ⊇ σ₁₀≡σ₂₀)
        )
      , ⊩ˢ≡∷-•ₛ ρ⊇ σ₁₊≡σ₂₊
      )

opaque

  -- A lemma related to _•ₛ_.

  ⊩ˢ∷-•ₛ :
    ρ ∷ʷ Η ⊇ Δ →
    Δ ⊩ˢ σ ∷ Γ →
    Η ⊩ˢ ρ •ₛ σ ∷ Γ
  ⊩ˢ∷-•ₛ ρ⊇ =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-•ₛ ρ⊇ ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

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
      ⊩A →
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((_ , _ , head≡head) , tail≡tail) →
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( ⊩A
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
  ⊩ˢ≡∷-wk1Subst ⊢A = ⊩ˢ≡∷-•ₛ (TW.stepʷ TW.id ⊢A)

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
    Γ ⊩ᵛ A →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ⊩ˢ liftSubst σ₁ ≡ liftSubst σ₂ ∷ Γ ∙ A
  ⊩ˢ≡∷-liftSubst {A} ⊩A σ₁≡σ₂ =
    case escape-⊩ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) .proj₂ of λ
      ⊢A[σ₁] →
    case ⊩ˢ≡∷-wk1Subst ⊢A[σ₁] σ₁≡σ₂ of λ
      σ₁⇑₊≡σ₂⇑₊ →
    case var (∙ ⊢A[σ₁])
           (PE.subst₂ (_∷_∈_ _) (PE.sym $ wk1Subst-wk1 A) PE.refl
              here) of λ
      ⊢0 →
    ⊩ˢ≡∷∙⇔ .proj₂
      ( ( _ , ⊩A
<<<<<<< HEAD
        , neutral-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A (wf-⊩ˢ≡∷ σ₁⇑₊≡σ₂⇑₊ .proj₁) .proj₂)
            (var _) (var _) ⊢0 ⊢0 (~-var ⊢0)
=======
        , neutral-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ wf-⊩ˢ≡∷ σ₁⇑₊≡σ₂⇑₊ .proj₁)
            (var _) (var _) (~-var ⊢0)
>>>>>>> master
        )
      , σ₁⇑₊≡σ₂⇑₊
      )

opaque

  -- A lemma related to liftSubst.

  ⊩ˢ∷-liftSubst :
    Γ ⊩ᵛ A →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊩ˢ liftSubst σ ∷ Γ ∙ A
  ⊩ˢ∷-liftSubst ⊩A =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-liftSubst ⊩A ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A variant of ⊩ˢ≡∷-liftSubst.

  ⊩ˢ≡∷-liftSubst′ :
    Γ ⊩ᵛ A₁ ≡ A₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A₁ [ σ₁ ] ⊩ˢ liftSubst σ₁ ≡ liftSubst σ₂ ∷ Γ ∙ A₂
  ⊩ˢ≡∷-liftSubst′ {A₁} {A₂} {σ₁} A₁≡A₂ σ₁≡σ₂ =
    conv-⊩ˢ≡∷-∙ A₁≡A₂ $
    ⊩ˢ≡∷-liftSubst (wf-⊩ᵛ≡ A₁≡A₂ .proj₁) σ₁≡σ₂

opaque

  -- A variant of ⊩ˢ∷-liftSubst.

  ⊩ˢ∷-liftSubst′ :
    Γ ⊩ᵛ A₁ ≡ A₂ →
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
    case ⊩ᵛ∙⇔ .proj₁ ⊩Γ∙A of λ
      ⊩A →
    PE.subst₃ _⊩ˢ_∷_ (PE.cong (_∙_ _) $ subst-id _) PE.refl PE.refl $
    cast-⊩ˢ∷ subst-lift-id $
    ⊩ˢ∷-liftSubst (⊩ᵛ∙⇔ .proj₁ ⊩Γ∙A)
      (⊩ˢ∷-idSubst (⊩ᵛ⇔ .proj₁ ⊩A .proj₁))

opaque

  -- A lemma related to sgSubst.

  ⊩ˢ≡∷-sgSubst :
    Γ ⊩ᵛ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩ˢ sgSubst t ≡ sgSubst u ∷ Γ ∙ A
  ⊩ˢ≡∷-sgSubst ⊩A t≡u =
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( ⊩A
      , (_ , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ subst-id _) t≡u)
      , refl-⊩ˢ≡∷ (⊩ˢ∷-idSubst (wf-⊩ᵛ ⊩A))
      )

opaque

  -- A lemma related to sgSubst.

  ⊩ˢ∷-sgSubst :
    Γ ⊩ᵛ A →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩ˢ sgSubst t ∷ Γ ∙ A
  ⊩ˢ∷-sgSubst ⊩A =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-sgSubst ⊩A ∘→ ⊩∷⇔⊩≡∷ .proj₁

------------------------------------------------------------------------
-- Reducibility from validity

opaque

  -- If there is a valid equality between A and B, then there is a
  -- reducible equality between A and B.

  ⊩ᵛ≡→⊩≡ : Γ ⊩ᵛ A ≡ B → ∃ λ l → Γ ⊩⟨ l ⟩ A ≡ B
  ⊩ᵛ≡→⊩≡ {Γ} {A} {B} =
    Γ ⊩ᵛ A ≡ B                            ⇔⟨ ⊩ᵛ≡⇔′ ⟩→

    (Γ ⊩ᵛ A) ×
    (Γ ⊩ᵛ B) ×
    (∀ {m} {Δ : Con Term m} {σ} →
     Δ ⊩ˢ σ ∷ Γ → ∃ λ l → Δ ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ])  →⟨ (λ (⊩A , _ , A≡B) → A≡B $ ⊩ˢ∷-idSubst $ wf-⊩ᵛ ⊩A) ⟩

    (∃ λ l → Γ ⊩⟨ l ⟩ A [ idSubst ] ≡ B [ idSubst ])     →⟨ Σ.map idᶠ (PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (subst-id _) (subst-id _)) ⟩

    (∃ λ l → Γ ⊩⟨ l ⟩ A ≡ B)                             □

opaque

  -- If A is valid, then A is reducible.

  ⊩ᵛ→⊩ : Γ ⊩ᵛ A → ∃ λ l → Γ ⊩⟨ l ⟩ A
  ⊩ᵛ→⊩ = Σ.map idᶠ (⊩⇔⊩≡ .proj₂) ∘→ ⊩ᵛ≡→⊩≡ ∘→ ⊩ᵛ⇔⊩ᵛ≡ .proj₁

opaque

  -- If there is a valid equality between t and u, then there is a
  -- reducible equality between t and u.

  ⊩ᵛ≡∷→⊩≡∷ : Γ ⊩ᵛ t ≡ u ∷ A → ∃ λ l → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩ᵛ≡∷→⊩≡∷ {Γ} {t} {u} {A} =
    Γ ⊩ᵛ t ≡ u ∷ A                                     ⇔⟨ ⊩ᵛ≡∷⇔′ ⟩→

    (Γ ⊩ᵛ t ∷ A) ×
    (Γ ⊩ᵛ u ∷ A) ×
    (∀ {m} {Δ : Con Term m} {σ} →
     Δ ⊩ˢ σ ∷ Γ → ∃ λ l → Δ ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ])     →⟨ (λ (⊩t , _ , t≡u) → t≡u $ ⊩ˢ∷-idSubst $ wf-⊩ᵛ $ wf-⊩ᵛ∷ ⊩t) ⟩

    (∃ λ l → Γ ⊩⟨ l ⟩ t [ idSubst ] ≡ u [ idSubst ] ∷ A [ idSubst ])  →⟨ Σ.map idᶠ (PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
                                                                 (subst-id _) (subst-id _) (subst-id _)) ⟩

    (∃ λ l → Γ ⊩⟨ l ⟩ t ≡ u ∷ A)                                      □

opaque

  -- If t is valid, then t is reducible.

  ⊩ᵛ∷→⊩∷ : Γ ⊩ᵛ t ∷ A → ∃ λ l → Γ ⊩⟨ l ⟩ t ∷ A
  ⊩ᵛ∷→⊩∷ = Σ.map idᶠ (⊩∷⇔⊩≡∷ .proj₂) ∘→ ⊩ᵛ≡∷→⊩≡∷ ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

------------------------------------------------------------------------
-- Escape lemmas

opaque

  -- An escape lemma for _⊩ᵛ_.

  escape-⊩ᵛ : Γ ⊩ᵛ A → Γ ⊢ A
  escape-⊩ᵛ = escape-⊩ ∘→ proj₂ ∘→ ⊩ᵛ→⊩

opaque

  -- An escape lemma for ⊩ᵛ_.

  escape-⊩ᵛ′ : ⊩ᵛ Γ → ⊢ Γ
  escape-⊩ᵛ′ {Γ = ε}     = λ _ → ε
<<<<<<< HEAD
  escape-⊩ᵛ′ {Γ = _ ∙ _} = ⊢→⊢∙ ∘→ escape-⊩ᵛ ∘→ ⊩ᵛ∙⇔ .proj₁
=======
  escape-⊩ᵛ′ {Γ = _ ∙ _} = ∙_ ∘→ escape-⊩ᵛ ∘→ proj₂ ∘→ ⊩ᵛ∙⇔ .proj₁
>>>>>>> master

opaque

  -- An escape lemma for _⊩ᵛ_≡_.

  escape-⊩ᵛ≡ : Γ ⊩ᵛ A ≡ B → Γ ⊢ A ≅ B
  escape-⊩ᵛ≡ = escape-⊩≡ ∘→ proj₂ ∘→ ⊩ᵛ≡→⊩≡

opaque

  -- An escape lemma for _⊩ᵛ_∷_.

  escape-⊩ᵛ∷ : Γ ⊩ᵛ t ∷ A → Γ ⊢ t ∷ A
  escape-⊩ᵛ∷ = escape-⊩∷ ∘→ proj₂ ∘→ ⊩ᵛ∷→⊩∷

opaque

  -- An escape lemma for _⊩ᵛ_≡_∷_.

  escape-⊩ᵛ≡∷ : Γ ⊩ᵛ t ≡ u ∷ A → Γ ⊢ t ≅ u ∷ A
  escape-⊩ᵛ≡∷ = escape-⊩≡∷ ∘→ proj₂ ∘→ ⊩ᵛ≡∷→⊩≡∷

opaque

  -- An escape lemma for _⊩ˢ_∷_.

  escape-⊩ˢ∷ : Δ ⊩ˢ σ ∷ Γ → ⊢ Δ × Δ ⊢ˢ σ ∷ Γ
  escape-⊩ˢ∷ {Δ} {σ} {Γ = ε} =
    Δ ⊩ˢ σ ∷ ε        ⇔⟨ ⊩ˢ∷ε⇔ ⟩→
    ⊢ Δ               →⟨ _, id ⟩
    ⊢ Δ × Δ ⊢ˢ σ ∷ ε  □
  escape-⊩ˢ∷ {Δ} {σ} {Γ = Γ ∙ A} =
    Δ ⊩ˢ σ ∷ Γ ∙ A                                              ⇔⟨ ⊩ˢ∷∙⇔ ⟩→

    (∃ λ l → (Γ ⊩ᵛ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
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
     (Γ ⊩ᵛ A) × Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                      →⟨ (λ ((_ , _ , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                          ≅ₜ-eq (escape-⊩≡∷ σ₁₀≡σ₂₀) , escape-⊩ˢ≡∷ σ₁₊≡σ₂₊) ⟩
    Δ ⊢ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ] ×
    ⊢ Δ × Δ ⊢ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                →⟨ (λ (σ₁₀≡σ₂₀ , ⊢Δ , σ₁₊≡σ₂₊) → ⊢Δ , (σ₁₊≡σ₂₊ , σ₁₀≡σ₂₀)) ⟩

    ⊢ Δ × Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A                                      □

------------------------------------------------------------------------
-- Embedding

opaque

  -- Embedding for _⊩ᵛ_.

  emb-⊩ᵛ :
    l ≤ᵘ l′ →
    Γ ⊩ᵛ A →
    Γ ⊩ᵛ A
  emb-⊩ᵛ l≤l′ ⊩A = ⊩A

opaque

  -- Embedding for _⊩ᵛ_≡_.

  emb-⊩ᵛ≡ :
    l ≤ᵘ l′ →
    Γ ⊩ᵛ t ≡ u →
    Γ ⊩ᵛ t ≡ u
  emb-⊩ᵛ≡ l≤l′ t≡u = t≡u

opaque

  -- Embedding for _⊩ᵛ_∷_.

  emb-⊩ᵛ∷ :
    l ≤ᵘ l′ →
    Γ ⊩ᵛ t ∷ A →
    Γ ⊩ᵛ t ∷ A
  emb-⊩ᵛ∷ l≤l′ ⊩t = ⊩t

opaque

  -- Embedding for _⊩ᵛ_≡_∷_.

  emb-⊩ᵛ≡∷ :
    l ≤ᵘ l′ →
    Γ ⊩ᵛ t ≡ u ∷ A →
    Γ ⊩ᵛ t ≡ u ∷ A
  emb-⊩ᵛ≡∷ l≤l′ t≡u∷A = t≡u∷A

------------------------------------------------------------------------
-- Weakening

opaque

  -- A weakening lemma for _⊩ᵛ_≡_.

  wk-⊩ᵛ≡ :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ A ≡ B → Δ ⊩ᵛ wk ρ A ≡ wk ρ B
  wk-⊩ᵛ≡ {ρ} {A} {B} ρ⊇ ⊩Δ A≡B =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (⊩Γ , A≡B) →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩Δ
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ → _ , (
          wk ρ A [ σ₁ ]  ≡⟨ subst-wk A ⟩⊩≡
          A [ σ₁ ₛ• ρ ]  ≡⟨ A≡B (⊩ˢ≡∷-ₛ• ρ⊇ ⊩Γ σ₁≡σ₂) .proj₂ ⟩⊩∎≡
          B [ σ₂ ₛ• ρ ]  ≡˘⟨ subst-wk B ⟩
          wk ρ B [ σ₂ ]  ∎)
      )

opaque

  -- Single-step weakening for _⊩ᵛ_≡_.

  wk1-⊩ᵛ≡ : Γ ⊩ᵛ C → Γ ⊩ᵛ A ≡ B → Γ ∙ C ⊩ᵛ wk1 A ≡ wk1 B
  wk1-⊩ᵛ≡ ⊩C =
    wk-⊩ᵛ≡ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩C)

opaque

  -- A weakening lemma for _⊩ᵛ_.

  wk-⊩ᵛ : ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ A → Δ ⊩ᵛ wk ρ A
  wk-⊩ᵛ ρ⊇ ⊩Δ =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ ∘→ wk-⊩ᵛ≡ ρ⊇ ⊩Δ ∘→ ⊩ᵛ⇔⊩ᵛ≡ .proj₁

opaque

  -- Single-step weakening for _⊩ᵛ_.

  wk1-⊩ᵛ : Γ ⊩ᵛ B → Γ ⊩ᵛ A → Γ ∙ B ⊩ᵛ wk1 A
  wk1-⊩ᵛ ⊩B =
    wk-⊩ᵛ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩B)

opaque

  -- A weakening lemma for _⊩ᵛ_≡_∷_.

  wk-⊩ᵛ≡∷ :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ t ≡ u ∷ A →
    Δ ⊩ᵛ wk ρ t ≡ wk ρ u ∷ wk ρ A
  wk-⊩ᵛ≡∷ {ρ} {t} {u} {A} ρ⊇ ⊩Δ t≡u =
    case wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t≡u .proj₁ of λ
      ⊩A →
    ⊩ᵛ≡∷⇔ .proj₂
      ( wk-⊩ᵛ ρ⊇ ⊩Δ ⊩A
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ → _ , (
          wk ρ t [ σ₁ ] ∷ wk ρ A [ σ₁ ]  ≡⟨ subst-wk t ⟩⊩∷∷≡
                                          ⟨ subst-wk A ⟩⊩∷≡
<<<<<<< HEAD
          t [ σ₁ ₛ• ρ ] ∷ A [ σ₁ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂ (
                                            ⊩ˢ≡∷-ₛ• ρ⊇ (wf-⊩ᵛ ⊩A) σ₁≡σ₂) .proj₂ ⟩⊩∷∎∷≡
=======
          t [ σ₁ ₛ• ρ ] ∷ A [ σ₁ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u $
                                            ⊩ˢ≡∷-ₛ• ρ⊇ (wf-⊩ᵛ ⊩A) σ₁≡σ₂ ⟩⊩∷∎∷≡
>>>>>>> master
          u [ σ₂ ₛ• ρ ]                  ≡˘⟨ subst-wk u ⟩
          wk ρ u [ σ₂ ]                  ∎)
      )

opaque

  -- Single-step weakening for _⊩ᵛ_≡_∷_.

  wk1-⊩ᵛ≡∷ :
    Γ ⊩ᵛ B → Γ ⊩ᵛ t ≡ u ∷ A →
    Γ ∙ B ⊩ᵛ wk1 t ≡ wk1 u ∷ wk1 A
  wk1-⊩ᵛ≡∷ ⊩B =
    wk-⊩ᵛ≡∷ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩B)

opaque

  -- A weakening lemma for _⊩ᵛ_∷_.

  wk-⊩ᵛ∷ :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ t ∷ A → Δ ⊩ᵛ wk ρ t ∷ wk ρ A
  wk-⊩ᵛ∷ ρ⊇ ⊩Δ =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ wk-⊩ᵛ≡∷ ρ⊇ ⊩Δ ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

opaque

  -- Single-step weakening for _⊩ᵛ_∷_.

  wk1-⊩ᵛ∷ : Γ ⊩ᵛ B → Γ ⊩ᵛ t ∷ A → Γ ∙ B ⊩ᵛ wk1 t ∷ wk1 A
  wk1-⊩ᵛ∷ ⊩B =
    wk-⊩ᵛ∷ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩B)

------------------------------------------------------------------------
-- Substitution lemmas

opaque

  -- A substitution lemma for _⊩ᵛ_≡_.

  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ :
    Γ ∙ A ⊩ᵛ B ≡ C →
    Γ ⊩ᵛ t ≡ u ∷ A →
    Γ ⊩ᵛ B [ t ]₀ ≡ C [ u ]₀
  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ {B} {C} B≡C t≡u =
    case ⊩ᵛ≡∷⇔ .proj₁ t≡u of λ
      (⊩A , t≡u) →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ ⊩A
      , λ σ₁≡σ₂ →
          _ , (
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (substConsId B) (substConsId C) $
<<<<<<< HEAD
          proj₂ $
          ⊩ᵛ≡⇔ .proj₁ B≡C .proj₂ $
          ⊩ˢ≡∷∙⇔ .proj₂ ((_ , ⊩A , t≡u σ₁≡σ₂ .proj₂) , σ₁≡σ₂))
=======
          ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B≡C $
          ⊩ˢ≡∷∙⇔ .proj₂ ((_ , ⊩A , t≡u σ₁≡σ₂) , σ₁≡σ₂)
>>>>>>> master
      )

opaque

  -- A substitution lemma for _⊩ᵛ_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ :
    Γ ∙ A ⊩ᵛ B →
    Γ ⊩ᵛ t ∷ A →
    Γ ⊩ᵛ B [ t ]₀
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B ⊩t =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $ ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩ᵛ≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ :
    Γ ∙ A ⊩ᵛ t ∷ B →
    Γ ⊩ᵛ u ∷ A →
    Γ ⊩ᵛ t [ u ]₀ ∷ B [ u ]₀
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ {t} {B} ⊩t ⊩u =
    case ⊩ᵛ∷⇔ .proj₁ ⊩t of λ
      (⊩B , t≡t) →
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B ⊩u
      , λ σ₁≡σ₂ →
          _ , (
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
            (substConsId t) (substConsId t) (substConsId B) $
          proj₂ $
          t≡t $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ ⊩B
            , (_ , ⊩ᵛ∷⇔ .proj₁ ⊩u .proj₂ σ₁≡σ₂ .proj₂)
            , σ₁≡σ₂
            ))
      )

opaque

  -- A substitution lemma for _⊩ᵛ_≡_.

  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ C₁ ≡ C₂ →
    Γ ⊩ᵛ t₁ ≡ t₂ ∷ A →
    Γ ⊩ᵛ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊩ᵛ C₁ [ t₁ , u₁ ]₁₀ ≡ C₂ [ t₂ , u₂ ]₁₀
  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ {B} {C₁} {C₂} C₁≡C₂ t₁≡t₂ u₁≡u₂ =
    case ⊩ᵛ≡⇔ .proj₁ C₁≡C₂ of λ
      (⊩Γ∙A∙B , C₁≡C₂) →
    case wf-⊩ᵛ-∙ ⊩Γ∙A∙B of λ
      ⊩B →
    case wf-∙-⊩ᵛ ⊩B of λ
      ⊩A →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ ⊩A
      , λ σ₁≡σ₂ → _ , (
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
            (PE.sym $ [,]-[]-fusion C₁) (PE.sym $ [,]-[]-fusion C₂) $
          proj₂ $
          C₁≡C₂ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( ⊩B
            , ( _
              , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ substConsId B)
<<<<<<< HEAD
                  (⊩ᵛ≡∷⇔ .proj₁ u₁≡u₂ .proj₂ σ₁≡σ₂ .proj₂)
              )
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( ⊩A
                , (_ , ⊩ᵛ≡∷⇔ .proj₁ t₁≡t₂ .proj₂ σ₁≡σ₂ .proj₂)
=======
                  (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( (_ , ⊩A)
                , (_ , ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂)
>>>>>>> master
                , σ₁≡σ₂
                )
            ))
      )

opaque

  -- A substitution lemma for _⊩ᵛ_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ C →
    Γ ⊩ᵛ t ∷ A →
    Γ ⊩ᵛ u ∷ B [ t ]₀ →
    Γ ⊩ᵛ C [ t , u ]₁₀
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ ⊩C ⊩t ⊩u =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $
    ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀
      (refl-⊩ᵛ≡ ⊩C) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_∷_.

  ⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ t₁ ≡ t₂ ∷ C →
    Γ ⊩ᵛ u₁ ≡ u₂ ∷ A →
    Γ ⊩ᵛ v₁ ≡ v₂ ∷ B [ u₁ ]₀ →
    Γ ⊩ᵛ t₁ [ u₁ , v₁ ]₁₀ ≡ t₂ [ u₂ , v₂ ]₁₀ ∷ C [ u₁ , v₁ ]₁₀
  ⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀∷ {B} {t₁} {t₂} {C} t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    case wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁ of λ
      ⊩C →
    case wf-∙-⊩ᵛ ⊩C of λ
      ⊩B →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀
          ⊩C (wf-⊩ᵛ≡∷ u₁≡u₂ .proj₁) (wf-⊩ᵛ≡∷ v₁≡v₂ .proj₁)
      , λ σ₁≡σ₂ → _ , (
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ [,]-[]-fusion t₁)
            (PE.sym $ [,]-[]-fusion t₂) (PE.sym $ [,]-[]-fusion C) $
<<<<<<< HEAD
          proj₂ $
          ⊩ᵛ≡∷⇔ .proj₁ t₁≡t₂ .proj₂ $
=======
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ $
>>>>>>> master
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( ⊩B
            , ( _
              , (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                   (PE.sym $ substConsId B) $
<<<<<<< HEAD
                 ⊩ᵛ≡∷⇔ .proj₁ v₁≡v₂ .proj₂ σ₁≡σ₂ .proj₂)
              )
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( wf-∙-⊩ᵛ ⊩B
                , (_ , ⊩ᵛ≡∷⇔ .proj₁ u₁≡u₂ .proj₂ σ₁≡σ₂ .proj₂)
=======
                 ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ v₁≡v₂ σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( wf-∙-⊩ᵛ ⊩B
                , (_ , ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂)
>>>>>>> master
                , σ₁≡σ₂
                )
            ))

      )

opaque

  -- A substitution lemma for _⊩ᵛ_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ t ∷ C →
    Γ ⊩ᵛ u ∷ A →
    Γ ⊩ᵛ v ∷ B [ u ]₀ →
    Γ ⊩ᵛ t [ u , v ]₁₀ ∷ C [ u , v ]₁₀
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ ⊩t ⊩u ⊩v =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀∷
      (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u) (refl-⊩ᵛ≡∷ ⊩v)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_.

  ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² :
    Γ ∙ A ⊩ᵛ D ≡ E →
    Γ ∙ B ∙ C ⊩ᵛ t ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ D [ t ]↑² ≡ E [ t ]↑²
  ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² {A} {D} {E} D≡E ⊩t =
    case ⊩ᵛ≡⇔ .proj₁ D≡E of λ
      (⊩Γ∙A , D≡E) →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
      , λ σ₁≡σ₂ → _ , (
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (substComp↑² D _) (substComp↑² E _) $
          proj₂ $
          D≡E $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( wf-⊩ᵛ-∙ ⊩Γ∙A
            , ( _
              , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk2-tail A)
                  (⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂ .proj₂)
              )
            , ⊩ˢ≡∷∙⇔ .proj₁ (⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ .proj₂) .proj₂
            ))
      )

opaque

  -- A substitution lemma for _⊩ᵛ_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² :
    Γ ∙ A ⊩ᵛ D →
    Γ ∙ B ∙ C ⊩ᵛ t ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ D [ t ]↑²
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² ⊩D ⊩t =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $ ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² (refl-⊩ᵛ≡ ⊩D) ⊩t

opaque

  -- A substitution lemma for _⊩ᵛ_≡_∷_.

  ⊩ᵛ≡∷→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²∷ :
    Γ ∙ A ⊩ᵛ t ≡ u ∷ D →
    Γ ∙ B ∙ C ⊩ᵛ v ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ t [ v ]↑² ≡ u [ v ]↑² ∷ D [ v ]↑²
  ⊩ᵛ≡∷→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²∷ {A} {t} {u} {D} t≡u ⊩v =
    case wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u .proj₁) of λ
      ⊩D →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² ⊩D ⊩v
      , λ σ₁≡σ₂ → _ , (
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (substComp↑² t _) (substComp↑² u _)
            (substComp↑² D _) $
<<<<<<< HEAD
          proj₂ $
          ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂ $
=======
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u $
>>>>>>> master
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ ⊩D
            , ( _
              , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk2-tail A)
                  (⊩ᵛ∷⇔ .proj₁ ⊩v .proj₂ σ₁≡σ₂ .proj₂)
              )
            , ⊩ˢ≡∷∙⇔ .proj₁ (⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ .proj₂) .proj₂
            ))
      )

opaque

  -- A substitution lemma for _⊩ᵛ_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ :
    Γ ∙ A ⊩ᵛ t ∷ D →
    Γ ∙ B ∙ C ⊩ᵛ u ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ t [ u ]↑² ∷ D [ u ]↑²
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $ ⊩ᵛ≡∷→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²∷ (refl-⊩ᵛ≡∷ ⊩t) ⊩u

opaque

  -- A substitution lemma for _⊩ᵛ_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ :
    Γ ∙ A ⊩ᵛ B ≡ C →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    ∃ λ l → Γ ⊩⟨ l ⟩ B [ t ]₀ ≡ C [ u ]₀
  ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ B≡C t≡u =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B≡C .proj₁) of λ
<<<<<<< HEAD
      ⊩A →
    ⊩ᵛ≡⇔ .proj₁ B≡C .proj₂ $
    ⊩ˢ≡∷-sgSubst ⊩A (level-⊩≡∷ (⊩ᵛ→⊩ ⊩A .proj₂) t≡u)
=======
      (_ , ⊩A) →
    ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B≡C $
    ⊩ˢ≡∷-sgSubst ⊩A (level-⊩≡∷ (⊩ᵛ→⊩ ⊩A) t≡u)
>>>>>>> master

opaque

  -- A substitution lemma for _⊩ᵛ_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩[]₀ :
    Γ ∙ A ⊩ᵛ B →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    ∃ λ l → Γ ⊩⟨ l ⟩ B [ t ]₀
  ⊩ᵛ→⊩∷→⊩[]₀ ⊩B ⊩t =
    Σ.map idᶠ (⊩⇔⊩≡ .proj₂) $ ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ :
    Γ ∙ A ⊩ᵛ t ≡ u ∷ B →
    Γ ⊩⟨ l′ ⟩ v ≡ w ∷ A →
    ∃ λ l → Γ ⊩⟨ l ⟩ t [ v ]₀ ≡ u [ w ]₀ ∷ B [ v ]₀
  ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ t≡u v≡w =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u .proj₁)) of λ
<<<<<<< HEAD
      ⊩A →
    ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂ $
    ⊩ˢ≡∷-sgSubst ⊩A (level-⊩≡∷ (⊩ᵛ→⊩ ⊩A .proj₂) v≡w)
=======
      (_ , ⊩A) →
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u $
    ⊩ˢ≡∷-sgSubst ⊩A (level-⊩≡∷ (⊩ᵛ→⊩ ⊩A) v≡w)
>>>>>>> master

opaque

  -- A substitution lemma for _⊩ᵛ_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩[]₀∷ :
    Γ ∙ A ⊩ᵛ t ∷ B →
    Γ ⊩⟨ l′ ⟩ u ∷ A →
    ∃ λ l → Γ ⊩⟨ l ⟩ t [ u ]₀ ∷ B [ u ]₀
  ⊩ᵛ∷→⊩∷→⊩[]₀∷ ⊩t ⊩u =
    Σ.map idᶠ (⊩∷⇔⊩≡∷ .proj₂) $ ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] :
    Γ ∙ A ⊩ᵛ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    ∃ λ l → Δ ⊩⟨ l ⟩ B₁ [ consSubst σ₁ t₁ ] ≡ B₂ [ consSubst σ₂ t₂ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] B₁≡B₂ σ₁≡σ₂ t₁≡t₂ =
    ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
    ⊩ˢ≡∷∙⇔′ .proj₂ (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁) , (_ , t₁≡t₂) , σ₁≡σ₂)

opaque

  -- A substitution lemma for _⊩ᵛ_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[,] :
    Γ ∙ A ⊩ᵛ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    ∃ λ l → Δ ⊩⟨ l ⟩ B [ consSubst σ t ]
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[,] ⊩B ⊩σ ⊩t =
    Σ.map idᶠ (⊩⇔⊩≡ .proj₂) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ) (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ :
    Γ ∙ A ⊩ᵛ t₁ ≡ t₂ ∷ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    ∃ λ l → Δ ⊩⟨ l ⟩ t₁ [ consSubst σ₁ u₁ ] ≡ t₂ [ consSubst σ₂ u₂ ] ∷
      B [ consSubst σ₁ u₁ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ t₁≡t₂ σ₁≡σ₂ u₁≡u₂ =
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ $
    ⊩ˢ≡∷∙⇔′ .proj₂
      (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁) , (_ , u₁≡u₂) , σ₁≡σ₂)

opaque

  -- A substitution lemma for _⊩ᵛ_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[,]∷ :
    Γ ∙ A ⊩ᵛ t ∷ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    ∃ λ l → Δ ⊩⟨ l ⟩ t [ consSubst σ u ] ∷ B [ consSubst σ u ]
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[,]∷ ⊩t ⊩σ ⊩u =
    Σ.map idᶠ (⊩∷⇔⊩≡∷ .proj₂) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] :
    Γ ∙ A ⊩ᵛ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    ∃ λ l → Δ ∙ A [ σ₁ ] ⊩⟨ l ⟩ B₁ [ σ₁ ⇑ ] ≡ B₂ [ σ₂ ⇑ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] B₁≡B₂ σ₁≡σ₂ =
<<<<<<< HEAD
    ⊩ᵛ≡⇔ .proj₁ B₁≡B₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁)) σ₁≡σ₂
=======
    ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
    ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁) .proj₂) σ₁≡σ₂
>>>>>>> master

opaque

  -- A substitution lemma for _⊩ᵛ_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩[⇑] :
    Γ ∙ A ⊩ᵛ B →
    Δ ⊩ˢ σ ∷ Γ →
    ∃ λ l → Δ ∙ A [ σ ] ⊩⟨ l ⟩ B [ σ ⇑ ]
  ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ =
    Σ.map idᶠ (⊩⇔⊩≡ .proj₂) $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ :
    Γ ∙ A ⊩ᵛ t₁ ≡ t₂ ∷ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    ∃ λ l → Δ ∙ A [ σ₁ ] ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ] ≡ t₂ [ σ₂ ⇑ ] ∷ B [ σ₁ ⇑ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ t₁≡t₂ σ₁≡σ₂ =
<<<<<<< HEAD
    ⊩ᵛ≡∷⇔ .proj₁ t₁≡t₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)))
=======
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ $
    ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) .proj₂)
>>>>>>> master
      σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ :
    Γ ∙ A ⊩ᵛ t ∷ B →
    Δ ⊩ˢ σ ∷ Γ →
    ∃ λ l → Δ ∙ A [ σ ] ⊩⟨ l ⟩ t [ σ ⇑ ] ∷ B [ σ ⇑ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ ⊩t ⊩σ =
    Σ.map idᶠ (⊩∷⇔⊩≡∷ .proj₂) $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] :
    Γ ∙ A ∙ B ⊩ᵛ C₁ ≡ C₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    ∃ λ l → Δ ∙ A [ σ₁ ] ∙ B [ σ₁ ⇑ ] ⊩⟨ l ⟩ C₁ [ σ₁ ⇑ ⇑ ] ≡ C₂ [ σ₂ ⇑ ⇑ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] C₁≡C₂ σ₁≡σ₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ≡ C₁≡C₂ .proj₁) of λ
<<<<<<< HEAD
      ⊩B →
    ⊩ᵛ≡⇔ .proj₁ C₁≡C₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst ⊩B $ ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ ⊩B) σ₁≡σ₂
=======
      (_ , ⊩B) →
    ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] C₁≡C₂ $
    ⊩ˢ≡∷-liftSubst ⊩B $ ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ ⊩B .proj₂) σ₁≡σ₂
>>>>>>> master

opaque

  -- A substitution lemma for _⊩ᵛ_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] :
    Γ ∙ A ∙ B ⊩ᵛ C →
    Δ ⊩ˢ σ ∷ Γ →
    ∃ λ l → Δ ∙ A [ σ ] ∙ B [ σ ⇑ ] ⊩⟨ l ⟩ C [ σ ⇑ ⇑ ]
  ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] ⊩C ⊩σ =
    Σ.map idᶠ (⊩⇔⊩≡ .proj₂) $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] (refl-⊩ᵛ≡ ⊩C) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ :
    Γ ∙ A ∙ B ⊩ᵛ t₁ ≡ t₂ ∷ C →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    ∃ λ l → Δ ∙ A [ σ₁ ] ∙ B [ σ₁ ⇑ ] ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ⇑ ] ≡ t₂ [ σ₂ ⇑ ⇑ ] ∷
      C [ σ₁ ⇑ ⇑ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ t₁≡t₂ σ₁≡σ₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) of λ
<<<<<<< HEAD
      ⊩B →
    ⊩ᵛ≡∷⇔ .proj₁ t₁≡t₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst ⊩B $ ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ ⊩B) σ₁≡σ₂
=======
      (_ , ⊩B) →
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ $
    ⊩ˢ≡∷-liftSubst ⊩B $ ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ ⊩B .proj₂) σ₁≡σ₂
>>>>>>> master

opaque

  -- A substitution lemma for _⊩ᵛ_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ :
    Γ ∙ A ∙ B ⊩ᵛ t ∷ C →
    Δ ⊩ˢ σ ∷ Γ →
    ∃ λ l → Δ ∙ A [ σ ] ∙ B [ σ ⇑ ] ⊩⟨ l ⟩ t [ σ ⇑ ⇑ ] ∷ C [ σ ⇑ ⇑ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ ⊩t ⊩σ =
    Σ.map idᶠ (⊩∷⇔⊩≡∷ .proj₂) $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ :
    Γ ∙ A ⊩ᵛ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    ∃ λ l → Δ ⊩⟨ l ⟩ B₁ [ σ₁ ⇑ ] [ t₁ ]₀ ≡ B₂ [ σ₂ ⇑ ] [ t₂ ]₀
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ {B₁} {B₂} B₁≡B₂ σ₁≡σ₂ t₁≡t₂ =
    Σ.map idᶠ (PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ singleSubstComp _ _ B₁)
      (PE.sym $ singleSubstComp _ _ B₂)) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] B₁≡B₂ σ₁≡σ₂ t₁≡t₂

opaque

  -- A substitution lemma for _⊩ᵛ_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ :
    Γ ∙ A ⊩ᵛ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    ∃ λ l → Δ ⊩⟨ l ⟩ B [ σ ⇑ ] [ t ]₀
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ ⊩B ⊩σ ⊩t =
    Σ.map idᶠ (⊩⇔⊩≡ .proj₂) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ :
    Γ ∙ A ⊩ᵛ t₁ ≡ t₂ ∷ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    ∃ λ l → Δ ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ] [ u₁ ]₀ ≡ t₂ [ σ₂ ⇑ ] [ u₂ ]₀ ∷
      B [ σ₁ ⇑ ] [ u₁ ]₀
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ {t₁} {t₂} {B} t₁≡t₂ σ₁≡σ₂ u₁≡u₂ =
    Σ.map idᶠ (PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
      (PE.sym $ singleSubstComp _ _ t₁)
      (PE.sym $ singleSubstComp _ _ t₂)
      (PE.sym $ singleSubstComp _ _ B)) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ t₁≡t₂ σ₁≡σ₂ u₁≡u₂

opaque

  -- A substitution lemma for _⊩ᵛ_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[⇑][]₀∷ :
    Γ ∙ A ⊩ᵛ t ∷ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    ∃ λ l → Δ ⊩⟨ l ⟩ t [ σ ⇑ ] [ u ]₀ ∷ B [ σ ⇑ ] [ u ]₀
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[⇑][]₀∷ ⊩t ⊩σ ⊩u =
    Σ.map idᶠ (⊩∷⇔⊩≡∷ .proj₂) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] :
    Γ ∙ A ⊩ᵛ B₁ ≡ B₂ →
    Δ ⊩⟨ l′ ⟩ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ B₁ [ t₁ ]₀ [ σ₁ ] ≡ B₂ [ t₂ ]₀ [ σ₂ ]
  ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] {B₁} {B₂} B₁≡B₂ t₁[σ₁]≡t₂[σ₂] σ₁≡σ₂ =
    Σ.map idᶠ (PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ singleSubstLift B₁ _)
      (PE.sym $ singleSubstLift B₂ _)) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ B₁≡B₂ σ₁≡σ₂ t₁[σ₁]≡t₂[σ₂]

opaque

  -- A substitution lemma for _⊩ᵛ_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩ˢ∷→⊩[]₀[] :
    Γ ∙ A ⊩ᵛ B →
    Δ ⊩⟨ l′ ⟩ t [ σ ] ∷ A [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ B [ t ]₀ [ σ ]
  ⊩ᵛ→⊩∷→⊩ˢ∷→⊩[]₀[] {t} ⊩B ⊩t[σ] ⊩σ =
    Σ.map idᶠ (⊩⇔⊩≡ .proj₂) $
    ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] {t₂ = t} (refl-⊩ᵛ≡ ⊩B) (refl-⊩≡∷ ⊩t[σ])
      (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ :
    Γ ∙ A ⊩ᵛ t₁ ≡ t₂ ∷ B →
    Δ ⊩⟨ l′ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ t₁ [ u₁ ]₀ [ σ₁ ] ≡ t₂ [ u₂ ]₀ [ σ₂ ] ∷ B [ u₁ ]₀ [ σ₁ ]
  ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ {t₁} {t₂} {B} t₁≡t₂ σ₁≡σ₂ u₁[σ₁]≡u₂[σ₂] =
    Σ.map idᶠ (PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ singleSubstLift t₁ _)
      (PE.sym $ singleSubstLift t₂ _) (PE.sym $ singleSubstLift B _)) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ t₁≡t₂ u₁[σ₁]≡u₂[σ₂] σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩ˢ∷→⊩[]₀[]∷ :
    Γ ∙ A ⊩ᵛ t ∷ B →
    Δ ⊩⟨ l′ ⟩ u [ σ ] ∷ A [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ t [ u ]₀ [ σ ] ∷ B [ u ]₀ [ σ ]
  ⊩ᵛ∷→⊩∷→⊩ˢ∷→⊩[]₀[]∷ {u} ⊩t ⊩u[σ] ⊩σ =
    Σ.map idᶠ (⊩∷⇔⊩≡∷ .proj₂) $
    ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ {u₂ = u} (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩≡∷ ⊩u[σ])
      (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ C₁ ≡ C₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ u₁ ≡ u₂ ∷ B [ σ₁ ⇑ ] [ t₁ ]₀ →
    ∃ λ l → Δ ⊩⟨ l ⟩ C₁ [ σ₁ ⇑ ⇑ ] [ t₁ , u₁ ]₁₀ ≡ C₂ [ σ₂ ⇑ ⇑ ] [ t₂ , u₂ ]₁₀
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀
    {B} {C₁} {C₂} C₁≡C₂ σ₁≡σ₂ t₁≡t₂ u₁≡u₂ =
    Σ.map idᶠ (PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ doubleSubstComp C₁ _ _ _)
      (PE.sym $ doubleSubstComp C₂ _ _ _)) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] C₁≡C₂
      (⊩ˢ≡∷∙⇔′ .proj₂
         ( wf-∙-⊩ᵛ (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ C₁≡C₂ .proj₁))
         , (_ , t₁≡t₂)
         , σ₁≡σ₂
         )) $
    PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstComp _ _ B) u₁≡u₂

opaque

  -- A substitution lemma for _⊩ᵛ_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑⇑][]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ C →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ u ∷ B [ σ ⇑ ] [ t ]₀ →
    ∃ λ l → Δ ⊩⟨ l ⟩ C [ σ ⇑ ⇑ ] [ t , u ]₁₀
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑⇑][]₁₀ ⊩C ⊩σ ⊩t ⊩u =
    Σ.map idᶠ (⊩⇔⊩≡ .proj₂) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩C) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩t) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ t₁ ≡ t₂ ∷ C →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ v₁ ≡ v₂ ∷ B [ σ₁ ⇑ ] [ u₁ ]₀ →
    ∃ λ l → Δ ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ⇑ ] [ u₁ , v₁ ]₁₀ ≡ t₂ [ σ₂ ⇑ ⇑ ] [ u₂ , v₂ ]₁₀ ∷
      C [ σ₁ ⇑ ⇑ ] [ u₁ , v₁ ]₁₀
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷
    {B} {t₁} {t₂} {C} t₁≡t₂ σ₁≡σ₂ u₁≡u₂ v₁≡v₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) of λ
      ⊩B →
    Σ.map idᶠ (PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
      (PE.sym $ doubleSubstComp t₁ _ _ _)
      (PE.sym $ doubleSubstComp t₂ _ _ _)
<<<<<<< HEAD
      (PE.sym $ doubleSubstComp C _ _ _)) $
    ⊩ᵛ≡∷⇔ .proj₁ t₁≡t₂ .proj₂ $
=======
      (PE.sym $ doubleSubstComp C _ _ _) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ $
>>>>>>> master
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( ⊩B
      , ( _
        , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstComp _ _ B) v₁≡v₂
        )
      , ⊩ˢ≡∷∙⇔′ .proj₂ (wf-∙-⊩ᵛ ⊩B , (_ , u₁≡u₂) , σ₁≡σ₂)
      )

opaque

  -- A substitution lemma for _⊩ᵛ_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩∷→⊩[⇑⇑][]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ t ∷ C →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ v ∷ B [ σ ⇑ ] [ u ]₀ →
    ∃ λ l → Δ ⊩⟨ l ⟩ t [ σ ⇑ ⇑ ] [ u , v ]₁₀ ∷ C [ σ ⇑ ⇑ ] [ u , v ]₁₀
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩∷→⊩[⇑⇑][]₁₀∷ ⊩t ⊩σ ⊩u ⊩v =
    Σ.map idᶠ (⊩∷⇔⊩≡∷ .proj₂) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩u) (refl-⊩≡∷ ⊩v)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[] :
    Γ ∙ A ∙ B ⊩ᵛ C₁ ≡ C₂ →
    Δ ⊩⟨ l′ ⟩ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ B [ t₁ ]₀ [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ C₁ [ t₁ , u₁ ]₁₀ [ σ₁ ] ≡ C₂ [ t₂ , u₂ ]₁₀ [ σ₂ ]
  ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]
    {B} {C₁} {C₂} C₁≡C₂ t₁[σ₁]≡t₂[σ₂] u₁[σ₁]≡u₂[σ₂] σ₁≡σ₂ =
    Σ.map idᶠ (PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ [,]-[]-commute C₁)
      (PE.sym $ [,]-[]-commute C₂)) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ C₁≡C₂ σ₁≡σ₂ t₁[σ₁]≡t₂[σ₂]
      (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B _)
         u₁[σ₁]≡u₂[σ₂])

opaque

  -- A substitution lemma for _⊩ᵛ_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[] :
    Γ ∙ A ∙ B ⊩ᵛ C →
    Δ ⊩⟨ l′ ⟩ t [ σ ] ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ u [ σ ] ∷ B [ t ]₀ [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ C [ t , u ]₁₀ [ σ ]
  ⊩ᵛ→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[] {t} {u} ⊩C ⊩t[σ] ⊩u[σ] ⊩σ =
    Σ.map idᶠ (⊩⇔⊩≡ .proj₂) $
    ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[] {t₂ = t} {u₂ = u} (refl-⊩ᵛ≡ ⊩C)
      (refl-⊩≡∷ ⊩t[σ]) (refl-⊩≡∷ ⊩u[σ]) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷ :
    Γ ∙ A ∙ B ⊩ᵛ t₁ ≡ t₂ ∷ C →
    Δ ⊩⟨ l′ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ v₁ [ σ₁ ] ≡ v₂ [ σ₂ ] ∷ B [ u₁ ]₀ [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ t₁ [ u₁ , v₁ ]₁₀ [ σ₁ ] ≡ t₂ [ u₂ , v₂ ]₁₀ [ σ₂ ] ∷
      C [ u₁ , v₁ ]₁₀ [ σ₁ ]
  ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷
    {B} {t₁} {t₂} {C} t₁≡t₂ u₁[σ₁]≡u₂[σ₂] v₁[σ₁]≡v₂[σ₂] σ₁≡σ₂ =
    Σ.map idᶠ (PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ [,]-[]-commute t₁)
      (PE.sym $ [,]-[]-commute t₂) (PE.sym $ [,]-[]-commute C)) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ t₁≡t₂ σ₁≡σ₂ u₁[σ₁]≡u₂[σ₂]
      (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B _)
         v₁[σ₁]≡v₂[σ₂])

opaque

  -- A substitution lemma for _⊩ᵛ_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[]∷ :
    Γ ∙ A ∙ B ⊩ᵛ t ∷ C →
    Δ ⊩⟨ l′ ⟩ u [ σ ] ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ v [ σ ] ∷ B [ u ]₀ [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    ∃ λ l → Δ ⊩⟨ l ⟩ t [ u , v ]₁₀ [ σ ] ∷ C [ u , v ]₁₀ [ σ ]
  ⊩ᵛ∷→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[]∷ {u} {v} ⊩t ⊩u[σ] ⊩v[σ] ⊩σ =
    Σ.map idᶠ (⊩∷⇔⊩≡∷ .proj₂) $
    ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷ {u₂ = u} {v₂ = v} (refl-⊩ᵛ≡∷ ⊩t)
      (refl-⊩≡∷ ⊩u[σ]) (refl-⊩≡∷ ⊩v[σ]) (refl-⊩ˢ≡∷ ⊩σ)
