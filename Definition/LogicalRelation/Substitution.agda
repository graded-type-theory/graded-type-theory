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

import Definition.LogicalRelation.Hidden R as H
open import Definition.LogicalRelation.Hidden.Restricted R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R as TW using (_∷_⊇_; _»_∷ʷ_⊇_)
open import Definition.Typed.Weakening.Definition R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  m n κ                                                 : Nat
  ∇ ∇′ ∇″                                               : DCon (Term 0) _
  Δ Η Φ                                                 : Con Term _
  Γ                                                     : Cons _ _
  A A₁ A₂ B B₁ B₂ C C₁ C₂ D E t t₁ t₂ u u₁ u₂ v v₁ v₂ w : Term _
  σ σ₁ σ₂ σ₃                                            : Subst _ _
  ξ                                                     : DExt (Term 0) _ _
  ρ                                                     : Wk _ _
  l l′ l″ l‴                                            : Universe-level

------------------------------------------------------------------------
-- The type formers

opaque mutual

  -- Valid contexts.

  infix 4 _»⊩ᵛ_

  _»⊩ᵛ_ : DCon (Term 0) κ → Con Term n → Set a
  ∇ »⊩ᵛ ε       = » ∇
  ∇ »⊩ᵛ (Γ ∙ A) = ∃ λ l → ∇ » Γ ⊩ᵛ⟨ l ⟩ A

  -- Valid types.

  infix 4 _⊩ᵛ⟨_⟩_

  _⊩ᵛ⟨_⟩_ : Cons κ n → Universe-level → Term n → Set a
  Γ ⊩ᵛ⟨ l ⟩ A = Γ ⊩ᵛ⟨ l ⟩ A ≡ A

  -- Valid type equality.

  infix 4 _⊩ᵛ⟨_⟩_≡_

  _⊩ᵛ⟨_⟩_≡_ : Cons κ n → Universe-level → Term n → Term n → Set a
  _⊩ᵛ⟨_⟩_≡_ {κ} {n} (∇ » Γ) l A B =
    ∇ »⊩ᵛ Γ ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Δ} {σ₁ σ₂ : Subst m n} → ∇′ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     ∇′ » Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ])

  -- Valid substitution equality.

  infix 4 _⊩ˢ_≡_∷_

  _⊩ˢ_≡_∷_ : Cons κ m → Subst m n → Subst m n → Con Term n → Set a
  ∇ » Δ ⊩ˢ _ ≡ _ ∷ ε =
    » ∇ × (⦃ inc : Var-included or-empty Δ ⦄ → ∇ »⊢ Δ)
  ∇ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A =
    (∃ λ l →
     (∇ » Γ ⊩ᵛ⟨ l ⟩ A) ×
     ∇ » Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    ∇ » Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ

-- Valid context pairs.

infix 4 ⊩ᵛ_

⊩ᵛ_ : Cons m n → Set a
⊩ᵛ (∇ » Γ) = ∇ »⊩ᵛ Γ

opaque

  -- Valid substitutions.

  infix 4 _⊩ˢ_∷_

  _⊩ˢ_∷_ : Cons κ m → Subst m n → Con Term n → Set a
  Δ ⊩ˢ σ ∷ Γ = Δ ⊩ˢ σ ≡ σ ∷ Γ

opaque

  -- Valid term equality.

  infix 4 _⊩ᵛ⟨_⟩_≡_∷_

  _⊩ᵛ⟨_⟩_≡_∷_ :
    Cons κ n → Universe-level → Term n → Term n → Term n → Set a
  _⊩ᵛ⟨_⟩_≡_∷_ {κ} {n} (∇ » Γ) l t u A =
    ∇ » Γ ⊩ᵛ⟨ l ⟩ A ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Δ} {σ₁ σ₂ : Subst m n} → ∇′ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     ∇′ » Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ])

opaque

  -- Valid terms.

  infix 4 _⊩ᵛ⟨_⟩_∷_

  _⊩ᵛ⟨_⟩_∷_ : Cons κ n → Universe-level → Term n → Term n → Set a
  Γ ⊩ᵛ⟨ l ⟩ t ∷ A = Γ ⊩ᵛ⟨ l ⟩ t ≡ t ∷ A

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _»⊩ᵛ_

  -- A characterisation lemma for ⊩ᵛ_.

  ⊩ᵛε⇔ : ∇ »⊩ᵛ ε ⇔ » ∇
  ⊩ᵛε⇔ = id⇔

opaque
  unfolding _»⊩ᵛ_

  -- A characterisation lemma for ⊩ᵛ_.

  ⊩ᵛ∙⇔ : ⊩ᵛ Γ »∙ A ⇔ ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A
  ⊩ᵛ∙⇔ = id⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ⇔⊩ᵛ≡ : (Γ ⊩ᵛ⟨ l ⟩ A) ⇔ Γ ⊩ᵛ⟨ l ⟩ A ≡ A
  ⊩ᵛ⇔⊩ᵛ≡ = id⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ⇔ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ⇔
    (∇ »⊩ᵛ Δ ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
      ∇′ » Η ⊩⟨ l ⟩ A [ σ₁ ] ≡ A [ σ₂ ]))
  ⊩ᵛ⇔ = id⇔

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ⇔ʰ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ⇔
    (∇ »⊩ᵛ Δ ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n}
        ⦃ inc : Var-included or-empty Η ⦄ →
      ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ → ∇′ » Η H.⊩⟨ l ⟩ A [ σ₁ ] ≡ A [ σ₂ ]))
  ⊩ᵛ⇔ʰ {κ} {∇} {n} {Δ} {l} {A} =
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A                                                ⇔⟨ ⊩ᵛ⇔ ⟩

    ∇ »⊩ᵛ Δ ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
     ∇′ » Η ⊩⟨ l ⟩ A [ σ₁ ] ≡ A [ σ₂ ])                            ⇔⟨ (Σ-cong-⇔ λ _ →
                                                                         implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                         implicit-Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                                         implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                         implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                         Π⦃⦄→⇔⦃⦄→Π ∘⇔ (Π-cong-⇔ λ _ → ⊩≡⇔)) ⟩
    ∇ »⊩ᵛ Δ ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n}
       ⦃ inc : Var-included or-empty Η ⦄ →
     ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ → ∇′ » Η H.⊩⟨ l ⟩ A [ σ₁ ] ≡ A [ σ₂ ])  □⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡⇔ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B ⇔
    (∇ »⊩ᵛ Δ ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
      ∇′ » Η ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ]))
  ⊩ᵛ≡⇔ = id⇔

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ≡⇔ʰ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B ⇔
    (∇ »⊩ᵛ Δ ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n}
      ⦃ inc : Var-included or-empty Η ⦄ →
      ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ → ∇′ » Η H.⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ]))
  ⊩ᵛ≡⇔ʰ {κ} {∇} {n} {Δ} {l} {A} {B} =
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B                                            ⇔⟨ ⊩ᵛ≡⇔ ⟩

    ∇ »⊩ᵛ Δ ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
     ∇′ » Η ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ])                            ⇔⟨ (Σ-cong-⇔ λ _ →
                                                                         implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                         implicit-Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                                         implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                         implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                         Π⦃⦄→⇔⦃⦄→Π ∘⇔ (Π-cong-⇔ λ _ → ⊩≡⇔)) ⟩
    ∇ »⊩ᵛ Δ ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n}
       ⦃ inc : Var-included or-empty Η ⦄ →
     ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ → ∇′ » Η H.⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ])  □⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷⇔⊩ᵛ≡∷ : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ⇔ Γ ⊩ᵛ⟨ l ⟩ t ≡ t ∷ A
  ⊩ᵛ∷⇔⊩ᵛ≡∷ = id⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_ _⊩ᵛ⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷⇔ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
      ∇′ » Η ⊩⟨ l ⟩ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ∷⇔ = id⇔

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷⇔ʰ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n}
      ⦃ inc : Var-included or-empty Η ⦄ →
      ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
      ∇′ » Η H.⊩⟨ l ⟩ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ∷⇔ʰ {κ} {∇} {n} {Δ} {l} {t} {A} =
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A                                                       ⇔⟨ ⊩ᵛ∷⇔ ⟩

    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
     ∇′ » Η ⊩⟨ l ⟩ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ])                            ⇔⟨ (Σ-cong-⇔ λ _ →
                                                                                    implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                                    implicit-Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                                                    implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                                    implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                                    Π⦃⦄→⇔⦃⦄→Π ∘⇔ (Π-cong-⇔ λ _ → ⊩≡∷⇔)) ⟩
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n}
       ⦃ inc : Var-included or-empty Η ⦄ →
     ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ → ∇′ » Η H.⊩⟨ l ⟩ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ])  □⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷⇔ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
      ∇′ » Η ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ≡∷⇔ = id⇔

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ≡∷⇔ʰ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n}
        ⦃ inc : Var-included or-empty Η ⦄ →
      ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
      ∇′ » Η H.⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ≡∷⇔ʰ {κ} {∇} {n} {Δ} {l} {t} {u} {A} =
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A                                                   ⇔⟨ ⊩ᵛ≡∷⇔ ⟩

    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
     ∇′ » Η ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ])                            ⇔⟨ (Σ-cong-⇔ λ _ →
                                                                                    implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                                    implicit-Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                                                    implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                                    implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                                    Π⦃⦄→⇔⦃⦄→Π ∘⇔ (Π-cong-⇔ λ _ → ⊩≡∷⇔)) ⟩
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n}
       ⦃ inc : Var-included or-empty Η ⦄ →
     ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ → ∇′ » Η H.⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ])  □⇔

opaque
  unfolding _⊩ˢ_≡_∷_

  -- A characterisation lemma for _⊩ˢ_≡_∷_.

  ⊩ˢ≡∷ε⇔ :
    ∇ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ ε ⇔
    (» ∇ × (⦃ inc : Var-included or-empty Δ ⦄ → ∇ »⊢ Δ))
  ⊩ˢ≡∷ε⇔ = id⇔

opaque
  unfolding _⊩ˢ_≡_∷_

  -- A characterisation lemma for _⊩ˢ_≡_∷_.

  ⊩ˢ≡∷∙⇔ :
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ A ⇔
    ((∃ λ l →
      (∇ » Δ ⊩ᵛ⟨ l ⟩ A) ×
      ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
     ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ)
  ⊩ˢ≡∷∙⇔ = id⇔

opaque
  unfolding _⊩ˢ_∷_

  -- A characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷⇔⊩ˢ≡∷ : ∇ » Η ⊩ˢ σ ∷ Δ ⇔ ∇ » Η ⊩ˢ σ ≡ σ ∷ Δ
  ⊩ˢ∷⇔⊩ˢ≡∷ = id⇔

opaque

  -- A characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷ε⇔ :
    ∇ » Δ ⊩ˢ σ ∷ ε ⇔
    (» ∇ × (⦃ inc : Var-included or-empty Δ ⦄ → ∇ »⊢ Δ))
  ⊩ˢ∷ε⇔ {∇} {Δ} {σ} =
    ∇ » Δ ⊩ˢ σ ∷ ε                                      ⇔⟨ ⊩ˢ∷⇔⊩ˢ≡∷ ⟩
    ∇ » Δ ⊩ˢ σ ≡ σ ∷ ε                                  ⇔⟨ ⊩ˢ≡∷ε⇔ ⟩
    » ∇ × (⦃ inc : Var-included or-empty Δ ⦄ → ∇ »⊢ Δ)  □⇔

opaque

  -- A characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷∙⇔ :
    ∇ » Η ⊩ˢ σ ∷ Δ ∙ A ⇔
    ((∃ λ l → (∇ » Δ ⊩ᵛ⟨ l ⟩ A) × ∇ » Η ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
     ∇ » Η ⊩ˢ tail σ ∷ Δ)
  ⊩ˢ∷∙⇔ {∇} {Η} {σ} {Δ} {A} =
    ∇ » Η ⊩ˢ σ ∷ Δ ∙ A                                                  ⇔⟨ ⊩ˢ∷⇔⊩ˢ≡∷ ⟩

    ∇ » Η ⊩ˢ σ ≡ σ ∷ Δ ∙ A                                              ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩

    (∃ λ l →
     (∇ » Δ ⊩ᵛ⟨ l ⟩ A) ×
     ∇ » Η ⊩⟨ l ⟩ head σ ≡ head σ ∷ A [ tail σ ]) ×
    ∇ » Η ⊩ˢ tail σ ≡ tail σ ∷ Δ                                        ⇔˘⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → ⊩∷⇔⊩≡∷)
                                                                              ×-cong-⇔
                                                                            ⊩ˢ∷⇔⊩ˢ≡∷ ⟩
    (∃ λ l → (∇ » Δ ⊩ᵛ⟨ l ⟩ A) × ∇ » Η ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    ∇ » Η ⊩ˢ tail σ ∷ Δ                                                 □⇔

------------------------------------------------------------------------
-- An introduction lemma

opaque

  -- An introduction lemma for ⊩ᵛ_.

  ⊩ᵛ-∙-intro : Γ ⊩ᵛ⟨ l ⟩ A → ⊩ᵛ Γ »∙ A
  ⊩ᵛ-∙-intro ⊩A = ⊩ᵛ∙⇔ .proj₂ (_ , ⊩A)

------------------------------------------------------------------------
-- Reflexivity

opaque

  -- Reflexivity for _⊩ˢ_≡_∷_.

  refl-⊩ˢ≡∷ :
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩ˢ σ ≡ σ ∷ Δ
  refl-⊩ˢ≡∷ = ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- Reflexivity for _⊩ᵛ⟨_⟩_≡_.

  refl-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ A
  refl-⊩ᵛ≡ = ⊩ᵛ⇔⊩ᵛ≡ .proj₁

opaque

  -- Reflexivity for _⊩ᵛ⟨_⟩_≡_∷_.

  refl-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ t ∷ A
  refl-⊩ᵛ≡∷ = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

------------------------------------------------------------------------
-- Some substitution lemmas

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A≡B = ⊩ᵛ≡⇔ .proj₁ A≡B .proj₂ id

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩[] :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ A [ σ ]
  ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A =
    ⊩⇔⊩≡ .proj₂ ∘→ ⊩ᵛ⇔ .proj₁ ⊩A .proj₂ id ∘→ refl-⊩ˢ≡∷

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u = ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂ id

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ t [ σ ] ∷ A [ σ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ id ∘→ refl-⊩ˢ≡∷

------------------------------------------------------------------------
-- Symmetry

opaque

  -- Symmetry for _⊩ˢ_≡_∷_.

  sym-⊩ˢ≡∷ :
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩ˢ σ₂ ≡ σ₁ ∷ Δ
  sym-⊩ˢ≡∷ {Δ = ε} =
    ⊩ˢ≡∷ε⇔ .proj₂ ∘→ ⊩ˢ≡∷ε⇔ .proj₁
  sym-⊩ˢ≡∷ {Δ = _ ∙ _} = λ σ₁≡σ₂ →
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((l , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
    case conv-⊩≡∷ (⊩ᵛ⇔ .proj₁ ⊩A .proj₂ id σ₁₊≡σ₂₊) $
         sym-⊩≡∷ σ₁₀≡σ₂₀ of λ
      σ₂₀≡σ₁₀ →
    ⊩ˢ≡∷∙⇔ .proj₂ ((l , ⊩A , σ₂₀≡σ₁₀) , sym-⊩ˢ≡∷ σ₁₊≡σ₂₊)

opaque

  -- Symmetry for _⊩ᵛ⟨_⟩_≡_.

  sym-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l ⟩ B ≡ A
  sym-⊩ᵛ≡ A≡B =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (⊩Γ , A≡B) →
    ⊩ᵛ≡⇔ .proj₂ (⊩Γ , λ ξ⊇ → sym-⊩≡ ∘→ A≡B ξ⊇ ∘→ sym-⊩ˢ≡∷)

opaque

  -- Symmetry for _⊩ᵛ⟨_⟩_≡_∷_.

  sym-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ u ≡ t ∷ A
  sym-⊩ᵛ≡∷ t≡u =
    case ⊩ᵛ≡∷⇔ .proj₁ t≡u of λ
      (⊩A , t≡u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩A
      , λ ξ⊇ σ₁≡σ₂ →
          conv-⊩≡∷ (sym-⊩≡ $ ⊩ᵛ⇔ .proj₁ ⊩A .proj₂ ξ⊇ σ₁≡σ₂) $
          sym-⊩≡∷ $ t≡u ξ⊇ $ sym-⊩ˢ≡∷ σ₁≡σ₂)

------------------------------------------------------------------------
-- One transitivity lemma

opaque

  -- Transitivity for _⊩ˢ_≡_∷_.

  trans-⊩ˢ≡ :
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩ˢ σ₂ ≡ σ₃ ∷ Δ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₃ ∷ Δ
  trans-⊩ˢ≡ {Δ = ε} σ₁≡σ₂ _ =
    ⊩ˢ≡∷ε⇔ .proj₂ $ ⊩ˢ≡∷ε⇔ .proj₁ σ₁≡σ₂
  trans-⊩ˢ≡ {Δ = _ ∙ _} σ₁≡σ₂ σ₂≡σ₃ =
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((l , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₂≡σ₃ of λ
      ((l , ⊩A , σ₂₀≡σ₃₀) , σ₂₊≡σ₃₊) →
    case conv-⊩≡∷ (⊩ᵛ⇔ .proj₁ ⊩A .proj₂ id $ sym-⊩ˢ≡∷ σ₁₊≡σ₂₊) σ₂₀≡σ₃₀ of λ
      σ₂₀≡σ₃₀ →
    ⊩ˢ≡∷∙⇔ .proj₂
      ( (l , ⊩A , trans-⊩≡∷ σ₁₀≡σ₂₀ σ₂₀≡σ₃₀)
      , trans-⊩ˢ≡ σ₁₊≡σ₂₊ σ₂₊≡σ₃₊
      )

------------------------------------------------------------------------
-- Some well-formedness lemmas

opaque

  -- A well-formedness lemma for ⊩ᵛ_.

  wf-⊩ᵛ-∙ : ⊩ᵛ Γ »∙ A → ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A
  wf-⊩ᵛ-∙ = ⊩ᵛ∙⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_.

  wf-⊩ᵛ : Γ ⊩ᵛ⟨ l ⟩ A → ⊩ᵛ Γ
  wf-⊩ᵛ = proj₁ ∘→ ⊩ᵛ⇔ .proj₁

opaque

  -- A well-formedness lemma for ⊩ᵛ_.

  wf-⊩ᵛ′ : ∇ »⊩ᵛ Δ → » ∇
  wf-⊩ᵛ′ {Δ = ε}     = ⊩ᵛε⇔ .proj₁
  wf-⊩ᵛ′ {Δ = Δ ∙ A} = wf-⊩ᵛ′ ∘→ wf-⊩ᵛ ∘→ proj₂ ∘→ ⊩ᵛ∙⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_.

  wf-∙-⊩ᵛ :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B →
    ∃ λ l′ → Γ ⊩ᵛ⟨ l′ ⟩ A
  wf-∙-⊩ᵛ = wf-⊩ᵛ-∙ ∘→ wf-⊩ᵛ

opaque

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_∷_.

  wf-⊩ᵛ∷ : Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ ⊩ᵛ⟨ l ⟩ A
  wf-⊩ᵛ∷ = proj₁ ∘→ ⊩ᵛ∷⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ˢ_∷_.

  wf-⊩ˢ∷ : ∇ » Η ⊩ˢ σ ∷ Δ → ∇ »⊩ᵛ Δ
  wf-⊩ˢ∷ {Δ = ε}     = ⊩ᵛε⇔ .proj₂ ∘→ proj₁ ∘→ ⊩ˢ∷ε⇔ .proj₁
  wf-⊩ˢ∷ {Δ = _ ∙ _} =
    ⊩ᵛ∙⇔ .proj₂ ∘→ Σ.map idᶠ proj₁ ∘→ proj₁ ∘→ ⊩ˢ∷∙⇔ .proj₁

opaque

  -- A well-formedness lemma for _⊩ˢ_∷_.

  ⊩ˢ∷→» : ∇ » Η ⊩ˢ σ ∷ Δ → » ∇
  ⊩ˢ∷→» = wf-⊩ᵛ′ ∘→ wf-⊩ˢ∷

opaque

  -- A well-formedness lemma for _⊩ˢ_≡_∷_.

  wf-⊩ˢ≡∷ : ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ → ∇ » Η ⊩ˢ σ₁ ∷ Δ × ∇ » Η ⊩ˢ σ₂ ∷ Δ
  wf-⊩ˢ≡∷ σ₁≡σ₂ =
      ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ (trans-⊩ˢ≡ σ₁≡σ₂ (sym-⊩ˢ≡∷ σ₁≡σ₂))
    , ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ (trans-⊩ˢ≡ (sym-⊩ˢ≡∷ σ₁≡σ₂) σ₁≡σ₂)

opaque

  -- A well-formedness lemma for _⊩ˢ_≡_∷_.

  ⊩ˢ≡∷→» : ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ → » ∇
  ⊩ˢ≡∷→» = ⊩ˢ∷→» ∘→ proj₁ ∘→ wf-⊩ˢ≡∷

------------------------------------------------------------------------
-- Weakening of the definition context

opaque mutual

  -- A definitional weakening lemma for ⊩ᵛ_.

  defn-wk-⊩ᵛ′ : ξ » ∇′ ⊇ ∇ → ∇ »⊩ᵛ Δ → ∇′ »⊩ᵛ Δ
  defn-wk-⊩ᵛ′ {Δ = ε} ξ⊇ ⊩Δ =
    ⊩ᵛε⇔ .proj₂ (wf-»⊇ ξ⊇ (⊩ᵛε⇔ .proj₁ ⊩Δ))
  defn-wk-⊩ᵛ′ {Δ = Δ ∙ A} ξ⊇ ⊩Δ =
    let (l , ⊩A) = ⊩ᵛ∙⇔ .proj₁ ⊩Δ in
    ⊩ᵛ∙⇔ .proj₂ (l , defn-wk-⊩ᵛ ξ⊇ ⊩A)

  -- A definitional weakening lemma for _⊩ᵛ⟨_⟩_.

  defn-wk-⊩ᵛ : ξ » ∇′ ⊇ ∇ → ∇ » Δ ⊩ᵛ⟨ l ⟩ A → ∇′ » Δ ⊩ᵛ⟨ l ⟩ A
  defn-wk-⊩ᵛ ξ⊇ = ⊩ᵛ⇔⊩ᵛ≡ .proj₂ ∘→ defn-wk-⊩ᵛ≡ ξ⊇ ∘→ ⊩ᵛ⇔⊩ᵛ≡ .proj₁

  -- A definitional weakening lemma for _⊩ᵛ⟨_⟩_≡_.

  defn-wk-⊩ᵛ≡ : ξ » ∇′ ⊇ ∇ → ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B → ∇′ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B
  defn-wk-⊩ᵛ≡ {A} {B} ξ⊇ A≡B =
    let (⊩Δ , A≡B) = ⊩ᵛ≡⇔ .proj₁ A≡B
    in  ⊩ᵛ≡⇔ .proj₂
          ( defn-wk-⊩ᵛ′ ξ⊇ ⊩Δ
          , λ ξ⊇′ → A≡B (ξ⊇′ •ₜᵈ ξ⊇)
          )

opaque

  -- A definitional weakening lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  defn-wk-⊩ᵛ≡∷ :
    ξ » ∇′ ⊇ ∇ →
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    ∇′ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A
  defn-wk-⊩ᵛ≡∷ {t} {u} {A} ξ⊇ t≡u =
    let (⊩A , t≡u) = ⊩ᵛ≡∷⇔ .proj₁ t≡u
    in  ⊩ᵛ≡∷⇔ .proj₂
          ( defn-wk-⊩ᵛ ξ⊇ ⊩A
          , λ ξ⊇′ → t≡u (ξ⊇′ •ₜᵈ ξ⊇)
          )

opaque

  -- A definitional weakening lemma for _⊩ᵛ⟨_⟩_∷_.

  defn-wk-⊩ᵛ∷ :
    ξ » ∇′ ⊇ ∇ →
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A →
    ∇′ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A
  defn-wk-⊩ᵛ∷ ξ⊇ = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ defn-wk-⊩ᵛ≡∷ ξ⊇ ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

opaque

  -- A definitional weakening lemma for _⊩ˢ_≡_∷_.

  defn-wk-⊩ˢ≡∷ :
    ⦃ inc : Var-included or-empty Η ⦄ →
    ξ » ∇′ ⊇ ∇ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ
  defn-wk-⊩ˢ≡∷ {Δ = ε} ⦃ inc ⦄ ξ⊇ σ₁≡σ₂ =
    ⊩ˢ≡∷ε⇔ .proj₂ (wf-»⊇ ξ⊇ (⊩ˢ≡∷→» σ₁≡σ₂) , defn-wk′ ξ⊇ (⊩ˢ≡∷ε⇔ .proj₁ σ₁≡σ₂ .proj₂ ⦃ inc ⦄))
  defn-wk-⊩ˢ≡∷ {Δ = Δ ∙ A} ξ⊇ σ₁≡σ₂ =
    let ((l , ⊩A , h≡h) , t≡t) = ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂
    in  ⊩ˢ≡∷∙⇔ .proj₂ $ (l , defn-wk-⊩ᵛ ξ⊇ ⊩A , defn-wk-⊩≡∷ ξ⊇ h≡h)
                      , defn-wk-⊩ˢ≡∷ ξ⊇ t≡t

opaque

  -- A definitional weakening lemma for _⊩ˢ_∷_.

  defn-wk-⊩ˢ∷ : ξ » ∇′ ⊇ ∇ → ∇ » Η ⊩ˢ σ ∷ Δ → ∇′ » Η ⊩ˢ σ ∷ Δ
  defn-wk-⊩ˢ∷ {Δ = ε} ξ⊇ ⊩σ =
    ⊩ˢ∷ε⇔ .proj₂ (wf-»⊇ ξ⊇ (⊩ˢ∷→» ⊩σ) , defn-wk′ ξ⊇ (⊩ˢ∷ε⇔ .proj₁ ⊩σ .proj₂))
  defn-wk-⊩ˢ∷ {Δ = Δ ∙ A} ξ⊇ ⊩σ =
    let ((l , ⊩A , ⊩h) , ⊩t) = ⊩ˢ∷∙⇔ .proj₁ ⊩σ
    in  ⊩ˢ∷∙⇔ .proj₂ $ (l , defn-wk-⊩ᵛ ξ⊇ ⊩A , defn-wk-⊩∷ ξ⊇ ⊩h)
                     , defn-wk-⊩ˢ∷ ξ⊇ ⊩t

------------------------------------------------------------------------
-- Changing type levels

opaque

  -- Changing type levels for _⊩ᵛ⟨_⟩_≡_.

  level-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B
  level-⊩ᵛ≡ ⊩A ⊩B A≡B =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (⊩Γ , A≡B) →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩Γ
      , λ ξ⊇ σ₁≡σ₂ →
          case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
            (⊩σ₁ , ⊩σ₂) →
          level-⊩≡ (⊩ᵛ→⊩ˢ∷→⊩[] (defn-wk-⊩ᵛ ξ⊇ ⊩A) ⊩σ₁)
                   (⊩ᵛ→⊩ˢ∷→⊩[] (defn-wk-⊩ᵛ ξ⊇ ⊩B) ⊩σ₂) $
          A≡B ξ⊇ σ₁≡σ₂
      )

opaque

  -- Changing type levels for _⊩ᵛ⟨_⟩_≡_∷_.

  level-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A
  level-⊩ᵛ≡∷ ⊩A t≡u =
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩A
      , λ ξ⊇ σ₁≡σ₂ → let »∇′ = ⊩ˢ≡∷→» σ₁≡σ₂ in
          level-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] (defn-wk-⊩ᵛ ξ⊇ ⊩A) $ wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) $
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t≡u) σ₁≡σ₂
      )

opaque

  -- Changing type levels for _⊩ᵛ⟨_⟩_∷_.

  level-⊩ᵛ∷ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A
  level-⊩ᵛ∷ ⊩A =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ level-⊩ᵛ≡∷ ⊩A ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

------------------------------------------------------------------------
-- More transitivity lemmas

opaque

  -- Transitivity for _⊩ᵛ⟨_⟩_≡_.

  trans-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l ⟩ B ≡ C →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ C
  trans-⊩ᵛ≡ {A} {B} {C} A≡B B≡C =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (⊩Γ , A≡B) →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩Γ
      , λ ξ⊇ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          A [ σ₁ ]  ≡⟨ A≡B ξ⊇ $ refl-⊩ˢ≡∷ (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) ⟩⊩
          B [ σ₁ ]  ≡⟨ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (defn-wk-⊩ᵛ≡ ξ⊇ B≡C) σ₁≡σ₂ ⟩⊩∎
          C [ σ₂ ]  ∎
      )

opaque

  -- Transitivity for _⊩ᵛ⟨_⟩_≡_∷_.

  trans-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ u ≡ v ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ v ∷ A
  trans-⊩ᵛ≡∷ {t} {u} {v} t≡u u≡v =
    case ⊩ᵛ≡∷⇔ .proj₁ u≡v of λ
      (⊩A , u≡v) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩A
      , λ ξ⊇ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          t [ σ₁ ]  ≡⟨ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ (level-⊩ᵛ≡∷ ⊩A t≡u)) $
                       refl-⊩ˢ≡∷ (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) ⟩⊩∷
          u [ σ₁ ]  ≡⟨ u≡v ξ⊇ σ₁≡σ₂ ⟩⊩∷∎
          v [ σ₂ ]  ∎
      )

------------------------------------------------------------------------
-- More well-formedness lemmas

opaque

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_≡_.

  wf-⊩ᵛ≡ : Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ⊩ᵛ⟨ l ⟩ A × Γ ⊩ᵛ⟨ l ⟩ B
  wf-⊩ᵛ≡ A≡B =
      ⊩ᵛ⇔⊩ᵛ≡ .proj₂ (trans-⊩ᵛ≡ A≡B (sym-⊩ᵛ≡ A≡B))
    , ⊩ᵛ⇔⊩ᵛ≡ .proj₂ (trans-⊩ᵛ≡ (sym-⊩ᵛ≡ A≡B) A≡B)

opaque

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  wf-⊩ᵛ≡∷ : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A → Γ ⊩ᵛ⟨ l ⟩ t ∷ A × Γ ⊩ᵛ⟨ l ⟩ u ∷ A
  wf-⊩ᵛ≡∷ t≡u =
      ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (trans-⊩ᵛ≡∷ t≡u (sym-⊩ᵛ≡∷ t≡u))
    , ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ (trans-⊩ᵛ≡∷ (sym-⊩ᵛ≡∷ t≡u) t≡u)

------------------------------------------------------------------------
-- More characterisation lemmas

opaque

  -- A variant of ⊩ᵛ≡⇔.

  ⊩ᵛ≡⇔′ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
     ∇ » Δ ⊩ᵛ⟨ l ⟩ B ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ : Subst m n} → ∇′ » Η ⊩ˢ σ ∷ Δ →
      ∇′ » Η ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ]))
  ⊩ᵛ≡⇔′ {A} {B} =
      (λ A≡B →
         case wf-⊩ᵛ≡ A≡B of λ
           (⊩A , ⊩B) →
         ⊩A , ⊩B , λ {_ _ _} ξ⊇ {_ _ _} ⊩σ →
                     ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (defn-wk-⊩ᵛ≡ ξ⊇ A≡B) (refl-⊩ˢ≡∷ ⊩σ))
    , (λ (⊩A , _ , A≡B) →
         ⊩ᵛ≡⇔ .proj₂
           ( wf-⊩ᵛ ⊩A
           , λ ξ⊇ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
               A [ σ₁ ]  ≡⟨ ⊩ᵛ⇔ .proj₁ ⊩A .proj₂ ξ⊇ σ₁≡σ₂ ⟩⊩
               A [ σ₂ ]  ≡⟨ A≡B ξ⊇ $ wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₂ ⟩⊩∎
               B [ σ₂ ]  ∎
           ))

opaque

  -- A variant of ⊩ᵛ≡⇔′.

  ⊩ᵛ≡⇔′ʰ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
     ∇ » Δ ⊩ᵛ⟨ l ⟩ B ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ : Subst m n}
        ⦃ inc : Var-included or-empty Η ⦄ →
      ∇′ » Η ⊩ˢ σ ∷ Δ →
      ∇′ » Η H.⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ]))
  ⊩ᵛ≡⇔′ʰ {κ} {∇} {n} {Δ} {l} {A} {B} =
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B                           ⇔⟨ ⊩ᵛ≡⇔′ ⟩

    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
    ∇ » Δ ⊩ᵛ⟨ l ⟩ B ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ : Subst m n} → ∇′ » Η ⊩ˢ σ ∷ Δ →
     ∇′ » Η ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ])             ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                      implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                      implicit-Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                      implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                      implicit-Π-cong-⇔ λ _ →
                                                      Π⦃⦄→⇔⦃⦄→Π ∘⇔ (Π-cong-⇔ λ _ → ⊩≡⇔)) ⟩
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
    ∇ » Δ ⊩ᵛ⟨ l ⟩ B ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ : Subst m n}
       ⦃ inc : Var-included or-empty Η ⦄ →
     ∇′ » Η ⊩ˢ σ ∷ Δ →
     ∇′ » Η H.⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ])           □⇔

opaque

  -- A variant of ⊩ᵛ≡⇔.

  ⊩ᵛ≡⇔″ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
     ∇ » Δ ⊩ᵛ⟨ l ⟩ B ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
      ∇′ » Η ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ]))
  ⊩ᵛ≡⇔″ =
      (λ A≡B →
         case wf-⊩ᵛ≡ A≡B of λ
           (⊩A , ⊩B) →
         ⊩A , ⊩B , λ {_ _ _} ξ⊇ {_ _ _ _} σ₁≡σ₂ →
                     ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (defn-wk-⊩ᵛ≡ ξ⊇ A≡B) σ₁≡σ₂)
    , (λ (⊩A , _ , A≡B) →
         ⊩ᵛ≡⇔ .proj₂ (wf-⊩ᵛ ⊩A , A≡B))

opaque

  -- A variant of ⊩ᵛ≡⇔″.

  ⊩ᵛ≡⇔″ʰ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
     ∇ » Δ ⊩ᵛ⟨ l ⟩ B ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n}
        ⦃ inc : Var-included or-empty Η ⦄ →
      ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
      ∇′ » Η H.⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ]))
  ⊩ᵛ≡⇔″ʰ {κ} {∇} {n} {Δ} {l} {A} {B} =
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B                                     ⇔⟨ ⊩ᵛ≡⇔″ ⟩

    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
    ∇ » Δ ⊩ᵛ⟨ l ⟩ B ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
     ∇′ » Η ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ])                     ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                implicit-Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                                implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                Π⦃⦄→⇔⦃⦄→Π ∘⇔ (Π-cong-⇔ λ _ → ⊩≡⇔)) ⟩
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ×
    ∇ » Δ ⊩ᵛ⟨ l ⟩ B ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n}
       ⦃ inc : Var-included or-empty Η ⦄ →
     ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
     ∇′ » Η H.⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ])                   □⇔

opaque

  -- A variant of ⊩ᵛ≡∷⇔.

  ⊩ᵛ≡∷⇔′ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A ×
     ∇ » Δ ⊩ᵛ⟨ l ⟩ u ∷ A ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ : Subst m n} → ∇′ » Η ⊩ˢ σ ∷ Δ →
      ∇′ » Η ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ]))
  ⊩ᵛ≡∷⇔′ {t} {u} =
      (λ t≡u →
         case wf-⊩ᵛ≡∷ t≡u of λ
           (⊩t , ⊩u) →
         ⊩t , ⊩u , λ {_ _ _} ξ⊇ {_ _ _} ⊩σ →
                     ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t≡u) (refl-⊩ˢ≡∷ ⊩σ))
    , (λ (_ , ⊩u , t≡u) →
         ⊩ᵛ≡∷⇔ .proj₂
           ( wf-⊩ᵛ∷ ⊩u
           , λ ξ⊇ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
               t [ σ₁ ]  ≡⟨ t≡u ξ⊇ $ wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁ ⟩⊩∷
               u [ σ₁ ]  ≡⟨ ⊩ᵛ∷⇔ .proj₁ ⊩u .proj₂ ξ⊇ σ₁≡σ₂ ⟩⊩∷∎
               u [ σ₂ ]  ∎
           ))

opaque

  -- A variant of ⊩ᵛ≡∷⇔′.

  ⊩ᵛ≡∷⇔′ʰ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A ×
     ∇ » Δ ⊩ᵛ⟨ l ⟩ u ∷ A ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ : Subst m n}
        ⦃ inc : Var-included or-empty Η ⦄ →
      ∇′ » Η ⊩ˢ σ ∷ Δ →
      ∇′ » Η H.⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ]))
  ⊩ᵛ≡∷⇔′ʰ {κ} {∇} {n} {Δ} {l} {t} {u} {A} =
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A                        ⇔⟨ ⊩ᵛ≡∷⇔′ ⟩

    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A ×
    ∇ » Δ ⊩ᵛ⟨ l ⟩ u ∷ A ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ : Subst m n} → ∇′ » Η ⊩ˢ σ ∷ Δ →
     ∇′ » Η ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ])    ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                       implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                       implicit-Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                       implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                       implicit-Π-cong-⇔ λ _ →
                                                       Π⦃⦄→⇔⦃⦄→Π ∘⇔ (Π-cong-⇔ λ _ → ⊩≡∷⇔)) ⟩
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A ×
    ∇ » Δ ⊩ᵛ⟨ l ⟩ u ∷ A ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ : Subst m n}
       ⦃ inc : Var-included or-empty Η ⦄ →
     ∇′ » Η ⊩ˢ σ ∷ Δ →
     ∇′ » Η H.⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ])  □⇔

opaque

  -- A variant of ⊩ᵛ≡∷⇔.

  ⊩ᵛ≡∷⇔″ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A ×
     ∇ » Δ ⊩ᵛ⟨ l ⟩ u ∷ A ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
      ∇′ » Η ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ≡∷⇔″ =
      (λ t≡u →
         case wf-⊩ᵛ≡∷ t≡u of λ
           (⊩t , ⊩u) →
         ⊩t , ⊩u , λ {_ _ _} ξ⊇ {_ _ _ _} σ₁≡σ₂ →
                     ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t≡u) σ₁≡σ₂)
    , (λ (⊩t , _ , t≡u) →
         ⊩ᵛ≡∷⇔ .proj₂ (wf-⊩ᵛ∷ ⊩t , t≡u))

opaque

  -- A variant of ⊩ᵛ≡∷⇔″.

  ⊩ᵛ≡∷⇔″ʰ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⇔
    (∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A ×
     ∇ » Δ ⊩ᵛ⟨ l ⟩ u ∷ A ×
     (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
      ∀ {m Η} {σ₁ σ₂ : Subst m n}
        ⦃ inc : Var-included or-empty Η ⦄ →
      ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
      ∇′ » Η H.⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ≡∷⇔″ʰ {κ} {∇} {n} {Δ} {l} {t} {u} {A} =
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A                                 ⇔⟨ ⊩ᵛ≡∷⇔″ ⟩

    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A ×
    ∇ » Δ ⊩ᵛ⟨ l ⟩ u ∷ A ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n} → ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
     ∇′ » Η ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ])          ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                implicit-Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                                implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                implicit-Π-cong-⇔ λ _ → implicit-Π-cong-⇔ λ _ →
                                                                Π⦃⦄→⇔⦃⦄→Π ∘⇔ (Π-cong-⇔ λ _ → ⊩≡∷⇔)) ⟩
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A ×
    ∇ » Δ ⊩ᵛ⟨ l ⟩ u ∷ A ×
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ₁ σ₂ : Subst m n}
       ⦃ inc : Var-included or-empty Η ⦄ →
     ∇′ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
     ∇′ » Η H.⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ])        □⇔

opaque

  -- A variant of ⊩ˢ∷∙⇔.

  ⊩ˢ∷∙⇔′ :
    ∇ » Η ⊩ˢ σ ∷ Δ ∙ A ⇔
    ((∃ λ l → ∇ » Δ ⊩ᵛ⟨ l ⟩ A) ×
     (∃ λ l → ∇ » Η ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
     ∇ » Η ⊩ˢ tail σ ∷ Δ)
  ⊩ˢ∷∙⇔′ {∇} {Η} {σ} {Δ} {A} =
    ∇ » Η ⊩ˢ σ ∷ Δ ∙ A                                                  ⇔⟨ ⊩ˢ∷∙⇔ ⟩

    (∃ λ l → (∇ » Δ ⊩ᵛ⟨ l ⟩ A) × ∇ » Η ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    ∇ » Η ⊩ˢ tail σ ∷ Δ                                                 ⇔⟨ (λ ((l , ⊩A , ⊩head) , ⊩tail) →
                                                                              (l , ⊩A) , (l , ⊩head) , ⊩tail)
                                                                         , (λ ((l₁ , ⊩A) , (_ , ⊩head) , ⊩tail) →
                                                                              (l₁ , ⊩A , level-⊩∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩tail) ⊩head) , ⊩tail)
                                                                         ⟩
    (∃ λ l → ∇ » Δ ⊩ᵛ⟨ l ⟩ A) ×
    (∃ λ l → ∇ » Η ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    ∇ » Η ⊩ˢ tail σ ∷ Δ                                                 □⇔

opaque

  -- A variant of ⊩ˢ≡∷∙⇔.

  ⊩ˢ≡∷∙⇔′ :
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ A ⇔
    ((∃ λ l → ∇ » Δ ⊩ᵛ⟨ l ⟩ A) ×
     (∃ λ l → ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
     ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ)
  ⊩ˢ≡∷∙⇔′ {∇} {Η} {σ₁} {σ₂} {Δ} {A} =
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ A                                                ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩

    (∃ λ l →
     (∇ » Δ ⊩ᵛ⟨ l ⟩ A) × ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ                                          ⇔⟨ (λ ((l , ⊩A , head≡head) , tail≡tail) →
                                                                                  (l , ⊩A) , (l , head≡head) , tail≡tail)
                                                                             , (λ ((l₁ , ⊩A) , (_ , head≡head) , tail≡tail) →
                                                                                    ( l₁ , ⊩A
                                                                                    , level-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A (wf-⊩ˢ≡∷ tail≡tail .proj₁))
                                                                                        head≡head
                                                                                    )
                                                                                  , tail≡tail)
                                                                             ⟩
    (∃ λ l → ∇ » Δ ⊩ᵛ⟨ l ⟩ A) ×
    (∃ λ l → ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ                                          □⇔

------------------------------------------------------------------------
-- Conversion

opaque

  -- Conversion for one of the contexts for _⊩ˢ_≡_∷_.

  conv-⊩ˢ≡∷-∙ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B → ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ A →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ B
  conv-⊩ˢ≡∷-∙ {∇} {Δ} {A} {B} {Η} {σ₁} {σ₂} A≡B =
    case ⊩ᵛ≡⇔′ .proj₁ A≡B of λ
      (_ , ⊩B , A≡B) →

    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ A                                                ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

    (∃ λ l →
     (∇ » Δ ⊩ᵛ⟨ l ⟩ A) × ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ                                          →⟨ (λ ((_ , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                                    (_ , ⊩B , conv-⊩≡∷ (A≡B id $ wf-⊩ˢ≡∷ σ₁₊≡σ₂₊ .proj₁) σ₁₀≡σ₂₀)
                                                                                  , σ₁₊≡σ₂₊) ⟩
    (∃ λ l →
     (∇ » Δ ⊩ᵛ⟨ l ⟩ B) × ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B [ tail σ₁ ]) ×
    ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ                                          ⇔˘⟨ ⊩ˢ≡∷∙⇔ ⟩→

    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ B                                                □

opaque

  -- Conversion for one of the contexts for _⊩ˢ_∷_.

  conv-⊩ˢ∷-∙ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B → ∇ » Η ⊩ˢ σ ∷ Δ ∙ A → ∇ » Η ⊩ˢ σ ∷ Δ ∙ B
  conv-⊩ˢ∷-∙ A≡B =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ conv-⊩ˢ≡∷-∙ A≡B ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- Conversion for the context for _⊩ᵛ⟨_⟩_.

  conv-∙-⊩ᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B →
    Γ »∙ A ⊩ᵛ⟨ l ⟩ C →
    Γ »∙ B ⊩ᵛ⟨ l ⟩ C
  conv-∙-⊩ᵛ {Γ} {A} {B} {l} {C} A≡B ⊩C =
    case ⊩ᵛ≡⇔′ .proj₁ A≡B of λ
      (⊩A , ⊩B , A≡B) →
    ⊩ᵛ⇔ .proj₂
      ( ⊩ᵛ-∙-intro ⊩B
      , λ {_} {∇′ = ∇} {_} ξ⊇ {_} {Η = Η} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          let Δ = Γ .vars in                                  $⟨ σ₁≡σ₂ ⟩

          ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ B                            ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

          (∃ λ l →
           (∇ » Δ ⊩ᵛ⟨ l ⟩ B) ×
           ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B [ tail σ₁ ]) ×
          ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ                      →⟨ (λ ((_ , _ , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                    (_ , defn-wk-⊩ᵛ ξ⊇ ⊩A ,
                                                                     conv-⊩≡∷ (sym-⊩≡ $ A≡B ξ⊇ $ wf-⊩ˢ≡∷ σ₁₊≡σ₂₊ .proj₁) σ₁₀≡σ₂₀)
                                                                    , σ₁₊≡σ₂₊) ⟩
          (∃ λ l →
           (∇ » Δ ⊩ᵛ⟨ l ⟩ A) ×
           ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
          ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ                      ⇔˘⟨ ⊩ˢ≡∷∙⇔ ⟩→

          ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ A                            →⟨ ⊩ᵛ⇔ .proj₁ ⊩C .proj₂ ξ⊇ ⟩

          ∇ » Η ⊩⟨ l ⟩ C [ σ₁ ] ≡ C [ σ₂ ]                    □
      )

opaque

  -- Another kind of conversion for the context for _⊩ᵛ⟨_⟩_.

  conv-∙∙-⊩ᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ »∙ A₁ ⊩ᵛ⟨ l″ ⟩ B₁ ≡ B₂ →
    Γ »∙ A₁ »∙ B₁ ⊩ᵛ⟨ l ⟩ C →
    Γ »∙ A₂ »∙ B₂ ⊩ᵛ⟨ l ⟩ C
  conv-∙∙-⊩ᵛ {Γ} {A₁} {A₂} {B₁} {B₂} {l} {C} A₁≡A₂ B₁≡B₂ ⊩C =
    case sym-⊩ᵛ≡ A₁≡A₂ of λ
      A₂≡A₁ →
    case ⊩ᵛ≡⇔′ .proj₁ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂ , B₁≡B₂) →
    ⊩ᵛ⇔ .proj₂
      ( ⊩ᵛ-∙-intro (conv-∙-⊩ᵛ A₁≡A₂ ⊩B₂)
      , λ {_} {∇′ = ∇} {_} ξ⊇ {_} {Η = Η} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          let Δ = Γ .vars
              »∇ = ⊩ˢ≡∷→» σ₁≡σ₂
              A₂≡A₁ = defn-wk-⊩ᵛ≡ ξ⊇ A₂≡A₁
          in                                                   $⟨ σ₁≡σ₂ ⟩

          ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ A₂ ∙ B₂                       ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

          (∃ λ l →
           (∇ » Δ ∙ A₂ ⊩ᵛ⟨ l ⟩ B₂) ×
           ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B₂ [ tail σ₁ ]) ×
          ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ ∙ A₂                  →⟨ (λ ((_ , _ , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                     (_ , defn-wk-⊩ᵛ ξ⊇ ⊩B₁ ,
                                                                      conv-⊩≡∷
                                                                        (sym-⊩≡ $ B₁≡B₂ ξ⊇ $ conv-⊩ˢ∷-∙ A₂≡A₁ $ wf-⊩ˢ≡∷ σ₁₊≡σ₂₊ .proj₁)
                                                                        σ₁₀≡σ₂₀) ,
                                                                     conv-⊩ˢ≡∷-∙ A₂≡A₁ σ₁₊≡σ₂₊) ⟩
          (∃ λ l →
           (∇ » Δ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁) ×
           ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ B₁ [ tail σ₁ ]) ×
          ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ ∙ A₁                  ⇔˘⟨ ⊩ˢ≡∷∙⇔ ⟩→

          ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ A₁ ∙ B₁                       →⟨ ⊩ᵛ⇔ .proj₁ ⊩C .proj₂ ξ⊇ ⟩

          ∇ » Η ⊩⟨ l ⟩ C [ σ₁ ] ≡ C [ σ₂ ]                     □
      )

opaque

  -- Conversion for _⊩ᵛ⟨_⟩_≡_∷_.

  conv-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ B
  conv-⊩ᵛ≡∷ A≡B t≡u =
    case ⊩ᵛ≡⇔′ .proj₁ A≡B of λ
      (_ , ⊩B , A≡B) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩B
      , λ ξ⊇ σ₁≡σ₂ →
          conv-⊩≡∷ (A≡B ξ⊇ $ wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁) $
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t≡u) σ₁≡σ₂
      )

opaque

  -- Conversion for _⊩ᵛ⟨_⟩_∷_.

  conv-⊩ᵛ∷ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ B
  conv-⊩ᵛ∷ A≡B =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ conv-⊩ᵛ≡∷ A≡B ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

opaque

  -- Conversion for the context for _⊩ᵛ⟨_⟩_∷_.

  conv-∙-⊩ᵛ∷ :
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B →
    Γ »∙ A ⊩ᵛ⟨ l ⟩ t ∷ C →
    Γ »∙ B ⊩ᵛ⟨ l ⟩ t ∷ C
  conv-∙-⊩ᵛ∷ A≡B ⊩t =
    case ⊩ᵛ∷⇔ .proj₁ ⊩t of λ
      (⊩C , t≡t) →
    ⊩ᵛ∷⇔ .proj₂
      ( conv-∙-⊩ᵛ A≡B ⊩C
      , λ ξ⊇ σ₁≡σ₂ → t≡t ξ⊇ (conv-⊩ˢ≡∷-∙ (sym-⊩ᵛ≡ (defn-wk-⊩ᵛ≡ ξ⊇ A≡B)) σ₁≡σ₂)
      )

------------------------------------------------------------------------
-- Expansion

opaque

  -- An expansion lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷-⇐ :
    (∀ {κ′ ∇′} {ξ : DExt _ κ′ κ} → ξ » ∇′ ⊇ ∇ →
     ∀ {m Η} {σ : Subst m n}
       ⦃ inc : Var-included or-empty Η ⦄ →
     ∇′ » Η ⊩ˢ σ ∷ Δ →
     ∇′ » Η ⊢ t [ σ ] ⇒ u [ σ ] ∷ A [ σ ]) →
    ∇ » Δ ⊩ᵛ⟨ l ⟩ u ∷ A →
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A
  ⊩ᵛ∷-⇐ {t} {u} t[]⇒u[] ⊩u =
    case ⊩ᵛ∷⇔ .proj₁ ⊩u of λ
      (⊩A , u≡u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩A
      , λ ξ⊇ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
            (⊩σ₁ , _) →
          case ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ξ⊇ ⊩u) ⊩σ₁ of λ
            ⊩u[σ₁] →
          with-inc-⊩≡∷
            (t [ σ₁ ]  ≡⟨ ⊩∷-⇐* (redMany (t[]⇒u[] ξ⊇ ⊩σ₁)) ⊩u[σ₁] ⟩⊩∷
             u [ σ₁ ]  ≡⟨ u≡u ξ⊇ σ₁≡σ₂ ⟩⊩∷∎
             u [ σ₂ ]  ∎)
      )

------------------------------------------------------------------------
-- Some lemmas related to _⊩ˢ_∷_ and _⊩ˢ_≡_∷_

opaque

  -- A cast lemma for _⊩ˢ_∷_.

  cast-⊩ˢ∷ :
    ((x : Fin n) → σ₁ x PE.≡ σ₂ x) →
    ∇ » Η ⊩ˢ σ₁ ∷ Δ → ∇ » Η ⊩ˢ σ₂ ∷ Δ
  cast-⊩ˢ∷ {Δ = ε} _ ⊩σ₁ =
    ⊩ˢ∷ε⇔ .proj₂ $ ⊩ˢ∷ε⇔ .proj₁ ⊩σ₁
  cast-⊩ˢ∷ {Δ = _ ∙ A} σ₁≡σ₂ ⊩σ₁ =
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
    (⦃ inc : Var-included or-empty Φ ⦄ → ∇ » ρ ∷ʷ Φ ⊇ Η) →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Φ ⊩ˢ ρ •ₛ σ₁ ≡ ρ •ₛ σ₂ ∷ Δ
  ⊩ˢ≡∷-•ₛ {Δ = ε} ρ⊇ σ₁≡σ₂ =
    ⊩ˢ≡∷ε⇔ .proj₂ (⊩ˢ≡∷→» σ₁≡σ₂ , TW.wf-∷ʷ⊇ ρ⊇)
  ⊩ˢ≡∷-•ₛ {Δ = _ ∙ A} ρ⊇ σ₁≡σ₂ =
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((_ , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
    ⊩ˢ≡∷∙⇔ .proj₂
      ( ( _ , ⊩A
        , with-inc-⊩≡∷
            (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A)
               (wk-⊩≡∷ ρ⊇ σ₁₀≡σ₂₀))
        )
      , ⊩ˢ≡∷-•ₛ ρ⊇ σ₁₊≡σ₂₊
      )

opaque

  -- A lemma related to _•ₛ_.

  ⊩ˢ∷-•ₛ :
    (⦃ inc : Var-included or-empty Φ ⦄ → ∇ » ρ ∷ʷ Φ ⊇ Η) →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Φ ⊩ˢ ρ •ₛ σ ∷ Δ
  ⊩ˢ∷-•ₛ ρ⊇ =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-•ₛ ρ⊇ ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A lemma related to _ₛ•_.

  ⊩ˢ≡∷-ₛ• :
    ρ ∷ Η ⊇ Δ → ∇ »⊩ᵛ Δ → ∇ » Φ ⊩ˢ σ₁ ≡ σ₂ ∷ Η →
    ∇ » Φ ⊩ˢ σ₁ ₛ• ρ ≡ σ₂ ₛ• ρ ∷ Δ
  ⊩ˢ≡∷-ₛ• TW.id _ σ₁≡σ₂ =
    σ₁≡σ₂
  ⊩ˢ≡∷-ₛ• (TW.step ρ⊇) ⊩Δ σ₁≡σ₂ =
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((_ , ⊩A , head≡head) , tail≡tail) →
    ⊩ˢ≡∷-ₛ• ρ⊇ ⊩Δ tail≡tail
  ⊩ˢ≡∷-ₛ• (TW.lift {A} ρ⊇) ⊩Δ∙A σ₁≡σ₂ =
    case wf-⊩ᵛ-∙ ⊩Δ∙A of λ
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

  ⊩ˢ∷-ₛ• : ρ ∷ Η ⊇ Δ → ∇ »⊩ᵛ Δ → ∇ » Φ ⊩ˢ σ ∷ Η → ∇ » Φ ⊩ˢ σ ₛ• ρ ∷ Δ
  ⊩ˢ∷-ₛ• ρ⊇ ⊩Δ =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-ₛ• ρ⊇ ⊩Δ ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A lemma related to wk1Subst.

  ⊩ˢ≡∷-wk1Subst :
    (⦃ inc : Var-included ⦄ → ∇ » Η ⊢ A) →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ∙ A ⊩ˢ wk1Subst σ₁ ≡ wk1Subst σ₂ ∷ Δ
  ⊩ˢ≡∷-wk1Subst ⊢A =
    ⊩ˢ≡∷-•ₛ $ TW.stepʷ TW.id $ ⊢A ⦃ inc = or-empty-1+→ ⦄

opaque

  -- A lemma related to wk1Subst.

  ⊩ˢ∷-wk1Subst :
    (⦃ inc : Var-included ⦄ → ∇ » Η ⊢ A) →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ∙ A ⊩ˢ wk1Subst σ ∷ Δ
  ⊩ˢ∷-wk1Subst ⊢A =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-wk1Subst ⊢A ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A lemma related to liftSubst.

  ⊩ˢ≡∷-liftSubst :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ∙ A [ σ₁ ] ⊩ˢ liftSubst σ₁ ≡ liftSubst σ₂ ∷ Δ ∙ A
  ⊩ˢ≡∷-liftSubst {A} ⊩A σ₁≡σ₂ =
    let ⊢A[σ₁]    = λ ⦃ inc = inc ⦄ →
                      escape-⊩ ⦃ inc = included ⦄ $
                      ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁)
        σ₁⇑₊≡σ₂⇑₊ = ⊩ˢ≡∷-wk1Subst ⊢A[σ₁] σ₁≡σ₂
    in
    ⊩ˢ≡∷∙⇔ .proj₂
      ( ( _ , ⊩A
        , (with-inc-⊩≡∷ $
           refl-⊩≡∷ $
           neutral-⊩∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ wf-⊩ˢ≡∷ σ₁⇑₊≡σ₂⇑₊ .proj₁)
             (varₗ′ _) $
           ~-var $
           _⊢_∷_.var (∙ ⊢A[σ₁] ⦃ inc = or-empty-1+→ ⦄) $
           PE.subst₂ (_∷_∈_ _) (PE.sym $ wk1Subst-wk1 A) PE.refl here)
        )
      , σ₁⇑₊≡σ₂⇑₊
      )

opaque

  -- A lemma related to liftSubst.

  ⊩ˢ∷-liftSubst :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ∙ A [ σ ] ⊩ˢ liftSubst σ ∷ Δ ∙ A
  ⊩ˢ∷-liftSubst ⊩A =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-liftSubst ⊩A ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A variant of ⊩ˢ≡∷-liftSubst.

  ⊩ˢ≡∷-liftSubst′ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ∙ A₁ [ σ₁ ] ⊩ˢ liftSubst σ₁ ≡ liftSubst σ₂ ∷ Δ ∙ A₂
  ⊩ˢ≡∷-liftSubst′ {A₁} {A₂} {σ₁} A₁≡A₂ σ₁≡σ₂ =
    conv-⊩ˢ≡∷-∙ A₁≡A₂ $
    ⊩ˢ≡∷-liftSubst (wf-⊩ᵛ≡ A₁≡A₂ .proj₁) σ₁≡σ₂

opaque

  -- A variant of ⊩ˢ∷-liftSubst.

  ⊩ˢ∷-liftSubst′ :
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ∙ A₁ [ σ ] ⊩ˢ liftSubst σ ∷ Δ ∙ A₂
  ⊩ˢ∷-liftSubst′ A₁≡A₂ =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-liftSubst′ A₁≡A₂ ∘→ ⊩ˢ∷⇔⊩ˢ≡∷ .proj₁

opaque

  -- A lemma related to idSubst.

  ⊩ˢ∷-idSubst :
    ∇ »⊩ᵛ Δ →
    ∇ » Δ ⊩ˢ idSubst ∷ Δ
  ⊩ˢ∷-idSubst {Δ = ε} ⊩ε =
    let »∇ = ⊩ᵛε⇔ .proj₁ ⊩ε in ⊩ˢ∷ε⇔ .proj₂ (»∇ , ε »∇)
  ⊩ˢ∷-idSubst {Δ = _ ∙ _} ⊩Δ∙A =
    case ⊩ᵛ∙⇔ .proj₁ ⊩Δ∙A .proj₂ of λ
      ⊩A →
    PE.subst₃ _⊩ˢ_∷_ (PE.cong (_»∙_ _) $ subst-id _) PE.refl PE.refl $
    cast-⊩ˢ∷ subst-lift-id $
    ⊩ˢ∷-liftSubst (⊩ᵛ∙⇔ .proj₁ ⊩Δ∙A .proj₂)
      (⊩ˢ∷-idSubst (⊩ᵛ⇔ .proj₁ ⊩A .proj₁))

opaque

  -- A lemma related to sgSubst.

  ⊩ˢ≡∷-sgSubst :
    ∇ » Δ ⊩ᵛ⟨ l′ ⟩ A →
    ∇ » Δ ⊩⟨ l ⟩ t ≡ u ∷ A →
    ∇ » Δ ⊩ˢ sgSubst t ≡ sgSubst u ∷ Δ ∙ A
  ⊩ˢ≡∷-sgSubst ⊩A t≡u =
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( (_ , ⊩A)
      , (_ , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ subst-id _) t≡u)
      , refl-⊩ˢ≡∷ (⊩ˢ∷-idSubst (wf-⊩ᵛ ⊩A))
      )

opaque

  -- A lemma related to sgSubst.

  ⊩ˢ∷-sgSubst :
    ∇ » Δ ⊩ᵛ⟨ l′ ⟩ A →
    ∇ » Δ ⊩⟨ l ⟩ t ∷ A →
    ∇ » Δ ⊩ˢ sgSubst t ∷ Δ ∙ A
  ⊩ˢ∷-sgSubst ⊩A =
    ⊩ˢ∷⇔⊩ˢ≡∷ .proj₂ ∘→ ⊩ˢ≡∷-sgSubst ⊩A ∘→ ⊩∷⇔⊩≡∷ .proj₁

------------------------------------------------------------------------
-- Reducibility from validity

opaque

  -- If there is a valid equality between A and B, then there is a
  -- reducible equality between A and B.

  ⊩ᵛ≡→⊩≡ : Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B
  ⊩ᵛ≡→⊩≡ {Γ} {l} {A} {B} =
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B                                       ⇔⟨ ⊩ᵛ≡⇔′ ⟩→

    (Γ ⊩ᵛ⟨ l ⟩ A) ×
    (Γ ⊩ᵛ⟨ l ⟩ B) ×
    (∀ {κ′ ∇} {ξ : DExt _ κ′ _} → ξ » ∇ ⊇ Γ .defs →
     ∀ {m} {Δ : Con Term m} {σ} → ∇ » Δ ⊩ˢ σ ∷ Γ .vars →
     ∇ » Δ ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ])                      →⟨ (λ (⊩A , _ , A≡B) → A≡B id $ ⊩ˢ∷-idSubst $ wf-⊩ᵛ ⊩A) ⟩

    Γ ⊩⟨ l ⟩ A [ idSubst ] ≡ B [ idSubst ]                ≡⟨ PE.cong₂ (_⊩⟨_⟩_≡_ _ _) (subst-id _) (subst-id _) ⟩→

    Γ ⊩⟨ l ⟩ A ≡ B                                        □

opaque

  -- If A is valid, then A is reducible.

  ⊩ᵛ→⊩ : Γ ⊩ᵛ⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A
  ⊩ᵛ→⊩ = ⊩⇔⊩≡ .proj₂ ∘→ ⊩ᵛ≡→⊩≡ ∘→ ⊩ᵛ⇔⊩ᵛ≡ .proj₁

opaque

  -- If there is a valid equality between t and u, then there is a
  -- reducible equality between t and u.

  ⊩ᵛ≡∷→⊩≡∷ : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩ᵛ≡∷→⊩≡∷ {Γ} {l} {t} {u} {A} =
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A                                     ⇔⟨ ⊩ᵛ≡∷⇔′ ⟩→

    (Γ ⊩ᵛ⟨ l ⟩ t ∷ A) ×
    (Γ ⊩ᵛ⟨ l ⟩ u ∷ A) ×
    (∀ {κ′ ∇} {ξ : DExt _ κ′ _} → ξ » ∇ ⊇ Γ .defs →
     ∀ {m} {Δ : Con Term m} {σ} → ∇ » Δ ⊩ˢ σ ∷ Γ .vars →
     ∇ » Δ ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ])              →⟨ (λ (⊩t , _ , t≡u) →
                                                                  t≡u id $ ⊩ˢ∷-idSubst $ wf-⊩ᵛ $ wf-⊩ᵛ∷ ⊩t) ⟩

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
  unfolding _⊩ᵛ⟨_⟩_

  -- An escape lemma for _⊩ᵛ⟨_⟩_.

  escape-⊩ᵛ :
    ⦃ inc : Var-included or-empty (Γ .vars) ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ A → Γ ⊢ A
  escape-⊩ᵛ = escape-⊩ ∘→ ⊩ᵛ→⊩

opaque

  -- An escape lemma for ⊩ᵛ_.

  escape-⊩ᵛ′ :
    ⦃ inc : Var-included or-empty (Γ .vars) ⦄ →
    ⊩ᵛ Γ → ⊢ Γ
  escape-⊩ᵛ′ {Γ = _ » ε}     ⊩ε = ε (⊩ᵛε⇔ .proj₁ ⊩ε)
  escape-⊩ᵛ′ {Γ = _ » _ ∙ _} ⊩Γ =
    ∙ escape-⊩ᵛ ⦃ inc = or-empty-∙→ ⦄ (⊩ᵛ∙⇔ .proj₁ ⊩Γ .proj₂)

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_

  -- An escape lemma for _⊩ᵛ⟨_⟩_≡_.

  escape-⊩ᵛ≡ :
    ⦃ inc : Var-included or-empty (Γ .vars) ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ⊢ A ≅ B
  escape-⊩ᵛ≡ = escape-⊩≡ ∘→ ⊩ᵛ≡→⊩≡

opaque

  -- An escape lemma for _⊩ᵛ⟨_⟩_∷_.

  escape-⊩ᵛ∷ :
    ⦃ inc : Var-included or-empty (Γ .vars) ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ ⊢ t ∷ A
  escape-⊩ᵛ∷ = escape-⊩∷ ∘→ ⊩ᵛ∷→⊩∷

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_∷_

  -- An escape lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  escape-⊩ᵛ≡∷ :
    ⦃ inc : Var-included or-empty (Γ .vars) ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A → Γ ⊢ t ≅ u ∷ A
  escape-⊩ᵛ≡∷ = escape-⊩≡∷ ∘→ ⊩ᵛ≡∷→⊩≡∷

opaque

  -- An escape lemma for _⊩ˢ_∷_.

  escape-⊩ˢ∷ :
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ ∷ Δ → ∇ »⊢ Η × ∇ » Η ⊢ˢʷ σ ∷ Δ
  escape-⊩ˢ∷ {Η} {∇} {σ} {Δ = ε} =
    ∇ » Η ⊩ˢ σ ∷ ε                                        ⇔⟨ ⊩ˢ∷ε⇔ ⟩→
    (» ∇ × (⦃ inc : Var-included or-empty Η ⦄ → ∇ »⊢ Η))  →⟨ (λ hyp → hyp .proj₂) ⟩
    ∇ »⊢ Η                                                →⟨ (λ ⊢Η → ⊢Η , ⊢ˢʷ∷ε⇔ .proj₂ ⊢Η) ⟩
    ∇ »⊢ Η × ∇ » Η ⊢ˢʷ σ ∷ ε                              □
  escape-⊩ˢ∷ {Η} {∇} {σ} {Δ = Δ ∙ A} =
    ∇ » Η ⊩ˢ σ ∷ Δ ∙ A                                                  ⇔⟨ ⊩ˢ∷∙⇔ ⟩→

    (∃ λ l → (∇ » Δ ⊩ᵛ⟨ l ⟩ A) × ∇ » Η ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    ∇ » Η ⊩ˢ tail σ ∷ Δ                                                 →⟨ (λ ((_ , _ , ⊩σ₀) , ⊩σ₊) →
                                                                              escape-⊩∷ ⊩σ₀ , escape-⊩ˢ∷ ⊩σ₊) ⟩

    ∇ » Η ⊢ head σ ∷ A [ tail σ ] × ∇ »⊢ Η × ∇ » Η ⊢ˢʷ tail σ ∷ Δ       →⟨ (λ (⊢σ₀ , ⊢Η , ⊢σ₊) → ⊢Η , →⊢ˢʷ∷∙ ⊢σ₊ ⊢σ₀) ⟩

    ∇ »⊢ Η × ∇ » Η ⊢ˢʷ σ ∷ Δ ∙ A                                        □

opaque

  -- An escape lemma for _⊩ˢ_≡_∷_.

  escape-⊩ˢ≡∷ :
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ → ∇ »⊢ Η × ∇ » Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ
  escape-⊩ˢ≡∷ {Η} {∇} {σ₁} {σ₂} {Δ = ε} =
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ ε                                ⇔⟨ ⊩ˢ≡∷ε⇔ ⟩→
    » ∇ × (⦃ inc : Var-included or-empty Η ⦄ → ∇ »⊢ Η)  →⟨ (λ hyp → hyp .proj₂) ⟩
    ∇ »⊢ Η                                              →⟨ (λ ⊢Η → ⊢Η , ⊢ˢʷ≡∷ε⇔ .proj₂ ⊢Η) ⟩
    ∇ »⊢ Η × ∇ » Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ ε                      □
  escape-⊩ˢ≡∷ {Η} {∇} {σ₁} {σ₂} {Δ = Δ ∙ A} =
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ ∙ A                                                ⇔⟨ ⊩ˢ≡∷∙⇔ ⟩→

    (∃ λ l →
     (∇ » Δ ⊩ᵛ⟨ l ⟩ A) × ∇ » Η ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    ∇ » Η ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Δ                                          →⟨ (λ ((_ , ⊩A , σ₁₀≡σ₂₀) , σ₁₊≡σ₂₊) →
                                                                                  let ⊩σ₁₀ , ⊩σ₂₀ = wf-⊩≡∷ σ₁₀≡σ₂₀ in
                                                                                  escape-⊩∷ ⊩σ₁₀ ,
                                                                                  escape-⊩∷ (conv-⊩∷ (⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (refl-⊩ᵛ≡ ⊩A) σ₁₊≡σ₂₊) ⊩σ₂₀) ,
                                                                                  ≅ₜ-eq (escape-⊩≡∷ σ₁₀≡σ₂₀) ,
                                                                                  escape-⊩ˢ≡∷ σ₁₊≡σ₂₊) ⟩
    ∇ » Η ⊢ head σ₁ ∷ A [ tail σ₁ ] ×
    ∇ » Η ⊢ head σ₂ ∷ A [ tail σ₂ ] ×
    ∇ » Η ⊢ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ] ×
    ∇ »⊢ Η × ∇ » Η ⊢ˢʷ tail σ₁ ≡ tail σ₂ ∷ Δ                                →⟨ (λ (⊢σ₁₀ , ⊢σ₂₀ , σ₁₀≡σ₂₀ , ⊢Η , σ₁₊≡σ₂₊) →
                                                                                  ⊢Η , ⊢ˢʷ≡∷∙⇔ .proj₂ (σ₁₊≡σ₂₊ , ⊢σ₁₀ , ⊢σ₂₀ , σ₁₀≡σ₂₀)) ⟩
    ∇ »⊢ Η × ∇ » Η ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ ∙ A                                      □

------------------------------------------------------------------------
-- Embedding

opaque

  -- Embedding for _⊩ᵛ⟨_⟩_.

  emb-⊩ᵛ :
    l ≤ᵘ l′ →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ A
  emb-⊩ᵛ l≤l′ ⊩A =
    case ⊩ᵛ⇔ .proj₁ ⊩A of λ
      (⊩Γ , A≡A) →
    ⊩ᵛ⇔ .proj₂ (⊩Γ , λ ξ⊇ → emb-⊩≡ l≤l′ ∘→ A≡A ξ⊇)

opaque

  -- Embedding for _⊩ᵛ⟨_⟩_≡_.

  emb-⊩ᵛ≡ :
    l ≤ᵘ l′ →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u
  emb-⊩ᵛ≡ l≤l′ t≡u =
    let ⊩t , ⊩u = wf-⊩ᵛ≡ t≡u
    in level-⊩ᵛ≡ (emb-⊩ᵛ l≤l′ ⊩t) (emb-⊩ᵛ l≤l′ ⊩u) t≡u


opaque

  -- Embedding for _⊩ᵛ⟨_⟩_∷_.

  emb-⊩ᵛ∷ :
    l ≤ᵘ l′ →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A
  emb-⊩ᵛ∷ l≤l′ ⊩t =
    level-⊩ᵛ∷ (emb-⊩ᵛ l≤l′ (wf-⊩ᵛ∷ ⊩t)) ⊩t

opaque

  -- Embedding for _⊩ᵛ⟨_⟩_≡_∷_.

  emb-⊩ᵛ≡∷ :
    l ≤ᵘ l′ →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A
  emb-⊩ᵛ≡∷ l≤l′ t≡u∷A =
    let ⊩A = wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u∷A .proj₁)
    in level-⊩ᵛ≡∷ (emb-⊩ᵛ l≤l′ ⊩A) t≡u∷A

------------------------------------------------------------------------
-- Weakening

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_≡_.

  wk-⊩ᵛ≡ :
    ρ ∷ Η ⊇ Δ → ∇ »⊩ᵛ Η → ∇ » Δ ⊩ᵛ⟨ l ⟩ A ≡ B →
    ∇ » Η ⊩ᵛ⟨ l ⟩ wk ρ A ≡ wk ρ B
  wk-⊩ᵛ≡ {ρ} {A} {B} ρ⊇ ⊩Η A≡B =
    case ⊩ᵛ≡⇔ .proj₁ A≡B of λ
      (⊩Δ , A≡B) →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩Η
      , λ {_ _ _} ξ⊇ {_ _} {σ₁} {σ₂} σ₁≡σ₂ →
          wk ρ A [ σ₁ ]  ≡⟨ subst-wk A ⟩⊩≡
          A [ σ₁ ₛ• ρ ]  ≡⟨ A≡B ξ⊇ $ ⊩ˢ≡∷-ₛ• ρ⊇ (defn-wk-⊩ᵛ′ ξ⊇ ⊩Δ) σ₁≡σ₂ ⟩⊩∎≡
          B [ σ₂ ₛ• ρ ]  ≡˘⟨ subst-wk B ⟩
          wk ρ B [ σ₂ ]  ∎
      )

opaque

  -- Single-step weakening for _⊩ᵛ⟨_⟩_≡_.

  wk1-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l′ ⟩ C → Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ »∙ C ⊩ᵛ⟨ l ⟩ wk1 A ≡ wk1 B
  wk1-⊩ᵛ≡ ⊩C =
    wk-⊩ᵛ≡ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩C)

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_.

  wk-⊩ᵛ : ρ ∷ Η ⊇ Δ → ∇ »⊩ᵛ Η → ∇ » Δ ⊩ᵛ⟨ l ⟩ A → ∇ » Η ⊩ᵛ⟨ l ⟩ wk ρ A
  wk-⊩ᵛ ρ⊇ ⊩Η =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ ∘→ wk-⊩ᵛ≡ ρ⊇ ⊩Η ∘→ ⊩ᵛ⇔⊩ᵛ≡ .proj₁

opaque

  -- Single-step weakening for _⊩ᵛ⟨_⟩_.

  wk1-⊩ᵛ : Γ ⊩ᵛ⟨ l′ ⟩ B → Γ ⊩ᵛ⟨ l ⟩ A → Γ »∙ B ⊩ᵛ⟨ l ⟩ wk1 A
  wk1-⊩ᵛ ⊩B =
    wk-⊩ᵛ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩B)

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  wk-⊩ᵛ≡∷ :
    ρ ∷ Η ⊇ Δ → ∇ »⊩ᵛ Η → ∇ » Δ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    ∇ » Η ⊩ᵛ⟨ l ⟩ wk ρ t ≡ wk ρ u ∷ wk ρ A
  wk-⊩ᵛ≡∷ {ρ} {t} {u} {A} ρ⊇ ⊩Η t≡u =
    case wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t≡u .proj₁ of λ
      ⊩A →
    ⊩ᵛ≡∷⇔ .proj₂
      ( wk-⊩ᵛ ρ⊇ ⊩Η ⊩A
      , λ {_ _ _} ξ⊇ {_ _} {σ₁} {σ₂} σ₁≡σ₂ →
          let »∇′ = ⊩ˢ≡∷→» σ₁≡σ₂ in
          wk ρ t [ σ₁ ] ∷ wk ρ A [ σ₁ ]  ≡⟨ subst-wk t ⟩⊩∷∷≡
                                          ⟨ subst-wk A ⟩⊩∷≡
          t [ σ₁ ₛ• ρ ] ∷ A [ σ₁ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t≡u) $
                                            ⊩ˢ≡∷-ₛ• ρ⊇ (wf-⊩ᵛ (defn-wk-⊩ᵛ ξ⊇ ⊩A)) σ₁≡σ₂ ⟩⊩∷∎∷≡
          u [ σ₂ ₛ• ρ ]                  ≡˘⟨ subst-wk u ⟩
          wk ρ u [ σ₂ ]                  ∎
      )

opaque

  -- Single-step weakening for _⊩ᵛ⟨_⟩_≡_∷_.

  wk1-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l′ ⟩ B → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Γ »∙ B ⊩ᵛ⟨ l ⟩ wk1 t ≡ wk1 u ∷ wk1 A
  wk1-⊩ᵛ≡∷ ⊩B =
    wk-⊩ᵛ≡∷ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩B)

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_∷_.

  wk-⊩ᵛ∷ :
    ρ ∷ Η ⊇ Δ → ∇ »⊩ᵛ Η → ∇ » Δ ⊩ᵛ⟨ l ⟩ t ∷ A →
    ∇ » Η ⊩ᵛ⟨ l ⟩ wk ρ t ∷ wk ρ A
  wk-⊩ᵛ∷ ρ⊇ ⊩Η =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ wk-⊩ᵛ≡∷ ρ⊇ ⊩Η ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

opaque

  -- Single-step weakening for _⊩ᵛ⟨_⟩_∷_.

  wk1-⊩ᵛ∷ :
    Γ ⊩ᵛ⟨ l′ ⟩ B → Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ »∙ B ⊩ᵛ⟨ l ⟩ wk1 t ∷ wk1 A
  wk1-⊩ᵛ∷ ⊩B =
    wk-⊩ᵛ∷ (TW.step TW.id) (⊩ᵛ-∙-intro ⊩B)

------------------------------------------------------------------------
-- Substitution lemmas

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B ≡ C →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ B [ t ]₀ ≡ C [ u ]₀
  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ {B} {C} B≡C t≡u =
    case ⊩ᵛ≡∷⇔ .proj₁ t≡u of λ
      (⊩A , t≡u) →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ ⊩A
      , λ ξ⊇ σ₁≡σ₂ → let »∇′ = ⊩ˢ≡∷→» σ₁≡σ₂ in
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (substConsId B) (substConsId C) $
          ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (defn-wk-⊩ᵛ≡ ξ⊇ B≡C) $
          ⊩ˢ≡∷∙⇔ .proj₂ ((_ , defn-wk-⊩ᵛ ξ⊇ ⊩A , t≡u ξ⊇ σ₁≡σ₂) , σ₁≡σ₂)
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ B [ t ]₀
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B ⊩t =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $ ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩ᵛ≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t [ u ]₀ ∷ B [ u ]₀
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ {t} {B} ⊩t ⊩u =
    case ⊩ᵛ∷⇔ .proj₁ ⊩t of λ
      (⊩B , t≡t) →
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B ⊩u
      , λ ξ⊇ σ₁≡σ₂ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
            (substConsId t) (substConsId t) (substConsId B) $
          t≡t ξ⊇ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ (defn-wk-⊩ᵛ ξ⊇ ⊩B)
            , (_ , ⊩ᵛ∷⇔ .proj₁ ⊩u .proj₂ ξ⊇ σ₁≡σ₂)
            , σ₁≡σ₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ :
    Γ »∙ A »∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ C₁ [ t₁ , u₁ ]₁₀ ≡ C₂ [ t₂ , u₂ ]₁₀
  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ {B} {C₁} {C₂} C₁≡C₂ t₁≡t₂ u₁≡u₂ =
    case ⊩ᵛ≡⇔ .proj₁ C₁≡C₂ of λ
      (⊩Γ∙A∙B , C₁≡C₂) →
    case wf-⊩ᵛ-∙ ⊩Γ∙A∙B of λ
      (_ , ⊩B) →
    case wf-∙-⊩ᵛ ⊩B of λ
      (_ , ⊩A) →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ ⊩A
      , λ ξ⊇ σ₁≡σ₂ → let »∇′ = ⊩ˢ≡∷→» σ₁≡σ₂ in
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
            (PE.sym $ [,]-[]-fusion C₁) (PE.sym $ [,]-[]-fusion C₂) $
          C₁≡C₂ ξ⊇ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( (_ , defn-wk-⊩ᵛ ξ⊇ ⊩B)
            , ( _
              , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ substConsId B)
                  (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ u₁≡u₂) σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( (_ , defn-wk-⊩ᵛ ξ⊇ ⊩A)
                , (_ , ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t₁≡t₂) σ₁≡σ₂)
                , σ₁≡σ₂
                )
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ :
    Γ »∙ A »∙ B ⊩ᵛ⟨ l ⟩ C →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ B [ t ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ C [ t , u ]₁₀
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ ⊩C ⊩t ⊩u =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $
    ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀
      (refl-⊩ᵛ≡ ⊩C) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀∷ :
    Γ »∙ A »∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    Γ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ v₁ ≡ v₂ ∷ B [ u₁ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ t₁ [ u₁ , v₁ ]₁₀ ≡ t₂ [ u₂ , v₂ ]₁₀ ∷ C [ u₁ , v₁ ]₁₀
  ⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀∷ {B} {t₁} {t₂} {C} t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    case wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁ of λ
      ⊩C →
    case wf-∙-⊩ᵛ ⊩C of λ
      (_ , ⊩B) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀
          ⊩C (wf-⊩ᵛ≡∷ u₁≡u₂ .proj₁) (wf-⊩ᵛ≡∷ v₁≡v₂ .proj₁)
      , λ ξ⊇ σ₁≡σ₂ →
          let »∇′ = ⊩ˢ≡∷→» σ₁≡σ₂
              ⊩B = defn-wk-⊩ᵛ ξ⊇ ⊩B
          in
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ [,]-[]-fusion t₁)
            (PE.sym $ [,]-[]-fusion t₂) (PE.sym $ [,]-[]-fusion C) $
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t₁≡t₂) $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( (_ , ⊩B)
            , ( _
              , (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                   (PE.sym $ substConsId B) $
                 ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ v₁≡v₂) σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( wf-∙-⊩ᵛ ⊩B
                , (_ , ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ u₁≡u₂) σ₁≡σ₂)
                , σ₁≡σ₂
                )
            )

      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ :
    Γ »∙ A »∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l″ ⟩ v ∷ B [ u ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ t [ u , v ]₁₀ ∷ C [ u , v ]₁₀
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ ⊩t ⊩u ⊩v =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀∷
      (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u) (refl-⊩ᵛ≡∷ ⊩v)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ D ≡ E →
    Γ »∙ B »∙ C ⊩ᵛ⟨ l′ ⟩ t ∷ wk2 A →
    Γ »∙ B »∙ C ⊩ᵛ⟨ l ⟩ D [ t ]↑² ≡ E [ t ]↑²
  ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² {A} {D} {E} D≡E ⊩t =
    case ⊩ᵛ≡⇔ .proj₁ D≡E of λ
      (⊩Γ∙A , D≡E) →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
      , λ ξ⊇ σ₁≡σ₂ →
          PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (substComp↑² D _) (substComp↑² E _) $
          D≡E ξ⊇ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( wf-⊩ᵛ-∙ (defn-wk-⊩ᵛ′ ξ⊇ ⊩Γ∙A)
            , ( _
              , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk2-tail A)
                  (⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ ξ⊇ σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔ .proj₁ (⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ .proj₂) .proj₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ D →
    Γ »∙ B »∙ C ⊩ᵛ⟨ l′ ⟩ t ∷ wk2 A →
    Γ »∙ B »∙ C ⊩ᵛ⟨ l ⟩ D [ t ]↑²
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² ⊩D ⊩t =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $ ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² (refl-⊩ᵛ≡ ⊩D) ⊩t

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²∷ :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ t ≡ u ∷ D →
    Γ »∙ B »∙ C ⊩ᵛ⟨ l′ ⟩ v ∷ wk2 A →
    Γ »∙ B »∙ C ⊩ᵛ⟨ l ⟩ t [ v ]↑² ≡ u [ v ]↑² ∷ D [ v ]↑²
  ⊩ᵛ≡∷→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²∷ {A} {t} {u} {D} t≡u ⊩v =
    case wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u .proj₁) of λ
      ⊩D →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² ⊩D ⊩v
      , λ ξ⊇ σ₁≡σ₂ → let »∇′ = ⊩ˢ≡∷→» σ₁≡σ₂ in
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (substComp↑² t _) (substComp↑² u _)
            (substComp↑² D _) $
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t≡u) $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ (defn-wk-⊩ᵛ ξ⊇ ⊩D)
            , ( _
              , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk2-tail A)
                  (⊩ᵛ∷⇔ .proj₁ ⊩v .proj₂ ξ⊇ σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔ .proj₁ (⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ .proj₂) .proj₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ t ∷ D →
    Γ »∙ B »∙ C ⊩ᵛ⟨ l′ ⟩ u ∷ wk2 A →
    Γ »∙ B »∙ C ⊩ᵛ⟨ l ⟩ t [ u ]↑² ∷ D [ u ]↑²
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $ ⊩ᵛ≡∷→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²∷ (refl-⊩ᵛ≡∷ ⊩t) ⊩u

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B ≡ C →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ B [ t ]₀ ≡ C [ u ]₀
  ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ B≡C t≡u =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B≡C .proj₁) of λ
      (_ , ⊩A) →
    ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B≡C $
    ⊩ˢ≡∷-sgSubst ⊩A (level-⊩≡∷ (⊩ᵛ→⊩ ⊩A) t≡u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩[]₀ :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ B [ t ]₀
  ⊩ᵛ→⊩∷→⊩[]₀ ⊩B ⊩t =
    ⊩⇔⊩≡ .proj₂ $ ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ t ≡ u ∷ B →
    Γ ⊩⟨ l′ ⟩ v ≡ w ∷ A →
    Γ ⊩⟨ l ⟩ t [ v ]₀ ≡ u [ w ]₀ ∷ B [ v ]₀
  ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ t≡u v≡w =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u .proj₁)) of λ
      (_ , ⊩A) →
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t≡u $
    ⊩ˢ≡∷-sgSubst ⊩A (level-⊩≡∷ (⊩ᵛ→⊩ ⊩A) v≡w)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩[]₀∷ :
    Γ »∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Γ ⊩⟨ l′ ⟩ u ∷ A →
    Γ ⊩⟨ l ⟩ t [ u ]₀ ∷ B [ u ]₀
  ⊩ᵛ∷→⊩∷→⊩[]₀∷ ⊩t ⊩u =
    ⊩∷⇔⊩≡∷ .proj₂ $ ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    ∇ » Η ⊩⟨ l ⟩ B₁ [ consSubst σ₁ t₁ ] ≡ B₂ [ consSubst σ₂ t₂ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] B₁≡B₂ σ₁≡σ₂ t₁≡t₂ =
    ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
    ⊩ˢ≡∷∙⇔′ .proj₂ (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁) , (_ , t₁≡t₂) , σ₁≡σ₂)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[,] :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    ∇ » Η ⊩⟨ l ⟩ B [ consSubst σ t ]
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[,] ⊩B ⊩σ ⊩t =
    ⊩⇔⊩≡ .proj₂ $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ) (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    ∇ » Η ⊩⟨ l ⟩ t₁ [ consSubst σ₁ u₁ ] ≡ t₂ [ consSubst σ₂ u₂ ] ∷
      B [ consSubst σ₁ u₁ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ t₁≡t₂ σ₁≡σ₂ u₁≡u₂ =
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ $
    ⊩ˢ≡∷∙⇔′ .proj₂
      (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁) , (_ , u₁≡u₂) , σ₁≡σ₂)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[,]∷ :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    ∇ » Η ⊩⟨ l ⟩ t [ consSubst σ u ] ∷ B [ consSubst σ u ]
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[,]∷ ⊩t ⊩σ ⊩u =
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ∙ A [ σ₁ ] ⊩⟨ l ⟩ B₁ [ σ₁ ⇑ ] ≡ B₂ [ σ₂ ⇑ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] B₁≡B₂ σ₁≡σ₂ =
    ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
    ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁) .proj₂) σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩[⇑] :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ∙ A [ σ ] ⊩⟨ l ⟩ B [ σ ⇑ ]
  ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ =
    ⊩⇔⊩≡ .proj₂ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ∙ A [ σ₁ ] ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ] ≡ t₂ [ σ₂ ⇑ ] ∷ B [ σ₁ ⇑ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ t₁≡t₂ σ₁≡σ₂ =
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ $
    ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) .proj₂)
      σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ∙ A [ σ ] ⊩⟨ l ⟩ t [ σ ⇑ ] ∷ B [ σ ⇑ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ ⊩t ⊩σ =
    ⊩∷⇔⊩≡∷ .proj₂ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] :
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ∙ A [ σ₁ ] ∙ B [ σ₁ ⇑ ] ⊩⟨ l ⟩ C₁ [ σ₁ ⇑ ⇑ ] ≡ C₂ [ σ₂ ⇑ ⇑ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] C₁≡C₂ σ₁≡σ₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ≡ C₁≡C₂ .proj₁) of λ
      (_ , ⊩B) →
    ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] C₁≡C₂ $
    ⊩ˢ≡∷-liftSubst ⊩B $ ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ ⊩B .proj₂) σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] :
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ∙ A [ σ ] ∙ B [ σ ⇑ ] ⊩⟨ l ⟩ C [ σ ⇑ ⇑ ]
  ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] ⊩C ⊩σ =
    ⊩⇔⊩≡ .proj₂ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] (refl-⊩ᵛ≡ ⊩C) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ :
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ∙ A [ σ₁ ] ∙ B [ σ₁ ⇑ ] ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ⇑ ] ≡ t₂ [ σ₂ ⇑ ⇑ ] ∷
      C [ σ₁ ⇑ ⇑ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ t₁≡t₂ σ₁≡σ₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) of λ
      (_ , ⊩B) →
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ $
    ⊩ˢ≡∷-liftSubst ⊩B $ ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ ⊩B .proj₂) σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ :
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ∙ A [ σ ] ∙ B [ σ ⇑ ] ⊩⟨ l ⟩ t [ σ ⇑ ⇑ ] ∷ C [ σ ⇑ ⇑ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ ⊩t ⊩σ =
    ⊩∷⇔⊩≡∷ .proj₂ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    ∇ » Η ⊩⟨ l ⟩ B₁ [ σ₁ ⇑ ] [ t₁ ]₀ ≡ B₂ [ σ₂ ⇑ ] [ t₂ ]₀
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ {B₁} {B₂} B₁≡B₂ σ₁≡σ₂ t₁≡t₂ =
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ singleSubstComp _ _ B₁)
      (PE.sym $ singleSubstComp _ _ B₂) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] B₁≡B₂ σ₁≡σ₂ t₁≡t₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    ∇ » Η ⊩⟨ l ⟩ B [ σ ⇑ ] [ t ]₀
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ ⊩B ⊩σ ⊩t =
    ⊩⇔⊩≡ .proj₂ $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    ∇ » Η ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ] [ u₁ ]₀ ≡ t₂ [ σ₂ ⇑ ] [ u₂ ]₀ ∷
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
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    ∇ » Η ⊩⟨ l ⟩ t [ σ ⇑ ] [ u ]₀ ∷ B [ σ ⇑ ] [ u ]₀
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[⇑][]₀∷ ⊩t ⊩σ ⊩u =
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    ∇ » Η ⊩⟨ l′ ⟩ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ] →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ B₁ [ t₁ ]₀ [ σ₁ ] ≡ B₂ [ t₂ ]₀ [ σ₂ ]
  ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] {B₁} {B₂} B₁≡B₂ t₁[σ₁]≡t₂[σ₂] σ₁≡σ₂ =
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ singleSubstLift B₁ _)
      (PE.sym $ singleSubstLift B₂ _) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ B₁≡B₂ σ₁≡σ₂ t₁[σ₁]≡t₂[σ₂]

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩ˢ∷→⊩[]₀[] :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B →
    ∇ » Η ⊩⟨ l′ ⟩ t [ σ ] ∷ A [ σ ] →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ B [ t ]₀ [ σ ]
  ⊩ᵛ→⊩∷→⊩ˢ∷→⊩[]₀[] {t} ⊩B ⊩t[σ] ⊩σ =
    ⊩⇔⊩≡ .proj₂ $
    ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] {t₂ = t} (refl-⊩ᵛ≡ ⊩B) (refl-⊩≡∷ ⊩t[σ])
      (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    ∇ » Η ⊩⟨ l′ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ A [ σ₁ ] →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ t₁ [ u₁ ]₀ [ σ₁ ] ≡ t₂ [ u₂ ]₀ [ σ₂ ] ∷
      B [ u₁ ]₀ [ σ₁ ]
  ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ {t₁} {t₂} {B} t₁≡t₂ σ₁≡σ₂ u₁[σ₁]≡u₂[σ₂] =
    PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ singleSubstLift t₁ _)
      (PE.sym $ singleSubstLift t₂ _) (PE.sym $ singleSubstLift B _) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ t₁≡t₂ u₁[σ₁]≡u₂[σ₂] σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩ˢ∷→⊩[]₀[]∷ :
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    ∇ » Η ⊩⟨ l′ ⟩ u [ σ ] ∷ A [ σ ] →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ t [ u ]₀ [ σ ] ∷ B [ u ]₀ [ σ ]
  ⊩ᵛ∷→⊩∷→⊩ˢ∷→⊩[]₀[]∷ {u} ⊩t ⊩u[σ] ⊩σ =
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ {u₂ = u} (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩≡∷ ⊩u[σ])
      (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ :
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    ∇ » Η ⊩⟨ l″ ⟩ u₁ ≡ u₂ ∷ B [ σ₁ ⇑ ] [ t₁ ]₀ →
    ∇ » Η ⊩⟨ l ⟩ C₁ [ σ₁ ⇑ ⇑ ] [ t₁ , u₁ ]₁₀ ≡
      C₂ [ σ₂ ⇑ ⇑ ] [ t₂ , u₂ ]₁₀
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
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    ∇ » Η ⊩⟨ l″ ⟩ u ∷ B [ σ ⇑ ] [ t ]₀ →
    ∇ » Η ⊩⟨ l ⟩ C [ σ ⇑ ⇑ ] [ t , u ]₁₀
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑⇑][]₁₀ ⊩C ⊩σ ⊩t ⊩u =
    ⊩⇔⊩≡ .proj₂ $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩C) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩t) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ :
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    ∇ » Η ⊩⟨ l″ ⟩ v₁ ≡ v₂ ∷ B [ σ₁ ⇑ ] [ u₁ ]₀ →
    ∇ » Η ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ⇑ ] [ u₁ , v₁ ]₁₀ ≡ t₂ [ σ₂ ⇑ ⇑ ] [ u₂ , v₂ ]₁₀ ∷
      C [ σ₁ ⇑ ⇑ ] [ u₁ , v₁ ]₁₀
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷
    {B} {t₁} {t₂} {C} t₁≡t₂ σ₁≡σ₂ u₁≡u₂ v₁≡v₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) of λ
      (_ , ⊩B) →
    PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
      (PE.sym $ doubleSubstComp t₁ _ _ _)
      (PE.sym $ doubleSubstComp t₂ _ _ _)
      (PE.sym $ doubleSubstComp C _ _ _) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ $
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
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    ∇ » Η ⊩⟨ l″ ⟩ v ∷ B [ σ ⇑ ] [ u ]₀ →
    ∇ » Η ⊩⟨ l ⟩ t [ σ ⇑ ⇑ ] [ u , v ]₁₀ ∷ C [ σ ⇑ ⇑ ] [ u , v ]₁₀
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩∷→⊩[⇑⇑][]₁₀∷ ⊩t ⊩σ ⊩u ⊩v =
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩u) (refl-⊩≡∷ ⊩v)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[] :
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    ∇ » Η ⊩⟨ l′ ⟩ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ] →
    ∇ » Η ⊩⟨ l″ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ B [ t₁ ]₀ [ σ₁ ] →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ C₁ [ t₁ , u₁ ]₁₀ [ σ₁ ] ≡ C₂ [ t₂ , u₂ ]₁₀ [ σ₂ ]
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
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    ∇ » Η ⊩⟨ l′ ⟩ t [ σ ] ∷ A [ σ ] →
    ∇ » Η ⊩⟨ l″ ⟩ u [ σ ] ∷ B [ t ]₀ [ σ ] →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ C [ t , u ]₁₀ [ σ ]
  ⊩ᵛ→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[] {t} {u} ⊩C ⊩t[σ] ⊩u[σ] ⊩σ =
    ⊩⇔⊩≡ .proj₂ $
    ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[] {t₂ = t} {u₂ = u} (refl-⊩ᵛ≡ ⊩C)
      (refl-⊩≡∷ ⊩t[σ]) (refl-⊩≡∷ ⊩u[σ]) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷ :
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    ∇ » Η ⊩⟨ l′ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ A [ σ₁ ] →
    ∇ » Η ⊩⟨ l″ ⟩ v₁ [ σ₁ ] ≡ v₂ [ σ₂ ] ∷ B [ u₁ ]₀ [ σ₁ ] →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ t₁ [ u₁ , v₁ ]₁₀ [ σ₁ ] ≡ t₂ [ u₂ , v₂ ]₁₀ [ σ₂ ] ∷
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
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    ∇ » Η ⊩⟨ l′ ⟩ u [ σ ] ∷ A [ σ ] →
    ∇ » Η ⊩⟨ l″ ⟩ v [ σ ] ∷ B [ u ]₀ [ σ ] →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ t [ u , v ]₁₀ [ σ ] ∷ C [ u , v ]₁₀ [ σ ]
  ⊩ᵛ∷→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[]∷ {u} {v} ⊩t ⊩u[σ] ⊩v[σ] ⊩σ =
    ⊩∷⇔⊩≡∷ .proj₂ $
    ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷ {u₂ = u} {v₂ = v} (refl-⊩ᵛ≡∷ ⊩t)
      (refl-⊩≡∷ ⊩u[σ]) (refl-⊩≡∷ ⊩v[σ]) (refl-⊩ˢ≡∷ ⊩σ)
