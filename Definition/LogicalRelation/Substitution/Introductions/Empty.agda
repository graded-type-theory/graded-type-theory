------------------------------------------------------------------------
-- Validity of the empty type.
------------------------------------------------------------------------

open import Configuration-types
open import Definition.Typed.EqualityRelation
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Empty
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  {{eqrel : EqRelSet TC}}
  where

open EqRelSet {{...}}
open Type-configuration TC

open import Definition.Untyped M
open import Definition.Untyped.Whnf M TC⁻
open import Definition.Typed TC
open import Definition.Typed.Properties TC
open import Definition.LogicalRelation TC
open import Definition.LogicalRelation.Hidden TC
open import Definition.LogicalRelation.Irrelevance TC
open import Definition.LogicalRelation.Properties TC
open import Definition.LogicalRelation.ShapeView TC
open import Definition.LogicalRelation.Substitution TC
open import Definition.LogicalRelation.Substitution.Introductions.Level
  TC
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe TC
open import Definition.LogicalRelation.Unary TC

open import Tools.Function
open import Tools.Product

private variable
  Γ : Cons _ _
  A B t u : Term _
  l : Universe-level

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  --  A characterisation lemma for _⊩⟨_⟩_.

  ⊩Empty⇔ :
    Γ ⊩⟨ l ⟩ Empty ⇔ ⊢ Γ
  ⊩Empty⇔ =
      wf ∘→ escape-⊩
    , (λ ⊢Γ → Emptyᵣ (id (⊢Empty ⊢Γ)))

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Empty≡⇔ : Γ ⊩⟨ l ⟩ Empty ≡ A ⇔ Γ ⊩Empty Empty ≡ A
  ⊩Empty≡⇔ =
      (λ (⊩Empty , _ , Empty≡A) →
         case Empty-view ⊩Empty of λ {
           (Emptyᵣ _) →
         Empty≡A })
    , (λ Empty≡A →
         case id (⊢Empty (wf (subset* Empty≡A))) of λ
           Empty⇒*Empty →
         let ⊩Empty = Emptyᵣ Empty⇒*Empty in
           ⊩Empty
         , (redSubst* Empty≡A ⊩Empty) .proj₁
         , Empty≡A)

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩Empty⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Empty⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ Empty ⇔ Γ ⊩Empty t ≡ u ∷Empty
  ⊩≡∷Empty⇔ =
      (λ (⊩Empty′ , t≡u) →
        case Empty-view ⊩Empty′ of λ {
          (Emptyᵣ _) →
        t≡u })
    , λ t≡u@(Emptyₜ₌ _ _ t⇒*t′ u⇒*u′ t′≅u′ prop) →
        ⊩Empty⇔ .proj₂ (wf (subset*Term t⇒*t′)) , t≡u

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Empty⇔ :
    Γ ⊩⟨ l ⟩ t ∷ Empty ⇔ Γ ⊩Empty t ∷Empty
  ⊩∷Empty⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ t ∷ Empty      ⇔⟨ ⊩∷⇔⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ t ≡ t ∷ Empty  ⇔⟨ ⊩≡∷Empty⇔ ⟩
    Γ ⊩Empty t ≡ t ∷Empty   ⇔˘⟨ ⊩Empty∷Empty⇔⊩Empty≡∷Empty ⟩
    Γ ⊩Empty t ∷Empty       □⇔

------------------------------------------------------------------------
-- Empty

opaque

  -- Reducibility for Empty.

  ⊩Empty : ⊢ Γ → Γ ⊩⟨ l ⟩ Empty
  ⊩Empty = ⊩Empty⇔ .proj₂

opaque

  -- Validity for Empty, seen as a type former.

  Emptyᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ l ⟩ Empty
  Emptyᵛ {Γ = _ » Γ} {l} ⊩Γ =
    ⊩ᵛ⇔ʰ .proj₂
      ( ⊩Γ
      , λ {_} {∇′ = ∇} ξ⊇ {_} {Η = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          ∇ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ        →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ∇ »⊢ Δ                      ⇔˘⟨ ⊩Empty⇔ ⟩→
          (∇ » Δ ⊩⟨ l ⟩ Empty)        →⟨ refl-⊩≡ ⟩
          ∇ » Δ ⊩⟨ l ⟩ Empty ≡ Empty  □
      )

opaque

  -- Validity for Empty, seen as a term former.

  Emptyᵗᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ Empty ∷ U₀
  Emptyᵗᵛ ⊩Γ =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ⊩ᵛU (zeroᵘᵛ′ ⊩Γ)
      , λ _ σ₁≡σ₂ →
          case escape-⊩ˢ≡∷ σ₁≡σ₂ of λ
            (⊢Δ , _) →
          Type→⊩≡∷U⇔ Emptyₙ Emptyₙ .proj₂
            ( ⊩zeroᵘ ⊢Δ
            , ↑ᵘ<ᵘωᵘ·2
            , refl-⊩≡ (⊩Empty ⊢Δ)
            , ≅ₜ-Emptyrefl ⊢Δ
            )
      )
