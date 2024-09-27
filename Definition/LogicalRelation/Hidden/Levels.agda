------------------------------------------------------------------------
-- Variants of _⊩⟨_⟩_, _⊩⟨_⟩_∷_, _⊩⟨_⟩_∷_ and _⊩⟨_⟩_≡_∷_ with hidden
-- universe level arguments
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Hidden.Levels
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R as H
  using (_⊩⟨_⟩_≡_; _⊩⟨_⟩_∷_; _⊩⟨_⟩_≡_∷_)
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
import Definition.LogicalRelation.Weakening R as W

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R using (_∷_⊇_)

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE

private variable
  n                 : Nat
  Γ Δ               : Con Term _
  A B C t t₁ t₂ u v : Term _
  ρ                 : Wk _ _
  l                 : Universe-level
  k                 : LogRelKit

------------------------------------------------------------------------
-- The type formers

opaque

  -- Reducible types.

  infix 4 _⊩_

  _⊩_ : Con Term n → Term n → Set a
  Γ ⊩ A = ∃ λ l → Γ ⊩⟨ l ⟩ A

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Reducible terms.

  infix 4 _⊩_∷_

  _⊩_∷_ : Con Term n → Term n → Term n → Set a
  Γ ⊩ t ∷ A = ∃ λ l → Γ ⊩⟨ l ⟩ t ∷ A

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Reducible type equality.

  infix 4 _⊩_≡_

  _⊩_≡_ : Con Term n → Term n → Term n → Set a
  Γ ⊩ A ≡ B = ∃ λ l → Γ ⊩⟨ l ⟩ A ≡ B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Reducible term equality.

  infix 4 _⊩_≡_∷_

  _⊩_≡_∷_ : Con Term n → Term n → Term n → Term n → Set a
  Γ ⊩ t ≡ u ∷ A = ∃ λ l → Γ ⊩⟨ l ⟩ t ≡ u ∷ A

------------------------------------------------------------------------
-- Reflexivity

opaque
  unfolding _⊩_ _⊩_≡_

  -- Reflexivity for _⊩_≡_.

  refl-⊩≡ :
    Γ ⊩ A →
    Γ ⊩ A ≡ A
  refl-⊩≡ (_ , ⊩A) = _ , H.refl-⊩≡ ⊩A

opaque
  unfolding _⊩_∷_ _⊩_≡_∷_

  -- Reflexivity for _⊩_≡_∷_.

  refl-⊩≡∷ :
    Γ ⊩ t ∷ A →
    Γ ⊩ t ≡ t ∷ A
  refl-⊩≡∷ (_ , ⊩t) = _ , H.refl-⊩≡∷ ⊩t

------------------------------------------------------------------------
-- Symmetry

opaque
  unfolding _⊩_≡_

  -- Symmetry for _⊩_≡_.

  sym-⊩≡ :
    Γ ⊩ A ≡ B →
    Γ ⊩ B ≡ A
  sym-⊩≡ (_ , A≡B) = _ , H.sym-⊩≡ A≡B

opaque
  unfolding _⊩_≡_∷_

  -- Symmetry for _⊩_≡_∷_.

  sym-⊩≡∷ :
    Γ ⊩ t ≡ u ∷ A →
    Γ ⊩ u ≡ t ∷ A
  sym-⊩≡∷ (_ , t≡u) = _ , H.sym-⊩≡∷ t≡u

------------------------------------------------------------------------
-- Transitivity

opaque
  unfolding _⊩_≡_

  -- Transitivity for _⊩_≡_.

  trans-⊩≡ :
    Γ ⊩ A ≡ B →
    Γ ⊩ B ≡ C →
    Γ ⊩ A ≡ C
  trans-⊩≡ (l₁ , A≡B) (l₂ , B≡C) =
    l₁ ⊔ᵘ l₂ , H.trans-⊩≡ (H.emb-⊩≡ ≤ᵘ⊔ᵘʳ A≡B) (H.emb-⊩≡ ≤ᵘ⊔ᵘˡ B≡C)

opaque
  unfolding _⊩_≡_∷_

  -- Transitivity for _⊩_≡_∷_.

  trans-⊩≡∷ :
    Γ ⊩ t ≡ u ∷ A →
    Γ ⊩ u ≡ v ∷ A →
    Γ ⊩ t ≡ v ∷ A
  trans-⊩≡∷ (_ , t≡u) (l , u≡v) =
    l , H.trans-⊩≡∷ t≡u u≡v

------------------------------------------------------------------------
-- Well-formedness lemmas

opaque
  unfolding _⊩_ _⊩_∷_

  -- A well-formedness lemma for _⊩_∷_.

  wf-⊩∷ : Γ ⊩ t ∷ A → Γ ⊩ A
  wf-⊩∷ (_ , ⊩t) = _ , H.wf-⊩∷ ⊩t

opaque
  unfolding _⊩_ _⊩_≡_

  -- A well-formedness lemma for _⊩_≡_.

  wf-⊩≡ : Γ ⊩ A ≡ B → Γ ⊩ A × Γ ⊩ B
  wf-⊩≡ (_ , A≡B) = Σ.map (_ ,_) (_ ,_) (H.wf-⊩≡ A≡B)

opaque
  unfolding _⊩_∷_ _⊩_≡_∷_

  -- A well-formedness lemma for _⊩_≡_∷_.

  wf-⊩≡∷ :
    Γ ⊩ t ≡ u ∷ A →
    Γ ⊩ t ∷ A × Γ ⊩ u ∷ A
  wf-⊩≡∷ (_ , t≡u) = Σ.map (_ ,_) (_ ,_) (H.wf-⊩≡∷ t≡u)

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩_ _⊩_≡_

  -- A characterisation lemma for _⊩_.

  ⊩⇔⊩≡ : (Γ ⊩ A) ⇔ Γ ⊩ A ≡ A
  ⊩⇔⊩≡ = Σ-cong-⇔ λ _ → H.⊩⇔⊩≡

opaque
  unfolding _⊩_∷_ _⊩_≡_∷_

  -- A characterisation lemma for _⊩_∷_.

  ⊩∷⇔⊩≡∷ : Γ ⊩ t ∷ A ⇔ Γ ⊩ t ≡ t ∷ A
  ⊩∷⇔⊩≡∷ = Σ-cong-⇔ λ _ → H.⊩∷⇔⊩≡∷

------------------------------------------------------------------------
-- Conversion

opaque
  unfolding _⊩_≡_ _⊩_≡_∷_

  -- Conversion for _⊩_≡_∷_.

  conv-⊩≡∷ :
    Γ ⊩ A ≡ B →
    Γ ⊩ t ≡ u ∷ A →
    Γ ⊩ t ≡ u ∷ B
  conv-⊩≡∷ (_ , A≡B) (_ , t≡u) =
    _ , H.conv-⊩≡∷ A≡B t≡u

opaque
  unfolding _⊩_≡_ _⊩_∷_

  -- Conversion for _⊩_∷_.

  conv-⊩∷ :
    Γ ⊩ A ≡ B →
    Γ ⊩ t ∷ A →
    Γ ⊩ t ∷ B
  conv-⊩∷ (_ , A≡B) (_ , ⊩t) =
    _ , H.conv-⊩∷ A≡B ⊩t

------------------------------------------------------------------------
-- Weakening

opaque
  unfolding _⊩_

  -- Weakening for _⊩_.

  wk-⊩ : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩ A → Δ ⊩ wk ρ A
  wk-⊩ ρ⊇ ⊢Δ (_ , ⊩A) = _ , H.wk-⊩ ρ⊇ ⊢Δ ⊩A

opaque
  unfolding _⊩_≡_

  -- Weakening for _⊩_≡_.

  wk-⊩≡ : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩ A ≡ B → Δ ⊩ wk ρ A ≡ wk ρ B
  wk-⊩≡ Δ⊇Γ ⊢Δ (_ , A≡B) = _ , H.wk-⊩≡ Δ⊇Γ ⊢Δ A≡B

opaque
  unfolding _⊩_≡_∷_

  -- Weakening for _⊩_≡_∷_.

  wk-⊩≡∷ :
    ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩ t ≡ u ∷ A →
    Δ ⊩ wk ρ t ≡ wk ρ u ∷ wk ρ A
  wk-⊩≡∷ Δ⊇Γ ⊢Δ (_ , t≡u) = _ , H.wk-⊩≡∷ Δ⊇Γ ⊢Δ t≡u

opaque
  unfolding _⊩_∷_

  -- Weakening for _⊩_∷_.

  wk-⊩∷ : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩ t ∷ A → Δ ⊩ wk ρ t ∷ wk ρ A
  wk-⊩∷ Δ⊇Γ ⊢Δ (_ , ⊩t) = _ , H.wk-⊩∷ Δ⊇Γ ⊢Δ ⊩t

------------------------------------------------------------------------
-- Reduction

opaque
  unfolding _⊩_ _⊩_≡_

  -- A reduction lemma for _⊩_.

  ⊩-⇒* : Γ ⊢ A :⇒*: B → Γ ⊩ A → Γ ⊩ A ≡ B
  ⊩-⇒* A⇒*B (_ , ⊩A) = _ , H.⊩-⇒* A⇒*B ⊩A

opaque
  unfolding _⊩_∷_ _⊩_≡_∷_

  -- A reduction lemma for _⊩_∷_.

  ⊩∷-⇒* :
    Γ ⊢ t :⇒*: u ∷ A →
    Γ ⊩ t ∷ A →
    Γ ⊩ t ≡ u ∷ A
  ⊩∷-⇒* t⇒*u (_ , ⊩t) = _ , H.⊩∷-⇒* t⇒*u ⊩t

------------------------------------------------------------------------
-- Expansion

opaque
  unfolding _⊩_ _⊩_≡_

  -- An expansion lemma for _⊩_.

  ⊩-⇐* : Γ ⊢ A ⇒* B → Γ ⊩ B → Γ ⊩ A ≡ B
  ⊩-⇐* A⇒*B (_ , ⊩B) = _ , H.⊩-⇐* A⇒*B ⊩B

opaque
  unfolding _⊩_∷_ _⊩_≡_∷_

  -- An expansion lemma for _⊩_∷_.

  ⊩∷-⇐* :
    Γ ⊢ t ⇒* u ∷ A →
    Γ ⊩ u ∷ A →
    Γ ⊩ t ≡ u ∷ A
  ⊩∷-⇐* t⇒*u (_ , ⊩u) = _ , H.⊩∷-⇐* t⇒*u ⊩u

------------------------------------------------------------------------
-- Escape lemmas

opaque
  unfolding _⊩_

  -- An escape lemma for _⊩_.

  escape-⊩ : Γ ⊩ A → Γ ⊢ A
  escape-⊩ (_ , ⊩A) = H.escape-⊩ ⊩A

opaque
  unfolding _⊩_∷_

  -- An escape lemma for _⊩_∷_.

  escape-⊩∷ : Γ ⊩ t ∷ A → Γ ⊢ t ∷ A
  escape-⊩∷ (_ , ⊩t) = H.escape-⊩∷ ⊩t

opaque
  unfolding _⊩_≡_

  -- An escape lemma for _⊩_≡_.

  escape-⊩≡ : Γ ⊩ A ≡ B → Γ ⊢ A ≅ B
  escape-⊩≡ (_ , A≡B) = H.escape-⊩≡ A≡B

opaque
  unfolding _⊩_≡_∷_

  -- An escape lemma for _⊩_≡_∷_.

  escape-⊩≡∷ : Γ ⊩ t ≡ u ∷ A → Γ ⊢ t ≅ u ∷ A
  escape-⊩≡∷ (_ , t≡u) = H.escape-⊩≡∷ t≡u

------------------------------------------------------------------------
-- Equational reasoning combinators

-- For more explanations of the combinators, see
-- Definition.Typed.Reasoning.Reduction.Primitive.

opaque

  -- Equational reasoning combinators for _⊩_≡_.

  infix -1
    _∎⟨_⟩⊩ finally-⊩≡ finally-⊩≡˘
  infixr -2
    step-⊩≡ step-⊩≡˘ step-⊩≡≡ step-⊩≡≡˘ step-⊩≡⇒* step-⊩≡⇒ step-⊩≡⇐*
    step-⊩≡⇐ _≡⟨⟩⊩_ finally-⊩≡≡ finally-⊩≡≡˘ finally-⊩≡⇐* finally-⊩≡:⇒*:

  step-⊩≡ : ∀ A → Γ ⊩ B ≡ C → Γ ⊩ A ≡ B → Γ ⊩ A ≡ C
  step-⊩≡ _ = flip trans-⊩≡

  syntax step-⊩≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩ B≡C

  step-⊩≡˘ : ∀ A → Γ ⊩ B ≡ C → Γ ⊩ B ≡ A → Γ ⊩ A ≡ C
  step-⊩≡˘ _ B≡C B≡A = trans-⊩≡ (sym-⊩≡ B≡A) B≡C

  syntax step-⊩≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩ B≡C

  step-⊩≡≡ : ∀ A → Γ ⊩ B ≡ C → A PE.≡ B → Γ ⊩ A ≡ C
  step-⊩≡≡ _ B≡C PE.refl = B≡C

  syntax step-⊩≡≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩≡ B≡C

  step-⊩≡≡˘ : ∀ A → Γ ⊩ B ≡ C → B PE.≡ A → Γ ⊩ A ≡ C
  step-⊩≡≡˘ _ B≡C PE.refl = B≡C

  syntax step-⊩≡≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩≡ B≡C

  step-⊩≡⇒* : ∀ A → Γ ⊩ B ≡ C → Γ ⊢ A ⇒* B → Γ ⊩ A ≡ C
  step-⊩≡⇒* _ B≡C A⇒*B =
    trans-⊩≡ (⊩-⇐* A⇒*B (wf-⊩≡ B≡C .proj₁)) B≡C

  syntax step-⊩≡⇒* A B≡C A⇒*B = A ⇒*⟨ A⇒*B ⟩⊩ B≡C

  step-⊩≡⇒ : ∀ A → Γ ⊩ B ≡ C → Γ ⊢ A ⇒ B → Γ ⊩ A ≡ C
  step-⊩≡⇒ _ B≡C A⇒B =
    step-⊩≡⇒* _ B≡C (A⇒B ⇨ id (escape-⊩ (wf-⊩≡ B≡C .proj₁)))

  syntax step-⊩≡⇒ A B≡C A⇒B = A ⇒⟨ A⇒B ⟩⊩ B≡C

  step-⊩≡⇐* : ∀ A → Γ ⊩ B ≡ C → Γ ⊢ B :⇒*: A → Γ ⊩ A ≡ C
  step-⊩≡⇐* _ B≡C B⇒*A =
    trans-⊩≡ (sym-⊩≡ (⊩-⇒* B⇒*A (wf-⊩≡ B≡C .proj₁))) B≡C

  syntax step-⊩≡⇐* A B≡C B⇒*A = A ⇐*⟨ B⇒*A ⟩⊩ B≡C

  step-⊩≡⇐ : ∀ A → Γ ⊩ B ≡ C → Γ ⊢ B ⇒ A → Γ ⊢ A → Γ ⊩ A ≡ C
  step-⊩≡⇐ _ B≡C B⇒A ⊢A =
    step-⊩≡⇐* _ B≡C
      ([_,_,_] (escape-⊩ (wf-⊩≡ B≡C .proj₁)) ⊢A (B⇒A ⇨ id ⊢A))

  syntax step-⊩≡⇐ A B≡C B⇒A ⊢A = A ⇐⟨ B⇒A , ⊢A ⟩⊩ B≡C

  _≡⟨⟩⊩_ : ∀ A → Γ ⊩ A ≡ B → Γ ⊩ A ≡ B
  _ ≡⟨⟩⊩ A≡B = A≡B

  _∎⟨_⟩⊩ : ∀ A → Γ ⊩ A → Γ ⊩ A ≡ A
  _ ∎⟨ ⊩A ⟩⊩ = refl-⊩≡ ⊩A

  finally-⊩≡ : ∀ A B → Γ ⊩ A ≡ B → Γ ⊩ A ≡ B
  finally-⊩≡ _ _ A≡B = A≡B

  syntax finally-⊩≡ A B A≡B = A ≡⟨ A≡B ⟩⊩∎ B ∎

  finally-⊩≡˘ : ∀ A B → Γ ⊩ B ≡ A → Γ ⊩ A ≡ B
  finally-⊩≡˘ _ _ A≡B = sym-⊩≡ A≡B

  syntax finally-⊩≡˘ A B B≡A = A ≡˘⟨ B≡A ⟩⊩∎ B ∎

  finally-⊩≡≡ : ∀ A → B PE.≡ C → Γ ⊩ A ≡ B → Γ ⊩ A ≡ C
  finally-⊩≡≡ _ PE.refl A≡B = A≡B

  syntax finally-⊩≡≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩∎≡ B≡C

  finally-⊩≡≡˘ : ∀ A → B PE.≡ C → Γ ⊩ B ≡ A → Γ ⊩ A ≡ C
  finally-⊩≡≡˘ _ PE.refl B≡A = sym-⊩≡ B≡A

  syntax finally-⊩≡≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩∎≡ B≡C

  finally-⊩≡⇐* : ∀ A → Γ ⊢ C ⇒* B → Γ ⊩ A ≡ B → Γ ⊩ A ≡ C
  finally-⊩≡⇐* _ C⇒*B A≡B =
    trans-⊩≡ A≡B (sym-⊩≡ (⊩-⇐* C⇒*B (wf-⊩≡ A≡B .proj₂)))

  syntax finally-⊩≡⇐* A C⇒*B A≡B = A ≡⟨ A≡B ⟩⊩⇐* C⇒*B

  finally-⊩≡:⇒*: : ∀ A → Γ ⊢ B :⇒*: C → Γ ⊩ A ≡ B → Γ ⊩ A ≡ C
  finally-⊩≡:⇒*: _ B⇒*C A≡B =
    case wf-⊩≡ A≡B of λ
      (_ , ⊩B) →
    trans-⊩≡ A≡B (⊩-⇒* B⇒*C ⊩B)

  syntax finally-⊩≡:⇒*: A B⇒*C A≡B = A ≡⟨ A≡B ⟩⊩:⇒*: B⇒*C

opaque

  -- Equational reasoning combinators for _⊩_≡_∷_.

  infix -1
    _∎⟨_⟩⊩∷ finally-⊩≡∷ finally-⊩≡∷˘
  infix -2
    step-⊩≡∷-conv step-⊩≡∷-conv˘ step-⊩≡∷-conv-≡ step-⊩≡∷-conv-≡˘
  infixr -2
    step-⊩≡∷ step-⊩≡∷˘ step-⊩≡∷≡ step-⊩≡∷≡˘ step-⊩≡∷⇒* step-⊩≡∷⇒
    step-⊩≡∷⇐* step-⊩≡∷⇐ _≡⟨⟩⊩∷_ finally-⊩≡∷≡ finally-⊩≡∷≡˘
    finally-⊩≡∷⇐* finally-⊩≡∷:⇒*:

  step-⊩≡∷ : ∀ t → Γ ⊩ u ≡ v ∷ A → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷ _ = flip trans-⊩≡∷

  syntax step-⊩≡∷ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷ u≡v

  step-⊩≡∷˘ : ∀ t → Γ ⊩ u ≡ v ∷ A → Γ ⊩ u ≡ t ∷ A → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷˘ _ u≡v u≡t = trans-⊩≡∷ (sym-⊩≡∷ u≡t) u≡v

  syntax step-⊩≡∷˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷ u≡v

  step-⊩≡∷≡ : ∀ t → Γ ⊩ u ≡ v ∷ A → t PE.≡ u → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷≡ _ u≡v PE.refl = u≡v

  syntax step-⊩≡∷≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷≡ u≡v

  step-⊩≡∷≡˘ : ∀ t → Γ ⊩ u ≡ v ∷ A → u PE.≡ t → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷≡˘ _ u≡v PE.refl = u≡v

  syntax step-⊩≡∷≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷≡ u≡v

  step-⊩≡∷⇒* : ∀ t → Γ ⊩ u ≡ v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷⇒* _ u≡v t⇒*u =
    trans-⊩≡∷ (⊩∷-⇐* t⇒*u (wf-⊩≡∷ u≡v .proj₁)) u≡v

  syntax step-⊩≡∷⇒* t u≡v t⇒*u = t ⇒*⟨ t⇒*u ⟩⊩∷ u≡v

  step-⊩≡∷⇒ : ∀ t → Γ ⊩ u ≡ v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷⇒ _ u≡v t⇒u =
    step-⊩≡∷⇒* _ u≡v (t⇒u ⇨ id (escape-⊩∷ (wf-⊩≡∷ u≡v .proj₁)))

  syntax step-⊩≡∷⇒ t u≡v t⇒u = t ⇒⟨ t⇒u ⟩⊩∷ u≡v

  step-⊩≡∷⇐* : ∀ t → Γ ⊩ u ≡ v ∷ A → Γ ⊢ u :⇒*: t ∷ A → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷⇐* _ u≡v u⇒*t =
    trans-⊩≡∷ (sym-⊩≡∷ (⊩∷-⇒* u⇒*t (wf-⊩≡∷ u≡v .proj₁))) u≡v

  syntax step-⊩≡∷⇐* t u≡v u⇒*t = t ⇐*⟨ u⇒*t ⟩⊩∷ u≡v

  step-⊩≡∷⇐ :
    ∀ t → Γ ⊩ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊢ t ∷ A →
    Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷⇐ _ u≡v u⇒t ⊢t =
    step-⊩≡∷⇐* _ u≡v
      ([_,_,_] (escape-⊩∷ (wf-⊩≡∷ u≡v .proj₁)) ⊢t (u⇒t ⇨ id ⊢t))

  syntax step-⊩≡∷⇐ t u≡v u⇒t ⊢t = t ⇐⟨ u⇒t , ⊢t ⟩⊩∷ u≡v

  _≡⟨⟩⊩∷_ : ∀ t → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ u ∷ A
  _ ≡⟨⟩⊩∷ t≡u = t≡u

  step-⊩≡∷-conv : Γ ⊩ t ≡ u ∷ B → Γ ⊩ A ≡ B → Γ ⊩ t ≡ u ∷ A
  step-⊩≡∷-conv t≡u A≡B = conv-⊩≡∷ (sym-⊩≡ A≡B) t≡u

  syntax step-⊩≡∷-conv t≡u A≡B = ⟨ A≡B ⟩⊩∷ t≡u

  step-⊩≡∷-conv˘ : Γ ⊩ t ≡ u ∷ B → Γ ⊩ B ≡ A → Γ ⊩ t ≡ u ∷ A
  step-⊩≡∷-conv˘ t≡u B≡A = conv-⊩≡∷ B≡A t≡u

  syntax step-⊩≡∷-conv˘ t≡u B≡A = ˘⟨ B≡A ⟩⊩∷ t≡u

  step-⊩≡∷-conv-≡ : Γ ⊩ t ≡ u ∷ B → A PE.≡ B → Γ ⊩ t ≡ u ∷ A
  step-⊩≡∷-conv-≡ t≡u PE.refl = t≡u

  syntax step-⊩≡∷-conv-≡ t≡u A≡B = ⟨ A≡B ⟩⊩∷≡ t≡u

  step-⊩≡∷-conv-≡˘ : Γ ⊩ t ≡ u ∷ B → B PE.≡ A → Γ ⊩ t ≡ u ∷ A
  step-⊩≡∷-conv-≡˘ t≡u PE.refl = t≡u

  syntax step-⊩≡∷-conv-≡˘ t≡u B≡A = ˘⟨ B≡A ⟩⊩∷≡ t≡u

  _∎⟨_⟩⊩∷ : ∀ t → Γ ⊩ t ∷ A → Γ ⊩ t ≡ t ∷ A
  _ ∎⟨ ⊩t ⟩⊩∷ = refl-⊩≡∷ ⊩t

  finally-⊩≡∷ : ∀ t u → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ u ∷ A
  finally-⊩≡∷ _ _ t≡u = t≡u

  syntax finally-⊩≡∷ t u t≡u = t ≡⟨ t≡u ⟩⊩∷∎ u ∎

  finally-⊩≡∷˘ : ∀ t u → Γ ⊩ u ≡ t ∷ A → Γ ⊩ t ≡ u ∷ A
  finally-⊩≡∷˘ _ _ t≡u = sym-⊩≡∷ t≡u

  syntax finally-⊩≡∷˘ t u u≡t = t ≡˘⟨ u≡t ⟩⊩∷∎ u ∎

  finally-⊩≡∷≡ : ∀ t → u PE.≡ v → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ v ∷ A
  finally-⊩≡∷≡ _ PE.refl t≡u = t≡u

  syntax finally-⊩≡∷≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷∎≡ u≡v

  finally-⊩≡∷≡˘ : ∀ t → u PE.≡ v → Γ ⊩ u ≡ t ∷ A → Γ ⊩ t ≡ v ∷ A
  finally-⊩≡∷≡˘ _ PE.refl u≡t = sym-⊩≡∷ u≡t

  syntax finally-⊩≡∷≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷∎≡ u≡v

  finally-⊩≡∷⇐* : ∀ t → Γ ⊢ v ⇒* u ∷ A → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ v ∷ A
  finally-⊩≡∷⇐* _ v⇒*u t≡u =
    trans-⊩≡∷ t≡u (sym-⊩≡∷ (⊩∷-⇐* v⇒*u (wf-⊩≡∷ t≡u .proj₂)))

  syntax finally-⊩≡∷⇐* t v⇒*u t≡u = t ≡⟨ t≡u ⟩⊩∷⇐* v⇒*u

  finally-⊩≡∷:⇒*: :
    ∀ t → Γ ⊢ u :⇒*: v ∷ A → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ v ∷ A
  finally-⊩≡∷:⇒*: _ u⇒*v t≡u =
    case wf-⊩≡∷ t≡u of λ
      (_ , ⊩u) →
    trans-⊩≡∷ t≡u (⊩∷-⇒* u⇒*v ⊩u)

  syntax finally-⊩≡∷:⇒*: t u⇒*v t≡u = t ≡⟨ t≡u ⟩⊩∷:⇒*: u⇒*v

opaque

  -- Equational reasoning combinators for _⊩_≡_∷_ with explicit types.

  infix -1
    _∷_∎⟨_⟩⊩∷∷ finally-⊩≡∷∷ finally-⊩≡∷∷˘
  infix -2
    step-⊩≡∷∷-conv step-⊩≡∷∷-conv˘ step-⊩≡∷∷-conv-≡ step-⊩≡∷∷-conv-≡˘
  infixr -2
    step-⊩≡∷∷ step-⊩≡∷∷˘ step-⊩≡∷∷≡ step-⊩≡∷∷≡˘ step-⊩≡∷∷⇒* step-⊩≡∷∷⇒
    step-⊩≡∷∷⇐* step-⊩≡∷∷⇐ _∷_≡⟨⟩⊩∷∷_ finally-⊩≡∷∷≡ finally-⊩≡∷∷≡˘
    finally-⊩≡∷∷⇐* finally-⊩≡∷∷:⇒*:

  step-⊩≡∷∷ : ∀ t A → Γ ⊩ u ≡ v ∷ A → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷∷ _ _ = step-⊩≡∷ _

  syntax step-⊩≡∷∷ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷˘ : ∀ t A → Γ ⊩ u ≡ v ∷ A → Γ ⊩ u ≡ t ∷ A → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷∷˘ _ _ = step-⊩≡∷˘ _

  syntax step-⊩≡∷∷˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∷ u≡v

  step-⊩≡∷∷≡ : ∀ t A → Γ ⊩ u ≡ v ∷ A → t PE.≡ u → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷∷≡ _ _ = step-⊩≡∷≡ _

  syntax step-⊩≡∷∷≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷≡ u≡v

  step-⊩≡∷∷≡˘ : ∀ t A → Γ ⊩ u ≡ v ∷ A → u PE.≡ t → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷∷≡˘ _ _ = step-⊩≡∷≡˘ _

  syntax step-⊩≡∷∷≡˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∷≡ u≡v

  step-⊩≡∷∷⇒* : ∀ t A → Γ ⊩ u ≡ v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷∷⇒* _ _ = step-⊩≡∷⇒* _

  syntax step-⊩≡∷∷⇒* t A u≡v t⇒*u = t ∷ A ⇒*⟨ t⇒*u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇒ : ∀ t A → Γ ⊩ u ≡ v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷∷⇒ _ _ = step-⊩≡∷⇒ _

  syntax step-⊩≡∷∷⇒ t A u≡v t⇒u = t ∷ A ⇒⟨ t⇒u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇐* : ∀ t A → Γ ⊩ u ≡ v ∷ A → Γ ⊢ u :⇒*: t ∷ A → Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷∷⇐* _ _ = step-⊩≡∷⇐* _

  syntax step-⊩≡∷∷⇐* t A u≡v u⇒*t = t ∷ A ⇐*⟨ u⇒*t ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇐ :
    ∀ t A → Γ ⊩ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊢ t ∷ A →
    Γ ⊩ t ≡ v ∷ A
  step-⊩≡∷∷⇐ _ _ = step-⊩≡∷⇐ _

  syntax step-⊩≡∷∷⇐ t A u≡v u⇒t ⊢t = t ∷ A ⇐⟨ u⇒t , ⊢t ⟩⊩∷∷ u≡v

  _∷_≡⟨⟩⊩∷∷_ : ∀ t A → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ u ∷ A
  _ ∷ _ ≡⟨⟩⊩∷∷ t≡u = t≡u

  step-⊩≡∷∷-conv : ∀ A → Γ ⊩ t ≡ u ∷ B → Γ ⊩ A ≡ B → Γ ⊩ t ≡ u ∷ A
  step-⊩≡∷∷-conv _ = step-⊩≡∷-conv

  syntax step-⊩≡∷∷-conv A t≡u A≡B = ∷ A ⟨ A≡B ⟩⊩∷∷ t≡u

  step-⊩≡∷∷-conv˘ : ∀ A → Γ ⊩ t ≡ u ∷ B → Γ ⊩ B ≡ A → Γ ⊩ t ≡ u ∷ A
  step-⊩≡∷∷-conv˘ _ = step-⊩≡∷-conv˘

  syntax step-⊩≡∷∷-conv˘ A t≡u B≡A = ∷ A ˘⟨ B≡A ⟩⊩∷∷ t≡u

  step-⊩≡∷∷-conv-≡ : ∀ A → Γ ⊩ t ≡ u ∷ B → A PE.≡ B → Γ ⊩ t ≡ u ∷ A
  step-⊩≡∷∷-conv-≡ _ = step-⊩≡∷-conv-≡

  syntax step-⊩≡∷∷-conv-≡ A t≡u A≡B = ∷ A ⟨ A≡B ⟩⊩∷∷≡ t≡u

  step-⊩≡∷∷-conv-≡˘ : ∀ A → Γ ⊩ t ≡ u ∷ B → B PE.≡ A → Γ ⊩ t ≡ u ∷ A
  step-⊩≡∷∷-conv-≡˘ _ = step-⊩≡∷-conv-≡˘

  syntax step-⊩≡∷∷-conv-≡˘ A t≡u B≡A = ∷ A ˘⟨ B≡A ⟩⊩∷∷≡ t≡u

  _∷_∎⟨_⟩⊩∷∷ : ∀ t A → Γ ⊩ t ∷ A → Γ ⊩ t ≡ t ∷ A
  _ ∷ _ ∎⟨ ⊩t ⟩⊩∷∷ = refl-⊩≡∷ ⊩t

  finally-⊩≡∷∷ : ∀ t A u → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ u ∷ A
  finally-⊩≡∷∷ _ _ _ t≡u = t≡u

  syntax finally-⊩≡∷∷ t A u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∎∷ u ∎

  finally-⊩≡∷∷˘ : ∀ t A u → Γ ⊩ u ≡ t ∷ A → Γ ⊩ t ≡ u ∷ A
  finally-⊩≡∷∷˘ _ _ _ t≡u = sym-⊩≡∷ t≡u

  syntax finally-⊩≡∷∷˘ t A u u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∎∷ u ∎

  finally-⊩≡∷∷≡ : ∀ t A → u PE.≡ v → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ v ∷ A
  finally-⊩≡∷∷≡ _ _ = finally-⊩≡∷≡ _

  syntax finally-⊩≡∷∷≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∎∷≡ u≡v

  finally-⊩≡∷∷≡˘ : ∀ t A → u PE.≡ v → Γ ⊩ u ≡ t ∷ A → Γ ⊩ t ≡ v ∷ A
  finally-⊩≡∷∷≡˘ _ _ = finally-⊩≡∷≡˘ _

  syntax finally-⊩≡∷∷≡˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∎∷≡ u≡v

  finally-⊩≡∷∷⇐* :
    ∀ t A → Γ ⊢ v ⇒* u ∷ A → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ v ∷ A
  finally-⊩≡∷∷⇐* _ _ = finally-⊩≡∷⇐* _

  syntax finally-⊩≡∷∷⇐* t A v⇒*u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷⇐* v⇒*u

  finally-⊩≡∷∷:⇒*: :
    ∀ t A → Γ ⊢ u :⇒*: v ∷ A → Γ ⊩ t ≡ u ∷ A → Γ ⊩ t ≡ v ∷ A
  finally-⊩≡∷∷:⇒*: _ _ = finally-⊩≡∷:⇒*: _

  syntax finally-⊩≡∷∷:⇒*: t A v⇒*u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷:⇒*: v⇒*u

------------------------------------------------------------------------
-- Some introduction lemmas

opaque
  unfolding _⊩_

  -- An introduction lemma for _⊩_.

  ⊩-intro :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩ A
  ⊩-intro = _ ,_

opaque
  unfolding _⊩_∷_

  -- An introduction lemma for _⊩_∷_.

  ⊩∷-intro :
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩ t ∷ A
  ⊩∷-intro = _ ,_

opaque
  unfolding _⊩_≡_

  -- An introduction lemma for _⊩_≡_.

  ⊩≡-intro :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩ A ≡ B
  ⊩≡-intro = _ ,_

opaque
  unfolding _⊩_≡_∷_

  -- An introduction lemma for _⊩_≡_∷_.

  ⊩≡∷-intro :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩ t ≡ u ∷ A
  ⊩≡∷-intro = _ ,_

------------------------------------------------------------------------
-- Neutral types and terms

opaque
  unfolding _⊩_

  -- Neutral types that satisfy certain properties are reducible.

  neutral-⊩ :
    Neutral A →
    Γ ⊢ A →
    Γ ⊢ A ≅ A →
    Γ ⊩ A
  neutral-⊩ A-ne ⊢A A≅A = 0 , H.neutral-⊩ A-ne ⊢A A≅A

opaque
  unfolding _⊩_ _⊩_∷_

  -- Neutral terms that satisfy certain properties are reducible.

  neutral-⊩∷ :
    Γ ⊩ A →
    Neutral t →
    Γ ⊢ t ∷ A →
    Γ ⊢ t ~ t ∷ A →
    Γ ⊩ t ∷ A
  neutral-⊩∷ (_ , ⊩A) t-ne ⊢t t~t = _ , H.neutral-⊩∷ ⊩A t-ne ⊢t t~t

opaque
  unfolding _⊩_ _⊩_≡_

  -- Reducible equality holds between neutral types that satisfy
  -- certain properties.

  neutral-⊩≡ :
    Γ ⊩ A →
    Γ ⊩ B →
    Neutral A →
    Neutral B →
    Γ ⊢ A ≅ B →
    Γ ⊩ A ≡ B
  neutral-⊩≡ (l₁ , ⊩A) (l₂ , ⊩B) A-ne B-ne A≅B =
      l₁ ⊔ᵘ l₂
    , H.neutral-⊩≡ (emb-≤-⊩ ≤ᵘ⊔ᵘʳ ⊩A) (emb-≤-⊩ ≤ᵘ⊔ᵘˡ ⊩B) A-ne B-ne A≅B

opaque
  unfolding _⊩_ _⊩_≡_∷_

  -- Reducible equality holds between neutral terms that satisfy
  -- certain properties.

  neutral-⊩≡∷ :
    Γ ⊩ A →
    Neutral t →
    Neutral u →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ A →
    Γ ⊢ t ~ u ∷ A →
    Γ ⊩ t ≡ u ∷ A
  neutral-⊩≡∷ (_ , ⊩A) t-ne u-ne ⊢t ⊢u t~u =
    _ , H.neutral-⊩≡∷ ⊩A t-ne u-ne ⊢t ⊢u t~u

opaque
  unfolding _⊩_

  -- A characterisation lemma for _⊩_.

  ⊩ne⇔ :
    Neutral A →
    Γ ⊩ A ⇔ ((Γ ⊢ A) × Γ ⊢ A ≅ A)
  ⊩ne⇔ {A} {Γ} A-ne =
    Γ ⊩ A                                 ⇔⟨ id⇔ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ A)                  ⇔⟨ (Σ-cong-⇔ λ _ → H.⊩ne⇔ A-ne) ⟩
    Universe-level × (Γ ⊢ A) × Γ ⊢ A ≅ A  ⇔⟨ proj₂ , (0 ,_) ⟩
    (Γ ⊢ A) × Γ ⊢ A ≅ A                   □⇔

opaque
  unfolding _⊩_ _⊩_∷_

  -- A characterisation lemma for _⊩_∷_.

  ⊩∷ne⇔ :
    Neutral A →
    Γ ⊩ t ∷ A ⇔
    (Γ ⊩ A × ∃ λ u → Γ ⊢ t :⇒*: u ∷ A × Neutral u × Γ ⊢ u ~ u ∷ A)
  ⊩∷ne⇔ {A} {Γ} {t} A-ne =
    Γ ⊩ t ∷ A                                                       ⇔⟨ id⇔ ⟩

    (∃ λ l → Γ ⊩⟨ l ⟩ t ∷ A)                                        ⇔⟨ (Σ-cong-⇔ λ _ → H.⊩∷ne⇔ A-ne) ⟩

    (∃ λ l → Γ ⊩⟨ l ⟩ A × ∃ λ u → Γ ⊢ t :⇒*: u ∷ A × Neutral u ×
     Γ ⊢ u ~ u ∷ A)                                                 ⇔⟨ (λ (l , ⊩A , rest) → (l , ⊩A) , rest)
                                                                     , (λ ((l , ⊩A) , rest) → l , ⊩A , rest)
                                                                     ⟩

    (Γ ⊩ A × ∃ λ u → Γ ⊢ t :⇒*: u ∷ A × Neutral u × Γ ⊢ u ~ u ∷ A)  □⇔

opaque
  unfolding _⊩_≡_

  -- A characterisation lemma for _⊩_≡_.

  ⊩ne≡⇔ :
    Neutral A →
    Γ ⊩ A ≡ B ⇔
    (Γ ⊢ A × ∃ λ C → Neutral C × (Γ ⊢ C) × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C)
  ⊩ne≡⇔ {A} {Γ} {B} A-ne =
    Γ ⊩ A ≡ B                                                       ⇔⟨ id⇔ ⟩

    (∃ λ l → Γ ⊩⟨ l ⟩ A ≡ B)                                        ⇔⟨ (Σ-cong-⇔ λ _ → H.⊩ne≡⇔ A-ne) ⟩

    Universe-level ×
    (Γ ⊢ A × ∃ λ C → Neutral C × (Γ ⊢ C) × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C)  ⇔⟨ proj₂ , (0 ,_) ⟩

    (Γ ⊢ A × ∃ λ C → Neutral C × (Γ ⊢ C) × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C)  □⇔

opaque
  unfolding _⊩_≡_

  -- A characterisation lemma for _⊩_≡_.

  ⊩ne≡ne⇔ :
    Neutral A →
    Neutral B →
    Γ ⊩ A ≡ B ⇔ ((Γ ⊢ A) × (Γ ⊢ B) × Γ ⊢ A ≅ B)
  ⊩ne≡ne⇔ {A} {B} {Γ} A-ne B-ne =
    Γ ⊩ A ≡ B                                       ⇔⟨ id⇔ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ A ≡ B)                        ⇔⟨ (Σ-cong-⇔ λ _ → H.⊩ne≡ne⇔ A-ne B-ne) ⟩
    Universe-level × (Γ ⊢ A) × (Γ ⊢ B) × Γ ⊢ A ≅ B  ⇔⟨ proj₂ , (0 ,_) ⟩
    (Γ ⊢ A) × (Γ ⊢ B) × Γ ⊢ A ≅ B                   □⇔

opaque
  unfolding _⊩_≡_∷_ ⊩ne⇔

  -- A characterisation lemma for _⊩_≡_∷_.

  ⊩≡∷ne⇔ :
    Neutral A →
    Γ ⊩ t₁ ≡ t₂ ∷ A ⇔
    (Γ ⊩ A ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t₁ :⇒*: u₁ ∷ A × Γ ⊢ t₂ :⇒*: u₂ ∷ A ×
     Γ ⊩neNf u₁ ≡ u₂ ∷ A)
  ⊩≡∷ne⇔ {A} {Γ} {t₁} {t₂} A-ne =
    Γ ⊩ t₁ ≡ t₂ ∷ A                             ⇔⟨ id⇔ ⟩

    (∃ λ l → Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A)              ⇔⟨ (Σ-cong-⇔ λ _ → H.⊩≡∷ne⇔ A-ne) ⟩

    (∃ λ l → Γ ⊩⟨ l ⟩ A ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t₁ :⇒*: u₁ ∷ A × Γ ⊢ t₂ :⇒*: u₂ ∷ A ×
     Γ ⊩neNf u₁ ≡ u₂ ∷ A)                       ⇔⟨ (λ (l , ⊩A , rest) → (l , ⊩A) , rest)
                                                 , (λ ((l , ⊩A) , rest) → l , ⊩A , rest)
                                                 ⟩
    (Γ ⊩ A ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t₁ :⇒*: u₁ ∷ A × Γ ⊢ t₂ :⇒*: u₂ ∷ A ×
     Γ ⊩neNf u₁ ≡ u₂ ∷ A)                       □⇔
