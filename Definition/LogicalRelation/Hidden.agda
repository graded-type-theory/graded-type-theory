------------------------------------------------------------------------
-- A variant of the logical relation with hidden reducibility
-- arguments, along with variants of some other relations
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Hidden
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R
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
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  n                 : Nat
  Γ Δ               : Con Term _
  A B C t t₁ t₂ u v : Term _
  ρ                 : Wk _ _
  l l′              : Universe-level
  k                 : LogRelKit

------------------------------------------------------------------------
-- The type formers

opaque

  -- Reducible terms.

  infix 4 _⊩⟨_⟩_∷_

  _⊩⟨_⟩_∷_ : Con Term n → Universe-level → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ t ∷ A =
    ∃ λ (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / ⊩A

opaque

  -- Reducible type equality.

  infix 4 _⊩⟨_⟩_≡_

  _⊩⟨_⟩_≡_ : Con Term n → Universe-level → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ A ≡ B =
    ∃ λ (⊩A : Γ ⊩⟨ l ⟩ A) → (Γ ⊩⟨ l ⟩ B) × Γ ⊩⟨ l ⟩ A ≡ B / ⊩A

opaque

  -- Reducible term equality.

  infix 4 _⊩⟨_⟩_≡_∷_

  _⊩⟨_⟩_≡_∷_ :
    Con Term n → Universe-level → Term n → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A =
    ∃ λ (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A ×
    Γ ⊩⟨ l ⟩ u ∷ A / ⊩A ×
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A

------------------------------------------------------------------------
-- Conversions to the underlying type formers

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A conversion to _⊩⟨_⟩_∷_/_.

  ⊩∷→⊩∷/ : (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l′ ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ∷ A / ⊩A
  ⊩∷→⊩∷/ ⊩A (⊩A′ , ⊩t) = irrelevanceTerm ⊩A′ ⊩A ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A conversion to _⊩⟨_⟩_≡_/_.

  ⊩≡→⊩≡/ : (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l′ ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B / ⊩A
  ⊩≡→⊩≡/ ⊩A (⊩A′ , _ , A≡B) = irrelevanceEq ⊩A′ ⊩A A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A conversion to _⊩⟨_⟩_≡_∷_/_.

  ⊩≡∷→⊩≡∷/ :
    (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A
  ⊩≡∷→⊩≡∷/ ⊩A (⊩A′ , _ , _ , t≡u) = irrelevanceEqTerm ⊩A′ ⊩A t≡u

------------------------------------------------------------------------
-- Reflexivity

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Reflexivity for _⊩⟨_⟩_≡_.

  refl-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ A ≡ A
  refl-⊩≡ ⊩A =
    ⊩A , ⊩A , reflEq ⊩A

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- Reflexivity for _⊩⟨_⟩_≡_∷_.

  refl-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  refl-⊩≡∷ (⊩A , ⊩t) =
    ⊩A , ⊩t , ⊩t , reflEqTerm ⊩A ⊩t

------------------------------------------------------------------------
-- Symmetry

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Symmetry for _⊩⟨_⟩_≡_.

  sym-⊩≡ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ B ≡ A
  sym-⊩≡ (⊩A , ⊩B , A≡B) =
    ⊩B , ⊩A , symEq ⊩A ⊩B A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Symmetry for _⊩⟨_⟩_≡_∷_.

  sym-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ u ≡ t ∷ A
  sym-⊩≡∷ (⊩A , ⊩t , ⊩u , t≡u) =
    ⊩A , ⊩u , ⊩t , symEqTerm ⊩A t≡u

------------------------------------------------------------------------
-- Transitivity

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Transitivity for _⊩⟨_⟩_≡_.

  trans-⊩≡ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ B ≡ C →
    Γ ⊩⟨ l ⟩ A ≡ C
  trans-⊩≡ (⊩A , _ , A≡B) (⊩B , ⊩C , B≡C) =
    ⊩A , ⊩C , transEq ⊩A ⊩B ⊩C A≡B B≡C

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Transitivity for _⊩⟨_⟩_≡_∷_.

  trans-⊩≡∷ :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ u ≡ v ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  trans-⊩≡∷ (⊩A′ , ⊩t , _ , t≡u) (⊩A , _ , ⊩v , u≡v) =
      ⊩A , irrelevanceTerm ⊩A′ ⊩A ⊩t , ⊩v
    , transEqTerm ⊩A (irrelevanceEqTerm ⊩A′ ⊩A t≡u) u≡v

------------------------------------------------------------------------
-- Well-formedness lemmas

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A well-formedness lemma for _⊩⟨_⟩_∷_.

  wf-⊩∷ : Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ A
  wf-⊩∷ (⊩A , _) = ⊩A

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A well-formedness lemma for _⊩⟨_⟩_≡_.

  wf-⊩≡ : Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A × Γ ⊩⟨ l ⟩ B
  wf-⊩≡ (⊩A , ⊩B , _) = ⊩A , ⊩B

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A well-formedness lemma for _⊩⟨_⟩_≡_∷_.

  wf-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A × Γ ⊩⟨ l ⟩ u ∷ A
  wf-⊩≡∷ (⊩A , ⊩t , ⊩u , _) = (⊩A , ⊩t) , (⊩A , ⊩u)

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩⇔⊩≡ : (Γ ⊩⟨ l ⟩ A) ⇔ Γ ⊩⟨ l ⟩ A ≡ A
  ⊩⇔⊩≡ = refl-⊩≡ , proj₁ ∘→ wf-⊩≡

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷⇔⊩≡∷ : Γ ⊩⟨ l ⟩ t ∷ A ⇔ Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  ⊩∷⇔⊩≡∷ = refl-⊩≡∷ , proj₁ ∘→ wf-⊩≡∷

------------------------------------------------------------------------
-- Changing type levels

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Changing type levels for _⊩⟨_⟩_≡_.

  level-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ B →
    Γ ⊩⟨ l′ ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ A ≡ B
  level-⊩≡ ⊩A ⊩B A≡B =
    ⊩A , ⊩B , ⊩≡→⊩≡/ ⊩A A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Changing type levels for _⊩⟨_⟩_≡_∷_.

  level-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  level-⊩≡∷ ⊩A t≡u =
    case wf-⊩≡∷ t≡u of λ
      (⊩t , ⊩u) →
    ⊩A , ⊩∷→⊩∷/ ⊩A ⊩t , ⊩∷→⊩∷/ ⊩A ⊩u , ⊩≡∷→⊩≡∷/ ⊩A t≡u

opaque

  -- Changing type levels for _⊩⟨_⟩_∷_.

  level-⊩∷ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A
  level-⊩∷ ⊩A =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ level-⊩≡∷ ⊩A ∘→ ⊩∷⇔⊩≡∷ .proj₁

------------------------------------------------------------------------
-- Conversion

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- Conversion for _⊩⟨_⟩_≡_∷_.

  conv-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ B
  conv-⊩≡∷ (⊩A , ⊩B , A≡B) (⊩A′ , ⊩t , ⊩u , t≡u) =
    case irrelevanceEq ⊩A ⊩A′ A≡B of λ
      A≡B →
      ⊩B , convTerm₁ ⊩A′ ⊩B A≡B ⊩t , convTerm₁ ⊩A′ ⊩B A≡B ⊩u
    , convEqTerm₁ ⊩A′ ⊩B A≡B t≡u

opaque

  -- Conversion for _⊩⟨_⟩_∷_.

  conv-⊩∷ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ B
  conv-⊩∷ A≡B =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ conv-⊩≡∷ A≡B ∘→ ⊩∷⇔⊩≡∷ .proj₁

------------------------------------------------------------------------
-- Weakening

opaque

  -- Weakening for _⊩⟨_⟩_.

  wk-⊩ : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ l ⟩ wk ρ A
  wk-⊩ = W.wk

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Weakening for _⊩⟨_⟩_≡_.

  wk-⊩≡ : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩⟨ l ⟩ A ≡ B → Δ ⊩⟨ l ⟩ wk ρ A ≡ wk ρ B
  wk-⊩≡ Δ⊇Γ ⊢Δ (⊩A , ⊩B , A≡B) =
    W.wk Δ⊇Γ ⊢Δ ⊩A , W.wk Δ⊇Γ ⊢Δ ⊩B , W.wkEq Δ⊇Γ ⊢Δ ⊩A A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Weakening for _⊩⟨_⟩_≡_∷_.

  wk-⊩≡∷ :
    ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Δ ⊩⟨ l ⟩ wk ρ t ≡ wk ρ u ∷ wk ρ A
  wk-⊩≡∷ Δ⊇Γ ⊢Δ (⊩A , ⊩t , ⊩u , t≡u) =
      W.wk Δ⊇Γ ⊢Δ ⊩A , W.wkTerm Δ⊇Γ ⊢Δ ⊩A ⊩t , W.wkTerm Δ⊇Γ ⊢Δ ⊩A ⊩u
    , W.wkEqTerm Δ⊇Γ ⊢Δ ⊩A t≡u

opaque

  -- Weakening for _⊩⟨_⟩_∷_.

  wk-⊩∷ : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩⟨ l ⟩ t ∷ A → Δ ⊩⟨ l ⟩ wk ρ t ∷ wk ρ A
  wk-⊩∷ Δ⊇Γ ⊢Δ =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ wk-⊩≡∷ Δ⊇Γ ⊢Δ ∘→ ⊩∷⇔⊩≡∷ .proj₁

------------------------------------------------------------------------
-- Reduction

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A reduction lemma for _⊩⟨_⟩_.

  ⊩-⇒* : Γ ⊢ A :⇒*: B → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A ≡ B
  ⊩-⇒* A⇒*B ⊩A = ⊩A , redSubst*′ A⇒*B ⊩A

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A reduction lemma for _⊩⟨_⟩_∷_.

  ⊩∷-⇒* :
    Γ ⊢ t :⇒*: u ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩∷-⇒* t⇒*u (⊩A , ⊩t) =
    ⊩A , ⊩t , redSubst*Term′ t⇒*u ⊩A ⊩t

------------------------------------------------------------------------
-- Expansion

opaque
  unfolding _⊩⟨_⟩_≡_

  -- An expansion lemma for _⊩⟨_⟩_.

  ⊩-⇐* : Γ ⊢ A ⇒* B → Γ ⊩⟨ l ⟩ B → Γ ⊩⟨ l ⟩ A ≡ B
  ⊩-⇐* A⇒*B ⊩B =
    case redSubst* A⇒*B ⊩B of λ
      (⊩A , A≡B) →
    ⊩A , ⊩B , A≡B

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- An expansion lemma for _⊩⟨_⟩_∷_.

  ⊩∷-⇐* :
    Γ ⊢ t ⇒* u ∷ A →
    Γ ⊩⟨ l ⟩ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩∷-⇐* t⇒*u (⊩A , ⊩u) =
    case redSubst*Term t⇒*u ⊩A ⊩u of λ
      (⊩t , t≡u) →
    ⊩A , ⊩t , ⊩u , t≡u

------------------------------------------------------------------------
-- Escape lemmas

opaque

  -- An escape lemma for _⊩⟨_⟩_.

  escape-⊩ : Γ ⊩⟨ l ⟩ A → Γ ⊢ A
  escape-⊩ = escape

opaque
  unfolding _⊩⟨_⟩_∷_

  -- An escape lemma for _⊩⟨_⟩_∷_.

  escape-⊩∷ : Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊢ t ∷ A
  escape-⊩∷ (⊩A , ⊩t) = escapeTerm ⊩A ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- An escape lemma for _⊩⟨_⟩_≡_.

  escape-⊩≡ : Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊢ A ≅ B
  escape-⊩≡ (⊩A , _ , A≡B) = escapeEq ⊩A A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- An escape lemma for _⊩⟨_⟩_≡_∷_.

  escape-⊩≡∷ : Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊢ t ≅ u ∷ A
  escape-⊩≡∷ (⊩A , _ , _ , t≡u) = escapeTermEq ⊩A t≡u

------------------------------------------------------------------------
-- Equational reasoning combinators

-- For more explanations of the combinators, see
-- Definition.Typed.Reasoning.Reduction.Primitive.

opaque

  -- Equational reasoning combinators for _⊩⟨_⟩_≡_.

  infix -1
    _∎⟨_⟩⊩ finally-⊩≡ finally-⊩≡˘
  infixr -2
    step-⊩≡ step-⊩≡˘ step-⊩≡≡ step-⊩≡≡˘ step-⊩≡⇒* step-⊩≡⇒ step-⊩≡⇐*
    step-⊩≡⇐ _≡⟨⟩⊩_ finally-⊩≡≡ finally-⊩≡≡˘ finally-⊩≡⇐* finally-⊩≡:⇒*:

  step-⊩≡ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡ _ = flip trans-⊩≡

  syntax step-⊩≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩ B≡C

  step-⊩≡˘ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡˘ _ B≡C B≡A = trans-⊩≡ (sym-⊩≡ B≡A) B≡C

  syntax step-⊩≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩ B≡C

  step-⊩≡≡ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → A PE.≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡≡ _ B≡C PE.refl = B≡C

  syntax step-⊩≡≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩≡ B≡C

  step-⊩≡≡˘ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → B PE.≡ A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡≡˘ _ B≡C PE.refl = B≡C

  syntax step-⊩≡≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩≡ B≡C

  step-⊩≡⇒* : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ A ⇒* B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇒* _ B≡C A⇒*B =
    trans-⊩≡ (⊩-⇐* A⇒*B (wf-⊩≡ B≡C .proj₁)) B≡C

  syntax step-⊩≡⇒* A B≡C A⇒*B = A ⇒*⟨ A⇒*B ⟩⊩ B≡C

  step-⊩≡⇒ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ A ⇒ B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇒ _ B≡C A⇒B =
    step-⊩≡⇒* _ B≡C (A⇒B ⇨ id (escape (wf-⊩≡ B≡C .proj₁)))

  syntax step-⊩≡⇒ A B≡C A⇒B = A ⇒⟨ A⇒B ⟩⊩ B≡C

  step-⊩≡⇐* : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ B :⇒*: A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇐* _ B≡C B⇒*A =
    trans-⊩≡ (sym-⊩≡ (⊩-⇒* B⇒*A (wf-⊩≡ B≡C .proj₁))) B≡C

  syntax step-⊩≡⇐* A B≡C B⇒*A = A ⇐*⟨ B⇒*A ⟩⊩ B≡C

  step-⊩≡⇐ :
    ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ B ⇒ A → Γ ⊢ A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇐ _ B≡C B⇒A ⊢A =
    step-⊩≡⇐* _ B≡C
      ([_,_,_] (escape (wf-⊩≡ B≡C .proj₁)) ⊢A (B⇒A ⇨ id ⊢A))

  syntax step-⊩≡⇐ A B≡C B⇒A ⊢A = A ⇐⟨ B⇒A , ⊢A ⟩⊩ B≡C

  _≡⟨⟩⊩_ : ∀ A → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B
  _ ≡⟨⟩⊩ A≡B = A≡B

  _∎⟨_⟩⊩ : ∀ A → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A ≡ A
  _ ∎⟨ ⊩A ⟩⊩ = refl-⊩≡ ⊩A

  finally-⊩≡ : ∀ A B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B
  finally-⊩≡ _ _ A≡B = A≡B

  syntax finally-⊩≡ A B A≡B = A ≡⟨ A≡B ⟩⊩∎ B ∎

  finally-⊩≡˘ : ∀ A B → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ A ≡ B
  finally-⊩≡˘ _ _ A≡B = sym-⊩≡ A≡B

  syntax finally-⊩≡˘ A B B≡A = A ≡˘⟨ B≡A ⟩⊩∎ B ∎

  finally-⊩≡≡ : ∀ A → B PE.≡ C → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡≡ _ PE.refl A≡B = A≡B

  syntax finally-⊩≡≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩∎≡ B≡C

  finally-⊩≡≡˘ : ∀ A → B PE.≡ C → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡≡˘ _ PE.refl B≡A = sym-⊩≡ B≡A

  syntax finally-⊩≡≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩∎≡ B≡C

  finally-⊩≡⇐* :
    ∀ A → Γ ⊢ C ⇒* B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡⇐* _ C⇒*B A≡B =
    trans-⊩≡ A≡B (sym-⊩≡ (⊩-⇐* C⇒*B (wf-⊩≡ A≡B .proj₂)))

  syntax finally-⊩≡⇐* A C⇒*B A≡B = A ≡⟨ A≡B ⟩⊩⇐* C⇒*B

  finally-⊩≡:⇒*: :
    ∀ A → Γ ⊢ B :⇒*: C → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡:⇒*: _ B⇒*C A≡B =
    case wf-⊩≡ A≡B of λ
      (_ , ⊩B) →
    trans-⊩≡ A≡B (⊩-⇒* B⇒*C ⊩B)

  syntax finally-⊩≡:⇒*: A B⇒*C A≡B = A ≡⟨ A≡B ⟩⊩:⇒*: B⇒*C

opaque

  -- Equational reasoning combinators for _⊩⟨_⟩_≡_∷_.

  infix -1
    _∎⟨_⟩⊩∷ finally-⊩≡∷ finally-⊩≡∷˘
  infix -2
    step-⊩≡∷-conv step-⊩≡∷-conv˘ step-⊩≡∷-conv-≡ step-⊩≡∷-conv-≡˘
  infixr -2
    step-⊩≡∷ step-⊩≡∷˘ step-⊩≡∷≡ step-⊩≡∷≡˘ step-⊩≡∷⇒* step-⊩≡∷⇒
    step-⊩≡∷⇐* step-⊩≡∷⇐ _≡⟨⟩⊩∷_ finally-⊩≡∷≡ finally-⊩≡∷≡˘
    finally-⊩≡∷⇐* finally-⊩≡∷:⇒*:

  step-⊩≡∷ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷ _ = flip trans-⊩≡∷

  syntax step-⊩≡∷ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷ u≡v

  step-⊩≡∷˘ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷˘ _ u≡v u≡t = trans-⊩≡∷ (sym-⊩≡∷ u≡t) u≡v

  syntax step-⊩≡∷˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷ u≡v

  step-⊩≡∷≡ : ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → t PE.≡ u → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷≡ _ u≡v PE.refl = u≡v

  syntax step-⊩≡∷≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷≡ u≡v

  step-⊩≡∷≡˘ : ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → u PE.≡ t → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷≡˘ _ u≡v PE.refl = u≡v

  syntax step-⊩≡∷≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷≡ u≡v

  step-⊩≡∷⇒* :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇒* _ u≡v t⇒*u =
    trans-⊩≡∷ (⊩∷-⇐* t⇒*u (wf-⊩≡∷ u≡v .proj₁)) u≡v

  syntax step-⊩≡∷⇒* t u≡v t⇒*u = t ⇒*⟨ t⇒*u ⟩⊩∷ u≡v

  step-⊩≡∷⇒ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇒ _ u≡v t⇒u =
    step-⊩≡∷⇒* _ u≡v (t⇒u ⇨ id (escape-⊩∷ (wf-⊩≡∷ u≡v .proj₁)))

  syntax step-⊩≡∷⇒ t u≡v t⇒u = t ⇒⟨ t⇒u ⟩⊩∷ u≡v

  step-⊩≡∷⇐* :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u :⇒*: t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇐* _ u≡v u⇒*t =
    trans-⊩≡∷ (sym-⊩≡∷ (⊩∷-⇒* u⇒*t (wf-⊩≡∷ u≡v .proj₁))) u≡v

  syntax step-⊩≡∷⇐* t u≡v u⇒*t = t ⇐*⟨ u⇒*t ⟩⊩∷ u≡v

  step-⊩≡∷⇐ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊢ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇐ _ u≡v u⇒t ⊢t =
    step-⊩≡∷⇐* _ u≡v
      ([_,_,_] (escape-⊩∷ (wf-⊩≡∷ u≡v .proj₁)) ⊢t (u⇒t ⇨ id ⊢t))

  syntax step-⊩≡∷⇐ t u≡v u⇒t ⊢t = t ⇐⟨ u⇒t , ⊢t ⟩⊩∷ u≡v

  _≡⟨⟩⊩∷_ : ∀ t → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  _ ≡⟨⟩⊩∷ t≡u = t≡u

  step-⊩≡∷-conv :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv t≡u A≡B = conv-⊩≡∷ (sym-⊩≡ A≡B) t≡u

  syntax step-⊩≡∷-conv t≡u A≡B = ⟨ A≡B ⟩⊩∷ t≡u

  step-⊩≡∷-conv˘ :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv˘ t≡u B≡A = conv-⊩≡∷ B≡A t≡u

  syntax step-⊩≡∷-conv˘ t≡u B≡A = ˘⟨ B≡A ⟩⊩∷ t≡u

  step-⊩≡∷-conv-≡ : Γ ⊩⟨ l ⟩ t ≡ u ∷ B → A PE.≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv-≡ t≡u PE.refl = t≡u

  syntax step-⊩≡∷-conv-≡ t≡u A≡B = ⟨ A≡B ⟩⊩∷≡ t≡u

  step-⊩≡∷-conv-≡˘ : Γ ⊩⟨ l ⟩ t ≡ u ∷ B → B PE.≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv-≡˘ t≡u PE.refl = t≡u

  syntax step-⊩≡∷-conv-≡˘ t≡u B≡A = ˘⟨ B≡A ⟩⊩∷≡ t≡u

  _∎⟨_⟩⊩∷ : ∀ t → Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  _ ∎⟨ ⊩t ⟩⊩∷ = refl-⊩≡∷ ⊩t

  finally-⊩≡∷ : ∀ t u → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷ _ _ t≡u = t≡u

  syntax finally-⊩≡∷ t u t≡u = t ≡⟨ t≡u ⟩⊩∷∎ u ∎

  finally-⊩≡∷˘ : ∀ t u → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷˘ _ _ t≡u = sym-⊩≡∷ t≡u

  syntax finally-⊩≡∷˘ t u u≡t = t ≡˘⟨ u≡t ⟩⊩∷∎ u ∎

  finally-⊩≡∷≡ :
    ∀ t → u PE.≡ v → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷≡ _ PE.refl t≡u = t≡u

  syntax finally-⊩≡∷≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷∎≡ u≡v

  finally-⊩≡∷≡˘ :
    ∀ t → u PE.≡ v → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷≡˘ _ PE.refl u≡t = sym-⊩≡∷ u≡t

  syntax finally-⊩≡∷≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷∎≡ u≡v

  finally-⊩≡∷⇐* :
    ∀ t → Γ ⊢ v ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷⇐* _ v⇒*u t≡u =
    trans-⊩≡∷ t≡u (sym-⊩≡∷ (⊩∷-⇐* v⇒*u (wf-⊩≡∷ t≡u .proj₂)))

  syntax finally-⊩≡∷⇐* t v⇒*u t≡u = t ≡⟨ t≡u ⟩⊩∷⇐* v⇒*u

  finally-⊩≡∷:⇒*: :
    ∀ t → Γ ⊢ u :⇒*: v ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷:⇒*: _ u⇒*v t≡u =
    case wf-⊩≡∷ t≡u of λ
      (_ , ⊩u) →
    trans-⊩≡∷ t≡u (⊩∷-⇒* u⇒*v ⊩u)

  syntax finally-⊩≡∷:⇒*: t u⇒*v t≡u = t ≡⟨ t≡u ⟩⊩∷:⇒*: u⇒*v

opaque

  -- Equational reasoning combinators for _⊩⟨_⟩_≡_∷_ with explicit
  -- types.

  infix -1
    _∷_∎⟨_⟩⊩∷∷ finally-⊩≡∷∷ finally-⊩≡∷∷˘
  infix -2
    step-⊩≡∷∷-conv step-⊩≡∷∷-conv˘ step-⊩≡∷∷-conv-≡ step-⊩≡∷∷-conv-≡˘
  infixr -2
    step-⊩≡∷∷ step-⊩≡∷∷˘ step-⊩≡∷∷≡ step-⊩≡∷∷≡˘ step-⊩≡∷∷⇒* step-⊩≡∷∷⇒
    step-⊩≡∷∷⇐* step-⊩≡∷∷⇐ _∷_≡⟨⟩⊩∷∷_ finally-⊩≡∷∷≡ finally-⊩≡∷∷≡˘
    finally-⊩≡∷∷⇐* finally-⊩≡∷∷:⇒*:

  step-⊩≡∷∷ :
    ∀ t A →
    Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷ _ _ = step-⊩≡∷ _

  syntax step-⊩≡∷∷ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷˘ :
    ∀ t A →
    Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷˘ _ _ = step-⊩≡∷˘ _

  syntax step-⊩≡∷∷˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∷ u≡v

  step-⊩≡∷∷≡ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → t PE.≡ u → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷≡ _ _ = step-⊩≡∷≡ _

  syntax step-⊩≡∷∷≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷≡ u≡v

  step-⊩≡∷∷≡˘ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → u PE.≡ t → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷≡˘ _ _ = step-⊩≡∷≡˘ _

  syntax step-⊩≡∷∷≡˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∷≡ u≡v

  step-⊩≡∷∷⇒* :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇒* _ _ = step-⊩≡∷⇒* _

  syntax step-⊩≡∷∷⇒* t A u≡v t⇒*u = t ∷ A ⇒*⟨ t⇒*u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇒ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇒ _ _ = step-⊩≡∷⇒ _

  syntax step-⊩≡∷∷⇒ t A u≡v t⇒u = t ∷ A ⇒⟨ t⇒u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇐* :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u :⇒*: t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇐* _ _ = step-⊩≡∷⇐* _

  syntax step-⊩≡∷∷⇐* t A u≡v u⇒*t = t ∷ A ⇐*⟨ u⇒*t ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇐ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊢ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇐ _ _ = step-⊩≡∷⇐ _

  syntax step-⊩≡∷∷⇐ t A u≡v u⇒t ⊢t = t ∷ A ⇐⟨ u⇒t , ⊢t ⟩⊩∷∷ u≡v

  _∷_≡⟨⟩⊩∷∷_ : ∀ t A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  _ ∷ _ ≡⟨⟩⊩∷∷ t≡u = t≡u

  step-⊩≡∷∷-conv :
    ∀ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv _ = step-⊩≡∷-conv

  syntax step-⊩≡∷∷-conv A t≡u A≡B = ∷ A ⟨ A≡B ⟩⊩∷∷ t≡u

  step-⊩≡∷∷-conv˘ :
    ∀ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv˘ _ = step-⊩≡∷-conv˘

  syntax step-⊩≡∷∷-conv˘ A t≡u B≡A = ∷ A ˘⟨ B≡A ⟩⊩∷∷ t≡u

  step-⊩≡∷∷-conv-≡ :
    ∀ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ B → A PE.≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv-≡ _ = step-⊩≡∷-conv-≡

  syntax step-⊩≡∷∷-conv-≡ A t≡u A≡B = ∷ A ⟨ A≡B ⟩⊩∷∷≡ t≡u

  step-⊩≡∷∷-conv-≡˘ :
    ∀ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ B → B PE.≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv-≡˘ _ = step-⊩≡∷-conv-≡˘

  syntax step-⊩≡∷∷-conv-≡˘ A t≡u B≡A = ∷ A ˘⟨ B≡A ⟩⊩∷∷≡ t≡u

  _∷_∎⟨_⟩⊩∷∷ : ∀ t A → Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  _ ∷ _ ∎⟨ ⊩t ⟩⊩∷∷ = refl-⊩≡∷ ⊩t

  finally-⊩≡∷∷ : ∀ t A u → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷∷ _ _ _ t≡u = t≡u

  syntax finally-⊩≡∷∷ t A u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∎∷ u ∎

  finally-⊩≡∷∷˘ : ∀ t A u → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷∷˘ _ _ _ t≡u = sym-⊩≡∷ t≡u

  syntax finally-⊩≡∷∷˘ t A u u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∎∷ u ∎

  finally-⊩≡∷∷≡ :
    ∀ t A → u PE.≡ v → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷≡ _ _ = finally-⊩≡∷≡ _

  syntax finally-⊩≡∷∷≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∎∷≡ u≡v

  finally-⊩≡∷∷≡˘ :
    ∀ t A → u PE.≡ v → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷≡˘ _ _ = finally-⊩≡∷≡˘ _

  syntax finally-⊩≡∷∷≡˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∎∷≡ u≡v

  finally-⊩≡∷∷⇐* :
    ∀ t A → Γ ⊢ v ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷⇐* _ _ = finally-⊩≡∷⇐* _

  syntax finally-⊩≡∷∷⇐* t A v⇒*u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷⇐* v⇒*u

  finally-⊩≡∷∷:⇒*: :
    ∀ t A → Γ ⊢ u :⇒*: v ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷:⇒*: _ _ = finally-⊩≡∷:⇒*: _

  syntax finally-⊩≡∷∷:⇒*: t A v⇒*u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷:⇒*: v⇒*u

------------------------------------------------------------------------
-- Embedding

opaque

  -- Embedding for _⊩⟨_⟩_.

  emb-⊩ :
    l ≤ᵘ l′ →
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ A
  emb-⊩ = emb-≤-⊩

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Embedding for _⊩⟨_⟩_≡_.

  emb-⊩≡ :
    l ≤ᵘ l′ →
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ A ≡ B
  emb-⊩≡ ≤ᵘ-refl        A≡B             = A≡B
  emb-⊩≡ (≤ᵘ-step l<l′) (⊩A , ⊩B , A≡B) =
    let p = 1+≤ᵘ1+ l<l′ in
      emb p (⊩<⇔⊩ p .proj₂ ⊩A)
    , emb p (⊩<⇔⊩ p .proj₂ ⊩B)
    , ⊩<≡⇔⊩≡′ p .proj₂ A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Embedding for _⊩⟨_⟩_≡_∷_.

  emb-⊩≡∷ :
    l ≤ᵘ l′ →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A
  emb-⊩≡∷ ≤ᵘ-refl        t≡u                  = t≡u
  emb-⊩≡∷ (≤ᵘ-step l<l′) (⊩A , ⊩t , ⊩u , t≡u) =
    let p   = 1+≤ᵘ1+ l<l′
        ⊩A′ = emb p (⊩<⇔⊩ p .proj₂ ⊩A)
    in
      ⊩A′
    , irrelevanceTerm ⊩A ⊩A′ ⊩t
    , irrelevanceTerm ⊩A ⊩A′ ⊩u
    , irrelevanceEqTerm ⊩A ⊩A′ t≡u

opaque

  -- Embedding for _⊩⟨_⟩_∷_.

  emb-⊩∷ :
    l ≤ᵘ l′ →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l′ ⟩ t ∷ A
  emb-⊩∷ l≤l′ =
    ⊩∷⇔⊩≡∷ .proj₂ ∘→ emb-⊩≡∷ l≤l′ ∘→ ⊩∷⇔⊩≡∷ .proj₁

------------------------------------------------------------------------
-- Some introduction lemmas

opaque
  unfolding _⊩⟨_⟩_∷_

  -- An introduction lemma for _⊩⟨_⟩_∷_.

  ⊩∷-intro :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ t ∷ A
  ⊩∷-intro = _,_

opaque
  unfolding _⊩⟨_⟩_≡_

  -- An introduction lemma for _⊩⟨_⟩_≡_.

  ⊩≡-intro :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ B →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A →
    Γ ⊩⟨ l ⟩ A ≡ B
  ⊩≡-intro ⊩A ⊩B A≡B = ⊩A , ⊩B , A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- An introduction lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷-intro :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩≡∷-intro ⊩A ⊩t ⊩u t≡u =
    ⊩A , ⊩∷→⊩∷/ ⊩A ⊩t , ⊩∷→⊩∷/ ⊩A ⊩u , t≡u

------------------------------------------------------------------------
-- Neutral types and terms

opaque

  -- Neutral types that satisfy certain properties are reducible.

  neutral-⊩ :
    Neutral A →
    Γ ⊢ A →
    Γ ⊢ A ≅ A →
    Γ ⊩⟨ l ⟩ A
  neutral-⊩ = neu

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Neutral terms that satisfy certain properties are reducible.

  neutral-⊩∷ :
    Γ ⊩⟨ l ⟩ A →
    Neutral t →
    Γ ⊢ t ∷ A →
    Γ ⊢ t ~ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A
  neutral-⊩∷ ⊩A t-ne ⊢t t~t =
    ⊩A , neuTerm ⊩A t-ne ⊢t t~t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Reducible equality holds between neutral types that satisfy
  -- certain properties.

  neutral-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ B →
    Neutral A →
    Neutral B →
    Γ ⊢ A ≅ B →
    Γ ⊩⟨ l ⟩ A ≡ B
  neutral-⊩≡ ⊩A ⊩B A-ne B-ne A≅B =
    ⊩A , ⊩B , neuEq ⊩A A-ne B-ne (escape ⊩A) (escape ⊩B) A≅B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Reducible equality holds between neutral terms that satisfy
  -- certain properties.

  neutral-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A →
    Neutral t →
    Neutral u →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ A →
    Γ ⊢ t ~ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  neutral-⊩≡∷ ⊩A t-ne u-ne ⊢t ⊢u t~u =
      ⊩A
    , neuTerm ⊩A t-ne ⊢t (~-trans t~u (~-sym t~u))
    , neuTerm ⊩A u-ne ⊢u (~-trans (~-sym t~u) t~u)
    , neuEqTerm ⊩A t-ne u-ne ⊢t ⊢u t~u

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ne⇔ :
    Neutral A →
    Γ ⊩⟨ l ⟩ A ⇔ ((Γ ⊢ A) × Γ ⊢ A ≅ A)
  ⊩ne⇔ A-ne =
      (λ ⊩A →
         case extractMaybeEmb (ne-elim A-ne ⊩A) of λ
           (_ , ne _ A⇒*B _ B≅B) →
         case whnfRed* (red A⇒*B) (ne A-ne) of λ {
           PE.refl →
         ⊢A-red A⇒*B , B≅B })
    , (λ (⊢A , A≅A) → neu A-ne ⊢A A≅A)

opaque
  unfolding _⊩⟨_⟩_∷_ ⊩ne⇔

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷ne⇔ :
    Neutral A →
    Γ ⊩⟨ l ⟩ t ∷ A ⇔
    (Γ ⊩⟨ l ⟩ A × ∃ λ u → Γ ⊢ t :⇒*: u ∷ A × Neutral u × Γ ⊢ u ~ u ∷ A)
  ⊩∷ne⇔ {A} A-ne =
      (λ (⊩A , ⊩t) →
         case ne-elim A-ne ⊩A of λ
           ⊩A′ →
         ⊩A , lemma ⊩A′ (irrelevanceTerm ⊩A (ne-intr ⊩A′) ⊩t))
    , (λ (⊩A , u , t⇒*u , u-ne , u~u) →
           ⊩ne⇔ A-ne .proj₂ (⊩ne⇔ A-ne .proj₁ ⊩A)
         , neₜ u t⇒*u (neNfₜ u-ne (⊢u-redₜ t⇒*u) u~u))
    where
    lemma :
      (⊩A : Γ ⊩⟨ l ⟩ne A) →
      Γ ⊩⟨ l ⟩ t ∷ A / ne-intr ⊩A →
      ∃ λ u → Γ ⊢ t :⇒*: u ∷ A × Neutral u × Γ ⊢ u ~ u ∷ A
    lemma (emb ≤ᵘ-refl ⊩A) ⊩t =
      lemma ⊩A ⊩t
    lemma (emb (≤ᵘ-step l<) ⊩A) ⊩t =
      lemma (emb l< ⊩A) ⊩t
    lemma (noemb (ne _ A⇒*A′ _ _)) (neₜ u t⇒*u (neNfₜ u-ne _ u~u)) =
      case whnfRed* (red A⇒*A′) (ne A-ne) of λ {
        PE.refl →
      u , t⇒*u , u-ne , u~u }

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ne≡⇔ :
    Neutral A →
    Γ ⊩⟨ l ⟩ A ≡ B ⇔
    (Γ ⊢ A × ∃ λ C → Neutral C × (Γ ⊢ C) × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C)
  ⊩ne≡⇔ {A} {B} A-ne =
      (λ (⊩A , ⊩B , A≡B) →
         case ne-elim A-ne ⊩A of λ
           ⊩A′ →
           escape-⊩ ⊩A
         , lemma ⊩A′ (irrelevanceEq ⊩A (ne-intr ⊩A′) A≡B))
    , (λ (⊢A , C , C-ne , ⊢C , B⇒*C , A≅C) →
         sym-⊩≡
           (B  ⇒*⟨ B⇒*C ⟩⊩
            C  ≡⟨ neutral-⊩≡
                    (⊩ne⇔ C-ne .proj₂ (⊢C , ≅-trans (≅-sym A≅C) A≅C))
                    (⊩ne⇔ A-ne .proj₂ (⊢A , ≅-trans A≅C (≅-sym A≅C)))
                    C-ne A-ne (≅-sym A≅C) ⟩⊩∎
            A  ∎))
    where
    lemma :
      (⊩A : Γ ⊩⟨ l ⟩ne A) →
      Γ ⊩⟨ l ⟩ A ≡ B / ne-intr ⊩A →
      ∃ λ C → Neutral C × (Γ ⊢ C) × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C
    lemma (emb ≤ᵘ-refl ⊩A) A≡B =
      lemma ⊩A A≡B
    lemma (emb (≤ᵘ-step l<) ⊩A) A≡B =
      lemma (emb l< ⊩A) A≡B
    lemma (noemb (ne _ A⇒*A′ _ _)) (ne₌ C [ _ , ⊢C , B⇒*C ] C-ne A′≅C) =
      case whnfRed* (red A⇒*A′) (ne A-ne) of λ {
        PE.refl →
      C , C-ne , ⊢C , B⇒*C , A′≅C }

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ne≡ne⇔ :
    Neutral A →
    Neutral B →
    Γ ⊩⟨ l ⟩ A ≡ B ⇔ ((Γ ⊢ A) × (Γ ⊢ B) × Γ ⊢ A ≅ B)
  ⊩ne≡ne⇔ {A} {B} {Γ} {l} A-ne B-ne =
    Γ ⊩⟨ l ⟩ A ≡ B                                                  ⇔⟨ ⊩ne≡⇔ A-ne ⟩
    (Γ ⊢ A × ∃ λ C → Neutral C × (Γ ⊢ C) × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C)  ⇔⟨ (Σ-cong-⇔ λ _ →
                                                                          (λ (_ , _ , ⊢C , B⇒*C , A≅C) →
                                                                             case whnfRed* B⇒*C (ne B-ne) of λ {
                                                                               PE.refl →
                                                                             ⊢C , A≅C })
                                                                        , (λ (⊢B , A≅B) →
                                                                             _ , B-ne , ⊢B , id ⊢B , A≅B)) ⟩
    (Γ ⊢ A) × (Γ ⊢ B) × Γ ⊢ A ≅ B                                   □⇔

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩ne⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷ne⇔ :
    Neutral A →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A ⇔
    (Γ ⊩⟨ l ⟩ A ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t₁ :⇒*: u₁ ∷ A × Γ ⊢ t₂ :⇒*: u₂ ∷ A ×
     Γ ⊩neNf u₁ ≡ u₂ ∷ A)
  ⊩≡∷ne⇔ {A} A-ne =
      (λ (⊩A , _ , _ , t₁≡t₂) →
         case ne-elim A-ne ⊩A of λ
           ⊩A′ →
         ⊩A , lemma ⊩A′ (irrelevanceEqTerm ⊩A (ne-intr ⊩A′) t₁≡t₂))
    , (λ (⊩A , u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ ,
          u₁≡u₂@(neNfₜ₌ u₁-ne u₂-ne u₁~u₂)) →
         let ⊩A′ = ⊩ne⇔ A-ne .proj₂ (⊩ne⇔ A-ne .proj₁ ⊩A) in
           ⊩A′
         , ⊩∷→⊩∷/ ⊩A′
             (⊩∷ne⇔ A-ne .proj₂
                ( ⊩A , u₁ , t₁⇒*u₁ , u₁-ne
                , ~-trans u₁~u₂ (~-sym u₁~u₂)
                ))
         , ⊩∷→⊩∷/ ⊩A′
             (⊩∷ne⇔ A-ne .proj₂
                ( ⊩A , u₂ , t₂⇒*u₂ , u₂-ne
                , ~-trans (~-sym u₁~u₂) u₁~u₂
                ))
         , neₜ₌ u₁ u₂ t₁⇒*u₁ t₂⇒*u₂ u₁≡u₂)
    where
    lemma :
      (⊩A : Γ ⊩⟨ l ⟩ne A) →
      Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A / ne-intr ⊩A →
      ∃₂ λ u₁ u₂ →
      Γ ⊢ t₁ :⇒*: u₁ ∷ A × Γ ⊢ t₂ :⇒*: u₂ ∷ A ×
      Γ ⊩neNf u₁ ≡ u₂ ∷ A
    lemma (emb ≤ᵘ-refl ⊩A) t₁≡t₂ =
      lemma ⊩A t₁≡t₂
    lemma (emb (≤ᵘ-step l<) ⊩A) t₁≡t₂ =
      lemma (emb l< ⊩A) t₁≡t₂
    lemma (noemb (ne _ A⇒*A′ _ _)) (neₜ₌ u₁ u₂ t₁⇒*u₁ t₂⇒*u₂ u₁≡u₂) =
      case whnfRed* (red A⇒*A′) (ne A-ne) of λ {
        PE.refl →
      u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≡u₂ }
