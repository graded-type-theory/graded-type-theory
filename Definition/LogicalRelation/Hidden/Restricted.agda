------------------------------------------------------------------------
-- Restricted variants of the logical relations
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Hidden.Restricted
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

import Definition.LogicalRelation R as L
import Definition.LogicalRelation.Hidden R as H
open import Definition.LogicalRelation.Weakening.Restricted R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R using (_∷ʷ_⊇_)

open import Definition.Untyped M
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties.Neutral M type-variant

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

------------------------------------------------------------------------
-- The type formers

opaque

  -- Reducible types.

  infix 4 _⊩⟨_⟩_

  _⊩⟨_⟩_ : Con Term n → Universe-level → Term n → Set a
  Γ ⊩⟨ l ⟩ A =
    ⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ L.⊩⟨ l ⟩ A

opaque

  -- Reducible terms.

  infix 4 _⊩⟨_⟩_∷_

  _⊩⟨_⟩_∷_ : Con Term n → Universe-level → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ t ∷ A =
    ⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ H.⊩⟨ l ⟩ t ∷ A

opaque

  -- Reducible type equality.

  infix 4 _⊩⟨_⟩_≡_

  _⊩⟨_⟩_≡_ : Con Term n → Universe-level → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ A ≡ B =
    ⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ H.⊩⟨ l ⟩ A ≡ B

opaque

  -- Reducible term equality.

  infix 4 _⊩⟨_⟩_≡_∷_

  _⊩⟨_⟩_≡_∷_ :
    Con Term n → Universe-level → Term n → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A =
    ⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ H.⊩⟨ l ⟩ t ≡ u ∷ A

------------------------------------------------------------------------
-- Characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩⇔ :
    Γ ⊩⟨ l ⟩ A ⇔
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ L.⊩⟨ l ⟩ A)
  ⊩⇔ = id⇔

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷⇔ :
    Γ ⊩⟨ l ⟩ t ∷ A ⇔
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ H.⊩⟨ l ⟩ t ∷ A)
  ⊩∷⇔ = id⇔

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩≡⇔ :
    Γ ⊩⟨ l ⟩ A ≡ B ⇔
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ H.⊩⟨ l ⟩ A ≡ B)
  ⊩≡⇔ = id⇔

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⇔
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ H.⊩⟨ l ⟩ t ≡ u ∷ A)
  ⊩≡∷⇔ = id⇔

------------------------------------------------------------------------
-- Conversion functions

opaque

  -- A conversion function for _⊩⟨_⟩_.

  →⊩ : Γ L.⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A
  →⊩ ⊩A = ⊩⇔ .proj₂ ⊩A

opaque

  -- A conversion function for _⊩⟨_⟩_.

  ⊩→ :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩⟨ l ⟩ A → Γ L.⊩⟨ l ⟩ A
  ⊩→ ⊩A = ⊩⇔ .proj₁ ⊩A

opaque

  -- A conversion function for _⊩⟨_⟩_∷_.

  →⊩∷ : Γ H.⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ∷ A
  →⊩∷ ⊩t = ⊩∷⇔ .proj₂ ⊩t

opaque

  -- A conversion function for _⊩⟨_⟩_∷_.

  ⊩∷→ :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩⟨ l ⟩ t ∷ A → Γ H.⊩⟨ l ⟩ t ∷ A
  ⊩∷→ ⊩t = ⊩∷⇔ .proj₁ ⊩t

opaque

  -- A conversion function for _⊩⟨_⟩_≡_.

  →⊩≡ : Γ H.⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B
  →⊩≡ A≡B = ⊩≡⇔ .proj₂ A≡B

opaque

  -- A conversion function for _⊩⟨_⟩_≡_.

  ⊩≡→ :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩⟨ l ⟩ A ≡ B → Γ H.⊩⟨ l ⟩ A ≡ B
  ⊩≡→ A≡B = ⊩≡⇔ .proj₁ A≡B

opaque

  -- A conversion function for _⊩⟨_⟩_≡_∷_.

  →⊩≡∷ : Γ H.⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  →⊩≡∷ t≡u = ⊩≡∷⇔ .proj₂ t≡u

opaque

  -- A conversion function for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷→ :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ H.⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩≡∷→ t≡u = ⊩≡∷⇔ .proj₁ t≡u

------------------------------------------------------------------------
-- Some utility functions

opaque
  unfolding _⊩⟨_⟩_

  -- If one can prove Γ ⊩⟨ l ⟩ A given Neutrals-included or-empty Γ,
  -- then Γ ⊩⟨ l ⟩ A holds.

  with-inc-⊩ :
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ A
  with-inc-⊩ f ⦃ inc ⦄ = f ⦃ inc = inc ⦄ ⦃ inc = inc ⦄

opaque
  unfolding _⊩⟨_⟩_∷_

  -- If one can prove Γ ⊩⟨ l ⟩ t ∷ A given
  -- Neutrals-included or-empty Γ, then Γ ⊩⟨ l ⟩ t ∷ A holds.

  with-inc-⊩∷ :
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ ⊩⟨ l ⟩ t ∷ A) →
    Γ ⊩⟨ l ⟩ t ∷ A
  with-inc-⊩∷ f ⦃ inc ⦄ = f ⦃ inc = inc ⦄ ⦃ inc = inc ⦄

opaque
  unfolding _⊩⟨_⟩_≡_

  -- If one can prove Γ ⊩⟨ l ⟩ A ≡ B given
  -- Neutrals-included or-empty Γ, then Γ ⊩⟨ l ⟩ A ≡ B holds.

  with-inc-⊩≡ :
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ ⊩⟨ l ⟩ A ≡ B) →
    Γ ⊩⟨ l ⟩ A ≡ B
  with-inc-⊩≡ f ⦃ inc ⦄ = f ⦃ inc = inc ⦄ ⦃ inc = inc ⦄

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- If one can prove Γ ⊩⟨ l ⟩ t ≡ u ∷ A given
  -- Neutrals-included or-empty Γ, then Γ ⊩⟨ l ⟩ t ≡ u ∷ A holds.

  with-inc-⊩≡∷ :
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ ⊩⟨ l ⟩ t ≡ u ∷ A) →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  with-inc-⊩≡∷ f ⦃ inc ⦄ = f ⦃ inc = inc ⦄ ⦃ inc = inc ⦄

------------------------------------------------------------------------
-- Reflexivity

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_

  -- Reflexivity for _⊩⟨_⟩_≡_.

  refl-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ A ≡ A
  refl-⊩≡ ⊩A = H.refl-⊩≡ ⊩A

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- Reflexivity for _⊩⟨_⟩_≡_∷_.

  refl-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  refl-⊩≡∷ ⊩t = H.refl-⊩≡∷ ⊩t

------------------------------------------------------------------------
-- Symmetry

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Symmetry for _⊩⟨_⟩_≡_.

  sym-⊩≡ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ B ≡ A
  sym-⊩≡ A≡B = H.sym-⊩≡ A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Symmetry for _⊩⟨_⟩_≡_∷_.

  sym-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ u ≡ t ∷ A
  sym-⊩≡∷ t≡u = H.sym-⊩≡∷ t≡u

------------------------------------------------------------------------
-- Transitivity

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Transitivity for _⊩⟨_⟩_≡_.

  trans-⊩≡ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ B ≡ C →
    Γ ⊩⟨ l ⟩ A ≡ C
  trans-⊩≡ A≡B B≡C = H.trans-⊩≡ A≡B B≡C

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Transitivity for _⊩⟨_⟩_≡_∷_.

  trans-⊩≡∷ :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ u ≡ v ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  trans-⊩≡∷ t≡u u≡v = H.trans-⊩≡∷ t≡u u≡v

------------------------------------------------------------------------
-- Well-formedness lemmas

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_∷_

  -- A well-formedness lemma for _⊩⟨_⟩_∷_.

  wf-⊩∷ : Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ A
  wf-⊩∷ ⊩t = H.wf-⊩∷ ⊩t

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_

  -- A well-formedness lemma for _⊩⟨_⟩_≡_.

  wf-⊩≡ : Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A × Γ ⊩⟨ l ⟩ B
  wf-⊩≡ A≡B = H.wf-⊩≡ A≡B .proj₁ , H.wf-⊩≡ A≡B .proj₂

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A well-formedness lemma for _⊩⟨_⟩_≡_∷_.

  wf-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A × Γ ⊩⟨ l ⟩ u ∷ A
  wf-⊩≡∷ t≡u = H.wf-⊩≡∷ t≡u .proj₁ , H.wf-⊩≡∷ t≡u .proj₂

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩⇔⊩≡ : (Γ ⊩⟨ l ⟩ A) ⇔ Γ ⊩⟨ l ⟩ A ≡ A
  ⊩⇔⊩≡ = instance-Π-cong-⇔ H.⊩⇔⊩≡

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷⇔⊩≡∷ : Γ ⊩⟨ l ⟩ t ∷ A ⇔ Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  ⊩∷⇔⊩≡∷ = instance-Π-cong-⇔ H.⊩∷⇔⊩≡∷

------------------------------------------------------------------------
-- Changing type levels

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_

  -- Changing type levels for _⊩⟨_⟩_≡_.

  level-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ B →
    Γ ⊩⟨ l′ ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ A ≡ B
  level-⊩≡ ⊩A ⊩B A≡B = H.level-⊩≡ ⊩A ⊩B A≡B

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_∷_

  -- Changing type levels for _⊩⟨_⟩_≡_∷_.

  level-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  level-⊩≡∷ ⊩A t≡u = H.level-⊩≡∷ ⊩A t≡u

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
  conv-⊩≡∷ A≡B t≡u = H.conv-⊩≡∷ A≡B t≡u

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
  unfolding _⊩⟨_⟩_≡_

  -- Weakening for _⊩⟨_⟩_≡_.

  wk-⊩≡ : ρ ∷ʷ Δ ⊇ Γ → Γ ⊩⟨ l ⟩ A ≡ B → Δ ⊩⟨ l ⟩ wk ρ A ≡ wk ρ B
  wk-⊩≡ Δ⊇Γ A≡B =
    let Δ⊇Γ = ∷ʷ⊇→∷ʷʳ⊇ Δ⊇Γ in
    H.wk-⊩≡ Δ⊇Γ $ A≡B ⦃ inc = wk-Neutrals-included-or-empty→ Δ⊇Γ ⦄

opaque

  -- Weakening for _⊩⟨_⟩_.

  wk-⊩ : ρ ∷ʷ Δ ⊇ Γ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ l ⟩ wk ρ A
  wk-⊩ Δ⊇Γ = ⊩⇔⊩≡ .proj₂ ∘→ wk-⊩≡ Δ⊇Γ ∘→ ⊩⇔⊩≡ .proj₁

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Weakening for _⊩⟨_⟩_≡_∷_.

  wk-⊩≡∷ :
    ρ ∷ʷ Δ ⊇ Γ → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Δ ⊩⟨ l ⟩ wk ρ t ≡ wk ρ u ∷ wk ρ A
  wk-⊩≡∷ Δ⊇Γ t≡u =
    let Δ⊇Γ = ∷ʷ⊇→∷ʷʳ⊇ Δ⊇Γ in
    H.wk-⊩≡∷ Δ⊇Γ $ t≡u ⦃ inc = wk-Neutrals-included-or-empty→ Δ⊇Γ ⦄

opaque

  -- Weakening for _⊩⟨_⟩_∷_.

  wk-⊩∷ : ρ ∷ʷ Δ ⊇ Γ → Γ ⊩⟨ l ⟩ t ∷ A → Δ ⊩⟨ l ⟩ wk ρ t ∷ wk ρ A
  wk-⊩∷ Δ⊇Γ = ⊩∷⇔⊩≡∷ .proj₂ ∘→ wk-⊩≡∷ Δ⊇Γ ∘→ ⊩∷⇔⊩≡∷ .proj₁

------------------------------------------------------------------------
-- Reduction

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_

  -- A reduction lemma for _⊩⟨_⟩_.

  ⊩-⇒* : Γ ⊢ A ⇒* B → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A ≡ B
  ⊩-⇒* A⇒*B ⊩A = H.⊩-⇒* A⇒*B ⊩A

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A reduction lemma for _⊩⟨_⟩_∷_.

  ⊩∷-⇒* :
    Γ ⊢ t ⇒* u ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩∷-⇒* t⇒*u ⊩t = H.⊩∷-⇒* t⇒*u ⊩t

------------------------------------------------------------------------
-- Expansion

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_

  -- An expansion lemma for _⊩⟨_⟩_.

  ⊩-⇐* : Γ ⊢ A ⇒* B → Γ ⊩⟨ l ⟩ B → Γ ⊩⟨ l ⟩ A ≡ B
  ⊩-⇐* A⇒*B ⊩B = H.⊩-⇐* A⇒*B ⊩B

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- An expansion lemma for _⊩⟨_⟩_∷_.

  ⊩∷-⇐* :
    Γ ⊢ t ⇒* u ∷ A →
    Γ ⊩⟨ l ⟩ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩∷-⇐* t⇒*u ⊩u = H.⊩∷-⇐* t⇒*u ⊩u

------------------------------------------------------------------------
-- Escape lemmas

opaque
  unfolding _⊩⟨_⟩_

  -- An escape lemma for _⊩⟨_⟩_.

  escape-⊩ :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩⟨ l ⟩ A → Γ ⊢ A
  escape-⊩ ⊩A = H.escape-⊩ ⊩A

opaque
  unfolding _⊩⟨_⟩_∷_

  -- An escape lemma for _⊩⟨_⟩_∷_.

  escape-⊩∷ :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊢ t ∷ A
  escape-⊩∷ ⊩t = H.escape-⊩∷ ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- An escape lemma for _⊩⟨_⟩_≡_.

  escape-⊩≡ :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊢ A ≅ B
  escape-⊩≡ A≡B = H.escape-⊩≡ A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- An escape lemma for _⊩⟨_⟩_≡_∷_.

  escape-⊩≡∷ :
    ⦃ inc : Neutrals-included or-empty Γ ⦄ →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊢ t ≅ u ∷ A
  escape-⊩≡∷ t≡u = H.escape-⊩≡∷ t≡u

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
    step-⊩≡⇐ _≡⟨⟩⊩_ finally-⊩≡≡ finally-⊩≡≡˘ finally-⊩≡⇐* finally-⊩≡⇒*

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
  step-⊩≡⇒ _ B≡C = step-⊩≡⇒* _ B≡C ∘→ redMany-⊢

  syntax step-⊩≡⇒ A B≡C A⇒B = A ⇒⟨ A⇒B ⟩⊩ B≡C

  step-⊩≡⇐* : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ B ⇒* A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇐* _ B≡C B⇒*A =
    trans-⊩≡ (sym-⊩≡ (⊩-⇒* B⇒*A (wf-⊩≡ B≡C .proj₁))) B≡C

  syntax step-⊩≡⇐* A B≡C B⇒*A = A ⇐*⟨ B⇒*A ⟩⊩ B≡C

  step-⊩≡⇐ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ B ⇒ A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇐ _ B≡C = step-⊩≡⇐* _ B≡C ∘→ redMany-⊢

  syntax step-⊩≡⇐ A B≡C B⇒A = A ⇐⟨ B⇒A ⟩⊩ B≡C

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

  finally-⊩≡⇒* : ∀ A → Γ ⊢ B ⇒* C → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡⇒* _ B⇒*C A≡B =
    case wf-⊩≡ A≡B of λ
      (_ , ⊩B) →
    trans-⊩≡ A≡B (⊩-⇒* B⇒*C ⊩B)

  syntax finally-⊩≡⇒* A B⇒*C A≡B = A ≡⟨ A≡B ⟩⊩⇒* B⇒*C

opaque

  -- Equational reasoning combinators for _⊩⟨_⟩_≡_∷_.

  infix -1
    _∎⟨_⟩⊩∷ finally-⊩≡∷ finally-⊩≡∷˘
  infix -2
    step-⊩≡∷-conv step-⊩≡∷-conv˘ step-⊩≡∷-conv-≡ step-⊩≡∷-conv-≡˘
  infixr -2
    step-⊩≡∷ step-⊩≡∷˘ step-⊩≡∷≡ step-⊩≡∷≡˘ step-⊩≡∷⇒* step-⊩≡∷⇒
    step-⊩≡∷⇐* step-⊩≡∷⇐ _≡⟨⟩⊩∷_ finally-⊩≡∷≡ finally-⊩≡∷≡˘
    finally-⊩≡∷⇐* finally-⊩≡∷⇒*

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
  step-⊩≡∷⇒ _ u≡v = step-⊩≡∷⇒* _ u≡v ∘→ redMany

  syntax step-⊩≡∷⇒ t u≡v t⇒u = t ⇒⟨ t⇒u ⟩⊩∷ u≡v

  step-⊩≡∷⇐* :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒* t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇐* _ u≡v u⇒*t =
    trans-⊩≡∷ (sym-⊩≡∷ (⊩∷-⇒* u⇒*t (wf-⊩≡∷ u≡v .proj₁))) u≡v

  syntax step-⊩≡∷⇐* t u≡v u⇒*t = t ⇐*⟨ u⇒*t ⟩⊩∷ u≡v

  step-⊩≡∷⇐ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇐ _ u≡v = step-⊩≡∷⇐* _ u≡v ∘→ redMany

  syntax step-⊩≡∷⇐ t u≡v u⇒t = t ⇐⟨ u⇒t ⟩⊩∷ u≡v

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

  finally-⊩≡∷⇒* :
    ∀ t → Γ ⊢ u ⇒* v ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷⇒* _ u⇒*v t≡u =
    case wf-⊩≡∷ t≡u of λ
      (_ , ⊩u) →
    trans-⊩≡∷ t≡u (⊩∷-⇒* u⇒*v ⊩u)

  syntax finally-⊩≡∷⇒* t u⇒*v t≡u = t ≡⟨ t≡u ⟩⊩∷⇒* u⇒*v

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
    finally-⊩≡∷∷⇐* finally-⊩≡∷∷⇒*

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
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒* t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇐* _ _ = step-⊩≡∷⇐* _

  syntax step-⊩≡∷∷⇐* t A u≡v u⇒*t = t ∷ A ⇐*⟨ u⇒*t ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇐ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
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

  finally-⊩≡∷∷⇒* :
    ∀ t A → Γ ⊢ u ⇒* v ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷⇒* _ _ = finally-⊩≡∷⇒* _

  syntax finally-⊩≡∷∷⇒* t A v⇒*u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷⇒* v⇒*u

------------------------------------------------------------------------
-- Embedding

opaque
  unfolding _⊩⟨_⟩_

  -- Embedding for _⊩⟨_⟩_.

  emb-⊩ :
    l ≤ᵘ l′ →
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ A
  emb-⊩ p ⊩A = H.emb-⊩ p ⊩A

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Embedding for _⊩⟨_⟩_≡_.

  emb-⊩≡ :
    l ≤ᵘ l′ →
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ A ≡ B
  emb-⊩≡ p A≡B = H.emb-⊩≡ p A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Embedding for _⊩⟨_⟩_≡_∷_.

  emb-⊩≡∷ :
    l ≤ᵘ l′ →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A
  emb-⊩≡∷ p t≡u = H.emb-⊩≡∷ p t≡u

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Embedding for _⊩⟨_⟩_∷_.

  emb-⊩∷ :
    l ≤ᵘ l′ →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l′ ⟩ t ∷ A
  emb-⊩∷ p ⊩t = H.emb-⊩∷ p ⊩t

------------------------------------------------------------------------
-- Neutral types and terms

opaque
  unfolding _⊩⟨_⟩_

  -- Atomic neutral types that satisfy certain properties are
  -- reducible.

  neutral-⊩ :
    Neutralᵃ A →
    Γ ⊢≅ A →
    Γ ⊩⟨ l ⟩ A
  neutral-⊩ A-ne ≅A =
    H.neutral-⊩ (or-empty-Neutral→ (ne⁻ A-ne)) A-ne ≅A

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_∷_

  -- Atomic neutral terms that satisfy certain properties are
  -- reducible.

  neutral-⊩∷ :
    Γ ⊩⟨ l ⟩ A →
    Neutralᵃ t →
    Γ ⊢~ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A
  neutral-⊩∷ ⊩A t-ne ~t =
    H.neutral-⊩∷ (or-empty-Neutral→ (ne⁻ t-ne)) ⊩A t-ne ~t

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_

  -- Reducible equality holds between atomic neutral types that
  -- satisfy certain properties.

  neutral-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ B →
    Neutralᵃ A →
    Neutralᵃ B →
    Γ ⊢ A ≅ B →
    Γ ⊩⟨ l ⟩ A ≡ B
  neutral-⊩≡ ⊩A ⊩B A-ne B-ne A≅B =
    H.neutral-⊩≡ ⊩A ⊩B A-ne B-ne A≅B

opaque
  unfolding _⊩⟨_⟩_ _⊩⟨_⟩_≡_∷_

  -- Reducible equality holds between atomic neutral terms that
  -- satisfy certain properties.

  neutral-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A →
    Neutralᵃ t →
    Neutralᵃ u →
    Γ ⊢ t ~ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  neutral-⊩≡∷ ⊩A t-ne u-ne t~u =
    H.neutral-⊩≡∷ (or-empty-Neutral→ (ne⁻ t-ne)) ⊩A t-ne u-ne t~u

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ne⇔ :
    Neutralᵃ A →
    Γ ⊩⟨ l ⟩ A ⇔ (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ ⊢≅ A)
  ⊩ne⇔ {A} {Γ} {l} A-ne =
    Γ ⊩⟨ l ⟩ A                                               ⇔⟨ ⊩⇔ ⟩

    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ L.⊩⟨ l ⟩ A)  ⇔⟨ instance-Π-cong-⇔ $ H.⊩ne⇔ A-ne ⟩

    (⦃ inc : Neutrals-included or-empty Γ ⦄ →
     Neutrals-included × Γ ⊢≅ A)                             ⇔⟨ instance-Π-cong-⇔ $
                                                                  proj₂
                                                                , (or-empty-Neutral→ (ne⁻ A-ne) ,_)
                                                              ⟩
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ ⊢≅ A)        □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷ne⇔ :
    Neutralᵃ A →
    Γ ⊩⟨ l ⟩ t ∷ A ⇔
    (⦃ inc : Neutrals-included or-empty Γ ⦄ →
     Γ ⊢≅ A × ∃ λ u → Γ ⊢ t ⇒* u ∷ A × Neutralᵃ u × Γ ⊢~ u ∷ A)
  ⊩∷ne⇔ {A} {Γ} {l} {t} A-ne =
    Γ ⊩⟨ l ⟩ t ∷ A                                               ⇔⟨ ⊩∷⇔ ⟩

    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ H.⊩⟨ l ⟩ t ∷ A)  ⇔⟨ instance-Π-cong-⇔ $ H.⊩∷ne⇔ A-ne ⟩

    (⦃ inc : Neutrals-included or-empty Γ ⦄ →
     Neutrals-included × Γ ⊢≅ A ×
     ∃ λ u → Γ ⊢ t ⇒* u ∷ A × Neutralᵃ u × Γ ⊢~ u ∷ A)           ⇔⟨ instance-Π-cong-⇔ $
                                                                      proj₂
                                                                    , (or-empty-Neutral→ (ne⁻ A-ne) ,_)
                                                                  ⟩
    (⦃ inc : Neutrals-included or-empty Γ ⦄ →
     Γ ⊢≅ A × ∃ λ u → Γ ⊢ t ⇒* u ∷ A × Neutralᵃ u × Γ ⊢~ u ∷ A)  □⇔

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ne≡⇔ :
    Neutralᵃ A →
    Γ ⊩⟨ l ⟩ A ≡ B ⇔
    (⦃ inc : Neutrals-included or-empty Γ ⦄ →
     ∃ λ C → Neutralᵃ C × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C)
  ⊩ne≡⇔ {A} {Γ} {l} {B} A-ne =
    Γ ⊩⟨ l ⟩ A ≡ B                                                     ⇔⟨ ⊩≡⇔ ⟩

    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ H.⊩⟨ l ⟩ A ≡ B)        ⇔⟨ instance-Π-cong-⇔ $ H.⊩ne≡⇔ A-ne ⟩

    (⦃ inc : Neutrals-included or-empty Γ ⦄ →
     Neutrals-included × ∃ λ C → Neutralᵃ C × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C)  ⇔⟨ instance-Π-cong-⇔ $
                                                                            proj₂
                                                                          , (or-empty-Neutral→ (ne⁻ A-ne) ,_) ⟩
    (⦃ inc : Neutrals-included or-empty Γ ⦄ →
     ∃ λ C → Neutralᵃ C × Γ ⊢ B ⇒* C × Γ ⊢ A ≅ C)                      □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ne≡ne⇔ :
    Neutralᵃ A →
    Neutralᵃ B →
    Γ ⊩⟨ l ⟩ A ≡ B ⇔
    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ ⊢ A ≅ B)
  ⊩ne≡ne⇔ {A} {B} {Γ} {l} A-ne B-ne =
    Γ ⊩⟨ l ⟩ A ≡ B                                               ⇔⟨ ⊩≡⇔ ⟩

    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ H.⊩⟨ l ⟩ A ≡ B)  ⇔⟨ instance-Π-cong-⇔ $ H.⊩ne≡ne⇔ A-ne B-ne ⟩

    (⦃ inc : Neutrals-included or-empty Γ ⦄ →
     Neutrals-included × Γ ⊢ A ≅ B)                              ⇔⟨ instance-Π-cong-⇔ $
                                                                      proj₂
                                                                    , (or-empty-Neutral→ (ne⁻ A-ne) ,_)
                                                                  ⟩

    (⦃ inc : Neutrals-included or-empty Γ ⦄ → Γ ⊢ A ≅ B)         □⇔

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩ne⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷ne⇔ :
    Neutralᵃ A →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A ⇔
    (⦃ inc : Neutrals-included or-empty Γ ⦄ →
     Γ ⊢≅ A ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t₁ ⇒* u₁ ∷ A × Γ ⊢ t₂ ⇒* u₂ ∷ A ×
     Γ L.⊩neNf u₁ ≡ u₂ ∷ A)
  ⊩≡∷ne⇔ A-ne = (instance-Π-cong-⇔ $ H.⊩≡∷ne⇔ A-ne) ∘⇔ ⊩≡∷⇔
