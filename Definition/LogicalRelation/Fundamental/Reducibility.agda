------------------------------------------------------------------------
-- The fundamental lemma of the logical relation for reducibility.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
import Definition.Untyped
open import Graded.Modality

module Definition.LogicalRelation.Fundamental.Reducibility
  {a} {M : Set a}
  (open Definition.Untyped M)
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  (open EqRelSet eqrel)
  {n} {Γ : Con Term n}
  -- Neutrals are included or Γ is empty.
  ⦃ inc : Neutrals-included-or-empty Γ ⦄
  where

open import Definition.Typed R
open import Definition.LogicalRelation R
import Definition.LogicalRelation.Fundamental.Reducibility.Restricted R
  as RR
open import Definition.LogicalRelation.Hidden R
import Definition.LogicalRelation.Hidden.Restricted R as R

open import Tools.Function
open import Tools.Product as Σ

private variable
  A B t u : Term _

opaque

  -- Well-formed types are reducible.

  reducible-⊩ : Γ ⊢ A → ∃ λ l → Γ ⊩⟨ l ⟩ A
  reducible-⊩ = Σ.map idᶠ R.⊩→ ∘→ RR.reducible-⊩

opaque

  -- If A and B are definitionally equal (with respect to Γ), then
  -- Γ ⊩⟨ l ⟩ A ≡ B holds for some type level l.

  reducible-⊩≡ : Γ ⊢ A ≡ B → ∃ λ l → Γ ⊩⟨ l ⟩ A ≡ B
  reducible-⊩≡ = Σ.map idᶠ R.⊩≡→ ∘→ RR.reducible-⊩≡

opaque

  -- Well-formed terms are reducible.

  reducible-⊩∷ : Γ ⊢ t ∷ A → ∃ λ l → Γ ⊩⟨ l ⟩ t ∷ A
  reducible-⊩∷ = Σ.map idᶠ R.⊩∷→ ∘→ RR.reducible-⊩∷

opaque

  -- If t and u are definitionally equal (with respect to Γ and A),
  -- then Γ ⊩⟨ l ⟩ t ≡ u ∷ A holds for some type level l.

  reducible-⊩≡∷ : Γ ⊢ t ≡ u ∷ A → ∃ λ l → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  reducible-⊩≡∷ = Σ.map idᶠ R.⊩≡∷→ ∘→ RR.reducible-⊩≡∷
