------------------------------------------------------------------------
-- The fundamental lemma of the logical relation for reducibility.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Fundamental.Reducibility
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Substitution R

open import Tools.Function
open import Tools.Nat using (Nat)

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u : Term _
    l : TypeLevel

opaque

  -- Well-formed types are reducible.

  reducible-⊩ : Γ ⊢ A → Γ ⊩⟨ ¹ ⟩ A
  reducible-⊩ = ⊩ᵛ→⊩ ∘→ fundamental-⊩ᵛ

opaque

  -- The relation _⊢_≡_ is contained in _⊩⟨ ¹ ⟩_≡_.

  reducible-⊩≡ : Γ ⊢ A ≡ B → Γ ⊩⟨ ¹ ⟩ A ≡ B
  reducible-⊩≡ = ⊩ᵛ≡→⊩≡ ∘→ fundamental-⊩ᵛ≡

opaque

  -- Well-formed terms are reducible.

  reducible-⊩∷ : Γ ⊢ t ∷ A → Γ ⊩⟨ ¹ ⟩ t ∷ A
  reducible-⊩∷ = ⊩ᵛ∷→⊩∷ ∘→ fundamental-⊩ᵛ∷

opaque

  -- The relation _⊢_≡_∷_ is contained in _⊩⟨ ¹ ⟩_≡_∷_.

  reducible-⊩≡∷ : Γ ⊢ t ≡ u ∷ A → Γ ⊩⟨ ¹ ⟩ t ≡ u ∷ A
  reducible-⊩≡∷ = ⊩ᵛ≡∷→⊩≡∷ ∘→ fundamental-⊩ᵛ≡∷
