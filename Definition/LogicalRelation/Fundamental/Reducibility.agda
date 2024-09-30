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
open import Tools.Product
open import Tools.Nat using (Nat)

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u : Term _
    l : TypeLevel

opaque

  -- Well-formed types are reducible.

  reducible-⊩ : Γ ⊢ A → ∃ λ l → Γ ⊩⟨ l ⟩ A
  reducible-⊩ ⊢A = _ , ⊩ᵛ→⊩ (fundamental-⊩ᵛ ⊢A .proj₂)

opaque

  -- The relation _⊢_≡_ is contained in _⊩⟨ ⟩_≡_.

  reducible-⊩≡ : Γ ⊢ A ≡ B → ∃ λ l → Γ ⊩⟨ l ⟩ A ≡ B
  reducible-⊩≡ ⊢A≡B = _ , ⊩ᵛ≡→⊩≡ (fundamental-⊩ᵛ≡ ⊢A≡B .proj₂)

opaque

  -- Well-formed terms are reducible.

  reducible-⊩∷ : Γ ⊢ t ∷ A → ∃ λ l → Γ ⊩⟨ l ⟩ t ∷ A
  reducible-⊩∷ ⊢t∷A = _ , ⊩ᵛ∷→⊩∷ (fundamental-⊩ᵛ∷ ⊢t∷A .proj₂)

opaque

  -- The relation _⊢_≡_∷_ is contained in _⊩⟨ ⟩_≡_∷_.

  reducible-⊩≡∷ : Γ ⊢ t ≡ u ∷ A → ∃ λ l → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  reducible-⊩≡∷ ⊢t≡u∷A = _ , ⊩ᵛ≡∷→⊩≡∷ (fundamental-⊩ᵛ≡∷ ⊢t≡u∷A .proj₂)
