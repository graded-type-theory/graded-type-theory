------------------------------------------------------------------------
-- Some embedding lemmas
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Embedding
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Kit R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Nat using (Nat)

private
  variable
    m n     : Nat
    ∇       : DCon (Term 0) m
    Γ       : Con Term n
    A B t u : Term n
    l₁ l₂   : Universe-level

opaque

  -- An embedding lemma for _⊩⟨_⟩_∷_/_.

  emb-≤-⊩∷ :
    {⊩A : ∇ » Γ ⊩⟨ l₁ ⟩ A} {p : l₁ ≤ᵘ l₂} →
    ∇ » Γ ⊩⟨ l₁ ⟩ t ∷ A / ⊩A →
    ∇ » Γ ⊩⟨ l₂ ⟩ t ∷ A / emb-≤-⊩ p ⊩A
  emb-≤-⊩∷ {⊩A} {p} = irrelevanceTerm ⊩A (emb-≤-⊩ p ⊩A)

opaque

  -- An embedding lemma for _⊩⟨_⟩_≡_/_.

  emb-≤-⊩≡ :
    {⊩A : ∇ » Γ ⊩⟨ l₁ ⟩ A} {p : l₁ ≤ᵘ l₂} →
    ∇ » Γ ⊩⟨ l₁ ⟩ A ≡ B / ⊩A → ∇ » Γ ⊩⟨ l₂ ⟩ A ≡ B / emb-≤-⊩ p ⊩A
  emb-≤-⊩≡ {⊩A} {p} = irrelevanceEq ⊩A (emb-≤-⊩ p ⊩A)

opaque

  -- An embedding lemma for _⊩⟨_⟩_≡_∷_/_.

  emb-≤-⊩≡∷ :
    {⊩A : ∇ » Γ ⊩⟨ l₁ ⟩ A} {p : l₁ ≤ᵘ l₂} →
    ∇ » Γ ⊩⟨ l₁ ⟩ t ≡ u ∷ A / ⊩A → ∇ » Γ ⊩⟨ l₂ ⟩ t ≡ u ∷ A / emb-≤-⊩ p ⊩A
  emb-≤-⊩≡∷ {⊩A} {p} = irrelevanceEqTerm ⊩A (emb-≤-⊩ p ⊩A)
