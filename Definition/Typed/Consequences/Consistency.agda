------------------------------------------------------------------------
-- Consistency of equality of natural numbers.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Consistency
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Consequences.Canonicity R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.EqRelInstance R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Substitution.Introductions R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Relation

private
  variable
    n   : Nat
    Γ   : Con Term n
    σ   : Subst _ _
    t u : Term n

opaque

  -- If there is some way to instantiate all the types in Γ, then Γ is
  -- consistent.

  inhabited-consistent : ε ⊢ˢ σ ∷ Γ → Consistent Γ
  inhabited-consistent ⊢σ _ ⊢t = ¬Empty (substitutionTerm ⊢t ⊢σ ε)

opaque

  -- Zero is not judgmentally equal to suc t.

  zero≢suc : ¬ Γ ⊢ zero ≡ suc t ∷ ℕ
  zero≢suc {Γ} {t} =
    Γ ⊢ zero ≡ suc t ∷ ℕ                 →⟨ reducible-⊩≡∷ ⟩
    (∃ λ l → Γ ⊩⟨ l ⟩ zero ≡ suc t ∷ ℕ)  →⟨ ⊩zero≡suc∷ℕ⇔ .proj₁ ∘→ proj₂ ⟩
    ⊥                                    □

zero≢one : Γ ⊢ zero ≡ suc zero ∷ ℕ → ⊥
zero≢one = zero≢suc

opaque

  -- A variant of zero≢suc: the identity type Id ℕ zero (suc t) is not
  -- inhabited in the empty context.

  ¬-Id-ℕ-zero-suc : ¬ ε ⊢ u ∷ Id ℕ zero (suc t)
  ¬-Id-ℕ-zero-suc {u} {t} =
    ε ⊢ u ∷ Id ℕ zero (suc t)  →⟨ ε⊢∷Id→ε⊢≡∷ ⟩
    ε ⊢ zero ≡ suc t ∷ ℕ       →⟨ zero≢suc ⟩
    ⊥                          □
