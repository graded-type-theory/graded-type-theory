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

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Consequences.Canonicity R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
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
    m n : Nat
    ∇   : DCon (Term 0) m
    Γ   : Con Term n
    σ   : Subst _ _
    t u : Term n

opaque

  -- If there is some way to instantiate all the types in Γ, then Γ is
  -- consistent.

  inhabited-consistent : ∇ » ε ⊢ˢʷ σ ∷ Γ → Consistent ∇ Γ
  inhabited-consistent ⊢σ _ ⊢t = ¬Empty (subst-⊢∷ ⊢t ⊢σ)

opaque

  -- If equality reflection is not allowed or the context is empty,
  -- then zero is not definitionally equal to suc t.

  zero≢suc :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ¬ ∇ » Γ ⊢ zero ≡ suc t ∷ ℕ
  zero≢suc {Γ} {∇} {t} =
    ∇ » Γ ⊢ zero ≡ suc t ∷ ℕ                 →⟨ reducible-⊩≡∷ ⟩
    (∃ λ l → ∇ » Γ ⊩⟨ l ⟩ zero ≡ suc t ∷ ℕ)  →⟨ ⊩zero≡suc∷ℕ⇔ .proj₁ ∘→ proj₂ ⟩
    ⊥                                        □

opaque

  -- If equality reflection is not allowed or the context is empty,
  -- then zero is not definitionally equal to one.

  zero≢one :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    ¬ ∇ » Γ ⊢ zero ≡ suc zero ∷ ℕ
  zero≢one = zero≢suc

opaque

  -- If equality reflection is allowed, then there is a context for
  -- which zero is definitionally equal to one.

  zero≡one :
    Equality-reflection →
    » ∇ →
    ∃ λ (Γ : Con Term 1) → ∇ » Γ ⊢ zero ≡ suc zero ∷ ℕ
  zero≡one ok »∇ =
    ε ∙ Id ℕ zero (suc zero) ,
    equality-reflection′ ok (var₀ (Idⱼ′ (zeroⱼ (ε »∇)) (sucⱼ (zeroⱼ (ε »∇)))))

opaque

  -- A variant of zero≢suc: the identity type Id ℕ zero (suc t) is not
  -- inhabited in the empty context.

  ¬-Id-ℕ-zero-suc : ¬ ∇ » ε ⊢ u ∷ Id ℕ zero (suc t)
  ¬-Id-ℕ-zero-suc {∇} {u} {t} =
    ∇ » ε ⊢ u ∷ Id ℕ zero (suc t)      →⟨ ε⊢∷Id→ε⊢≡∷ ⟩
    glassify ∇ » ε ⊢ zero ≡ suc t ∷ ℕ  →⟨ zero≢suc ⦃ ok = ε ⦄ ⟩
    ⊥                                  □
