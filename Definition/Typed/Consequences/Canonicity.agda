------------------------------------------------------------------------
-- Canonicity theorems for natural numbers and the empty type
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Canonicity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
open import Definition.Typed.EqRelInstance R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution.Introductions R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.Relation
open import Tools.Sum

private
  variable
    A t u v : Term _

opaque

  -- Canonicity for natural numbers.

  canonicity : ε ⊢ t ∷ ℕ → ∃ λ n → ε ⊢ t ≡ sucᵏ n ∷ ℕ
  canonicity {t} =
    ε ⊢ t ∷ ℕ                     →⟨ ⊩∷ℕ⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩∷ (inj₂ ε) ⟩
    ε ⊩ℕ t ∷ℕ                     →⟨ lemma ⟩
    (∃ λ n → ε ⊢ t ≡ sucᵏ n ∷ ℕ)  □
    where
    lemma : ε ⊩ℕ u ∷ℕ → ∃ λ n → ε ⊢ u ≡ sucᵏ n ∷ ℕ
    lemma (ℕₜ v u⇒*v _ ⊩v) =
      Σ.map idᶠ (trans (subset*Term u⇒*v))
        (case ⊩v of λ where
           (ne (neNfₜ _ u-ne _)) → ⊥-elim $ noClosedNe u-ne
           zeroᵣ                 → 0 , refl (zeroⱼ ε)
           (sucᵣ ⊩u)             → Σ.map 1+ suc-cong (lemma ⊩u))

opaque

  -- Canonicity for the empty type.

  ¬Empty : ¬ ε ⊢ t ∷ Empty
  ¬Empty {t} =
    ε ⊢ t ∷ Empty      →⟨ ⊩∷Empty⇔ .proj₁ ∘→ proj₂ ∘→ reducible-⊩∷ (inj₂ ε) ⟩
    ε ⊩Empty t ∷Empty  →⟨ (λ { (Emptyₜ _ _ _ (ne (neNfₜ _ u-ne _))) →
                               noClosedNe u-ne }) ⟩
    ⊥                  □

opaque

  -- Every closed equality proof reduces to rfl.

  ε⊢⇒*rfl∷Id : ε ⊢ v ∷ Id A t u → ε ⊢ v ⇒* rfl ∷ Id A t u
  ε⊢⇒*rfl∷Id ⊢v =
    case ⊩∷Id⇔ .proj₁ $ reducible-⊩∷ (inj₂ ε) ⊢v .proj₂ of λ
      (_ , v⇒*w , _ , _ , rest) →
    case rest of λ where
      (rflᵣ _)      → v⇒*w
      (ne _ w-ne _) → ⊥-elim $ noClosedNe w-ne

opaque

  -- If Id A t u is inhabited in the empty context, then t is
  -- definitionally equal to u at type A.

  ε⊢∷Id→ε⊢≡∷ : ε ⊢ v ∷ Id A t u → ε ⊢ t ≡ u ∷ A
  ε⊢∷Id→ε⊢≡∷ {v} {A} {t} {u} =
    ε ⊢ v ∷ Id A t u         →⟨ ε⊢⇒*rfl∷Id ⟩
    ε ⊢ v ⇒* rfl ∷ Id A t u  →⟨ proj₂ ∘→ proj₂ ∘→ syntacticEqTerm ∘→ subset*Term ⟩
    ε ⊢ rfl ∷ Id A t u       →⟨ inversion-rfl-Id ⟩
    ε ⊢ t ≡ u ∷ A            □
