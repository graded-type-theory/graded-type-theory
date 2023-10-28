------------------------------------------------------------------------
-- Consistency of equality of natural numbers.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Consequences.Consistency
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Consequences.Canonicity R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Empty
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    σ : Subst _ _
    t : Term n

opaque

  -- If there is some way to instantiate all the types in Γ, then Γ is
  -- consistent.

  inhabited-consistent : ε ⊢ˢ σ ∷ Γ → Consistent Γ
  inhabited-consistent ⊢σ _ ⊢t = ¬Empty (substitutionTerm ⊢t ⊢σ ε)

zero≢suc′ : ∀ {l} ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
           → Γ ⊩⟨ l ⟩ zero ≡ suc t ∷ ℕ / ℕ-intr [ℕ] → ⊥
zero≢suc′ (noemb x) (ℕₜ₌ .(suc _) .(suc _) d d′ k≡k′ (sucᵣ x₁))
  with whnfRed*Term (redₜ d) zeroₙ
... | ()
zero≢suc′ (noemb x) (ℕₜ₌ .zero .zero d d′ k≡k′ zeroᵣ)
  with (PE.sym (whnfRed*Term (redₜ d′) sucₙ))
... | ()
zero≢suc′ (noemb x) (ℕₜ₌ k k′ d d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) =
  zero≢ne neK (whnfRed*Term (redₜ d) zeroₙ)
zero≢suc′ (emb 0<1 [ℕ]) n = zero≢suc′ [ℕ] n

-- Zero cannot be judgmentally equal to suc t.
zero≢suc : Γ ⊢ zero ≡ suc t ∷ ℕ → ⊥
zero≢suc 0≡s =
  let [ℕ] , [0≡s] = reducibleEqTerm 0≡s
  in  zero≢suc′ (ℕ-elim [ℕ]) (irrelevanceEqTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [0≡s])

zero≢one : Γ ⊢ zero ≡ suc zero ∷ ℕ → ⊥
zero≢one = zero≢suc
