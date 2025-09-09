------------------------------------------------------------------------
-- The term formers ω and Ω
------------------------------------------------------------------------

-- Typing rules for the term formers defined in this module can be
-- found in Definition.Typed.Properties.Admissible.Omega, and usage
-- rules can be found in Graded.Derived.Omega.

module Definition.Untyped.Omega {a} (M : Set a) where

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Nat
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality

private variable
  n : Nat
  σ : Subst _ _
  ρ : Wk _ _
  p : M

------------------------------------------------------------------------
-- Term formers

opaque

  -- The term former ω.

  ω : M → Term n
  ω p = lam p (var x0 ∘⟨ p ⟩ var x0)

opaque

  -- The term former Ω.

  Ω : M → Term n
  Ω p = ω p ∘⟨ p ⟩ ω p

------------------------------------------------------------------------
-- Substitution lemmas

opaque
  unfolding ω

  -- A substitution lemma for ω.

  ω-[] : ω p [ σ ] ≡ ω p
  ω-[] = refl

opaque
  unfolding Ω

  -- A substitution lemma for Ω.

  Ω-[] : Ω p [ σ ] ≡ Ω p
  Ω-[] {p} {σ} =
    (ω p [ σ ]) ∘⟨ p ⟩ (ω p [ σ ])  ≡⟨ cong₂ _∘⟨ _ ⟩_ ω-[] ω-[] ⟩
    ω p ∘⟨ p ⟩ ω p                  ∎

------------------------------------------------------------------------
-- Weakening lemmas

opaque

  -- A weakening lemma for ω.

  wk-ω : wk ρ (ω p) ≡ ω p
  wk-ω {ρ} {p} =
    wk ρ (ω p)         ≡⟨ wk≡subst _ _ ⟩
    ω p [ toSubst ρ ]  ≡⟨ ω-[] ⟩
    ω p                ∎

opaque

  -- A weakening lemma for Ω.

  wk-Ω : wk ρ (Ω p) ≡ Ω p
  wk-Ω {ρ} {p} =
    wk ρ (Ω p)         ≡⟨ wk≡subst _ _ ⟩
    Ω p [ toSubst ρ ]  ≡⟨ Ω-[] ⟩
    Ω p                ∎
