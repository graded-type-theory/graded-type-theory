------------------------------------------------------------------------
-- A restricted variant of _∷_⊇_, used in the definition of the
-- logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Weakening.Restricted
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel

open import Definition.Typed R
open import Definition.Typed.Weakening R as W using (_»_∷ʷ_⊇_)
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Properties.Well-formed R

open import Definition.Untyped M

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private variable
  m n κ   : Nat
  ξ       : DExt (Term 0) _ _
  ρ ρ₁ ρ₂ : Wk _ _
  ∇ ∇′    : DCon (Term 0) _
  Γ Δ Η   : Con Term _

-- A restricted variant of _∷ʷ_⊇_.

data _»_∷ʷʳ_⊇_ : DCon (Term 0) κ → Wk m n → Con Term m → Con Term n → Set a where
  includedʷʳ : ⦃ inc : Var-included ⦄ → ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » ρ ∷ʷʳ Δ ⊇ Γ
  id         : ∇ »⊢ Γ → ∇ » id ∷ʷʳ Γ ⊇ Γ

opaque

  -- Converts from _∷ʷ_⊇_ to _∷ʷʳ_⊇_.

  ∷ʷ⊇→∷ʷʳ⊇ :
    ⦃ inc : Var-included or-empty Δ ⦄ →
    ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇ » ρ ∷ʷʳ Δ ⊇ Γ
  ∷ʷ⊇→∷ʷʳ⊇ ⦃ inc = possibly-nonempty ⦄ ρ⊇ = includedʷʳ ρ⊇
  ∷ʷ⊇→∷ʷʳ⊇ ⦃ inc = ε                 ⦄ ρ⊇ =
    case W.∷ʷ⊇→∷⊇ ρ⊇ of λ where
      W.id → id (ε (defn-wf (W.wf-∷ʷ⊇ ρ⊇)))

opaque

  -- Converts from _∷ʷʳ_⊇_ to _∷ʷ_⊇_.

  ∷ʷʳ⊇→∷ʷ⊇ : ∇ » ρ ∷ʷʳ Δ ⊇ Γ → ∇ » ρ ∷ʷ Δ ⊇ Γ
  ∷ʷʳ⊇→∷ʷ⊇ (includedʷʳ ρ⊇) = ρ⊇
  ∷ʷʳ⊇→∷ʷ⊇ (id ⊢Γ)         = W.idʷ ⊢Γ

opaque

  -- If there is a _∷ʷʳ_⊇_-weakening from Γ to Δ, then
  -- Var-included or-empty Δ is logically equivalent to
  -- Var-included or-empty Γ.

  wk-Var-included-or-empty :
    ∇ » ρ ∷ʷʳ Δ ⊇ Γ →
    Var-included or-empty Δ ⇔
    Var-included or-empty Γ
  wk-Var-included-or-empty (id _)         = id⇔
  wk-Var-included-or-empty (includedʷʳ _) =
    (λ _ → included) , (λ _ → included)

opaque

  -- A variant of wk-Var-included-or-empty.

  wk-Var-included-or-empty→ :
    ∇ » ρ ∷ʷʳ Δ ⊇ Γ →
    ⦃ inc : Var-included or-empty Δ ⦄ →
    Var-included or-empty Γ
  wk-Var-included-or-empty→ ρ⊇ ⦃ inc ⦄ =
    wk-Var-included-or-empty ρ⊇ .proj₁ inc

opaque

  -- A variant of wk-Var-included-or-empty.

  wk-Var-included-or-empty← :
    ∇ » ρ ∷ʷʳ Δ ⊇ Γ →
    ⦃ inc : Var-included or-empty Γ ⦄ →
    Var-included or-empty Δ
  wk-Var-included-or-empty← ρ⊇ ⦃ inc ⦄ =
    wk-Var-included-or-empty ρ⊇ .proj₂ inc

opaque

  -- If ρ ∷ʷʳ Δ ⊇ Γ holds, then Δ is well-formed.

  wf-∷ʷʳ⊇ : ∇ » ρ ∷ʷʳ Δ ⊇ Γ → ∇ »⊢ Δ
  wf-∷ʷʳ⊇ (includedʷʳ ρ⊇) = W.wf-∷ʷ⊇ ρ⊇
  wf-∷ʷʳ⊇ (id ⊢Γ)         = ⊢Γ

opaque

  -- Composition.

  _•ₜʷʳ_ : ∇ » ρ₁ ∷ʷʳ Η ⊇ Δ → ∇ » ρ₂ ∷ʷʳ Δ ⊇ Γ → ∇ » ρ₁ • ρ₂ ∷ʷʳ Η ⊇ Γ
  id _           •ₜʷʳ ρ₂⊇ = ρ₂⊇
  includedʷʳ ρ₁⊇ •ₜʷʳ ρ₂⊇ = includedʷʳ (ρ₁⊇ W.•ₜʷ ∷ʷʳ⊇→∷ʷ⊇ ρ₂⊇)

opaque

  wk₀∷ʷʳ⊇ :
    ⦃ inc : Var-included or-empty Γ ⦄ →
    ∇ »⊢ Γ → ∇ » wk₀ ∷ʷʳ Γ ⊇ ε
  wk₀∷ʷʳ⊇ ⊢Γ = ∷ʷ⊇→∷ʷʳ⊇ (W.wk₀∷ʷ⊇ ⊢Γ)

opaque

  -- A definitional weakening lemma for _∷ʷʳ_⊇_ weakenings.

  defn-wkWkʷʳ : ξ » ∇′ ⊇ ∇ → ∇ » ρ ∷ʷʳ Δ ⊇ Γ → ∇′ » ρ ∷ʷʳ Δ ⊇ Γ
  defn-wkWkʷʳ ξ⊇ (includedʷʳ ρ) = includedʷʳ (defn-wkWkʷ ξ⊇ ρ)
  defn-wkWkʷʳ ξ⊇ (id ⊢Δ)        = id (defn-wk′ ξ⊇ ⊢Δ)
