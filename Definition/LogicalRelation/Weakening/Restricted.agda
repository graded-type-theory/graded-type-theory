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
open import Definition.Typed.Weakening R as W using (_∷ʷ_⊇_)

open import Definition.Untyped M

open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Sum

private variable
  m n     : Nat
  ρ ρ₁ ρ₂ : Wk _ _
  Γ Δ Η   : Con Term _

-- A restricted variant of _∷ʷ_⊇_.

data _∷ʷʳ_⊇_ : Wk m n → Con Term m → Con Term n → Set a where
  included : Neutrals-included → ρ ∷ʷ Δ ⊇ Γ → ρ ∷ʷʳ Δ ⊇ Γ
  id       : ⊢ Γ → id ∷ʷʳ Γ ⊇ Γ

opaque

  -- Converts from _∷ʷ_⊇_ to _∷ʷʳ_⊇_.

  ∷ʷ⊇→∷ʷʳ⊇ :
    Neutrals-included-or-empty Δ →
    ρ ∷ʷ Δ ⊇ Γ → ρ ∷ʷʳ Δ ⊇ Γ
  ∷ʷ⊇→∷ʷʳ⊇ (inj₁ inc) ρ⊇ = included inc ρ⊇
  ∷ʷ⊇→∷ʷʳ⊇ (inj₂ ε)   ρ⊇ =
    case W.∷ʷ⊇→∷⊇ ρ⊇ of λ where
      W.id → id ε

opaque

  -- Converts from _∷ʷʳ_⊇_ to _∷ʷ_⊇_.

  ∷ʷʳ⊇→∷ʷ⊇ : ρ ∷ʷʳ Δ ⊇ Γ → ρ ∷ʷ Δ ⊇ Γ
  ∷ʷʳ⊇→∷ʷ⊇ (included _ ρ⊇) = ρ⊇
  ∷ʷʳ⊇→∷ʷ⊇ (id ⊢Γ)         = W.idʷ ⊢Γ

opaque

  -- If there is a _∷ʷʳ_⊇_-weakening from Γ to Δ, then
  -- Neutrals-included-or-empty Δ is logically equivalent to
  -- Neutrals-included-or-empty Γ.

  wk-Neutrals-included-or-empty :
    ρ ∷ʷʳ Δ ⊇ Γ →
    Neutrals-included-or-empty Δ ⇔
    Neutrals-included-or-empty Γ
  wk-Neutrals-included-or-empty (id _)           = id⇔
  wk-Neutrals-included-or-empty (included inc _) =
    (λ _ → inj₁ inc) , (λ _ → inj₁ inc)

opaque

  -- If ρ ∷ʷʳ Δ ⊇ Γ holds, then Δ is well-formed.

  wf-∷ʷʳ⊇ : ρ ∷ʷʳ Δ ⊇ Γ → ⊢ Δ
  wf-∷ʷʳ⊇ (included _ ρ⊇) = W.wf-∷ʷ⊇ ρ⊇
  wf-∷ʷʳ⊇ (id ⊢Γ)         = ⊢Γ

opaque

  -- Composition.

  _•ₜʷʳ_ : ρ₁ ∷ʷʳ Η ⊇ Δ → ρ₂ ∷ʷʳ Δ ⊇ Γ → ρ₁ • ρ₂ ∷ʷʳ Η ⊇ Γ
  id _             •ₜʷʳ ρ₂⊇ = ρ₂⊇
  included inc ρ₁⊇ •ₜʷʳ ρ₂⊇ = included inc (ρ₁⊇ W.•ₜʷ ∷ʷʳ⊇→∷ʷ⊇ ρ₂⊇)
