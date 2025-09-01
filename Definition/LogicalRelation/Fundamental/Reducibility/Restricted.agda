------------------------------------------------------------------------
-- Variants of the lemmas in
-- Definition.LogicalRelation.Fundamental.Reducibility
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Fundamental.Reducibility.Restricted
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.LogicalRelation.Hidden.Restricted R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Substitution R

open import Tools.Product

private variable
  Γ       : Cons _ _
  A B t u : Term _

opaque

  -- Well-formed types are reducible.

  reducible-⊩ : Γ ⊢ A → ∃ λ l → Γ ⊩⟨ l ⟩ A
  reducible-⊩ ⊢A = _ , ⊩ᵛ→⊩ (fundamental-⊩ᵛ ⊢A .proj₂)

opaque

  -- If A and B are definitionally equal (with respect to Γ), then
  -- Γ ⊩⟨ l ⟩ A ≡ B holds for some type level l.

  reducible-⊩≡ : Γ ⊢ A ≡ B → ∃ λ l → Γ ⊩⟨ l ⟩ A ≡ B
  reducible-⊩≡ ⊢A≡B = _ , ⊩ᵛ≡→⊩≡ (fundamental-⊩ᵛ≡ ⊢A≡B .proj₂)

opaque

  -- Well-formed terms are reducible.

  reducible-⊩∷ : Γ ⊢ t ∷ A → ∃ λ l → Γ ⊩⟨ l ⟩ t ∷ A
  reducible-⊩∷ ⊢t∷A = _ , ⊩ᵛ∷→⊩∷ (fundamental-⊩ᵛ∷ ⊢t∷A .proj₂)

opaque

  -- If t and u are definitionally equal (with respect to Γ and A),
  -- then Γ ⊩⟨ l ⟩ t ≡ u ∷ A holds for some type level l.

  reducible-⊩≡∷ : Γ ⊢ t ≡ u ∷ A → ∃ λ l → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  reducible-⊩≡∷ ⊢t≡u∷A = _ , ⊩ᵛ≡∷→⊩≡∷ (fundamental-⊩ᵛ≡∷ ⊢t≡u∷A .proj₂)
