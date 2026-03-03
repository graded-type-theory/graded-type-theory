------------------------------------------------------------------------
-- Typing, equality and reduction rules related to Bool for the theory
-- with nr functions.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Definition.Untyped.Bool.Nr
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Consequences.Admissible.Bool.Nr
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  (open Modality 𝕄)
  (open Definition.Untyped.Bool.Nr 𝕄 𝐌)
  -- It is assumed that the modality has an nr function.
  ⦃ has-nr : Has-nr _ 𝕄 ⦄
  -- It is assumed that certain Σ-types are allowed.
  (Σ-ok : Σʷ-allowed ω Boolᵍ)
  -- It is assumed that weak unit types are allowed.
  (Unitʷ-ok : Unitʷ-allowed)
  where

open import Definition.Typed R
open import Definition.Untyped M

import Definition.Typed.Consequences.Admissible.Bool
  𝐌 R ω Boolᵍ OKᵍ Σ-ok Unitʷ-ok as B

private variable
  Γ                                 : Cons _ _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  p                                : M

-- Export typing rules from Definition.Typed.Consequences.Admissible.Bool
-- except those related to boolrec.

open B public hiding
  (boolrec-cong; ⊢boolrec; boolrec-true-≡; boolrec-false-≡)

------------------------------------------------------------------------
-- Typing rules for boolrec

opaque
  unfolding boolrec

  -- An equality rule for boolrec.

  boolrec-cong :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ A₁ [ true ]₀ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ false ]₀ →
    Γ ⊢ v₁ ≡ v₂ ∷ Bool →
    Γ ⊢ boolrec p A₁ t₁ u₁ v₁ ≡
        boolrec p A₂ t₂ u₂ v₂ ∷ A₁ [ v₁ ]₀
  boolrec-cong = B.boolrec-cong

opaque
  unfolding boolrec

  -- A typing rule for boolrec.

  ⊢boolrec :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ v ∷ Bool →
    Γ ⊢ boolrec p A t u v ∷ A [ v ]₀
  ⊢boolrec = B.⊢boolrec

opaque
  unfolding boolrec

  -- An equality rule for boolrec.

  boolrec-true-≡ :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u true ≡ t ∷ A [ true ]₀
  boolrec-true-≡ = B.boolrec-true-≡

opaque
  unfolding boolrec

  -- An equality rule for boolrec.

  boolrec-false-≡ :
    Π-allowed boolrecᵍ-Π p →
    Π-allowed 𝟙 𝟘 →
    Unitˢ-allowed →
    Γ »∙ Bool ⊢ A →
    Γ ⊢ t ∷ A [ true ]₀ →
    Γ ⊢ u ∷ A [ false ]₀ →
    Γ ⊢ boolrec p A t u false ≡ u ∷ A [ false ]₀
  boolrec-false-≡ = B.boolrec-false-≡
