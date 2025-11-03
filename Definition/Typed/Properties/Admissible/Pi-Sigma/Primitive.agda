------------------------------------------------------------------------
-- Some admissible rules related to Π and Σ
------------------------------------------------------------------------

-- Note that lemmas corresponding to the lemmas in this module, but
-- with fewer arguments, can (at the time of writing) be found in
-- Definition.Typed.Properties.Admissible.Pi-Sigma.

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Pi-Sigma.Primitive
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Lift M
open import Definition.Untyped.Pi-Sigma M
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Weakening R
open import Definition.Typed.Properties.Admissible.Level.Primitive R
open import Definition.Typed.Properties.Admissible.Lift.Primitive R

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  Γ                                     : Con _ _
  A A₁ A₂ B B₁ B₂ l₁ l₁₁ l₁₂ l₂ l₂₁ l₂₂ : Term _
  p q                                   : M
  b                                     : BinderMode

------------------------------------------------------------------------
-- Some admissible rules for ΠΣʰ

opaque
  unfolding ΠΣʰ lower₀

  -- An admissible typing rule for ΠΣʰ.

  ΠΣʰⱼ :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ A ∷ U l₁ →
    Γ ∙ A ⊢ B ∷ U (wk1 l₂) →
    ΠΣ-allowed b p q →
    Γ ⊢ ΠΣʰ b p q l₁ l₂ A B ∷ U (l₁ supᵘₗ l₂)
  ΠΣʰⱼ ⊢l₁ ⊢l₂ ⊢A ⊢B ok =
    let ⊢Lift-A = Liftⱼ ⊢l₁ ⊢l₂ ⊢A in
    ΠΣⱼ (⊢supᵘₗ ⊢l₁ ⊢l₂) ⊢Lift-A
      (PE.subst (_⊢_∷_ _ _) (PE.cong U $ PE.sym wk-supᵘₗ) $
       Liftⱼ-comm (wkLevel₁ (univ ⊢Lift-A) ⊢l₂)
         (wkLevel₁ (univ ⊢Lift-A) ⊢l₁)
         (PE.subst (_⊢_∷_ _ _) wk[]′-[]↑ $
          lower₀Term ⊢l₂ ⊢B))
      ok

opaque
  unfolding ΠΣʰ lower₀

  -- An admissible equality rule for ΠΣʰ.

  ΠΣʰ-cong :
    Γ ⊢ l₁₁ ∷Level →
    Γ ⊢ l₂₁ ∷Level →
    Γ ⊢ l₁₁ ≡ l₁₂ ∷Level →
    Γ ⊢ l₂₁ ≡ l₂₂ ∷Level →
    Γ ⊢ A₁ →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁₁ →
    Γ ∙ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk1 l₂₁) →
    ΠΣ-allowed b p q →
    Γ ⊢ ΠΣʰ b p q l₁₁ l₂₁ A₁ B₁ ≡ ΠΣʰ b p q l₁₂ l₂₂ A₂ B₂ ∷
      U (l₁₁ supᵘₗ l₂₁)
  ΠΣʰ-cong ⊢l₁₁ ⊢l₂₁ l₁₁≡l₁₂ l₂₁≡l₂₂ ⊢A₁ A₁≡A₂ B₁≡B₂ ok =
    let ⊢Lift-A₁ = Liftⱼ ⊢l₂₁ ⊢A₁ in
    ΠΣ-cong (⊢supᵘₗ ⊢l₁₁ ⊢l₂₁)
      (Lift-cong ⊢l₁₁ ⊢l₂₁ l₂₁≡l₂₂ A₁≡A₂)
      (PE.subst (_⊢_≡_∷_ _ _ _) (PE.cong U $ PE.sym wk-supᵘₗ) $
       Lift-cong-comm (wkLevel₁ ⊢Lift-A₁ ⊢l₂₁) (wkLevel₁ ⊢Lift-A₁ ⊢l₁₁)
         (wkEqLevel₁ ⊢Lift-A₁ l₁₁≡l₁₂)
         (PE.subst (_⊢_≡_∷_ _ _ _) wk[]′-[]↑ $
          lower₀TermEq ⊢l₂₁ B₁≡B₂))
      ok
