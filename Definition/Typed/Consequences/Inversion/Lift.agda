------------------------------------------------------------------------
-- An inversion lemma for Lift
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Inversion.Lift
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R

open import Definition.Untyped M
open import Definition.Untyped.Lift 𝕄
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ     : Con Term _
  A t u : Term _
  s     : Strength

opaque
  unfolding Lift

  -- An inversion lemma for Lift.

  inversion-Lift-U :
    Γ ⊢ Lift s t A ∷ U u →
    Lift-allowed s ×
    Γ ∙ A ⊢ wk1 t ∷ Level ×
    ∃₂ λ v w → Γ ⊢ A ∷ U v ×
      (⦃ ok : No-equality-reflection or-empty Γ ⦄ →
       Γ ⊢ u ≡ v maxᵘ w ∷ Level) ×
      (⦃ ok : No-equality-reflection ⦄ →
       Γ ∙ A ⊢ wk1 w ≡ wk1 t ∷ Level)
  inversion-Lift-U ⊢Lift =
    let v , w , ⊢A , ⊢Unit , U≡U₁ , ok₁ = inversion-ΠΣ-U ⊢Lift
        ⊢wk1-t , U≡U₂ , ok₂             = inversion-Unit-U ⊢Unit
    in
      (ok₁ , ok₂) , ⊢wk1-t , v , w , ⊢A
    , U-injectivity U≡U₁
    , U-injectivity ⦃ ok = possibly-nonempty ⦄ U≡U₂
