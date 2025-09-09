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
  Γ     : Cons _ _
  A     : Term _
  s     : Strength
  l₁ l₂ : Universe-level

opaque
  unfolding Lift

  -- An inversion lemma for Lift.

  inversion-Lift-U :
    Γ ⊢ Lift s l₁ A ∷ U l₂ →
    Lift-allowed s ×
    (⦃ not-ok : No-equality-reflection ⦄ → l₁ ≤ᵘ l₂) ×
    ∃ λ l → Γ ⊢ A ∷ U l ×
      (⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ → l ≤ᵘ l₂)
  inversion-Lift-U {l₁} ⊢Lift =
    let l , l′ , ⊢A , ⊢Unit , U≡U₁ , ok₁ = inversion-ΠΣ-U ⊢Lift
        U≡U₂ , ok₂                       = inversion-Unit-U ⊢Unit

        l⊔l′≡l₂ = λ ok → PE.sym $ U-injectivity ⦃ ok = ok ⦄ U≡U₁
        l′≡l₁   = λ ok → U-injectivity ⦃ ok = ok ⦄ U≡U₂
    in
      (ok₁ , ok₂)
    , PE.subst₂ _≤ᵘ_ (l′≡l₁ included) (l⊔l′≡l₂ included) ≤ᵘ⊔ᵘˡ
    , l
    , ⊢A
    , (λ ⦃ ok = ok ⦄ → PE.subst (l ≤ᵘ_) (l⊔l′≡l₂ ok) ≤ᵘ⊔ᵘʳ)
