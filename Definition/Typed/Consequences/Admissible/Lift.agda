------------------------------------------------------------------------
-- An inversion lemma for Lift
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Admissible.Lift
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Consequences.Injectivity R
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
  A     : Term _
  s     : Strength
  l₁ l₂ : Universe-level

opaque
  unfolding Lift

  -- An inversion lemma for Lift.

  inversion-Lift-U :
    Γ ⊢ Lift s l₁ A ∷ U l₂ →
    Lift-allowed s × l₁ ≤ᵘ l₂ × ∃ λ l → Γ ⊢ A ∷ U l × l ≤ᵘ l₂
  inversion-Lift-U {l₁} ⊢Lift =
    let l , l′ , ⊢A , ⊢Unit , U≡U₁ , ok₁ = inversion-ΠΣ-U ⊢Lift
        U≡U₂ , ok₂                       = inversion-Unit-U ⊢Unit
        l⊔l′≡l₂                          = PE.sym $ U-injectivity U≡U₁
        l′≡l₁                            = U-injectivity U≡U₂
    in
      (ok₁ , ok₂)
    , PE.subst₂ _≤ᵘ_ l′≡l₁ l⊔l′≡l₂ ≤ᵘ⊔ᵘˡ
    , l
    , ⊢A
    , PE.subst (l ≤ᵘ_) l⊔l′≡l₂ ≤ᵘ⊔ᵘʳ
