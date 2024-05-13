------------------------------------------------------------------------
-- Equal terms of type U are equal types.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Conversion.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Conversion R
open import Definition.Conversion.Reduction R
open import Definition.Conversion.Lift R

open import Tools.Nat
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Algorithmic equality of terms in WHNF of type U are equal as types.
univConv↓ : ∀ {A B}
          → Γ ⊢ A [conv↓] B ∷ U
          → Γ ⊢ A [conv↓] B
univConv↓ (ne-ins t u () x)
univConv↓ (univ x x₁ x₂) = x₂

-- Algorithmic equality of terms of type U are equal as types.
univConv↑ : ∀ {A B}
      → Γ ⊢ A [conv↑] B ∷ U
      → Γ ⊢ A [conv↑] B
univConv↑ ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
      rewrite PE.sym (whnfRed* D Uₙ) =
  reductionConv↑ (univ* d) (univ* d′) (liftConv (univConv↓ t<>u))
