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

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed.Properties R
open import Definition.Typed.RedSteps R
open import Definition.Conversion R
open import Definition.Conversion.Reduction R
open import Definition.Conversion.Lift R

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    l : Universe-level

-- The relation _⊢_[conv↓]_∷ U l is contained in _⊢_[conv↓]_.

univConv↓ : ∀ {A B}
          → Γ ⊢ A [conv↓] B ∷ U l
          → Γ ⊢ A [conv↓] B
univConv↓ (ne-ins t u () x)
univConv↓ (univ x x₁ x₂) = x₂

-- The relation _⊢_[conv↑]_∷ U l is contained in _⊢_[conv↑]_.

univConv↑ : ∀ {A B}
      → Γ ⊢ A [conv↑] B ∷ U l
      → Γ ⊢ A [conv↑] B
univConv↑ ([↑]ₜ _ _ _ (D , _) (d , _) (d′ , _) t<>u)
      rewrite PE.sym (whnfRed* D Uₙ) =
  reductionConv↑ (univ* d) (univ* d′) (liftConv (univConv↓ t<>u))
