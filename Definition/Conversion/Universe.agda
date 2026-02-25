------------------------------------------------------------------------
-- Equal terms of type U are equal types
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
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed.Properties R
open import Definition.Conversion R

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    Γ     : Cons _ _
    A B l : Term _

-- The relation _⊢_[conv↓]_∷ U l is contained in _⊢_[conv↓]_.

univConv↓ : ∀ {A B}
          → Γ ⊢ A [conv↓] B ∷ U l
          → Γ ⊢ A [conv↓] B
univConv↓ (ne-ins t u () x)
univConv↓ (univ x x₁ x₂) = x₂

opaque

  -- The relation _⊢_[conv↑]_∷ U l is contained in _⊢_[conv↑]_.

  univConv↑ :
    Γ ⊢ A [conv↑] B ∷ U l →
    Γ ⊢ A [conv↑] B
  univConv↑ ([↑]ₜ _ _ _ (U⇒* , _) A↘A′ B↘B′ A′≡B′)
    rewrite PE.sym (whnfRed* U⇒* Uₙ) =
    [↑] _ _ (univ↘ A↘A′) (univ↘ B↘B′) (univConv↓ A′≡B′)
