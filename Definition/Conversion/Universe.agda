------------------------------------------------------------------------
-- Equal terms of type U are equal types
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality

module Definition.Conversion.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TC : Type-configuration 𝕄)
  where

open Type-configuration TC

open import Definition.Untyped M
open import Definition.Untyped.Whnf M TC⁻
open import Definition.Typed.Properties TC
open import Definition.Conversion TC

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ   : Cons _ _
  A B : Term _
  l   : Lvl _

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
