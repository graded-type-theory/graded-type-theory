{-# OPTIONS --without-K --safe #-}

open import Tools.Relation

module Definition.Conversion.Universe {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ using () renaming (Carrier to M)

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed.Properties M′
open import Definition.Typed.RedSteps M′
open import Definition.Conversion M′
open import Definition.Conversion.Reduction M′
open import Definition.Conversion.Lift M′

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
