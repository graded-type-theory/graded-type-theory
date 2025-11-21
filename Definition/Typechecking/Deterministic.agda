------------------------------------------------------------------------
-- Type inference is deterministic.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typechecking.Deterministic
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typechecking R
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    t A B : Term n
    Δ : Con Term n
    Γ : Cons m n


deterministic⇉-var : {x : Fin n} → x ∷ A ∈ Δ → x ∷ B ∈ Δ → A PE.≡ B
deterministic⇉-var {x = x0} here here = PE.refl
deterministic⇉-var {x = x +1} (there y) (there z) rewrite deterministic⇉-var y z = PE.refl

-- Type inference is deterministic.

deterministic⇉ : Γ ⊢ t ⇉ A → Γ ⊢ t ⇉ B → A PE.≡ B
deterministic⇉ (Levelᵢ _) (Levelᵢ _) = PE.refl
deterministic⇉ (zeroᵘᵢ _) (zeroᵘᵢ _) = PE.refl
deterministic⇉ (sucᵘᵢ _) (sucᵘᵢ _) = PE.refl
deterministic⇉ (supᵘᵢ _ _) (supᵘᵢ _ _) = PE.refl
deterministic⇉ (Uᵢ x) (Uᵢ y) = PE.refl
deterministic⇉ (Liftᵢ _ x ↘U₁) (Liftᵢ _ y ↘U₂) =
  case deterministic⇉ x y of λ {
    PE.refl →
  case whrDet* ↘U₁ ↘U₂ of λ {
    PE.refl →
  PE.refl }}
deterministic⇉ (ΠΣᵢ A₁ C₁ B₁ _) (ΠΣᵢ A₂ C₂ B₂ _) =
  case deterministic⇉ A₁ A₂ of λ {
    PE.refl →
  case whrDet* C₁ C₂ of λ {
    PE.refl →
  PE.refl }}
deterministic⇉ (varᵢ x) (varᵢ x₁) = deterministic⇉-var x x₁
deterministic⇉ (defnᵢ ↦∷A) (defnᵢ ↦∷A′) =
  PE.cong (wk wk₀) (unique-↦∈ ↦∷A ↦∷A′ PE.refl)
deterministic⇉ (lowerᵢ x y) (lowerᵢ x′ y′) =
  case deterministic⇉ x x′ of λ {
    PE.refl →
  case whrDet* y y′ of λ {
    PE.refl →
  PE.refl }}
deterministic⇉ (appᵢ x x₁ x₂) (appᵢ y x₃ x₄)
  rewrite deterministic⇉ x y
  with B-PE-injectivity BΠ! BΠ! (whrDet* x₁ x₃)
... | PE.refl , PE.refl , _ = PE.refl
deterministic⇉ (fstᵢ x x₁) (fstᵢ y x₂)
  rewrite deterministic⇉ x y
  with B-PE-injectivity BΣ! BΣ! (whrDet* x₁ x₂)
... | PE.refl , PE.refl , _ = PE.refl
deterministic⇉ (sndᵢ x x₁) (sndᵢ y x₂)
  rewrite deterministic⇉ x y
  with B-PE-injectivity BΣ! BΣ! (whrDet* x₁ x₂)
... | PE.refl , PE.refl , _ = PE.refl
deterministic⇉ (prodrecᵢ _ _ _ _) (prodrecᵢ _ _ _ _) = PE.refl
deterministic⇉ ℕᵢ ℕᵢ = PE.refl
deterministic⇉ zeroᵢ zeroᵢ = PE.refl
deterministic⇉ (sucᵢ x) (sucᵢ x₁) = PE.refl
deterministic⇉ (natrecᵢ x x₁ x₂ x₃) (natrecᵢ x₄ x₅ x₆ x₇) = PE.refl
deterministic⇉ (Unitᵢ _) (Unitᵢ _) = PE.refl
deterministic⇉ (starᵢ _) (starᵢ _) = PE.refl
deterministic⇉ (unitrecᵢ _ _ _) (unitrecᵢ _ _ _) = PE.refl
deterministic⇉ Emptyᵢ Emptyᵢ = PE.refl
deterministic⇉ (emptyrecᵢ x x₁) (emptyrecᵢ x₂ x₃) = PE.refl
deterministic⇉ (Idᵢ A₁ B₁ _ _) (Idᵢ A₂ B₂ _ _) =
  case deterministic⇉ A₁ A₂ of λ {
    PE.refl →
  case whrDet* B₁ B₂ of λ {
    PE.refl →
  PE.refl }}
deterministic⇉ (Jᵢ _ _ _ _ _ _) (Jᵢ _ _ _ _ _ _) = PE.refl
deterministic⇉ (Kᵢ _ _ _ _ _ _) (Kᵢ _ _ _ _ _ _) = PE.refl
deterministic⇉ ([]-congᵢ _ _ _ _ _ _) ([]-congᵢ _ _ _ _ _ _) = PE.refl
