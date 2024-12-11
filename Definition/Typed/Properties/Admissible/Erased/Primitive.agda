------------------------------------------------------------------------
-- A variant of Definition.Typed.Properties.Admissible.Erased with
-- fewer dependencies
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Product

module Definition.Typed.Properties.Admissible.Erased.Primitive
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- Erased is assumed to be allowed.
  {s}
  ((Unit-ok , Σ-ok) : Erased-allowed s)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R

open import Definition.Untyped M hiding (_[_])
open import Definition.Untyped.Erased 𝕄 s

open import Tools.Function
open import Tools.Nat
import Tools.PropositionalEquality as PE

private variable
  Γ       : Con Term _
  A B l t u : Term _

-- A formation rule for Erased.

Erasedⱼ : Γ ⊢ A → Γ ⊢ Erased A
Erasedⱼ ⊢A = ΠΣⱼ (Unitⱼ (zeroᵘⱼ (∙ ⊢A)) Unit-ok) Σ-ok

-- A corresponding congruence rule.

Erased-cong :
  Γ ⊢ A →
  Γ ⊢ A ≡ B →
  Γ ⊢ Erased A ≡ Erased B
Erased-cong ⊢A A≡B =
  ΠΣ-cong A≡B (refl (Unitⱼ (zeroᵘⱼ (∙ ⊢A)) Unit-ok)) Σ-ok

opaque

  -- An introduction rule for U.

  Erasedⱼ-U :
    Γ ⊢ l ∷ Level →
    Γ ⊢ A →
    Γ ⊢ A ∷ U l →
    Γ ⊢ Erased A ∷ U l
  Erasedⱼ-U ⊢l ⊢A ⊢A∷U = conv (ΠΣⱼ ⊢l (zeroᵘⱼ (wf ⊢A)) ⊢A∷U (Unitⱼ (zeroᵘⱼ (∙ ⊢A)) Unit-ok) Σ-ok) {!   !}

-- A corresponding congruence rule.

Erased-cong-U :
  Γ ⊢ l ∷ Level →
  Γ ⊢ A →
  Γ ⊢ A ≡ B ∷ U l →
  Γ ⊢ Erased A ≡ Erased B ∷ U l
Erased-cong-U ⊢l ⊢A A≡B =
  conv (ΠΣ-cong ⊢l (zeroᵘⱼ (wf ⊢A)) A≡B (refl (Unitⱼ (zeroᵘⱼ (∙ ⊢A)) Unit-ok)) Σ-ok) {!   !}

-- An introduction rule for Erased.

[]ⱼ :
  Γ ⊢ A →
  Γ ⊢ t ∷ A →
  Γ ⊢ [ t ] ∷ Erased A
[]ⱼ ⊢A ⊢t =
  prodⱼ (Unitⱼ (zeroᵘⱼ (∙ ⊢A)) Unit-ok) ⊢t (starⱼ (zeroᵘⱼ ⊢Γ) Unit-ok) Σ-ok
  where
  ⊢Γ = wf ⊢A

-- A corresponding congruence rule.

[]-cong′ :
  Γ ⊢ A →
  Γ ⊢ t ≡ u ∷ A →
  Γ ⊢ [ t ] ≡ [ u ] ∷ Erased A
[]-cong′ ⊢A t≡u =
  prod-cong (Unitⱼ (zeroᵘⱼ (∙ ⊢A)) Unit-ok) t≡u (refl (starⱼ (zeroᵘⱼ (wf ⊢A)) Unit-ok))
    Σ-ok
