------------------------------------------------------------------------
-- A variant of Graded.Derived.Erased.Typed with fewer dependencies
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Product

module Graded.Derived.Erased.Typed.Primitive
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- Erased is assumed to be allowed.
  ((Unit-ok , Σₚ-ok) : Erased-allowed)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R

open import Definition.Untyped M hiding (_∷_; _[_])

open import Graded.Derived.Erased.Untyped 𝕄

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  Γ       : Con Term _
  A B t u : Term _

-- A formation rule for Erased.

Erasedⱼ : Γ ⊢ A → Γ ⊢ Erased A
Erasedⱼ ⊢A = ΠΣⱼ ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) Σₚ-ok

-- A corresponding congruence rule.

Erased-cong :
  Γ ⊢ A →
  Γ ⊢ A ≡ B →
  Γ ⊢ Erased A ≡ Erased B
Erased-cong ⊢A A≡B =
  ΠΣ-cong ⊢A A≡B (refl (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok)) Σₚ-ok

-- An introduction rule for U.

Erasedⱼ-U :
  Γ ⊢ A → Γ ⊢ A ∷ U → Γ ⊢ Erased A ∷ U
Erasedⱼ-U ⊢A ⊢A∷U = ΠΣⱼ ⊢A∷U (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) Σₚ-ok

-- A corresponding congruence rule.

Erased-cong-U :
  Γ ⊢ A →
  Γ ⊢ A ≡ B ∷ U →
  Γ ⊢ Erased A ≡ Erased B ∷ U
Erased-cong-U ⊢A A≡B =
  ΠΣ-cong ⊢A A≡B (refl (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok)) Σₚ-ok

-- An introduction rule for Erased.

[]ⱼ :
  Γ ⊢ A →
  Γ ⊢ t ∷ A →
  Γ ⊢ [ t ] ∷ Erased A
[]ⱼ ⊢A ⊢t =
  prodⱼ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A) Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) Σₚ-ok
  where
  ⊢Γ = wf ⊢A

-- A corresponding congruence rule.

[]-cong′ :
  Γ ⊢ A →
  Γ ⊢ t ≡ u ∷ A →
  Γ ⊢ [ t ] ≡ [ u ] ∷ Erased A
[]-cong′ ⊢A t≡u =
  prod-cong ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) t≡u
    (refl (starⱼ (wf ⊢A) Unit-ok)) Σₚ-ok

-- An elimination rule for Erased.

erasedⱼ :
  Γ ⊢ A →
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ erased t ∷ A
erasedⱼ ⊢A ⊢t = fstⱼ ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) ⊢t

-- A corresponding congruence rule.

erased-cong :
  Γ ⊢ A →
  Γ ⊢ t ≡ u ∷ Erased A →
  Γ ⊢ erased t ≡ erased u ∷ A
erased-cong ⊢A t≡u = fst-cong ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) t≡u

-- A β-rule for Erased.

Erased-β :
  Γ ⊢ A →
  Γ ⊢ t ∷ A →
  Γ ⊢ erased [ t ] ≡ t ∷ A
Erased-β ⊢A ⊢t =
  Σ-β₁ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A) Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) PE.refl Σₚ-ok
  where
  ⊢Γ = wf ⊢A

-- An η-rule for Erased.

Erased-η :
  Γ ⊢ A →
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ u ∷ Erased A →
  Γ ⊢ erased t ≡ erased u ∷ A →
  Γ ⊢ t ≡ u ∷ Erased A
Erased-η ⊢A ⊢t ⊢u t≡u = Σ-η
  ⊢A Γ∙A⊢Unit ⊢t ⊢u t≡u
  (η-unit (sndⱼ ⊢A Γ∙A⊢Unit ⊢t) (sndⱼ ⊢A Γ∙A⊢Unit ⊢u))
  where
  Γ∙A⊢Unit = Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok

-- An instance of the η-rule.

[erased] :
  Γ ⊢ A →
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ [ erased t ] ≡ t ∷ Erased A
[erased] ⊢A ⊢t =
  Erased-η ⊢A ([]ⱼ ⊢A (erasedⱼ ⊢A ⊢t)) ⊢t $
  Erased-β ⊢A (erasedⱼ ⊢A ⊢t)
