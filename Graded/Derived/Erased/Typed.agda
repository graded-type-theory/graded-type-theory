------------------------------------------------------------------------
-- Some properties related to typing and Erased
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions

module Graded.Derived.Erased.Typed
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Modality 𝕄)
  (R : Type-restrictions M)
  (open Type-restrictions R)
  -- The Unit type is assumed to be allowed.
  (Unit-ok : Unit-allowed)
  -- It is assumed that Σ-types with η-equality are allowed for the
  -- quantities 𝟘 and 𝟘.
  (Σₚ-ok : Σₚ-allowed 𝟘 𝟘)
  where

open import Definition.Typed R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R

open import Definition.Untyped M hiding (_∷_; _[_])

open import Graded.Derived.Erased.Untyped 𝕄

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ       : Con Term _
  A B t u : Term _

-- A formation rule for Erased.

Erasedⱼ : Γ ⊢ A → Γ ⊢ Erased A
Erasedⱼ ⊢A = ΠΣⱼ ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) Σₚ-ok

-- A corresponding congruence rule.

Erased-cong :
  Γ ⊢ A ≡ B →
  Γ ⊢ Erased A ≡ Erased B
Erased-cong A≡B =
  ΠΣ-cong ⊢A A≡B (refl (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok)) Σₚ-ok
  where
  ⊢A = syntacticEq A≡B .proj₁

-- An introduction rule for U.

Erasedⱼ-U : Γ ⊢ A ∷ U → Γ ⊢ Erased A ∷ U
Erasedⱼ-U ⊢A∷U = ΠΣⱼ ⊢A∷U (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) Σₚ-ok
  where
  ⊢A = univ ⊢A∷U

-- A corresponding congruence rule.

Erased-cong-U :
  Γ ⊢ A ≡ B ∷ U →
  Γ ⊢ Erased A ≡ Erased B ∷ U
Erased-cong-U A≡B =
  ΠΣ-cong ⊢A A≡B (refl (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok)) Σₚ-ok
  where
  ⊢A = univ (syntacticEqTerm A≡B .proj₂ .proj₁)

-- An introduction rule for Erased.

[]ⱼ : Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Erased A
[]ⱼ ⊢t = prodⱼ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A) Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) Σₚ-ok
  where
  ⊢A = syntacticTerm ⊢t
  ⊢Γ = wf ⊢A

-- A corresponding congruence rule.

[]-cong :
  Γ ⊢ t ≡ u ∷ A → Γ ⊢ [ t ] ≡ [ u ] ∷ Erased A
[]-cong t≡u =
  prod-cong ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) t≡u
    (refl (starⱼ (wf ⊢A) Unit-ok)) Σₚ-ok
  where
  ⊢A = syntacticEqTerm t≡u .proj₁

-- An elimination rule for Erased.

erasedⱼ : Γ ⊢ t ∷ Erased A → Γ ⊢ erased t ∷ A
erasedⱼ ⊢t = fstⱼ ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) ⊢t
  where
  ⊢A = inversion-ΠΣ (syntacticTerm ⊢t) .proj₁

-- A corresponding congruence rule.

erased-cong : Γ ⊢ t ≡ u ∷ Erased A → Γ ⊢ erased t ≡ erased u ∷ A
erased-cong t≡u = fst-cong ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok) t≡u
  where
  ⊢A = inversion-ΠΣ (syntacticEqTerm t≡u .proj₁) .proj₁

-- A β-rule for Erased.

Erased-β :
  Γ ⊢ t ∷ A →
  Γ ⊢ erased [ t ] ≡ t ∷ A
Erased-β ⊢t =
  Σ-β₁ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A) Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) PE.refl Σₚ-ok
  where
  ⊢A = syntacticTerm ⊢t
  ⊢Γ = wf ⊢A

-- An η-rule for Erased.

Erased-η :
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ u ∷ Erased A →
  Γ ⊢ erased t ≡ erased u ∷ A →
  Γ ⊢ t ≡ u ∷ Erased A
Erased-η ⊢t ⊢u t≡u = Σ-η
  ⊢A Γ∙A⊢Unit ⊢t ⊢u t≡u
  (η-unit (sndⱼ ⊢A Γ∙A⊢Unit ⊢t) (sndⱼ ⊢A Γ∙A⊢Unit ⊢u))
  where
  ⊢A       = syntacticEqTerm t≡u .proj₁
  Γ∙A⊢Unit = Unitⱼ (wf ⊢A ∙ ⊢A) Unit-ok

-- An instance of the η-rule.

[erased] :
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ [ erased t ] ≡ t ∷ Erased A
[erased] ⊢t =
  Erased-η ([]ⱼ (erasedⱼ ⊢t)) ⊢t $
  Erased-β (erasedⱼ ⊢t)
