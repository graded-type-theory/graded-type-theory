------------------------------------------------------------------------
-- A variant of Graded.Derived.Erased.Eta.Typed with fewer dependencies
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Product

module Graded.Derived.Erased.Eta.Typed.Primitive
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Modality 𝕄)
  (R : Type-restrictions 𝕄)
  (open Type-restrictions R)
  -- Erased with η-equality is assumed to be allowed.
  ((Unit-ok , Σ-ok) : Erasedˢ-allowed)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R

open import Definition.Untyped M hiding (_∷_; _[_])

open import Graded.Derived.Erased.Eta.Untyped 𝕄
open import Graded.Derived.Erased.Typed.Primitive R (Unit-ok , Σ-ok) public
open import Graded.Derived.Erased.Untyped 𝕄 𝕤 hiding (erased)

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  Γ       : Con Term _
  A B t u : Term _

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
  Σ-β₁ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A) Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) PE.refl Σ-ok
  where
  ⊢Γ = wf ⊢A

-- A definitional η-rule for Erased.

Erased-η-≡ :
  Γ ⊢ A →
  Γ ⊢ t ∷ Erased A →
  Γ ⊢ u ∷ Erased A →
  Γ ⊢ erased t ≡ erased u ∷ A →
  Γ ⊢ t ≡ u ∷ Erased A
Erased-η-≡ ⊢A ⊢t ⊢u t≡u = Σ-η
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
  Erased-η-≡ ⊢A ([]ⱼ ⊢A (erasedⱼ ⊢A ⊢t)) ⊢t $
  Erased-β ⊢A (erasedⱼ ⊢A ⊢t)
