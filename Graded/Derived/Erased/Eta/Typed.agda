------------------------------------------------------------------------
-- Some properties related to typing and the strong variant of Erased
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Product

module Graded.Derived.Erased.Eta.Typed
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M hiding (_[_])
open import Definition.Untyped.Erased 𝕄 𝕤 hiding (erased)
open import Definition.Untyped.Erased.Eta 𝕄

import Graded.Derived.Erased.Typed.Primitive R as ET

open import Tools.Function
import Tools.PropositionalEquality as PE
open import Tools.Sum

private variable
  Γ       : Con Term _
  A B t u : Term _

opaque

  -- A β-rule for Erased.

  Erased-β :
    Erasedˢ-allowed →
    Γ ⊢ t ∷ A →
    Γ ⊢ erased [ t ] ≡ t ∷ A
  Erased-β (Unit-ok , Σ-ok) ⊢t =
    let ⊢A = wf-⊢∷ ⊢t in
    Σ-β₁-≡ (Unitⱼ (∙ ⊢A) Unit-ok) ⊢t (starⱼ (wf ⊢A) Unit-ok) Σ-ok

opaque

  -- An elimination rule for Erased.

  erasedⱼ : Γ ⊢ t ∷ Erased A → Γ ⊢ erased t ∷ A
  erasedⱼ ⊢t = fstⱼ′ ⊢t

opaque

  -- A corresponding congruence rule.

  erased-cong : Γ ⊢ t ≡ u ∷ Erased A → Γ ⊢ erased t ≡ erased u ∷ A
  erased-cong t≡u = fst-cong′ t≡u

opaque

  -- A definitional η-rule for Erased.

  Erased-η-≡ :
    Γ ⊢ t ∷ Erased A →
    Γ ⊢ u ∷ Erased A →
    Γ ⊢ erased t ≡ erased u ∷ A →
    Γ ⊢ t ≡ u ∷ Erased A
  Erased-η-≡ ⊢t ⊢u t≡u =
    Σ-η′ ⊢t ⊢u t≡u (η-unit (sndⱼ′ ⊢t) (sndⱼ′ ⊢u) (inj₁ PE.refl))

opaque

  -- An instance of the η-rule.

  [erased] :
    Γ ⊢ t ∷ Erased A →
    Γ ⊢ [ erased t ] ≡ t ∷ Erased A
  [erased] ⊢t =
    let ⊢A , ⊢Unit , Σˢ-ok = inversion-ΠΣ (wf-⊢∷ ⊢t)
        Erased-ok          = inversion-Unit ⊢Unit , Σˢ-ok
    in
    Erased-η-≡ (ET.[]ⱼ Erased-ok ⊢A (erasedⱼ ⊢t)) ⊢t $
    Erased-β Erased-ok (erasedⱼ ⊢t)
