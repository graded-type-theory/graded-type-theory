------------------------------------------------------------------------
-- Some properties related to typing and the weak variant of Erased
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions

module Definition.Typed.Properties.Admissible.Erased.No-eta
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Syntactic R

open import Definition.Untyped M hiding (_[_])
open import Definition.Untyped.Erased 𝕄 𝕨 hiding (erased)
open import Definition.Untyped.Erased.No-eta 𝕄

open import Tools.Function
open import Tools.Product

private variable
  Γ         : Con Term _
  A B C t u : Term _

-- A β-rule for Erased.

Erased-β :
  Erasedʷ-allowed →
  Γ ⊢ t ∷ A →
  Γ ⊢ erased A [ t ] ≡ t ∷ A
Erased-β (Unit-ok , Σ-ok) ⊢t =
  fstʷ-β-≡ (Unitⱼ ⊢ΓA Unit-ok) ⊢t (starⱼ ⊢Γ Unit-ok) Σ-ok
  where
  ⊢Γ = wfTerm ⊢t
  ⊢ΓA = ∙ syntacticTerm ⊢t

-- An elimination rule for Erased.

erasedⱼ : Γ ⊢ t ∷ Erased A → Γ ⊢ erased A t ∷ A
erasedⱼ ⊢t = fstʷⱼ ⊢t

-- A corresponding congruence rule.

erased-cong :
  Γ ⊢ A ≡ B → Γ ⊢ t ≡ u ∷ Erased A → Γ ⊢ erased A t ≡ erased B u ∷ A
erased-cong = fstʷ-cong

opaque

  -- An inversion lemma for erased.
  --
  -- TODO: Make it possible to replace the conclusion with
  --
  --   Γ ⊢ t ∷ Erased A × Erased-allowed?
  --
  -- See also ¬-inversion-erased′ and ¬-inversion-erased in
  -- Definition.Typed.Consequences.Inversion.Erased.No-eta.

  inversion-erased :
    Γ ⊢ erased C t ∷ A →
    ∃₂ λ q B → Γ ⊢ t ∷ Σʷ 𝟘 , q ▷ A ▹ B × Σʷ-allowed 𝟘 q
  inversion-erased {C = C} {t} ⊢erased =
    case inversion-fstʷ ⊢erased of λ
      (q , B , ⊢t , A≡C) →
    case inversion-ΠΣ (syntacticTerm ⊢t) of λ
      (_ , ⊢B , Σ-ok) →
    q , B , conv ⊢t (ΠΣ-cong (sym A≡C) (refl ⊢B) Σ-ok) , Σ-ok
