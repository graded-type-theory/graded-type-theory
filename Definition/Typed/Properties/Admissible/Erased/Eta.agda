------------------------------------------------------------------------
-- Some properties related to typing and the strong variant of Erased
------------------------------------------------------------------------

import Graded.Modality
open import Definition.Typed.Restrictions
open import Tools.Product

module Definition.Typed.Properties.Admissible.Erased.Eta
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (R : Type-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
import Definition.Typed.Properties.Admissible.Erased.Primitive R as ET
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Admissible.Lift R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Admissible.Unit R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M hiding (_[_])
open import Definition.Untyped.Erased 𝕄 𝕤 hiding (erased)
open import Definition.Untyped.Erased.Eta 𝕄
open import Definition.Untyped.Properties M

open import Tools.Function
import Tools.PropositionalEquality as PE
open import Tools.Sum

private variable
  Γ         : Con Term _
  A B l t u : Term _

opaque
  unfolding erased [_]

  -- A β-rule for Erased.

  Erased-β :
    Erasedˢ-allowed →
    Γ ⊢ t ∷ A →
    Γ ⊢ erased [ t ] ≡ t ∷ A
  Erased-β (Unit-ok , Σ-ok) ⊢t =
    let ⊢A = wf-⊢∷ ⊢t
        ⊢Γ = wf ⊢A
    in
    Σ-β₁-≡ (Liftⱼ (⊢zeroᵘ (∙ ⊢A)) (⊢Unit (∙ ⊢A) Unit-ok)) ⊢t
      (liftⱼ′ (⊢zeroᵘ ⊢Γ) (starⱼ ⊢Γ Unit-ok)) Σ-ok

opaque
  unfolding Erased erased

  -- An elimination rule for Erased.

  erasedⱼ : Γ ⊢ t ∷ Erased l A → Γ ⊢ erased t ∷ A
  erasedⱼ ⊢t = fstⱼ′ ⊢t

opaque
  unfolding Erased erased

  -- A corresponding congruence rule.

  erased-cong : Γ ⊢ t ≡ u ∷ Erased l A → Γ ⊢ erased t ≡ erased u ∷ A
  erased-cong t≡u = fst-cong′ t≡u

opaque
  unfolding Erased erased

  -- A definitional η-rule for Erased.

  Erased-η-≡ :
    Γ ⊢ t ∷ Erased l A →
    Γ ⊢ u ∷ Erased l A →
    Γ ⊢ erased t ≡ erased u ∷ A →
    Γ ⊢ t ≡ u ∷ Erased l A
  Erased-η-≡ {l} ⊢t ⊢u t≡u =
    let Unit-ok =
          inversion-Unit $
          inversion-Lift (inversion-ΠΣ (wf-⊢∷ ⊢t) .proj₂ .proj₁) .proj₂
    in
    Σ-η′ ⊢t ⊢u t≡u $
    Lift-η′
      (sndⱼ′ ⊢t)
      (PE.subst (_⊢_∷_ _ _)
         (PE.cong (flip Lift _) $
          PE.trans (wk1-sgSubst l _) $ PE.sym $ wk1-sgSubst _ _) $
       sndⱼ′ ⊢u) $
    η-unit (lowerⱼ (sndⱼ′ ⊢t)) (lowerⱼ (sndⱼ′ ⊢u)) Unit-ok (inj₁ PE.refl)

opaque
  unfolding Erased

  -- Another kind of η-rule.

  [erased] :
    Γ ⊢ l ∷Level →
    Γ ⊢ t ∷ Erased l A →
    Γ ⊢ [ erased t ] ≡ t ∷ Erased l A
  [erased] ⊢l ⊢t =
    let ⊢A , ⊢Lift-Unit , Σ-ok = inversion-ΠΣ (wf-⊢∷ ⊢t)
        _ , ⊢Unit              = inversion-Lift ⊢Lift-Unit
        Erased-ok              = inversion-Unit ⊢Unit , Σ-ok
    in
    Erased-η-≡ (ET.[]ⱼ Erased-ok ⊢l ⊢A (erasedⱼ ⊢t)) ⊢t $
    Erased-β Erased-ok (erasedⱼ ⊢t)

opaque
  unfolding erased

  -- An inversion lemma for erased.
  --
  -- TODO: Make it possible to replace the conclusion with
  --
  --   Γ ⊢ t ∷ Erased A × Erased-allowed?
  --
  -- See also ¬-inversion-erased′ and ¬-inversion-erased in
  -- Definition.Typed.Consequences.Inversion.Erased.Eta.

  inversion-erased :
    Γ ⊢ erased t ∷ A →
    ∃₂ λ q B → Γ ⊢ t ∷ Σˢ 𝟘 , q ▷ A ▹ B × Σˢ-allowed 𝟘 q
  inversion-erased ⊢erased =
    case inversion-fst ⊢erased of λ {
      (_ , C , q , _ , ⊢C , ⊢t , ≡B) →
    case ⊢∷ΠΣ→ΠΣ-allowed ⊢t of λ {
      Σˢ-ok →
      q
    , C
    , conv ⊢t (ΠΣ-cong (_⊢_≡_.sym ≡B) (refl ⊢C) Σˢ-ok)
    , Σˢ-ok }}
