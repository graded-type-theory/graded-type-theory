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
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Admissible.Lift R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Admissible.Unit R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M hiding (_[_])
open import Definition.Untyped.Erased 𝕄 𝕨 hiding (erased)
open import Definition.Untyped.Erased.No-eta 𝕄
open import Definition.Untyped.Sigma 𝕄

open import Tools.Product

private variable
  Γ                   : Con Term _
  A A₁ A₂ C l t t₁ t₂ : Term _

opaque
  unfolding Erased erased

  -- A typing rule for erased.

  erasedⱼ : Γ ⊢ t ∷ Erased l A → Γ ⊢ erased A t ∷ A
  erasedⱼ = ⊢fst⟨⟩

opaque
  unfolding erased [_]

  -- A β-rule for erased.

  Erased-β :
    Erasedʷ-allowed →
    Γ ⊢ t ∷ A →
    Γ ⊢ erased A [ t ] ≡ t ∷ A
  Erased-β (Unit-ok , Σ-ok) ⊢t =
    let ⊢Γ = wfTerm ⊢t
        ⊢A = wf-⊢∷ ⊢t
    in
    fst⟨⟩-β-≡ (Liftⱼ (⊢zeroᵘ (∙ ⊢A)) (⊢Unit (∙ ⊢A) Unit-ok)) ⊢t
      (liftⱼ′ (⊢zeroᵘ ⊢Γ) (starⱼ ⊢Γ Unit-ok)) Σ-ok

opaque
  unfolding Erased erased

  -- An equality rule for erased.
  --
  -- Note that the assumption of type Γ ⊢ A₁ ≡ A₂ ∷ U l could be
  -- replaced by one of type Γ ⊢ A₁ ≡ A₂. See
  -- Definition.Typed.Properties.Admissible.Erased.Primitive.[]ⱼ for
  -- some motivation.

  erased-cong :
    Γ ⊢ A₁ ≡ A₂ ∷ U l →
    Γ ⊢ t₁ ≡ t₂ ∷ Erased l A₁ →
    Γ ⊢ erased A₁ t₁ ≡ erased A₂ t₂ ∷ A₁
  erased-cong A₁≡A₂ t₁≡t₂ =
    let A₁≡A₂ = univ A₁≡A₂ in
    fst⟨⟩-cong A₁≡A₂ t₁≡t₂

opaque
  unfolding erased fst⟨_⟩

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
  inversion-erased {C} {t} ⊢erased =
    let q , B , ⊢t , A≡C = inversion-fstʷ ⊢erased
        _ , ⊢B , Σ-ok    = inversion-ΠΣ (wf-⊢∷ ⊢t)
    in
    q , B , conv ⊢t (ΠΣ-cong (sym A≡C) (refl ⊢B) Σ-ok) , Σ-ok
