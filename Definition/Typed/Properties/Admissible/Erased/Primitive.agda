------------------------------------------------------------------------
-- Some properties related to typing and Erased
------------------------------------------------------------------------

-- Note that lemmas corresponding to the lemmas in this module, but
-- with fewer arguments, can (at the time of writing) be found in
-- Definition.Typed.Properties.Admissible.Erased.

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
open import Definition.Typed.Properties.Admissible.Sigma.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Substitution.Primitive.Primitive R
open import Definition.Typed.Weakening R

open import Definition.Untyped M hiding (_[_])
open import Definition.Untyped.Erased 𝕄 s
open import Definition.Untyped.Properties M

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  Γ                       : Con Term _
  A A₁ A₂ l l₁ l₂ t t₁ t₂ : Term _

opaque
  unfolding Erased

  -- An introduction rule for U for Erased.

  Erasedⱼ-U :
    Γ ⊢ l ∷ Level →
    Γ ⊢ A ∷ U l →
    Γ ⊢ Erased l A ∷ U l
  Erasedⱼ-U ⊢l ⊢A =
    let ⊢A′ = univ ⊢A
        ⊢l′ = wkTerm₁ ⊢A′ ⊢l
    in
    ΠΣⱼ ⊢l ⊢A
      (conv
         (_⊢_∷_.Liftⱼ (zeroᵘⱼ (∙ ⊢A′)) ⊢l′ $
          Unitⱼ (∙ ⊢A′) Unit-ok)
         (U-cong (supᵘ-zeroˡ ⊢l′)))
      Σ-ok

opaque
  unfolding Erased

  -- An equality rule for U for Erased.

  Erased-cong-U :
    Γ ⊢ l₁ ∷ Level →
    Γ ⊢ l₁ ≡ l₂ ∷ Level →
    Γ ⊢ A₁ →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
    Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂ ∷ U l₁
  Erased-cong-U ⊢l₁ l₁≡l₂ ⊢A₁ A₁≡A₂ =
    let ⊢l₁′ = wkTerm₁ ⊢A₁ ⊢l₁
    in
    ΠΣ-cong ⊢l₁ A₁≡A₂
      (conv
         (_⊢_≡_∷_.Lift-cong (zeroᵘⱼ (∙ ⊢A₁)) (wkEqTerm₁ ⊢A₁ l₁≡l₂) $
          refl (Unitⱼ (∙ ⊢A₁) Unit-ok))
         (U-cong (supᵘ-zeroˡ ⊢l₁′)))
      Σ-ok

opaque

  -- A formation rule for Erased.

  Erasedⱼ :
    Γ ⊢ l ∷ Level →
    Γ ⊢ A ∷ U l →
    Γ ⊢ Erased l A
  Erasedⱼ ⊢l ⊢A = univ (Erasedⱼ-U ⊢l ⊢A)

opaque

  -- An equality rule for Erased.

  Erased-cong :
    Γ ⊢ l₁ ∷ Level →
    Γ ⊢ l₁ ≡ l₂ ∷ Level →
    Γ ⊢ A₁ →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
    Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂
  Erased-cong ⊢l₁ l₁≡l₂ ⊢A₁ A₁≡A₂ =
    univ (Erased-cong-U ⊢l₁ l₁≡l₂ ⊢A₁ A₁≡A₂)

opaque
  unfolding Erased [_]

  -- An introduction rule for Erased.
  --
  -- Note that the assumption of type Γ ⊢ A ∷ U l could be replaced by
  -- one of type Γ ⊢ A. The current type signature is used for the
  -- following reasons:
  --
  -- * This is more in line with the type of the corresponding Agda
  --   construction.
  --
  -- * If the implementation of Erased or [_] is changed, or they are
  --   turned into primitives, then fewer changes might be needed.

  []ⱼ :
    Γ ⊢ l ∷ Level →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t ∷ A →
    Γ ⊢ [ t ] ∷ Erased l A
  []ⱼ ⊢l ⊢A ⊢t =
    let ⊢A    = univ ⊢A
        ⊢Γ    = wfTerm ⊢l
        ⊢Unit = Unitⱼ ⊢Γ Unit-ok
    in
    prodⱼ (Liftⱼ (wkTerm₁ ⊢A ⊢l) (wk₁ ⊢A ⊢Unit)) ⊢t
      (liftⱼ (PE.subst (flip (_⊢_∷_ _) _) (PE.sym $ wk1-sgSubst _ _) ⊢l)
         ⊢Unit (starⱼ ⊢Γ Unit-ok))
      Σ-ok

opaque
  unfolding Erased [_]

  -- An equality rule for Erased.
  --
  -- Note that the assumption of type Γ ⊢ A ∷ U l could be replaced by
  -- one of type Γ ⊢ A.

  []-cong′ :
    Γ ⊢ l ∷ Level →
    Γ ⊢ A ∷ U l →
    Γ ⊢ t₁ ∷ A →
    Γ ⊢ t₂ ∷ A →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ [ t₁ ] ≡ [ t₂ ] ∷ Erased l A
  []-cong′ ⊢l ⊢A ⊢t₁ ⊢t₂ t₁≡t₂ =
    let ⊢A    = univ ⊢A
        ⊢Γ    = wfTerm ⊢l
        ⊢Unit = Unitⱼ ⊢Γ Unit-ok
        ⊢star = starⱼ ⊢Γ Unit-ok
    in
    prod-cong (Liftⱼ (wkTerm₁ ⊢A ⊢l) (wk₁ ⊢A ⊢Unit)) t₁≡t₂
      (lift-cong
         (PE.subst (flip (_⊢_∷_ _) _) (PE.sym $ wk1-sgSubst _ _) ⊢l)
         ⊢Unit ⊢star ⊢star (refl ⊢star))
      Σ-ok
