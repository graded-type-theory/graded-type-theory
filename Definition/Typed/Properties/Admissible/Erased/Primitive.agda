------------------------------------------------------------------------
-- Some properties related to typing and Erased
------------------------------------------------------------------------

-- Note that lemmas corresponding to the lemmas in this module, in
-- some cases with fewer arguments, can (at the time of writing) be
-- found in Definition.Typed.Properties.Admissible.Erased.

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
open import Definition.Typed.Properties.Admissible.Level.Primitive R
open import Definition.Typed.Properties.Admissible.U.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Substitution.Primitive.Primitive R
open import Definition.Typed.Weakening R

open import Definition.Untyped M hiding (_[_])
open import Definition.Untyped.Erased 𝕄 s
open import Definition.Untyped.Properties M

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  Γ                       : Cons _ _
  A A₁ A₂ l l₁ l₂ t t₁ t₂ : Term _

opaque
  unfolding Erased

  -- A formation rule for Erased.

  Erasedⱼ′ :
    Γ »∙ A ⊢ wk1 l ∷Level →
    Γ ⊢ Erased l A
  Erasedⱼ′ ⊢l =
    ΠΣⱼ (Liftⱼ ⊢l (univ (Unitⱼ (wfLevel ⊢l) Unit-ok))) Σ-ok

opaque

  -- A variant of Erasedⱼ′.

  Erasedⱼ :
    Γ ⊢ l ∷Level →
    Γ ⊢ A →
    Γ ⊢ Erased l A
  Erasedⱼ ⊢l ⊢A = Erasedⱼ′ (wkLevel₁ ⊢A ⊢l)

opaque
  unfolding Erased

  -- An equality rule for Erased.

  Erased-cong′ :
    Γ »∙ A₁ ⊢ wk1 l₁ ≡ wk1 l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂
  Erased-cong′ l₁≡l₂ A₁≡A₂ =
    ΠΣ-cong A₁≡A₂
      (Lift-cong l₁≡l₂ (refl (univ (Unitⱼ (wfEqLevel l₁≡l₂) Unit-ok))))
      Σ-ok

opaque

  -- A variant of Erased-cong′.

  Erased-cong :
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ A₁ →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂
  Erased-cong l₁≡l₂ ⊢A₁ =
    Erased-cong′ (wkEqLevel₁ ⊢A₁ l₁≡l₂)

opaque
  unfolding Erased

  -- An introduction rule for U for Erased.

  Erasedⱼ-U :
    Γ ⊢ l ∷Level →
    Γ ⊢ A ∷ U l →
    Γ ⊢ Erased l A ∷ U l
  Erasedⱼ-U ⊢l ⊢A =
    let ⊢A′ = univ ⊢A
        ⊢l′ = wkLevel₁ ⊢A′ ⊢l
    in
    ΠΣⱼ ⊢l ⊢A
      (conv
         (_⊢_∷_.Liftⱼ (⊢zeroᵘ (∙ ⊢A′)) ⊢l′ $
          Unitⱼ (∙ ⊢A′) Unit-ok)
         (U-cong-⊢≡ (supᵘₗ-identityˡ ⊢l′)))
      Σ-ok

opaque
  unfolding Erased

  -- An equality rule for U for Erased.

  Erased-cong-U′ :
    Γ ⊢ l₁ ∷Level →
    Γ »∙ A₁ ⊢ wk1 l₁ ≡ wk1 l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
    Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂ ∷ U l₁
  Erased-cong-U′ ⊢l₁ l₁≡l₂ A₁≡A₂ =
    let ⊢∙A₁ = wfEqLevel l₁≡l₂
        ⊢l₁′ = wkLevel₁ (⊢∙→⊢ ⊢∙A₁) ⊢l₁
    in
    ΠΣ-cong ⊢l₁ A₁≡A₂
      (conv
         (_⊢_≡_∷_.Lift-cong (⊢zeroᵘ ⊢∙A₁) ⊢l₁′ l₁≡l₂ $
          refl (Unitⱼ ⊢∙A₁ Unit-ok))
         (U-cong-⊢≡ (supᵘₗ-identityˡ ⊢l₁′)))
      Σ-ok

opaque

  -- A variant of Erased-cong-U′.

  Erased-cong-U :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ A₁ →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
    Γ ⊢ Erased l₁ A₁ ≡ Erased l₂ A₂ ∷ U l₁
  Erased-cong-U ⊢l₁ l₁≡l₂ ⊢A₁ =
    Erased-cong-U′ ⊢l₁ (wkEqLevel₁ ⊢A₁ l₁≡l₂)

opaque
  unfolding Erased [_]

  -- An introduction rule for Erased.

  []ⱼ :
    Γ ⊢ l ∷Level →
    Γ ⊢ A →
    Γ ⊢ t ∷ A →
    Γ ⊢ [ t ] ∷ Erased l A
  []ⱼ ⊢l ⊢A ⊢t =
    let ⊢Γ    = wfTerm ⊢t
        ⊢Unit = univ (Unitⱼ ⊢Γ Unit-ok)
    in
    prodⱼ (Liftⱼ (wkLevel₁ ⊢A ⊢l) (wk₁ ⊢A ⊢Unit)) ⊢t
      (liftⱼ (PE.subst (_⊢_∷Level _) (PE.sym $ wk1-sgSubst _ _) ⊢l)
         ⊢Unit (starⱼ ⊢Γ Unit-ok))
      Σ-ok

opaque
  unfolding Erased [_]

  -- An equality rule for Erased.

  []-cong′ :
    Γ ⊢ l ∷Level →
    Γ ⊢ A →
    Γ ⊢ t₁ ≡ t₂ ∷ A →
    Γ ⊢ [ t₁ ] ≡ [ t₂ ] ∷ Erased l A
  []-cong′ ⊢l ⊢A t₁≡t₂ =
    let ⊢Γ    = wf ⊢A
        ⊢Unit = univ (Unitⱼ ⊢Γ Unit-ok)
        ⊢star = starⱼ ⊢Γ Unit-ok
    in
    prod-cong (Liftⱼ (wkLevel₁ ⊢A ⊢l) (wk₁ ⊢A ⊢Unit)) t₁≡t₂
      (lift-cong
         (PE.subst (_⊢_∷Level _) (PE.sym $ wk1-sgSubst _ _) ⊢l)
         ⊢Unit ⊢star ⊢star (refl ⊢star))
      Σ-ok
