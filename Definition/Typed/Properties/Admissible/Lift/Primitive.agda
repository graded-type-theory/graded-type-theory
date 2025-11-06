------------------------------------------------------------------------
-- Some admissible rules related to Lift
------------------------------------------------------------------------

-- Note that lemmas corresponding to the lemmas in this module, in
-- some cases with fewer arguments, can (at the time of writing) be
-- imported from Definition.Typed.Properties.Admissible.Lift.

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Lift.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Level.Primitive R
open import Definition.Typed.Properties.Admissible.U.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Substitution.Primitive.Primitive R

open import Definition.Untyped M
open import Definition.Untyped.Lift M
open import Definition.Untyped.Properties M

open import Tools.Function
import Tools.PropositionalEquality as PE

private variable
  Γ                                  : Con _ _
  A A₁ A₂ B B₁ B₂ l l₁ l₂ l₃ t t₁ t₂ : Term _

------------------------------------------------------------------------
-- Some lemmas related to Lift

opaque

  -- A variant of Liftⱼ.

  Liftⱼ-comm :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ A ∷ U l₁ →
    Γ ⊢ Lift l₂ A ∷ U (l₂ supᵘₗ l₁)
  Liftⱼ-comm ⊢l₁ ⊢l₂ ⊢A =
    conv (Liftⱼ ⊢l₁ ⊢l₂ ⊢A) (U-cong-⊢≡ (supᵘₗ-comm ⊢l₁ ⊢l₂))

opaque

  -- A variant of Lift-cong.

  Lift-cong-comm :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ l₂ ≡ l₃ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l₁ →
    Γ ⊢ Lift l₂ A₁ ≡ Lift l₃ A₂ ∷ U (l₂ supᵘₗ l₁)
  Lift-cong-comm ⊢l₁ ⊢l₂ l₂≡l₃ A₁≡A₂ =
    conv (Lift-cong ⊢l₁ ⊢l₂ l₂≡l₃ A₁≡A₂)
      (U-cong-⊢≡ (supᵘₗ-comm ⊢l₁ ⊢l₂))

------------------------------------------------------------------------
-- Some lemmas related to lower₀

opaque
  unfolding lower₀

  -- A typing rule for lower₀.

  lower₀Type
    : Γ ⊢ l ∷Level
    → Γ ∙ A ⊢ B
    → Γ ∙ Lift l A ⊢ lower₀ B
  lower₀Type ⊢l ⊢B =
    subst-⊢ ⊢B $
    ⊢ˢʷ∷-[][]↑ (lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wf ⊢B))) here))

opaque
  unfolding lower₀

  -- An equality rule for lower₀.

  lower₀TypeEq
    : Γ ⊢ l ∷Level
    → Γ ∙ A ⊢ B₁ ≡ B₂
    → Γ ∙ Lift l A ⊢ lower₀ B₁ ≡ lower₀ B₂
  lower₀TypeEq ⊢l B₁≡B₂ =
    subst-⊢≡ B₁≡B₂ $ refl-⊢ˢʷ≡∷ $
    ⊢ˢʷ∷-[][]↑ (lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wfEq B₁≡B₂))) here))

opaque
  unfolding lower₀

  -- A typing rule for lower₀.

  lower₀Term :
    Γ ⊢ l ∷Level →
    Γ ∙ A ⊢ t ∷ B →
    Γ ∙ Lift l A ⊢ lower₀ t ∷ lower₀ B
  lower₀Term ⊢l ⊢t =
    subst-⊢∷ ⊢t
      (⊢ˢʷ∷-[][]↑ (lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wfTerm ⊢t))) here)))

opaque
  unfolding lower₀

  -- An equality rule for lower₀.

  lower₀TermEq :
    Γ ⊢ l ∷Level →
    Γ ∙ A ⊢ t₁ ≡ t₂ ∷ B →
    Γ ∙ Lift l A ⊢ lower₀ t₁ ≡ lower₀ t₂ ∷ lower₀ B
  lower₀TermEq ⊢l t₁≡t₂ =
    subst-⊢≡∷ t₁≡t₂
      (refl-⊢ˢʷ≡∷ $ ⊢ˢʷ∷-[][]↑ $
       lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wfEqTerm t₁≡t₂))) here))

opaque
  unfolding lower₀

  -- A typing rule involving lower₀, lift and _[_]₀.

  ⊢lower₀[lift]₀ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ lower₀ B [ lift t ]₀
  ⊢lower₀[lift]₀ {B} ⊢B ⊢t =
    let ⊢A = ⊢∙→⊢ (wf ⊢B) in
    PE.subst (_⊢_ _) (PE.sym ([]↑-[]₀ B)) $
    substType ⊢B (lowerⱼ (liftⱼ (⊢zeroᵘ (wf ⊢A)) ⊢A ⊢t))

opaque
  unfolding lower₀

  -- An equality rule involving lower₀, lift and _[_]₀.

  lower₀[lift]₀ :
    Γ ∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ lower₀ B [ lift t ]₀ ≡ B [ t ]₀
  lower₀[lift]₀ {B} ⊢B ⊢t =
    let ⊢A = ⊢∙→⊢ (wf ⊢B) in
    PE.subst₂ (_⊢_≡_ _) (PE.sym ([]↑-[]₀ B)) PE.refl $
    subst-⊢≡ (refl ⊢B) $
    ⊢ˢʷ≡∷-sgSubst (lowerⱼ (liftⱼ (⊢zeroᵘ (wf ⊢A)) ⊢A ⊢t)) ⊢t
      (Lift-β ⊢A ⊢t)
