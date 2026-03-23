------------------------------------------------------------------------
-- Admissible rules for Lift
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Lift
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Equality R
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Admissible.U.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Substitution.Primitive R
import Definition.Typed.Substitution.Primitive.Primitive R as S
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Lift M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  n                               : Nat
  Γ                               : Cons _ _
  A A₁ A₂ B B₁ B₂ t t₁ t₂ u u₁ u₂ : Term n
  l l₁ l₂ l₂′                     : Lvl _
  s                               : Strength
  q r                             : M

------------------------------------------------------------------------
-- Simple variants of typing, equality and reduction rules

opaque

  -- An admissible typing rule for Lift.

  Liftⱼ′ : Γ ⊢ l₂ ∷Level
         → Γ ⊢ A ∷ U l₁
         → Γ ⊢ Lift l₂ A ∷ U (l₁ supᵘₗ l₂)
  Liftⱼ′ ⊢l₂ ⊢A =
    let ok = inversion-U-Level (wf-⊢∷ ⊢A) in
    Liftⱼ ok ⊢l₂ ⊢A

opaque
  unfolding _supᵘₗ_

  -- An admissible typing rule for Lift using _⊢_≤_∷Level.

  Liftⱼ≤ :
    Γ ⊢ t₁ ≤ t₂ ∷Level →
    Γ ⊢ A ∷ U (level t₁) →
    Γ ⊢ Lift (level t₂) A ∷ U (level t₂)
  Liftⱼ≤ t₁≤t₂ ⊢A =
    let _ , ⊢t₂ = wf-⊢≤ t₁≤t₂
        ok      = inversion-Level-⊢ (wf-⊢∷ ⊢t₂)
    in
    _⊢_∷_.conv (Liftⱼ′ (term-⊢∷ ⊢t₂) ⊢A) $
    PE.subst (flip (_⊢_≡_ _) _) (PE.sym (PE.cong U (supᵘₗ≡supᵘ ok))) $
    U-cong t₁≤t₂

opaque

  -- An admissible typing rule for Lift that swaps levels.

  Liftⱼ-comm
    : Γ ⊢ l₂ ∷Level
    → Γ ⊢ A ∷ U l₁
    → Γ ⊢ Lift l₂ A ∷ U (l₂ supᵘₗ l₁)
  Liftⱼ-comm ⊢l₂ ⊢A =
    let ⊢l₁ = inversion-U-Level (wf-⊢∷ ⊢A) in
    conv (Liftⱼ′ ⊢l₂ ⊢A) (U-cong-⊢≡ (supᵘₗ-comm ⊢l₁ ⊢l₂))

opaque

  -- An admissible congruence rule for Lift.

  Lift-cong′ : Γ ⊢ l₂ ≡ l₂′ ∷Level
             → Γ ⊢ A ≡ B ∷ U l₁
             → Γ ⊢ Lift l₂ A ≡ Lift l₂′ B ∷ U (l₁ supᵘₗ l₂)
  Lift-cong′ l₂≡l₂′ A≡B =
    let ⊢l₁     = inversion-U-Level (wf-⊢≡∷ A≡B .proj₁)
        ⊢l₂ , _ = wf-⊢≡∷L l₂≡l₂′
    in
    Lift-cong ⊢l₁ ⊢l₂ l₂≡l₂′ A≡B

opaque

  -- An admissible equality rule for Lift.

  Lift-cong-≤ₗ :
    Γ ⊢ l ≤ₗ l₁ ∷Level →
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ A₁ ≡ A₂ ∷ U l →
    Γ ⊢ Lift l₁ A₁ ≡ Lift l₂ A₂ ∷ U l₁
  Lift-cong-≤ₗ l≤l₁ l₁≡l₂ A₁≡A₂ =
    conv (Lift-cong′ l₁≡l₂ A₁≡A₂)
      (U-cong-⊢≡ (⊢≤ₗ∷L→⊢≡∷L l≤l₁))

opaque

  -- An admissible typing rule for Lift.

  ⊢Lift-≤ₗ :
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ A ∷ U l₁ →
    Γ ⊢ Lift l₂ A ∷ U l₂
  ⊢Lift-≤ₗ l₁≤l₂ ⊢A =
    wf-⊢≡∷
      (Lift-cong-≤ₗ l₁≤l₂ (refl-⊢≡∷L (wf-⊢≤ₗ∷L l₁≤l₂ .proj₂)) (refl ⊢A))
      .proj₂ .proj₁

opaque

  -- An admissible congruence rule for Lift that swaps levels.

  Lift-cong-comm
    : Γ ⊢ l₂ ≡ l₂′ ∷Level
    → Γ ⊢ A ≡ B ∷ U l₁
    → Γ ⊢ Lift l₂ A ≡ Lift l₂′ B ∷ U (l₂ supᵘₗ l₁)
  Lift-cong-comm l₂≡l₂′ A≡B =
    let ⊢l₁     = inversion-U-Level (wf-⊢≡∷ A≡B .proj₁)
        ⊢l₂ , _ = wf-⊢≡∷L l₂≡l₂′
    in
    conv (Lift-cong ⊢l₁ ⊢l₂ l₂≡l₂′ A≡B)
      (U-cong-⊢≡ (supᵘₗ-comm ⊢l₁ ⊢l₂))

opaque

  -- An admissible typing rule for lift.

  liftⱼ′ : Γ ⊢ l₂ ∷Level
         → Γ ⊢ t ∷ A
         → Γ ⊢ lift t ∷ Lift l₂ A
  liftⱼ′ ⊢l₂ ⊢t = liftⱼ ⊢l₂ (wf-⊢∷ ⊢t) ⊢t

opaque

  -- An admissible congruence rule for lift.

  lift-cong :
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ t ≡ u ∷ A →
    Γ ⊢ lift t ≡ lift u ∷ Lift l₂ A
  lift-cong ⊢l₂ t≡u =
    let _ , ⊢t , ⊢u = wf-⊢≡∷ t≡u
    in S.lift-cong ⊢l₂ (wf-⊢≡∷ t≡u .proj₁) ⊢t ⊢u t≡u

opaque

  -- An admissible β-equality rule for Lift.

  Lift-β′ : Γ ⊢ t ∷ A
          → Γ ⊢ lower (lift t) ≡ t ∷ A
  Lift-β′ ⊢t = Lift-β (wf-⊢∷ ⊢t) ⊢t

opaque

  -- An admissible β-reduction rule for Lift.

  Lift-β⇒ : Γ ⊢ t ∷ A
          → Γ ⊢ lower (lift t) ⇒ t ∷ A
  Lift-β⇒ ⊢t = Lift-β (wf-⊢∷ ⊢t) ⊢t

opaque

  -- An admissible η-equality rule for Lift.

  Lift-η′ : Γ ⊢ t ∷ Lift l₂ A
          → Γ ⊢ u ∷ Lift l₂ A
          → Γ ⊢ lower t ≡ lower u ∷ A
          → Γ ⊢ t ≡ u ∷ Lift l₂ A
  Lift-η′ ⊢t ⊢u lowert≡loweru =
    let ⊢l₂ , _ = inversion-Lift (wf-⊢∷ ⊢t)
    in Lift-η ⊢l₂ (wf-⊢≡∷ lowert≡loweru .proj₁) ⊢t ⊢u lowert≡loweru

opaque

  -- An admissible alternative η-equality rule for Lift.

  Lift-η-swap
    : Γ ⊢ t ∷ Lift l A
    → Γ ⊢ lower t ≡ u ∷ A
    → Γ ⊢ t ≡ lift u ∷ Lift l A
  Lift-η-swap ⊢t lowert≡u =
    let _ , _ , ⊢u = wf-⊢≡∷ lowert≡u
        ⊢l , ⊢A = inversion-Lift (wf-⊢∷ ⊢t)
    in Lift-η′ ⊢t (liftⱼ′ ⊢l ⊢u) (trans lowert≡u (sym′ (Lift-β′ ⊢u)))

opaque

  -- An admissible η-rule for Lift.

  ⊢lift-lower≡∷ :
    Γ ⊢ t ∷ Lift l A →
    Γ ⊢ lift (lower t) ≡ t ∷ Lift l A
  ⊢lift-lower≡∷ ⊢t =
    let ⊢l , _ = inversion-Lift (wf-⊢∷ ⊢t) in
    Lift-η′ (liftⱼ′ ⊢l (lowerⱼ ⊢t)) ⊢t
      (Lift-β′ (lowerⱼ ⊢t))

------------------------------------------------------------------------
-- Some lemmas related to lower₀

opaque
  unfolding lower₀

  -- A typing rule for lower₀.

  lower₀Type
    : Γ ⊢ l ∷Level
    → Γ »∙ A ⊢ B
    → Γ »∙ Lift l A ⊢ lower₀ B
  lower₀Type ⊢l ⊢B =
    subst-⊢ ⊢B $
    ⊢ˢʷ∷-[][]↑ (lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wf ⊢B))) here))

opaque
  unfolding lower₀

  -- An equality rule for lower₀.

  lower₀TypeEq
    : Γ ⊢ l ∷Level
    → Γ »∙ A ⊢ B₁ ≡ B₂
    → Γ »∙ Lift l A ⊢ lower₀ B₁ ≡ lower₀ B₂
  lower₀TypeEq ⊢l B₁≡B₂ =
    subst-⊢≡ B₁≡B₂ $ refl-⊢ˢʷ≡∷ $
    ⊢ˢʷ∷-[][]↑ (lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wf B₁≡B₂))) here))

opaque
  unfolding lower₀

  -- A typing rule for lower₀.

  lower₀Term :
    Γ ⊢ l ∷Level →
    Γ »∙ A ⊢ t ∷ B →
    Γ »∙ Lift l A ⊢ lower₀ t ∷ lower₀ B
  lower₀Term ⊢l ⊢t =
    subst-⊢ ⊢t
      (⊢ˢʷ∷-[][]↑ (lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wf ⊢t))) here)))

opaque
  unfolding lower₀

  -- An equality rule for lower₀.

  lower₀TermEq :
    Γ ⊢ l ∷Level →
    Γ »∙ A ⊢ t₁ ≡ t₂ ∷ B →
    Γ »∙ Lift l A ⊢ lower₀ t₁ ≡ lower₀ t₂ ∷ lower₀ B
  lower₀TermEq ⊢l t₁≡t₂ =
    subst-⊢≡ t₁≡t₂
      (refl-⊢ˢʷ≡∷ $ ⊢ˢʷ∷-[][]↑ $
       lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wf t₁≡t₂))) here))

opaque
  unfolding lower₀

  -- A typing rule involving lower₀, lift and _[_]₀.

  ⊢lower₀[lift]₀ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ lower₀ B [ lift t ]₀
  ⊢lower₀[lift]₀ {B} ⊢B ⊢t =
    let ⊢A = ⊢∙→⊢ (wf ⊢B) in
    PE.subst (_⊢_ _) (PE.sym ([]↑-[]₀ B)) $
    subst-⊢₀ ⊢B (lowerⱼ (liftⱼ (⊢zeroᵘ (wf ⊢A)) ⊢A ⊢t))

opaque
  unfolding lower₀

  lower₀[lift]₀ :
    Γ »∙ A ⊢ B →
    Γ ⊢ t ∷ A →
    Γ ⊢ lower₀ B [ lift t ]₀ ≡ B [ t ]₀
  lower₀[lift]₀ {B} ⊢B ⊢t =
    let ⊢A = ⊢∙→⊢ (wf ⊢B) in
    PE.subst₂ (_⊢_≡_ _) (PE.sym ([]↑-[]₀ B)) PE.refl $
    subst-⊢≡ (refl ⊢B) $
    ⊢ˢʷ≡∷-sgSubst (Lift-β ⊢A ⊢t)

opaque
  unfolding lower₀

  lower₀[lift]₀∷
    : Γ »∙ A ⊢ t ∷ B
    → Γ ⊢ u ∷ A
    → Γ ⊢ lower₀ t [ lift u ]₀ ≡ t [ u ]₀ ∷ B [ u ]₀
  lower₀[lift]₀∷ {t} {B} ⊢t ⊢u =
    PE.subst₃ (_⊢_≡_∷_ _) (PE.sym ([]↑-[]₀ t)) PE.refl PE.refl
      (sym′ (subst-⊢≡₀ ⊢t (sym′ (Lift-β′ ⊢u))))
