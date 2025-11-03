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
import Definition.Typed.Properties.Admissible.Lift.Primitive R as LP
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Substitution.Primitive R
import Definition.Typed.Substitution.Primitive.Primitive R as S
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Lift M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

open LP public
  using
    (lower₀Type; lower₀TypeEq; lower₀Term; lower₀TermEq;
     ⊢lower₀[lift]₀; lower₀[lift]₀)

private variable
  n                                     : Nat
  Γ                                     : Con Term n
  A B B₁ B₂ l l₁ l₂ l₂′ t t₁ t₂ u u₁ u₂ : Term n

------------------------------------------------------------------------
-- Simple variants of typing, equality and reduction rules

opaque

  -- An admissible typing rule for Lift.

  Liftⱼ′ : Γ ⊢ l₂ ∷Level
         → Γ ⊢ A ∷ U l₁
         → Γ ⊢ Lift l₂ A ∷ U (l₁ supᵘₗ l₂)
  Liftⱼ′ ⊢l₂ ⊢A =
    let _ , ok = inversion-U-Level (wf-⊢∷ ⊢A) in
    Liftⱼ ok ⊢l₂ ⊢A

opaque

  -- An admissible typing rule for Lift using _⊢_≤_∷Level.

  Liftⱼ≤ : Γ ⊢ l₁ ≤ l₂ ∷Level
         → Γ ⊢ A ∷ U l₁
         → Γ ⊢ Lift l₂ A ∷ U l₂
  Liftⱼ≤ l₁≤l₂ ⊢A =
    let _ , ⊢l₂ = wf-⊢≤ l₁≤l₂
        ok      = inversion-Level-⊢ (wf-⊢∷ ⊢l₂)
    in
    _⊢_∷_.conv (Liftⱼ′ (term-⊢∷ ⊢l₂) ⊢A) $ U-cong $
    PE.subst₃ (_⊢_≡_∷_ _) (PE.sym (supᵘₗ≡supᵘ ok)) PE.refl PE.refl l₁≤l₂

opaque

  -- An admissible typing rule for Lift that swaps levels.

  Liftⱼ-comm
    : Γ ⊢ l₂ ∷Level
    → Γ ⊢ A ∷ U l₁
    → Γ ⊢ Lift l₂ A ∷ U (l₂ supᵘₗ l₁)
  Liftⱼ-comm ⊢l₂ ⊢A =
    let _ , ok = inversion-U-Level (wf-⊢∷ ⊢A) in
    LP.Liftⱼ-comm ok ⊢l₂ ⊢A

opaque

  -- An admissible congruence rule for Lift.

  Lift-cong′ : Γ ⊢ l₂ ≡ l₂′ ∷Level
             → Γ ⊢ A ≡ B ∷ U l₁
             → Γ ⊢ Lift l₂ A ≡ Lift l₂′ B ∷ U (l₁ supᵘₗ l₂)
  Lift-cong′ l₂≡l₂′ A≡B =
    let _ , ⊢l₁ = inversion-U-Level (wf-⊢≡∷ A≡B .proj₁)
        ⊢l₂ , _ = wf-⊢≡∷L l₂≡l₂′
    in
    Lift-cong ⊢l₁ ⊢l₂ l₂≡l₂′ A≡B

opaque

  -- An admissible congruence rule for Lift that swaps levels.

  Lift-cong-comm
    : Γ ⊢ l₂ ≡ l₂′ ∷Level
    → Γ ⊢ A ≡ B ∷ U l₁
    → Γ ⊢ Lift l₂ A ≡ Lift l₂′ B ∷ U (l₂ supᵘₗ l₁)
  Lift-cong-comm l₂≡l₂′ A≡B =
    let _ , ⊢l₁ = inversion-U-Level (wf-⊢≡∷ A≡B .proj₁)
        ⊢l₂ , _ = wf-⊢≡∷L l₂≡l₂′
    in
    LP.Lift-cong-comm ⊢l₁ ⊢l₂ l₂≡l₂′ A≡B

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
-- A lemma related to lower₀

opaque
  unfolding lower₀

  lower₀[lift]₀∷
    : Γ ∙ A ⊢ t ∷ B
    → Γ ⊢ u ∷ A
    → Γ ⊢ lower₀ t [ lift u ]₀ ≡ t [ u ]₀ ∷ B [ u ]₀
  lower₀[lift]₀∷ {t} {B} ⊢t ⊢u =
    PE.subst₃ (_⊢_≡_∷_ _) (PE.sym ([]↑-[]₀ t)) PE.refl PE.refl
      (sym′ (substTermEq (refl ⊢t) (sym′ (Lift-β′ ⊢u))))
