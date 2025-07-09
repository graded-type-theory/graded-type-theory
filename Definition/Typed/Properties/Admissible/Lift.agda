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

open Modality 𝕄
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Equality R
open import Definition.Typed.Properties.Admissible.Level R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Substitution.Primitive R
import Definition.Typed.Substitution.Primitive.Primitive R as S
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  n                                     : Nat
  Γ                                     : Con Term n
  A B B₁ B₂ C l l₁ l₂ l₂′ t t₁ t₂ u u₁ u₂ : Term n

------------------------------------------------------------------------
-- Simple variants of typing, equality and reduction rules

opaque

  Liftⱼ′ : Γ ⊢ l₂ ∷ Level
         → Γ ⊢ A ∷ U l₁
         → Γ ⊢ Lift l₂ A ∷ U (l₁ supᵘ l₂)
  Liftⱼ′ ⊢l₂ ⊢A = Liftⱼ (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢l₂ ⊢A

opaque

  Liftⱼ≤ : Γ ⊢ l₁ ≤ l₂ ∷Level
         → Γ ⊢ A ∷ U l₁
         → Γ ⊢ Lift l₂ A ∷ U l₂
  Liftⱼ≤ l₁≤l₂ ⊢A =
    let ⊢l₁ , ⊢l₂ = wf-⊢≤ l₁≤l₂
    in conv (Liftⱼ′ ⊢l₂ ⊢A) (U-cong l₁≤l₂)

opaque

  Liftⱼ-comm
    : Γ ⊢ l₂ ∷ Level
    → Γ ⊢ A ∷ U l₁
    → Γ ⊢ Lift l₂ A ∷ U (l₂ supᵘ l₁)
  Liftⱼ-comm ⊢l₂ ⊢A =
    let ⊢l₁ = inversion-U-Level (wf-⊢∷ ⊢A)
    in conv (Liftⱼ ⊢l₁ ⊢l₂ ⊢A) (U-cong (supᵘ-comm ⊢l₁ ⊢l₂))

opaque

  Lift-cong′ : Γ ⊢ l₂ ≡ l₂′ ∷ Level
             → Γ ⊢ A ≡ B ∷ U l₁
             → Γ ⊢ Lift l₂ A ≡ Lift l₂′ B ∷ U (l₁ supᵘ l₂)
  Lift-cong′ l₂≡l₂′ A≡B =
    Lift-cong (inversion-U-Level (wf-⊢≡∷ A≡B .proj₁)) l₂≡l₂′ A≡B

opaque

  Lift-cong-comm
    : Γ ⊢ l₂ ≡ l₂′ ∷ Level
    → Γ ⊢ A ≡ B ∷ U l₁
    → Γ ⊢ Lift l₂ A ≡ Lift l₂′ B ∷ U (l₂ supᵘ l₁)
  Lift-cong-comm l₂≡l₂′ A≡B =
    let ⊢l₁ = inversion-U-Level (wf-⊢≡∷ A≡B .proj₁)
        _ , ⊢l₂ , _ = wf-⊢≡∷ l₂≡l₂′
    in conv (Lift-cong ⊢l₁ l₂≡l₂′ A≡B) (U-cong (supᵘ-comm ⊢l₁ ⊢l₂))

opaque

  liftⱼ′ : Γ ⊢ l₂ ∷ Level
         → Γ ⊢ t ∷ A
         → Γ ⊢ lift t ∷ Lift l₂ A
  liftⱼ′ ⊢l₂ ⊢t = liftⱼ ⊢l₂ (wf-⊢∷ ⊢t) ⊢t

opaque

  lift-cong :
    Γ ⊢ l₂ ∷ Level →
    Γ ⊢ t ≡ u ∷ A →
    Γ ⊢ lift t ≡ lift u ∷ Lift l₂ A
  lift-cong ⊢l₂ t≡u =
    let _ , ⊢t , ⊢u = wf-⊢≡∷ t≡u
    in S.lift-cong ⊢l₂ (wf-⊢≡∷ t≡u .proj₁) ⊢t ⊢u t≡u

opaque

  Lift-β′ : Γ ⊢ t ∷ A
          → Γ ⊢ lower (lift t) ≡ t ∷ A
  Lift-β′ ⊢t = Lift-β (wf-⊢∷ ⊢t) ⊢t

opaque

  Lift-β⇒ : Γ ⊢ t ∷ A
          → Γ ⊢ lower (lift t) ⇒ t ∷ A
  Lift-β⇒ ⊢t = Lift-β (wf-⊢∷ ⊢t) ⊢t

opaque

  Lift-η′ : Γ ⊢ t ∷ Lift l₂ A
          → Γ ⊢ u ∷ Lift l₂ A
          → Γ ⊢ lower t ≡ lower u ∷ A
          → Γ ⊢ t ≡ u ∷ Lift l₂ A
  Lift-η′ ⊢t ⊢u lowert≡loweru =
    let ⊢l₂ , _ = inversion-Lift (wf-⊢∷ ⊢t)
    in Lift-η ⊢l₂ (wf-⊢≡∷ lowert≡loweru .proj₁) ⊢t ⊢u lowert≡loweru

opaque

  Lift-η-swap
    : Γ ⊢ t ∷ Lift l A
    → Γ ⊢ lower t ≡ u ∷ A
    → Γ ⊢ t ≡ lift u ∷ Lift l A
  Lift-η-swap ⊢t lowert≡u =
    let _ , _ , ⊢u = wf-⊢≡∷ lowert≡u
        ⊢l , ⊢A = inversion-Lift (wf-⊢∷ ⊢t)
    in Lift-η′ ⊢t (liftⱼ′ ⊢l ⊢u) (trans lowert≡u (sym′ (Lift-β′ ⊢u)))

------------------------------------------------------------------------
-- A helper substitution for heterogeneous Π and Σ

-- If Γ ∙ A ⊢ t ∷ B, then Γ ∙ Lift l A ⊢ lower₀ t ∷ lower₀ B.

lower₀ : Term (1+ n) → Term (1+ n)
lower₀ t = t [ lower (var x0) ]↑

opaque

  lower₀Type
    : Γ ⊢ l ∷ Level
    → Γ ∙ A ⊢ B
    → Γ ∙ Lift l A ⊢ lower₀ B
  lower₀Type ⊢l ⊢B = subst-⊢ ⊢B
    (⊢ˢʷ∷-[][]↑ (lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wf ⊢B))) here)))

opaque

  lower₀TypeEq
    : Γ ⊢ l ∷ Level
    → Γ ∙ A ⊢ B ≡ C
    → Γ ∙ Lift l A ⊢ lower₀ B ≡ lower₀ C
  lower₀TypeEq ⊢l B≡C = subst-⊢≡ B≡C
    (refl-⊢ˢʷ≡∷ (⊢ˢʷ∷-[][]↑ (lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wfEq B≡C))) here))))

opaque

  lower₀Term
    : Γ ⊢ l ∷ Level
    → Γ ∙ A ⊢ t ∷ B
    → Γ ∙ Lift l A ⊢ lower₀ t ∷ lower₀ B
  lower₀Term ⊢l ⊢t = subst-⊢∷ ⊢t
    (⊢ˢʷ∷-[][]↑ (lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wfTerm ⊢t))) here)))

opaque

  lower₀TermEq
    : Γ ⊢ l ∷ Level
    → Γ ∙ A ⊢ t ≡ u ∷ B
    → Γ ∙ Lift l A ⊢ lower₀ t ≡ lower₀ u ∷ lower₀ B
  lower₀TermEq ⊢l t≡u = subst-⊢≡∷ t≡u
    (refl-⊢ˢʷ≡∷ (⊢ˢʷ∷-[][]↑ (lowerⱼ (var (∙ Liftⱼ ⊢l (⊢∙→⊢ (wfEqTerm t≡u))) here))))

opaque

  lower₀[lift]₀
    : Γ ∙ A ⊢ B
    → Γ ⊢ u ∷ A
    → Γ ⊢ lower₀ B [ lift u ]₀ ≡ B [ u ]₀
  lower₀[lift]₀ {B} ⊢B ⊢u =
    PE.subst₂ (_⊢_≡_ _) (PE.sym ([]↑-[]₀ B)) PE.refl
      (substTypeEq (refl ⊢B) (Lift-β′ ⊢u))

opaque

  lower₀[lift]₀∷
    : Γ ∙ A ⊢ t ∷ B
    → Γ ⊢ u ∷ A
    → Γ ⊢ lower₀ t [ lift u ]₀ ≡ t [ u ]₀ ∷ B [ u ]₀
  lower₀[lift]₀∷ {t} {B} ⊢t ⊢u =
    PE.subst₃ (_⊢_≡_∷_ _) (PE.sym ([]↑-[]₀ t)) PE.refl PE.refl
      (sym′ (substTermEq (refl ⊢t) (sym′ (Lift-β′ ⊢u))))
