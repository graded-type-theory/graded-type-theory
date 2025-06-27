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
import Definition.Typed.Substitution.Primitive.Primitive R as S
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  Γ                                     : Con Term _
  A B B₁ B₂ l l₁ l₂ l₂′ t t₁ t₂ u u₁ u₂ : Term _

------------------------------------------------------------------------
-- Simple variants of typing, equality and reduction rules

opaque

  Liftⱼ′ : Γ ⊢ l₂ ∷ Level
         → Γ ⊢ A ∷ U l₁
         → Γ ⊢ Lift l₂ A ∷ U (l₁ maxᵘ l₂)
  Liftⱼ′ ⊢l₂ ⊢A = Liftⱼ (inversion-U-Level (wf-⊢∷ ⊢A)) ⊢l₂ ⊢A

opaque

  Liftⱼ-comm
    : Γ ⊢ l₂ ∷ Level
    → Γ ⊢ A ∷ U l₁
    → Γ ⊢ Lift l₂ A ∷ U (l₂ maxᵘ l₁)
  Liftⱼ-comm ⊢l₂ ⊢A =
    let ⊢l₁ = inversion-U-Level (wf-⊢∷ ⊢A)
    in conv (Liftⱼ ⊢l₁ ⊢l₂ ⊢A) (U-cong (maxᵘ-comm ⊢l₁ ⊢l₂))

opaque

  Lift-cong′ : Γ ⊢ l₂ ≡ l₂′ ∷ Level
             → Γ ⊢ A ≡ B ∷ U l₁
             → Γ ⊢ Lift l₂ A ≡ Lift l₂′ B ∷ U (l₁ maxᵘ l₂)
  Lift-cong′ l₂≡l₂′ A≡B =
    Lift-cong (inversion-U-Level (wf-⊢≡∷ A≡B .proj₁)) l₂≡l₂′ A≡B

opaque

  Lift-cong-comm
    : Γ ⊢ l₂ ≡ l₂′ ∷ Level
    → Γ ⊢ A ≡ B ∷ U l₁
    → Γ ⊢ Lift l₂ A ≡ Lift l₂′ B ∷ U (l₂ maxᵘ l₁)
  Lift-cong-comm l₂≡l₂′ A≡B =
    let ⊢l₁ = inversion-U-Level (wf-⊢≡∷ A≡B .proj₁)
        _ , ⊢l₂ , _ = wf-⊢≡∷ l₂≡l₂′
    in conv (Lift-cong ⊢l₁ l₂≡l₂′ A≡B) (U-cong (maxᵘ-comm ⊢l₁ ⊢l₂))

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

  Lift-η′ : Γ ⊢ t ∷ Lift l₂ A
          → Γ ⊢ u ∷ Lift l₂ A
          → Γ ⊢ lower t ≡ lower u ∷ A
          → Γ ⊢ t ≡ u ∷ Lift l₂ A
  Lift-η′ ⊢t ⊢u lowert≡loweru =
    let ⊢l₂ , _ = inversion-Lift (wf-⊢∷ ⊢t)
    in Lift-η ⊢l₂ (wf-⊢≡∷ lowert≡loweru .proj₁) ⊢t ⊢u lowert≡loweru

opaque

  Lift-β⇒ : Γ ⊢ t ∷ A
          → Γ ⊢ lower (lift t) ⇒ t ∷ A
  Lift-β⇒ ⊢t = Lift-β (wf-⊢∷ ⊢t) ⊢t
