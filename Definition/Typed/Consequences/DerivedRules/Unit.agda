------------------------------------------------------------------------
-- Derived rules related to the unit types
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.DerivedRules.Unit
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed TR
open import Definition.Typed.Consequences.DerivedRules.Identity TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Reduction TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Properties TR
open import Definition.Untyped.Unit 𝕄

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ                       : Con Term _
  A A₁ A₂ t t₁ t₂ u u₁ u₂ : Term _
  s                       : Strength
  p q                     : M

------------------------------------------------------------------------
-- A definitional η-rule

opaque

  -- A definitional η-rule for the strong unit type.

  Unit-η-≡ :
    Γ ⊢ t ∷ Unitˢ →
    Γ ⊢ starˢ ≡ t ∷ Unitˢ
  Unit-η-≡ ⊢t = η-unit
    (starⱼ (wfTerm ⊢t) (⊢∷Unit→Unit-allowed ⊢t))
    ⊢t

------------------------------------------------------------------------
-- Lemmas related to unitrec⟨_⟩

opaque
  unfolding unitrec⟨_⟩

  -- A typing rule for unitrec⟨_⟩.

  ⊢unitrec⟨⟩ :
    Γ ∙ Unit s ⊢ A →
    Γ ⊢ t ∷ Unit s →
    Γ ⊢ u ∷ A [ star s ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ p q A t u ∷ A [ t ]₀
  ⊢unitrec⟨⟩ {s = 𝕨} ⊢A ⊢t ⊢u =
    unitrecⱼ ⊢A ⊢t ⊢u (⊢∷Unit→Unit-allowed ⊢t)
  ⊢unitrec⟨⟩ {s = 𝕤} ⊢A ⊢t ⊢u =
    conv ⊢u (substTypeEq (refl ⊢A) (Unit-η-≡ ⊢t))

opaque
  unfolding unitrec⟨_⟩

  -- A reduction rule for unitrec⟨_⟩.

  unitrec⟨⟩-β-⇒* :
    (s PE.≡ 𝕨 → Γ ∙ Unit s ⊢ A) →
    Γ ⊢ t ∷ A [ star s ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ p q A (star s) t ⇒* t ∷ A [ star s ]₀
  unitrec⟨⟩-β-⇒* {s = 𝕨} ⊢A ⊢t =
    case wf (⊢A PE.refl) of λ {
      (_ ∙ ⊢Unit) →
    redMany $ unitrec-β (⊢A PE.refl) ⊢t (inversion-Unit ⊢Unit) }
  unitrec⟨⟩-β-⇒* {s = 𝕤} ⊢A ⊢t =
    id ⊢t

opaque

  -- An equality rule for unitrec⟨_⟩.

  unitrec⟨⟩-β-≡ :
    (s PE.≡ 𝕨 → Γ ∙ Unit s ⊢ A) →
    Γ ⊢ t ∷ A [ star s ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ p q A (star s) t ≡ t ∷ A [ star s ]₀
  unitrec⟨⟩-β-≡ ⊢A ⊢t =
    subset*Term (unitrec⟨⟩-β-⇒* ⊢A ⊢t)

opaque
  unfolding unitrec⟨_⟩

  -- Another reduction rule for unitrec⟨_⟩.

  unitrec⟨⟩-subst :
    Γ ∙ Unit s ⊢ A →
    Γ ⊢ u ∷ A [ star s ]₀ →
    Γ ⊢ t₁ ⇒ t₂ ∷ Unit s →
    Γ ⊢ unitrec⟨ s ⟩ p q A t₁ u ⇒* unitrec⟨ s ⟩ p q A t₂ u ∷ A [ t₁ ]₀
  unitrec⟨⟩-subst {s = 𝕨} ⊢A ⊢u t₁⇒t₂ =
    redMany $
    unitrec-subst ⊢A ⊢u t₁⇒t₂ $
    inversion-Unit $ syntacticEqTerm (subsetTerm t₁⇒t₂) .proj₁
  unitrec⟨⟩-subst {s = 𝕤} {p} {q} ⊢A ⊢u t₁⇒t₂ =
    id $
    ⊢unitrec⟨⟩ {p = p} {q = q} ⊢A
      (syntacticEqTerm (subsetTerm t₁⇒t₂) .proj₂ .proj₁) ⊢u

opaque
  unfolding unitrec⟨_⟩

  -- Another equality rule for unitrec⟨_⟩.

  unitrec⟨⟩-cong :
    Γ ∙ Unit s ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Unit s →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ star s ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ p q A₁ t₁ u₁ ≡ unitrec⟨ s ⟩ p q A₂ t₂ u₂ ∷
      A₁ [ t₁ ]₀
  unitrec⟨⟩-cong {s = 𝕨} A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ $
    inversion-Unit $ syntacticEqTerm t₁≡t₂ .proj₁
  unitrec⟨⟩-cong {s = 𝕤} A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    conv u₁≡u₂ $
    substTypeEq (refl (syntacticEq A₁≡A₂ .proj₁))
      (Unit-η-≡ $ syntacticEqTerm t₁≡t₂ .proj₂ .proj₁)

------------------------------------------------------------------------
-- A lemma related to Unit-η

opaque
  unfolding Unit-η

  -- A typing rule for Unit-η.

  ⊢Unit-η :
    Γ ⊢ t ∷ Unit s →
    Γ ⊢ Unit-η s p t ∷ Id (Unit s) (star s) t
  ⊢Unit-η ⊢t =
    case syntacticTerm ⊢t of λ
      ⊢Unit →
    case wf ⊢Unit of λ
      ⊢Γ →
    case inversion-Unit ⊢Unit of λ
      ok →
    ⊢unitrec⟨⟩
      (Idⱼ (starⱼ (⊢→⊢∙ (Unitⱼ ⊢Γ ok)) ok) (var₀ ⊢Unit))
      ⊢t
      (rflⱼ (starⱼ ⊢Γ ok))
