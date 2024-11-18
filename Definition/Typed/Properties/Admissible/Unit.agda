------------------------------------------------------------------------
-- Admissible rules related to the unit types
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Unit
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR

open import Definition.Untyped M
open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties.Admissible.Equality TR
open import Definition.Typed.Properties.Admissible.Identity.Primitive TR
open import Definition.Typed.Properties.Admissible.Var TR
open import Definition.Typed.Properties.Reduction TR
open import Definition.Typed.Properties.Well-formed TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Substitution.Primitive TR
open import Definition.Typed.Syntactic TR
open import Definition.Untyped.Unit 𝕄

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  Γ                          : Con Term _
  A A₁ A₂ t t′ t₁ t₂ u u₁ u₂ : Term _
  s                          : Strength
  l                          : Universe-level
  p q                        : M

------------------------------------------------------------------------
-- A definitional η-rule

opaque

  -- A definitional η-rule for unit types with η-equality.

  Unit-η-≡ :
    Unit-with-η s →
    Γ ⊢ t ∷ Unit s l →
    Γ ⊢ star s l ≡ t ∷ Unit s l
  Unit-η-≡ η ⊢t =
    η-unit (starⱼ (wfTerm ⊢t) (⊢∷Unit→Unit-allowed ⊢t)) ⊢t η

------------------------------------------------------------------------
-- Lemmas related to unitrec

opaque

  -- A variant of unitrecⱼ.

  unitrecⱼ′ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ Unitʷ l →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    Γ ⊢ unitrec l p q A t u ∷ A [ t ]₀
  unitrecⱼ′ ⊢A ⊢t ⊢u =
    unitrecⱼ ⊢A ⊢t ⊢u (⊢∷Unit→Unit-allowed ⊢t)

opaque

  -- A generalisation of unitrec-cong.

  unitrec-cong′ :
    Γ ∙ Unitʷ l ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Unitʷ l →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ starʷ l ]₀ →
    Γ ⊢ unitrec l p q A₁ t₁ u₁ ≡ unitrec l p q A₂ t₂ u₂ ∷ A₁ [ t₁ ]₀
  unitrec-cong′
    {l} {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} {p} {q} A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    case inversion-Unit $ syntacticEqTerm t₁≡t₂ .proj₁ of λ
      ok →
    case Unitʷ-η? of λ where
      (no no-η) →
        unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ ok no-η
      (yes η) →
        case syntacticEq A₁≡A₂ of λ
          (⊢A₁ , ⊢A₂) →
        case syntacticEqTerm t₁≡t₂ of λ
          (_ , ⊢t₁ , ⊢t₂) →
        case syntacticEqTerm u₁≡u₂ of λ
          (_ , ⊢u₁ , ⊢u₂) →
        unitrec l p q A₁ t₁ u₁  ≡⟨ unitrec-β-η ⊢A₁ ⊢t₁ ⊢u₁ ok η ⟩⊢
        u₁                      ≡⟨ conv u₁≡u₂
                                     (substTypeEq (refl ⊢A₁) (Unit-η-≡ (inj₂ η) ⊢t₁)) ⟩⊢
        u₂                      ≡˘⟨ conv (unitrec-β-η ⊢A₂ ⊢t₂ (conv ⊢u₂ (substTypeEq A₁≡A₂ (refl (starⱼ (wfTerm ⊢t₁) ok)))) ok η)
                                      (sym (substTypeEq A₁≡A₂ t₁≡t₂)) ⟩⊢∎
        unitrec l p q A₂ t₂ u₂  ∎

opaque

  -- A generalisation of _⊢_≡_∷_.unitrec-β.

  unitrec-β-≡ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ A [ starʷ l ]₀ →
    Γ ⊢ unitrec l p q A (starʷ l) t ≡ t ∷ A [ starʷ l ]₀
  unitrec-β-≡ ⊢A ⊢t =
    case wf ⊢A of λ {
      (∙ ⊢Unit) →
    case inversion-Unit ⊢Unit of λ
      Unit-ok →
    case Unitʷ-η? of λ where
      (yes ok) →
        unitrec-β-η ⊢A (starⱼ (wf ⊢Unit) Unit-ok) ⊢t Unit-ok ok
      (no not-ok) →
        unitrec-β ⊢A ⊢t Unit-ok not-ok }

opaque

  -- A generalisation of _⊢_⇒_∷_.unitrec-β.

  unitrec-β-⇒ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ A [ starʷ l ]₀ →
    Γ ⊢ unitrec l p q A (starʷ l) t ⇒ t ∷ A [ starʷ l ]₀
  unitrec-β-⇒ ⊢A ⊢t =
    case wf ⊢A of λ {
      (∙ ⊢Unit) →
    case inversion-Unit ⊢Unit of λ
      Unit-ok →
    case Unitʷ-η? of λ where
      (yes ok) →
        unitrec-β-η ⊢A (starⱼ (wf ⊢Unit) Unit-ok) ⊢t Unit-ok ok
      (no not-ok) →
        unitrec-β ⊢A ⊢t Unit-ok not-ok }


opaque

  -- A variant of _⊢_≡_∷_.unitrec-β-η.

  unitrec-β-η-≡ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ Unitʷ l →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    Unitʷ-η →
    Γ ⊢ unitrec l p q A t u ≡ u ∷ A [ t ]₀
  unitrec-β-η-≡ ⊢A ⊢t ⊢u η =
    unitrec-β-η ⊢A ⊢t ⊢u (⊢∷Unit→Unit-allowed ⊢t) η

opaque

  -- A variant of _⊢_⇒_∷_.unitrec-β-η.

  unitrec-β-η-⇒ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ Unitʷ l →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    Unitʷ-η →
    Γ ⊢ unitrec l p q A t u ⇒ u ∷ A [ t ]₀
  unitrec-β-η-⇒ ⊢A ⊢t ⊢u η =
    unitrec-β-η ⊢A ⊢t ⊢u (⊢∷Unit→Unit-allowed ⊢t) η

opaque

  -- A variant of unitrec-subst

  unitrec-subst′ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    Γ ⊢ t₁ ⇒ t₂ ∷ Unitʷ l →
    ¬ Unitʷ-η →
    Γ ⊢ unitrec l p q A t₁ u ⇒ unitrec l p q A t₂ u ∷ A [ t₁ ]₀
  unitrec-subst′ ⊢A ⊢u t₁⇒t₂ =
    unitrec-subst ⊢A ⊢u t₁⇒t₂ $
    inversion-Unit $ syntacticEqTerm (subsetTerm t₁⇒t₂) .proj₁

opaque

  -- A variant of unitrec-subst for _⊢_⇒*_∷_.

  unitrec-subst* :
    Γ ⊢ t ⇒* t′ ∷ Unitʷ l →
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    ¬ Unitʷ-η →
    Γ ⊢ unitrec l p q A t u ⇒* unitrec l p q A t′ u ∷ A [ t ]₀
  unitrec-subst* (id ⊢t) ⊢A ⊢u _ =
    id (unitrecⱼ ⊢A ⊢t ⊢u (⊢∷Unit→Unit-allowed ⊢t))
  unitrec-subst* (t⇒t′ ⇨ t′⇒*t″) ⊢A ⊢u not-ok =
    let ok = ⊢∷Unit→Unit-allowed (redFirstTerm t⇒t′) in
    unitrec-subst ⊢A ⊢u t⇒t′ ok not-ok ⇨
    conv* (unitrec-subst* t′⇒*t″ ⊢A ⊢u not-ok)
      (substTypeEq (refl ⊢A) (sym′ (subsetTerm t⇒t′)))

------------------------------------------------------------------------
-- Lemmas related to unitrec⟨_⟩

opaque
  unfolding unitrec⟨_⟩

  -- A typing rule for unitrec⟨_⟩.

  ⊢unitrec⟨⟩ :
    Γ ∙ Unit s l ⊢ A →
    Γ ⊢ t ∷ Unit s l →
    Γ ⊢ u ∷ A [ star s l ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ l p q A t u ∷ A [ t ]₀
  ⊢unitrec⟨⟩ {s = 𝕨} ⊢A ⊢t ⊢u =
    unitrecⱼ′ ⊢A ⊢t ⊢u
  ⊢unitrec⟨⟩ {s = 𝕤} ⊢A ⊢t ⊢u =
    conv ⊢u (substTypeEq (refl ⊢A) (Unit-η-≡ (inj₁ PE.refl) ⊢t))

opaque
  unfolding unitrec⟨_⟩

  -- A reduction rule for unitrec⟨_⟩.

  unitrec⟨⟩-β-⇒* :
    (s PE.≡ 𝕨 → Γ ∙ Unit s l ⊢ A) →
    Γ ⊢ t ∷ A [ star s l ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ l p q A (star s l) t ⇒* t ∷ A [ star s l ]₀
  unitrec⟨⟩-β-⇒* {s = 𝕨} ⊢A ⊢t =
    redMany $ unitrec-β-⇒ (⊢A PE.refl) ⊢t
  unitrec⟨⟩-β-⇒* {s = 𝕤} ⊢A ⊢t =
    id ⊢t

opaque

  -- An equality rule for unitrec⟨_⟩.

  unitrec⟨⟩-β-≡ :
    (s PE.≡ 𝕨 → Γ ∙ Unit s l ⊢ A) →
    Γ ⊢ t ∷ A [ star s l ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ l p q A (star s l) t ≡ t ∷ A [ star s l ]₀
  unitrec⟨⟩-β-≡ ⊢A ⊢t =
    subset*Term (unitrec⟨⟩-β-⇒* ⊢A ⊢t)

opaque
  unfolding unitrec⟨_⟩

  -- Another reduction rule for unitrec⟨_⟩.

  unitrec⟨⟩-subst :
    Γ ∙ Unit s l ⊢ A →
    Γ ⊢ u ∷ A [ star s l ]₀ →
    Γ ⊢ t₁ ⇒ t₂ ∷ Unit s l →
    s PE.≡ 𝕤 ⊎ ¬ Unitʷ-η →
    Γ ⊢ unitrec⟨ s ⟩ l p q A t₁ u ⇒* unitrec⟨ s ⟩ l p q A t₂ u ∷
      A [ t₁ ]₀
  unitrec⟨⟩-subst {s = 𝕨} ⊢A ⊢u t₁⇒t₂ (inj₂ not-ok) =
    redMany $
    unitrec-subst ⊢A ⊢u t₁⇒t₂
      (inversion-Unit $ syntacticEqTerm (subsetTerm t₁⇒t₂) .proj₁)
      not-ok
  unitrec⟨⟩-subst {s = 𝕤} {p} {q} ⊢A ⊢u t₁⇒t₂ _ =
    id $
    ⊢unitrec⟨⟩ {p = p} {q = q} ⊢A
      (syntacticEqTerm (subsetTerm t₁⇒t₂) .proj₂ .proj₁) ⊢u

opaque
  unfolding unitrec⟨_⟩

  -- Another equality rule for unitrec⟨_⟩.

  unitrec⟨⟩-cong :
    Γ ∙ Unit s l ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Unit s l →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ star s l ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ l p q A₁ t₁ u₁ ≡ unitrec⟨ s ⟩ l p q A₂ t₂ u₂ ∷
      A₁ [ t₁ ]₀
  unitrec⟨⟩-cong {s = 𝕨} A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    unitrec-cong′ A₁≡A₂ t₁≡t₂ u₁≡u₂
  unitrec⟨⟩-cong {s = 𝕤} A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    conv u₁≡u₂ $
    substTypeEq (refl (syntacticEq A₁≡A₂ .proj₁))
      (Unit-η-≡ (inj₁ PE.refl) $ syntacticEqTerm t₁≡t₂ .proj₂ .proj₁)

------------------------------------------------------------------------
-- A lemma related to Unit-η

opaque
  unfolding Unit-η

  -- A typing rule for Unit-η.

  ⊢Unit-η :
    Γ ⊢ t ∷ Unit s l →
    Γ ⊢ Unit-η s l p t ∷ Id (Unit s l) (star s l) t
  ⊢Unit-η ⊢t =
    case syntacticTerm ⊢t of λ
      ⊢Unit →
    case wf ⊢Unit of λ
      ⊢Γ →
    case inversion-Unit ⊢Unit of λ
      ok →
    ⊢unitrec⟨⟩
      (Idⱼ′ (starⱼ (∙ Unitⱼ ⊢Γ ok) ok) (var₀ ⊢Unit))
      ⊢t
      (rflⱼ (starⱼ ⊢Γ ok))
