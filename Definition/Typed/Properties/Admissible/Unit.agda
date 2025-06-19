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
open import Definition.Untyped.Properties M
open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties.Admissible.Equality TR
open import Definition.Typed.Properties.Admissible.Identity.Primitive TR
open import Definition.Typed.Properties.Admissible.Var TR
open import Definition.Typed.Properties.Reduction TR
open import Definition.Typed.Properties.Well-formed TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Stability TR
open import Definition.Typed.Substitution.Primitive TR
open import Definition.Typed.Syntactic TR
open import Definition.Typed.Weakening TR
open import Definition.Typed.Well-formed TR
open import Definition.Untyped.Unit 𝕄

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  Γ                                     : Con Term _
  A A₁ A₂ l l′ l₁ l₂ t t′ t₁ t₂ u u₁ u₂ : Term _
  s                                     : Strength
  p q                                   : M

------------------------------------------------------------------------
-- A definitional η-rule

opaque

  -- A definitional η-rule for unit types with η-equality.

  Unit-η-≡ :
    Unit-with-η s →
    Γ ⊢ t ∷ Unit s l →
    Γ ⊢ star s l ≡ t ∷ Unit s l
  Unit-η-≡ η ⊢t =
    let (⊢l , ok) = inversion-Unit (syntacticTerm ⊢t) in
    η-unit ⊢l (starⱼ ⊢l ok) ⊢t ok η

------------------------------------------------------------------------
-- Lemmas related to unitrec

opaque

  -- A variant of unitrecⱼ.

  unitrecⱼ′ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ Unitʷ l →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    Γ ⊢ unitrec p q l A t u ∷ A [ t ]₀
  unitrecⱼ′ ⊢A ⊢t ⊢u =
    let (⊢l , ok) = inversion-Unit (⊢∙→⊢ (wf ⊢A)) in
    unitrecⱼ ⊢l ⊢A ⊢t ⊢u ok

opaque

  -- A generalisation of unitrec-cong.

  unitrec-cong′ :
    Γ ⊢ l₁ ≡ l₂ ∷ Level →
    Γ ∙ Unitʷ l₁ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Unitʷ l₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ starʷ l₁ ]₀ →
    Γ ⊢ unitrec p q l₁ A₁ t₁ u₁ ≡ unitrec p q l₂ A₂ t₂ u₂ ∷ A₁ [ t₁ ]₀
  unitrec-cong′
    {l₁} {l₂} {A₁} {A₂} {t₁} {t₂} {u₁} {u₂} {p} {q} l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    case wfEqTerm l₁≡l₂ of λ
      ⊢Γ →
    case syntacticEqTerm l₁≡l₂ of λ
      (_ , ⊢l₁ , ⊢l₂) →
    case inversion-Unit $ syntacticEqTerm t₁≡t₂ .proj₁ of λ
      (_ , ok) →
    case Unitʷ-η? of λ where
      (no no-η) →
        unitrec-cong ⊢l₁ ⊢l₂ l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ ok no-η
      (yes η) →
        case syntacticEq A₁≡A₂ of λ
          (⊢A₁ , ⊢A₂) →
        case syntacticEqTerm t₁≡t₂ of λ
          (_ , ⊢t₁ , ⊢t₂) →
        case syntacticEqTerm u₁≡u₂ of λ
          (_ , ⊢u₁ , ⊢u₂) →
        unitrec p q l₁ A₁ t₁ u₁  ≡⟨ unitrec-β-η ⊢l₁ ⊢A₁ ⊢t₁ ⊢u₁ ok η ⟩⊢
        u₁                      ≡⟨ conv u₁≡u₂
                                     (substTypeEq (refl ⊢A₁) (Unit-η-≡ (inj₂ η) ⊢t₁)) ⟩⊢
        u₂                      ≡˘⟨ conv
                                      (unitrec-β-η ⊢l₂
                                        (stability (reflConEq ⊢Γ ∙ Unit-cong l₁≡l₂ ok) ⊢A₂)
                                        (conv ⊢t₂ (Unit-cong l₁≡l₂ ok))
                                        (conv ⊢u₂ (substTypeEq A₁≡A₂ (star-cong l₁≡l₂ ok)))
                                        ok η)
                                      (sym (substTypeEq A₁≡A₂ t₁≡t₂)) ⟩⊢∎
        unitrec p q l₂ A₂ t₂ u₂  ∎

opaque

  -- A generalisation of _⊢_≡_∷_.unitrec-β.

  unitrec-β-≡ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ A [ starʷ l ]₀ →
    Γ ⊢ unitrec p q l A (starʷ l) t ≡ t ∷ A [ starʷ l ]₀
  unitrec-β-≡ ⊢A ⊢t =
    case wf ⊢A of λ {
      (∙ ⊢Unit) →
    case inversion-Unit ⊢Unit of λ
      (⊢l , Unit-ok) →
    case Unitʷ-η? of λ where
      (yes ok) →
        unitrec-β-η ⊢l ⊢A (starⱼ ⊢l Unit-ok) ⊢t Unit-ok ok
      (no not-ok) →
        unitrec-β ⊢l ⊢A ⊢t Unit-ok not-ok }

opaque

  -- A generalisation of _⊢_⇒_∷_.unitrec-β.

  unitrec-β-⇒ :
    Γ ⊢ l ≡ l′ ∷ Level →
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ A [ starʷ l ]₀ →
    Γ ⊢ unitrec p q l A (starʷ l′) t ⇒ t ∷ A [ starʷ l ]₀
  unitrec-β-⇒ l≡l′ ⊢A ⊢t =
    let ⊢l , Unit-ok = inversion-Unit (⊢∙→⊢ (wf ⊢A))
        _ , _ , ⊢l′  = wf-⊢≡∷ l≡l′
    in
    case Unitʷ-η? of λ where
      (yes ok) →
        conv
          (unitrec-β-η ⊢l ⊢A
             (conv (starⱼ ⊢l′ Unit-ok) (Unit-cong (sym′ l≡l′) Unit-ok))
             ⊢t Unit-ok ok)
          (substTypeEq (refl ⊢A) (sym′ (star-cong l≡l′ Unit-ok)))
      (no not-ok) →
        unitrec-β ⊢l l≡l′ ⊢A ⊢t Unit-ok not-ok

opaque

  -- A variant of _⊢_≡_∷_.unitrec-β-η.

  unitrec-β-η-≡ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ Unitʷ l →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    Unitʷ-η →
    Γ ⊢ unitrec p q l A t u ≡ u ∷ A [ t ]₀
  unitrec-β-η-≡ ⊢A ⊢t ⊢u η =
    case wf ⊢A of λ {
      (∙ ⊢Unit) →
    case inversion-Unit ⊢Unit of λ
      (⊢l , Unit-ok) →
    unitrec-β-η ⊢l ⊢A ⊢t ⊢u (⊢∷Unit→Unit-allowed ⊢t) η }

opaque

  -- A variant of _⊢_⇒_∷_.unitrec-β-η.

  unitrec-β-η-⇒ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ t ∷ Unitʷ l →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    Unitʷ-η →
    Γ ⊢ unitrec p q l A t u ⇒ u ∷ A [ t ]₀
  unitrec-β-η-⇒ ⊢A ⊢t ⊢u η =
    case wf ⊢A of λ {
      (∙ ⊢Unit) →
    case inversion-Unit ⊢Unit of λ
      (⊢l , Unit-ok) →
    unitrec-β-η ⊢l ⊢A ⊢t ⊢u (⊢∷Unit→Unit-allowed ⊢t) η }

opaque

  -- A variant of unitrec-subst

  unitrec-subst′ :
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    Γ ⊢ t₁ ⇒ t₂ ∷ Unitʷ l →
    ¬ Unitʷ-η →
    Γ ⊢ unitrec p q l A t₁ u ⇒ unitrec p q l A t₂ u ∷ A [ t₁ ]₀
  unitrec-subst′ ⊢A ⊢u t₁⇒t₂ =
    case wf ⊢A of λ {
      (∙ ⊢Unit) →
    case inversion-Unit ⊢Unit of λ
      (⊢l , Unit-ok) →
    unitrec-subst ⊢l ⊢A ⊢u t₁⇒t₂ $ proj₂ $
    inversion-Unit $ syntacticEqTerm (subsetTerm t₁⇒t₂) .proj₁ }

opaque

  -- A variant of unitrec-subst for _⊢_⇒*_∷_.

  unitrec-subst* :
    Γ ⊢ t ⇒* t′ ∷ Unitʷ l →
    Γ ∙ Unitʷ l ⊢ A →
    Γ ⊢ u ∷ A [ starʷ l ]₀ →
    ¬ Unitʷ-η →
    Γ ⊢ unitrec p q l A t u ⇒* unitrec p q l A t′ u ∷ A [ t ]₀
  unitrec-subst* (id ⊢t) ⊢A ⊢u _ =
    case inversion-Unit (⊢∙→⊢ (wf ⊢A)) of λ
      (⊢l , _) →
    id (unitrecⱼ ⊢l ⊢A ⊢t ⊢u (⊢∷Unit→Unit-allowed ⊢t))
  unitrec-subst* (t⇒t′ ⇨ t′⇒*t″) ⊢A ⊢u not-ok =
    let ok = ⊢∷Unit→Unit-allowed (redFirstTerm t⇒t′) in
    case inversion-Unit (⊢∙→⊢ (wf ⊢A)) of λ
      (⊢l , _) →
    unitrec-subst ⊢l ⊢A ⊢u t⇒t′ ok not-ok ⇨
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
    Γ ⊢ unitrec⟨ s ⟩ p q l A t u ∷ A [ t ]₀
  ⊢unitrec⟨⟩ {s = 𝕨} ⊢A ⊢t ⊢u =
    unitrecⱼ′ ⊢A ⊢t ⊢u
  ⊢unitrec⟨⟩ {s = 𝕤} ⊢A ⊢t ⊢u =
    conv ⊢u (substTypeEq (refl ⊢A) (Unit-η-≡ (inj₁ PE.refl) ⊢t))

opaque
  unfolding unitrec⟨_⟩

  -- A reduction rule for unitrec⟨_⟩.

  unitrec⟨⟩-β-⇒* :
    (s PE.≡ 𝕨 → Γ ⊢ l ≡ l′ ∷ Level) →
    (s PE.≡ 𝕨 → Γ ∙ Unit s l ⊢ A) →
    Γ ⊢ t ∷ A [ star s l ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ p q l A (star s l′) t ⇒* t ∷ A [ star s l ]₀
  unitrec⟨⟩-β-⇒* {s = 𝕨} l≡l′ ⊢A ⊢t =
    redMany $ unitrec-β-⇒ (l≡l′ PE.refl) (⊢A PE.refl) ⊢t
  unitrec⟨⟩-β-⇒* {s = 𝕤} _ _ ⊢t =
    id ⊢t

opaque

  -- An equality rule for unitrec⟨_⟩.

  unitrec⟨⟩-β-≡ :
    (s PE.≡ 𝕨 → Γ ⊢ l ≡ l′ ∷ Level) →
    (s PE.≡ 𝕨 → Γ ∙ Unit s l ⊢ A) →
    Γ ⊢ t ∷ A [ star s l ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ p q l A (star s l′) t ≡ t ∷ A [ star s l ]₀
  unitrec⟨⟩-β-≡ l≡l′ ⊢A ⊢t =
    subset*Term (unitrec⟨⟩-β-⇒* l≡l′ ⊢A ⊢t)

opaque
  unfolding unitrec⟨_⟩

  -- Another reduction rule for unitrec⟨_⟩.

  unitrec⟨⟩-subst :
    Γ ∙ Unit s l ⊢ A →
    Γ ⊢ u ∷ A [ star s l ]₀ →
    Γ ⊢ t₁ ⇒ t₂ ∷ Unit s l →
    s PE.≡ 𝕤 ⊎ ¬ Unitʷ-η →
    Γ ⊢ unitrec⟨ s ⟩ p q l A t₁ u ⇒* unitrec⟨ s ⟩ p q l A t₂ u ∷
      A [ t₁ ]₀
  unitrec⟨⟩-subst {s = 𝕨} _  _  _     (inj₁ ())
  unitrec⟨⟩-subst {s = 𝕨} ⊢A ⊢u t₁⇒t₂ (inj₂ not-ok) =
    case inversion-Unit (⊢∙→⊢ (wf ⊢A)) of λ
      (⊢l , ok) →
    redMany $
    unitrec-subst ⊢l ⊢A ⊢u t₁⇒t₂ ok not-ok
  unitrec⟨⟩-subst {s = 𝕤} {p} {q} ⊢A ⊢u t₁⇒t₂ _ =
    id $
    ⊢unitrec⟨⟩ {p = p} {q = q} ⊢A
      (syntacticEqTerm (subsetTerm t₁⇒t₂) .proj₂ .proj₁) ⊢u

opaque
  unfolding unitrec⟨_⟩

  -- Another equality rule for unitrec⟨_⟩.

  unitrec⟨⟩-cong :
    (s PE.≡ 𝕨 → Γ ⊢ l₁ ≡ l₂ ∷ Level) →
    Γ ∙ Unit s l₁ ⊢ A₁ ≡ A₂ →
    Γ ⊢ t₁ ≡ t₂ ∷ Unit s l₁ →
    Γ ⊢ u₁ ≡ u₂ ∷ A₁ [ star s l₁ ]₀ →
    Γ ⊢ unitrec⟨ s ⟩ p q l₁ A₁ t₁ u₁ ≡ unitrec⟨ s ⟩ p q l₂ A₂ t₂ u₂ ∷
      A₁ [ t₁ ]₀
  unitrec⟨⟩-cong {s = 𝕨} l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
    case inversion-Unit (⊢∙→⊢ (wfEq A₁≡A₂)) of λ
      (⊢l , _) →
    unitrec-cong′ (l₁≡l₂ PE.refl) A₁≡A₂ t₁≡t₂ u₁≡u₂
  unitrec⟨⟩-cong {s = 𝕤} _ A₁≡A₂ t₁≡t₂ u₁≡u₂ =
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
    Γ ⊢ Unit-η s p l t ∷ Id (Unit s l) (star s l) t
  ⊢Unit-η {t} {s} {l} ⊢t =
    case syntacticTerm ⊢t of λ
      ⊢Unit →
    case inversion-Unit ⊢Unit of λ
      (⊢l , ok) →
    PE.subst (_⊢_∷_ _ _) (PE.sym ≡Id-wk1-wk1-0[]₀) $
    ⊢unitrec⟨⟩ (Idⱼ′ (starⱼ (wkTerm₁ ⊢Unit ⊢l) ok) (var₀ ⊢Unit)) ⊢t $
    PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ $
    rflⱼ (starⱼ ⊢l ok)
