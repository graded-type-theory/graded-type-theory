------------------------------------------------------------------------
-- Eta-long normal forms
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Eta-long-normal-form
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Conversion R
open import Definition.Conversion.Consequences.Completeness R
open import Definition.Conversion.Consequences.InverseUniv R
open import Definition.Conversion.Soundness R

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.NeTypeEq R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Normal-form M type-variant

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n             : Nat
  x             : Fin _
  Γ Δ           : Con _ _
  A B C l l₁ l₂ t u v w : Term _
  b             : BinderMode
  s             : Strength
  p q q′ r      : M

------------------------------------------------------------------------
-- Definitions of η-long normal types and terms and some associated
-- concepts

mutual

  -- Γ ⊢nf A holds if A is a type in η-long normal form (with respect
  -- to the context Γ).

  infix 4 _⊢nf_

  data _⊢nf_ (Γ : Con Term n) : Term n → Set a where
    Levelₙ : ⊢ Γ →
             Γ ⊢nf Level
    univₙ  : Γ ⊢nf A ∷ U l →
             Γ ⊢nf A
    Liftₙ  : Γ ⊢nf l ∷ Level →
             Γ ⊢nf A →
             Γ ⊢nf Lift l A
    ΠΣₙ    : Γ ⊢nf A →
             Γ ∙ A ⊢nf B →
             ΠΣ-allowed b p q →
             Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
    Idₙ    : Γ ⊢nf A →
             Γ ⊢nf t ∷ A →
             Γ ⊢nf u ∷ A →
             Γ ⊢nf Id A t u

  -- Γ ⊢nf t ∷ A holds if t is a term in η-long normal form (with
  -- respect to the context Γ and the type A).

  infix 4 _⊢nf_∷_

  data _⊢nf_∷_ (Γ : Con Term n) : Term n → Term n → Set a where
    convₙ  : Γ ⊢nf t ∷ A →
             Γ ⊢ A ≡ B →
             Γ ⊢nf t ∷ B
    Levelₙ : ⊢ Γ →
             Level-is-small →
             Γ ⊢nf Level ∷ U zeroᵘ
    zeroᵘₙ : ⊢ Γ →
             Γ ⊢nf zeroᵘ ∷ Level
    sucᵘₙ  : Γ ⊢nf t ∷ Level →
             Γ ⊢nf sucᵘ t ∷ Level
    Uₙ     : Γ ⊢nf l ∷ Level →
             Γ ⊢nf U l ∷ U (sucᵘ l)
    Liftₙ  : Γ ⊢nf l₂ ∷ Level →
             Γ ⊢nf A ∷ U l₁ →
             Γ ⊢nf Lift l₂ A ∷ U (l₁ supᵘ l₂)
    liftₙ  : Γ ⊢ l₂ ∷ Level →
             Γ ⊢nf t ∷ A →
             Γ ⊢nf lift t ∷ Lift l₂ A
    ΠΣₙ    : Γ ⊢nf A ∷ U l →
             Γ ∙ A ⊢nf B ∷ U (wk1 l) →
             ΠΣ-allowed b p q →
             Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U l
    lamₙ   : Γ ∙ A ⊢nf t ∷ B →
             Π-allowed p q →
             Γ ⊢nf lam p t ∷ Π p , q ▷ A ▹ B
    prodₙ  : Γ ∙ A ⊢ B →
             Γ ⊢nf t ∷ A →
             Γ ⊢nf u ∷ B [ t ]₀ →
             Σ-allowed s p q →
             Γ ⊢nf prod s p t u ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
    Emptyₙ : ⊢ Γ →
             Γ ⊢nf Empty ∷ U zeroᵘ
    Unitₙ  : ⊢ Γ →
             Unit-allowed s →
             Γ ⊢nf Unit s ∷ U zeroᵘ
    starₙ  : ⊢ Γ →
             Unit-allowed s →
             Γ ⊢nf star s ∷ Unit s
    ℕₙ     : ⊢ Γ →
             Γ ⊢nf ℕ ∷ U zeroᵘ
    zeroₙ  : ⊢ Γ →
             Γ ⊢nf zero ∷ ℕ
    sucₙ   : Γ ⊢nf t ∷ ℕ →
             Γ ⊢nf suc t ∷ ℕ
    Idₙ    : Γ ⊢nf A ∷ U l →
             Γ ⊢nf t ∷ A →
             Γ ⊢nf u ∷ A →
             Γ ⊢nf Id A t u ∷ U l
    rflₙ   : Γ ⊢ t ∷ A →
             Γ ⊢nf rfl ∷ Id A t t
    neₙ    : No-η-equality A →
             Γ ⊢neˡ t ∷ A →
             Γ ⊢nf t ∷ A

  -- Γ ⊢neˡ t ∷ A holds if t is a neutral level for which the
  -- "non-neutral parts" are in η-long normal form.

  infix 4 _⊢neˡ_∷_

  data _⊢neˡ_∷_ (Γ : Con Term n) : Term n → Term n → Set a where
    supᵘˡₙ : Γ ⊢neˡ t ∷ Level
           → Γ ⊢nf u ∷ Level
           → Γ ⊢neˡ t supᵘ u ∷ Level
    supᵘʳₙ : Γ ⊢nf t ∷ Level
           → Γ ⊢neˡ u ∷ Level
           → Γ ⊢neˡ sucᵘ t supᵘ u ∷ Level
    neₙ    : Γ ⊢ne t ∷ A
           → Γ ⊢neˡ t ∷ A

  -- Γ ⊢ne t ∷ A holds if t is a neutral term (with respect to the
  -- context Γ and the type A) for which the "non-neutral parts" are
  -- in η-long normal form.

  infix 4 _⊢ne_∷_

  data _⊢ne_∷_ (Γ : Con Term n) : Term n → Term n → Set a where
    convₙ     : Γ ⊢ne t ∷ A →
                Γ ⊢ A ≡ B →
                Γ ⊢ne t ∷ B
    varₙ      : ⊢ Γ →
                x ∷ A ∈ Γ →
                Γ ⊢ne var x ∷ A
    lowerₙ    : Γ ⊢ne t ∷ Lift l A →
                Γ ⊢ne lower t ∷ A
    ∘ₙ        : Γ ⊢ne t ∷ Π p , q ▷ A ▹ B →
                Γ ⊢nf u ∷ A →
                Γ ⊢ne t ∘⟨ p ⟩ u ∷ B [ u ]₀
    fstₙ      : Γ ∙ A ⊢ B →
                Γ ⊢ne t ∷ Σˢ p , q ▷ A ▹ B →
                Γ ⊢ne fst p t ∷ A
    sndₙ      : Γ ∙ A ⊢ B →
                Γ ⊢ne t ∷ Σˢ p , q ▷ A ▹ B →
                Γ ⊢ne snd p t ∷ B [ fst p t ]₀
    prodrecₙ  : Γ ∙ Σʷ p , q′ ▷ A ▹ B ⊢nf C →
                Γ ⊢ne t ∷ Σʷ p , q′ ▷ A ▹ B →
                Γ ∙ A ∙ B ⊢nf u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
                Σʷ-allowed p q′ →
                Γ ⊢ne prodrec r p q C t u ∷ C [ t ]₀
    emptyrecₙ : Γ ⊢nf A →
                Γ ⊢ne t ∷ Empty →
                Γ ⊢ne emptyrec p A t ∷ A
    natrecₙ   : Γ ∙ ℕ ⊢nf A →
                Γ ⊢nf t ∷ A [ zero ]₀ →
                Γ ∙ ℕ ∙ A ⊢nf u ∷ A [ suc (var x1) ]↑² →
                Γ ⊢ne v ∷ ℕ →
                Γ ⊢ne natrec p q r A t u v ∷ A [ v ]₀
    unitrecₙ  : Γ ∙ Unitʷ ⊢nf A →
                Γ ⊢ne t ∷ Unitʷ →
                Γ ⊢nf u ∷ A [ starʷ ]₀ →
                Unitʷ-allowed →
                ¬ Unitʷ-η →
                Γ ⊢ne unitrec p q A t u ∷ A [ t ]₀
    Jₙ        : Γ ⊢nf A →
                Γ ⊢nf t ∷ A →
                Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢nf B →
                Γ ⊢nf u ∷ B [ t , rfl ]₁₀ →
                Γ ⊢nf v ∷ A →
                Γ ⊢ne w ∷ Id A t v →
                Γ ⊢ne J p q A t B u v w ∷ B [ v , w ]₁₀
    Kₙ        : Γ ⊢nf A →
                Γ ⊢nf t ∷ A →
                Γ ∙ Id A t t ⊢nf B →
                Γ ⊢nf u ∷ B [ rfl ]₀ →
                Γ ⊢ne v ∷ Id A t t →
                K-allowed →
                Γ ⊢ne K p A t B u v ∷ B [ v ]₀
    []-congₙ  : Γ ⊢nf l ∷ Level →
                Γ ⊢nf A ∷ U l →
                Γ ⊢nf t ∷ A →
                Γ ⊢nf u ∷ A →
                Γ ⊢ne v ∷ Id A t u →
                []-cong-allowed s →
                let open Erased s in
                Γ ⊢ne []-cong s l A t u v ∷
                  Id (Erased l A) ([ t ]) ([ u ])

------------------------------------------------------------------------
-- Some conversion functions

mutual

  -- If A is an η-long normal type, then A is well-typed.

  ⊢nf→⊢ : Γ ⊢nf A → Γ ⊢ A
  ⊢nf→⊢ = λ where
    (Levelₙ ⊢Γ)   → Levelⱼ′ ⊢Γ
    (Liftₙ ⊢l ⊢A) → Liftⱼ (⊢nf∷→⊢∷ ⊢l) (⊢nf→⊢ ⊢A)
    (univₙ ⊢A)    → univ (⊢nf∷→⊢∷ ⊢A)
    (ΠΣₙ _ ⊢B ok) → ΠΣⱼ (⊢nf→⊢ ⊢B) ok
    (Idₙ _ ⊢t ⊢u) → Idⱼ′ (⊢nf∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢u)

  -- If t is an η-long normal term, then t is well-typed.

  ⊢nf∷→⊢∷ : Γ ⊢nf t ∷ A → Γ ⊢ t ∷ A
  ⊢nf∷→⊢∷ = λ where
    (Levelₙ ⊢Γ ok)      → Levelⱼ ⊢Γ ok
    (zeroᵘₙ ⊢Γ)         → zeroᵘⱼ ⊢Γ
    (sucᵘₙ ⊢t)          → sucᵘⱼ (⊢nf∷→⊢∷ ⊢t)
    (convₙ ⊢t A≡B)      → conv (⊢nf∷→⊢∷ ⊢t) A≡B
    (Uₙ ⊢l)             → Uⱼ (⊢nf∷→⊢∷ ⊢l)
    (Liftₙ ⊢l ⊢A)       → Liftⱼ′ (⊢nf∷→⊢∷ ⊢l) (⊢nf∷→⊢∷ ⊢A)
    (liftₙ ⊢l ⊢t)       → liftⱼ′ ⊢l (⊢nf∷→⊢∷ ⊢t)
    (ΠΣₙ ⊢A ⊢B ok)      → ΠΣⱼ′ (⊢nf∷→⊢∷ ⊢A) (⊢nf∷→⊢∷ ⊢B) ok
    (lamₙ ⊢t ok)        → lamⱼ′ ok (⊢nf∷→⊢∷ ⊢t)
    (prodₙ ⊢B ⊢t ⊢u ok) → prodⱼ ⊢B (⊢nf∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢u) ok
    (Emptyₙ ⊢Γ)         → Emptyⱼ ⊢Γ
    (Unitₙ ⊢Γ ok)       → Unitⱼ ⊢Γ ok
    (starₙ ⊢Γ ok)       → starⱼ ⊢Γ ok
    (ℕₙ ⊢Γ)             → ℕⱼ ⊢Γ
    (zeroₙ ⊢Γ)          → zeroⱼ ⊢Γ
    (sucₙ ⊢t)           → sucⱼ (⊢nf∷→⊢∷ ⊢t)
    (Idₙ ⊢A ⊢t ⊢u)      → Idⱼ (⊢nf∷→⊢∷ ⊢A) (⊢nf∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢u)
    (rflₙ ⊢t)           → rflⱼ ⊢t
    (neₙ _ ⊢t)          → ⊢neˡ∷→⊢∷ ⊢t

  -- If Γ ⊢neˡ t ∷ A holds, then t is well-typed.

  ⊢neˡ∷→⊢∷ : Γ ⊢neˡ t ∷ A → Γ ⊢ t ∷ A
  ⊢neˡ∷→⊢∷ = λ where
    (supᵘˡₙ ⊢t ⊢u) → supᵘⱼ (⊢neˡ∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢u)
    (supᵘʳₙ ⊢t ⊢u) → supᵘⱼ (sucᵘⱼ (⊢nf∷→⊢∷ ⊢t)) (⊢neˡ∷→⊢∷ ⊢u)
    (neₙ x) → ⊢ne∷→⊢∷ x

  -- If Γ ⊢ne t ∷ A holds, then t is well-typed.

  ⊢ne∷→⊢∷ : Γ ⊢ne t ∷ A → Γ ⊢ t ∷ A
  ⊢ne∷→⊢∷ = λ where
    (convₙ ⊢t A≡B)            → conv (⊢ne∷→⊢∷ ⊢t) A≡B
    (varₙ ⊢Γ x∈)              → var ⊢Γ x∈
    (∘ₙ ⊢t ⊢u)                → ⊢ne∷→⊢∷ ⊢t ∘ⱼ ⊢nf∷→⊢∷ ⊢u
    (lowerₙ ⊢t)               → lowerⱼ (⊢ne∷→⊢∷ ⊢t)
    (fstₙ ⊢B ⊢t)              → fstⱼ ⊢B (⊢ne∷→⊢∷ ⊢t)
    (sndₙ ⊢B ⊢t)              → sndⱼ ⊢B (⊢ne∷→⊢∷ ⊢t)
    (prodrecₙ ⊢C ⊢t ⊢u ok)    → prodrecⱼ (⊢nf→⊢ ⊢C) (⊢ne∷→⊢∷ ⊢t)
                                  (⊢nf∷→⊢∷ ⊢u) ok
    (emptyrecₙ ⊢A ⊢t)         → emptyrecⱼ (⊢nf→⊢ ⊢A) (⊢ne∷→⊢∷ ⊢t)
    (natrecₙ _ ⊢t ⊢u ⊢v)      → natrecⱼ (⊢nf∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢u)
                                  (⊢ne∷→⊢∷ ⊢v)
    (unitrecₙ ⊢A ⊢t ⊢u ok _)  → unitrecⱼ (⊢nf→⊢ ⊢A) (⊢ne∷→⊢∷ ⊢t)
                                  (⊢nf∷→⊢∷ ⊢u) ok
    (Jₙ _ ⊢t ⊢B ⊢u ⊢v ⊢w)     → Jⱼ (⊢nf∷→⊢∷ ⊢t) (⊢nf→⊢ ⊢B) (⊢nf∷→⊢∷ ⊢u)
                                  (⊢nf∷→⊢∷ ⊢v) (⊢ne∷→⊢∷ ⊢w)
    (Kₙ _ _ ⊢B ⊢u ⊢v ok)      → Kⱼ (⊢nf→⊢ ⊢B) (⊢nf∷→⊢∷ ⊢u) (⊢ne∷→⊢∷ ⊢v)
                                  ok
    ([]-congₙ _ ⊢A _ _ ⊢v ok) → []-congⱼ′ ok (⊢nf∷→⊢∷ ⊢A) (⊢ne∷→⊢∷ ⊢v)

mutual

  -- If A is an η-long normal type, then A is normal.

  ⊢nf→Nf : Γ ⊢nf A → Nf A
  ⊢nf→Nf = λ where
    (Levelₙ _)     → Levelₙ
    (univₙ ⊢A)     → ⊢nf∷→Nf ⊢A
    (Liftₙ ⊢l ⊢A)  → Liftₙ (⊢nf∷→Nf ⊢l) (⊢nf→Nf ⊢A)
    (ΠΣₙ ⊢A ⊢B _)  → ΠΣₙ (⊢nf→Nf ⊢A) (⊢nf→Nf ⊢B)
    (Idₙ ⊢A ⊢t ⊢u) → Idₙ (⊢nf→Nf ⊢A) (⊢nf∷→Nf ⊢t) (⊢nf∷→Nf ⊢u)

  -- If t is an η-long normal term, then t is normal.

  ⊢nf∷→Nf : Γ ⊢nf t ∷ A → Nf t
  ⊢nf∷→Nf = λ where
    (convₙ ⊢t _)      → ⊢nf∷→Nf ⊢t
    (Levelₙ _ _)      → Levelₙ
    (zeroᵘₙ _)        → zeroᵘₙ
    (sucᵘₙ ⊢t)        → sucᵘₙ (⊢nf∷→Nf ⊢t)
    (Uₙ ⊢l)           → Uₙ (⊢nf∷→Nf ⊢l)
    (Liftₙ ⊢l ⊢A)     → Liftₙ (⊢nf∷→Nf ⊢l) (⊢nf∷→Nf ⊢A)
    (liftₙ ⊢l ⊢t)     → liftₙ (⊢nf∷→Nf ⊢t)
    (ΠΣₙ ⊢A ⊢B _)     → ΠΣₙ (⊢nf∷→Nf ⊢A) (⊢nf∷→Nf ⊢B)
    (lamₙ ⊢t _)       → lamₙ (⊢nf∷→Nf ⊢t)
    (prodₙ _ ⊢t ⊢u _) → prodₙ (⊢nf∷→Nf ⊢t) (⊢nf∷→Nf ⊢u)
    (Emptyₙ _)        → Emptyₙ
    (Unitₙ ⊢Γ _)      → Unitₙ
    (starₙ ⊢Γ _)      → starₙ
    (ℕₙ _)            → ℕₙ
    (zeroₙ _)         → zeroₙ
    (sucₙ ⊢t)         → sucₙ (⊢nf∷→Nf ⊢t)
    (Idₙ ⊢A ⊢t ⊢u)    → Idₙ (⊢nf∷→Nf ⊢A) (⊢nf∷→Nf ⊢t) (⊢nf∷→Nf ⊢u)
    (rflₙ ⊢t)         → rflₙ
    (neₙ _ ⊢t)        → ne (⊢neˡ∷→NfNeutralˡ ⊢t)

  -- If Γ ⊢neˡ t ∷ A holds, then t is "NfNeutralˡ".

  ⊢neˡ∷→NfNeutralˡ : Γ ⊢neˡ t ∷ A → NfNeutralˡ t
  ⊢neˡ∷→NfNeutralˡ = λ where
    (supᵘˡₙ ⊢t ⊢u) → supᵘˡₙ (⊢neˡ∷→NfNeutralˡ ⊢t) (⊢nf∷→Nf ⊢u)
    (supᵘʳₙ ⊢t ⊢u) → supᵘʳₙ (⊢nf∷→Nf ⊢t) (⊢neˡ∷→NfNeutralˡ ⊢u)
    (neₙ x) → ne (⊢ne∷→NfNeutral x)

  -- If Γ ⊢ne t ∷ A holds, then t is "NfNeutral".

  ⊢ne∷→NfNeutral : Γ ⊢ne t ∷ A → NfNeutral t
  ⊢ne∷→NfNeutral = λ where
    (convₙ ⊢t _)                 → ⊢ne∷→NfNeutral ⊢t
    (varₙ _ _)                   → var _
    (lowerₙ ⊢t)                  → lowerₙ (⊢ne∷→NfNeutral ⊢t)
    (∘ₙ ⊢t ⊢u)                   → ∘ₙ (⊢ne∷→NfNeutral ⊢t) (⊢nf∷→Nf ⊢u)
    (fstₙ _ ⊢t)                  → fstₙ (⊢ne∷→NfNeutral ⊢t)
    (sndₙ _ ⊢t)                  → sndₙ (⊢ne∷→NfNeutral ⊢t)
    (prodrecₙ ⊢C ⊢t ⊢u _)        → prodrecₙ (⊢nf→Nf ⊢C)
                                     (⊢ne∷→NfNeutral ⊢t) (⊢nf∷→Nf ⊢u)
    (emptyrecₙ ⊢A ⊢t)            → emptyrecₙ (⊢nf→Nf ⊢A)
                                     (⊢ne∷→NfNeutral ⊢t)
    (natrecₙ ⊢A ⊢t ⊢u ⊢v)        → natrecₙ (⊢nf→Nf ⊢A) (⊢nf∷→Nf ⊢t)
                                     (⊢nf∷→Nf ⊢u) (⊢ne∷→NfNeutral ⊢v)
    (unitrecₙ ⊢A ⊢t ⊢u _ not-ok) → unitrecₙ not-ok (⊢nf→Nf ⊢A)
                                     (⊢ne∷→NfNeutral ⊢t) (⊢nf∷→Nf ⊢u)
    (Jₙ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w)       → Jₙ (⊢nf→Nf ⊢A) (⊢nf∷→Nf ⊢t)
                                     (⊢nf→Nf ⊢B) (⊢nf∷→Nf ⊢u)
                                     (⊢nf∷→Nf ⊢v) (⊢ne∷→NfNeutral ⊢w)
    (Kₙ ⊢A ⊢t ⊢B ⊢u ⊢v _)        → Kₙ (⊢nf→Nf ⊢A) (⊢nf∷→Nf ⊢t)
                                     (⊢nf→Nf ⊢B) (⊢nf∷→Nf ⊢u)
                                     (⊢ne∷→NfNeutral ⊢v)
    ([]-congₙ ⊢l ⊢A ⊢t ⊢u ⊢v _)  → []-congₙ (⊢nf∷→Nf ⊢l) (⊢nf∷→Nf ⊢A)
                                     (⊢nf∷→Nf ⊢t) (⊢nf∷→Nf ⊢u)
                                     (⊢ne∷→NfNeutral ⊢v)

------------------------------------------------------------------------
-- A lemma

opaque

  -- If A is a normal type of type U l, then A is a normal term of
  -- type U l (if equality reflection is not allowed).

  ⊢nf∷U→⊢nf∷U :
    ⦃ not-ok : No-equality-reflection ⦄ →
    Γ ⊢nf A → Γ ⊢ A ∷ U l → Γ ⊢nf A ∷ U l
  ⊢nf∷U→⊢nf∷U = λ where
    (Levelₙ ⊢Γ) ⊢Level →
      let A≡ , ok = inversion-Level ⊢Level
      in convₙ (Levelₙ ⊢Γ ok) (sym A≡)
    (univₙ ⊢A) ⊢A∷U →
      convₙ ⊢A (U-cong (universe-level-unique (⊢nf∷→⊢∷ ⊢A) ⊢A∷U))
    (Liftₙ ⊢l ⊢A) ⊢A∷U →
      let _ , ⊢l′ , ⊢A∷ , U≡U = inversion-Lift∷ ⊢A∷U
      in convₙ (Liftₙ ⊢l (⊢nf∷U→⊢nf∷U ⊢A ⊢A∷)) (sym U≡U)
    (ΠΣₙ ⊢A ⊢B ok) ⊢ΠΣ →
      let _ , _ , ⊢A∷U , ⊢B∷U , U≡U , _ = inversion-ΠΣ-U ⊢ΠΣ in
      convₙ (ΠΣₙ (⊢nf∷U→⊢nf∷U ⊢A ⊢A∷U) (⊢nf∷U→⊢nf∷U ⊢B ⊢B∷U) ok)
        (sym U≡U)
    (Idₙ ⊢A ⊢t ⊢u) ⊢Id →
      let _ , ⊢A∷U , _ , _ , U≡U = inversion-Id-U ⊢Id in
      convₙ (Idₙ (⊢nf∷U→⊢nf∷U ⊢A ⊢A∷U) ⊢t ⊢u) (sym U≡U)

------------------------------------------------------------------------
-- Stability

mutual

  -- If A is a normal type with respect to the context Γ, and Γ is
  -- judgmentally equal to Δ, then A is also a normal type with
  -- respect to Δ.

  ⊢nf-stable : ⊢ Γ ≡ Δ → Γ ⊢nf A → Δ ⊢nf A
  ⊢nf-stable Γ≡Δ = λ where
      (Levelₙ ⊢Γ)    → Levelₙ ⊢Δ
      (univₙ ⊢A)     → univₙ (⊢nf∷-stable Γ≡Δ ⊢A)
      (Liftₙ ⊢l ⊢A)  → Liftₙ (⊢nf∷-stable Γ≡Δ ⊢l) (⊢nf-stable Γ≡Δ ⊢A)
      (ΠΣₙ ⊢A ⊢B ok) → ΠΣₙ (⊢nf-stable Γ≡Δ ⊢A)
                         (⊢nf-stable (Γ≡Δ ∙ refl (⊢nf→⊢ ⊢A)) ⊢B) ok
      (Idₙ ⊢A ⊢t ⊢u) → Idₙ (⊢nf-stable Γ≡Δ ⊢A) (⊢nf∷-stable Γ≡Δ ⊢t)
                         (⊢nf∷-stable Γ≡Δ ⊢u)
    where
    ⊢Δ = contextConvSubst Γ≡Δ .proj₂ .proj₁

  -- If t is a normal term with respect to the context Γ, and Γ is
  -- judgmentally equal to Δ, then t is also a normal term with
  -- respect to Δ.

  ⊢nf∷-stable : ⊢ Γ ≡ Δ → Γ ⊢nf t ∷ A → Δ ⊢nf t ∷ A
  ⊢nf∷-stable Γ≡Δ = λ where
      (convₙ ⊢t B≡A) → convₙ
        (⊢nf∷-stable Γ≡Δ ⊢t)
        (stabilityEq Γ≡Δ B≡A)
      (Levelₙ ⊢Γ ok) → Levelₙ ⊢Δ ok
      (zeroᵘₙ ⊢Γ)   → zeroᵘₙ ⊢Δ
      (sucᵘₙ ⊢t)    → sucᵘₙ
        (⊢nf∷-stable Γ≡Δ ⊢t)
      (Uₙ ⊢l)       → Uₙ (⊢nf∷-stable Γ≡Δ ⊢l)
      (Liftₙ ⊢l ⊢A) → Liftₙ (⊢nf∷-stable Γ≡Δ ⊢l) (⊢nf∷-stable Γ≡Δ ⊢A)
      (liftₙ ⊢l ⊢t) → liftₙ (stabilityTerm Γ≡Δ ⊢l) (⊢nf∷-stable Γ≡Δ ⊢t)
      (ΠΣₙ ⊢A ⊢B ok) → ΠΣₙ
        (⊢nf∷-stable Γ≡Δ ⊢A)
        (⊢nf∷-stable (Γ≡Δ ∙ refl (⊢nf→⊢ (univₙ ⊢A))) ⊢B)
        ok
      (lamₙ ⊢t ok) → lamₙ
        (⊢nf∷-stable (Γ≡Δ ∙ refl (⊢∙→⊢ (wfTerm (⊢nf∷→⊢∷ ⊢t)))) ⊢t)
        ok
      (prodₙ ⊢B ⊢t ⊢u ok) → prodₙ
        (stability (Γ≡Δ ∙ refl (⊢∙→⊢ (wf ⊢B))) ⊢B)
        (⊢nf∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable Γ≡Δ ⊢u)
        ok
      (Emptyₙ ⊢Γ)   → Emptyₙ ⊢Δ
      (Unitₙ ⊢Γ ok) → Unitₙ ⊢Δ ok
      (starₙ ⊢Γ ok) → starₙ ⊢Δ ok
      (ℕₙ ⊢Γ)       → ℕₙ ⊢Δ
      (zeroₙ ⊢Γ)    → zeroₙ ⊢Δ
      (sucₙ ⊢t)     → sucₙ
        (⊢nf∷-stable Γ≡Δ ⊢t)
      (Idₙ ⊢A ⊢t ⊢u) → Idₙ
        (⊢nf∷-stable Γ≡Δ ⊢A)
        (⊢nf∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable Γ≡Δ ⊢u)
      (rflₙ ⊢t) → rflₙ
        (stabilityTerm Γ≡Δ ⊢t)
      (neₙ ok ⊢t) → neₙ
        ok
        (⊢neˡ∷-stable Γ≡Δ ⊢t)
    where
    ⊢Δ = contextConvSubst Γ≡Δ .proj₂ .proj₁

  -- If t is a neutral level (according to _⊢neˡ_∷_) with respect to the
  -- context Γ, and Γ is judgmentally equal to Δ, then t is also a
  -- neutral level with respect to Δ.

  ⊢neˡ∷-stable : ⊢ Γ ≡ Δ → Γ ⊢neˡ t ∷ A → Δ ⊢neˡ t ∷ A
  ⊢neˡ∷-stable Γ≡Δ = λ where
      (supᵘˡₙ ⊢t ⊢u) → supᵘˡₙ (⊢neˡ∷-stable Γ≡Δ ⊢t) (⊢nf∷-stable Γ≡Δ ⊢u)
      (supᵘʳₙ ⊢t ⊢u) → supᵘʳₙ (⊢nf∷-stable Γ≡Δ ⊢t) (⊢neˡ∷-stable Γ≡Δ ⊢u)
      (neₙ x)        → neₙ (⊢ne∷-stable Γ≡Δ x)
    where
    ⊢Δ = contextConvSubst Γ≡Δ .proj₂ .proj₁

  -- If t is a neutral term (according to _⊢ne_∷_) with respect to the
  -- context Γ, and Γ is judgmentally equal to Δ, then t is also a
  -- neutral term with respect to Δ.

  ⊢ne∷-stable : ⊢ Γ ≡ Δ → Γ ⊢ne t ∷ A → Δ ⊢ne t ∷ A
  ⊢ne∷-stable Γ≡Δ = λ where
      (convₙ ⊢t B≡A) → convₙ
        (⊢ne∷-stable Γ≡Δ ⊢t)
        (stabilityEq Γ≡Δ B≡A)
      (varₙ ⊢Γ x∷A∈Γ) →
        case inversion-var (stabilityTerm Γ≡Δ (var ⊢Γ x∷A∈Γ)) of λ {
          (B , x∷B∈Δ , A≡B) →
        convₙ (varₙ ⊢Δ x∷B∈Δ) (sym A≡B) }
      (lowerₙ ⊢t) → lowerₙ
        (⊢ne∷-stable Γ≡Δ ⊢t)
      (∘ₙ ⊢t ⊢u) → ∘ₙ
        (⊢ne∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable Γ≡Δ ⊢u)
      (fstₙ ⊢B ⊢t) → fstₙ
        (stability (Γ≡Δ ∙ refl (⊢∙→⊢ (wf ⊢B))) ⊢B)
        (⊢ne∷-stable Γ≡Δ ⊢t)
      (sndₙ ⊢B ⊢t) → sndₙ
        (stability (Γ≡Δ ∙ refl (⊢∙→⊢ (wf ⊢B))) ⊢B)
        (⊢ne∷-stable Γ≡Δ ⊢t)
      (prodrecₙ ⊢C ⊢t ⊢u ok) →
        let ⊢B = ⊢∙→⊢ (wfTerm (⊢nf∷→⊢∷ ⊢u)) in
        prodrecₙ (⊢nf-stable (Γ≡Δ ∙ refl (ΠΣⱼ ⊢B ok)) ⊢C)
          (⊢ne∷-stable Γ≡Δ ⊢t)
          (⊢nf∷-stable (Γ≡Δ ∙ refl (⊢∙→⊢ (wf ⊢B)) ∙ refl ⊢B) ⊢u) ok
      (emptyrecₙ ⊢A ⊢t) → emptyrecₙ
        (⊢nf-stable Γ≡Δ ⊢A)
        (⊢ne∷-stable Γ≡Δ ⊢t)
      (natrecₙ ⊢A ⊢t ⊢u ⊢v) →
        case Γ≡Δ ∙ refl (⊢ℕ (wfTerm (⊢nf∷→⊢∷ ⊢t))) of λ {
          ⊢Γℕ≡Δℕ → natrecₙ
        (⊢nf-stable ⊢Γℕ≡Δℕ ⊢A)
        (⊢nf∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable (⊢Γℕ≡Δℕ ∙ refl (⊢nf→⊢ ⊢A)) ⊢u)
        (⊢ne∷-stable Γ≡Δ ⊢v) }
      (unitrecₙ ⊢A ⊢t ⊢u ok not-ok) →
        case Γ≡Δ ∙ refl (⊢Unit (wfTerm (⊢nf∷→⊢∷ ⊢u)) ok) of λ {
          ⊢Γ⊤≡Δ⊤ → unitrecₙ
        (⊢nf-stable ⊢Γ⊤≡Δ⊤ ⊢A)
        (⊢ne∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable Γ≡Δ ⊢u) ok not-ok }
      (Jₙ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) → Jₙ
        (⊢nf-stable Γ≡Δ ⊢A)
        (⊢nf∷-stable Γ≡Δ ⊢t)
        (⊢nf-stable
           (J-motive-context-cong Γ≡Δ (refl (⊢nf→⊢ ⊢A))
              (refl (⊢nf∷→⊢∷ ⊢t)))
           ⊢B)
        (⊢nf∷-stable Γ≡Δ ⊢u)
        (⊢nf∷-stable Γ≡Δ ⊢v)
        (⊢ne∷-stable Γ≡Δ ⊢w)
      (Kₙ ⊢A ⊢t ⊢B ⊢u ⊢v ok) → Kₙ
        (⊢nf-stable Γ≡Δ ⊢A)
        (⊢nf∷-stable Γ≡Δ ⊢t)
        (⊢nf-stable (Γ≡Δ ∙ refl (Idⱼ′ (⊢nf∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢t))) ⊢B)
        (⊢nf∷-stable Γ≡Δ ⊢u)
        (⊢ne∷-stable Γ≡Δ ⊢v)
        ok
      ([]-congₙ ⊢l ⊢A ⊢t ⊢u ⊢v ok) → []-congₙ
        (⊢nf∷-stable Γ≡Δ ⊢l)
        (⊢nf∷-stable Γ≡Δ ⊢A)
        (⊢nf∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable Γ≡Δ ⊢u)
        (⊢ne∷-stable Γ≡Δ ⊢v)
        ok
    where
    ⊢Δ = contextConvSubst Γ≡Δ .proj₂ .proj₁

------------------------------------------------------------------------
-- Inversion lemmas

-- Inversion for terms that are Π- or Σ-types.

inversion-nf-ΠΣ-U :
  Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ C →
  ∃ λ l →
  Γ ⊢nf A ∷ U l × Γ ∙ A ⊢nf B ∷ U (wk1 l) × Γ ⊢ C ≡ U l ×
  ΠΣ-allowed b p q
inversion-nf-ΠΣ-U (ΠΣₙ ⊢A ⊢B ok) =
  _ , ⊢A , ⊢B ,
  refl (⊢U (inversion-U-Level (syntacticTerm (⊢nf∷→⊢∷ ⊢A)))) , ok
inversion-nf-ΠΣ-U (convₙ ⊢ΠΣ D≡C) =
  case inversion-nf-ΠΣ-U ⊢ΠΣ of λ {
    (_ , ⊢A , ⊢B , D≡U , ok) →
  _ , ⊢A , ⊢B , trans (sym D≡C) D≡U , ok }
inversion-nf-ΠΣ-U (neₙ _ ⊢ΠΣ) =
  case ⊢neˡ∷→NfNeutralˡ ⊢ΠΣ of λ { (ne ()) }

-- Inversion for Π- and Σ-types.

inversion-nf-ΠΣ :
  Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  Γ ⊢nf A × Γ ∙ A ⊢nf B × ΠΣ-allowed b p q
inversion-nf-ΠΣ = λ where
  (ΠΣₙ ⊢A ⊢B ok) → ⊢A , ⊢B , ok
  (univₙ ⊢ΠΣAB)  → case inversion-nf-ΠΣ-U ⊢ΠΣAB of λ where
    (_ , ⊢A , ⊢B , _ , ok) → univₙ ⊢A , univₙ ⊢B , ok

-- Inversion for lam.

inversion-nf-lam :
  Γ ⊢nf lam p t ∷ A →
  ∃₃ λ B C q →
     Γ ∙ B ⊢nf t ∷ C ×
     Γ ⊢ A ≡ Π p , q ▷ B ▹ C ×
     Π-allowed p q
inversion-nf-lam (neₙ _ ⊢lam) =
  case ⊢neˡ∷→NfNeutralˡ ⊢lam of λ { (ne ()) }
inversion-nf-lam (lamₙ ⊢t ok) =
  _ , _ , _ , ⊢t , refl (ΠΣⱼ (syntacticTerm (⊢nf∷→⊢∷ ⊢t)) ok) , ok
inversion-nf-lam (convₙ ⊢lam A≡B) =
  case inversion-nf-lam ⊢lam of λ {
    (_ , _ , _ , ⊢t , A≡ , ok) →
  _ , _ , _ , ⊢t , trans (sym A≡B) A≡ , ok }

-- Inversion for prod.

inversion-nf-prod :
  Γ ⊢nf prod s p t u ∷ A →
  ∃₃ λ B C q →
    (Γ ∙ B ⊢ C) ×
    Γ ⊢nf t ∷ B × Γ ⊢nf u ∷ C [ t ]₀ ×
    Γ ⊢ A ≡ Σ⟨ s ⟩ p , q ▷ B ▹ C ×
    Σ-allowed s p q
inversion-nf-prod (neₙ _ ⊢prod) =
  case ⊢neˡ∷→NfNeutralˡ ⊢prod of λ { (ne ()) }
inversion-nf-prod (prodₙ ⊢C ⊢t ⊢u ok) =
  _ , _ , _ , ⊢C , ⊢t , ⊢u , refl (ΠΣⱼ ⊢C ok) , ok
inversion-nf-prod (convₙ ⊢prod A≡B) =
  case inversion-nf-prod ⊢prod of λ {
    (_ , _ , _ , ⊢C , ⊢t , ⊢u , A≡ , ok) →
  _ , _ , _ , ⊢C , ⊢t , ⊢u , trans (sym A≡B) A≡ , ok }

-- Inversion for suc.

inversion-nf-suc :
  Γ ⊢nf suc t ∷ A →
  Γ ⊢nf t ∷ ℕ × Γ ⊢ A ≡ ℕ
inversion-nf-suc (neₙ _ ⊢suc) =
  case ⊢neˡ∷→NfNeutralˡ ⊢suc of λ { (ne ()) }
inversion-nf-suc (sucₙ ⊢t) =
  ⊢t , refl (⊢ℕ (wfTerm (⊢nf∷→⊢∷ ⊢t)))
inversion-nf-suc (convₙ ⊢suc A≡B) =
  case inversion-nf-suc ⊢suc of λ {
    (⊢t , A≡) →
  ⊢t , trans (sym A≡B) A≡ }

-- Inversion for application.

inversion-ne-app :
  Γ ⊢ne t ∘⟨ p ⟩ u ∷ A →
  ∃₃ λ B C q →
     Γ ⊢ne t ∷ Π p , q ▷ B ▹ C × Γ ⊢nf u ∷ B × Γ ⊢ A ≡ C [ u ]₀
inversion-ne-app (∘ₙ ⊢t ⊢u) =
  _ , _ , _ , ⊢t , ⊢u ,
  refl (substTypeΠ (syntacticTerm (⊢ne∷→⊢∷ ⊢t)) (⊢nf∷→⊢∷ ⊢u))
inversion-ne-app (convₙ ⊢app A≡B) =
  case inversion-ne-app ⊢app of λ {
    (_ , _ , _ , ⊢t , ⊢u , A≡) →
  _ , _ , _ , ⊢t , ⊢u , trans (sym A≡B) A≡ }

inversion-neˡ-app :
  Γ ⊢neˡ t ∘⟨ p ⟩ u ∷ A →
  ∃₃ λ B C q →
     Γ ⊢ne t ∷ Π p , q ▷ B ▹ C × Γ ⊢nf u ∷ B × Γ ⊢ A ≡ C [ u ]₀
inversion-neˡ-app (neₙ x) = inversion-ne-app x

inversion-nf-app :
  Γ ⊢nf t ∘⟨ p ⟩ u ∷ A →
  ∃₃ λ B C q →
     Γ ⊢ne t ∷ Π p , q ▷ B ▹ C × Γ ⊢nf u ∷ B × Γ ⊢ A ≡ C [ u ]₀
inversion-nf-app (neₙ _ ⊢app) =
  inversion-neˡ-app ⊢app
inversion-nf-app (convₙ ⊢app A≡B) =
  case inversion-nf-app ⊢app of λ {
    (_ , _ , _ , ⊢t , ⊢u , A≡) →
  _ , _ , _ , ⊢t , ⊢u , trans (sym A≡B) A≡ }

inversion-nf-ne-app :
  Γ ⊢nf t ∘⟨ p ⟩ u ∷ A ⊎ Γ ⊢ne t ∘⟨ p ⟩ u ∷ A →
  ∃₃ λ B C q →
     Γ ⊢ne t ∷ Π p , q ▷ B ▹ C × Γ ⊢nf u ∷ B × Γ ⊢ A ≡ C [ u ]₀
inversion-nf-ne-app (inj₁ ⊢app) = inversion-nf-app ⊢app
inversion-nf-ne-app (inj₂ ⊢app) = inversion-ne-app ⊢app

-- Inversion for fst.

inversion-ne-fst :
  Γ ⊢ne fst p t ∷ A →
  ∃₃ λ B C q → (Γ ∙ B ⊢ C) × Γ ⊢ne t ∷ Σˢ p , q ▷ B ▹ C × Γ ⊢ A ≡ B
inversion-ne-fst (fstₙ ⊢C ⊢t) =
  _ , _ , _ , ⊢C , ⊢t , refl (⊢∙→⊢ (wf ⊢C))
inversion-ne-fst (convₙ ⊢fst A≡B) =
  case inversion-ne-fst ⊢fst of λ {
    (_ , _ , _ , ⊢C , ⊢t , A≡) →
  _ , _ , _ , ⊢C , ⊢t , trans (sym A≡B) A≡ }

inversion-neˡ-fst :
  Γ ⊢neˡ fst p t ∷ A →
  ∃₃ λ B C q → (Γ ∙ B ⊢ C) × Γ ⊢ne t ∷ Σˢ p , q ▷ B ▹ C × Γ ⊢ A ≡ B
inversion-neˡ-fst (neₙ x) = inversion-ne-fst x

inversion-nf-fst :
  Γ ⊢nf fst p t ∷ A →
  ∃₃ λ B C q → (Γ ∙ B ⊢ C) × Γ ⊢ne t ∷ Σˢ p , q ▷ B ▹ C × Γ ⊢ A ≡ B
inversion-nf-fst (neₙ _ ⊢fst) =
  inversion-neˡ-fst ⊢fst
inversion-nf-fst (convₙ ⊢fst A≡B) =
  case inversion-nf-fst ⊢fst of λ {
    (_ , _ , _ , ⊢C , ⊢t , A≡) →
  _ , _ , _ , ⊢C , ⊢t , trans (sym A≡B) A≡ }

inversion-nf-ne-fst :
  Γ ⊢nf fst p t ∷ A ⊎ Γ ⊢ne fst p t ∷ A →
  ∃₃ λ B C q → (Γ ∙ B ⊢ C) × Γ ⊢ne t ∷ Σˢ p , q ▷ B ▹ C × Γ ⊢ A ≡ B
inversion-nf-ne-fst (inj₁ ⊢fst) = inversion-nf-fst ⊢fst
inversion-nf-ne-fst (inj₂ ⊢fst) = inversion-ne-fst ⊢fst

-- Inversion for snd.

inversion-ne-snd :
  Γ ⊢ne snd p t ∷ A →
  ∃₃ λ B C q →
     (Γ ∙ B ⊢ C) ×
     Γ ⊢ne t ∷ Σˢ p , q ▷ B ▹ C ×
     Γ ⊢ A ≡ C [ fst p t ]₀
inversion-ne-snd (sndₙ ⊢C ⊢t) =
  _ , _ , _ , ⊢C , ⊢t ,
  refl (substType ⊢C (fstⱼ ⊢C (⊢ne∷→⊢∷ ⊢t)))
inversion-ne-snd (convₙ ⊢snd A≡B) =
  case inversion-ne-snd ⊢snd of λ {
    (_ , _ , _ , ⊢C , ⊢t , A≡) →
  _ , _ , _ , ⊢C , ⊢t , trans (sym A≡B) A≡ }

inversion-neˡ-snd :
  Γ ⊢neˡ snd p t ∷ A →
  ∃₃ λ B C q →
     (Γ ∙ B ⊢ C) ×
     Γ ⊢ne t ∷ Σˢ p , q ▷ B ▹ C ×
     Γ ⊢ A ≡ C [ fst p t ]₀
inversion-neˡ-snd (neₙ x) = inversion-ne-snd x

inversion-nf-snd :
  Γ ⊢nf snd p t ∷ A →
  ∃₃ λ B C q →
     (Γ ∙ B ⊢ C) ×
     Γ ⊢ne t ∷ Σˢ p , q ▷ B ▹ C ×
     Γ ⊢ A ≡ C [ fst p t ]₀
inversion-nf-snd (neₙ _ ⊢snd) =
  inversion-neˡ-snd ⊢snd
inversion-nf-snd (convₙ ⊢snd A≡B) =
  case inversion-nf-snd ⊢snd of λ {
    (_ , _ , _ , ⊢C , ⊢t , A≡) →
  _ , _ , _ , ⊢C , ⊢t , trans (sym A≡B) A≡ }

inversion-nf-ne-snd :
  Γ ⊢nf snd p t ∷ A ⊎ Γ ⊢ne snd p t ∷ A →
  ∃₃ λ B C q →
     (Γ ∙ B ⊢ C) ×
     Γ ⊢ne t ∷ Σˢ p , q ▷ B ▹ C ×
     Γ ⊢ A ≡ C [ fst p t ]₀
inversion-nf-ne-snd (inj₁ ⊢snd) = inversion-nf-snd ⊢snd
inversion-nf-ne-snd (inj₂ ⊢snd) = inversion-ne-snd ⊢snd

-- Inversion for prodrec.

inversion-ne-prodrec :
  Γ ⊢ne prodrec r p q A t u ∷ B →
  ∃₃ λ C D q →
    (Γ ∙ (Σʷ p , q ▷ C ▹ D) ⊢nf A) ×
    Γ ⊢ne t ∷ Σʷ p , q ▷ C ▹ D ×
    Γ ∙ C ∙ D ⊢nf u ∷ A [ prodʷ p (var x1) (var x0) ]↑² ×
    Γ ⊢ B ≡ A [ t ]₀
inversion-ne-prodrec (prodrecₙ ⊢A ⊢t ⊢u _) =
  _ , _ , _ , ⊢A , ⊢t , ⊢u ,
  refl (substType (⊢nf→⊢ ⊢A) (⊢ne∷→⊢∷ ⊢t))
inversion-ne-prodrec (convₙ ⊢pr B≡C) =
  case inversion-ne-prodrec ⊢pr of λ {
    (_ , _ , _ , ⊢A , ⊢t , ⊢u , B≡) →
  _ , _ , _ , ⊢A , ⊢t , ⊢u , trans (sym B≡C) B≡ }

inversion-nf-prodrec :
  Γ ⊢nf prodrec r p q A t u ∷ B →
  ∃₃ λ C D q →
    (Γ ∙ (Σʷ p , q ▷ C ▹ D) ⊢nf A) ×
    Γ ⊢ne t ∷ Σʷ p , q ▷ C ▹ D ×
    Γ ∙ C ∙ D ⊢nf u ∷ A [ prodʷ p (var x1) (var x0) ]↑² ×
    Γ ⊢ B ≡ A [ t ]₀
inversion-nf-prodrec (neₙ _ (neₙ ⊢pr)) =
  inversion-ne-prodrec ⊢pr
inversion-nf-prodrec (convₙ ⊢pr B≡C) =
  case inversion-nf-prodrec ⊢pr of λ {
    (_ , _ , _ , ⊢A , ⊢t , ⊢u , B≡) →
  _ , _ , _ , ⊢A , ⊢t , ⊢u , trans (sym B≡C) B≡ }

inversion-nf-ne-prodrec :
  Γ ⊢nf prodrec r p q A t u ∷ B ⊎ Γ ⊢ne prodrec r p q A t u ∷ B →
  ∃₃ λ C D q →
    (Γ ∙ (Σʷ p , q ▷ C ▹ D) ⊢nf A) ×
    Γ ⊢ne t ∷ Σʷ p , q ▷ C ▹ D ×
    Γ ∙ C ∙ D ⊢nf u ∷ A [ prodʷ p (var x1) (var x0) ]↑² ×
    Γ ⊢ B ≡ A [ t ]₀
inversion-nf-ne-prodrec (inj₁ ⊢pr) = inversion-nf-prodrec ⊢pr
inversion-nf-ne-prodrec (inj₂ ⊢pr) = inversion-ne-prodrec ⊢pr

-- Inversion for emptyrec.

inversion-ne-emptyrec :
  Γ ⊢ne emptyrec p A t ∷ B →
  Γ ⊢nf A × Γ ⊢ne t ∷ Empty × Γ ⊢ B ≡ A
inversion-ne-emptyrec (emptyrecₙ ⊢A ⊢t) =
  ⊢A , ⊢t , refl (⊢nf→⊢ ⊢A)
inversion-ne-emptyrec (convₙ ⊢er A≡B) =
  case inversion-ne-emptyrec ⊢er of λ {
    (⊢A , ⊢t , A≡) →
  ⊢A , ⊢t , trans (sym A≡B) A≡ }

inversion-nf-emptyrec :
  Γ ⊢nf emptyrec p A t ∷ B →
  Γ ⊢nf A × Γ ⊢ne t ∷ Empty × Γ ⊢ B ≡ A
inversion-nf-emptyrec (neₙ _ (neₙ ⊢er)) =
  inversion-ne-emptyrec ⊢er
inversion-nf-emptyrec (convₙ ⊢er A≡B) =
  case inversion-nf-emptyrec ⊢er of λ {
    (⊢A , ⊢t , A≡) →
  ⊢A , ⊢t , trans (sym A≡B) A≡ }

inversion-nf-ne-emptyrec :
  Γ ⊢nf emptyrec p A t ∷ B ⊎ Γ ⊢ne emptyrec p A t ∷ B →
  Γ ⊢nf A × Γ ⊢ne t ∷ Empty × Γ ⊢ B ≡ A
inversion-nf-ne-emptyrec (inj₁ ⊢er) = inversion-nf-emptyrec ⊢er
inversion-nf-ne-emptyrec (inj₂ ⊢er) = inversion-ne-emptyrec ⊢er

-- Inversion for natrec.

inversion-ne-natrec :
  Γ ⊢ne natrec p q r A t u v ∷ B →
  (Γ ∙ ℕ ⊢nf A) ×
  Γ ⊢nf t ∷ A [ zero ]₀ ×
  Γ ∙ ℕ ∙ A ⊢nf u ∷ A [ suc (var x1) ]↑² ×
  Γ ⊢ne v ∷ ℕ ×
  Γ ⊢ B ≡ A [ v ]₀
inversion-ne-natrec (natrecₙ ⊢A ⊢t ⊢u ⊢v) =
  ⊢A , ⊢t , ⊢u , ⊢v ,
  refl (substType (⊢nf→⊢ ⊢A) (⊢ne∷→⊢∷ ⊢v))
inversion-ne-natrec (convₙ ⊢pr B≡C) =
  case inversion-ne-natrec ⊢pr of λ {
    (⊢A , ⊢t , ⊢u , ⊢v , B≡) →
  ⊢A , ⊢t , ⊢u , ⊢v , trans (sym B≡C) B≡ }

inversion-nf-natrec :
  Γ ⊢nf natrec p q r A t u v ∷ B →
  (Γ ∙ ℕ ⊢nf A) ×
  Γ ⊢nf t ∷ A [ zero ]₀ ×
  Γ ∙ ℕ ∙ A ⊢nf u ∷ A [ suc (var x1) ]↑² ×
  Γ ⊢ne v ∷ ℕ ×
  Γ ⊢ B ≡ A [ v ]₀
inversion-nf-natrec (neₙ _ (neₙ ⊢nr)) =
  inversion-ne-natrec ⊢nr
inversion-nf-natrec (convₙ ⊢pr B≡C) =
  case inversion-nf-natrec ⊢pr of λ {
    (⊢A , ⊢t , ⊢u , ⊢v , B≡) →
  ⊢A , ⊢t , ⊢u , ⊢v , trans (sym B≡C) B≡ }

inversion-nf-ne-natrec :
  Γ ⊢nf natrec p q r A t u v ∷ B ⊎ Γ ⊢ne natrec p q r A t u v ∷ B →
  (Γ ∙ ℕ ⊢nf A) ×
  Γ ⊢nf t ∷ A [ zero ]₀ ×
  Γ ∙ ℕ ∙ A ⊢nf u ∷ A [ suc (var x1) ]↑² ×
  Γ ⊢ne v ∷ ℕ ×
  Γ ⊢ B ≡ A [ v ]₀
inversion-nf-ne-natrec (inj₁ ⊢nr) = inversion-nf-natrec ⊢nr
inversion-nf-ne-natrec (inj₂ ⊢nr) = inversion-ne-natrec ⊢nr

opaque

  -- Inversion for terms that are identity types.

  inversion-nf-Id-U :
    Γ ⊢nf Id A t u ∷ B →
    ∃ λ l → Γ ⊢nf A ∷ U l × Γ ⊢nf t ∷ A × Γ ⊢nf u ∷ A × Γ ⊢ B ≡ U l
  inversion-nf-Id-U = λ where
    (Idₙ ⊢A ⊢t ⊢u) →
      _ , ⊢A , ⊢t , ⊢u , refl (syntacticTerm (⊢nf∷→⊢∷ ⊢A))
    (convₙ ⊢Id C≡B) →
      case inversion-nf-Id-U ⊢Id of λ {
        (_ , ⊢A , ⊢t , ⊢u , C≡U) →
      _ , ⊢A , ⊢t , ⊢u , trans (sym C≡B) C≡U }
    (neₙ _ ⊢Id) →
      case ⊢neˡ∷→NfNeutralˡ ⊢Id of λ { (ne ()) }

opaque

  -- Inversion for identity types.

  inversion-nf-Id :
    Γ ⊢nf Id A t u →
    (Γ ⊢nf A) × Γ ⊢nf t ∷ A × Γ ⊢nf u ∷ A
  inversion-nf-Id = λ where
    (Idₙ ⊢A ⊢t ⊢u) → ⊢A , ⊢t , ⊢u
    (univₙ ⊢Id)    → case inversion-nf-Id-U ⊢Id of λ where
      (_ , ⊢A , ⊢t , ⊢u , _) → univₙ ⊢A , ⊢t , ⊢u

-- Inversion for J.

opaque

  inversion-ne-J :
    Γ ⊢ne J p q A t B u v w ∷ C →
    (Γ ⊢nf A) ×
    Γ ⊢nf t ∷ A ×
    (Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢nf B) ×
    Γ ⊢nf u ∷ B [ t , rfl ]₁₀ ×
    Γ ⊢nf v ∷ A ×
    Γ ⊢ne w ∷ Id A t v ×
    Γ ⊢ C ≡ B [ v , w ]₁₀
  inversion-ne-J = λ where
    ⊢J@(Jₙ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) →
      ⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , refl (syntacticTerm (⊢ne∷→⊢∷ ⊢J))
    (convₙ ⊢J D≡C) →
      case inversion-ne-J ⊢J of λ {
        (⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , D≡B) →
      ⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , trans (sym D≡C) D≡B }

opaque

  inversion-nf-J :
    Γ ⊢nf J p q A t B u v w ∷ C →
    (Γ ⊢nf A) ×
    Γ ⊢nf t ∷ A ×
    (Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢nf B) ×
    Γ ⊢nf u ∷ B [ t , rfl ]₁₀ ×
    Γ ⊢nf v ∷ A ×
    Γ ⊢ne w ∷ Id A t v ×
    Γ ⊢ C ≡ B [ v , w ]₁₀
  inversion-nf-J = λ where
    (neₙ _ (neₙ ⊢J)) →
      inversion-ne-J ⊢J
    (convₙ ⊢J C≡D) →
      case inversion-nf-J ⊢J of λ {
        (⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , C≡B) →
      ⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w , trans (sym C≡D) C≡B }

opaque

  inversion-nf-ne-J :
    Γ ⊢nf J p q A t B u v w ∷ C ⊎ Γ ⊢ne J p q A t B u v w ∷ C →
    (Γ ⊢nf A) ×
    Γ ⊢nf t ∷ A ×
    (Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢nf B) ×
    Γ ⊢nf u ∷ B [ t , rfl ]₁₀ ×
    Γ ⊢nf v ∷ A ×
    Γ ⊢ne w ∷ Id A t v ×
    Γ ⊢ C ≡ B [ v , w ]₁₀
  inversion-nf-ne-J = λ where
    (inj₁ ⊢J) → inversion-nf-J ⊢J
    (inj₂ ⊢J) → inversion-ne-J ⊢J

-- Inversion for K.

opaque

  inversion-ne-K :
    Γ ⊢ne K p A t B u v ∷ C →
    (Γ ⊢nf A) ×
    Γ ⊢nf t ∷ A ×
    (Γ ∙ Id A t t ⊢nf B) ×
    Γ ⊢nf u ∷ B [ rfl ]₀ ×
    Γ ⊢ne v ∷ Id A t t ×
    K-allowed ×
    Γ ⊢ C ≡ B [ v ]₀
  inversion-ne-K = λ where
    ⊢K@(Kₙ ⊢A ⊢t ⊢B ⊢u ⊢v ok) →
      ⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ok , refl (syntacticTerm (⊢ne∷→⊢∷ ⊢K))
    (convₙ ⊢K D≡C) →
      case inversion-ne-K ⊢K of λ {
        (⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ok , D≡B) →
      ⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ok , trans (sym D≡C) D≡B }

opaque

  inversion-nf-K :
    Γ ⊢nf K p A t B u v ∷ C →
    (Γ ⊢nf A) ×
    Γ ⊢nf t ∷ A ×
    (Γ ∙ Id A t t ⊢nf B) ×
    Γ ⊢nf u ∷ B [ rfl ]₀ ×
    Γ ⊢ne v ∷ Id A t t ×
    K-allowed ×
    Γ ⊢ C ≡ B [ v ]₀
  inversion-nf-K = λ where
    (neₙ _ (neₙ ⊢K)) →
      inversion-ne-K ⊢K
    (convₙ ⊢K C≡D) →
      case inversion-nf-K ⊢K of λ {
        (⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ok , C≡B) →
      ⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ok , trans (sym C≡D) C≡B }

opaque

  inversion-nf-ne-K :
    Γ ⊢nf K p A t B u v ∷ C ⊎ Γ ⊢ne K p A t B u v ∷ C →
    (Γ ⊢nf A) ×
    Γ ⊢nf t ∷ A ×
    (Γ ∙ Id A t t ⊢nf B) ×
    Γ ⊢nf u ∷ B [ rfl ]₀ ×
    Γ ⊢ne v ∷ Id A t t ×
    K-allowed ×
    Γ ⊢ C ≡ B [ v ]₀
  inversion-nf-ne-K = λ where
    (inj₁ ⊢K) → inversion-nf-K ⊢K
    (inj₂ ⊢K) → inversion-ne-K ⊢K

-- Inversion for []-cong.

opaque

  inversion-ne-[]-cong :
    Γ ⊢ne []-cong s l A t u v ∷ B →
    let open Erased s in
    Γ ⊢nf l ∷ Level ×
    Γ ⊢nf A ∷ U l ×
    Γ ⊢nf t ∷ A ×
    Γ ⊢nf u ∷ A ×
    Γ ⊢ne v ∷ Id A t u ×
    []-cong-allowed s ×
    Γ ⊢ B ≡ Id (Erased l A) [ t ] ([ u ])
  inversion-ne-[]-cong = λ where
    ⊢[]-cong@([]-congₙ ⊢l ⊢A ⊢t ⊢u ⊢v ok) →
      ⊢l , ⊢A , ⊢t , ⊢u , ⊢v , ok ,
      refl (syntacticTerm (⊢ne∷→⊢∷ ⊢[]-cong))
    (convₙ ⊢[]-cong C≡B) →
      let ⊢l , ⊢A , ⊢t , ⊢u , ⊢v , ok , C≡Id =
            inversion-ne-[]-cong ⊢[]-cong
      in
      ⊢l , ⊢A , ⊢t , ⊢u , ⊢v , ok , trans (sym C≡B) C≡Id

opaque

  inversion-nf-[]-cong :
    Γ ⊢nf []-cong s l A t u v ∷ B →
    let open Erased s in
    Γ ⊢nf l ∷ Level ×
    Γ ⊢nf A ∷ U l ×
    Γ ⊢nf t ∷ A ×
    Γ ⊢nf u ∷ A ×
    Γ ⊢ne v ∷ Id A t u ×
    []-cong-allowed s ×
    Γ ⊢ B ≡ Id (Erased l A) [ t ] ([ u ])
  inversion-nf-[]-cong = λ where
    (neₙ _ (neₙ ⊢[]-cong)) →
      inversion-ne-[]-cong ⊢[]-cong
    (convₙ ⊢[]-cong C≡B) →
      let ⊢l , ⊢A , ⊢t , ⊢u , ⊢v , ok , C≡Id =
            inversion-nf-[]-cong ⊢[]-cong
      in
      ⊢l , ⊢A , ⊢t , ⊢u , ⊢v , ok , trans (sym C≡B) C≡Id

opaque

  inversion-nf-ne-[]-cong :
    Γ ⊢nf []-cong s l A t u v ∷ B ⊎ Γ ⊢ne []-cong s l A t u v ∷ B →
    let open Erased s in
    Γ ⊢nf l ∷ Level ×
    Γ ⊢nf A ∷ U l ×
    Γ ⊢nf t ∷ A ×
    Γ ⊢nf u ∷ A ×
    Γ ⊢ne v ∷ Id A t u ×
    []-cong-allowed s ×
    Γ ⊢ B ≡ Id (Erased l A) [ t ] ([ u ])
  inversion-nf-ne-[]-cong = λ where
    (inj₁ ⊢[]-cong) → inversion-nf-[]-cong ⊢[]-cong
    (inj₂ ⊢[]-cong) → inversion-ne-[]-cong ⊢[]-cong

-- Inversion for unitrec

opaque

  inversion-ne-unitrec :
    Γ ⊢ne unitrec p q A t u ∷ B →
    (Γ ∙ Unitʷ ⊢nf A) ×
    Γ ⊢ne t ∷ Unitʷ ×
    Γ ⊢nf u ∷ A [ starʷ ]₀ ×
    Γ ⊢ B ≡ A [ t ]₀ ×
    ¬ Unitʷ-η
  inversion-ne-unitrec (unitrecₙ ⊢A ⊢t ⊢u _ not-ok) =
    ⊢A , ⊢t , ⊢u , refl (substType (⊢nf→⊢ ⊢A) (⊢ne∷→⊢∷ ⊢t)) , not-ok
  inversion-ne-unitrec (convₙ ⊢ur B≡C) =
    case inversion-ne-unitrec ⊢ur of λ {
      (⊢A , ⊢t , ⊢u , B≡ , not-ok) →
    ⊢A , ⊢t , ⊢u , trans (sym B≡C) B≡ , not-ok }

opaque

  inversion-nf-unitrec :
    Γ ⊢nf unitrec p q A t u ∷ B →
    (Γ ∙ Unitʷ ⊢nf A) ×
    Γ ⊢ne t ∷ Unitʷ ×
    Γ ⊢nf u ∷ A [ starʷ ]₀ ×
    Γ ⊢ B ≡ A [ t ]₀ ×
    ¬ Unitʷ-η
  inversion-nf-unitrec (neₙ _ (neₙ ⊢ur)) = inversion-ne-unitrec ⊢ur
  inversion-nf-unitrec (convₙ ⊢ur B≡C) =
    case inversion-nf-unitrec ⊢ur of λ {
      (⊢A , ⊢t , ⊢u , B≡ , not-ok) →
    ⊢A , ⊢t , ⊢u , trans (sym B≡C) B≡ , not-ok }

opaque

  inversion-nf-ne-unitrec :
    Γ ⊢nf unitrec p q A t u ∷ B ⊎ Γ ⊢ne unitrec p q A t u ∷ B →
    (Γ ∙ Unitʷ ⊢nf A) ×
    Γ ⊢ne t ∷ Unitʷ ×
    Γ ⊢nf u ∷ A [ starʷ ]₀ ×
    Γ ⊢ B ≡ A [ t ]₀ ×
    ¬ Unitʷ-η
  inversion-nf-ne-unitrec (inj₁ ⊢ur) = inversion-nf-unitrec ⊢ur
  inversion-nf-ne-unitrec (inj₂ ⊢ur) = inversion-ne-unitrec ⊢ur


------------------------------------------------------------------------
-- Lemmas related to η-long normal forms for types with η-equality

-- Normal forms of type Π p , q ▷ A ▹ B are not neutral (given a
-- certain assumption).

⊢nf∷Π→Neutral→⊥ :
  ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
  Γ ⊢nf t ∷ Π p , q ▷ A ▹ B → Neutral t → ⊥
⊢nf∷Π→Neutral→⊥ {Γ} ⊢t =
  ⊢nf∷Π→Neutral→⊥′ ⊢t (refl (syntacticTerm (⊢nf∷→⊢∷ ⊢t)))
  where
  ⊢nf∷Π→Neutral→⊥′ :
    Γ ⊢nf t ∷ A → Γ ⊢ A ≡ Π p , q ▷ B ▹ C → Neutral t → ⊥
  ⊢nf∷Π→Neutral→⊥′ = λ where
    (convₙ ⊢t B≡A) A≡Σ t-ne →
      ⊢nf∷Π→Neutral→⊥′ ⊢t (trans B≡A A≡Σ) t-ne
    (neₙ A-no-η _) A≡Π _ →
      No-η-equality→≢Π A-no-η A≡Π
    (Levelₙ _ _)    _ ()
    (zeroᵘₙ _)      _ ()
    (sucᵘₙ _)       _ ()
    (Uₙ _)          _ ()
    (Liftₙ _ _)     _ ()
    (liftₙ _ _)     _ ()
    (ΠΣₙ _ _ _)     _ ()
    (lamₙ _ _)      _ ()
    (prodₙ _ _ _ _) _ ()
    (Emptyₙ _)      _ ()
    (Unitₙ _ _)     _ ()
    (starₙ _ _)     _ ()
    (ℕₙ _)          _ ()
    (zeroₙ _)       _ ()
    (sucₙ _)        _ ()
    (Idₙ _ _ _)     _ ()
    (rflₙ _)        _ ()

-- Normal forms of type Σˢ p , q ▷ A ▹ B are not neutral (given a
-- certain assumption).

⊢nf∷Σˢ→Neutral→⊥ :
  ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
  Γ ⊢nf t ∷ Σˢ p , q ▷ A ▹ B → Neutral t → ⊥
⊢nf∷Σˢ→Neutral→⊥ {Γ} ⊢t =
  ⊢nf∷Σˢ→Neutral→⊥′ ⊢t (refl (syntacticTerm (⊢nf∷→⊢∷ ⊢t)))
  where
  ⊢nf∷Σˢ→Neutral→⊥′ :
    Γ ⊢nf t ∷ A → Γ ⊢ A ≡ Σˢ p , q ▷ B ▹ C → Neutral t → ⊥
  ⊢nf∷Σˢ→Neutral→⊥′ = λ where
    (convₙ ⊢t B≡A) A≡Σ t-ne →
      ⊢nf∷Σˢ→Neutral→⊥′ ⊢t (trans B≡A A≡Σ) t-ne
    (neₙ A-no-η _) A≡Σ _ →
      No-η-equality→≢Σˢ A-no-η A≡Σ
    (Levelₙ _ _)    _ ()
    (zeroᵘₙ _)      _ ()
    (sucᵘₙ _)       _ ()
    (Uₙ _)          _ ()
    (Liftₙ _ _)     _ ()
    (liftₙ _ _)     _ ()
    (ΠΣₙ _ _ _)     _ ()
    (lamₙ _ _)      _ ()
    (prodₙ _ _ _ _) _ ()
    (Emptyₙ _)      _ ()
    (Unitₙ _ _)     _ ()
    (starₙ _ _)     _ ()
    (ℕₙ _)          _ ()
    (zeroₙ _)       _ ()
    (sucₙ _)        _ ()
    (Idₙ _ _ _)     _ ()
    (rflₙ _)        _ ()

-- Normal forms of type Unit s l are equal to star s l if Unit s l
-- comes with η-equality (given a certain assumption).

⊢nf∷Unitˢ→≡starˢ :
  ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
  Unit-with-η s → Γ ⊢nf t ∷ Unit s → t PE.≡ star s
⊢nf∷Unitˢ→≡starˢ {Γ} {s} ok ⊢t =
  ⊢nf∷Unitˢ→≡starˢ′ (refl (syntacticTerm (⊢nf∷→⊢∷ ⊢t))) ⊢t
  where
  ⊢nf∷Unitˢ→≡starˢ′ :
    Γ ⊢ A ≡ Unit s → Γ ⊢nf t ∷ A → t PE.≡ star s
  ⊢nf∷Unitˢ→≡starˢ′ A≡Unit = λ where
    (starₙ ⊢Γ ok)     →
      case Unit-injectivity A≡Unit of λ {
        PE.refl →
      PE.refl }
    (convₙ ⊢t ≡A)   → ⊢nf∷Unitˢ→≡starˢ′ (trans ≡A A≡Unit) ⊢t
    (neₙ A-no-η _)  → ⊥-elim (No-η-equality→≢Unit A-no-η A≡Unit ok)
    (Levelₙ _ _)    → ⊥-elim (U≢Unitⱼ A≡Unit)
    (zeroᵘₙ _)      → ⊥-elim (Level≢Unitⱼ A≡Unit)
    (sucᵘₙ _)       → ⊥-elim (Level≢Unitⱼ A≡Unit)
    (Uₙ _)          → ⊥-elim (U≢Unitⱼ A≡Unit)
    (Liftₙ _ _)     → ⊥-elim (U≢Unitⱼ A≡Unit)
    (liftₙ _ _)     → ⊥-elim (Lift≢Unitⱼ A≡Unit)
    (ΠΣₙ _ _ _)     → ⊥-elim (U≢Unitⱼ A≡Unit)
    (lamₙ _ _)      → ⊥-elim (Unit≢ΠΣⱼ (sym A≡Unit))
    (prodₙ _ _ _ _) → ⊥-elim (Unit≢ΠΣⱼ (sym A≡Unit))
    (Emptyₙ _)      → ⊥-elim (U≢Unitⱼ A≡Unit)
    (Unitₙ _ _)     → ⊥-elim (U≢Unitⱼ A≡Unit)
    (ℕₙ _)          → ⊥-elim (U≢Unitⱼ A≡Unit)
    (zeroₙ _)       → ⊥-elim (ℕ≢Unitⱼ A≡Unit)
    (sucₙ _)        → ⊥-elim (ℕ≢Unitⱼ A≡Unit)
    (Idₙ _ _ _)     → ⊥-elim (U≢Unitⱼ A≡Unit)
    (rflₙ _)        → ⊥-elim (Id≢Unit A≡Unit)

-- Normal forms of type Lift l A are equal to applications of lift
-- (given a certain assumption).

⊢nf∷Lift→≡lift :
  ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
  Γ ⊢nf t ∷ Lift l A → ∃ λ t′ → t PE.≡ lift t′
⊢nf∷Lift→≡lift {Γ} ⊢t =
  ⊢nf∷Lift→≡lift′ (refl (wf-⊢∷ (⊢nf∷→⊢∷ ⊢t))) ⊢t
  where
  ⊢nf∷Lift→≡lift′ :
    Γ ⊢ A ≡ Lift l B → Γ ⊢nf t ∷ A → ∃ λ t′ → t PE.≡ lift t′
  ⊢nf∷Lift→≡lift′ A≡Lift = λ where
    (liftₙ _ _)     → _ , PE.refl
    (convₙ ⊢t ≡A)   → ⊢nf∷Lift→≡lift′ (trans ≡A A≡Lift) ⊢t
    (neₙ A-no-η _)  → ⊥-elim (No-η-equality→≢Lift A-no-η A≡Lift)
    (Levelₙ _ _)    → ⊥-elim (U≢Liftⱼ A≡Lift)
    (zeroᵘₙ _)      → ⊥-elim (Lift≢Level (sym A≡Lift))
    (sucᵘₙ _)       → ⊥-elim (Lift≢Level (sym A≡Lift))
    (Uₙ _)          → ⊥-elim (U≢Liftⱼ A≡Lift)
    (Liftₙ _ _)     → ⊥-elim (U≢Liftⱼ A≡Lift)
    (ΠΣₙ _ _ _)     → ⊥-elim (U≢Liftⱼ A≡Lift)
    (lamₙ _ _)      → ⊥-elim (Lift≢ΠΣⱼ (sym A≡Lift))
    (prodₙ _ _ _ _) → ⊥-elim (Lift≢ΠΣⱼ (sym A≡Lift))
    (Emptyₙ _)      → ⊥-elim (U≢Liftⱼ A≡Lift)
    (Unitₙ _ _)     → ⊥-elim (U≢Liftⱼ A≡Lift)
    (starₙ _ _)     → ⊥-elim (Lift≢Unitⱼ (sym A≡Lift))
    (ℕₙ _)          → ⊥-elim (U≢Liftⱼ A≡Lift)
    (zeroₙ _)       → ⊥-elim (Lift≢ℕ (sym A≡Lift))
    (sucₙ _)        → ⊥-elim (Lift≢ℕ (sym A≡Lift))
    (Idₙ _ _ _)     → ⊥-elim (U≢Liftⱼ A≡Lift)
    (rflₙ _)        → ⊥-elim (I.Id≢Lift A≡Lift)
