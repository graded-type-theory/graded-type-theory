------------------------------------------------------------------------
-- A well-resourced term has a well-resourced η-long normal form
-- (given a certain assumption)
------------------------------------------------------------------------

open import Definition.Modality
import Definition.Mode

module Definition.Modality.FullReduction
  {a} {M : Set a} (𝕄 : Modality M)
  where

open Modality 𝕄

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Nullary
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (_⊎_; inj₂)
open import Tools.Unit

open import Definition.Untyped M as U hiding (_∷_)
open import Definition.Typed M
open import Definition.Typed.Properties M
open import Definition.Typed.Usage 𝕄
open import Definition.Typed.Weakening M
open import Definition.Typed.Consequences.DerivedRules M
open import Definition.Typed.Consequences.InverseUniv M
open import Definition.Typed.Consequences.Inversion M
open import Definition.Typed.Consequences.NeTypeEq M
open import Definition.Typed.Consequences.Substitution M
open import Definition.Typed.Consequences.Syntactic M

open import Definition.Conversion M
open import Definition.Conversion.Consequences.Completeness M
open import Definition.Conversion.FullReduction M
  using (NfNeutral; Nf)
open import Definition.Conversion.Soundness M
open import Definition.Conversion.Stability M
open import Definition.Conversion.Whnf M

open NfNeutral
open Nf

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Modality.Usage.Properties 𝕄
open import Definition.Modality.Usage.Weakening 𝕄

open import Definition.Mode 𝕄

private
  variable
    n : Nat
    x : Fin n
    Γ Δ : Con Term n
    A A′ B C t t′ u v : Term n
    p q q′ r : M
    γ : Conₘ n
    m : Mode
    b : BinderMode
    s : SigmaMode

------------------------------------------------------------------------
-- Definitions of η-long normal types and terms and some associated
-- concepts

-- No-η-equality A holds if A is a type without (top-level)
-- η-equality, or a neutral term.

data No-η-equality {n : Nat} : Term n → Set a where
  Uₙ     : No-η-equality U
  Σᵣₙ    : No-η-equality (Σᵣ p , q ▷ A ▹ B)
  Emptyₙ : No-η-equality Empty
  ℕₙ     : No-η-equality ℕ
  neₙ    : Neutral A → No-η-equality A

mutual

  -- Γ ⊢nf A holds if A is a type in η-long normal form (with respect
  -- to the context Γ).

  infix 4 _⊢nf_

  data _⊢nf_ (Γ : Con Term n) : Term n → Set a where
    Uₙ     : ⊢ Γ →
             Γ ⊢nf U
    univₙ  : Γ ⊢nf A ∷ U →
             Γ ⊢nf A
    ΠΣₙ    : Γ ⊢nf A →
             Γ ∙ A ⊢nf B →
             Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
    Emptyₙ : ⊢ Γ →
             Γ ⊢nf Empty
    Unitₙ  : ⊢ Γ →
             Γ ⊢nf Unit
    ℕₙ     : ⊢ Γ →
             Γ ⊢nf ℕ

  -- Γ ⊢nf t ∷ A holds if t is a term in η-long normal form (with
  -- respect to the context Γ and the type A).

  infix 4 _⊢nf_∷_

  data _⊢nf_∷_ (Γ : Con Term n) : Term n → Term n → Set a where
    convₙ  : Γ ⊢nf t ∷ A →
             Γ ⊢ A ≡ B →
             Γ ⊢nf t ∷ B
    ΠΣₙ    : Γ ⊢nf A ∷ U →
             Γ ∙ A ⊢nf B ∷ U →
             Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U
    lamₙ   : Γ ⊢ A →
             Γ ∙ A ⊢nf t ∷ B →
             Γ ⊢nf lam p t ∷ Π p , q ▷ A ▹ B
    prodₙ  : Γ ⊢ A →
             Γ ∙ A ⊢ B →
             Γ ⊢nf t ∷ A →
             Γ ⊢nf u ∷ B [ t ] →
             Γ ⊢nf prod s p t u ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
    Emptyₙ : ⊢ Γ →
             Γ ⊢nf Empty ∷ U
    Unitₙ  : ⊢ Γ →
             Γ ⊢nf Unit ∷ U
    starₙ  : ⊢ Γ →
             Γ ⊢nf star ∷ Unit
    ℕₙ     : ⊢ Γ →
             Γ ⊢nf ℕ ∷ U
    zeroₙ  : ⊢ Γ →
             Γ ⊢nf zero ∷ ℕ
    sucₙ   : Γ ⊢nf t ∷ ℕ →
             Γ ⊢nf suc t ∷ ℕ
    neₙ    : No-η-equality A →
             Γ ⊢ne t ∷ A →
             Γ ⊢nf t ∷ A

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
    ∘ₙ        : Γ ⊢ne t ∷ Π p , q ▷ A ▹ B →
                Γ ⊢nf u ∷ A →
                Γ ⊢ne t ∘⟨ p ⟩ u ∷ B [ u ]
    fstₙ      : Γ ⊢ A →
                Γ ∙ A ⊢ B →
                Γ ⊢ne t ∷ Σₚ p , q ▷ A ▹ B →
                Γ ⊢ne fst p t ∷ A
    sndₙ      : Γ ⊢ A →
                Γ ∙ A ⊢ B →
                Γ ⊢ne t ∷ Σₚ p , q ▷ A ▹ B →
                Γ ⊢ne snd p t ∷ B [ fst p t ]
    prodrecₙ  : Γ ⊢ A →
                Γ ∙ A ⊢ B →
                Γ ∙ (Σᵣ p , q′ ▷ A ▹ B) ⊢nf C →
                Γ ⊢ne t ∷ Σᵣ p , q′ ▷ A ▹ B →
                Γ ∙ A ∙ B ⊢nf u ∷
                  C [ prodᵣ p (var (x0 +1)) (var x0) ]↑² →
                Γ ⊢ne prodrec r p q C t u ∷ C [ t ]
    Emptyrecₙ : Γ ⊢nf A →
                Γ ⊢ne t ∷ Empty →
                Γ ⊢ne Emptyrec p A t ∷ A
    natrecₙ   : Γ ∙ ℕ ⊢nf A →
                Γ ⊢nf t ∷ A [ zero ] →
                Γ ∙ ℕ ∙ A ⊢nf u ∷ wk1 (A [ suc (var x0) ]↑) →
                Γ ⊢ne v ∷ ℕ →
                Γ ⊢ne natrec p q r A t u v ∷ A [ v ]

------------------------------------------------------------------------
-- A lemma

-- If A is a normal type of type U, then A is a normal term of type U.

⊢nf∷U→⊢nf∷U : Γ ⊢nf A → Γ ⊢ A ∷ U → Γ ⊢nf A ∷ U
⊢nf∷U→⊢nf∷U = λ where
  (Uₙ _)      ⊢U∷U    → ⊥-elim (inversion-U ⊢U∷U)
  (univₙ ⊢A)  _       → ⊢A
  (ΠΣₙ ⊢A ⊢B) ⊢ΠΣAB∷U →
    case inversion-ΠΣ-U ⊢ΠΣAB∷U of λ {
      (⊢A∷U , ⊢B∷U , _) →
    ΠΣₙ (⊢nf∷U→⊢nf∷U ⊢A ⊢A∷U) (⊢nf∷U→⊢nf∷U ⊢B ⊢B∷U) }
  (Emptyₙ ⊢Γ) _ → Emptyₙ ⊢Γ
  (Unitₙ ⊢Γ)  _ → Unitₙ ⊢Γ
  (ℕₙ ⊢Γ)     _ → ℕₙ ⊢Γ

------------------------------------------------------------------------
-- Some conversion functions

mutual

  -- If A is an η-long normal type, then A is well-typed.

  ⊢nf→⊢ : Γ ⊢nf A → Γ ⊢ A
  ⊢nf→⊢ = λ where
    (Uₙ ⊢Γ)     → Uⱼ ⊢Γ
    (univₙ ⊢A)  → univ (⊢nf∷→⊢∷ ⊢A)
    (ΠΣₙ ⊢A ⊢B) → ΠΣⱼ ⊢nf→⊢ ⊢A ▹ ⊢nf→⊢ ⊢B
    (Emptyₙ ⊢Γ) → Emptyⱼ ⊢Γ
    (Unitₙ ⊢Γ)  → Unitⱼ ⊢Γ
    (ℕₙ ⊢Γ)     → ℕⱼ ⊢Γ

  -- If t is an η-long normal term, then t is well-typed.

  ⊢nf∷→⊢∷ : Γ ⊢nf t ∷ A → Γ ⊢ t ∷ A
  ⊢nf∷→⊢∷ = λ where
    (convₙ ⊢t A≡B)      → conv (⊢nf∷→⊢∷ ⊢t) A≡B
    (ΠΣₙ ⊢A ⊢B)         → ΠΣⱼ ⊢nf∷→⊢∷ ⊢A ▹ ⊢nf∷→⊢∷ ⊢B
    (lamₙ ⊢A ⊢t)        → lamⱼ ⊢A (⊢nf∷→⊢∷ ⊢t)
    (prodₙ ⊢A ⊢B ⊢t ⊢u) → prodⱼ ⊢A ⊢B (⊢nf∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢u)
    (Emptyₙ ⊢Γ)         → Emptyⱼ ⊢Γ
    (Unitₙ ⊢Γ)          → Unitⱼ ⊢Γ
    (starₙ ⊢Γ)          → starⱼ ⊢Γ
    (ℕₙ ⊢Γ)             → ℕⱼ ⊢Γ
    (zeroₙ ⊢Γ)          → zeroⱼ ⊢Γ
    (sucₙ ⊢t)           → sucⱼ (⊢nf∷→⊢∷ ⊢t)
    (neₙ _ ⊢t)          → ⊢ne∷→⊢∷ ⊢t

  -- If Γ ⊢ne t ∷ A holds, then t is well-typed.

  ⊢ne∷→⊢∷ : Γ ⊢ne t ∷ A → Γ ⊢ t ∷ A
  ⊢ne∷→⊢∷ = λ where
    (convₙ ⊢t A≡B)            → conv (⊢ne∷→⊢∷ ⊢t) A≡B
    (varₙ ⊢Γ x∈)              → var ⊢Γ x∈
    (∘ₙ ⊢t ⊢u)                → ⊢ne∷→⊢∷ ⊢t ∘ⱼ ⊢nf∷→⊢∷ ⊢u
    (fstₙ ⊢A ⊢B ⊢t)           → fstⱼ ⊢A ⊢B (⊢ne∷→⊢∷ ⊢t)
    (sndₙ ⊢A ⊢B ⊢t)           → sndⱼ ⊢A ⊢B (⊢ne∷→⊢∷ ⊢t)
    (prodrecₙ ⊢A ⊢B ⊢C ⊢t ⊢u) → prodrecⱼ ⊢A ⊢B (⊢nf→⊢ ⊢C) (⊢ne∷→⊢∷ ⊢t)
                                 (⊢nf∷→⊢∷ ⊢u)
    (Emptyrecₙ ⊢A ⊢t)         → Emptyrecⱼ (⊢nf→⊢ ⊢A) (⊢ne∷→⊢∷ ⊢t)
    (natrecₙ ⊢A ⊢t ⊢u ⊢v)     → natrecⱼ (⊢nf→⊢ ⊢A) (⊢nf∷→⊢∷ ⊢t)
                                 (⊢nf∷→⊢∷ ⊢u) (⊢ne∷→⊢∷ ⊢v)

mutual

  -- If A is an η-long normal type, then A is normal.

  ⊢nf→Nf : Γ ⊢nf A → Nf A
  ⊢nf→Nf = λ where
    (Uₙ _)      → Uₙ
    (univₙ ⊢A)  → ⊢nf∷→Nf ⊢A
    (ΠΣₙ ⊢A ⊢B) → ΠΣₙ (⊢nf→Nf ⊢A) (⊢nf→Nf ⊢B)
    (Emptyₙ _)  → Emptyₙ
    (Unitₙ _)   → Unitₙ
    (ℕₙ _)      → ℕₙ

  -- If t is an η-long normal term, then t is normal.

  ⊢nf∷→Nf : Γ ⊢nf t ∷ A → Nf t
  ⊢nf∷→Nf = λ where
    (convₙ ⊢t _)      → ⊢nf∷→Nf ⊢t
    (ΠΣₙ ⊢A ⊢B)       → ΠΣₙ (⊢nf∷→Nf ⊢A) (⊢nf∷→Nf ⊢B)
    (lamₙ _ ⊢t)       → lamₙ (⊢nf∷→Nf ⊢t)
    (prodₙ _ _ ⊢t ⊢u) → prodₙ (⊢nf∷→Nf ⊢t) (⊢nf∷→Nf ⊢u)
    (Emptyₙ _)        → Emptyₙ
    (Unitₙ _)         → Unitₙ
    (starₙ _)         → starₙ
    (ℕₙ _)            → ℕₙ
    (zeroₙ _)         → zeroₙ
    (sucₙ ⊢t)         → sucₙ (⊢nf∷→Nf ⊢t)
    (neₙ _ ⊢t)        → ne (⊢ne∷→NfNeutral ⊢t)

  -- If Γ ⊢ne t ∷ A holds, then t is "NfNeutral".

  ⊢ne∷→NfNeutral : Γ ⊢ne t ∷ A → NfNeutral t
  ⊢ne∷→NfNeutral = λ where
    (convₙ ⊢t _)            → ⊢ne∷→NfNeutral ⊢t
    (varₙ _ _)              → var _
    (∘ₙ ⊢t ⊢u)              → ∘ₙ (⊢ne∷→NfNeutral ⊢t) (⊢nf∷→Nf ⊢u)
    (fstₙ _ _ ⊢t)           → fstₙ (⊢ne∷→NfNeutral ⊢t)
    (sndₙ _ _ ⊢t)           → sndₙ (⊢ne∷→NfNeutral ⊢t)
    (prodrecₙ _ _ ⊢C ⊢t ⊢u) → prodrecₙ (⊢nf→Nf ⊢C) (⊢ne∷→NfNeutral ⊢t)
                                (⊢nf∷→Nf ⊢u)
    (Emptyrecₙ ⊢A ⊢t)       → Emptyrecₙ (⊢nf→Nf ⊢A) (⊢ne∷→NfNeutral ⊢t)
    (natrecₙ ⊢A ⊢t ⊢u ⊢v)   → natrecₙ (⊢nf→Nf ⊢A) (⊢nf∷→Nf ⊢t)
                                (⊢nf∷→Nf ⊢u) (⊢ne∷→NfNeutral ⊢v)

------------------------------------------------------------------------
-- Stability

mutual

  -- If A is a normal type with respect to the context Γ, and Γ is
  -- judgmentally equal to Δ, then A is also a normal type with
  -- respect to Δ.

  ⊢nf-stable : ⊢ Γ ≡ Δ → Γ ⊢nf A → Δ ⊢nf A
  ⊢nf-stable Γ≡Δ = λ where
      (Uₙ ⊢Γ)     → Uₙ ⊢Δ
      (univₙ ⊢A)  → univₙ (⊢nf∷-stable Γ≡Δ ⊢A)
      (ΠΣₙ ⊢A ⊢B) → ΠΣₙ (⊢nf-stable Γ≡Δ ⊢A)
                      (⊢nf-stable (Γ≡Δ ∙ refl (⊢nf→⊢ ⊢A)) ⊢B)
      (Emptyₙ ⊢Γ) → Emptyₙ ⊢Δ
      (Unitₙ ⊢Γ)  → Unitₙ ⊢Δ
      (ℕₙ ⊢Γ)     → ℕₙ ⊢Δ
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
      (ΠΣₙ ⊢A ⊢B) → ΠΣₙ
        (⊢nf∷-stable Γ≡Δ ⊢A)
        (⊢nf∷-stable (Γ≡Δ ∙ refl (⊢nf→⊢ (univₙ ⊢A))) ⊢B)
      (lamₙ ⊢A ⊢t) → lamₙ
        (stability Γ≡Δ ⊢A)
        (⊢nf∷-stable (Γ≡Δ ∙ refl ⊢A) ⊢t)
      (prodₙ ⊢A ⊢B ⊢t ⊢u) → prodₙ
        (stability Γ≡Δ ⊢A)
        (stability (Γ≡Δ ∙ refl ⊢A) ⊢B)
        (⊢nf∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable Γ≡Δ ⊢u)
      (Emptyₙ ⊢Γ) → Emptyₙ ⊢Δ
      (Unitₙ ⊢Γ)  → Unitₙ ⊢Δ
      (starₙ ⊢Γ)  → starₙ ⊢Δ
      (ℕₙ ⊢Γ)     → ℕₙ ⊢Δ
      (zeroₙ ⊢Γ)  → zeroₙ ⊢Δ
      (sucₙ ⊢t)   → sucₙ
        (⊢nf∷-stable Γ≡Δ ⊢t)
      (neₙ ok ⊢t) → neₙ
        ok
        (⊢ne∷-stable Γ≡Δ ⊢t)
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
      (∘ₙ ⊢t ⊢u) → ∘ₙ
        (⊢ne∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable Γ≡Δ ⊢u)
      (fstₙ ⊢A ⊢B ⊢t) → fstₙ
        (stability Γ≡Δ ⊢A)
        (stability (Γ≡Δ ∙ refl ⊢A) ⊢B)
        (⊢ne∷-stable Γ≡Δ ⊢t)
      (sndₙ ⊢A ⊢B ⊢t) → sndₙ
        (stability Γ≡Δ ⊢A)
        (stability (Γ≡Δ ∙ refl ⊢A) ⊢B)
        (⊢ne∷-stable Γ≡Δ ⊢t)
      (prodrecₙ ⊢A ⊢B ⊢C ⊢t ⊢u) → prodrecₙ
        (stability Γ≡Δ ⊢A)
        (stability (Γ≡Δ ∙ refl ⊢A) ⊢B)
        (⊢nf-stable (Γ≡Δ ∙ refl (ΠΣⱼ ⊢A ▹ ⊢B)) ⊢C)
        (⊢ne∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable (Γ≡Δ ∙ refl ⊢A ∙ refl ⊢B) ⊢u)
      (Emptyrecₙ ⊢A ⊢t) → Emptyrecₙ
        (⊢nf-stable Γ≡Δ ⊢A)
        (⊢ne∷-stable Γ≡Δ ⊢t)
      (natrecₙ ⊢A ⊢t ⊢u ⊢v) →
        case Γ≡Δ ∙ refl (ℕⱼ (wfTerm (⊢nf∷→⊢∷ ⊢t))) of λ {
          ⊢Γℕ≡Δℕ → natrecₙ
        (⊢nf-stable ⊢Γℕ≡Δℕ ⊢A)
        (⊢nf∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable (⊢Γℕ≡Δℕ ∙ refl (⊢nf→⊢ ⊢A)) ⊢u)
        (⊢ne∷-stable Γ≡Δ ⊢v) }
    where
    ⊢Δ = contextConvSubst Γ≡Δ .proj₂ .proj₁

------------------------------------------------------------------------
-- Predicates used to state the full reduction lemmas and theorems

mutual

  -- The full reduction lemmas hold for derivations that satisfy the
  -- following predicates (if the mode is 𝟙ᵐ).
  --
  -- The three main cases below impose certain requirements:
  -- * If unit types (with η-equality) are used (in a certain way),
  --   then 𝟘 must be the largest quantity.
  -- * If a Σ-type with η-equality and the "first component
  --   quantity" p is used (in a certain way), then p ·_ must be
  --   increasing, and if ⌞ p ⌟ is 𝟙ᵐ, then p ≤ 𝟙 must hold.

  OK-⊢[conv↓]∷ : Γ ⊢ t [conv↓] u ∷ A → Set a
  OK-⊢[conv↓]∷ = λ where

    -- The following three cases are the main ones.

    (Unit-ins _) →
      (p : M) → p ≤ 𝟘
    (η-unit _ _ _ _) →
      (p : M) → p ≤ 𝟘
    (Σ-η {p = p} _ _ _ _ fst-t↑ snd-t↑) →
      (⌞ p ⌟ PE.≡ 𝟙ᵐ → OK-⊢[conv↑]∷ fst-t↑) ×
      OK-⊢[conv↑]∷ snd-t↑ ×
      (⌞ p ⌟ PE.≡ 𝟙ᵐ → p ≤ 𝟙) ×
      ((q : M) → q ≤ p · q)

    (ℕ-ins t~) →
      OK-⊢~↓ t~
    (Empty-ins t~) →
      OK-⊢~↓ t~
    (Σᵣ-ins _ _ t~) →
      OK-⊢~↓ t~
    (ne-ins _ _ _ t~) →
      OK-⊢~↓ t~
    (univ _ _ A↓) →
      OK-⊢[conv↓] A↓
    (zero-refl _) →
      Lift _ ⊤
    (suc-cong t↑) →
      OK-⊢[conv↑]∷ t↑
    (prod-cong {p = p} _ _ t↑ u↑) →
      (⌞ p ⌟ PE.≡ 𝟙ᵐ → OK-⊢[conv↑]∷ t↑) ×
      OK-⊢[conv↑]∷ u↑
    (η-eq _ _ _ _ t0≡u0) →
      OK-⊢[conv↑]∷ t0≡u0

  OK-⊢[conv↑]∷ : Γ ⊢ t [conv↑] u ∷ A → Set a
  OK-⊢[conv↑]∷ ([↑]ₜ _ _ _ _ _ _ _ _ _ t′↓) =
    OK-⊢[conv↓]∷ t′↓

  OK-⊢[conv↓] : Γ ⊢ A [conv↓] B → Set a
  OK-⊢[conv↓] = λ where
    (ne A~) →
      OK-⊢~↓ A~
    (ΠΣ-cong {p = p} _ A↑ B↑) →
      (⌞ p ⌟ PE.≡ 𝟙ᵐ → OK-⊢[conv↑] A↑) ×
      OK-⊢[conv↑] B↑
    _ →
      Lift _ ⊤

  OK-⊢[conv↑] : Γ ⊢ A [conv↑] B → Set a
  OK-⊢[conv↑] ([↑] _ _ _ _ _ _ A′↓) =
    OK-⊢[conv↓] A′↓

  OK-⊢~↓ : Γ ⊢ t ~ u ↓ A → Set a
  OK-⊢~↓ ([~] _ _ _ t~) =
    OK-⊢~↑ t~

  OK-⊢~↑ : Γ ⊢ t ~ t′ ↑ A → Set a
  OK-⊢~↑ = λ where
    (var-refl _ _) →
      Lift _ ⊤
    (app-cong {p = p} t~ u↑) →
      OK-⊢~↓ t~ ×
      (⌞ p ⌟ PE.≡ 𝟙ᵐ → OK-⊢[conv↑]∷ u↑)
    (fst-cong t~) →
      OK-⊢~↓ t~
    (snd-cong t~) →
      OK-⊢~↓ t~
    (natrec-cong A↑ t↑ u↑ v~) →
      (¬ T 𝟘ᵐ-allowed → OK-⊢[conv↑] A↑) ×
      OK-⊢[conv↑]∷ t↑ ×
      OK-⊢[conv↑]∷ u↑ ×
      OK-⊢~↓ v~
    (prodrec-cong {r = r} C↑ u~ v↑) →
      (¬ T 𝟘ᵐ-allowed → OK-⊢[conv↑] C↑) ×
      (⌞ r ⌟ PE.≡ 𝟙ᵐ → OK-⊢~↓ u~) ×
      OK-⊢[conv↑]∷ v↑
    (Emptyrec-cong {p = p} A↑ t~) →
      (¬ T 𝟘ᵐ-allowed → OK-⊢[conv↑] A↑) ×
      (⌞ p ⌟ PE.≡ 𝟙ᵐ → OK-⊢~↓ t~)

private

  -- Some lemmas used to propagate the "OK" predicate information.

  ᵐ·≡𝟙ᵐ→ :
    {A : Set a} →
    (m PE.≡ 𝟙ᵐ → ⌞ p ⌟ PE.≡ 𝟙ᵐ → A) →
    m ᵐ· p PE.≡ 𝟙ᵐ → A
  ᵐ·≡𝟙ᵐ→ {m = 𝟙ᵐ} = _$ PE.refl

  𝟘ᵐ?≡𝟙ᵐ→ :
    {A : Set a} →
    (m PE.≡ 𝟙ᵐ → ¬ T 𝟘ᵐ-allowed → A) →
    𝟘ᵐ? PE.≡ 𝟙ᵐ → A
  𝟘ᵐ?≡𝟙ᵐ→ {A = A} hyp = 𝟘ᵐ?-elim
    (λ m → m PE.≡ 𝟙ᵐ → A)
    (λ ())
    (λ not-ok _ → hyp (only-𝟙ᵐ-without-𝟘ᵐ not-ok) not-ok)

------------------------------------------------------------------------
-- The full reduction lemmas

private

  -- A lemma used in the Unit-ins and η-unit cases of
  -- fullRedTermConv↓.

  ▸→≤ᶜ𝟘ᶜ :
    ∀ {t : Term n} m →
    (m PE.≡ 𝟙ᵐ → (p : M) → p ≤ 𝟘) →
    γ ▸[ m ] t → γ ≤ᶜ 𝟘ᶜ
  ▸→≤ᶜ𝟘ᶜ 𝟘ᵐ _  γ▸t = ▸-𝟘ᵐ γ▸t
  ▸→≤ᶜ𝟘ᶜ 𝟙ᵐ ≤𝟘 _   = ≤ᶜ𝟘ᶜ (≤𝟘 PE.refl _)

  -- A lemma used in the Σ-η case of fullRedTermConv↓.

  Σ-η-lemma :
    ∀ m →
    (m PE.≡ 𝟙ᵐ →
     (⌞ p ⌟ PE.≡ 𝟙ᵐ → p ≤ 𝟙) ×
     ((q : M) → q ≤ p · q)) →
    γ ▸[ m ] t →
    ∃ λ δ → δ ▸[ m ᵐ· p ] fst p t × γ ≤ᶜ p ·ᶜ δ
  Σ-η-lemma {p = p} {γ = γ} = λ where
    𝟘ᵐ[ ok ] _ ▸t →
        𝟘ᶜ
      , fstₘ 𝟘ᵐ[ ok ] (▸-𝟘 ▸t) PE.refl (λ ())
      , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           γ        ≤⟨ ▸-𝟘ᵐ ▸t ⟩
           𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
           p ·ᶜ 𝟘ᶜ  ∎)
    𝟙ᵐ ok ▸t →
      case ok PE.refl of λ {
        (p≤𝟙 , p·-increasing) →
        ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ
      , fstₘ 𝟙ᵐ
          (▸-cong
             (let open Tools.Reasoning.PropositionalEquality in
                ⌞ p ⌟ ·ᵐ 𝟙ᵐ  ≡⟨ ·ᵐ-identityʳ _ ⟩
                ⌞ p ⌟        ∎)
             (▸-· ▸t))
          PE.refl
          p≤𝟙
      , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           γ                     ≤⟨ ·ᶜ-increasing (p·-increasing _) ⟩
           p ·ᶜ γ                ≈˘⟨ ·ᶜ-congʳ ·⌜⌞⌟⌝ ⟩
           (p · ⌜ ⌞ p ⌟ ⌝) ·ᶜ γ  ≈⟨ ·ᶜ-assoc _ _ _ ⟩
           p ·ᶜ ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ   ∎) }

mutual

  -- The full reduction lemmas, used to prove the main theorems below.

  fullRedNe :
    (t~ : Γ ⊢ t ~ t′ ↑ A) → γ ▸[ m ] t →
    (m PE.≡ 𝟙ᵐ → OK-⊢~↑ t~) →
    ∃ λ u → Γ ⊢ne u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
  fullRedNe {Γ = Γ} = λ where
    (var-refl {x = x} ⊢x _) ▸x _ →
      case inversion-var ⊢x of λ {
        (_ , x∈ , A≡B) →
        var x
      , convₙ (varₙ (wfEq A≡B) x∈) (sym A≡B)
      , refl ⊢x
      , ▸x }
    (app-cong {G = B} {t = u} t~ u↑) ▸tu ok →
      case inv-usage-app ▸tu of λ {
        (invUsageApp ▸t ▸u γ≤) →
      case fullRedNe~↓ t~ ▸t (proj₁ ∘→ ok) of λ {
        (t′ , t′-ne , t≡t′ , ▸t′) →
      case fullRedTermConv↑ u↑ ▸u (ᵐ·≡𝟙ᵐ→ (proj₂ ∘→ ok)) of λ {
        (u′ , u′-nf , u≡u′ , ▸u′) →
      case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) .proj₂ of λ {
        ⊢B →
        t′ ∘ u′
      , (                          $⟨ ∘ₙ t′-ne u′-nf ⟩
         Γ ⊢ne t′ ∘ u′ ∷ B [ u′ ]  →⟨ flip convₙ $
                                      substTypeEq (refl ⊢B) (sym u≡u′) ⟩
         Γ ⊢ne t′ ∘ u′ ∷ B [ u ]   □)
      , app-cong t≡t′ u≡u′
      , sub (▸t′ ∘ₘ ▸u′) γ≤ }}}}
    (fst-cong {p = p} t~) ▸fst-t ok →
      case inv-usage-fst ▸fst-t of λ {
        (invUsageFst m′ PE.refl ▸t γ≤ fst-ok) →
      case fullRedNe~↓ t~ ▸t ok of λ {
        (t′ , t′-ne , t≡t′ , ▸t′) →
      case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
        (⊢A , ⊢B) →
        fst p t′
      , fstₙ ⊢A ⊢B t′-ne
      , fst-cong ⊢A ⊢B t≡t′
      , sub (fstₘ m′ ▸t′ PE.refl fst-ok) γ≤ }}}
    (snd-cong {k = t} {p = p} {G = B} t~) ▸snd-t ok →
      case inv-usage-snd ▸snd-t of λ {
        (invUsageSnd ▸t γ≤) →
      case fullRedNe~↓ t~ ▸t ok of λ {
        (t′ , t′-ne , t≡t′ , ▸t′) →
      case inversion-ΠΣ (syntacticEqTerm t≡t′ .proj₁) of λ {
        (⊢A , ⊢B) →
        snd p t′
      , (                                 $⟨ sndₙ ⊢A ⊢B t′-ne ⟩
         Γ ⊢ne snd p t′ ∷ B [ fst p t′ ]  →⟨ flip _⊢ne_∷_.convₙ $
                                             substTypeEq (refl ⊢B) (fst-cong ⊢A ⊢B (sym t≡t′)) ⟩
         Γ ⊢ne snd p t′ ∷ B [ fst p t ]   □)
      , snd-cong ⊢A ⊢B t≡t′
      , sub (sndₘ ▸t′) γ≤ }}}
    (natrec-cong {F = A} {k = v} {p = p} {q = q} {r = r} A↑ t↑ u↑ v~)
      ▸natrec ok →
      case inv-usage-natrec ▸natrec of λ {
        (invUsageNatrec ▸t ▸u ▸v ▸A γ≤) →
      case fullRedConv↑ A↑ ▸A (𝟘ᵐ?≡𝟙ᵐ→ (proj₁ ∘→ ok)) of λ {
        (A′ , A′-nf , A≡A′ , ▸A′) →
      case fullRedTermConv↑ t↑ ▸t (proj₁ ∘→ proj₂ ∘→ ok) of λ {
        (t′ , t′-nf , t≡t′ , ▸t′) →
      case fullRedTermConv↑ u↑ ▸u (proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ ok) of λ {
        (u′ , u′-nf , u≡u′ , ▸u′) →
      case fullRedNe~↓ v~ ▸v (proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ ok) of λ {
        (v′ , v′-ne , v≡v′ , ▸v′) →
      case syntacticEq A≡A′ of λ {
        (⊢A , ⊢A′) →
      case wfEqTerm v≡v′ of λ {
        ⊢Γ →
      case ⊢Γ ∙ ℕⱼ ⊢Γ of λ {
        ⊢Γℕ →
        natrec p q r A′ t′ u′ v′
      , (                                                $⟨ u′-nf ⟩
         Γ ∙ ℕ ∙ A ⊢nf u′ ∷ wk1 (A [ suc (var x0) ]↑)    →⟨ ⊢nf∷-stable (reflConEq ⊢Γℕ ∙ A≡A′) ⟩
         Γ ∙ ℕ ∙ A′ ⊢nf u′ ∷ wk1 (A [ suc (var x0) ]↑)   →⟨ flip _⊢nf_∷_.convₙ $
                                                            wkEq (step id) (⊢Γℕ ∙ ⊢A′) $
                                                            subst↑TypeEq A≡A′ (refl (sucⱼ (var ⊢Γℕ here))) ⟩
         Γ ∙ ℕ ∙ A′ ⊢nf u′ ∷ wk1 (A′ [ suc (var x0) ]↑)  →⟨ (λ hyp → natrecₙ
                                                               A′-nf
                                                               (convₙ t′-nf (substTypeEq A≡A′ (refl (zeroⱼ ⊢Γ))))
                                                               hyp
                                                               v′-ne) ⟩
         Γ ⊢ne natrec p q r A′ t′ u′ v′ ∷ A′ [ v′ ]      →⟨ flip _⊢ne_∷_.convₙ $ _⊢_≡_.sym $
                                                            substTypeEq A≡A′ v≡v′ ⟩
         Γ ⊢ne natrec p q r A′ t′ u′ v′ ∷ A [ v ]        □)
      , natrec-cong ⊢A A≡A′ t≡t′ u≡u′ v≡v′
      , sub (natrecₘ ▸t′ ▸u′ ▸v′ ▸A′) γ≤ }}}}}}}}
    (prodrec-cong
       {p = p} {F = A} {G = B} {C = C} {g = u} {r = r} {q′ = q}
       C↑ u~ v↑)
      ▸prodrec ok →
      case inv-usage-prodrec ▸prodrec of λ {
        (invUsageProdrec ▸u ▸v ▸C prodrec-ok γ≤) →
      case fullRedConv↑ C↑ ▸C (𝟘ᵐ?≡𝟙ᵐ→ (proj₁ ∘→ ok)) of λ {
        (C′ , C′-nf , C≡C′ , ▸C′) →
      case fullRedNe~↓ u~ ▸u (ᵐ·≡𝟙ᵐ→ (proj₁ ∘→ proj₂ ∘→ ok)) of λ {
        (u′ , u′-ne , u≡u′ , ▸u′) →
      case fullRedTermConv↑ v↑ ▸v (proj₂ ∘→ proj₂ ∘→ ok) of λ {
        (v′ , v′-nf , v≡v′ , ▸v′) →
      case inversion-ΠΣ (syntacticEqTerm u≡u′ .proj₁) of λ {
        (⊢A , ⊢B) →
        prodrec r p q C′ u′ v′
      , (                                                            $⟨ v′-nf ⟩
         Γ ∙ A ∙ B ⊢nf v′ ∷ C [ prodᵣ p (var (x0 +1)) (var x0) ]↑²   →⟨ flip _⊢nf_∷_.convₙ $
                                                                        subst↑²TypeEq C≡C′ ⟩
         Γ ∙ A ∙ B ⊢nf v′ ∷ C′ [ prodᵣ p (var (x0 +1)) (var x0) ]↑²  →⟨ prodrecₙ ⊢A ⊢B C′-nf u′-ne ⟩
         Γ ⊢ne prodrec r p q C′ u′ v′ ∷ C′ [ u′ ]                    →⟨ flip _⊢ne_∷_.convₙ $ _⊢_≡_.sym $
                                                                        substTypeEq C≡C′ u≡u′ ⟩
         Γ ⊢ne prodrec r p q C′ u′ v′ ∷ C [ u ]                      □)
      , prodrec-cong ⊢A ⊢B C≡C′ u≡u′ v≡v′
      , sub (prodrecₘ ▸u′ ▸v′ ▸C′ prodrec-ok) γ≤ }}}}}
    (Emptyrec-cong {F = A} {p = p} A↑ t~) ▸Emptyrec ok →
      case inv-usage-Emptyrec ▸Emptyrec of λ {
        (invUsageEmptyrec ▸t ▸A γ≤) →
      case fullRedConv↑ A↑ ▸A (𝟘ᵐ?≡𝟙ᵐ→ (proj₁ ∘→ ok)) of λ {
        (A′ , A′-nf , A≡A′ , ▸A′) →
      case fullRedNe~↓ t~ ▸t (ᵐ·≡𝟙ᵐ→ (proj₂ ∘→ ok)) of λ {
        (t′ , t′-ne , t≡t′ , ▸t′) →
        Emptyrec p A′ t′
      , (                             $⟨ Emptyrecₙ A′-nf t′-ne ⟩
         Γ ⊢ne Emptyrec p A′ t′ ∷ A′  →⟨ flip _⊢ne_∷_.convₙ (sym A≡A′) ⟩
         Γ ⊢ne Emptyrec p A′ t′ ∷ A   □)
      , Emptyrec-cong A≡A′ t≡t′
      , sub (Emptyrecₘ ▸t′ ▸A′) γ≤ }}}

  fullRedNe~↓ :
    (t~ : Γ ⊢ t ~ t′ ↓ A) → γ ▸[ m ] t →
    (m PE.≡ 𝟙ᵐ → OK-⊢~↓ t~) →
    ∃ λ u → Γ ⊢ne u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
  fullRedNe~↓ ([~] A D whnfB k~l) γ▸t ok =
    let u , A-ne , t≡u , γ▸u = fullRedNe k~l γ▸t ok
    in  u , convₙ A-ne A≡ , conv t≡u A≡ , γ▸u
    where
    A≡ = subset* D

  fullRedConv↑ :
    (A↑ : Γ ⊢ A [conv↑] A′) → γ ▸[ m ] A →
    (m PE.≡ 𝟙ᵐ → OK-⊢[conv↑] A↑) →
    ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B × γ ▸[ m ] B
  fullRedConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) γ▸A ok =
    let γ▸A′ = usagePres* γ▸A D
        B″ , nf , B′≡B″ , γ▸B″ = fullRedConv↓ A′<>B′ γ▸A′ ok
    in  B″ , nf , trans (subset* D) B′≡B″ , γ▸B″

  fullRedConv↓ :
    (A↓ : Γ ⊢ A [conv↓] A′) → γ ▸[ m ] A →
    (m PE.≡ 𝟙ᵐ → OK-⊢[conv↓] A↓) →
    ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B × γ ▸[ m ] B
  fullRedConv↓ = λ where
    (U-refl     ⊢Γ) ▸U _  → U     , Uₙ     ⊢Γ , refl (Uⱼ     ⊢Γ) , ▸U
    (ℕ-refl     ⊢Γ) ▸ℕ _  → ℕ     , ℕₙ     ⊢Γ , refl (ℕⱼ     ⊢Γ) , ▸ℕ
    (Empty-refl ⊢Γ) ▸⊥ _  → Empty , Emptyₙ ⊢Γ , refl (Emptyⱼ ⊢Γ) , ▸⊥
    (Unit-refl  ⊢Γ) ▸⊤ _  → Unit  , Unitₙ  ⊢Γ , refl (Unitⱼ  ⊢Γ) , ▸⊤
    (ne A~)         ▸A ok →
      case fullRedNe~↓ A~ ▸A ok of λ {
        (B , B-ne , A≡B , ▸B) →
      B , univₙ (neₙ Uₙ B-ne) , univ A≡B , ▸B }
    (ΠΣ-cong ⊢A A↑ B↑) ▸ΠΣAB ok →
      case inv-usage-ΠΣ ▸ΠΣAB of λ {
        (invUsageΠΣ ▸A ▸B γ≤ ΠΣ-ok) →
      case fullRedConv↑ A↑ ▸A (ᵐ·≡𝟙ᵐ→ (proj₁ ∘→ ok)) of λ {
        (A′ , A′-nf , A≡A′ , ▸A′) →
      case fullRedConv↑ B↑ ▸B (proj₂ ∘→ ok) of λ {
        (B′ , B′-nf , B≡B′ , ▸B′) →
      ΠΣ⟨ _ ⟩ _ , _ ▷ A′ ▹ B′ ,
      ΠΣₙ A′-nf (⊢nf-stable (reflConEq (wfEq A≡A′) ∙ A≡A′) B′-nf) ,
      ΠΣ-cong ⊢A A≡A′ B≡B′ ,
      sub (ΠΣₘ ▸A′ ▸B′ ΠΣ-ok) γ≤ }}}

  fullRedTermConv↑ :
    (t↑ : Γ ⊢ t [conv↑] t′ ∷ A) → γ ▸[ m ] t →
    (m PE.≡ 𝟙ᵐ → OK-⊢[conv↑]∷ t↑) →
    ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
  fullRedTermConv↑
    ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) γ▸t ok =
    let γ▸t′ = usagePres*Term γ▸t d
        u″ , nf , u′≡u″ , γ▸u″ = fullRedTermConv↓ t<>u γ▸t′ ok
    in  u″ , convₙ nf B≡A , conv (trans (subset*Term d) u′≡u″) B≡A , γ▸u″
    where
    B≡A = sym (subset* D)

  fullRedTermConv↓ :
    (t↓ : Γ ⊢ t [conv↓] t′ ∷ A) → γ ▸[ m ] t →
    (m PE.≡ 𝟙ᵐ → OK-⊢[conv↓]∷ t↓) →
    ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
  fullRedTermConv↓ {Γ = Γ} {t = t} {γ = γ} {m = m} = λ where
    (ℕ-ins t~) ▸t ok →
      case fullRedNe~↓ t~ ▸t ok of λ {
        (u , u-nf , t≡u , ▸u) →
      u , neₙ ℕₙ u-nf , t≡u , ▸u }
    (Empty-ins t~) ▸t ok →
      case fullRedNe~↓ t~ ▸t ok of λ {
        (u , u-nf , t≡u , ▸u) →
      u , neₙ Emptyₙ u-nf , t≡u , ▸u }
    (Unit-ins t~) ▸t ok →
      case syntacticEqTerm (soundness~↓ t~) of λ {
        (Γ⊢ , ⊢t , _) →
      case wf Γ⊢ of λ {
        ⊢Γ →
        star
      , starₙ ⊢Γ
      , η-unit ⊢t (starⱼ ⊢Γ)
      , sub starₘ (▸→≤ᶜ𝟘ᶜ _ ok ▸t) }}
    (Σᵣ-ins ⊢t∷ΣAB _ t~) ▸t ok →
      case fullRedNe~↓ t~ ▸t ok of λ {
        (v , v-ne , t≡v , ▸v) →
      case syntacticEqTerm t≡v of λ {
        (_ , ⊢t∷ΣCD , _) →
      case ne~↓ t~ of λ {
        (_ , t-ne , _) →
      case neTypeEq t-ne ⊢t∷ΣCD ⊢t∷ΣAB of λ {
        ΣCD≡ΣAB →
      case inversion-ΠΣ (syntacticTerm ⊢t∷ΣAB) of λ {
        (⊢A , ⊢B) →
        v
      , neₙ Σᵣₙ (convₙ v-ne ΣCD≡ΣAB)
      , conv t≡v ΣCD≡ΣAB
      , ▸v }}}}}
    (ne-ins ⊢t∷A _ A-ne t~↓B) ▸t ok →
      case fullRedNe~↓ t~↓B ▸t ok of λ {
        (u , u-ne , t≡u∷B , ▸u) →
      case syntacticEqTerm t≡u∷B of λ {
        (_ , ⊢t∷B , _) →
      case ne~↓ t~↓B of λ {
        (_ , t-ne , _) →
      case neTypeEq t-ne ⊢t∷B ⊢t∷A of λ {
        B≡A →
        u
      , neₙ (neₙ A-ne) (convₙ u-ne B≡A)
      , conv t≡u∷B B≡A
      , ▸u }}}}
    (univ {A = A} ⊢A _ A↓) ▸A ok →
      case fullRedConv↓ A↓ ▸A ok of λ {
        (B , B-nf , A≡B , ▸B) →
        B
      , (               $⟨ A≡B ⟩
         (Γ ⊢ A ≡ B)    →⟨ inverseUnivEq ⊢A ⟩
         Γ ⊢ A ≡ B ∷ U  →⟨ (λ hyp → syntacticEqTerm hyp .proj₂ .proj₂) ⟩
         Γ ⊢ B ∷ U      →⟨ ⊢nf∷U→⊢nf∷U B-nf ⟩
         Γ ⊢nf B ∷ U    □)
      , inverseUnivEq ⊢A A≡B
      , ▸B }
    (zero-refl ⊢Γ) ▸zero _ →
      zero , zeroₙ ⊢Γ , refl (zeroⱼ ⊢Γ) , ▸zero
    (suc-cong t↑) ▸suc-t ok →
      case inv-usage-suc ▸suc-t of λ {
        (invUsageSuc ▸t γ≤) →
      case fullRedTermConv↑ t↑ ▸t ok of λ {
        (u , u-nf , t≡u , ▸u) →
      suc u , sucₙ u-nf , suc-cong t≡u , sub (sucₘ ▸u) γ≤ }}
    (prod-cong {p = p} {q = q} {F = A} {G = B} {t = t} ⊢A ⊢B t↑ u↑)
      ▸t,u ok →
      case inv-usage-prodᵣ ▸t,u of λ {
        (invUsageProdᵣ ▸t ▸u γ≤) →
      case fullRedTermConv↑ t↑ ▸t (ᵐ·≡𝟙ᵐ→ (proj₁ ∘→ ok)) of λ {
        (t′ , t′-nf , t≡t′ , ▸t′) →
      case fullRedTermConv↑ u↑ ▸u (proj₂ ∘→ ok) of λ {
        (u′ , u′-nf , u≡u′ , ▸u′) →
        prod! t′ u′
      , (                                      $⟨ u′-nf ⟩
         Γ ⊢nf u′ ∷ B [ t ]                    →⟨ flip _⊢nf_∷_.convₙ $
                                                  substTypeEq (refl ⊢B) t≡t′ ⟩
         Γ ⊢nf u′ ∷ B [ t′ ]                   →⟨ prodₙ ⊢A ⊢B t′-nf ⟩
         Γ ⊢nf prod! t′ u′ ∷ Σᵣ p , q ▷ A ▹ B  □)
      , prod-cong ⊢A ⊢B t≡t′ u≡u′
      , sub (prodᵣₘ ▸t′ ▸u′) γ≤ }}}
    (η-eq {p = p} {q = q} {f = t} {F = A} {G = B} ⊢t _ _ _ t0≡u0)
      ▸t ok →
      case fullRedTermConv↑ t0≡u0
             (wkUsage (step id) ▸t ∘ₘ var) ok of λ {
        (u , u-nf , t0≡u , ▸u) →
        lam p u
      , lamₙ (inversion-ΠΣ (syntacticTerm ⊢t) .proj₁) u-nf
      , (                                                       $⟨ sym (Π-η ⊢t) ⟩
         Γ ⊢ t ≡ lam p (wk1 t ∘⟨ p ⟩ var x0) ∷ Π p , q ▷ A ▹ B  →⟨ flip _⊢_≡_∷_.trans (lam-cong t0≡u) ⟩
         Γ ⊢ t ≡ lam p u ∷ Π p , q ▷ A ▹ B                      □)
      , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
         lamₘ $ sub ▸u $ begin
           γ ∙ ⌜ m ⌝ · p                      ≈⟨ ≈ᶜ-refl ∙ ⌜⌝-·-comm m ⟩
           γ ∙ p · ⌜ m ⌝                      ≈˘⟨ +ᶜ-identityʳ _ ∙ ·⌜ᵐ·⌝ m ⟩
           γ +ᶜ 𝟘ᶜ ∙ p · ⌜ m ᵐ· p ⌝           ≈˘⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ∙ +-identityˡ _ ⟩
           γ +ᶜ p ·ᶜ 𝟘ᶜ ∙ 𝟘 + p · ⌜ m ᵐ· p ⌝  ∎) }
    (Σ-η {p = p} {q = q} {F = A} {G = B} ⊢t _ _ _ fst-t↑ snd-t↑) ▸t ok →
      case Σ-η-lemma m (proj₂ ∘→ proj₂ ∘→ ok) ▸t of λ {
        (δ , ▸fst-t , γ≤) →
      case fullRedTermConv↑ fst-t↑ ▸fst-t (ᵐ·≡𝟙ᵐ→ (proj₁ ∘→ ok)) of λ {
        (u₁ , u₁-nf , fst-t≡u₁ , ▸u₁) →
      case fullRedTermConv↑ snd-t↑ (sndₘ ▸t)
             (proj₁ ∘→ proj₂ ∘→ ok) of λ {
        (u₂ , u₂-nf , snd-t≡u₂ , ▸u₂) →
      case inversion-ΠΣ (syntacticTerm ⊢t) of λ {
        (⊢A , ⊢B) →
        prodₚ p u₁ u₂
      , (                                        $⟨ u₂-nf ⟩
         Γ ⊢nf u₂ ∷ B [ fst p t ]                →⟨ flip _⊢nf_∷_.convₙ $
                                                    substTypeEq (refl ⊢B) fst-t≡u₁ ⟩
         Γ ⊢nf u₂ ∷ B [ u₁ ]                     →⟨ prodₙ ⊢A ⊢B u₁-nf ⟩
         Γ ⊢nf prodₚ p u₁ u₂ ∷ Σₚ p , q ▷ A ▹ B  □)
      , (                                                        $⟨ sym (Σ-η-prod-fst-snd ⊢t) ⟩
         Γ ⊢ t ≡ prodₚ p (fst p t) (snd p t) ∷ Σₚ p , q ▷ A ▹ B  →⟨ flip _⊢_≡_∷_.trans $
                                                                    prod-cong ⊢A ⊢B fst-t≡u₁ snd-t≡u₂ ⟩
         Γ ⊢ t ≡ prodₚ p u₁ u₂ ∷ Σₚ p , q ▷ A ▹ B                □)
      , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
         sub (prodₚₘ ▸u₁ ▸u₂) $ begin
           γ            ≤⟨ ∧ᶜ-greatest-lower-bound γ≤ ≤ᶜ-refl ⟩
           p ·ᶜ δ ∧ᶜ γ  ∎) }}}}
    (η-unit ⊢t _ _ _) ▸t ok →
      case wfTerm ⊢t of λ {
        ⊢Γ →
        star
      , starₙ ⊢Γ
      , η-unit ⊢t (starⱼ ⊢Γ)
      , sub starₘ (▸→≤ᶜ𝟘ᶜ _ ok ▸t) }

------------------------------------------------------------------------
-- The full reduction theorems

-- If a type is well-formed and well-resourced, then it is
-- definitionally equal to a well-resourced type in η-long normal form
-- (given a certain assumption).

fullRed :
  (⊢A : Γ ⊢ A) → γ ▸[ m ] A →
  (m PE.≡ 𝟙ᵐ → OK-⊢[conv↑] (completeEq (refl ⊢A))) →
  ∃ λ B → Γ ⊢nf B × Γ ⊢ A ≡ B × γ ▸[ m ] B
fullRed ⊢A = fullRedConv↑ (completeEq (refl ⊢A))

-- If a term is well-formed and well-resourced, then it is
-- definitionally equal to a well-resourced term in η-long normal
-- form (given a certain assumption).

fullRedTerm :
  (⊢t : Γ ⊢ t ∷ A) → γ ▸[ m ] t →
  (m PE.≡ 𝟙ᵐ → OK-⊢[conv↑]∷ (completeEqTerm (refl ⊢t))) →
  ∃ λ u → Γ ⊢nf u ∷ A × Γ ⊢ t ≡ u ∷ A × γ ▸[ m ] u
fullRedTerm ⊢t = fullRedTermConv↑ (completeEqTerm (refl ⊢t))
