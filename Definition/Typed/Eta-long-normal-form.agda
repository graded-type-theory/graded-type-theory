------------------------------------------------------------------------
-- Eta-long normal forms
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Eta-long-normal-form
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open Type-restrictions R

open import Definition.Conversion R
open import Definition.Conversion.Consequences.Completeness R
open import Definition.Conversion.Soundness R

open import Definition.Typed R
open import Definition.Typed.Consequences.DerivedRules R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.NeTypeEq R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Stability R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R

open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Normal-form M

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n             : Nat
  x             : Fin _
  Γ Δ           : Con _ _
  A B C t u v w : Term _
  b             : BinderMode
  s             : SigmaMode
  p q q′ r      : M

------------------------------------------------------------------------
-- Definitions of η-long normal types and terms and some associated
-- concepts

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
             ΠΣ-allowed b p q →
             Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
    Emptyₙ : ⊢ Γ →
             Γ ⊢nf Empty
    Unitₙ  : ⊢ Γ →
             Unit-allowed →
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
             ΠΣ-allowed b p q →
             Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U
    lamₙ   : Γ ⊢ A →
             Γ ∙ A ⊢nf t ∷ B →
             Π-allowed p q →
             Γ ⊢nf lam p t ∷ Π p , q ▷ A ▹ B
    prodₙ  : Γ ⊢ A →
             Γ ∙ A ⊢ B →
             Γ ⊢nf t ∷ A →
             Γ ⊢nf u ∷ B [ t ]₀ →
             Σ-allowed s p q →
             Γ ⊢nf prod s p t u ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
    Emptyₙ : ⊢ Γ →
             Γ ⊢nf Empty ∷ U
    Unitₙ  : ⊢ Γ →
             Unit-allowed →
             Γ ⊢nf Unit ∷ U
    starₙ  : ⊢ Γ →
             Unit-allowed →
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
                Γ ⊢ne t ∘⟨ p ⟩ u ∷ B [ u ]₀
    fstₙ      : Γ ⊢ A →
                Γ ∙ A ⊢ B →
                Γ ⊢ne t ∷ Σₚ p , q ▷ A ▹ B →
                Γ ⊢ne fst p t ∷ A
    sndₙ      : Γ ⊢ A →
                Γ ∙ A ⊢ B →
                Γ ⊢ne t ∷ Σₚ p , q ▷ A ▹ B →
                Γ ⊢ne snd p t ∷ B [ fst p t ]₀
    prodrecₙ  : Γ ⊢ A →
                Γ ∙ A ⊢ B →
                Γ ∙ (Σᵣ p , q′ ▷ A ▹ B) ⊢nf C →
                Γ ⊢ne t ∷ Σᵣ p , q′ ▷ A ▹ B →
                Γ ∙ A ∙ B ⊢nf u ∷ C [ prodᵣ p (var x1) (var x0) ]↑² →
                Σᵣ-allowed p q′ →
                Γ ⊢ne prodrec r p q C t u ∷ C [ t ]₀
    emptyrecₙ : Γ ⊢nf A →
                Γ ⊢ne t ∷ Empty →
                Γ ⊢ne emptyrec p A t ∷ A
    natrecₙ   : Γ ∙ ℕ ⊢nf A →
                Γ ⊢nf t ∷ A [ zero ]₀ →
                Γ ∙ ℕ ∙ A ⊢nf u ∷ A [ suc (var x1) ]↑² →
                Γ ⊢ne v ∷ ℕ →
                Γ ⊢ne natrec p q r A t u v ∷ A [ v ]₀

------------------------------------------------------------------------
-- A lemma

-- If A is a normal type of type U, then A is a normal term of type U.

⊢nf∷U→⊢nf∷U : Γ ⊢nf A → Γ ⊢ A ∷ U → Γ ⊢nf A ∷ U
⊢nf∷U→⊢nf∷U = λ where
  (Uₙ _)         ⊢U∷U    → ⊥-elim (inversion-U ⊢U∷U)
  (univₙ ⊢A)     _       → ⊢A
  (ΠΣₙ ⊢A ⊢B ok) ⊢ΠΣAB∷U →
    case inversion-ΠΣ-U ⊢ΠΣAB∷U of λ {
      (⊢A∷U , ⊢B∷U , _) →
    ΠΣₙ (⊢nf∷U→⊢nf∷U ⊢A ⊢A∷U) (⊢nf∷U→⊢nf∷U ⊢B ⊢B∷U) ok }
  (Emptyₙ ⊢Γ)    _ → Emptyₙ ⊢Γ
  (Unitₙ ⊢Γ ok)  _ → Unitₙ ⊢Γ ok
  (ℕₙ ⊢Γ)        _ → ℕₙ ⊢Γ

------------------------------------------------------------------------
-- Some conversion functions

mutual

  -- If A is an η-long normal type, then A is well-typed.

  ⊢nf→⊢ : Γ ⊢nf A → Γ ⊢ A
  ⊢nf→⊢ = λ where
    (Uₙ ⊢Γ)        → Uⱼ ⊢Γ
    (univₙ ⊢A)     → univ (⊢nf∷→⊢∷ ⊢A)
    (ΠΣₙ ⊢A ⊢B ok) → ΠΣⱼ (⊢nf→⊢ ⊢A) (⊢nf→⊢ ⊢B) ok
    (Emptyₙ ⊢Γ)    → Emptyⱼ ⊢Γ
    (Unitₙ ⊢Γ ok)  → Unitⱼ ⊢Γ ok
    (ℕₙ ⊢Γ)        → ℕⱼ ⊢Γ

  -- If t is an η-long normal term, then t is well-typed.

  ⊢nf∷→⊢∷ : Γ ⊢nf t ∷ A → Γ ⊢ t ∷ A
  ⊢nf∷→⊢∷ = λ where
    (convₙ ⊢t A≡B)         → conv (⊢nf∷→⊢∷ ⊢t) A≡B
    (ΠΣₙ ⊢A ⊢B ok)         → ΠΣⱼ (⊢nf∷→⊢∷ ⊢A) (⊢nf∷→⊢∷ ⊢B) ok
    (lamₙ ⊢A ⊢t ok)        → lamⱼ ⊢A (⊢nf∷→⊢∷ ⊢t) ok
    (prodₙ ⊢A ⊢B ⊢t ⊢u ok) → prodⱼ ⊢A ⊢B (⊢nf∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢u) ok
    (Emptyₙ ⊢Γ)            → Emptyⱼ ⊢Γ
    (Unitₙ ⊢Γ ok)          → Unitⱼ ⊢Γ ok
    (starₙ ⊢Γ ok)          → starⱼ ⊢Γ ok
    (ℕₙ ⊢Γ)                → ℕⱼ ⊢Γ
    (zeroₙ ⊢Γ)             → zeroⱼ ⊢Γ
    (sucₙ ⊢t)              → sucⱼ (⊢nf∷→⊢∷ ⊢t)
    (neₙ _ ⊢t)             → ⊢ne∷→⊢∷ ⊢t

  -- If Γ ⊢ne t ∷ A holds, then t is well-typed.

  ⊢ne∷→⊢∷ : Γ ⊢ne t ∷ A → Γ ⊢ t ∷ A
  ⊢ne∷→⊢∷ = λ where
    (convₙ ⊢t A≡B)               → conv (⊢ne∷→⊢∷ ⊢t) A≡B
    (varₙ ⊢Γ x∈)                 → var ⊢Γ x∈
    (∘ₙ ⊢t ⊢u)                   → ⊢ne∷→⊢∷ ⊢t ∘ⱼ ⊢nf∷→⊢∷ ⊢u
    (fstₙ ⊢A ⊢B ⊢t)              → fstⱼ ⊢A ⊢B (⊢ne∷→⊢∷ ⊢t)
    (sndₙ ⊢A ⊢B ⊢t)              → sndⱼ ⊢A ⊢B (⊢ne∷→⊢∷ ⊢t)
    (prodrecₙ ⊢A ⊢B ⊢C ⊢t ⊢u ok) → prodrecⱼ ⊢A ⊢B (⊢nf→⊢ ⊢C)
                                     (⊢ne∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢u) ok
    (emptyrecₙ ⊢A ⊢t)            → emptyrecⱼ (⊢nf→⊢ ⊢A) (⊢ne∷→⊢∷ ⊢t)
    (natrecₙ ⊢A ⊢t ⊢u ⊢v)        → natrecⱼ (⊢nf→⊢ ⊢A) (⊢nf∷→⊢∷ ⊢t)
                                     (⊢nf∷→⊢∷ ⊢u) (⊢ne∷→⊢∷ ⊢v)

mutual

  -- If A is an η-long normal type, then A is normal.

  ⊢nf→Nf : Γ ⊢nf A → Nf A
  ⊢nf→Nf = λ where
    (Uₙ _)        → Uₙ
    (univₙ ⊢A)    → ⊢nf∷→Nf ⊢A
    (ΠΣₙ ⊢A ⊢B _) → ΠΣₙ (⊢nf→Nf ⊢A) (⊢nf→Nf ⊢B)
    (Emptyₙ _)    → Emptyₙ
    (Unitₙ _ _)   → Unitₙ
    (ℕₙ _)        → ℕₙ

  -- If t is an η-long normal term, then t is normal.

  ⊢nf∷→Nf : Γ ⊢nf t ∷ A → Nf t
  ⊢nf∷→Nf = λ where
    (convₙ ⊢t _)        → ⊢nf∷→Nf ⊢t
    (ΠΣₙ ⊢A ⊢B _)       → ΠΣₙ (⊢nf∷→Nf ⊢A) (⊢nf∷→Nf ⊢B)
    (lamₙ _ ⊢t _)       → lamₙ (⊢nf∷→Nf ⊢t)
    (prodₙ _ _ ⊢t ⊢u _) → prodₙ (⊢nf∷→Nf ⊢t) (⊢nf∷→Nf ⊢u)
    (Emptyₙ _)          → Emptyₙ
    (Unitₙ _ _)         → Unitₙ
    (starₙ _ _)         → starₙ
    (ℕₙ _)              → ℕₙ
    (zeroₙ _)           → zeroₙ
    (sucₙ ⊢t)           → sucₙ (⊢nf∷→Nf ⊢t)
    (neₙ _ ⊢t)          → ne (⊢ne∷→NfNeutral ⊢t)

  -- If Γ ⊢ne t ∷ A holds, then t is "NfNeutral".

  ⊢ne∷→NfNeutral : Γ ⊢ne t ∷ A → NfNeutral t
  ⊢ne∷→NfNeutral = λ where
    (convₙ ⊢t _)              → ⊢ne∷→NfNeutral ⊢t
    (varₙ _ _)                → var _
    (∘ₙ ⊢t ⊢u)                → ∘ₙ (⊢ne∷→NfNeutral ⊢t) (⊢nf∷→Nf ⊢u)
    (fstₙ _ _ ⊢t)             → fstₙ (⊢ne∷→NfNeutral ⊢t)
    (sndₙ _ _ ⊢t)             → sndₙ (⊢ne∷→NfNeutral ⊢t)
    (prodrecₙ _ _ ⊢C ⊢t ⊢u _) → prodrecₙ (⊢nf→Nf ⊢C)
                                  (⊢ne∷→NfNeutral ⊢t) (⊢nf∷→Nf ⊢u)
    (emptyrecₙ ⊢A ⊢t)         → emptyrecₙ (⊢nf→Nf ⊢A)
                                  (⊢ne∷→NfNeutral ⊢t)
    (natrecₙ ⊢A ⊢t ⊢u ⊢v)     → natrecₙ (⊢nf→Nf ⊢A) (⊢nf∷→Nf ⊢t)
                                  (⊢nf∷→Nf ⊢u) (⊢ne∷→NfNeutral ⊢v)

------------------------------------------------------------------------
-- Stability

mutual

  -- If A is a normal type with respect to the context Γ, and Γ is
  -- judgmentally equal to Δ, then A is also a normal type with
  -- respect to Δ.

  ⊢nf-stable : ⊢ Γ ≡ Δ → Γ ⊢nf A → Δ ⊢nf A
  ⊢nf-stable Γ≡Δ = λ where
      (Uₙ ⊢Γ)        → Uₙ ⊢Δ
      (univₙ ⊢A)     → univₙ (⊢nf∷-stable Γ≡Δ ⊢A)
      (ΠΣₙ ⊢A ⊢B ok) → ΠΣₙ (⊢nf-stable Γ≡Δ ⊢A)
                         (⊢nf-stable (Γ≡Δ ∙ refl (⊢nf→⊢ ⊢A)) ⊢B) ok
      (Emptyₙ ⊢Γ)    → Emptyₙ ⊢Δ
      (Unitₙ ⊢Γ ok)  → Unitₙ ⊢Δ ok
      (ℕₙ ⊢Γ)        → ℕₙ ⊢Δ
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
      (ΠΣₙ ⊢A ⊢B ok) → ΠΣₙ
        (⊢nf∷-stable Γ≡Δ ⊢A)
        (⊢nf∷-stable (Γ≡Δ ∙ refl (⊢nf→⊢ (univₙ ⊢A))) ⊢B)
        ok
      (lamₙ ⊢A ⊢t ok) → lamₙ
        (stability Γ≡Δ ⊢A)
        (⊢nf∷-stable (Γ≡Δ ∙ refl ⊢A) ⊢t)
        ok
      (prodₙ ⊢A ⊢B ⊢t ⊢u ok) → prodₙ
        (stability Γ≡Δ ⊢A)
        (stability (Γ≡Δ ∙ refl ⊢A) ⊢B)
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
      (prodrecₙ ⊢A ⊢B ⊢C ⊢t ⊢u ok) → prodrecₙ
        (stability Γ≡Δ ⊢A)
        (stability (Γ≡Δ ∙ refl ⊢A) ⊢B)
        (⊢nf-stable (Γ≡Δ ∙ refl (ΠΣⱼ ⊢A ⊢B ok)) ⊢C)
        (⊢ne∷-stable Γ≡Δ ⊢t)
        (⊢nf∷-stable (Γ≡Δ ∙ refl ⊢A ∙ refl ⊢B) ⊢u)
        ok
      (emptyrecₙ ⊢A ⊢t) → emptyrecₙ
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
-- Inversion lemmas

-- Inversion for terms that are Π- or Σ-types.

inversion-nf-ΠΣ-U :
  Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ C →
  Γ ⊢nf A ∷ U × Γ ∙ A ⊢nf B ∷ U × Γ ⊢ C ≡ U × ΠΣ-allowed b p q
inversion-nf-ΠΣ-U (ΠΣₙ ⊢A ⊢B ok) =
  ⊢A , ⊢B , refl (Uⱼ (wfTerm (⊢nf∷→⊢∷ ⊢A))) , ok
inversion-nf-ΠΣ-U (convₙ ⊢ΠΣ D≡C) =
  case inversion-nf-ΠΣ-U ⊢ΠΣ of λ {
    (⊢A , ⊢B , D≡U , ok) →
  ⊢A , ⊢B , trans (sym D≡C) D≡U , ok }
inversion-nf-ΠΣ-U (neₙ _ ⊢ΠΣ) =
  case ⊢ne∷→NfNeutral ⊢ΠΣ of λ ()

-- Inversion for Π- and Σ-types.

inversion-nf-ΠΣ :
  Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  Γ ⊢nf A × Γ ∙ A ⊢nf B × ΠΣ-allowed b p q
inversion-nf-ΠΣ = λ where
  (ΠΣₙ ⊢A ⊢B ok) → ⊢A , ⊢B , ok
  (univₙ ⊢ΠΣAB)  → case inversion-nf-ΠΣ-U ⊢ΠΣAB of λ where
    (⊢A , ⊢B , _ , ok) → univₙ ⊢A , univₙ ⊢B , ok

-- Inversion for lam.

inversion-nf-lam :
  Γ ⊢nf lam p t ∷ A →
  ∃₃ λ B C q →
     (Γ ⊢ B) ×
     Γ ∙ B ⊢nf t ∷ C ×
     Γ ⊢ A ≡ Π p , q ▷ B ▹ C ×
     Π-allowed p q
inversion-nf-lam (neₙ _ ⊢lam) =
  case ⊢ne∷→NfNeutral ⊢lam of λ ()
inversion-nf-lam (lamₙ ⊢B ⊢t ok) =
  _ , _ , _ , ⊢B , ⊢t ,
  refl (ΠΣⱼ ⊢B (syntacticTerm (⊢nf∷→⊢∷ ⊢t)) ok) , ok
inversion-nf-lam (convₙ ⊢lam A≡B) =
  case inversion-nf-lam ⊢lam of λ {
    (_ , _ , _ , ⊢B , ⊢t , A≡ , ok) →
  _ , _ , _ , ⊢B , ⊢t , trans (sym A≡B) A≡ , ok }

-- Inversion for prod.

inversion-nf-prod :
  Γ ⊢nf prod s p t u ∷ A →
  ∃₃ λ B C q →
    (Γ ⊢ B) × (Γ ∙ B ⊢ C) ×
    Γ ⊢nf t ∷ B × Γ ⊢nf u ∷ C [ t ]₀ ×
    Γ ⊢ A ≡ Σ⟨ s ⟩ p , q ▷ B ▹ C ×
    Σ-allowed s p q
inversion-nf-prod (neₙ _ ⊢prod) =
  case ⊢ne∷→NfNeutral ⊢prod of λ ()
inversion-nf-prod (prodₙ ⊢B ⊢C ⊢t ⊢u ok) =
  _ , _ , _ , ⊢B , ⊢C , ⊢t , ⊢u , refl (ΠΣⱼ ⊢B ⊢C ok) , ok
inversion-nf-prod (convₙ ⊢prod A≡B) =
  case inversion-nf-prod ⊢prod of λ {
    (_ , _ , _ , ⊢B , ⊢C , ⊢t , ⊢u , A≡ , ok) →
  _ , _ , _ , ⊢B , ⊢C , ⊢t , ⊢u , trans (sym A≡B) A≡ , ok }

-- Inversion for suc.

inversion-nf-suc :
  Γ ⊢nf suc t ∷ A →
  Γ ⊢nf t ∷ ℕ × Γ ⊢ A ≡ ℕ
inversion-nf-suc (neₙ _ ⊢suc) =
  case ⊢ne∷→NfNeutral ⊢suc of λ ()
inversion-nf-suc (sucₙ ⊢t) =
  ⊢t , refl (ℕⱼ (wfTerm (⊢nf∷→⊢∷ ⊢t)))
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

inversion-nf-app :
  Γ ⊢nf t ∘⟨ p ⟩ u ∷ A →
  ∃₃ λ B C q →
     Γ ⊢ne t ∷ Π p , q ▷ B ▹ C × Γ ⊢nf u ∷ B × Γ ⊢ A ≡ C [ u ]₀
inversion-nf-app (neₙ _ ⊢app) =
  inversion-ne-app ⊢app
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
  ∃₃ λ B C q →
     (Γ ⊢ B) × (Γ ∙ B ⊢ C) ×
     Γ ⊢ne t ∷ Σₚ p , q ▷ B ▹ C × Γ ⊢ A ≡ B
inversion-ne-fst (fstₙ ⊢B ⊢C ⊢t) =
  _ , _ , _ , ⊢B , ⊢C , ⊢t , refl ⊢B
inversion-ne-fst (convₙ ⊢fst A≡B) =
  case inversion-ne-fst ⊢fst of λ {
    (_ , _ , _ , ⊢B , ⊢C , ⊢t , A≡) →
  _ , _ , _ , ⊢B , ⊢C , ⊢t , trans (sym A≡B) A≡ }

inversion-nf-fst :
  Γ ⊢nf fst p t ∷ A →
  ∃₃ λ B C q →
     (Γ ⊢ B) × (Γ ∙ B ⊢ C) ×
     Γ ⊢ne t ∷ Σₚ p , q ▷ B ▹ C × Γ ⊢ A ≡ B
inversion-nf-fst (neₙ _ ⊢fst) =
  inversion-ne-fst ⊢fst
inversion-nf-fst (convₙ ⊢fst A≡B) =
  case inversion-nf-fst ⊢fst of λ {
    (_ , _ , _ , ⊢B , ⊢C , ⊢t , A≡) →
  _ , _ , _ , ⊢B , ⊢C , ⊢t , trans (sym A≡B) A≡ }

inversion-nf-ne-fst :
  Γ ⊢nf fst p t ∷ A ⊎ Γ ⊢ne fst p t ∷ A →
  ∃₃ λ B C q →
     (Γ ⊢ B) × (Γ ∙ B ⊢ C) ×
     Γ ⊢ne t ∷ Σₚ p , q ▷ B ▹ C × Γ ⊢ A ≡ B
inversion-nf-ne-fst (inj₁ ⊢fst) = inversion-nf-fst ⊢fst
inversion-nf-ne-fst (inj₂ ⊢fst) = inversion-ne-fst ⊢fst

-- Inversion for snd.

inversion-ne-snd :
  Γ ⊢ne snd p t ∷ A →
  ∃₃ λ B C q →
     (Γ ⊢ B) × (Γ ∙ B ⊢ C) ×
     Γ ⊢ne t ∷ Σₚ p , q ▷ B ▹ C ×
     Γ ⊢ A ≡ C [ fst p t ]₀
inversion-ne-snd (sndₙ ⊢B ⊢C ⊢t) =
  _ , _ , _ , ⊢B , ⊢C , ⊢t ,
  refl (substType ⊢C (fstⱼ ⊢B ⊢C (⊢ne∷→⊢∷ ⊢t)))
inversion-ne-snd (convₙ ⊢snd A≡B) =
  case inversion-ne-snd ⊢snd of λ {
    (_ , _ , _ , ⊢B , ⊢C , ⊢t , A≡) →
  _ , _ , _ , ⊢B , ⊢C , ⊢t , trans (sym A≡B) A≡ }

inversion-nf-snd :
  Γ ⊢nf snd p t ∷ A →
  ∃₃ λ B C q →
     (Γ ⊢ B) × (Γ ∙ B ⊢ C) ×
     Γ ⊢ne t ∷ Σₚ p , q ▷ B ▹ C ×
     Γ ⊢ A ≡ C [ fst p t ]₀
inversion-nf-snd (neₙ _ ⊢snd) =
  inversion-ne-snd ⊢snd
inversion-nf-snd (convₙ ⊢snd A≡B) =
  case inversion-nf-snd ⊢snd of λ {
    (_ , _ , _ , ⊢B , ⊢C , ⊢t , A≡) →
  _ , _ , _ , ⊢B , ⊢C , ⊢t , trans (sym A≡B) A≡ }

inversion-nf-ne-snd :
  Γ ⊢nf snd p t ∷ A ⊎ Γ ⊢ne snd p t ∷ A →
  ∃₃ λ B C q →
     (Γ ⊢ B) × (Γ ∙ B ⊢ C) ×
     Γ ⊢ne t ∷ Σₚ p , q ▷ B ▹ C ×
     Γ ⊢ A ≡ C [ fst p t ]₀
inversion-nf-ne-snd (inj₁ ⊢snd) = inversion-nf-snd ⊢snd
inversion-nf-ne-snd (inj₂ ⊢snd) = inversion-ne-snd ⊢snd

-- Inversion for prodrec.

inversion-ne-prodrec :
  Γ ⊢ne prodrec r p q A t u ∷ B →
  ∃₃ λ C D q →
    (Γ ⊢ C) × (Γ ∙ C ⊢ D) ×
    (Γ ∙ (Σᵣ p , q ▷ C ▹ D) ⊢nf A) ×
    Γ ⊢ne t ∷ Σᵣ p , q ▷ C ▹ D ×
    Γ ∙ C ∙ D ⊢nf u ∷ A [ prodᵣ p (var x1) (var x0) ]↑² ×
    Γ ⊢ B ≡ A [ t ]₀
inversion-ne-prodrec (prodrecₙ ⊢C ⊢D ⊢A ⊢t ⊢u _) =
  _ , _ , _ , ⊢C , ⊢D , ⊢A , ⊢t , ⊢u ,
  refl (substType (⊢nf→⊢ ⊢A) (⊢ne∷→⊢∷ ⊢t))
inversion-ne-prodrec (convₙ ⊢pr B≡C) =
  case inversion-ne-prodrec ⊢pr of λ {
    (_ , _ , _ , ⊢C , ⊢D , ⊢A , ⊢t , ⊢u , B≡) →
  _ , _ , _ , ⊢C , ⊢D , ⊢A , ⊢t , ⊢u , trans (sym B≡C) B≡ }

inversion-nf-prodrec :
  Γ ⊢nf prodrec r p q A t u ∷ B →
  ∃₃ λ C D q →
    (Γ ⊢ C) × (Γ ∙ C ⊢ D) ×
    (Γ ∙ (Σᵣ p , q ▷ C ▹ D) ⊢nf A) ×
    Γ ⊢ne t ∷ Σᵣ p , q ▷ C ▹ D ×
    Γ ∙ C ∙ D ⊢nf u ∷ A [ prodᵣ p (var x1) (var x0) ]↑² ×
    Γ ⊢ B ≡ A [ t ]₀
inversion-nf-prodrec (neₙ _ ⊢pr) =
  inversion-ne-prodrec ⊢pr
inversion-nf-prodrec (convₙ ⊢pr B≡C) =
  case inversion-nf-prodrec ⊢pr of λ {
    (_ , _ , _ , ⊢C , ⊢D , ⊢A , ⊢t , ⊢u , B≡) →
  _ , _ , _ , ⊢C , ⊢D , ⊢A , ⊢t , ⊢u , trans (sym B≡C) B≡ }

inversion-nf-ne-prodrec :
  Γ ⊢nf prodrec r p q A t u ∷ B ⊎ Γ ⊢ne prodrec r p q A t u ∷ B →
  ∃₃ λ C D q →
    (Γ ⊢ C) × (Γ ∙ C ⊢ D) ×
    (Γ ∙ (Σᵣ p , q ▷ C ▹ D) ⊢nf A) ×
    Γ ⊢ne t ∷ Σᵣ p , q ▷ C ▹ D ×
    Γ ∙ C ∙ D ⊢nf u ∷ A [ prodᵣ p (var x1) (var x0) ]↑² ×
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
inversion-nf-emptyrec (neₙ _ ⊢er) =
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
inversion-nf-natrec (neₙ _ ⊢nr) =
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

------------------------------------------------------------------------
-- Lemmas related to η-long normal forms for types with η-equality

-- Normal forms of type Π p , q ▷ A ▹ B are not neutral.

⊢nf∷Π→Neutral→⊥ : Γ ⊢nf t ∷ Π p , q ▷ A ▹ B → Neutral t → ⊥
⊢nf∷Π→Neutral→⊥ ⊢t =
  ⊢nf∷Π→Neutral→⊥′ ⊢t (refl (syntacticTerm (⊢nf∷→⊢∷ ⊢t)))
  where
  ⊢nf∷Π→Neutral→⊥′ :
    Γ ⊢nf t ∷ A → Γ ⊢ A ≡ Π p , q ▷ B ▹ C → Neutral t → ⊥
  ⊢nf∷Π→Neutral→⊥′ = λ where
    (convₙ ⊢t B≡A) A≡Σ t-ne →
      ⊢nf∷Π→Neutral→⊥′ ⊢t (trans B≡A A≡Σ) t-ne
    (neₙ A-no-η _) A≡Π _ →
      No-η-equality→≢Π A-no-η A≡Π
    (ΠΣₙ _ _ _)       _ ()
    (lamₙ _ _ _)      _ ()
    (prodₙ _ _ _ _ _) _ ()
    (Emptyₙ _)        _ ()
    (Unitₙ _ _)       _ ()
    (starₙ _ _)       _ ()
    (ℕₙ _)            _ ()
    (zeroₙ _)         _ ()
    (sucₙ _)          _ ()

-- Normal forms of type Σₚ p , q ▷ A ▹ B are not neutral.

⊢nf∷Σₚ→Neutral→⊥ : Γ ⊢nf t ∷ Σₚ p , q ▷ A ▹ B → Neutral t → ⊥
⊢nf∷Σₚ→Neutral→⊥ ⊢t =
  ⊢nf∷Σₚ→Neutral→⊥′ ⊢t (refl (syntacticTerm (⊢nf∷→⊢∷ ⊢t)))
  where
  ⊢nf∷Σₚ→Neutral→⊥′ :
    Γ ⊢nf t ∷ A → Γ ⊢ A ≡ Σₚ p , q ▷ B ▹ C → Neutral t → ⊥
  ⊢nf∷Σₚ→Neutral→⊥′ = λ where
    (convₙ ⊢t B≡A) A≡Σ t-ne →
      ⊢nf∷Σₚ→Neutral→⊥′ ⊢t (trans B≡A A≡Σ) t-ne
    (neₙ A-no-η _) A≡Σ _ →
      No-η-equality→≢Σₚ A-no-η A≡Σ
    (ΠΣₙ _ _ _)       _ ()
    (lamₙ _ _ _)      _ ()
    (prodₙ _ _ _ _ _) _ ()
    (Emptyₙ _)        _ ()
    (Unitₙ _ _)       _ ()
    (starₙ _ _)       _ ()
    (ℕₙ _)            _ ()
    (zeroₙ _)         _ ()
    (sucₙ _)          _ ()

-- Normal forms of type Unit are equal to star.

⊢nf∷Unit→≡star : Γ ⊢nf t ∷ Unit → t PE.≡ star
⊢nf∷Unit→≡star ⊢t =
  ⊢nf∷Unit→≡star′ (refl (syntacticTerm (⊢nf∷→⊢∷ ⊢t))) ⊢t
  where
  ⊢nf∷Unit→≡star′ :
    Γ ⊢ A ≡ Unit → Γ ⊢nf t ∷ A → t PE.≡ star
  ⊢nf∷Unit→≡star′ A≡Unit = λ where
    (starₙ _ _)       → PE.refl
    (convₙ ⊢t ≡A)     → ⊢nf∷Unit→≡star′ (trans ≡A A≡Unit) ⊢t
    (neₙ A-no-η _)    → ⊥-elim (No-η-equality→≢Unit A-no-η A≡Unit)
    (ΠΣₙ _ _ _)       → ⊥-elim (U≢Unitⱼ A≡Unit)
    (lamₙ _ _ _)      → ⊥-elim (Unit≢ΠΣⱼ (sym A≡Unit))
    (prodₙ _ _ _ _ _) → ⊥-elim (Unit≢ΠΣⱼ (sym A≡Unit))
    (Emptyₙ _)        → ⊥-elim (U≢Unitⱼ A≡Unit)
    (Unitₙ _ _)       → ⊥-elim (U≢Unitⱼ A≡Unit)
    (ℕₙ _)            → ⊥-elim (U≢Unitⱼ A≡Unit)
    (zeroₙ _)         → ⊥-elim (ℕ≢Unitⱼ A≡Unit)
    (sucₙ _)          → ⊥-elim (ℕ≢Unitⱼ A≡Unit)

------------------------------------------------------------------------
-- Normal forms (η-long) are unique

mutual

  -- Lemmas used to prove that η-long normal forms are unique.

  normal-types-unique-[conv↑] :
    Γ ⊢nf A → Γ ⊢nf B → Γ ⊢ A [conv↑] B → A PE.≡ B
  normal-types-unique-[conv↑] ⊢A ⊢B ([↑] _ _ A⇒* B⇒* _ _ A≡B) =
    case whnfRed* A⇒* (nfWhnf (⊢nf→Nf ⊢A)) of λ {
      PE.refl →
    case whnfRed* B⇒* (nfWhnf (⊢nf→Nf ⊢B)) of λ {
      PE.refl →
    normal-types-unique-[conv↓] ⊢A ⊢B A≡B }}

  normal-types-unique-[conv↓] :
    Γ ⊢nf A → Γ ⊢nf B → Γ ⊢ A [conv↓] B → A PE.≡ B
  normal-types-unique-[conv↓] ⊢A ⊢B = λ where
    (U-refl _) →
      PE.refl
    (ℕ-refl _) →
      PE.refl
    (Empty-refl _) →
      PE.refl
    (Unit-refl _ _) →
      PE.refl
    (ne A≡B) →
      case syntacticEqTerm (soundness~↓ A≡B) of λ {
        (_ , ⊢A∷U , ⊢B∷U) →
      normal-terms-unique-~↓
        (⊢nf∷U→⊢nf∷U ⊢A ⊢A∷U)
        (⊢nf∷U→⊢nf∷U ⊢B ⊢B∷U)
        A≡B }
    (ΠΣ-cong _ A₁≡B₁ A₂≡B₂ _) →
      case inversion-nf-ΠΣ ⊢A of λ {
        (⊢A₁ , ⊢A₂ , _) →
      case inversion-nf-ΠΣ ⊢B of λ {
        (⊢B₁ , ⊢B₂ , _) →
      PE.cong₂ ΠΣ⟨ _ ⟩ _ , _ ▷_▹_
        (normal-types-unique-[conv↑] ⊢A₁ ⊢B₁ A₁≡B₁)
        (normal-types-unique-[conv↑] ⊢A₂
           (⊢nf-stable
              (reflConEq (wf (⊢nf→⊢ ⊢A)) ∙ sym (soundnessConv↑ A₁≡B₁))
              ⊢B₂)
           A₂≡B₂) }}

  normal-or-neutral-terms-unique-~↑ :
    Γ ⊢nf u ∷ A ⊎ Γ ⊢ne u ∷ A →
    Γ ⊢nf v ∷ B ⊎ Γ ⊢ne v ∷ B →
    Γ ⊢ u ~ v ↑ C → u PE.≡ v
  normal-or-neutral-terms-unique-~↑ ⊢u ⊢v = λ where
    (var-refl _ PE.refl) →
      PE.refl
    (app-cong t≡v u≡w) →
      case inversion-nf-ne-app ⊢u of λ {
        (_ , _ , _ , ⊢t , ⊢u , _) →
      case inversion-nf-ne-app ⊢v of λ {
        (_ , _ , _ , ⊢v , ⊢w , _) →
      case syntacticEqTerm (soundness~↓ t≡v) .proj₂ of λ {
        (⊢t′ , ⊢v′) →
      case nfNeutral (⊢ne∷→NfNeutral ⊢t) of λ {
        t-ne →
      case nfNeutral (⊢ne∷→NfNeutral ⊢v) of λ {
        v-ne →
      case ΠΣ-injectivity (neTypeEq t-ne (⊢ne∷→⊢∷ ⊢t) ⊢t′) of λ {
        (A≡ , _) →
      case ΠΣ-injectivity (neTypeEq v-ne (⊢ne∷→⊢∷ ⊢v) ⊢v′) of λ {
        (C≡ , _) →
      PE.cong₂ _∘⟨ _ ⟩_
        (neutral-terms-unique-~↓ ⊢t ⊢v t≡v)
        (normal-terms-unique-[conv↑]∷
           (convₙ ⊢u A≡) (convₙ ⊢w C≡) u≡w) }}}}}}}
    (fst-cong u≡v) →
      case inversion-nf-ne-fst ⊢u of λ {
        (_ , _ , _ , _ , _ , ⊢u , _) →
      case inversion-nf-ne-fst ⊢v of λ {
        (_ , _ , _ , _ , _ , ⊢v , _) →
      PE.cong (fst _) (neutral-terms-unique-~↓ ⊢u ⊢v u≡v) }}
    (snd-cong u≡v) →
      case inversion-nf-ne-snd ⊢u of λ {
        (_ , _ , _ , _ , _ , ⊢u , _) →
      case inversion-nf-ne-snd ⊢v of λ {
        (_ , _ , _ , _ , _ , ⊢v , _) →
      PE.cong (snd _) (neutral-terms-unique-~↓ ⊢u ⊢v u≡v) }}
    (natrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) →
      case inversion-nf-ne-natrec ⊢u of λ {
        (⊢A₁ , ⊢t₁ , ⊢u₁ , ⊢v₁ , _) →
      case inversion-nf-ne-natrec ⊢v of λ {
        (⊢A₂ , ⊢t₂ , ⊢u₂ , ⊢v₂ , _) →
      case normal-types-unique-[conv↑] ⊢A₁ ⊢A₂ A₁≡A₂ of λ {
        PE.refl →
      PE.cong₂
        (λ t ((u , v) : _ × _) → natrec _ _ _ _ t u v)
        (normal-terms-unique-[conv↑]∷ ⊢t₁ ⊢t₂ t₁≡t₂)
        (PE.cong₂ _,_
           (normal-terms-unique-[conv↑]∷ ⊢u₁ ⊢u₂ u₁≡u₂)
           (neutral-terms-unique-~↓ ⊢v₁ ⊢v₂ v₁≡v₂)) }}}
    (prodrec-cong A≡B t≡u v≡w) →
      case inversion-nf-ne-prodrec ⊢u of λ {
        (_ , _ , _ , ⊢C , _ , ⊢A , ⊢t , ⊢v′ , _) →
      case inversion-nf-ne-prodrec ⊢v of λ {
        (_ , _ , _ , ⊢E , _ , ⊢B , ⊢u , ⊢w , _) →
      case syntacticEqTerm (soundness~↓ t≡u) .proj₂ of λ {
        (⊢t′ , ⊢u′) →
      case nfNeutral (⊢ne∷→NfNeutral ⊢t) of λ {
        t-ne →
      case nfNeutral (⊢ne∷→NfNeutral ⊢u) of λ {
        u-ne →
      case ΠΣ-injectivity (neTypeEq t-ne (⊢ne∷→⊢∷ ⊢t) ⊢t′) of λ {
        (C≡ , D≡ , _ , PE.refl , _) →
      case ΠΣ-injectivity (neTypeEq u-ne (⊢ne∷→⊢∷ ⊢u) ⊢u′) of λ {
        (E≡ , F≡ , _ , PE.refl , _) →
      case reflConEq (wfTerm ⊢t′) of λ {
        Γ≡Γ →
      case ⊢∷ΠΣ→ΠΣ-allowed (⊢ne∷→⊢∷ ⊢t) of λ {
        ok →
      case
        normal-types-unique-[conv↑]
          (⊢nf-stable (Γ≡Γ ∙ ΠΣ-cong ⊢C C≡ D≡ ok) ⊢A)
          (⊢nf-stable (Γ≡Γ ∙ ΠΣ-cong ⊢E E≡ F≡ ok) ⊢B)
          A≡B of λ {
        PE.refl →
      PE.cong₂ (prodrec _ _ _ _)
        (neutral-terms-unique-~↓ ⊢t ⊢u t≡u)
        (normal-terms-unique-[conv↑]∷
           (⊢nf∷-stable (Γ≡Γ ∙ C≡ ∙ D≡) ⊢v′)
           (⊢nf∷-stable (Γ≡Γ ∙ E≡ ∙ F≡) ⊢w)
           v≡w) }}}}}}}}}}
    (emptyrec-cong A≡B u≡v) →
      case inversion-nf-ne-emptyrec ⊢u of λ {
        (⊢A , ⊢u , _) →
      case inversion-nf-ne-emptyrec ⊢v of λ {
        (⊢B , ⊢v , _) →
      PE.cong₂ (emptyrec _)
        (normal-types-unique-[conv↑] ⊢A ⊢B A≡B)
        (neutral-terms-unique-~↓ ⊢u ⊢v u≡v) }}

  neutral-terms-unique-~↑ :
    Γ ⊢ne u ∷ A → Γ ⊢ne v ∷ B → Γ ⊢ u ~ v ↑ C → u PE.≡ v
  neutral-terms-unique-~↑ ⊢u ⊢v u≡v =
    normal-or-neutral-terms-unique-~↑ (inj₂ ⊢u) (inj₂ ⊢v) u≡v

  normal-terms-unique-~↑ :
    Γ ⊢nf u ∷ A → Γ ⊢nf v ∷ B → Γ ⊢ u ~ v ↑ C → u PE.≡ v
  normal-terms-unique-~↑ ⊢u ⊢v u≡v =
    normal-or-neutral-terms-unique-~↑ (inj₁ ⊢u) (inj₁ ⊢v) u≡v

  normal-terms-unique-~↓ :
    Γ ⊢nf u ∷ A → Γ ⊢nf v ∷ B → Γ ⊢ u ~ v ↓ C → u PE.≡ v
  normal-terms-unique-~↓ ⊢u ⊢v ([~] _ _ _ u≡v) =
    normal-terms-unique-~↑ ⊢u ⊢v u≡v

  neutral-terms-unique-~↓ :
    Γ ⊢ne u ∷ A → Γ ⊢ne v ∷ B → Γ ⊢ u ~ v ↓ C → u PE.≡ v
  neutral-terms-unique-~↓ ⊢u ⊢v ([~] _ _ _ u≡v) =
    neutral-terms-unique-~↑ ⊢u ⊢v u≡v

  normal-terms-unique-[conv↓]∷ :
    Γ ⊢nf u ∷ A → Γ ⊢nf v ∷ A → Γ ⊢ u [conv↓] v ∷ A → u PE.≡ v
  normal-terms-unique-[conv↓]∷ ⊢u ⊢v = λ where
    (ℕ-ins u≡v) →
      normal-terms-unique-~↓ ⊢u ⊢v u≡v
    (Empty-ins u≡v) →
      normal-terms-unique-~↓ ⊢u ⊢v u≡v
    (Unit-ins u≡v) →
      normal-terms-unique-~↓ ⊢u ⊢v u≡v
    (Σᵣ-ins _ _ u≡v) →
      normal-terms-unique-~↓ ⊢u ⊢v u≡v
    (ne-ins _ _ _ u≡v) →
      normal-terms-unique-~↓ ⊢u ⊢v u≡v
    (univ _ _ u≡v) →
      normal-types-unique-[conv↓] (univₙ ⊢u) (univₙ ⊢v) u≡v
    (zero-refl _) →
      PE.refl
    (suc-cong u≡v) →
      case inversion-nf-suc ⊢u of λ {
        (⊢u , _) →
      case inversion-nf-suc ⊢v of λ {
        (⊢v , _) →
      PE.cong suc (normal-terms-unique-[conv↑]∷ ⊢u ⊢v u≡v) }}
    (prod-cong _ _ t≡v u≡w _) →
      case inversion-nf-prod ⊢u of λ {
        (_ , _ , _ , _ , _ , ⊢t , ⊢u , Σ≡Σ₁ , _) →
      case inversion-nf-prod ⊢v of λ {
        (_ , _ , _ , _ , _ , ⊢v , ⊢w , Σ≡Σ₂ , _) →
      case ΠΣ-injectivity Σ≡Σ₁ of λ {
        (B≡₁ , C≡₁ , _) →
      case ΠΣ-injectivity Σ≡Σ₂ of λ {
        (B≡₂ , C≡₂ , _) →
      case convₙ ⊢t (sym B≡₁) of λ {
        ⊢t →
      PE.cong₂ (prodᵣ _)
        (normal-terms-unique-[conv↑]∷ ⊢t (convₙ ⊢v (sym B≡₂)) t≡v)
        (normal-terms-unique-[conv↑]∷
           (convₙ ⊢u (sym (substTypeEq C≡₁ (refl (⊢nf∷→⊢∷ ⊢t)))))
           (convₙ ⊢w (sym (substTypeEq C≡₂ (soundnessConv↑Term t≡v))))
           u≡w) }}}}}
    λ≡λ@(η-eq ⊢λu ⊢λv lamₙ lamₙ u∘0≡v∘0) →
      case lam-injective (soundnessConv↓Term λ≡λ) of λ {
        (PE.refl , _ , _ , PE.refl) →
      case inversion-nf-lam ⊢u of λ {
        (_ , _ , _ , ⊢B , ⊢u , Π≡₁ , _) →
      case inversion-nf-lam ⊢v of λ {
        (_ , _ , _ , ⊢D , ⊢v , Π≡₂ , _) →
      case ΠΣ-injectivity (sym Π≡₁) of λ {
        (B≡ , C≡ , _ , _ , _) →
      case ΠΣ-injectivity (sym Π≡₂) of λ {
        (D≡ , E≡ , _ , _ , _) →
      PE.cong (lam _)
        (normal-terms-unique-[conv↑]∷′
           (⊢nf∷-stable (reflConEq (wf ⊢B) ∙ B≡) (convₙ ⊢u C≡))
           (⊢nf∷-stable (reflConEq (wf ⊢D) ∙ D≡) (convₙ ⊢v E≡))
           (redMany (wk1-lam∘0⇒ ⊢λu))
           (redMany (wk1-lam∘0⇒ ⊢λv))
           u∘0≡v∘0) }}}}}
    (η-eq _ _ (ne u-ne) _ _) →
      ⊥-elim (⊢nf∷Π→Neutral→⊥ ⊢u u-ne)
    (η-eq _ _ _ (ne v-ne) _) →
      ⊥-elim (⊢nf∷Π→Neutral→⊥ ⊢v v-ne)
    ,≡,@(Σ-η _ _ prodₙ prodₙ fst≡fst snd≡snd) →
      case inversion-nf-prod ⊢u of λ {
        (_ , _ , _ , ⊢B , ⊢C , ⊢t , ⊢u , Σ≡₁ , ok₁) →
      case inversion-nf-prod ⊢v of λ {
        (_ , _ , _ , ⊢D , ⊢E , ⊢v , ⊢w , Σ≡₂ , ok₂) →
      case ΠΣ-injectivity (sym Σ≡₁) of λ {
        (B≡ , C≡ , PE.refl , _ , PE.refl) →
      case ΠΣ-injectivity (sym Σ≡₂) of λ {
        (D≡ , E≡ , PE.refl , _ , PE.refl) →
      case Σ-β₁ ⊢B ⊢C (⊢nf∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢u) PE.refl ok₁ of λ {
        fst-t,u⇒t →
      case trans B≡ (sym D≡) of λ {
        B≡D →
      case
        normal-terms-unique-[conv↑]∷′
          (convₙ ⊢t B≡)
          (convₙ ⊢v D≡)
          (redMany (conv fst-t,u⇒t B≡))
          (redMany
             (conv (Σ-β₁ ⊢D ⊢E (⊢nf∷→⊢∷ ⊢v) (⊢nf∷→⊢∷ ⊢w) PE.refl ok₂)
                D≡))
          fst≡fst of λ {
        PE.refl →
      PE.cong (prod _ _ _)
        (normal-terms-unique-[conv↑]∷′
           (convₙ ⊢u (substTypeEq C≡ (sym (subsetTerm fst-t,u⇒t))))
           (convₙ ⊢w
              (substTypeEq E≡
                 (conv (sym (subsetTerm fst-t,u⇒t)) B≡D)))
           (redMany
              (conv (Σ-β₂ ⊢B ⊢C (⊢nf∷→⊢∷ ⊢t) (⊢nf∷→⊢∷ ⊢u) PE.refl ok₁)
                 (substTypeEq C≡ (refl (redFirstTerm fst-t,u⇒t)))))
           (redMany
              (conv (Σ-β₂ ⊢D ⊢E (⊢nf∷→⊢∷ ⊢v) (⊢nf∷→⊢∷ ⊢w) PE.refl ok₂)
                 (substTypeEq E≡
                    (fst-cong ⊢D ⊢E
                       (sym (conv (soundnessConv↓Term ,≡,) Σ≡₂))))))
           snd≡snd) }}}}}}}
    (Σ-η _ _ (ne u-ne) _ _ _) →
      ⊥-elim (⊢nf∷Σₚ→Neutral→⊥ ⊢u u-ne)
    (Σ-η _ _ _ (ne v-ne) _ _) →
      ⊥-elim (⊢nf∷Σₚ→Neutral→⊥ ⊢v v-ne)
    (η-unit _ _ _ _) →
      case ⊢nf∷Unit→≡star ⊢u of λ {
        PE.refl →
      case ⊢nf∷Unit→≡star ⊢v of λ {
        PE.refl →
      PE.refl }}

  normal-terms-unique-[conv↑]∷ :
    Γ ⊢nf u ∷ A → Γ ⊢nf v ∷ A → Γ ⊢ u [conv↑] v ∷ A → u PE.≡ v
  normal-terms-unique-[conv↑]∷ ⊢u ⊢v u≡v =
    normal-terms-unique-[conv↑]∷′
      ⊢u ⊢v (id (⊢nf∷→⊢∷ ⊢u)) (id (⊢nf∷→⊢∷ ⊢v)) u≡v

  normal-terms-unique-[conv↑]∷′ :
    Γ ⊢nf u ∷ A → Γ ⊢nf w ∷ A →
    Γ ⊢ t ⇒* u ∷ A → Γ ⊢ v ⇒* w ∷ A →
    Γ ⊢ t [conv↑] v ∷ A → u PE.≡ w
  normal-terms-unique-[conv↑]∷′
    ⊢u ⊢w t⇒*u v⇒*w
    ([↑]ₜ _ _ _ A⇒*B t⇒*t′ v⇒*v′ _ t′-whnf  v′-whnf u≡w) =
    case whrDet*Term (t⇒*u , nfWhnf (⊢nf∷→Nf ⊢u))
           (t⇒*t′ , t′-whnf) of λ {
      PE.refl →
    case whrDet*Term (v⇒*w , nfWhnf (⊢nf∷→Nf ⊢w))
           (v⇒*v′ , v′-whnf) of λ {
      PE.refl →
    case subset* A⇒*B of λ {
      A≡B →
    normal-terms-unique-[conv↓]∷ (convₙ ⊢u A≡B) (convₙ ⊢w A≡B) u≡w }}}

-- Normal types are unique (definitionally equal η-long normal types
-- are equal).

normal-types-unique :
  Γ ⊢nf A → Γ ⊢nf B → Γ ⊢ A ≡ B → A PE.≡ B
normal-types-unique ⊢A ⊢B A≡B =
  normal-types-unique-[conv↑] ⊢A ⊢B (completeEq A≡B)

-- Normal terms are unique (definitionally equal η-long normal terms
-- are equal).

normal-terms-unique :
  Γ ⊢nf u ∷ A → Γ ⊢nf v ∷ A → Γ ⊢ u ≡ v ∷ A → u PE.≡ v
normal-terms-unique ⊢u ⊢v u≡v =
  normal-terms-unique-[conv↑]∷ ⊢u ⊢v (completeEqTerm u≡v)
