------------------------------------------------------------------------
-- Eta-long normal forms
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Eta-long-normal-form
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open Type-restrictions R

open import Definition.Conversion.FullReduction R
  using (NfNeutral; Nf)
open import Definition.Conversion.Stability R

open NfNeutral
open Nf

open import Definition.Typed R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Properties R

open import Definition.Untyped M hiding (_∷_)

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product

private variable
  n           : Nat
  x           : Fin _
  Γ Δ         : Con _ _
  A B C t u v : Term _
  b           : BinderMode
  s           : SigmaMode
  p q q′ r    : M

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
             ΠΣ-restriction b p q →
             Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
    Emptyₙ : ⊢ Γ →
             Γ ⊢nf Empty
    Unitₙ  : ⊢ Γ →
             Unit-restriction →
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
             ΠΣ-restriction b p q →
             Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U
    lamₙ   : Γ ⊢ A →
             Γ ∙ A ⊢nf t ∷ B →
             Π-restriction p q →
             Γ ⊢nf lam p t ∷ Π p , q ▷ A ▹ B
    prodₙ  : Γ ⊢ A →
             Γ ∙ A ⊢ B →
             Γ ⊢nf t ∷ A →
             Γ ⊢nf u ∷ B [ t ] →
             Σ-restriction s p q →
             Γ ⊢nf prod s p t u ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B
    Emptyₙ : ⊢ Γ →
             Γ ⊢nf Empty ∷ U
    Unitₙ  : ⊢ Γ →
             Unit-restriction →
             Γ ⊢nf Unit ∷ U
    starₙ  : ⊢ Γ →
             Unit-restriction →
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
                Γ ∙ A ∙ B ⊢nf u ∷ C [ prodᵣ p (var x1) (var x0) ]↑² →
                Σᵣ-restriction p q′ →
                Γ ⊢ne prodrec r p q C t u ∷ C [ t ]
    Emptyrecₙ : Γ ⊢nf A →
                Γ ⊢ne t ∷ Empty →
                Γ ⊢ne Emptyrec p A t ∷ A
    natrecₙ   : Γ ∙ ℕ ⊢nf A →
                Γ ⊢nf t ∷ A [ zero ] →
                Γ ∙ ℕ ∙ A ⊢nf u ∷ A [ suc (var x1) ]↑² →
                Γ ⊢ne v ∷ ℕ →
                Γ ⊢ne natrec p q r A t u v ∷ A [ v ]

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

-- If No-η-equality A holds, then A is a WHNF.

No-η-equality→Whnf : No-η-equality A → Whnf A
No-η-equality→Whnf = λ where
  Uₙ      → Uₙ
  Σᵣₙ     → ΠΣₙ
  Emptyₙ  → Emptyₙ
  ℕₙ      → ℕₙ
  (neₙ n) → ne n

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
    (Emptyrecₙ ⊢A ⊢t)            → Emptyrecⱼ (⊢nf→⊢ ⊢A) (⊢ne∷→⊢∷ ⊢t)
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
    (Emptyrecₙ ⊢A ⊢t)         → Emptyrecₙ (⊢nf→Nf ⊢A)
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
