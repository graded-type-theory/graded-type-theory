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
open import Definition.Typed.Consequences.Inequality R as TI
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.Typed.Properties R

open import Definition.Untyped M hiding (_∷_)

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)

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
-- Some lemmas related to No-η-equality

-- If No-η-equality A holds, then A is a WHNF.

No-η-equality→Whnf : No-η-equality A → Whnf A
No-η-equality→Whnf = λ where
  Uₙ      → Uₙ
  Σᵣₙ     → ΠΣₙ
  Emptyₙ  → Emptyₙ
  ℕₙ      → ℕₙ
  (neₙ n) → ne n

-- If No-η-equality A holds, then A is not a Π-type.

No-η-equality→≢Π : No-η-equality A → Γ ⊢ A ≡ Π p , q ▷ B ▹ C → ⊥
No-η-equality→≢Π = λ where
  Uₙ         U≡Π     → U≢ΠΣⱼ U≡Π
  Σᵣₙ        Σᵣ≡Π    → Π≢Σⱼ (sym Σᵣ≡Π)
  Emptyₙ     Empty≡Π → Empty≢ΠΣⱼ Empty≡Π
  ℕₙ         ℕ≡Π     → ℕ≢ΠΣⱼ ℕ≡Π
  (neₙ A-ne) A≡Π     → TI.ΠΣ≢ne A-ne (sym A≡Π)

-- If No-η-equality A holds, then A is not a Σ-type with η-equality.

No-η-equality→≢Σₚ : No-η-equality A → Γ ⊢ A ≡ Σₚ p , q ▷ B ▹ C → ⊥
No-η-equality→≢Σₚ = λ where
  Uₙ         U≡Σ     → U≢ΠΣⱼ U≡Σ
  Σᵣₙ        Σᵣ≡Σ    → Σₚ≢Σᵣⱼ (sym Σᵣ≡Σ)
  Emptyₙ     Empty≡Σ → Empty≢ΠΣⱼ Empty≡Σ
  ℕₙ         ℕ≡Σ     → ℕ≢ΠΣⱼ ℕ≡Σ
  (neₙ A-ne) A≡Σ     → TI.ΠΣ≢ne A-ne (sym A≡Σ)

-- If No-η-equality A holds, then A is not the unit type with
-- η-equality.

No-η-equality→≢Unit : No-η-equality A → Γ ⊢ A ≡ Unit → ⊥
No-η-equality→≢Unit = λ where
  Uₙ         U≡Unit     → U≢Unitⱼ U≡Unit
  Σᵣₙ        Σᵣ≡Unit    → Unit≢ΠΣⱼ (sym Σᵣ≡Unit)
  Emptyₙ     Empty≡Unit → Empty≢Unitⱼ Empty≡Unit
  ℕₙ         ℕ≡Unit     → ℕ≢Unitⱼ ℕ≡Unit
  (neₙ A-ne) A≡Unit     → TI.Unit≢neⱼ A-ne (sym A≡Unit)

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

------------------------------------------------------------------------
-- Inversion lemmas

-- Inversion for terms that are Π- or Σ-types.

inversion-nf-ΠΣ-U :
  Γ ⊢nf ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ C →
  Γ ⊢nf A ∷ U × Γ ∙ A ⊢nf B ∷ U × Γ ⊢ C ≡ U × ΠΣ-restriction b p q
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
  Γ ⊢nf A × Γ ∙ A ⊢nf B × ΠΣ-restriction b p q
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
     Π-restriction p q
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
    Γ ⊢nf t ∷ B × Γ ⊢nf u ∷ C [ t ] ×
    Γ ⊢ A ≡ Σ⟨ s ⟩ p , q ▷ B ▹ C ×
    Σ-restriction s p q
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
     Γ ⊢ne t ∷ Π p , q ▷ B ▹ C × Γ ⊢nf u ∷ B × Γ ⊢ A ≡ C [ u ]
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
     Γ ⊢ne t ∷ Π p , q ▷ B ▹ C × Γ ⊢nf u ∷ B × Γ ⊢ A ≡ C [ u ]
inversion-nf-app (neₙ _ ⊢app) =
  inversion-ne-app ⊢app
inversion-nf-app (convₙ ⊢app A≡B) =
  case inversion-nf-app ⊢app of λ {
    (_ , _ , _ , ⊢t , ⊢u , A≡) →
  _ , _ , _ , ⊢t , ⊢u , trans (sym A≡B) A≡ }

inversion-nf-ne-app :
  Γ ⊢nf t ∘⟨ p ⟩ u ∷ A ⊎ Γ ⊢ne t ∘⟨ p ⟩ u ∷ A →
  ∃₃ λ B C q →
     Γ ⊢ne t ∷ Π p , q ▷ B ▹ C × Γ ⊢nf u ∷ B × Γ ⊢ A ≡ C [ u ]
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
     Γ ⊢ A ≡ C [ fst p t ]
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
     Γ ⊢ A ≡ C [ fst p t ]
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
     Γ ⊢ A ≡ C [ fst p t ]
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
    Γ ⊢ B ≡ A [ t ]
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
    Γ ⊢ B ≡ A [ t ]
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
    Γ ⊢ B ≡ A [ t ]
inversion-nf-ne-prodrec (inj₁ ⊢pr) = inversion-nf-prodrec ⊢pr
inversion-nf-ne-prodrec (inj₂ ⊢pr) = inversion-ne-prodrec ⊢pr

-- Inversion for Emptyrec.

inversion-ne-Emptyrec :
  Γ ⊢ne Emptyrec p A t ∷ B →
  Γ ⊢nf A × Γ ⊢ne t ∷ Empty × Γ ⊢ B ≡ A
inversion-ne-Emptyrec (Emptyrecₙ ⊢A ⊢t) =
  ⊢A , ⊢t , refl (⊢nf→⊢ ⊢A)
inversion-ne-Emptyrec (convₙ ⊢er A≡B) =
  case inversion-ne-Emptyrec ⊢er of λ {
    (⊢A , ⊢t , A≡) →
  ⊢A , ⊢t , trans (sym A≡B) A≡ }

inversion-nf-Emptyrec :
  Γ ⊢nf Emptyrec p A t ∷ B →
  Γ ⊢nf A × Γ ⊢ne t ∷ Empty × Γ ⊢ B ≡ A
inversion-nf-Emptyrec (neₙ _ ⊢er) =
  inversion-ne-Emptyrec ⊢er
inversion-nf-Emptyrec (convₙ ⊢er A≡B) =
  case inversion-nf-Emptyrec ⊢er of λ {
    (⊢A , ⊢t , A≡) →
  ⊢A , ⊢t , trans (sym A≡B) A≡ }

inversion-nf-ne-Emptyrec :
  Γ ⊢nf Emptyrec p A t ∷ B ⊎ Γ ⊢ne Emptyrec p A t ∷ B →
  Γ ⊢nf A × Γ ⊢ne t ∷ Empty × Γ ⊢ B ≡ A
inversion-nf-ne-Emptyrec (inj₁ ⊢er) = inversion-nf-Emptyrec ⊢er
inversion-nf-ne-Emptyrec (inj₂ ⊢er) = inversion-ne-Emptyrec ⊢er

-- Inversion for natrec.

inversion-ne-natrec :
  Γ ⊢ne natrec p q r A t u v ∷ B →
  (Γ ∙ ℕ ⊢nf A) ×
  Γ ⊢nf t ∷ A [ zero ] ×
  Γ ∙ ℕ ∙ A ⊢nf u ∷ A [ suc (var x1) ]↑² ×
  Γ ⊢ne v ∷ ℕ ×
  Γ ⊢ B ≡ A [ v ]
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
  Γ ⊢nf t ∷ A [ zero ] ×
  Γ ∙ ℕ ∙ A ⊢nf u ∷ A [ suc (var x1) ]↑² ×
  Γ ⊢ne v ∷ ℕ ×
  Γ ⊢ B ≡ A [ v ]
inversion-nf-natrec (neₙ _ ⊢nr) =
  inversion-ne-natrec ⊢nr
inversion-nf-natrec (convₙ ⊢pr B≡C) =
  case inversion-nf-natrec ⊢pr of λ {
    (⊢A , ⊢t , ⊢u , ⊢v , B≡) →
  ⊢A , ⊢t , ⊢u , ⊢v , trans (sym B≡C) B≡ }

inversion-nf-ne-natrec :
  Γ ⊢nf natrec p q r A t u v ∷ B ⊎ Γ ⊢ne natrec p q r A t u v ∷ B →
  (Γ ∙ ℕ ⊢nf A) ×
  Γ ⊢nf t ∷ A [ zero ] ×
  Γ ∙ ℕ ∙ A ⊢nf u ∷ A [ suc (var x1) ]↑² ×
  Γ ⊢ne v ∷ ℕ ×
  Γ ⊢ B ≡ A [ v ]
inversion-nf-ne-natrec (inj₁ ⊢nr) = inversion-nf-natrec ⊢nr
inversion-nf-ne-natrec (inj₂ ⊢nr) = inversion-ne-natrec ⊢nr
