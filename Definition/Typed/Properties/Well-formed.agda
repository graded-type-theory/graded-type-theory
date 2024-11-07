------------------------------------------------------------------------
-- Some lemmas that are re-exported from Definition.Typed.Properties
------------------------------------------------------------------------

-- This module is imported from Graded.Derived.Erased.Typed.Primitive,
-- which is imported from Definition.Typed.Properties.

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Well-formed
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.Typed.Size R

open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.Size

private variable
  Γ           : Con Term _
  A B C D t u : Term _
  l           : Nat
  s₁ s₂       : Size

------------------------------------------------------------------------
-- Context well-formedness lemmas

opaque
  unfolding size-⊢′

  -- If there is a proof of ⊢ Γ ∙ A, then there are strictly smaller
  -- proofs of ⊢ Γ and Γ ⊢ A.

  ⊢∙→⊢-<ˢ :
    (⊢Γ∙A : ⊢ Γ ∙ A) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢′ ⊢Γ∙A) ×
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢′ ⊢Γ∙A)
  ⊢∙→⊢-<ˢ (⊢Γ ∙ ⊢A) = (⊢Γ , ↙ ◻) , (⊢A , ↘ ◻)

private opaque

  -- A lemma used below.

  fix :
    s₁ ≤ˢ s₂ →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ s₁) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ s₂)
  fix s₁≤ˢs₂ = Σ.map idᶠ (flip <ˢ-trans-≤ˢʳ s₁≤ˢs₂)

opaque
  unfolding size-⊢′

  mutual

    -- If there is a proof of type Γ ⊢ A, then there is a strictly
    -- smaller proof of type ⊢ Γ.

    wf-<ˢ : (⊢A : Γ ⊢ A) → ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢ ⊢A
    wf-<ˢ (Uⱼ ⊢Γ)      = ⊢Γ , ↙ ◻
    wf-<ˢ (univ A)     = fix (↙ ◻) (wfTerm-<ˢ A)
    wf-<ˢ (ΠΣⱼ ⊢B _)   = fix (↙ ◻) (∙⊢→⊢-<ˢ ⊢B .proj₁)
    wf-<ˢ (Emptyⱼ ⊢Γ)  = ⊢Γ , ↙ ◻
    wf-<ˢ (Unitⱼ ⊢Γ _) = ⊢Γ , ↙ ◻
    wf-<ˢ (ℕⱼ ⊢Γ)      = ⊢Γ , ↙ ◻
    wf-<ˢ (Idⱼ ⊢t _)   = fix (↙ ◻) (wfTerm-<ˢ ⊢t)

    -- If there is a proof of type Γ ⊢ t ∷ A, then there is a strictly
    -- smaller proof of type ⊢ Γ.

    wfTerm-<ˢ :
      (⊢t : Γ ⊢ t ∷ A) → ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢∷ ⊢t
    wfTerm-<ˢ (conv ⊢t _)          = fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ (var ⊢Γ _)           = ⊢Γ , ↙ ◻
    wfTerm-<ˢ (Uⱼ ⊢Γ)              = ⊢Γ , ↙ ◻
    wfTerm-<ˢ (ΠΣⱼ ⊢A _ _)         = fix (↙ ◻) (wfTerm-<ˢ ⊢A)
    wfTerm-<ˢ (lamⱼ ⊢t _)          = fix (↙ ◻) (∙⊢∷→⊢-<ˢ ⊢t .proj₁)
    wfTerm-<ˢ (⊢t ∘ⱼ _)            = fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ (prodⱼ _ ⊢t _ _)     = fix (↘ ↙ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ (fstⱼ _ ⊢t)          = fix (↘ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ (sndⱼ _ ⊢t)          = fix (↘ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ (prodrecⱼ _ ⊢t _ _)  = fix (↘ ↙ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ (Emptyⱼ ⊢Γ)          = ⊢Γ , ↙ ◻
    wfTerm-<ˢ (emptyrecⱼ ⊢A _)     = fix (↙ ◻) (wf-<ˢ ⊢A)
    wfTerm-<ˢ (Unitⱼ ⊢Γ _)         = ⊢Γ , ↙ ◻
    wfTerm-<ˢ (starⱼ ⊢Γ _)         = ⊢Γ , ↙ ◻
    wfTerm-<ˢ (unitrecⱼ ⊢A ⊢t _ _) = fix (↘ ↙ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ (ℕⱼ ⊢Γ)              = ⊢Γ , ↙ ◻
    wfTerm-<ˢ (zeroⱼ ⊢Γ)           = ⊢Γ , ↙ ◻
    wfTerm-<ˢ (sucⱼ n)             = fix (↙ ◻) (wfTerm-<ˢ n)
    wfTerm-<ˢ (natrecⱼ ⊢t _ _)     = fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ (Idⱼ ⊢A _ _)         = fix (↙ ◻) (wfTerm-<ˢ ⊢A)
    wfTerm-<ˢ (rflⱼ ⊢t)            = fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ (Jⱼ ⊢t _ _ _ _)      = fix (↙ ↙ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ (Kⱼ ⊢t _ _ _ _)      = fix (↙ ↙ ◻) (wfTerm-<ˢ ⊢t)
    wfTerm-<ˢ ([]-congⱼ ⊢t _ _ _)  = fix (↙ ◻) (wfTerm-<ˢ ⊢t)

    -- If there is a proof of Γ ∙ A ⊢ B, then there are strictly
    -- smaller proofs of ⊢ Γ and Γ ⊢ A.

    ∙⊢→⊢-<ˢ :
      (⊢B : Γ ∙ A ⊢ B) →
      (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢ ⊢B) ×
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢ ⊢B)
    ∙⊢→⊢-<ˢ ⊢B =
      let ⊢Γ∙A , p            = wf-<ˢ ⊢B
          (⊢Γ , q) , (⊢A , r) = ⊢∙→⊢-<ˢ ⊢Γ∙A
      in
      (⊢Γ , <ˢ-trans q p) , (⊢A , <ˢ-trans r p)

    -- If there is a proof of Γ ∙ A ⊢ t ∷ B, then there are strictly
    -- smaller proofs of ⊢ Γ and Γ ⊢ A.

    ∙⊢∷→⊢-<ˢ :
      (⊢t : Γ ∙ A ⊢ t ∷ B) →
      (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢∷ ⊢t) ×
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢∷ ⊢t)
    ∙⊢∷→⊢-<ˢ ⊢t =
      let ⊢Γ∙A , p            = wfTerm-<ˢ ⊢t
          (⊢Γ , q) , (⊢A , r) = ⊢∙→⊢-<ˢ ⊢Γ∙A
      in
      (⊢Γ , <ˢ-trans q p) , (⊢A , <ˢ-trans r p)

opaque
  unfolding size-⊢′

  mutual

    -- If there is a proof of type Γ ⊢ A ≡ B, then there is a strictly
    -- smaller proof of type ⊢ Γ.

    wfEq-<ˢ :
      (A≡B : Γ ⊢ A ≡ B) → ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢≡ A≡B
    wfEq-<ˢ (univ A≡B)          = fix (↙ ◻) (wfEqTerm-<ˢ A≡B)
    wfEq-<ˢ (refl ⊢A)           = fix (↙ ◻) (wf-<ˢ ⊢A)
    wfEq-<ˢ (sym B≡A)           = fix (↙ ◻) (wfEq-<ˢ B≡A)
    wfEq-<ˢ (trans A≡B B≡C)     = fix (↙ ◻) (wfEq-<ˢ A≡B)
    wfEq-<ˢ (ΠΣ-cong A₁≡B₁ _ _) = fix (↙ ◻) (wfEq-<ˢ A₁≡B₁)
    wfEq-<ˢ (Id-cong A≡B _ _)   = fix (↙ ◻) (wfEq-<ˢ A≡B)

    -- If there is a proof of type Γ ⊢ t ≡ u ∷ A, then there is a
    -- strictly smaller proof of type ⊢ Γ.

    wfEqTerm-<ˢ :
      (t≡u : Γ ⊢ t ≡ u ∷ A) →
      ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢≡∷ t≡u
    wfEqTerm-<ˢ (refl ⊢t) =
      fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (sym u≡t) =
      fix (↙ ◻) (wfEqTerm-<ˢ u≡t)
    wfEqTerm-<ˢ (trans t≡u _) =
      fix (↙ ◻) (wfEqTerm-<ˢ t≡u)
    wfEqTerm-<ˢ (conv t≡u _) =
      fix (↙ ◻) (wfEqTerm-<ˢ t≡u)
    wfEqTerm-<ˢ (ΠΣ-cong A≡B _ _) =
      fix (↙ ◻) (wfEqTerm-<ˢ A≡B)
    wfEqTerm-<ˢ (app-cong t₁≡u₁ _) =
      fix (↙ ◻) (wfEqTerm-<ˢ t₁≡u₁)
    wfEqTerm-<ˢ (β-red _ _ ⊢u _ _) =
      fix (↘ ↘ ◻) (wfTerm-<ˢ ⊢u)
    wfEqTerm-<ˢ (η-eq ⊢t _ _) =
      fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (fst-cong _ t≡u) =
      fix (↘ ◻) (wfEqTerm-<ˢ t≡u)
    wfEqTerm-<ˢ (snd-cong _ t≡u) =
      fix (↘ ◻) (wfEqTerm-<ˢ t≡u)
    wfEqTerm-<ˢ (Σ-β₁ _ ⊢t _ _ _) =
      fix (↘ ↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (Σ-β₂ _ ⊢t _ _ _) =
      fix (↘ ↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (Σ-η _ ⊢t _ _ _) =
      fix (↙ ↘ ↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (prod-cong _ t₁≡u₁ _ _) =
      fix (↘ ↙ ◻) (wfEqTerm-<ˢ t₁≡u₁)
    wfEqTerm-<ˢ (prodrec-cong _ t₁≡u₁ _ _) =
      fix (↘ ↙ ◻) (wfEqTerm-<ˢ t₁≡u₁)
    wfEqTerm-<ˢ (prodrec-β _ ⊢t _ _ _ _) =
      fix (↙ ↘ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (emptyrec-cong A≡B _) =
      fix (↙ ◻) (wfEq-<ˢ A≡B)
    wfEqTerm-<ˢ (unitrec-cong _ t₁≡u₁ _ _ _) =
      fix (↘ ↙ ◻) (wfEqTerm-<ˢ t₁≡u₁)
    wfEqTerm-<ˢ (unitrec-β _ ⊢t _ _) =
      fix (↘ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (unitrec-β-η _ ⊢t _ _ _) =
      fix (↘ ↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (η-unit ⊢t _ _) =
      fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (suc-cong t≡u) =
      fix (↙ ◻) (wfEqTerm-<ˢ t≡u)
    wfEqTerm-<ˢ (natrec-cong _ t₁≡u₁ _ _) =
      fix (↙ ↘ ◻) (wfEqTerm-<ˢ t₁≡u₁)
    wfEqTerm-<ˢ (natrec-zero ⊢t _) =
      fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (natrec-suc ⊢t _ _) =
      fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (Id-cong A≡B _ _) =
      fix (↙ ◻) (wfEqTerm-<ˢ A≡B)
    wfEqTerm-<ˢ (J-cong _ ⊢t₁ _ _ _ _ _) =
      fix (↙ ↘ ↙ ◻) (wfTerm-<ˢ ⊢t₁)
    wfEqTerm-<ˢ (K-cong A₁≡A₂ _ _ _ _ _ _) =
      fix (↙ ↙ ◻) (wfEq-<ˢ A₁≡A₂)
    wfEqTerm-<ˢ ([]-cong-cong A≡B _ _ _ _) =
      fix (↙ ↙ ◻) (wfEq-<ˢ A≡B)
    wfEqTerm-<ˢ (J-β ⊢t _ _ _) =
      fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ (K-β ⊢t _ _ _) =
      fix (↙ ◻) (wfTerm-<ˢ ⊢t)
    wfEqTerm-<ˢ ([]-cong-β ⊢t _ _) =
      fix (↙ ◻) (wfTerm-<ˢ ⊢t)

opaque

  -- If there is a proof of type Γ ⊢ A, then there is a proof of type
  -- ⊢ Γ that is no larger than the first proof.

  wf-≤ˢ : (⊢A : Γ ⊢ A) → ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ ≤ˢ size-⊢ ⊢A
  wf-≤ˢ = Σ.map idᶠ <ˢ→≤ˢ ∘→ wf-<ˢ

opaque

  -- If there is a proof of type Γ ⊢ t ∷ A, then there is a proof of
  -- type ⊢ Γ that is no larger than the first proof.

  wfTerm-≤ˢ :
    (⊢t : Γ ⊢ t ∷ A) → ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ ≤ˢ size-⊢∷ ⊢t
  wfTerm-≤ˢ = Σ.map idᶠ <ˢ→≤ˢ ∘→ wfTerm-<ˢ

opaque

  -- If there is a proof of type Γ ⊢ A ≡ B, then there is a proof of
  -- type ⊢ Γ that is no larger than the first proof.

  wfEq-≤ˢ :
    (A≡B : Γ ⊢ A ≡ B) → ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ ≤ˢ size-⊢≡ A≡B
  wfEq-≤ˢ = Σ.map idᶠ <ˢ→≤ˢ ∘→ wfEq-<ˢ

opaque

  -- If there is a proof of type Γ ⊢ t ≡ u ∷ A, then there is a proof
  -- of type ⊢ Γ that is no larger than the first proof.

  wfEqTerm-≤ˢ :
    (t≡u : Γ ⊢ t ≡ u ∷ A) → ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ ≤ˢ size-⊢≡∷ t≡u
  wfEqTerm-≤ˢ = Σ.map idᶠ <ˢ→≤ˢ ∘→ wfEqTerm-<ˢ

opaque

  -- If a type is well-typed with respect to Γ, then Γ is well-formed.

  wf : Γ ⊢ A → ⊢ Γ
  wf = proj₁ ∘→ wf-<ˢ

opaque

  -- If a term is well-typed with respect to Γ, then Γ is well-formed.

  wfTerm : Γ ⊢ t ∷ A → ⊢ Γ
  wfTerm = proj₁ ∘→ wfTerm-<ˢ

opaque

  -- If a type equality is well-formed with respect to Γ, then Γ is
  -- well-formed.

  wfEq : Γ ⊢ A ≡ B → ⊢ Γ
  wfEq = proj₁ ∘→ wfEq-<ˢ

opaque

  -- If a term equality is well-formed with respect to Γ, then Γ is
  -- well-formed.

  wfEqTerm : Γ ⊢ t ≡ u ∷ A → ⊢ Γ
  wfEqTerm = proj₁ ∘→ wfEqTerm-<ˢ

opaque

  -- If there is a proof of Γ ∙ A ⊢ B ≡ C, then there are strictly
  -- smaller proofs of ⊢ Γ and Γ ⊢ A.

  ∙⊢≡→⊢-<ˢ :
    (B≡C : Γ ∙ A ⊢ B ≡ C) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢≡ B≡C) ×
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢≡ B≡C)
  ∙⊢≡→⊢-<ˢ B≡C =
    let ⊢Γ∙A , p            = wfEq-<ˢ B≡C
        (⊢Γ , q) , (⊢A , r) = ⊢∙→⊢-<ˢ ⊢Γ∙A
    in
    (⊢Γ , <ˢ-trans q p) , (⊢A , <ˢ-trans r p)

opaque

  -- If there is a proof of Γ ∙ A ⊢ t ≡ u ∷ B, then there are strictly
  -- smaller proofs of ⊢ Γ and Γ ⊢ A.

  ∙⊢≡∷→⊢-<ˢ :
    (t≡u : Γ ∙ A ⊢ t ≡ u ∷ B) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢≡∷ t≡u) ×
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢≡∷ t≡u)
  ∙⊢≡∷→⊢-<ˢ t≡u =
    let ⊢Γ∙A , p            = wfEqTerm-<ˢ t≡u
        (⊢Γ , q) , (⊢A , r) = ⊢∙→⊢-<ˢ ⊢Γ∙A
    in
    (⊢Γ , <ˢ-trans q p) , (⊢A , <ˢ-trans r p)

opaque

  -- If there is a proof of Γ ∙ A ∙ B ⊢ C, then there are strictly
  -- smaller proofs of ⊢ Γ, Γ ⊢ A and Γ ∙ A ⊢ B.

  ∙∙⊢→⊢-<ˢ :
    (⊢C : Γ ∙ A ∙ B ⊢ C) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢ ⊢C) ×
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢ ⊢C) ×
    (∃ λ (⊢B : Γ ∙ A ⊢ B) → size-⊢ ⊢B <ˢ size-⊢ ⊢C)
  ∙∙⊢→⊢-<ˢ ⊢C =
    let (⊢Γ∙A , Γ∙A<) , (⊢B , B<) = ∙⊢→⊢-<ˢ ⊢C
        (⊢Γ , Γ<) , (⊢A , A<)     = ⊢∙→⊢-<ˢ ⊢Γ∙A
    in
    (⊢Γ , <ˢ-trans Γ< Γ∙A<) , (⊢A , <ˢ-trans A< Γ∙A<) , (⊢B , B<)

opaque

  -- If there is a proof of Γ ∙ A ∙ B ⊢ t ∷ C, then there are strictly
  -- smaller proofs of ⊢ Γ, Γ ⊢ A and Γ ∙ A ⊢ B.

  ∙∙⊢∷→⊢-<ˢ :
    (⊢t : Γ ∙ A ∙ B ⊢ t ∷ C) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢∷ ⊢t) ×
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢∷ ⊢t) ×
    (∃ λ (⊢B : Γ ∙ A ⊢ B) → size-⊢ ⊢B <ˢ size-⊢∷ ⊢t)
  ∙∙⊢∷→⊢-<ˢ ⊢t =
    let (⊢Γ∙A , Γ∙A<) , (⊢B , B<) = ∙⊢∷→⊢-<ˢ ⊢t
        (⊢Γ , Γ<) , (⊢A , A<)     = ⊢∙→⊢-<ˢ ⊢Γ∙A
    in
    (⊢Γ , <ˢ-trans Γ< Γ∙A<) , (⊢A , <ˢ-trans A< Γ∙A<) , (⊢B , B<)

opaque

  -- If there is a proof of Γ ∙ A ∙ B ⊢ C ≡ D, then there are strictly
  -- smaller proofs of ⊢ Γ, Γ ⊢ A and Γ ∙ A ⊢ B.

  ∙∙⊢≡→⊢-<ˢ :
    (C≡D : Γ ∙ A ∙ B ⊢ C ≡ D) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢≡ C≡D) ×
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢≡ C≡D) ×
    (∃ λ (⊢B : Γ ∙ A ⊢ B) → size-⊢ ⊢B <ˢ size-⊢≡ C≡D)
  ∙∙⊢≡→⊢-<ˢ C≡D =
    let (⊢Γ∙A , Γ∙A<) , (⊢B , B<) = ∙⊢≡→⊢-<ˢ C≡D
        (⊢Γ , Γ<) , (⊢A , A<)     = ⊢∙→⊢-<ˢ ⊢Γ∙A
    in
    (⊢Γ , <ˢ-trans Γ< Γ∙A<) , (⊢A , <ˢ-trans A< Γ∙A<) , (⊢B , B<)

opaque

  -- If there is a proof of Γ ∙ A ∙ B ⊢ t ≡ u ∷ C, then there are
  -- strictly smaller proofs of ⊢ Γ, Γ ⊢ A and Γ ∙ A ⊢ B.

  ∙∙⊢≡∷→⊢-<ˢ :
    (t≡u : Γ ∙ A ∙ B ⊢ t ≡ u ∷ C) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢≡∷ t≡u) ×
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢≡∷ t≡u) ×
    (∃ λ (⊢B : Γ ∙ A ⊢ B) → size-⊢ ⊢B <ˢ size-⊢≡∷ t≡u)
  ∙∙⊢≡∷→⊢-<ˢ t≡u =
    let (⊢Γ∙A , Γ∙A<) , (⊢B , B<) = ∙⊢≡∷→⊢-<ˢ t≡u
        (⊢Γ , Γ<) , (⊢A , A<)     = ⊢∙→⊢-<ˢ ⊢Γ∙A
    in
    (⊢Γ , <ˢ-trans Γ< Γ∙A<) , (⊢A , <ˢ-trans A< Γ∙A<) , (⊢B , B<)

opaque

  -- If Γ ⊢ A holds, then ⊢ Γ ∙ A also holds.

  ⊢→⊢∙ : Γ ⊢ A → ⊢ Γ ∙ A
  ⊢→⊢∙ ⊢A = wf ⊢A ∙ ⊢A

opaque

  -- If ⊢ Γ ∙ A holds, then Γ ⊢ A also holds.

  ⊢∙→⊢ : ⊢ Γ ∙ A → Γ ⊢ A
  ⊢∙→⊢ = proj₁ ∘→ proj₂ ∘→ ⊢∙→⊢-<ˢ

opaque

  -- A lemma which could perhaps be used to make certain proofs more
  -- readable.

  infixl 24 _∙[_]

  _∙[_] : ⊢ Γ → (⊢ Γ → Γ ⊢ A) → ⊢ Γ ∙ A
  ⊢Γ ∙[ f ] = ⊢→⊢∙ (f ⊢Γ)

-- An example of how _∙[_] can be used.

_ : ⊢ ε ∙ ℕ ∙ U l ∙ Empty
_ = ε ∙[ ℕⱼ ] ∙[ Uⱼ ] ∙[ Emptyⱼ ]
