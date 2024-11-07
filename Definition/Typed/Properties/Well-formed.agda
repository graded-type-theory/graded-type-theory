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
import Tools.PropositionalEquality as PE
open import Tools.Size

private variable
  Γ           : Con Term _
  A B C D t u : Term _
  l           : Nat
  s s₁ s₂     : Size

------------------------------------------------------------------------
-- Context well-formedness lemmas

private opaque

  -- A lemma used below.

  fix :
    s₁ ≤ˢ s₂ →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ s₁) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ s₂)
  fix s₁≤ˢs₂ = Σ.map idᶠ (flip <ˢ-trans-≤ˢʳ s₁≤ˢs₂)

private

  -- Below several properties are proved simultaneously using
  -- well-founded induction. The properties are collected in the
  -- record type P.

  record P (s : Size) : Set ℓ where
    no-eta-equality
    field
      wf-<ˢ :
        (⊢A : Γ ⊢ A) →
        size-⊢ ⊢A PE.≡ s →
        ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢ ⊢A
      wfTerm-<ˢ :
        (⊢t : Γ ⊢ t ∷ A) →
        size-⊢∷ ⊢t PE.≡ s →
        ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢∷ ⊢t

-- Variants of the fields of P, along with some lemmas.

private module Variants (hyp : ∀ {s₁} → s₁ <ˢ s₂ → P s₁) where

  opaque

    -- Variants of the fields of P.

    wf-<ˢ′ :
      (⊢A : Γ ⊢ A) →
      size-⊢ ⊢A <ˢ s₂ →
      ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢ ⊢A
    wf-<ˢ′ ⊢A <s₂ = P.wf-<ˢ (hyp <s₂) ⊢A PE.refl

    wfTerm-<ˢ′ :
      (⊢t : Γ ⊢ t ∷ A) →
      size-⊢∷ ⊢t <ˢ s₂ →
      ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢∷ ⊢t
    wfTerm-<ˢ′ ⊢t <s₂ = P.wfTerm-<ˢ (hyp <s₂) ⊢t PE.refl

  opaque
    unfolding size-⊢′

    -- If there is a proof of ⊢ Γ ∙ A, then there are strictly smaller
    -- proofs of ⊢ Γ and Γ ⊢ A.

    ⊢∙→⊢-<ˢ :
      (⊢Γ∙A : ⊢ Γ ∙ A) →
      size-⊢′ ⊢Γ∙A ≤ˢ s₂ →
      (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢′ ⊢Γ∙A) ×
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢′ ⊢Γ∙A)
    ⊢∙→⊢-<ˢ (∙ ⊢A) ≤s₂ =
      let ⊢Γ , Γ< = wf-<ˢ′ ⊢A (⊕≤ˢ→<ˢˡ ≤s₂) in
      (⊢Γ , ↙ <ˢ→≤ˢ Γ<) , (⊢A , ↙ ◻)

  opaque

    -- If there is a proof of Γ ∙ A ⊢ B, then there are strictly
    -- smaller proofs of ⊢ Γ and Γ ⊢ A.

    ∙⊢→⊢-<ˢ :
      (⊢B : Γ ∙ A ⊢ B) →
      size-⊢ ⊢B <ˢ s₂ →
      (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢ ⊢B) ×
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢ ⊢B)
    ∙⊢→⊢-<ˢ ⊢B B< =
      let ⊢Γ∙A , Γ∙A<           = wf-<ˢ′ ⊢B B<
          (⊢Γ , Γ<) , (⊢A , A<) = ⊢∙→⊢-<ˢ ⊢Γ∙A $
                                  <ˢ→≤ˢ (<ˢ-trans Γ∙A< B<)
      in
      (⊢Γ , <ˢ-trans Γ< Γ∙A<) , (⊢A , <ˢ-trans A< Γ∙A<)

  opaque

    -- If there is a proof of Γ ∙ A ⊢ t ∷ B, then there are strictly
    -- smaller proofs of ⊢ Γ and Γ ⊢ A.

    ∙⊢∷→⊢-<ˢ :
      (⊢t : Γ ∙ A ⊢ t ∷ B) →
      size-⊢∷ ⊢t <ˢ s₂ →
      (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢∷ ⊢t) ×
      (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢∷ ⊢t)
    ∙⊢∷→⊢-<ˢ ⊢t t< =
      let ⊢Γ∙A , Γ∙A<           = wfTerm-<ˢ′ ⊢t t<
          (⊢Γ , Γ<) , (⊢A , A<) = ⊢∙→⊢-<ˢ ⊢Γ∙A $
                                  <ˢ→≤ˢ (<ˢ-trans Γ∙A< t<)
      in
      (⊢Γ , <ˢ-trans Γ< Γ∙A<) , (⊢A , <ˢ-trans A< Γ∙A<)

-- The type P s is inhabited for every s.

private module Lemmas where

  opaque
    unfolding size-⊢

    -- If there is a proof of type Γ ⊢ A, then there is a strictly
    -- smaller proof of type ⊢ Γ.

    wf-<ˢ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      (⊢A : Γ ⊢ A) →
      size-⊢ ⊢A PE.≡ s₂ →
      ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢ ⊢A
    wf-<ˢ hyp = λ where
        (Uⱼ ⊢Γ)      _       → ⊢Γ , ↙ ◻
        (univ A)     PE.refl → fix (↙ ◻) (wfTerm-<ˢ′ A (↙ ◻))
        (ΠΣⱼ ⊢B _)   PE.refl → fix (↙ ◻) (∙⊢→⊢-<ˢ ⊢B (↙ ◻) .proj₁)
        (Emptyⱼ ⊢Γ)  _       → ⊢Γ , ↙ ◻
        (Unitⱼ ⊢Γ _) _       → ⊢Γ , ↙ ◻
        (ℕⱼ ⊢Γ)      _       → ⊢Γ , ↙ ◻
        (Idⱼ ⊢t _)   PE.refl → fix (↙ ◻) (wfTerm-<ˢ′ ⊢t (↙ ◻))
      where
      open Variants hyp

  opaque
    unfolding size-⊢∷

    -- If there is a proof of type Γ ⊢ t ∷ A, then there is a strictly
    -- smaller proof of type ⊢ Γ.

    wfTerm-<ˢ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      (⊢t : Γ ⊢ t ∷ A) →
      size-⊢∷ ⊢t PE.≡ s₂ →
      ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢∷ ⊢t
    wfTerm-<ˢ hyp = λ where
        (conv ⊢t _)          PE.refl → fix (↙ ◻) (wfTerm-<ˢ′ ⊢t (↙ ◻))
        (var ⊢Γ _)           _       → ⊢Γ , ↙ ◻
        (Uⱼ ⊢Γ)              _       → ⊢Γ , ↙ ◻
        (ΠΣⱼ ⊢A _ _)         PE.refl → fix (↙ ◻) (wfTerm-<ˢ′ ⊢A (↙ ◻))
        (lamⱼ ⊢t _)          PE.refl → fix (↙ ◻) $
                                       ∙⊢∷→⊢-<ˢ ⊢t (↙ ◻) .proj₁
        (⊢t ∘ⱼ _)            PE.refl → fix (↙ ◻) (wfTerm-<ˢ′ ⊢t (↙ ◻))
        (prodⱼ _ ⊢t _ _)     PE.refl → fix (↘ ↙ ◻) $
                                       wfTerm-<ˢ′ ⊢t (↘ ↙ ◻)
        (fstⱼ _ ⊢t)          PE.refl → fix (↘ ◻) (wfTerm-<ˢ′ ⊢t (↘ ◻))
        (sndⱼ _ ⊢t)          PE.refl → fix (↘ ◻) (wfTerm-<ˢ′ ⊢t (↘ ◻))
        (prodrecⱼ _ ⊢t _ _)  PE.refl → fix (↘ ↙ ◻) $
                                       wfTerm-<ˢ′ ⊢t (↘ ↙ ◻)
        (Emptyⱼ ⊢Γ)          _       → ⊢Γ , ↙ ◻
        (emptyrecⱼ ⊢A _)     PE.refl → fix (↙ ◻) (wf-<ˢ′ ⊢A (↙ ◻))
        (Unitⱼ ⊢Γ _)         _       → ⊢Γ , ↙ ◻
        (starⱼ ⊢Γ _)         _       → ⊢Γ , ↙ ◻
        (unitrecⱼ ⊢A ⊢t _ _) PE.refl → fix (↘ ↙ ◻) $
                                       wfTerm-<ˢ′ ⊢t (↘ ↙ ◻)
        (ℕⱼ ⊢Γ)              _       → ⊢Γ , ↙ ◻
        (zeroⱼ ⊢Γ)           _       → ⊢Γ , ↙ ◻
        (sucⱼ n)             PE.refl → fix (↙ ◻) (wfTerm-<ˢ′ n (↙ ◻))
        (natrecⱼ ⊢t _ _)     PE.refl → fix (↙ ◻) (wfTerm-<ˢ′ ⊢t (↙ ◻))
        (Idⱼ ⊢A _ _)         PE.refl → fix (↙ ◻) (wfTerm-<ˢ′ ⊢A (↙ ◻))
        (rflⱼ ⊢t)            PE.refl → fix (↙ ◻) (wfTerm-<ˢ′ ⊢t (↙ ◻))
        (Jⱼ ⊢t _ _ _ _)      PE.refl → fix (↙ ↙ ◻) $
                                       wfTerm-<ˢ′ ⊢t (↙ ↙ ◻)
        (Kⱼ ⊢t _ _ _ _)      PE.refl → fix (↙ ↙ ◻) $
                                       wfTerm-<ˢ′ ⊢t (↙ ↙ ◻)
        ([]-congⱼ ⊢t _ _ _)  PE.refl → fix (↙ ◻) (wfTerm-<ˢ′ ⊢t (↙ ◻))
      where
      open Variants hyp

  opaque

    -- The type P s is inhabited for every s.

    P-inhabited : P s
    P-inhabited =
      well-founded-induction P
        (λ _ hyp →
           record
             { wf-<ˢ     = wf-<ˢ     hyp
             ; wfTerm-<ˢ = wfTerm-<ˢ hyp
             })
        _

opaque

  -- If there is a proof of type Γ ⊢ A, then there is a strictly
  -- smaller proof of type ⊢ Γ.

  wf-<ˢ : (⊢A : Γ ⊢ A) → ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢ ⊢A
  wf-<ˢ ⊢A = P.wf-<ˢ Lemmas.P-inhabited ⊢A PE.refl

opaque

  -- If there is a proof of type Γ ⊢ t ∷ A, then there is a strictly
  -- smaller proof of type ⊢ Γ.

  wfTerm-<ˢ :
    (⊢t : Γ ⊢ t ∷ A) → ∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢∷ ⊢t
  wfTerm-<ˢ ⊢t = P.wfTerm-<ˢ Lemmas.P-inhabited ⊢t PE.refl

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

  -- If there is a proof of ⊢ Γ ∙ A, then there are strictly smaller
  -- proofs of ⊢ Γ and Γ ⊢ A.

  ⊢∙→⊢-<ˢ :
    (⊢Γ∙A : ⊢ Γ ∙ A) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢′ ⊢Γ∙A) ×
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢′ ⊢Γ∙A)
  ⊢∙→⊢-<ˢ ⊢Γ∙A = Variants.⊢∙→⊢-<ˢ (λ _ → Lemmas.P-inhabited) ⊢Γ∙A ◻

opaque

  -- If ⊢ Γ ∙ A holds, then Γ ⊢ A also holds.

  ⊢∙→⊢ : ⊢ Γ ∙ A → Γ ⊢ A
  ⊢∙→⊢ = proj₁ ∘→ proj₂ ∘→ ⊢∙→⊢-<ˢ

opaque

  -- If there is a proof of Γ ∙ A ⊢ B, then there are strictly
  -- smaller proofs of ⊢ Γ and Γ ⊢ A.

  ∙⊢→⊢-<ˢ :
    (⊢B : Γ ∙ A ⊢ B) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢ ⊢B) ×
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢ ⊢B)
  ∙⊢→⊢-<ˢ ⊢B =
    Variants.∙⊢→⊢-<ˢ {s₂ = node _} (λ _ → Lemmas.P-inhabited) ⊢B (↙ ◻)

opaque

  -- If there is a proof of Γ ∙ A ⊢ t ∷ B, then there are strictly
  -- smaller proofs of ⊢ Γ and Γ ⊢ A.

  ∙⊢∷→⊢-<ˢ :
    (⊢t : Γ ∙ A ⊢ t ∷ B) →
    (∃ λ (⊢Γ : ⊢ Γ) → size-⊢′ ⊢Γ <ˢ size-⊢∷ ⊢t) ×
    (∃ λ (⊢A : Γ ⊢ A) → size-⊢ ⊢A <ˢ size-⊢∷ ⊢t)
  ∙⊢∷→⊢-<ˢ ⊢t =
    Variants.∙⊢∷→⊢-<ˢ {s₂ = node _} (λ _ → Lemmas.P-inhabited) ⊢t (↙ ◻)

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

  -- A lemma which could perhaps be used to make certain proofs more
  -- readable.

  infixl 24 _∙[_]

  _∙[_] : ⊢ Γ → (⊢ Γ → Γ ⊢ A) → ⊢ Γ ∙ A
  ⊢Γ ∙[ f ] = ∙ f ⊢Γ

-- An example of how _∙[_] can be used.

_ : ⊢ ε ∙ ℕ ∙ U l ∙ Empty
_ = ε ∙[ ℕⱼ ] ∙[ Uⱼ ] ∙[ Emptyⱼ ]
