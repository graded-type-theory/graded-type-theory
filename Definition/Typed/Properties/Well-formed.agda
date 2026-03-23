------------------------------------------------------------------------
-- Context well-formedness lemmas
------------------------------------------------------------------------

{-# OPTIONS --backtracking-instance-search #-}

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

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Size
open import Tools.Size.Instances

private variable
  Γ           : Cons _ _
  𝓙           : Judgement _
  A B C D t u : Term _
  l l₁ l₂     : Lvl _
  s s₁ s₂     : Size

private opaque

  -- A lemma used below.

  fix :
    ⦃ leq : s₁ ≤ˢ s₂ ⦄ →
    (∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ s₁) →
    (∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ s₂)
  fix ⦃ leq ⦄ = Σ.map idᶠ (flip <ˢ-trans-≤ˢʳ leq)

private

  -- Below several properties are proved simultaneously using
  -- well-founded induction. The properties are collected in the
  -- record type P.

  record P (s : Size) : Set ℓ where
    no-eta-equality
    field
      wf-<ˢ :
        (⊢A : Γ ⊢ A) →
        size ⊢A PE.≡ s →
        ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢A
      wfTerm-<ˢ :
        (⊢t : Γ ⊢ t ∷ A) →
        size ⊢t PE.≡ s →
        ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢t
      wfLevel-<ˢ :
        (⊢l : Γ ⊢ l ∷Level) →
        size ⊢l PE.≡ s →
        ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢l

-- Variants of the fields of P, along with some lemmas.

private module Variants (hyp : ∀ {s₁} → s₁ <ˢ s₂ → P s₁) where

  opaque

    -- Variants of the fields of P.

    wf-<ˢ :
      (⊢A : Γ ⊢ A) →
      ⦃ lt : size ⊢A <ˢ s₂ ⦄ →
      ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢A
    wf-<ˢ ⊢A ⦃ lt ⦄ = P.wf-<ˢ (hyp lt) ⊢A PE.refl

    wfTerm-<ˢ :
      (⊢t : Γ ⊢ t ∷ A) →
      ⦃ lt : size ⊢t <ˢ s₂ ⦄ →
      ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢t
    wfTerm-<ˢ ⊢t ⦃ lt ⦄ = P.wfTerm-<ˢ (hyp lt) ⊢t PE.refl

    wfLevel-<ˢ :
      (⊢l : Γ ⊢ l ∷Level) →
      ⦃ lt : size ⊢l <ˢ s₂ ⦄ →
      ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢l
    wfLevel-<ˢ ⊢l ⦃ lt ⦄ = P.wfLevel-<ˢ (hyp lt) ⊢l PE.refl

  opaque
    unfolding size

    -- If there is a proof of ⊢ Γ »∙ A, then there are strictly
    -- smaller proofs of ⊢ Γ and Γ ⊢ A.

    ⊢∙→⊢-<ˢ :
      (⊢Γ∙A : ⊢ Γ »∙ A) →
      ⦃ leq : size ⊢Γ∙A ≤ˢ s₂ ⦄ →
      (∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢Γ∙A) ×
      (∃ λ (⊢A : Γ ⊢ A) → size ⊢A <ˢ size ⊢Γ∙A)
    ⊢∙→⊢-<ˢ (∙ ⊢A) ⦃ leq ⦄ =
      let ⊢Γ , Γ< = wf-<ˢ ⊢A ⦃ lt = ⊕≤ˢ→<ˢˡ leq ⦄ in
      (⊢Γ , ↙ <ˢ→≤ˢ Γ<) , (⊢A , !)

  opaque

    -- If there is a proof of Γ »∙ A ⊢ B, then there are strictly
    -- smaller proofs of ⊢ Γ and Γ ⊢ A.

    ∙⊢→⊢-<ˢ :
      (⊢B : Γ »∙ A ⊢ B) →
      ⦃ lt : size ⊢B <ˢ s₂ ⦄ →
      (∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢B) ×
      (∃ λ (⊢A : Γ ⊢ A) → size ⊢A <ˢ size ⊢B)
    ∙⊢→⊢-<ˢ ⊢B =
      let ⊢Γ∙A , Γ∙A<           = wf-<ˢ ⊢B
          (⊢Γ , Γ<) , (⊢A , A<) = ⊢∙→⊢-<ˢ ⊢Γ∙A
                                    ⦃ leq = <ˢ→≤ˢ (<ˢ-trans Γ∙A< !) ⦄
      in
      (⊢Γ , <ˢ-trans Γ< Γ∙A<) , (⊢A , <ˢ-trans A< Γ∙A<)

  opaque

    -- If there is a proof of Γ »∙ A ⊢ t ∷ B, then there are strictly
    -- smaller proofs of ⊢ Γ and Γ ⊢ A.

    ∙⊢∷→⊢-<ˢ :
      (⊢t : Γ »∙ A ⊢ t ∷ B) →
      ⦃ lt : size ⊢t <ˢ s₂ ⦄ →
      (∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢t) ×
      (∃ λ (⊢A : Γ ⊢ A) → size ⊢A <ˢ size ⊢t)
    ∙⊢∷→⊢-<ˢ ⊢t =
      let ⊢Γ∙A , Γ∙A<           = wfTerm-<ˢ ⊢t
          (⊢Γ , Γ<) , (⊢A , A<) = ⊢∙→⊢-<ˢ ⊢Γ∙A
                                    ⦃ leq = <ˢ→≤ˢ (<ˢ-trans Γ∙A< !) ⦄
      in
      (⊢Γ , <ˢ-trans Γ< Γ∙A<) , (⊢A , <ˢ-trans A< Γ∙A<)

-- The type P s is inhabited for every s.

private module Lemmas where

  opaque
    unfolding size

    -- If there is a proof of type Γ ⊢ A, then there is a strictly
    -- smaller proof of type ⊢ Γ.

    wf-<ˢ′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      (⊢A : Γ ⊢ A) →
      size ⊢A PE.≡ s₂ →
      ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢A
    wf-<ˢ′ hyp = λ where
        (Levelⱼ _ ⊢Γ) _       → ⊢Γ , !
        (univ A)      PE.refl → fix (wfTerm-<ˢ A)
        (Liftⱼ _ ⊢A)  PE.refl → fix (wf-<ˢ ⊢A)
        (ΠΣⱼ ⊢B _)    PE.refl → fix (∙⊢→⊢-<ˢ ⊢B .proj₁)
        (Idⱼ ⊢A _ _)  PE.refl → fix (wf-<ˢ ⊢A)
      where
      open Variants hyp

  opaque
    unfolding size

    -- If there is a proof of type Γ ⊢ t ∷ A, then there is a strictly
    -- smaller proof of type ⊢ Γ.

    wfTerm-<ˢ′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      (⊢t : Γ ⊢ t ∷ A) →
      size ⊢t PE.≡ s₂ →
      ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢t
    wfTerm-<ˢ′ hyp = λ where
        (conv ⊢t _)             PE.refl → fix (wfTerm-<ˢ ⊢t)
        (var ⊢Γ _)              _       → ⊢Γ , !
        (defn ⊢Γ _ _)           _       → ⊢Γ , !
        (Levelⱼ ⊢Γ _)           _       → ⊢Γ , !
        (zeroᵘⱼ _ ⊢Γ)           _       → ⊢Γ , !
        (sucᵘⱼ t)               PE.refl → fix (wfTerm-<ˢ t)
        (supᵘⱼ t u)             PE.refl → fix (wfTerm-<ˢ t)
        (Uⱼ ⊢l)                 PE.refl → fix (wfLevel-<ˢ ⊢l)
        (Liftⱼ _ _ ⊢A)          PE.refl → fix (wfTerm-<ˢ ⊢A)
        (liftⱼ _ ⊢A _)          PE.refl → fix (wf-<ˢ ⊢A)
        (lowerⱼ ⊢t)             PE.refl → fix (wfTerm-<ˢ ⊢t)
        (ΠΣⱼ _ ⊢A _ _)          PE.refl → fix (wfTerm-<ˢ ⊢A)
        (lamⱼ _ ⊢t _)           PE.refl → fix (∙⊢∷→⊢-<ˢ ⊢t .proj₁)
        (⊢t ∘ⱼ _)               PE.refl → fix (wfTerm-<ˢ ⊢t)
        (prodⱼ _ ⊢t _ _)        PE.refl → fix (wfTerm-<ˢ ⊢t)
        (fstⱼ _ ⊢t)             PE.refl → fix (wfTerm-<ˢ ⊢t)
        (sndⱼ _ ⊢t)             PE.refl → fix (wfTerm-<ˢ ⊢t)
        (prodrecⱼ _ ⊢t _ _)     PE.refl → fix (wfTerm-<ˢ ⊢t)
        (Emptyⱼ ⊢Γ)             _       → ⊢Γ , !
        (emptyrecⱼ ⊢A _)        PE.refl → fix (wf-<ˢ ⊢A)
        (Unitⱼ ⊢Γ _)            PE.refl → ⊢Γ , !
        (starⱼ ⊢Γ _)            PE.refl → ⊢Γ , !
        (unitrecⱼ ⊢A ⊢t _ _)    PE.refl → fix (wfTerm-<ˢ ⊢t)
        (ℕⱼ ⊢Γ)                 _       → ⊢Γ , !
        (zeroⱼ ⊢Γ)              _       → ⊢Γ , !
        (sucⱼ n)                PE.refl → fix (wfTerm-<ˢ n)
        (natrecⱼ ⊢t _ _)        PE.refl → fix (wfTerm-<ˢ ⊢t)
        (Idⱼ ⊢A _ _)            PE.refl → fix (wfTerm-<ˢ ⊢A)
        (rflⱼ ⊢t)               PE.refl → fix (wfTerm-<ˢ ⊢t)
        (Jⱼ ⊢t _ _ _ _)         PE.refl → fix (wfTerm-<ˢ ⊢t)
        (Kⱼ _ ⊢u _ _)           PE.refl → fix (wfTerm-<ˢ ⊢u)
        ([]-congⱼ _ ⊢A _ _ _ _) PE.refl → fix (wf-<ˢ ⊢A)
      where
      open Variants hyp

  opaque
    unfolding size

    -- If there is a proof of type Γ ⊢ l ∷Level, then there is a
    -- strictly smaller proof of type ⊢ Γ.

    wfLevel-<ˢ′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      (⊢l : Γ ⊢ l ∷Level) →
      size ⊢l PE.≡ s₂ →
      ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢l
    wfLevel-<ˢ′ hyp = λ where
        (term _ ⊢l)    PE.refl → fix (wfTerm-<ˢ ⊢l)
        (literal _ ⊢Γ) _       → ⊢Γ , !
      where
      open Variants hyp

  opaque

    -- The type P s is inhabited for every s.

    P-inhabited : P s
    P-inhabited =
      well-founded-induction P
        (λ _ hyp →
           record
             { wf-<ˢ      = wf-<ˢ′      hyp
             ; wfTerm-<ˢ  = wfTerm-<ˢ′  hyp
             ; wfLevel-<ˢ = wfLevel-<ˢ′ hyp
             })
        _

  opaque

    -- If there is a proof of type Γ ⊢ A, then there is a strictly
    -- smaller proof of type ⊢ Γ.

    wf-<ˢ : (⊢A : Γ ⊢ A) → ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢A
    wf-<ˢ ⊢A = P.wf-<ˢ P-inhabited ⊢A PE.refl

  opaque

    -- If there is a proof of type Γ ⊢ t ∷ A, then there is a strictly
    -- smaller proof of type ⊢ Γ.

    wfTerm-<ˢ :
      (⊢t : Γ ⊢ t ∷ A) → ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢t
    wfTerm-<ˢ ⊢t = P.wfTerm-<ˢ P-inhabited ⊢t PE.refl

  opaque

    -- If there is a proof of type Γ ⊢ l ∷Level, then there is a
    -- strictly smaller proof of type ⊢ Γ.

    wfLevel-<ˢ :
      (⊢l : Γ ⊢ l ∷Level) → ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢l
    wfLevel-<ˢ ⊢l = P.wfLevel-<ˢ P-inhabited ⊢l PE.refl

  opaque
    unfolding size

    mutual

      -- If there is a proof of type Γ ⊢ A ≡ B, then there is a
      -- strictly smaller proof of type ⊢ Γ.

      wfEq-<ˢ :
        (A≡B : Γ ⊢ A ≡ B) → ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size A≡B
      wfEq-<ˢ (univ A≡B)          = fix (wfEqTerm-<ˢ A≡B)
      wfEq-<ˢ (refl ⊢A)           = fix (wf-<ˢ ⊢A)
      wfEq-<ˢ (sym B≡A)           = fix (wfEq-<ˢ B≡A)
      wfEq-<ˢ (trans A≡B B≡C)     = fix (wfEq-<ˢ A≡B)
      wfEq-<ˢ (U-cong l₁≡l₂)      = fix (wfEqTerm-<ˢ l₁≡l₂)
      wfEq-<ˢ (Lift-cong _ A≡B)   = fix (wfEq-<ˢ A≡B)
      wfEq-<ˢ (ΠΣ-cong A₁≡B₁ _ _) = fix (wfEq-<ˢ A₁≡B₁)
      wfEq-<ˢ (Id-cong A≡B _ _)   = fix (wfEq-<ˢ A≡B)

      -- If there is a proof of type Γ ⊢ t ≡ u ∷ A, then there is a
      -- strictly smaller proof of type ⊢ Γ.

      wfEqTerm-<ˢ :
        (t≡u : Γ ⊢ t ≡ u ∷ A) →
        ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size t≡u
      wfEqTerm-<ˢ (refl ⊢t) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (sym ⊢A _) =
        fix (wf-<ˢ ⊢A)
      wfEqTerm-<ˢ (trans t≡u _) =
        fix (wfEqTerm-<ˢ t≡u)
      wfEqTerm-<ˢ (conv t≡u _) =
        fix (wfEqTerm-<ˢ t≡u)
      wfEqTerm-<ˢ (δ-red ⊢Γ _ _ _) =
        ⊢Γ , !
      wfEqTerm-<ˢ (sucᵘ-cong t≡u) =
        fix (wfEqTerm-<ˢ t≡u)
      wfEqTerm-<ˢ (supᵘ-cong t≡t' u≡u') =
        fix (wfEqTerm-<ˢ t≡t')
      wfEqTerm-<ˢ (supᵘ-zeroˡ l) =
        fix (wfTerm-<ˢ l)
      wfEqTerm-<ˢ (supᵘ-sucᵘ l₁ l₂) =
        fix (wfTerm-<ˢ l₁)
      wfEqTerm-<ˢ (supᵘ-assoc l₁ l₂ l₃) =
        fix (wfTerm-<ˢ l₁)
      wfEqTerm-<ˢ (supᵘ-comm l₁ l₂) =
        fix (wfTerm-<ˢ l₁)
      wfEqTerm-<ˢ (supᵘ-idem ⊢l) =
        fix (wfTerm-<ˢ ⊢l)
      wfEqTerm-<ˢ (supᵘ-sub ⊢l) =
        fix (wfTerm-<ˢ ⊢l)
      wfEqTerm-<ˢ (U-cong l₁≡l₂) =
        fix (wfEqTerm-<ˢ l₁≡l₂)
      wfEqTerm-<ˢ (Lift-cong _ _ _ A≡B) =
        fix (wfEqTerm-<ˢ A≡B)
      wfEqTerm-<ˢ (lower-cong t≡u) =
        fix (wfEqTerm-<ˢ t≡u)
      wfEqTerm-<ˢ (Lift-β x _) =
        fix (wf-<ˢ x)
      wfEqTerm-<ˢ (Lift-η _ ⊢A _ _ _) =
        fix (wf-<ˢ ⊢A)
      wfEqTerm-<ˢ (ΠΣ-cong _ A≡B _ _) =
        fix (wfEqTerm-<ˢ A≡B)
      wfEqTerm-<ˢ (app-cong t₁≡u₁ _) =
        fix (wfEqTerm-<ˢ t₁≡u₁)
      wfEqTerm-<ˢ (β-red _ _ ⊢u _ _) =
        fix (wfTerm-<ˢ ⊢u)
      wfEqTerm-<ˢ (η-eq _ ⊢t _ _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (fst-cong _ t≡u) =
        fix (wfEqTerm-<ˢ t≡u)
      wfEqTerm-<ˢ (snd-cong _ t≡u) =
        fix (wfEqTerm-<ˢ t≡u)
      wfEqTerm-<ˢ (Σ-β₁ _ ⊢t _ _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (Σ-β₂ _ ⊢t _ _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (Σ-η _ ⊢t _ _ _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (prod-cong _ t₁≡u₁ _ _) =
        fix (wfEqTerm-<ˢ t₁≡u₁)
      wfEqTerm-<ˢ (prodrec-cong _ t₁≡u₁ _ _) =
        fix (wfEqTerm-<ˢ t₁≡u₁)
      wfEqTerm-<ˢ (prodrec-β _ ⊢t _ _ _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (emptyrec-cong A≡B _) =
        fix (wfEq-<ˢ A≡B)
      wfEqTerm-<ˢ (unitrec-cong _ t₁≡u₁ _ _ _) =
        fix (wfEqTerm-<ˢ t₁≡u₁)
      wfEqTerm-<ˢ (unitrec-β _ ⊢t _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (unitrec-β-η _ ⊢t _ _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (η-unit ⊢t _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (suc-cong t≡u) =
        fix (wfEqTerm-<ˢ t≡u)
      wfEqTerm-<ˢ (natrec-cong _ t₁≡u₁ _ _) =
        fix (wfEqTerm-<ˢ t₁≡u₁)
      wfEqTerm-<ˢ (natrec-zero ⊢t _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (natrec-suc ⊢t _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (Id-cong A≡B _ _) =
        fix (wfEqTerm-<ˢ A≡B)
      wfEqTerm-<ˢ (J-cong _ ⊢t₁ _ _ _ _ _) =
        fix (wfTerm-<ˢ ⊢t₁)
      wfEqTerm-<ˢ (K-cong A₁≡A₂ _ _ _ _ _) =
        fix (wfEq-<ˢ A₁≡A₂)
      wfEqTerm-<ˢ ([]-cong-cong _ A≡B _ _ _ _) =
        fix (wfEq-<ˢ A≡B)
      wfEqTerm-<ˢ (J-β ⊢t _ _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (K-β _ ⊢u _) =
        fix (wfTerm-<ˢ ⊢u)
      wfEqTerm-<ˢ ([]-cong-β _ ⊢t _ _) =
        fix (wfTerm-<ˢ ⊢t)
      wfEqTerm-<ˢ (equality-reflection _ _ ⊢v) =
        fix (wfTerm-<ˢ ⊢v)

  opaque
    unfolding size

    -- If there is a proof of type Γ ⊢ l₁ ≡ l₂ ∷Level, then there is a
    -- strictly smaller proof of type ⊢ Γ.

    wfEqLevel-<ˢ :
      (l₁≡l₂ : Γ ⊢ l₁ ≡ l₂ ∷Level) →
      ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size l₁≡l₂
    wfEqLevel-<ˢ (term _ l₁≡l₂) = fix (wfEqTerm-<ˢ l₁≡l₂)
    wfEqLevel-<ˢ (literal _ ⊢Γ) = ⊢Γ , !

opaque

  -- If there is a proof of type Γ ⊢[ 𝓙 ], where 𝓙 is not [ctxt], then
  -- there is a strictly smaller proof of type ⊢ Γ.

  wf-<ˢ :
    ∀ {𝓙} → 𝓙 PE.≢ [ctxt] → (⊢𝓙 : Γ ⊢[ 𝓙 ]) →
    ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢𝓙
  wf-<ˢ {𝓙 = [ctxt]}          hyp = ⊥-elim (hyp PE.refl)
  wf-<ˢ {𝓙 = [ _ type]}       _   = Lemmas.wf-<ˢ
  wf-<ˢ {𝓙 = [ _ ≡ _ type]}   _   = Lemmas.wfEq-<ˢ
  wf-<ˢ {𝓙 = [ _ ∷ _ ]}       _   = Lemmas.wfTerm-<ˢ
  wf-<ˢ {𝓙 = [ _ ≡ _ ∷ _ ]}   _   = Lemmas.wfEqTerm-<ˢ
  wf-<ˢ {𝓙 = [ _ ∷Level]}     _   = Lemmas.wfLevel-<ˢ
  wf-<ˢ {𝓙 = [ _ ≡ _ ∷Level]} _   = Lemmas.wfEqLevel-<ˢ

opaque

  -- If there is a proof of type Γ ⊢[ 𝓙 ], then there is a proof of
  -- type ⊢ Γ that is no larger than the first proof.

  wf-≤ˢ :
    ∀ {𝓙} (⊢𝓙 : Γ ⊢[ 𝓙 ]) → ∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ ≤ˢ size ⊢𝓙
  wf-≤ˢ {𝓙 = [ctxt]}          = λ ⊢Γ → ⊢Γ , ◻
  wf-≤ˢ {𝓙 = [ _ type]}       = Σ.map idᶠ <ˢ→≤ˢ ∘→ wf-<ˢ (λ ())
  wf-≤ˢ {𝓙 = [ _ ≡ _ type]}   = Σ.map idᶠ <ˢ→≤ˢ ∘→ wf-<ˢ (λ ())
  wf-≤ˢ {𝓙 = [ _ ∷ _ ]}       = Σ.map idᶠ <ˢ→≤ˢ ∘→ wf-<ˢ (λ ())
  wf-≤ˢ {𝓙 = [ _ ≡ _ ∷ _ ]}   = Σ.map idᶠ <ˢ→≤ˢ ∘→ wf-<ˢ (λ ())
  wf-≤ˢ {𝓙 = [ _ ∷Level]}     = Σ.map idᶠ <ˢ→≤ˢ ∘→ wf-<ˢ (λ ())
  wf-≤ˢ {𝓙 = [ _ ≡ _ ∷Level]} = Σ.map idᶠ <ˢ→≤ˢ ∘→ wf-<ˢ (λ ())

opaque

  -- If the judgement Γ ⊢[ 𝓙 ] is inhabited, then Γ is well-formed.

  wf : Γ ⊢[ 𝓙 ] → ⊢ Γ
  wf = proj₁ ∘→ wf-≤ˢ

opaque

  -- If a term is well-typed with respect to Γ, then Γ is well-formed.

  wfTerm : Γ ⊢ t ∷ A → ⊢ Γ
  wfTerm = wf

opaque

  -- If a level is well-typed with respect to Γ, then Γ is well-formed.

  wfLevel : Γ ⊢ l ∷Level → ⊢ Γ
  wfLevel = wf

opaque

  -- If a type equality is well-formed with respect to Γ, then Γ is
  -- well-formed.

  wfEq : Γ ⊢ A ≡ B → ⊢ Γ
  wfEq = wf

opaque

  -- If a term equality is well-formed with respect to Γ, then Γ is
  -- well-formed.

  wfEqTerm : Γ ⊢ t ≡ u ∷ A → ⊢ Γ
  wfEqTerm = wf

opaque

  -- If a level equality is well-formed with respect to Γ, then Γ is
  -- well-formed.

  wfEqLevel : Γ ⊢ l₁ ≡ l₂ ∷Level → ⊢ Γ
  wfEqLevel = wf

opaque

  -- If there is a proof of Γ »∙ A ⊢[ 𝓙 ], then there are strictly
  -- smaller proofs of ⊢ Γ and Γ ⊢ A.

  ∙⊢→⊢-<ˢ :
    ∀ {𝓙} (⊢𝓙 : Γ »∙ A ⊢[ 𝓙 ]) →
    (∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢𝓙) ×
    (∃ λ (⊢A : Γ ⊢ A) → size ⊢A <ˢ size ⊢𝓙)
  ∙⊢→⊢-<ˢ ⊢𝓙 =
    let ⊢Γ∙A , leq              = wf-≤ˢ ⊢𝓙
        (⊢Γ , lt₁) , (⊢A , lt₂) =
          Variants.⊢∙→⊢-<ˢ (λ _ → Lemmas.P-inhabited) ⊢Γ∙A ⦃ leq = ◻ ⦄
    in
    (⊢Γ , <ˢ-trans-≤ˢʳ lt₁ leq) ,
    (⊢A , <ˢ-trans-≤ˢʳ lt₂ leq)

opaque

  -- If ⊢ Γ »∙ A holds, then Γ ⊢ A also holds.

  ⊢∙→⊢ : ⊢ Γ »∙ A → Γ ⊢ A
  ⊢∙→⊢ = proj₁ ∘→ proj₂ ∘→ ∙⊢→⊢-<ˢ

opaque

  -- If there is a proof of Γ »∙ A »∙ B ⊢[ 𝓙 ], then there are
  -- strictly smaller proofs of ⊢ Γ, Γ ⊢ A and Γ »∙ A ⊢ B.

  ∙∙⊢→⊢-<ˢ :
    ∀ {𝓙} (⊢𝓙 : Γ »∙ A »∙ B ⊢[ 𝓙 ]) →
    (∃ λ (⊢Γ : ⊢ Γ) → size ⊢Γ <ˢ size ⊢𝓙) ×
    (∃ λ (⊢A : Γ ⊢ A) → size ⊢A <ˢ size ⊢𝓙) ×
    (∃ λ (⊢B : Γ »∙ A ⊢ B) → size ⊢B <ˢ size ⊢𝓙)
  ∙∙⊢→⊢-<ˢ ⊢C =
    let (⊢Γ∙A , Γ∙A<) , (⊢B , B<) = ∙⊢→⊢-<ˢ ⊢C
        (⊢Γ , Γ<) , (⊢A , A<)     = ∙⊢→⊢-<ˢ ⊢Γ∙A
    in
    (⊢Γ , <ˢ-trans Γ< Γ∙A<) , (⊢A , <ˢ-trans A< Γ∙A<) , (⊢B , B<)

opaque
  unfolding size

  -- If there is a proof of ⊢ Γ, then there is a proof of » Γ .defs
  -- that is strictly smaller than the first proof.

  ⊢→»-<ˢ : (⊢Γ : ⊢ Γ) → ∃ λ (»Γ : » Γ .defs) → size-» »Γ <ˢ size ⊢Γ
  ⊢→»-<ˢ (ε »∇) = »∇ , !
  ⊢→»-<ˢ (∙ ⊢A) = let ⊢Γ , Γ< = wf-<ˢ (λ ()) ⊢A
                      »∇ , ∇< = ⊢→»-<ˢ ⊢Γ
                  in
                  »∇ , <ˢ-trans ∇< (<ˢ-trans Γ< !)

opaque

  -- If a context pair is well-formed, then the definition context is
  -- well-formed.

  defn-wf : ⊢ Γ → » Γ .defs
  defn-wf = proj₁ ∘→ ⊢→»-<ˢ

opaque

  -- A lemma which could perhaps be used to make certain proofs more
  -- readable.

  infixl 24 _∙[_]

  _∙[_] : ⊢ Γ → (⊢ Γ → Γ ⊢ A) → ⊢ Γ »∙ A
  ⊢Γ ∙[ f ] = ∙ f ⊢Γ

-- An example of how _∙[_] can be used.

_ : ε »⊢ ε ∙ ℕ ∙ Empty
_ = εε ∙[ _⊢_.univ ∘→ ℕⱼ ] ∙[ _⊢_.univ ∘→ Emptyⱼ ]
