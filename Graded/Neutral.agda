------------------------------------------------------------------------
-- A result related to neutral terms and usage
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Neutral
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Typed TR
open import Definition.Typed.Inversion TR
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Erasure.Consequences.Soundness TR UR
open import Graded.Erasure.Target using (non-strict)
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Restrictions 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Restrictions.Instance UR

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  Γ   : Con Term _
  A t : Term _
  χ   : Conₘ _
  p   : M
  s   : Strength
  sem : Some-erased-matches

opaque

  -- If the modality's zero is well-behaved and erased matches are not
  -- allowed, then neutral, well-typed terms are not well-resourced
  -- with respect to consistent, erasable contexts. (The contexts only
  -- need to be consistent if emptyrec is allowed for 𝟙ᵐ and 𝟘.)

  neutral-not-well-resourced :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
    No-erased-matches TR UR →
    (Emptyrec-allowed 𝟙ᵐ 𝟘 → Consistent Γ) →
    Neutral t →
    Γ ⊢ t ∷ A →
    ¬ 𝟘ᶜ ▸[ 𝟙ᵐ ] t
  neutral-not-well-resourced {Γ} nem consistent =
    λ t-ne ⊢t ▸t → helper t-ne ⊢t ▸t ≈ᶜ-refl
    where
    helper : Neutral t → Γ ⊢ t ∷ A → χ ▸[ 𝟙ᵐ ] t → ¬ χ ≈ᶜ 𝟘ᶜ
    helper {χ} = λ where
      (var x) _ var →
        (𝟘ᶜ , x ≔ 𝟙) ≈ᶜ 𝟘ᶜ             →⟨ lookup-cong ⟩
        (𝟘ᶜ , x ≔ 𝟙) ⟨ x ⟩ ≡ 𝟘ᶜ ⟨ x ⟩  →⟨ PE.trans (PE.sym (update-lookup 𝟘ᶜ x)) ∘→
                                          flip PE.trans (𝟘ᶜ-lookup x) ⟩
        𝟙 ≡ 𝟘                          →⟨ non-trivial ⟩
        ⊥                              □
      (∘ₙ t-n) ⊢∘ (▸t ∘ₘ _) →
        case inversion-app ⊢∘ of λ {
          (_ , _ , _ , ⊢t , _) →
        helper t-n ⊢t ▸t ∘→ proj₁ ∘→ +ᶜ-positive }
      (fstₙ t-n) ⊢fst (fstₘ _ ▸t mp≡𝟙ᵐ _) →
        case inversion-fst ⊢fst of λ {
          (_ , _ , _ , _ , _ , ⊢t , _) →
        helper t-n ⊢t (▸-cong mp≡𝟙ᵐ ▸t) }
      (sndₙ t-n) ⊢snd (sndₘ ▸t) →
        case inversion-snd ⊢snd of λ {
          (_ , _ , _ , _ , _ , ⊢t , _) →
        helper t-n ⊢t ▸t }
      (prodrecₙ t-n) ⊢pr (prodrecₘ {γ} {r} {δ} ▸t _ _ ok) →
        case inversion-prodrec ⊢pr of λ {
          (_ , _ , _ , _ , _ , _ , ⊢t , _) →
        case nem non-trivial .proj₁ ok of λ {
          r≢𝟘 →
        r ·ᶜ γ +ᶜ δ ≈ᶜ 𝟘ᶜ  →⟨ proj₁ ∘→ +ᶜ-positive ⟩
        r ·ᶜ γ ≈ᶜ 𝟘ᶜ       →⟨ ·ᶜ-zero-product ⟩
        r ≡ 𝟘 ⊎ γ ≈ᶜ 𝟘ᶜ    →⟨ (λ where
                                 (inj₁ r≡𝟘) → ⊥-elim (r≢𝟘 r≡𝟘)
                                 (inj₂ γ≈𝟘) → γ≈𝟘) ⟩
        γ ≈ᶜ 𝟘ᶜ            →⟨ helper t-n ⊢t (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) ▸t) ⟩
        ⊥                  □ }}
      (natrecₙ v-n) ⊢nr (natrecₘ {γ} {δ} {p} {r} {η} _ _ ▸v _) →
        case inversion-natrec ⊢nr of λ {
          (_ , _ , _ , ⊢v , _) →
        nrᶜ p r γ δ η ≈ᶜ 𝟘ᶜ  →⟨ proj₂ ∘→ proj₂ ∘→ nrᶜ-positive ⟩
        η ≈ᶜ 𝟘ᶜ              →⟨ helper v-n ⊢v ▸v ⟩
        ⊥                    □ }
      (natrecₙ v-n) ⊢nr (natrec-no-nrₘ {η} _ _ ▸v _ _ _ χ≤η _) →
        case inversion-natrec ⊢nr of λ {
          (_ , _ , _ , ⊢v , _) →
        χ ≈ᶜ 𝟘ᶜ  →⟨ ≤ᶜ→≈ᶜ𝟘ᶜ→≈ᶜ𝟘ᶜ χ≤η ⟩
        η ≈ᶜ 𝟘ᶜ  →⟨ helper v-n ⊢v ▸v ⟩
        ⊥        □ }
      (natrecₙ v-n) ⊢nr (natrec-no-nr-glbₘ {γ} {δ} {p} {r} {η} {χ} {x} _ _ ▸v  _ x-glb χ-glb) xη+χ≈𝟘 →
        case ·ᶜ-zero-product (+ᶜ-positive xη+χ≈𝟘 .proj₁) of λ where
          (inj₁ PE.refl) →
            𝟘≰𝟙 (x-glb .proj₁ 0)
          (inj₂ η≈𝟘) →
            let _ , _ , _ , ⊢v , _ = inversion-natrec ⊢nr
            in  helper v-n ⊢v ▸v η≈𝟘
      (emptyrecₙ t-n) ⊢er (emptyrecₘ {γ} {p} γ▸t _ allowed) →
        case inversion-emptyrec ⊢er of λ
          (_ , ⊢t , _) →
        case is-𝟘? p of λ where
          (yes PE.refl) → ⊥-elim $ consistent allowed _ ⊢t
          (no p≢𝟘)      →
            p ·ᶜ γ ≈ᶜ 𝟘ᶜ     →⟨ ·ᶜ-zero-product ⟩
            p ≡ 𝟘 ⊎ γ ≈ᶜ 𝟘ᶜ  →⟨ (λ { (inj₁ p≡𝟘) → ⊥-elim $ p≢𝟘 p≡𝟘; (inj₂ γ≈𝟘) → γ≈𝟘 }) ⟩
            γ ≈ᶜ 𝟘ᶜ          →⟨ helper t-n ⊢t (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) γ▸t) ⟩
            ⊥                □
      (unitrecₙ no-η t-n) ⊢ur (unitrecₘ {γ} {p} {δ} ▸t _ _ ok) →
        case inversion-unitrec ⊢ur of λ {
          (_ , ⊢t , _ , _) →
        case no-η ∘→ nem non-trivial .proj₂ .proj₁ ok of λ
          p≢𝟘 →
          p ·ᶜ γ +ᶜ δ ≈ᶜ 𝟘ᶜ →⟨ proj₁ ∘→ +ᶜ-positive ⟩
          p ·ᶜ γ ≈ᶜ 𝟘ᶜ  →⟨ ·ᶜ-zero-product ⟩
          p ≡ 𝟘 ⊎ γ ≈ᶜ 𝟘ᶜ →⟨ (λ where
                                (inj₁ p≡𝟘) → ⊥-elim (p≢𝟘 p≡𝟘)
                                (inj₂ γ≈𝟘) → γ≈𝟘) ⟩
          γ ≈ᶜ 𝟘ᶜ →⟨ helper t-n ⊢t (▸-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ▸t) ⟩
          ⊥ □ }
      (Jₙ w-n) ⊢J (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} _ _ _ _ _ _ _ ▸w) →
        case inversion-J ⊢J of λ {
          (_ , _ , _ , _ , _ , ⊢w , _) →
        ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ≈ᶜ 𝟘ᶜ   →⟨ ·ᶜ-zero-product ⟩
        ω ≡ 𝟘 ⊎ γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆ ≈ᶜ 𝟘ᶜ  →⟨ (λ where
                                                        (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘)
                                                        (inj₂ hyp) → hyp) ⟩
        γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆ ≈ᶜ 𝟘ᶜ          →⟨ proj₂ ∘→ +ᶜ-positive ∘→
                                                     proj₂ ∘→ +ᶜ-positive ∘→
                                                     proj₂ ∘→ +ᶜ-positive ∘→
                                                     proj₂ ∘→ +ᶜ-positive ⟩
        γ₆ ≈ᶜ 𝟘ᶜ                                  →⟨ helper w-n ⊢w ▸w ⟩
        ⊥                                         □ }
      (Jₙ _) _ (J₀ₘ₁ em _ _ _ _ _ _ _ _) →
        case
          PE.trans (PE.sym em)
            (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁)
        of λ ()
      (Jₙ _) _ (J₀ₘ₂ em _ _ _ _ _ _) →
        case
          PE.trans (PE.sym em)
            (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁)
        of λ ()
      (Kₙ v-n) ⊢K (Kₘ {γ₂} {γ₃} {γ₄} {γ₅} _ _ _ _ _ _ ▸v) →
        case inversion-K ⊢K of λ {
          (_ , _ , _ , _ , ⊢v , _) →
        ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ≈ᶜ 𝟘ᶜ   →⟨ ·ᶜ-zero-product ⟩
        ω ≡ 𝟘 ⊎ γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ ≈ᶜ 𝟘ᶜ  →⟨ (λ where
                                                  (inj₁ ω≡𝟘) → ⊥-elim (ω≢𝟘 ω≡𝟘)
                                                  (inj₂ hyp) → hyp) ⟩
        γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ ≈ᶜ 𝟘ᶜ          →⟨ proj₂ ∘→ +ᶜ-positive ∘→
                                               proj₂ ∘→ +ᶜ-positive ∘→
                                               proj₂ ∘→ +ᶜ-positive ⟩
        γ₅ ≈ᶜ 𝟘ᶜ                            →⟨ helper v-n ⊢v ▸v ⟩
        ⊥                                   □ }
      (Kₙ _) _ (K₀ₘ₁ em _ _ _ _ _ _) →
        case
          PE.trans (PE.sym em)
            (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂)
        of λ ()
      (Kₙ _) _ (K₀ₘ₂ em _ _ _ _ _) →
        case
          PE.trans (PE.sym em)
            (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂)
        of λ ()
      ([]-congₙ _) ⊢bc _ →
        case inversion-[]-cong ⊢bc of λ {
          (_ , _ , _ , _ , ok , _) →
        ⊥-elim $ nem non-trivial .proj₂ .proj₂ .proj₁ ok }
      t-n ⊢t (sub {γ} ▸t χ≤γ) →
        χ ≈ᶜ 𝟘ᶜ  →⟨ ≤ᶜ→≈ᶜ𝟘ᶜ→≈ᶜ𝟘ᶜ χ≤γ ⟩
        γ ≈ᶜ 𝟘ᶜ  →⟨ helper t-n ⊢t ▸t ⟩
        ⊥        □

opaque

  -- If Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 holds for some p (which means that
  -- certain kinds of erased matches are allowed), and if additionally
  -- Σʷ-allowed p 𝟘 holds, then there is a well-typed, well-resourced,
  -- neutral term in a consistent, erasable context.

  neutral-well-resourced₁ :
    Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 →
    Σʷ-allowed p 𝟘 →
    ∃₄ λ n (Γ : Con Term n) (t A : Term n) →
    Consistent Γ ×
    Neutral t ×
    Γ ⊢ t ∷ A ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t
  neutral-well-resourced₁ ok₁ ok₂ =
    case soundness-ℕ-only-source-counterexample₁ ok₁ ok₂ of λ {
      (consistent , ⊢t , ▸t , _) →
    _ , _ , _ , _ , consistent , prodrecₙ (var _) , ⊢t , ▸t }

opaque

  -- If []-cong is allowed, then there is a well-typed,
  -- well-resourced, neutral term in a consistent, erasable context.

  neutral-well-resourced₂ :
    []-cong-allowed s →
    []-cong-allowed-mode s 𝟙ᵐ →
    ∃₄ λ n (Γ : Con Term n) (t A : Term n) →
    Consistent Γ ×
    Neutral t ×
    Γ ⊢ t ∷ A ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t
  neutral-well-resourced₂ ok ok′ =
    case soundness-ℕ-only-source-counterexample₂ ok ok′ of λ {
      (consistent , ⊢t , ▸t , _) →
    _ , _ , _ , _ , consistent , Jₙ ([]-congₙ (var _)) , ⊢t , ▸t }

opaque

  -- If erased-matches-for-J 𝟙ᵐ is equal to not-none sem, then there
  -- is a well-typed, well-resourced, neutral term in a consistent,
  -- erasable context.

  neutral-well-resourced₃ :
    erased-matches-for-J 𝟙ᵐ ≡ not-none sem →
    ∃₄ λ n (Γ : Con Term n) (t A : Term n) →
    Consistent Γ ×
    Neutral t ×
    Γ ⊢ t ∷ A ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t
  neutral-well-resourced₃ ok =
    case soundness-ℕ-only-source-counterexample₃ ok of λ {
      (consistent , ⊢t , ▸t , _) →
    _ , _ , _ , _ , consistent , Jₙ (var _) , ⊢t , ▸t }

opaque

  -- If the K rule is allowed and erased-matches-for-K 𝟙ᵐ is equal to
  -- not-none sem, then there is a well-typed, well-resourced, neutral
  -- term in a consistent, erasable context.

  neutral-well-resourced₄ :
    K-allowed →
    erased-matches-for-K 𝟙ᵐ ≡ not-none sem →
    ∃₄ λ n (Γ : Con Term n) (t A : Term n) →
    Consistent Γ ×
    Neutral t ×
    Γ ⊢ t ∷ A ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t
  neutral-well-resourced₄ ok₁ ok₂ =
    case soundness-ℕ-only-source-counterexample₄ ok₁ ok₂ of λ {
      (consistent , ⊢t , ▸t , _) →
    _ , _ , _ , _ , consistent , Kₙ (var _) , ⊢t , ▸t }

opaque

  -- If Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 and Unitʷ-allowed hold and η-equality
  -- is not allowed for weak unit types, then there is a well-typed,
  -- well-resourced, neutral term in a consistent, erasable context.

  neutral-well-resourced₅ :
    Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 →
    Unitʷ-allowed →
    ¬ Unitʷ-η →
    ∃₄ λ n (Γ : Con Term n) (t A : Term n) →
    Consistent Γ ×
    Neutral t ×
    Γ ⊢ t ∷ A ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t
  neutral-well-resourced₅ ok₁ ok₂ no-η =
    case soundness-ℕ-only-source-counterexample₅ ok₁ ok₂ no-η of λ {
      (consistent , ⊢t , ▸t , _) →
    _ , _ , _ , _ , consistent , unitrecₙ no-η (var _) , ⊢t , ▸t }

opaque

  -- If Emptyrec-allowed 𝟙ᵐ 𝟘 holds, then there is a well-typed,
  -- well-resourced, neutral term in an erasable context.

  neutral-well-resourced₆ :
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    ∃₄ λ n (Γ : Con Term n) (t A : Term n) →
    Neutral t ×
    Γ ⊢ t ∷ A ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t
  neutral-well-resourced₆ ok =
    let ⊢t , ▸t , _ = soundness-ℕ-counterexample₆ {str = non-strict} ok in
    _ , _ , _ , _ , emptyrecₙ (var _) , ⊢t , ▸t
