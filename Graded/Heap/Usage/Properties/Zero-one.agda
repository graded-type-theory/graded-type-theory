------------------------------------------------------------------------
-- Properties of the usage relation for Heaps, Stacks and States.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Usage.Properties.Zero-one
  {a} {M : Set a}
  {𝕄 : Modality M}
  {mode-variant : Mode-variant 𝕄}
  (type-variant : Type-variant)
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  (open Usage-restrictions UR)
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open Modality 𝕄

open import Definition.Untyped M
open import Graded.Context 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Restrictions.Zero-one 𝕄 mode-variant

open import Graded.Heap.Untyped type-variant UR factoring-nr
open import Graded.Heap.Untyped.Properties type-variant UR factoring-nr
open import Graded.Heap.Usage type-variant UR factoring-nr

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
import Tools.Reasoning.PartialOrder as RPo
import Tools.Reasoning.PropositionalEquality as RPe


private variable
  k n : Nat
  γ δ η : Conₘ _
  p q r : M
  m : Mode
  H H′ : Heap _ _
  x : Fin _
  y : Ptr _
  A z s t : Term _
  ρ ρ′ : Wk _ _
  S : Stack _
  c : Cont _
  e : Entryₘ _ _
  e′ : Entry _ _

-- Some properties proven under some assumptions about erased matches

module _ (nem : No-erased-matches′ type-variant UR) where

  opaque

    -- The multiplicity of a well-resourced continuation is not zero
    -- unless it is an erased emptyrec

    ▸∣∣ᶜ≢𝟘 :
      ⦃ Has-well-behaved-zero M semiring-with-meet ⦄ →
      γ ▸ᶜ[ 𝟙ᵐ ] c →
      ¬ ∣ c ∣ᶜ[ 𝟙ᵐ ]≡ 𝟘 ⊎
      ∃₃ λ n (A : Term n) ρ → c ≡ emptyrecₑ 𝟘 A ρ × Emptyrec-allowed 𝟙ᵐ 𝟘
    ▸∣∣ᶜ≢𝟘 (∘ₑ _) = inj₁ λ ∣e∣≡𝟘 → non-trivial (∣∣ᶜ-functional ∘ₑ ∣e∣≡𝟘)
    ▸∣∣ᶜ≢𝟘 = λ where
        lowerₑ → inj₁ (lemma non-trivial lowerₑ)
        (∘ₑ _) → inj₁ (lemma non-trivial ∘ₑ)
        (fstₑ _) → inj₁ (lemma non-trivial fstₑ)
        sndₑ → inj₁ (lemma non-trivial sndₑ)
        (prodrecₑ _ ok) →
          inj₁ (lemma (nem non-trivial .proj₁ ok) prodrecₑ)
        (natrecₑ _ _ _) →
          inj₁ (lemma nr₂≢𝟘 (natrecₑ has-nrₑ))
        (natrec-no-nrₑ _ _ _ _) →
          inj₁ λ { (natrecₑ x) → lemma-nr x refl}
        (unitrecₑ _ ok no-η) →
          inj₁ (lemma (no-η ∘→ nem non-trivial .proj₂ .proj₁ ok) unitrecₑ)
        (emptyrecₑ {p} ok) →
          case is-𝟘? p of λ where
            (yes refl) → inj₂ (_ , _ , _ , refl , ok)
            (no p≢𝟘) → inj₁ (lemma p≢𝟘 emptyrecₑ)
        (Jₑ _) →
          inj₁ (lemma ω≢𝟘
            (Jₑ (subst (∣J_, _ , _ ∣≡ _)
                  (sym (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₁))
                  J-none)))
        (Kₑ _) →
          inj₁ (lemma ω≢𝟘
            (Kₑ (subst (∣K_, _ ∣≡ _)
                  (sym (nem non-trivial .proj₂ .proj₂ .proj₂ .proj₂))
                  K-none)))
        ([]-congₑ ok) →
          inj₁ λ _ → nem non-trivial .proj₂ .proj₂ .proj₁ ok
      where
      lemma :  p ≢ r → ∣ c ∣ᶜ[ m ]≡ p → ∣ c ∣ᶜ[ m ]≡ r → ⊥
      lemma p≢r ≡p ≡r = p≢r (∣∣ᶜ-functional ≡p ≡r)
      lemma-nr : ∣natrec p , r ∣≡ q → q ≢ 𝟘
      lemma-nr has-nrₑ nr₂≡𝟘 = nr₂≢𝟘 nr₂≡𝟘
      lemma-nr (no-nrₑ x) refl = 𝟘≰𝟙 (x .proj₁ 0)

  opaque

    -- The multiplicity of a well-resourced stack is either not zero
    -- or contains an erased application of emptyrec

    ▸∣∣≢𝟘 : ⦃ Has-well-behaved-zero M semiring-with-meet ⦄
           → γ ▸ˢ S → ¬ ∣ S ∣≡ 𝟘 ⊎ (emptyrec 𝟘 ∈ S × Emptyrec-allowed 𝟙ᵐ 𝟘)
    ▸∣∣≢𝟘 ε = inj₁ λ ≡𝟘 → non-trivial (∣∣-functional ε ≡𝟘)
    ▸∣∣≢𝟘 (▸ˢ∙ ∣S∣≡ ▸c ▸S) =
      case ▸∣∣≢𝟘 ▸S of λ where
        (inj₂ (x , ok)) → inj₂ (there x , ok)
        (inj₁ ∣S∣≢𝟘) →
          case ▸∣∣ᶜ≢𝟘 (subst (_ ▸ᶜ[_] _)
                        (≢𝟘→⌞⌟≡𝟙ᵐ (λ {refl → ∣S∣≢𝟘 ∣S∣≡})) ▸c) of λ where
            (inj₂ (_ , _ , _ , refl , ok)) → inj₂ (here , ok)
            (inj₁ ∣c∣≢𝟘) → inj₁ λ ∣cS∣≡ →
              let q , r , ∣c∣≡q , ∣S∣≡r , 𝟘≡rq = ∣∣∙-inv ∣cS∣≡
              in  case is-𝟘? r of λ where
                (yes r≡𝟘) → ∣S∣≢𝟘 (subst (∣ _ ∣≡_) r≡𝟘 ∣S∣≡r)
                (no r≢𝟘) →
                  case zero-product (sym 𝟘≡rq) of λ where
                    (inj₁ r≡𝟘) → ⊥-elim (r≢𝟘 r≡𝟘)
                    (inj₂ q≡𝟘) → ∣c∣≢𝟘 (subst₂ (∣ _ ∣ᶜ[_]≡_) (≢𝟘→⌞⌟≡𝟙ᵐ r≢𝟘) q≡𝟘 ∣c∣≡q)
