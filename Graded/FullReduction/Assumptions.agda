------------------------------------------------------------------------
-- Assumptions used to state some theorems in Graded.FullReduction
------------------------------------------------------------------------

open import Graded.Modality
import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant
open import Definition.Typed.Restrictions
open import Graded.Usage.Restrictions

module Graded.FullReduction.Assumptions
  {a} {M : Set a}
  {𝕄 : Modality M}
  (mode-variant : Mode-variant 𝕄)
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR
open Mode-variant mode-variant

open import Definition.Untyped M

open import Graded.Modality.Properties 𝕄

open import Tools.Bool
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Sum as ⊎

private variable
  p q r : M
  s     : Strength

-- The theorems in Graded.FullReduction are proved under the
-- assumption that the following property holds.

record Full-reduction-assumptions : Set a where
  no-eta-equality
  field
    -- If Unit s is allowed and η-equality is allowed for such types,
    -- then either s is 𝕤 and Unitˢ is allowed to be used as a sink,
    -- or 𝟙 ≤ 𝟘.
    sink⊎𝟙≤𝟘 :
      Unit-allowed s → Unit-with-η s → s ≡ 𝕤 × Starˢ-sink ⊎ 𝟙 ≤ 𝟘

    -- If a strong Σ-type with the "first component quantity" p is
    -- allowed, then either p ≡ 𝟙, or p ≡ 𝟘, 𝟘ᵐ is allowed and 𝟙 ≤ 𝟘.
    ≡𝟙⊎𝟙≤𝟘 : Σˢ-allowed p q → p ≡ 𝟙 ⊎ p ≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘

-- An alternative way to state Full-reduction-assumptions.

record Full-reduction-assumptions′ : Set a where
  no-eta-equality
  field
    -- If Unit s is allowed and η-equality is allowed for such types,
    -- then either s is 𝕤 and Unitˢ is allowed to be used as a sink,
    -- or 𝟘 is the largest grade.
    sink⊎≤𝟘 :
      Unit-allowed s → Unit-with-η s →
      s ≡ 𝕤 × Starˢ-sink ⊎ (∀ {p} → p ≤ 𝟘)

    -- If a strong Σ-type with the "first component quantity" p is
    -- allowed, then p ·_ must be increasing.
    ·-increasing : Σˢ-allowed p q → r ≤ p · r

    -- If a strong Σ-type with the "first component quantity" p is
    -- allowed, and ⌞ p ⌟ is 𝟙ᵐ, then p ≤ 𝟙 must hold.
    ⌞⌟≡𝟙ᵐ→≤𝟙 : Σˢ-allowed p q → ⌞ p ⌟ ≡ 𝟙ᵐ → p ≤ 𝟙

-- Full-reduction-assumptions is logically equivalent to
-- Full-reduction-assumptions′.

Full-reduction-assumptions⇔Full-reduction-assumptions′ :
  Full-reduction-assumptions ⇔ Full-reduction-assumptions′
Full-reduction-assumptions⇔Full-reduction-assumptions′ =
    (λ as → record
       { sink⊎≤𝟘 =
           λ ok → ⊎.map idᶠ (≤𝟘⇔𝟙≤𝟘 .proj₂) ∘→ sink⊎𝟙≤𝟘 as ok
       ; ·-increasing = λ {p = p} {q = q} {r = r} →
           Σˢ-allowed p q                        →⟨ ≡𝟙⊎𝟙≤𝟘 as ⟩

           p ≡ 𝟙 ⊎ p ≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘  →⟨ (λ { (inj₁ refl) → begin

             r                                             ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · r                                         ∎
                                                       ; (inj₂ (refl , _ , 𝟙≤𝟘)) → begin
             r                                             ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · r                                         ≤⟨ ·-monotoneˡ 𝟙≤𝟘 ⟩
             𝟘 · r                                         ∎
                                                       }) ⟩
           r ≤ p · r                             □
       ; ⌞⌟≡𝟙ᵐ→≤𝟙 = λ {p = p} {q = q} →
           Σˢ-allowed p q                        →⟨ ≡𝟙⊎𝟙≤𝟘 as ⟩
           p ≡ 𝟙 ⊎ p ≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘  →⟨ ⊎.map ≤-reflexive (λ (p≡𝟘 , ok , _) → (ok , p≡𝟘)) ⟩
           p ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘          →⟨ ⌞⌟≡𝟙→⇔⊎𝟘ᵐ×≡𝟘 .proj₂ ⟩
           (⌞ p ⌟ ≡ 𝟙ᵐ → p ≤ 𝟙)                  □
       })
  , (λ as → record
       { sink⊎𝟙≤𝟘 =
           λ ok → ⊎.map idᶠ (≤𝟘⇔𝟙≤𝟘 .proj₁) ∘→ sink⊎≤𝟘 as ok
       ; ≡𝟙⊎𝟙≤𝟘 = λ {p = p} {q = q} →
           Σˢ-allowed p q                          →⟨ (λ ok → ·-increasing as ok , ⌞⌟≡𝟙ᵐ→≤𝟙 as ok) ⟩
           𝟙 ≤ p · 𝟙 × (⌞ p ⌟ ≡ 𝟙ᵐ → p ≤ 𝟙)        →⟨ (λ (𝟙≤p1 , ⌞⌟≡𝟙ᵐ→≤𝟙) →
                                                          subst (_ ≤_) (·-identityʳ _) 𝟙≤p1
                                                        , ⌞⌟≡𝟙→⇔⊎𝟘ᵐ×≡𝟘 .proj₁ ⌞⌟≡𝟙ᵐ→≤𝟙) ⟩
           𝟙 ≤ p × (p ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘)  →⟨ (λ where
                                                        (𝟙≤p , inj₁ p≤𝟙)         → inj₁ (≤-antisym p≤𝟙 𝟙≤p)
                                                        (𝟙≤𝟘 , inj₂ (ok , refl)) → inj₂ (refl , ok , 𝟙≤𝟘)) ⟩
           p ≡ 𝟙 ⊎ p ≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘    □
       })
  where
  open Full-reduction-assumptions
  open Full-reduction-assumptions′
  open Tools.Reasoning.PartialOrder ≤-poset
