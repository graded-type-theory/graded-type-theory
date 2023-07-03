------------------------------------------------------------------------
-- Assumptions used to state some theorems in Graded.FullReduction
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.Restrictions

module Graded.FullReduction.Assumptions
  {a} {M : Set a}
  (𝕄 : Modality M)
  (R : Type-restrictions M)
  where

open Modality 𝕄
open Type-restrictions R

open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

open import Tools.Bool
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Sum

private variable
  p q r : M

-- The theorems in Graded.FullReduction are proved under the
-- assumption that the following property holds.

record Full-reduction-assumptions : Set a where
  no-eta-equality
  field
    -- If the unit type (with η-equality) is allowed, then 𝟙 ≤ 𝟘.
    𝟙≤𝟘 : Unit-allowed → 𝟙 ≤ 𝟘

    -- If a Σ-type with η-equality and the "first component
    -- quantity" p is allowed, then either p ≡ 𝟙 or p ≡ 𝟘, 𝟘ᵐ is
    -- allowed and 𝟙 ≤ 𝟘.
    ≡𝟙⊎𝟙≤𝟘 : Σₚ-allowed p q → p ≡ 𝟙 ⊎ p ≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘

-- An alternative way to state Full-reduction-assumptions.

record Full-reduction-assumptions′ : Set a where
  no-eta-equality
  field
    -- If the unit type (with η-equality) is allowed, then 𝟘 must be
    -- the largest quantity.
    ≤𝟘 : Unit-allowed → p ≤ 𝟘

    -- If a Σ-type with η-equality and the "first component
    -- quantity" p is allowed, then p ·_ must be increasing.
    ·-increasing : Σₚ-allowed p q → r ≤ p · r

    -- If a Σ-type with η-equality and the "first component
    -- quantity" p is allowed, and ⌞ p ⌟ is 𝟙ᵐ, then p ≤ 𝟙 must hold.
    ⌞⌟≡𝟙ᵐ→≤𝟙 : Σₚ-allowed p q → ⌞ p ⌟ ≡ 𝟙ᵐ → p ≤ 𝟙

-- Full-reduction-assumptions is logically equivalent to
-- Full-reduction-assumptions′.

Full-reduction-assumptions⇔Full-reduction-assumptions′ :
  Full-reduction-assumptions ⇔ Full-reduction-assumptions′
Full-reduction-assumptions⇔Full-reduction-assumptions′ =
    (λ as → record
       { ≤𝟘 = λ {p = p} →
           Unit-allowed  →⟨ 𝟙≤𝟘 as ⟩

           𝟙 ≤ 𝟘         →⟨ (λ 𝟙≤𝟘 → begin

             p                   ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · p               ≤⟨ ·-monotoneˡ 𝟙≤𝟘 ⟩
             𝟘 · p               ≡⟨ ·-zeroˡ _ ⟩
             𝟘                   ∎) ⟩

           p ≤ 𝟘         □
       ; ·-increasing = λ {p = p} {q = q} {r = r} →
           Σₚ-allowed p q                        →⟨ ≡𝟙⊎𝟙≤𝟘 as ⟩

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
           Σₚ-allowed p q                        →⟨ ≡𝟙⊎𝟙≤𝟘 as ⟩
           p ≡ 𝟙 ⊎ p ≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘  →⟨ (λ { (inj₁ p≡𝟙) → inj₁ (≤-reflexive p≡𝟙)
                                                       ; (inj₂ (p≡𝟘 , ok , _)) → inj₂ (ok , p≡𝟘)
                                                       }) ⟩
           p ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed × p ≡ 𝟘          →⟨ ⌞⌟≡𝟙→⇔⊎𝟘ᵐ×≡𝟘 .proj₂ ⟩
           (⌞ p ⌟ ≡ 𝟙ᵐ → p ≤ 𝟙)                  □
       })
  , (λ as → record
       { 𝟙≤𝟘    = ≤𝟘 as
       ; ≡𝟙⊎𝟙≤𝟘 = λ {p = p} {q = q} →
           Σₚ-allowed p q                          →⟨ (λ ok → ·-increasing as ok , ⌞⌟≡𝟙ᵐ→≤𝟙 as ok) ⟩
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