------------------------------------------------------------------------
-- An investigation of to what degree weak Σ-types can emulate strong
-- Σ-types, and vice versa, for the Zero-one mode structure.
------------------------------------------------------------------------

-- This module contains parts of an investigation of to what degree
-- weak Σ-types can emulate strong Σ-types, and vice versa. This
-- investigation was prompted by a question asked by an anonymous
-- reviewer. See also Definition.Untyped.Sigma, which contains some
-- basic definitions, Definition.Typed.Properties.Admissible.Sigma
-- as well as Definition.Typed.Consequences.Admissible.Sigma, which
-- contain properties related to typing. This module contains
-- properties related to usage. See also Graded.Derived.Sigma for
-- usage properties that are not specific to the Zero-one mode
-- structure.

import Graded.Modality
import Graded.Mode.Instances.Zero-one.Variant
import Graded.Mode.Instances.Zero-one
open import Graded.Usage.Restrictions

module Graded.Derived.Sigma.Zero-one
  {a} {M : Set a}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Graded.Mode.Instances.Zero-one.Variant 𝕄)
  {mode-variant : Mode-variant}
  (open Graded.Mode.Instances.Zero-one mode-variant)
  (UR : Usage-restrictions 𝕄 Zero-one-isMode)
  where

open Modality 𝕄
open Mode-variant mode-variant
open Usage-restrictions UR

open import Graded.Context 𝕄
import Graded.Derived.Sigma UR as Σ
open import Graded.Modality.Properties 𝕄
open import Graded.Usage UR
open import Graded.Usage.Properties UR

open import Definition.Untyped M
open import Definition.Untyped.Sigma 𝕄

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

private variable
  n        : Nat
  A B t u  : Term _
  s        : Strength
  p q r r′ : M
  γ δ η    : Conₘ _
  m        : Mode

------------------------------------------------------------------------
-- Some private lemmas related to the modality

private

  -- Some lemmas used below.

  opaque

    ≢𝟘⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ : p ≢ 𝟘 ⊎ Trivial → ⌞ p ⌟ PE.≡ 𝟙ᵐ
    ≢𝟘⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ (inj₁ p≢𝟘) = ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘
    ≢𝟘⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ (inj₂ 𝟙≡𝟘) = ≡-trivialᵐ (Trivial→Trivialᵐ 𝟙≡𝟘)

  opaque

    𝟘≢⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ : 𝟘 ≢ p ⊎ Trivial → ⌞ p ⌟ PE.≡ 𝟙ᵐ
    𝟘≢⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ (inj₁ 𝟘≢p) = ≢𝟘⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ (inj₁ (𝟘≢p ∘→ PE.sym))
    𝟘≢⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ (inj₂ 𝟙≡𝟘) = ≢𝟘⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ (inj₂ 𝟙≡𝟘)

  opaque

    𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ :
      ∀ m → ¬ 𝟘 ≤ 𝟙 ⊎ Trivial ⊎ m ≢ 𝟙ᵐ → m ᵐ· (𝟘 ∧ 𝟙) PE.≡ m
    𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ = λ where
        m (inj₁ 𝟘≰𝟙) → begin
          m ᵐ· (𝟘 ∧ 𝟙) ≡⟨ ·ᵐ-congˡ (𝟘≢⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ (inj₁ 𝟘≰𝟙)) ⟩
          m ·ᵐ 𝟙ᵐ      ≡⟨ ·ᵐ-identityʳ _ ⟩
          m            ∎
        m (inj₂ (inj₁ 𝟙≡𝟘)) → begin
          m ᵐ· (𝟘 ∧ 𝟙) ≡⟨ ·ᵐ-congˡ (𝟘≢⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ (inj₂ 𝟙≡𝟘)) ⟩
          m ·ᵐ 𝟙ᵐ      ≡⟨ ·ᵐ-identityʳ _ ⟩
          m            ∎
        𝟘ᵐ (inj₂ (inj₂ m≢𝟙ᵐ)) → begin
          𝟘ᵐ ᵐ· (𝟘 ∧ 𝟙)  ≡˘⟨ ᵐ·-congʳ 𝟘ᵐ?≡𝟘ᵐ ⟩
          𝟘ᵐ? ᵐ· (𝟘 ∧ 𝟙) ≡⟨ ᵐ·-zeroˡ ⟩
          𝟘ᵐ?            ≡⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
          𝟘ᵐ             ∎
        𝟙ᵐ (inj₂ (inj₂ m≢𝟙ᵐ)) →
          ⊥-elim (m≢𝟙ᵐ PE.refl)
      where
      open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Usage lemmas for prodrecˢ

opaque

  -- A usage lemma for prodrecˢ.

  prodrecˢₘ :
    (m ᵐ· r · p PE.≡ 𝟙ᵐ → p ≤ 𝟙) →
    γ ▸[ m ᵐ· r ] t →
    δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
    (⌜ m ⌝ · r · (𝟙 + p)) ·ᶜ γ +ᶜ δ ▸[ m ] prodrecˢ p t u
  prodrecˢₘ mrp≡𝟙→p≤𝟙 =
    Σ.prodrecˢₘ (mrp≡𝟙→p≤𝟙 ∘→ ⌜⌝≢𝟘→≡𝟙ᵐ)

opaque

  -- A variant of the main usage lemma for prodrecˢ with the mode set
  -- to 𝟘ᵐ.

  prodrecˢₘ-𝟘ᵐ :
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    γ ▸[ 𝟘ᵐ ] t →
    δ ∙ 𝟘 ∙ 𝟘 ▸[ 𝟘ᵐ ] u →
    δ ▸[ 𝟘ᵐ ] prodrecˢ p t u
  prodrecˢₘ-𝟘ᵐ ▸t ▸u =
    ▸-cong 𝟘ᵐ?≡𝟘ᵐ
      (Σ.prodrecˢₘ-𝟘ᵐ 𝟘ᵐ-allowed→¬Trivialᵐ′ (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t)
        (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸u))

opaque

  -- A variant of the main usage lemma for prodrecˢ with the mode set to
  -- 𝟙ᵐ and the quantity p to 𝟘.

  prodrecˢₘ-𝟙ᵐ-𝟘 :
    𝟘 ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed →
    γ ▸[ ⌞ r ⌟ ] t →
    δ ∙ 𝟘 ∙ r ▸[ 𝟙ᵐ ] u →
    r ·ᶜ γ +ᶜ δ ▸[ 𝟙ᵐ ] prodrecˢ 𝟘 t u
  prodrecˢₘ-𝟙ᵐ-𝟘 ok =
    Σ.prodrecˢₘ-𝟙ᵐ-𝟘 (⊎.map idᶠ 𝟘ᵐ-allowed→¬Trivialᵐ ok)

------------------------------------------------------------------------
-- A usage lemma for prodrec⟨_⟩

opaque
  unfolding prodrec⟨_⟩

  -- A usage lemma for prodrec⟨_⟩.

  ▸prodrec⟨⟩ :
    (s PE.≡ 𝕤 → m ᵐ· r · p PE.≡ 𝟙ᵐ → p ≤ 𝟙) →
    (s PE.≡ 𝕤 → r′ ≤ ⌜ m ⌝ · r · (𝟙 + p)) →
    (s PE.≡ 𝕨 → r′ ≤ r) →
    (s PE.≡ 𝕨 → Prodrec-allowed m r p q) →
    (s PE.≡ 𝕨 → ∃ λ η → η ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A) →
    γ ▸[ m ᵐ· r ] t →
    δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
    r′ ·ᶜ γ +ᶜ δ ▸[ m ] prodrec⟨ s ⟩ r p q A t u
  ▸prodrec⟨⟩ hyp =
    Σ.▸prodrec⟨⟩ (λ s≡𝕤 ≢𝟘 → hyp s≡𝕤 (⌜⌝≢𝟘→≡𝟙ᵐ ≢𝟘))

------------------------------------------------------------------------
-- An investigation of different potential implementations of a first
-- projection for weak Σ-types

opaque

  -- An inversion lemma for fstʷ′ with the mode set to 𝟙ᵐ.

  inv-usage-fstʷ′-≢𝟘-𝟙ᵐ :
    r ≢ 𝟘 ⊎ Trivial →
    γ ▸[ 𝟙ᵐ ] Σ.fstʷ′ r p q A t →
    ∃₂ λ η δ →
      γ ≤ᶜ r ·ᶜ η ×
      η ▸[ 𝟙ᵐ ] t ×
      δ ▸[ 𝟘ᵐ? ] A ×
      r · p ≤ 𝟙 ×
      r ≤ 𝟘 ×
      Prodrec-allowed 𝟙ᵐ r p q
  inv-usage-fstʷ′-≢𝟘-𝟙ᵐ r≢𝟘⊎𝟙≡𝟘 =
    Σ.inv-usage-fstʷ′-≢𝟘-𝟙ᵐ (≢𝟘⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ r≢𝟘⊎𝟙≡𝟘)

opaque

  -- An inversion lemma for fstʷ′ with the mode set to 𝟙ᵐ and "r" set to
  -- 𝟘 ∧ 𝟙.

  inv-usage-fstʷ′-𝟘∧𝟙-𝟙ᵐ :
    ¬ 𝟘 ≤ 𝟙 ⊎ Trivial →
    γ ▸[ 𝟙ᵐ ] Σ.fstʷ′ (𝟘 ∧ 𝟙) p q A t →
    ∃₂ λ η δ →
      γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ 𝟙ᵐ ] t ×
      δ ▸[ 𝟘ᵐ? ] A ×
      𝟘 ∧ p ≤ 𝟙 ×
      Prodrec-allowed 𝟙ᵐ (𝟘 ∧ 𝟙) p q
  inv-usage-fstʷ′-𝟘∧𝟙-𝟙ᵐ 𝟘≰𝟙⊎𝟙≡𝟘 =
    Σ.inv-usage-fstʷ′-𝟘∧𝟙-𝟙ᵐ (𝟘≢⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ 𝟘≰𝟙⊎𝟙≡𝟘)

------------------------------------------------------------------------
-- Inversion lemmas for usage for fstʷ

opaque

  -- An inversion lemma for fstʷ.

  inv-usage-fstʷ :
    ¬ 𝟘 ≤ 𝟙 ⊎ Trivial ⊎ m ≢ 𝟙ᵐ →
    γ ▸[ m ] fstʷ p A t →
    ∃₂ λ η δ →
      γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ m ] t ×
      δ ▸[ 𝟘ᵐ? ] A ×
      𝟘 ∧ ⌜ m ⌝ · p ≤ ⌜ m ⌝ ×
      Prodrec-allowed m (𝟘 ∧ 𝟙) p 𝟘
  inv-usage-fstʷ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ =
    Σ.inv-usage-fstʷ (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ)

opaque

  -- An inversion lemma for fstʷ with the mode set to 𝟘ᵐ.

  inv-usage-fstʷ-𝟘ᵐ :
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    γ ▸[ 𝟘ᵐ ] fstʷ p A t →
    ∃ λ δ →
      γ ≤ᶜ 𝟘ᶜ × 𝟘ᶜ ▸[ 𝟘ᵐ ] t ×
      δ ▸[ 𝟘ᵐ ] A
  inv-usage-fstʷ-𝟘ᵐ ▸fstʷ =
    let _ , γ≤𝟘 , ▸t , ▸A = Σ.inv-usage-fstʷ-𝟘ᵐ 𝟘ᵐ-allowed→¬Trivialᵐ′
                             (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸fstʷ)
    in  _ , γ≤𝟘 , ▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t , ▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A

opaque

  -- An inversion lemma for fstʷ with the mode set to 𝟙ᵐ.

  inv-usage-fstʷ-𝟙ᵐ :
    ¬ 𝟘 ≤ 𝟙 ⊎ Trivial →
    γ ▸[ 𝟙ᵐ ] fstʷ p A t →
    ∃₂ λ η δ →
      γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ 𝟙ᵐ ] t ×
      δ ▸[ 𝟘ᵐ? ] A ×
      𝟘 ∧ p ≤ 𝟙 ×
      Prodrec-allowed 𝟙ᵐ (𝟘 ∧ 𝟙) p 𝟘
  inv-usage-fstʷ-𝟙ᵐ 𝟘≰𝟙⊎𝟙≡𝟘 =
    Σ.inv-usage-fstʷ-𝟙ᵐ (𝟘≢⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ 𝟘≰𝟙⊎𝟙≡𝟘)

------------------------------------------------------------------------
-- Usage lemmas for fstʷ

opaque

  -- A usage lemma for fstʷ.

  fstʷₘ :
    ¬ 𝟘 ≤ 𝟙 ⊎ Trivial ⊎ m ≢ 𝟙ᵐ →
    𝟘 ∧ ⌜ m ⌝ · p ≤ ⌜ m ⌝ →
    Prodrec-allowed m (𝟘 ∧ 𝟙) p 𝟘 →
    γ ▸[ m ] t →
    δ ▸[ 𝟘ᵐ? ] A →
    𝟘ᶜ ∧ᶜ γ ▸[ m ] fstʷ p A t
  fstʷₘ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ =
    Σ.fstʷₘ (PE.sym (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ))

opaque

  -- A usage lemma for fstʷ with the mode set to 𝟘ᵐ.

  fstʷₘ-𝟘ᵐ :
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) p 𝟘 →
    γ ▸[ 𝟘ᵐ ] t →
    δ ▸[ 𝟘ᵐ ] A →
    γ ▸[ 𝟘ᵐ ] fstʷ p A t
  fstʷₘ-𝟘ᵐ  ok ▸t ▸A =
    ▸-cong 𝟘ᵐ?≡𝟘ᵐ
      (Σ.fstʷₘ-𝟘ᵐ 𝟘ᵐ-allowed→¬Trivialᵐ′
        (PE.subst (λ m → Prodrec-allowed m _ _ _) (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ok)
        (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t)
        (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A))

opaque

  -- A usage lemma for fstʷ with the mode set to 𝟙ᵐ.

  fstʷₘ-𝟙ᵐ :
    ¬ 𝟘 ≤ 𝟙 ⊎ Trivial →
    𝟘 ∧ p ≤ 𝟙 →
    Prodrec-allowed 𝟙ᵐ (𝟘 ∧ 𝟙) p 𝟘 →
    γ ▸[ 𝟙ᵐ ] t →
    δ ▸[ 𝟘ᵐ? ] A →
    𝟘ᶜ ∧ᶜ γ ▸[ 𝟙ᵐ ] fstʷ p A t
  fstʷₘ-𝟙ᵐ 𝟘≰𝟙⊎𝟙≢𝟘 = Σ.fstʷₘ-𝟙ᵐ (𝟘≢⊎𝟙≡𝟘→⌞⌟≡𝟙ᵐ 𝟘≰𝟙⊎𝟙≢𝟘)

------------------------------------------------------------------------
-- Inversion lemmas for usage for sndʷ

opaque

  -- An inversion lemma for sndʷ.

  inv-usage-sndʷ :
    ¬ 𝟘 ≤ 𝟙 ⊎ Trivial ⊎ m ≢ 𝟙ᵐ →
    ∀ B →
    γ ▸[ m ] sndʷ p q A B t →
    ∃₂ λ η δ →
      γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ m ] t ×
      δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fstʷ p (wk1 A) (var x0) ]↑ ×
      Prodrec-allowed m (𝟘 ∧ 𝟙) p q
  inv-usage-sndʷ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ =
    Σ.inv-usage-sndʷ (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ)

opaque

  -- An inversion lemma for sndʷ with the mode set to 𝟘ᵐ.

  inv-usage-sndʷ-𝟘ᵐ :
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    ∀ B →
    γ ▸[ 𝟘ᵐ ] sndʷ p q A B t →
    ∃ λ δ →
      γ ≤ᶜ 𝟘ᶜ × 𝟘ᶜ ▸[ 𝟘ᵐ ] t ×
      δ ∙ 𝟘 ▸[ 𝟘ᵐ ] B [ fstʷ p (wk1 A) (var x0) ]↑
  inv-usage-sndʷ-𝟘ᵐ B ▸sndʷ =
    let _ , γ≤ , ▸t , ▸B = Σ.inv-usage-sndʷ-𝟘ᵐ 𝟘ᵐ-allowed→¬Trivialᵐ′ B
                             (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸sndʷ)
    in _ , γ≤ , ▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸t , ▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸B

------------------------------------------------------------------------
-- Usage lemmas for sndʷ

opaque

  -- A usage lemma for sndʷ.

  sndʷₘ :
    ¬ 𝟘 ≤ 𝟙 ⊎ Trivial ⊎ m ≢ 𝟙ᵐ →
    Prodrec-allowed m (𝟘 ∧ 𝟙) p q →
    ∀ B →
    γ ▸[ m ] t →
    δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fstʷ p (wk1 A) (var x0) ]↑ →
    𝟘ᶜ ∧ᶜ γ ▸[ m ] sndʷ p q A B t
  sndʷₘ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ =
    Σ.sndʷₘ (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ)


opaque

  -- A usage lemma for sndʷ with the mode set to 𝟘ᵐ.

  sndʷₘ-𝟘ᵐ :
    ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
    Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) p q →
    ∀ B →
    γ ▸[ 𝟘ᵐ ] t →
    δ ∙ 𝟘 ▸[ 𝟘ᵐ ] B [ fstʷ p (wk1 A) (var x0) ]↑ →
    γ ▸[ 𝟘ᵐ ] sndʷ p q A B t
  sndʷₘ-𝟘ᵐ ok B ▸t ▸B =
    ▸-cong 𝟘ᵐ?≡𝟘ᵐ
      (Σ.sndʷₘ-𝟘ᵐ 𝟘ᵐ-allowed→¬Trivialᵐ′
        (PE.subst (λ m → Prodrec-allowed m _ _ _) (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ok) B
        (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸t)
        (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸B))

------------------------------------------------------------------------
-- Usage lemmas for fst⟨_⟩ and snd⟨_⟩

opaque
  unfolding fst⟨_⟩

  -- A usage lemma for fst⟨_⟩.

  ▸fst⟨⟩ :
    (s PE.≡ 𝕨 → ¬ 𝟘 ≤ 𝟙 ⊎ Trivial ⊎ m ≢ 𝟙ᵐ) →
    (s PE.≡ 𝕨 → Prodrec-allowed m (𝟘 ∧ 𝟙) p 𝟘) →
    (m PE.≡ 𝟙ᵐ → p ≤ 𝟙) →
    γ ▸[ m ] t →
    (s PE.≡ 𝕨 → δ ▸[ 𝟘ᵐ? ] A) →
    𝟘ᶜ ∧ᶜ γ ▸[ m ] fst⟨ s ⟩ p A t
  ▸fst⟨⟩ {m} {p} hyp₁ hyp₂ hyp₃ =
    Σ.▸fst⟨⟩ (PE.sym ∘→ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ ∘→ hyp₁) hyp₂
      (hyp₃ ∘→ ⌜⌝≢𝟘→≡𝟙ᵐ)
      (λ _ _ → hyp₄)
      λ _ → hyp₅
    where
    hyp₄ : m ᵐ· p PE.≡ m
    hyp₄ =
      case is-𝟘? p of λ where
        (no p≢𝟘) → ≢𝟘→ᵐ·≡ p≢𝟘
        (yes PE.refl) → 𝟘ᵐ-allowed-elim
          (λ ok → case PE.singleton m of λ where
            (𝟘ᵐ , PE.refl) →
              PE.refl
            (𝟙ᵐ , PE.refl) →
              ⊥-elim (𝟘≰𝟙 ⦃ 𝟘-well-behaved ok ⦄ (hyp₃ PE.refl)))
          Mode-propositional-without-𝟘ᵐ
    hyp₅ : ⌜ m ⌝ ≢ 𝟘 → 𝟙 ≤ ⌜ ⌞ p ⌟ ⌝
    hyp₅ ⌜m⌝≢𝟘 = let open ≤-reasoning in
      case is-𝟘? p of λ where
        (no p≢𝟘) → begin
          𝟙         ≡⟨⟩
          ⌜ 𝟙ᵐ ⌝    ≡˘⟨ ⌜⌝-cong (≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘) ⟩
          ⌜ ⌞ p ⌟ ⌝ ∎
        (yes PE.refl) → 𝟘ᵐ-allowed-elim
          (λ ok → case PE.singleton m of λ where
            (𝟘ᵐ , PE.refl) →
              ⊥-elim (⌜m⌝≢𝟘 PE.refl)
            (𝟙ᵐ , PE.refl) →
              ⊥-elim (𝟘≰𝟙 ⦃ 𝟘-well-behaved ok ⦄ (hyp₃ PE.refl)))
          λ not-ok → begin
            𝟙         ≡⟨⟩
            ⌜ 𝟙ᵐ ⌝    ≡⟨ ⌜⌝-cong {m₁ = 𝟙ᵐ} {m₂ = ⌞ 𝟘 ⌟}
                           (Mode-propositional-without-𝟘ᵐ not-ok) ⟩
            ⌜ ⌞ 𝟘 ⌟ ⌝ ∎

opaque
  unfolding fst⟨_⟩ snd⟨_⟩

  -- A usage lemma for snd⟨_⟩.

  ▸snd⟨⟩ :
    (s PE.≡ 𝕨 → ¬ 𝟘 ≤ 𝟙 ⊎ Trivial ⊎ m ≢ 𝟙ᵐ) →
    (s PE.≡ 𝕨 → Prodrec-allowed m (𝟘 ∧ 𝟙) p q) →
    γ ▸[ m ] t →
    (s PE.≡ 𝕨 →
     δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fst⟨ s ⟩ p (wk1 A) (var x0) ]↑) →
    𝟘ᶜ ∧ᶜ γ ▸[ m ] snd⟨ s ⟩ p q A B t
  ▸snd⟨⟩ hyp =
    Σ.▸snd⟨⟩ (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ ∘→ hyp)
