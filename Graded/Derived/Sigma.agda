------------------------------------------------------------------------
-- Properties related to usage and Σ
------------------------------------------------------------------------

-- This module contains parts of an investigation of to what degree
-- weak Σ-types can emulate strong Σ-types, and vice versa. This
-- investigation was prompted by a question asked by an anonymous
-- reviewer. See also Definition.Untyped.Sigma, which contains some
-- basic definitions, and Definition.Typed.Properties.Admissible.Sigma
-- as well as Definition.Typed.Consequences.Admissible.Sigma, which
-- contain properties related to typing. This module contains
-- properties related to usage. See also Graded.Derivied.Sigma.Zero-one
-- for properties related to the Zero-one mode instance.

import Graded.Modality
import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Derived.Sigma
  {a b} {M : Set a} {Mode : Set b}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Graded.Mode Mode 𝕄)
  {𝐌 : IsMode}
  (UR : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR
open import Graded.Usage.Weakening UR
open import Graded.Substitution UR
open import Graded.Substitution.Properties UR

open import Definition.Untyped M
open import Definition.Untyped.Sigma 𝕄

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n        : Nat
  A B t u  : Term _
  s        : Strength
  p q r r′ : M
  γ δ η    : Conₘ _
  m        : Mode

------------------------------------------------------------------------
-- An investigation of to what degree weak Σ-types can emulate strong
-- Σ-types, and vice versa

-- The first part of this module (at the time of writing up to and
-- including the section "Usage lemmas for fst⟨_⟩ and snd⟨_⟩")
-- contains parts of an investigation of to what degree weak Σ-types
-- can emulate strong Σ-types, and vice versa. This investigation was
-- prompted by a question asked by an anonymous reviewer. See also
-- Definition.Untyped.Sigma, which contains some basic definitions,
-- and Definition.Typed.Properties.Admissible.Sigma as well as
-- Definition.Typed.Consequences.Admissible.Sigma, which contain
-- properties related to typing. This module contains properties
-- related to usage.

------------------------------------------------------------------------
-- Some private lemmas related to the modality

private

  opaque

    -- Some lemmas used below.

    [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ : (𝟘 ∧ 𝟙) ·ᶜ γ PE.≡ 𝟘ᶜ ∧ᶜ γ
    [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ {γ = γ} =
      (𝟘 ∧ 𝟙) ·ᶜ γ      ≡⟨ ≈ᶜ→≡ (·ᶜ-distribʳ-∧ᶜ _ _ _) ⟩
      𝟘 ·ᶜ γ ∧ᶜ 𝟙 ·ᶜ γ  ≡⟨ ≈ᶜ→≡ (∧ᶜ-cong (·ᶜ-zeroˡ _) (·ᶜ-identityˡ _)) ⟩
      𝟘ᶜ ∧ᶜ γ           ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    [𝟘∧𝟙]·≡𝟘∧ : (𝟘 ∧ 𝟙) · p PE.≡ 𝟘 ∧ p
    [𝟘∧𝟙]·≡𝟘∧ {p = p} =
      (𝟘 ∧ 𝟙) · p    ≡⟨ ·-distribʳ-∧ _ _ _ ⟩
      𝟘 · p ∧ 𝟙 · p  ≡⟨ ∧-cong (·-zeroˡ _) (·-identityˡ _) ⟩
      𝟘 ∧ p          ∎
      where
      open Tools.Reasoning.PropositionalEquality

  opaque

    ·[𝟘∧𝟙]·≡𝟘∧· : p · (𝟘 ∧ 𝟙) · q PE.≡ 𝟘 ∧ p · q
    ·[𝟘∧𝟙]·≡𝟘∧· {p = p} {q = q} =
      p · (𝟘 ∧ 𝟙) · q  ≡⟨ ·-congˡ [𝟘∧𝟙]·≡𝟘∧ ⟩
      p · (𝟘 ∧ q)      ≡⟨ ·-distribˡ-∧ _ _ _ ⟩
      p · 𝟘 ∧ p · q    ≡⟨ ∧-congʳ (·-zeroʳ _) ⟩
      𝟘 ∧ p · q        ∎
      where
      open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Pair constructors

opaque

  -- If _+_ is pointwise bounded by _∧_, then a usage rule like the one
  -- for prodʷ can be derived for prodˢ.

  prodˢʷₘ :
    (∀ p q → p + q ≤ p ∧ q) →
    γ ▸[ m ᵐ· p ] t →
    δ ▸[ m ] u →
    p ·ᶜ γ +ᶜ δ ▸[ m ] prodˢ p t u
  prodˢʷₘ +≤∧ ▸t ▸u = sub (prodˢₘ ▸t ▸u) (+ᶜ≤ᶜ∧ᶜ +≤∧)

opaque

  -- If _∧_ is pointwise bounded by _+_, then a usage rule like the one
  -- for prodˢ can be derived for prodʷ.

  prodʷˢₘ :
    (∀ p q → p ∧ q ≤ p + q) →
    γ ▸[ m ᵐ· p ] t →
    δ ▸[ m ] u →
    p ·ᶜ γ ∧ᶜ δ ▸[ m ] prodʷ p t u
  prodʷˢₘ ∧≤+ ▸t ▸u = sub (prodʷₘ ▸t ▸u) (∧ᶜ≤ᶜ+ᶜ ∧≤+)

opaque

  -- A usage rule that works for both kinds of pair constructors.

  prodₘ :
    γ ▸[ m ᵐ· p ] t →
    δ ▸[ m ] u →
    (s PE.≡ 𝕨 → η ≤ᶜ p ·ᶜ γ +ᶜ δ) →
    (s PE.≡ 𝕤 → η ≤ᶜ p ·ᶜ γ ∧ᶜ δ) →
    η ▸[ m ] prod s p t u
  prodₘ {s = 𝕤} ▸t ▸u _  ok = sub (prodˢₘ ▸t ▸u) (ok PE.refl)
  prodₘ {s = 𝕨} ▸t ▸u ok _  = sub (prodʷₘ ▸t ▸u) (ok PE.refl)

------------------------------------------------------------------------
-- Usage lemmas for prodrecˢ

opaque

  -- A usage lemma for prodrecˢ.

  prodrecˢₘ :
    (⌜ m ᵐ· r · p ⌝ PE.≢ 𝟘 → p ≤ 𝟙) →
    γ ▸[ m ᵐ· r ] t →
    δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
    (⌜ m ⌝ · r · (𝟙 + p)) ·ᶜ γ +ᶜ δ ▸[ m ] prodrecˢ p t u
  prodrecˢₘ {m = m} {r = r} {p = p} {γ = γ} {δ = δ} mrp≢𝟘→p≤𝟙 ▸t ▸u = sub
    (doubleSubstₘ-lemma₁ ▸u
       (sndₘ ▸t)
       (fstₘ (m ᵐ· r) (▸-cong (·ᵐ-comm _ _) (▸-· ▸t)) (ᵐ·-·-assoc m) mrp≢𝟘→p≤𝟙))
      (begin
         (⌜ m ⌝ · r · (𝟙 + p)) ·ᶜ γ +ᶜ δ                             ≈⟨ +ᶜ-comm _ _ ⟩
         δ +ᶜ (⌜ m ⌝ · r · (𝟙 + p)) ·ᶜ γ                             ≈⟨ +ᶜ-congˡ $
                                                                        ≈ᶜ-trans
                                                                          (·ᶜ-congʳ $
                                                                           PE.trans
                                                                             (·-congˡ $
                                                                              PE.trans (·-distribˡ-+ _ _ _) $
                                                                              +-congʳ $
                                                                              ·-identityʳ _) $
                                                                           ·-distribˡ-+ _ _ _) $
                                                                        ·ᶜ-distribʳ-+ᶜ _ _ _ ⟩
         δ +ᶜ (⌜ m ⌝ · r) ·ᶜ γ +ᶜ (⌜ m ⌝ · r · p) ·ᶜ γ               ≈˘⟨ +ᶜ-congˡ $ +ᶜ-congˡ $
                                                                         ≈ᶜ-trans (≈ᶜ-sym (·ᶜ-assoc _ _ _)) $
                                                                         ·ᶜ-congʳ $
                                                                         PE.trans (·-assoc _ _ _) $
                                                                         ·-congˡ $
                                                                         PE.trans (·-assoc _ _ _) $
                                                                         ·-congˡ $
                                                                         ·⌜⌞⌟⌝ ⟩
         δ +ᶜ (⌜ m ⌝ · r) ·ᶜ γ +ᶜ (⌜ m ⌝ · r · p) ·ᶜ ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ  ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- A variant of the main usage lemma for prodrecˢ with the mode set
  -- to 𝟘ᵐ.

  prodrecˢₘ-𝟘ᵐ :
    ¬ Trivialᵐ →
    γ ▸[ 𝟘ᵐ ] t →
    δ ∙ 𝟘 ∙ 𝟘 ▸[ 𝟘ᵐ ] u →
    δ ▸[ 𝟘ᵐ ] prodrecˢ p t u
  prodrecˢₘ-𝟘ᵐ {γ} {δ} {p} 𝟙ᵐ≢𝟘ᵐ ▸t ▸u = sub
    (prodrecˢₘ
       (λ ≢𝟘 → ⊥-elim (𝟙ᵐ≢𝟘ᵐ (⌜𝟘ᵐ⌝≢𝟘→ (PE.subst (λ m → ⌜ m ⌝ ≢ 𝟘) ᵐ·-zeroˡ ≢𝟘))))
       (▸-cong (PE.sym ᵐ·-zeroˡ) ▸t)
       (sub ▸u $ begin
          δ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘 · p ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (·-zeroˡ _) ∙ ·-zeroʳ _ ⟩
          δ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘 ∙ 𝟘               ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ PE.refl ⟩
          δ ∙ 𝟘 ∙ 𝟘                        ∎))
    (begin
       δ                                 ≈˘⟨ +ᶜ-identityˡ _ ⟩
       𝟘ᶜ +ᶜ δ                           ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
       𝟘 ·ᶜ γ +ᶜ δ                       ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroʳ _)) ⟩
       (⌜ 𝟘ᵐ ⌝ · 𝟘) ·ᶜ γ +ᶜ δ            ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-congˡ (·-zeroˡ _))) ⟩
       (⌜ 𝟘ᵐ ⌝ · 𝟘 · (𝟙 + p)) ·ᶜ γ +ᶜ δ  ∎)
    where
    open ≤ᶜ-reasoning

opaque

  -- A variant of the main usage lemma for prodrecˢ with the mode set to
  -- 𝟙ᵐ and the quantity p to 𝟘.

  prodrecˢₘ-𝟙ᵐ-𝟘 :
    𝟘 ≤ 𝟙 ⊎ ¬ Trivialᵐ →
    γ ▸[ ⌞ r ⌟ ] t →
    δ ∙ 𝟘 ∙ r ▸[ 𝟙ᵐ ] u →
    r ·ᶜ γ +ᶜ δ ▸[ 𝟙ᵐ ] prodrecˢ 𝟘 t u
  prodrecˢₘ-𝟙ᵐ-𝟘 {γ = γ} {r = r} {δ = δ} ok ▸t ▸u = sub-≈ᶜ
    (prodrecˢₘ
       (λ ⌞r𝟘⌟≢𝟘 → case ok of λ where
         (inj₁ 𝟘≤𝟙) → 𝟘≤𝟙
         (inj₂ 𝟙ᵐ≢𝟘ᵐ) →
           let open Tools.Reasoning.PropositionalEquality in
           ⊥-elim (𝟙ᵐ≢𝟘ᵐ (⌜𝟘ᵐ⌝≢𝟘→ (PE.subst (λ m → ⌜ m ⌝ ≢ 𝟘) (begin
               𝟙ᵐ ᵐ· r · 𝟘 ≡⟨ ᵐ·-congˡ (·-zeroʳ _) ⟩
               𝟙ᵐ ᵐ· 𝟘     ≡⟨ ᵐ·-zeroʳ _ ⟩
               𝟘ᵐ          ∎)
             ⌞r𝟘⌟≢𝟘))))
       (▸-cong (PE.sym ᵐ·-identityˡ) ▸t)
       (let open ≤ᶜ-reasoning in
        sub ▸u $ begin
          δ ∙ ⌜ 𝟙ᵐ ⌝ · r · 𝟘 ∙ ⌜ 𝟙ᵐ ⌝ · r ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (·-zeroʳ _) ∙ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
          δ ∙ ⌜ 𝟙ᵐ ⌝ · 𝟘 ∙ 𝟙 · r          ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-identityˡ _ ⟩
          δ ∙ 𝟘 ∙ r                       ∎))
    (let open ≈ᶜ-reasoning in begin
      r ·ᶜ γ +ᶜ δ                      ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-identityʳ _)) ⟩
      (r · 𝟙) ·ᶜ γ +ᶜ δ                ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-identityˡ _)) ⟩
      (𝟙 · r · 𝟙) ·ᶜ γ +ᶜ δ            ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-cong ⌜𝟙ᵐ⌝ (·-congˡ (+-identityʳ _)))) ⟩
      (⌜ 𝟙ᵐ ⌝ · r · (𝟙 + 𝟘)) ·ᶜ γ +ᶜ δ ∎)

opaque

  -- A variant of the main usage lemma for prodrecˢ with the mode set to
  -- 𝟙ᵐ and the quantity p to 𝟙. Note that the context in the conclusion
  -- is (r + r) ·ᶜ γ +ᶜ δ, while the corresponding context in the usage
  -- rule for prodrec is r ·ᶜ γ +ᶜ δ.

  prodrecˢₘ-𝟙ᵐ-𝟙 :
    γ ▸[ ⌞ r ⌟ ] t →
    δ ∙ r ∙ r ▸[ 𝟙ᵐ ] u →
    (r + r) ·ᶜ γ +ᶜ δ ▸[ 𝟙ᵐ ] prodrecˢ 𝟙 t u
  prodrecˢₘ-𝟙ᵐ-𝟙 {γ = γ} {r = r} {δ = δ} ▸t ▸u = sub-≈ᶜ
    (prodrecˢₘ
       (λ _ → ≤-refl)
       (▸-cong (PE.sym ᵐ·-identityˡ) ▸t)
       (sub-≈ᶜ ▸u $ begin
          δ ∙ ⌜ 𝟙ᵐ ⌝ · r · 𝟙 ∙ ⌜ 𝟙ᵐ ⌝ · r  ≈⟨ ≈ᶜ-refl ∙ ·-cong ⌜𝟙ᵐ⌝ (·-identityʳ _) ∙ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
          δ ∙ 𝟙 · r ∙ 𝟙 · r                ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ∙ ·-identityˡ _ ⟩
          δ ∙ r ∙ r                        ∎))
    (begin
      (r + r) ·ᶜ γ +ᶜ δ                 ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (+-cong (·-identityʳ _) (·-identityʳ _))) ⟩
      (r · 𝟙 + r · 𝟙) ·ᶜ γ +ᶜ δ         ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-identityˡ _)) ⟩
      (𝟙 · (r · 𝟙 + r · 𝟙)) ·ᶜ γ +ᶜ δ   ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-cong ⌜𝟙ᵐ⌝ (·-distribˡ-+ _ _ _))) ⟩
      (⌜ 𝟙ᵐ ⌝ · r · (𝟙 + 𝟙)) ·ᶜ γ +ᶜ δ  ∎)
    where
    open ≈ᶜ-reasoning

opaque

  -- A variant of the previous lemma with the assumption that _∧_ is
  -- pointwise bounded by _+_.

  prodrecˢₘ-𝟙ᵐ-𝟙-∧≤+ :
    (∀ p q → p ∧ q ≤ p + q) →
    γ ▸[ ⌞ r ⌟ ] t →
    δ ∙ r ∙ r ▸[ 𝟙ᵐ ] u →
    r ·ᶜ γ +ᶜ δ ▸[ 𝟙ᵐ ] prodrecˢ 𝟙 t u
  prodrecˢₘ-𝟙ᵐ-𝟙-∧≤+ {γ = γ} {r = r} {δ = δ} ∧≤+ ▸t ▸u = sub
    (prodrecˢₘ-𝟙ᵐ-𝟙 ▸t ▸u)
    (begin
       r ·ᶜ γ +ᶜ δ        ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (∧-idem _)) ⟩
       (r ∧ r) ·ᶜ γ +ᶜ δ  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ (∧≤+ _ _)) ⟩
       (r + r) ·ᶜ γ +ᶜ δ  ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

  -- One cannot in general derive the usage rule of prodrec for
  -- prodrecˢ.
  --
  -- Note that the assumption 𝟙 ≰ 𝟙 + 𝟙 is satisfied by, for instance,
  -- the linearity modality, see
  -- Graded.Modality.Instances.Linearity.Properties.¬prodrecₘ-Linearity.

  ¬prodrecₘ : Prodrec-allowed 𝟙ᵐ 𝟙 𝟙 𝟘
            → ¬ (𝟙 ≤ 𝟙 + 𝟙)
            → ¬ (∀ {n} {γ η : Conₘ n} {δ m r p q t u A}
                 → γ ▸[ m ᵐ· r ] t
                 → δ ∙ ⌜ m ⌝ · r  · p ∙ ⌜ m ⌝ · r ▸[ m ] u
                 → η ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A
                 → Prodrec-allowed m r p q
                 → r ·ᶜ γ +ᶜ δ ▸[ m ] prodrecˢ p t u)
  ¬prodrecₘ ok 𝟙≰𝟚 prodrecˢₘ′ =
    let t = prod 𝕤 𝟙 (var x0) (var x0)
        u = prod 𝕨 𝟙 (var x1) (var x0)
        γ▸t′ = prodˢₘ {γ = ε ∙ ⌜ 𝟙ᵐ ⌝} {m = 𝟙ᵐ} {p = 𝟙} {δ = ε ∙ ⌜ 𝟙ᵐ ⌝}
                        (PE.subst (λ x → ε ∙ ⌜ 𝟙ᵐ ⌝ ▸[ x ] var x0) (PE.sym ᵐ·-identityʳ) var)
                        (var {x = x0})

        γ▸t = PE.subst₂ (λ x y → x ▸[ y ] t)
                (PE.cong (ε ∙_) (PE.trans (PE.cong (_∧ ⌜ 𝟙ᵐ ⌝) (·-identityˡ _))
                                          (∧-idem _)))
                        (PE.sym ᵐ·-identityʳ) γ▸t′
        δ▸u′ : _ ▸[ 𝟙ᵐ ] u
        δ▸u′ = prodʷₘ var var
        δ▸u = let open Tools.Reasoning.PropositionalEquality
              in  PE.subst₃ (λ x y z → ε ∙ x ∙ y ∙ z ▸[ 𝟙ᵐ ] u)
                        (PE.trans (+-identityʳ _) (·-identityˡ 𝟘))
                        (𝟙 · ⌜ 𝟙ᵐ ᵐ· 𝟙 ⌝ + 𝟘  ≡⟨ +-identityʳ _ ⟩
                         𝟙 · ⌜ 𝟙ᵐ ᵐ· 𝟙 ⌝      ≡⟨ ·-identityˡ _ ⟩
                         ⌜ 𝟙ᵐ ᵐ· 𝟙 ⌝          ≡⟨ PE.cong ⌜_⌝ (ᵐ·-identityʳ {m = 𝟙ᵐ}) ⟩
                         ⌜ 𝟙ᵐ ⌝               ≡˘⟨ ·-identityʳ _ ⟩
                         ⌜ 𝟙ᵐ ⌝ · 𝟙           ≡˘⟨ ·-congˡ (·-identityʳ _) ⟩
                         ⌜ 𝟙ᵐ ⌝ · 𝟙 · 𝟙       ∎)
                        (𝟙 · 𝟘 + ⌜ 𝟙ᵐ ⌝  ≡⟨ PE.cong (flip _+_ _) (·-identityˡ 𝟘) ⟩
                         𝟘 + ⌜ 𝟙ᵐ ⌝      ≡⟨ +-identityˡ _ ⟩
                         ⌜ 𝟙ᵐ ⌝          ≡˘⟨ ·-identityʳ _ ⟩
                         ⌜ 𝟙ᵐ ⌝ · 𝟙      ∎)
                        δ▸u′
        η▸A′ = ΠΣₘ {γ = 𝟘ᶜ} {p = 𝟘} {δ = 𝟘ᶜ} {b = BMΣ 𝕨}
                   ℕₘ (sub-≈ᶜ ℕₘ (≈ᶜ-refl ∙ ·-zeroʳ _))
        η▸A = sub-≈ᶜ η▸A′ (≈ᶜ-sym (≈ᶜ-trans (+ᶜ-identityʳ _) (·ᶜ-zeroˡ _)) ∙
                            PE.trans (·-zeroʳ _) (PE.sym (PE.trans (+-identityʳ _) (·-zeroˡ _))))
    in  case prodrecˢₘ′ {η = 𝟘ᶜ} γ▸t δ▸u η▸A ok of λ ▸pr′ →
        case inv-usage-prodʷ ▸pr′ of λ {
          (invUsageProdʷ {δ = ε ∙ a} {ε ∙ b} a▸fstt b▸sndt 𝟙≤a+b) → case inv-usage-fst a▸fstt of λ {
          (invUsageFst {δ = ε ∙ c} m′ eq c▸t a≤c _) → case inv-usage-snd b▸sndt of λ {
          (invUsageSnd {δ = ε ∙ d} d▸t b≤d) → case inv-usage-prodˢ c▸t of λ {
          (invUsageProdˢ {δ = ε ∙ e} {η = ε ∙ f} e▸x₀ f▸x₀ c≤e∧f) → case inv-usage-prodˢ d▸t of λ {
          (invUsageProdˢ {δ = ε ∙ g} {η = ε ∙ h} g▸x₀ h▸x₀ d≤g∧h) →
            let i = ⌜ (𝟙ᵐ ᵐ· 𝟙) ᵐ· 𝟙 ⌝
                j = ⌜ 𝟙ᵐ ᵐ· 𝟙 ⌝
                j≡𝟙 = PE.trans (⌜⌝-cong ᵐ·-identityʳ) ⌜𝟙ᵐ⌝
                open ≤-reasoning

            in  case begin
                  𝟙 ≡˘⟨ ·-identityˡ 𝟙 ⟩
                  𝟙 · 𝟙 ≡˘⟨ +-identityʳ _ ⟩
                  𝟙 · 𝟙 + 𝟘 ≈˘⟨ +-congʳ (·-congˡ ⌜𝟙ᵐ⌝) ⟩
                  𝟙 · ⌜ 𝟙ᵐ ⌝ + 𝟘 ≤⟨ ⦅ 𝟙≤a+b ⦆ ⟩
                  𝟙 · a + b ≡⟨ PE.cong (_+ b) (·-identityˡ a) ⟩
                  a + b ≤⟨ +-monotone ⦅ a≤c ⦆ ⦅ b≤d ⦆ ⟩
                  c + d ≤⟨ +-monotone ⦅ c≤e∧f ⦆ ⦅ d≤g∧h ⦆ ⟩
                  (𝟙 · e ∧ f) + (𝟙 · g ∧ h) ≡⟨ +-cong (∧-congʳ (·-identityˡ e)) (∧-congʳ (·-identityˡ g)) ⟩
                  (e ∧ f) + (g ∧ h) ≤⟨  +-monotone (∧-monotone ⦅ inv-usage-var e▸x₀ ⦆ ⦅ inv-usage-var f▸x₀ ⦆)
                                                  (∧-monotone ⦅ inv-usage-var g▸x₀ ⦆ ⦅ inv-usage-var h▸x₀ ⦆)
                                     ⟩
                  (i ∧ j) + (j ∧ ⌜ 𝟙ᵐ ⌝) ≡⟨ +-cong (∧-congʳ (⌜⌝-cong ᵐ·-identityʳ)) (∧-congˡ ⌜𝟙ᵐ⌝) ⟩
                  (j ∧ j) + (j ∧ 𝟙) ≡⟨ +-cong (∧-cong j≡𝟙 j≡𝟙) (∧-congʳ j≡𝟙) ⟩
                  (𝟙 ∧ 𝟙) + (𝟙 ∧ 𝟙) ≡⟨ +-cong (∧-idem 𝟙) (∧-idem 𝟙) ⟩
                  𝟙 + 𝟙 ∎
                  of 𝟙≰𝟚
              }}}}}
    where
    ⦅_⦆ : {p q : M} → ε ∙ p ≤ᶜ ε ∙ q → p ≤ q
    ⦅_⦆ = headₘ-monotone

------------------------------------------------------------------------
-- A usage lemma for prodrec⟨_⟩

opaque
  unfolding prodrec⟨_⟩

  -- A usage lemma for prodrec⟨_⟩.

  ▸prodrec⟨⟩ :
    (s PE.≡ 𝕤 → ⌜ m ᵐ· r · p ⌝ PE.≢ 𝟘 → p ≤ 𝟙) →
    (s PE.≡ 𝕤 → r′ ≤ ⌜ m ⌝ · r · (𝟙 + p)) →
    (s PE.≡ 𝕨 → r′ ≤ r) →
    (s PE.≡ 𝕨 → Prodrec-allowed m r p q) →
    (s PE.≡ 𝕨 → ∃ λ η → η ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A) →
    γ ▸[ m ᵐ· r ] t →
    δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
    r′ ·ᶜ γ +ᶜ δ ▸[ m ] prodrec⟨ s ⟩ r p q A t u
  ▸prodrec⟨⟩ {s = 𝕨} {r} {r′} {γ} {δ} _ _ hyp₃ ok ▸A ▸t ▸u =
    sub (prodrecₘ ▸t ▸u (▸A PE.refl .proj₂) (ok PE.refl)) $ begin
      r′ ·ᶜ γ +ᶜ δ  ≤⟨ +ᶜ-monotoneˡ $ ·ᶜ-monotoneˡ $ hyp₃ PE.refl ⟩
      r ·ᶜ γ +ᶜ δ   ∎
    where
    open ≤ᶜ-reasoning
  ▸prodrec⟨⟩ {s = 𝕤} {m} {r} {p} {r′} {γ} {δ} hyp₁ hyp₂ _ _ _ ▸t ▸u =
    sub (prodrecˢₘ (hyp₁ PE.refl) ▸t ▸u) (begin
      r′ ·ᶜ γ +ᶜ δ                     ≤⟨ +ᶜ-monotoneˡ $ ·ᶜ-monotoneˡ $ hyp₂ PE.refl ⟩
      (⌜ m ⌝ · r · (𝟙 + p)) ·ᶜ γ +ᶜ δ  ∎)
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- An investigation of different potential implementations of a first
-- projection for weak Σ-types

-- A generalised first projection with two extra quantities.

fstʷ′ : M → M → M → Term n → Term n → Term n
fstʷ′ r p q = Fstʷ-sndʷ.fstʷ r q p

opaque

  -- An inversion lemma for fstʷ′.

  inv-usage-fstʷ′ :
    γ ▸[ m ] fstʷ′ r p q A t →
    ∃₂ λ η δ →
      γ ≤ᶜ r ·ᶜ η ×
      η ▸[ m ᵐ· r ] t ×
      δ ▸[ 𝟘ᵐ ] A ×
      ⌜ m ⌝ · r · p ≤ ⌜ m ⌝ ×
      ⌜ m ⌝ · r ≤ 𝟘 ×
      Prodrec-allowed m r p q
  inv-usage-fstʷ′ {γ = γ} {m = m} {r = r} {p = p} {q = q} ▸fstʷ′ =
    case inv-usage-prodrec ▸fstʷ′ of λ {
      (invUsageProdrec {δ = δ} {η = η} {θ = θ} ▸t ▸var ▸A ok γ≤rδ+η) →
    case inv-usage-var ▸var of λ {
      (η≤𝟘 ∙ mrp≤m ∙ mr≤𝟘) →
      δ
    , θ
    , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         γ             ≤⟨ γ≤rδ+η ⟩
         r ·ᶜ δ +ᶜ η   ≤⟨ +ᶜ-monotoneʳ η≤𝟘 ⟩
         r ·ᶜ δ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
         r ·ᶜ δ        ∎)
    , ▸t
    , wkUsage⁻¹ ▸A
    , mrp≤m
    , mr≤𝟘
    , ok }}

opaque

  -- An inversion lemma for fstʷ′ with the mode set to 𝟙ᵐ.

  inv-usage-fstʷ′-𝟙ᵐ :
    γ ▸[ 𝟙ᵐ ] fstʷ′ r p q A t →
    ∃₂ λ η δ →
      γ ≤ᶜ r ·ᶜ η ×
      η ▸[ ⌞ r ⌟ ] t ×
      δ ▸[ 𝟘ᵐ ] A ×
      r · p ≤ 𝟙 ×
      r ≤ 𝟘 ×
      Prodrec-allowed 𝟙ᵐ r p q
  inv-usage-fstʷ′-𝟙ᵐ {r = r} {p = p} ▸fstʷ′ =
    case inv-usage-fstʷ′ ▸fstʷ′ of λ {
      (_ , _ , leq₁ , ▸t , ▸A , leq₂ , leq₃ , ok) →
    _ , _ , leq₁ , ▸-cong ᵐ·-identityˡ ▸t , ▸A ,
    (begin
       r · p           ≡˘⟨ ·-identityˡ _ ⟩
       𝟙 · r · p       ≡˘⟨ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
       ⌜ 𝟙ᵐ ⌝ · r · p  ≤⟨ leq₂ ⟩
       ⌜ 𝟙ᵐ ⌝          ≈⟨ ⌜𝟙ᵐ⌝ ⟩
       𝟙               ∎) ,
    (begin
       r           ≡˘⟨ ·-identityˡ _ ⟩
       𝟙 · r       ≡˘⟨ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
       ⌜ 𝟙ᵐ ⌝ · r  ≤⟨ leq₃ ⟩
       𝟘           ∎) ,
    ok }
    where
    open ≤-reasoning

opaque

  -- If 𝟘 ≰ 𝟙 then no application of fstʷ′ 𝟘 is well-resourced (with
  -- respect to the mode 𝟙ᵐ).

  𝟘≰𝟙→fstʷ′-𝟘-not-ok :
    ¬ 𝟘 ≤ 𝟙 →
    ¬ γ ▸[ 𝟙ᵐ ] fstʷ′ 𝟘 p q A t
  𝟘≰𝟙→fstʷ′-𝟘-not-ok {γ = γ} {p = p} {q = q} {A = A} {t = t} 𝟘≰𝟙 =
    γ ▸[ 𝟙ᵐ ] fstʷ′ 𝟘 p q A t  →⟨ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ inv-usage-fstʷ′-𝟙ᵐ ⟩
    𝟘 · p ≤ 𝟙                  →⟨ ≤-trans (≤-reflexive (PE.sym (·-zeroˡ _))) ⟩
    𝟘 ≤ 𝟙                      →⟨ 𝟘≰𝟙 ⟩
    ⊥                          □

opaque

  -- If 𝟙 ≰ 𝟘 then no application of fstʷ′ 𝟙 is well-resourced (with
  -- respect to the mode 𝟙ᵐ).

  𝟙≰𝟘→fstʷ′-𝟙-not-ok :
    ¬ 𝟙 ≤ 𝟘 →
    ¬ γ ▸[ 𝟙ᵐ ] fstʷ′ 𝟙 p q A t
  𝟙≰𝟘→fstʷ′-𝟙-not-ok {γ = γ} {p = p} {q = q} {A = A} {t = t} 𝟙≰𝟘 =
    γ ▸[ 𝟙ᵐ ] fstʷ′ 𝟙 p q A t  →⟨ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ inv-usage-fstʷ′-𝟙ᵐ ⟩
    𝟙 ≤ 𝟘                      →⟨ 𝟙≰𝟘 ⟩
    ⊥                          □

opaque

  -- An inversion lemma for fstʷ′ with the mode set to 𝟙ᵐ.

  inv-usage-fstʷ′-≢𝟘-𝟙ᵐ :
    ⌞ r ⌟ PE.≡ 𝟙ᵐ →
    γ ▸[ 𝟙ᵐ ] fstʷ′ r p q A t →
    ∃₂ λ η δ →
      γ ≤ᶜ r ·ᶜ η ×
      η ▸[ 𝟙ᵐ ] t ×
      δ ▸[ 𝟘ᵐ ] A ×
      r · p ≤ 𝟙 ×
      r ≤ 𝟘 ×
      Prodrec-allowed 𝟙ᵐ r p q
  inv-usage-fstʷ′-≢𝟘-𝟙ᵐ ⌞r⌟≡𝟙ᵐ ▸fstʷ′ =
    case inv-usage-fstʷ′-𝟙ᵐ ▸fstʷ′ of λ {
      (_ , _ , leq₁ , ▸t , ▸A , leq₂ , leq₃ , ok) →
    _ , _ , leq₁ , ▸-cong ⌞r⌟≡𝟙ᵐ ▸t ,
    ▸A , leq₂ , leq₃ , ok }

opaque

  -- An inversion lemma for fstʷ′ with the mode set to 𝟙ᵐ and "r" set to
  -- 𝟘 ∧ 𝟙.

  inv-usage-fstʷ′-𝟘∧𝟙-𝟙ᵐ :
    ⌞ 𝟘 ∧ 𝟙 ⌟ PE.≡ 𝟙ᵐ →
    γ ▸[ 𝟙ᵐ ] fstʷ′ (𝟘 ∧ 𝟙) p q A t →
    ∃₂ λ η δ →
      γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ 𝟙ᵐ ] t ×
      δ ▸[ 𝟘ᵐ ] A ×
      𝟘 ∧ p ≤ 𝟙 ×
      Prodrec-allowed 𝟙ᵐ (𝟘 ∧ 𝟙) p q
  inv-usage-fstʷ′-𝟘∧𝟙-𝟙ᵐ {γ = γ} {p = p} ⌞𝟘∧𝟙⌟≡𝟙ᵐ ▸fstʷ′ =
    case inv-usage-fstʷ′-≢𝟘-𝟙ᵐ ⌞𝟘∧𝟙⌟≡𝟙ᵐ ▸fstʷ′ of λ {
      (η , _ , leq₁ , ▸t , ▸A , leq₂ , _ , ok) →
    _ , _ ,
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       γ             ≤⟨ leq₁ ⟩
       (𝟘 ∧ 𝟙) ·ᶜ η  ≡⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
       𝟘ᶜ ∧ᶜ η       ∎) ,
    ▸t , ▸A ,
    (let open Tools.Reasoning.PartialOrder ≤-poset in begin
       𝟘 ∧ p        ≡˘⟨ [𝟘∧𝟙]·≡𝟘∧ ⟩
       (𝟘 ∧ 𝟙) · p  ≤⟨ leq₂ ⟩
       𝟙            ∎) ,
    ok }

opaque

  -- If a certain usage rule holds for fstʷ′ r 𝟙 q A (where A has type
  -- Term 1), then r is equal to 𝟙 and 𝟙 ≤ 𝟘.

  fstʷ′ₘ→≡𝟙≤𝟘 :
    {A : Term 1} →
    (∀ {γ t} →
     γ ▸[ 𝟙ᵐ ] t →
     γ ▸[ 𝟙ᵐ ] fstʷ′ r 𝟙 q A t) →
    r PE.≡ 𝟙 × 𝟙 ≤ 𝟘
  fstʷ′ₘ→≡𝟙≤𝟘 {r = r} {q = q} {A = A} =
    (∀ {γ t} → γ ▸[ 𝟙ᵐ ] t → γ ▸[ 𝟙ᵐ ] fstʷ′ r 𝟙 q A t)  →⟨ _$ var ⟩
    γ′ ▸[ 𝟙ᵐ ] fstʷ′ r 𝟙 q A t′                          →⟨ lemma ⟩
    r PE.≡ 𝟙 × 𝟙 ≤ 𝟘                                     □
    where
    γ′ : Conₘ 1
    γ′ = ε ∙ ⌜ 𝟙ᵐ ⌝
    t′ : Term 1
    t′ = var x0

    lemma : γ′ ▸[ 𝟙ᵐ ] fstʷ′ r 𝟙 q A t′ → r PE.≡ 𝟙 × 𝟙 ≤ 𝟘
    lemma ▸fst-t =
      case inv-usage-fstʷ′ ▸fst-t of λ {
        (ε ∙ p , _ , ε ∙ 𝟙≤rp , ▸t , _ , 𝟙r𝟙≤𝟙 , 𝟙r≤𝟘 , _) →
      case inv-usage-var ▸t of λ {
        (ε ∙ p≤⌜⌞r⌟⌝) →
      let r≤𝟙 = begin
            r              ≡˘⟨ ·-identityʳ _ ⟩
            r · 𝟙          ≡˘⟨ ·-identityˡ _ ⟩
            𝟙 · r · 𝟙      ≡˘⟨ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
            ⌜ 𝟙ᵐ ⌝ · r · 𝟙 ≤⟨ 𝟙r𝟙≤𝟙 ⟩
            ⌜ 𝟙ᵐ ⌝         ≈⟨ ⌜𝟙ᵐ⌝ ⟩
            𝟙              ∎

          r≤𝟘 = begin
            r          ≡˘⟨ ·-identityˡ _ ⟩
            𝟙 · r      ≡˘⟨ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
            ⌜ 𝟙ᵐ ⌝ · r ≤⟨ 𝟙r≤𝟘 ⟩
            𝟘          ∎
      in
        ≤-antisym
          r≤𝟙
          (begin
             𝟙                ≡˘⟨ ⌜𝟙ᵐ⌝ ⟩
             ⌜ 𝟙ᵐ ⌝           ≤⟨ 𝟙≤rp ⟩
             r · p            ≤⟨ ·-monotoneʳ p≤⌜⌞r⌟⌝ ⟩
             r · ⌜ 𝟙ᵐ ᵐ· r ⌝  ≡⟨ ·-congˡ (⌜⌝-cong ᵐ·-identityˡ) ⟩
             r · ⌜ ⌞ r ⌟ ⌝    ≡⟨ ·⌜⌞⌟⌝ ⟩
             r                ∎)
      , (begin
           𝟙      ≡˘⟨ ⌜𝟙ᵐ⌝ ⟩
           ⌜ 𝟙ᵐ ⌝ ≤⟨ 𝟙≤rp ⟩
           r · p  ≤⟨ ·-monotoneˡ r≤𝟘 ⟩
           𝟘 · p  ≡⟨ ·-zeroˡ _ ⟩
           𝟘      ∎) }}
      where
      open Tools.Reasoning.PartialOrder ≤-poset

opaque

  -- If 𝟙 is not bounded by 𝟘, then a certain usage rule for
  -- fstʷ′ r 𝟙 q A (where A has type Term 1) does not hold.

  ¬fstʷ′ₘ′ :
    {A : Term 1} →
    ¬ 𝟙 ≤ 𝟘 →
    ¬ ({γ : Conₘ 1} {t : Term 1} →
       γ ▸[ 𝟙ᵐ ] t →
       γ ▸[ 𝟙ᵐ ] fstʷ′ r 𝟙 q A t)
  ¬fstʷ′ₘ′ 𝟙≰𝟘 hyp = 𝟙≰𝟘 (fstʷ′ₘ→≡𝟙≤𝟘 hyp .proj₂)

opaque

  -- If 𝟙 is not bounded by 𝟘, then a certain usage rule for fstʷ′ does
  -- not hold.

  ¬fstʷ′ₘ :
    ¬ 𝟙 ≤ 𝟘 →
    ¬ (∀ {γ : Conₘ 1} {t : Term 1} {p m′} m →
       γ ▸[ m ᵐ· p ] t →
       m ᵐ· p PE.≡ m′ →
       (m′ PE.≡ 𝟙ᵐ → p ≤ 𝟙) →
       γ ▸[ m′ ] fstʷ′ r p q A t)
  ¬fstʷ′ₘ 𝟙≰𝟘 hyp =
    ¬fstʷ′ₘ′ 𝟙≰𝟘 λ ▸t →
      hyp 𝟙ᵐ (▸-cong (PE.sym ᵐ·-identityʳ) ▸t) ᵐ·-identityʳ (λ _ → ≤-refl)

------------------------------------------------------------------------
-- Inversion lemmas for usage for fstʷ

opaque

  -- An inversion lemma for fstʷ.

  inv-usage-fstʷ :
    m ᵐ· (𝟘 ∧ 𝟙) PE.≡ m →
    γ ▸[ m ] fstʷ p A t →
    ∃₂ λ η δ →
      γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ m ] t ×
      δ ▸[ 𝟘ᵐ ] A ×
      𝟘 ∧ ⌜ m ⌝ · p ≤ ⌜ m ⌝ ×
      Prodrec-allowed m (𝟘 ∧ 𝟙) p 𝟘
  inv-usage-fstʷ {m = m} {γ = γ} {p = p} ≡m ▸fstʷ =
    case inv-usage-fstʷ′ ▸fstʷ of λ {
      (η , δ , leq₁ , ▸t , ▸A , leq₂ , leq₃ , ok) →
    _ , _ ,
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       γ             ≤⟨ leq₁ ⟩
       (𝟘 ∧ 𝟙) ·ᶜ η  ≡⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
       𝟘ᶜ ∧ᶜ η       ∎) ,
    ▸-cong ≡m ▸t ,
    ▸A ,
    (let open Tools.Reasoning.PartialOrder ≤-poset in begin
       𝟘 ∧ ⌜ m ⌝ · p        ≡˘⟨ ·[𝟘∧𝟙]·≡𝟘∧· ⟩
       ⌜ m ⌝ · (𝟘 ∧ 𝟙) · p  ≤⟨ leq₂ ⟩
       ⌜ m ⌝                ∎) ,
    ok }

opaque

  -- An inversion lemma for fstʷ with the mode set to 𝟘ᵐ.

  inv-usage-fstʷ-𝟘ᵐ :
    ¬ Trivialᵐ →
    γ ▸[ 𝟘ᵐ ] fstʷ p A t →
    ∃ λ δ →
      γ ≤ᶜ 𝟘ᶜ × 𝟘ᶜ ▸[ 𝟘ᵐ ] t ×
      δ ▸[ 𝟘ᵐ ] A
  inv-usage-fstʷ-𝟘ᵐ {γ = γ} 𝟙ᵐ≢𝟘ᵐ ▸fstʷ =
    case inv-usage-fstʷ ᵐ·-zeroˡ ▸fstʷ of λ {
      (η , _ , leq₁ , ▸t , ▸A , leq₂ , _) →
    _ ,
    (begin
       γ        ≤⟨ leq₁ ⟩
       𝟘ᶜ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
       η        ≤⟨ ▸-𝟘ᵐ 𝟙ᵐ≢𝟘ᵐ ▸t ⟩
       𝟘ᶜ       ∎) ,
    ▸-𝟘′ 𝟙ᵐ≢𝟘ᵐ ▸t , ▸A }
    where
    open ≤ᶜ-reasoning

opaque

  -- An inversion lemma for fstʷ with the mode set to 𝟙ᵐ.

  inv-usage-fstʷ-𝟙ᵐ :
    ⌞ 𝟘 ∧ 𝟙 ⌟ PE.≡ 𝟙ᵐ →
    γ ▸[ 𝟙ᵐ ] fstʷ p A t →
    ∃₂ λ η δ →
      γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ 𝟙ᵐ ] t ×
      δ ▸[ 𝟘ᵐ ] A ×
      𝟘 ∧ p ≤ 𝟙 ×
      Prodrec-allowed 𝟙ᵐ (𝟘 ∧ 𝟙) p 𝟘
  inv-usage-fstʷ-𝟙ᵐ {p = p} ≡𝟙ᵐ ▸fstʷ =
    case inv-usage-fstʷ (PE.trans ᵐ·-identityˡ ≡𝟙ᵐ) ▸fstʷ of λ {
      (_ , _ , leq₁ , ▸t , ▸A , leq₂ , ok) →
    _ , _ , leq₁ , ▸t , ▸A ,
    (begin
       𝟘 ∧ p          ≡˘⟨ ∧-congˡ (·-identityˡ _) ⟩
       𝟘 ∧ 𝟙 · p      ≡˘⟨ ∧-congˡ (·-congʳ ⌜𝟙ᵐ⌝) ⟩
       𝟘 ∧ ⌜ 𝟙ᵐ ⌝ · p ≤⟨ leq₂ ⟩
       ⌜ 𝟙ᵐ ⌝         ≡⟨ ⌜𝟙ᵐ⌝ ⟩
       𝟙              ∎) ,
    ok }
    where
    open ≤-reasoning

------------------------------------------------------------------------
-- Usage lemmas for fstʷ

opaque

  -- A usage lemma for fstʷ.

  fstʷₘ :
    m PE.≡ m ᵐ· (𝟘 ∧ 𝟙) →
    𝟘 ∧ ⌜ m ⌝ · p ≤ ⌜ m ⌝ →
    Prodrec-allowed m (𝟘 ∧ 𝟙) p 𝟘 →
    γ ▸[ m ] t →
    δ ▸[ 𝟘ᵐ ] A →
    𝟘ᶜ ∧ᶜ γ ▸[ m ] fstʷ p A t
  fstʷₘ {m = m} {p = p} {γ = γ} {δ = δ} m≡ 𝟘∧mp≤m ok ▸t ▸A = sub
    (prodrecₘ
       (▸-cong m≡ ▸t)
       (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
        sub var $ begin
          𝟘ᶜ ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙) · p ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙)  ≈⟨ ≈ᶜ-refl ∙ ·[𝟘∧𝟙]·≡𝟘∧· ∙ ·[𝟘∧𝟙]≡𝟘∧ ⟩
          𝟘ᶜ ∙ 𝟘 ∧ ⌜ m ⌝ · p ∙ 𝟘 ∧ ⌜ m ⌝              ≤⟨ ≤ᶜ-refl ∙ 𝟘∧mp≤m ∙ ∧-decreasingˡ _ _ ⟩
          𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘                              ∎)
       (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
        sub (wkUsage (step id) ▸A) $ begin
          δ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
          δ ∙ 𝟘            ∎)
       ok)
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       𝟘ᶜ ∧ᶜ γ             ≡˘⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
       (𝟘 ∧ 𝟙) ·ᶜ γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       (𝟘 ∧ 𝟙) ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)

opaque

  -- A usage lemma for fstʷ with the mode set to 𝟘ᵐ.

  fstʷₘ-𝟘ᵐ :
    ¬ Trivialᵐ →
    Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) p 𝟘 →
    γ ▸[ 𝟘ᵐ ] t →
    δ ▸[ 𝟘ᵐ ] A →
    γ ▸[ 𝟘ᵐ ] fstʷ p A t
  fstʷₘ-𝟘ᵐ {p} {γ} {δ} 𝟙ᵐ≢𝟘ᵐ ok ▸t ▸A = sub
    (fstʷₘ
       (PE.sym ᵐ·-zeroˡ)
       (let open ≤-reasoning in begin
          𝟘 ∧ ⌜ 𝟘ᵐ ⌝ · p  ≡⟨ ∧-congˡ (·-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ)) ⟩
          𝟘 ∧ 𝟘 · p       ≡⟨ ∧-congˡ (·-zeroˡ _) ⟩
          𝟘 ∧ 𝟘           ≡⟨ ∧-idem _ ⟩
          𝟘               ≡˘⟨ ⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ ⟩
          ⌜ 𝟘ᵐ ⌝          ∎)
       ok
       ▸t
       ▸A)
    (let open ≤ᶜ-reasoning in begin
       γ        ≤⟨ ∧ᶜ-greatest-lower-bound (▸-𝟘ᵐ 𝟙ᵐ≢𝟘ᵐ ▸t) ≤ᶜ-refl ⟩
       𝟘ᶜ ∧ᶜ γ  ∎)

opaque

  -- A usage lemma for fstʷ with the mode set to 𝟙ᵐ.

  fstʷₘ-𝟙ᵐ :
    ⌞ 𝟘 ∧ 𝟙 ⌟ PE.≡ 𝟙ᵐ →
    𝟘 ∧ p ≤ 𝟙 →
    Prodrec-allowed 𝟙ᵐ (𝟘 ∧ 𝟙) p 𝟘 →
    γ ▸[ 𝟙ᵐ ] t →
    δ ▸[ 𝟘ᵐ ] A →
    𝟘ᶜ ∧ᶜ γ ▸[ 𝟙ᵐ ] fstʷ p A t
  fstʷₘ-𝟙ᵐ {p = p} ≡𝟙ᵐ 𝟘∧p≤𝟙 = fstʷₘ
    (PE.sym (PE.trans ᵐ·-identityˡ ≡𝟙ᵐ))
    (begin
       𝟘 ∧ ⌜ 𝟙ᵐ ⌝ · p  ≡⟨ ∧-congˡ (·-congʳ ⌜𝟙ᵐ⌝) ⟩
       𝟘 ∧ 𝟙 · p       ≡⟨ ∧-congˡ (·-identityˡ _) ⟩
       𝟘 ∧ p           ≤⟨ 𝟘∧p≤𝟙 ⟩
       𝟙               ≡˘⟨ ⌜𝟙ᵐ⌝ ⟩
       ⌜ 𝟙ᵐ ⌝          ∎)
    where
    open ≤-reasoning

opaque

  -- A usage lemma for fstʷ with the mode set to 𝟙ᵐ and the assumption
  -- that 𝟘 is the largest quantity.

  fstʷₘ-𝟙ᵐ-≤𝟘 :
    (∀ p → p ≤ 𝟘) →
    p ≤ 𝟙 →
    Prodrec-allowed 𝟙ᵐ (𝟘 ∧ 𝟙) p 𝟘 →
    γ ▸[ 𝟙ᵐ ] t →
    δ ▸[ 𝟘ᵐ ] A →
    γ ▸[ 𝟙ᵐ ] fstʷ p A t
  fstʷₘ-𝟙ᵐ-≤𝟘 {p = p} {γ = γ} ≤𝟘 p≤𝟙 ok ▸t ▸A = sub
    (fstʷₘ-𝟙ᵐ
       (let open Tools.Reasoning.PropositionalEquality in begin
         ⌞ 𝟘 ∧ 𝟙 ⌟ ≡⟨ (⌞⌟-cong $ ∧-comm _ _) ⟩
         ⌞ 𝟙 ∧ 𝟘 ⌟ ≡˘⟨ (⌞⌟-cong $ ≤𝟘 𝟙) ⟩
         ⌞ 𝟙 ⌟     ≡⟨ ⌞𝟙⌟ ⟩
         𝟙ᵐ ∎)
       (let open ≤-reasoning in begin
          𝟘 ∧ p  ≤⟨ ∧-decreasingʳ _ _ ⟩
          p      ≤⟨ p≤𝟙 ⟩
          𝟙      ∎)
       ok
       ▸t
       ▸A)
    (let open ≤ᶜ-reasoning in begin
       γ        ≤⟨ ∧ᶜ-greatest-lower-bound (≤ᶜ𝟘ᶜ (≤𝟘 _)) ≤ᶜ-refl ⟩
       𝟘ᶜ ∧ᶜ γ  ∎)

opaque

  -- A usage lemma for fstʷ with the mode set to 𝟙ᵐ and the assumption
  -- that _+_ is pointwise bounded by _∧_.

  fstʷₘ-𝟙ᵐ-∧≤+ :
    (∀ p q → p + q ≤ p ∧ q) →
    p ≤ 𝟙 →
    Prodrec-allowed 𝟙ᵐ (𝟘 ∧ 𝟙) p 𝟘 →
    γ ▸[ 𝟙ᵐ ] t →
    δ ▸[ 𝟘ᵐ ] A →
    γ ▸[ 𝟙ᵐ ] fstʷ p A t
  fstʷₘ-𝟙ᵐ-∧≤+ +≤∧ = fstʷₘ-𝟙ᵐ-≤𝟘 (+≤∧→≤𝟘 +≤∧)

opaque

  -- If 𝟙 is not bounded by 𝟘, then a certain usage rule for fstʷ 𝟙 A
  -- (where A has type Term 1) does not hold.
  --
  -- Note that the assumption 𝟙 ≰ 𝟘 is satisfied by, for instance, the
  -- linearity modality, see
  -- Graded.Modality.Instances.Linearity.Properties.¬fstʷₘ′.

  ¬fstʷₘ′ :
    {A : Term 1} →
    ¬ 𝟙 ≤ 𝟘 →
    ¬ ({γ : Conₘ 1} {t : Term 1} →
       γ ▸[ 𝟙ᵐ ] t →
       γ ▸[ 𝟙ᵐ ] fstʷ 𝟙 A t)
  ¬fstʷₘ′ = ¬fstʷ′ₘ′

opaque

  -- If 𝟙 is not bounded by 𝟘, then a certain usage rule for fstʷ does
  -- not hold.
  --
  -- Note that the assumption 𝟙 ≰ 𝟘 is satisfied by, for instance, the
  -- linearity modality, see
  -- Graded.Modality.Instances.Linearity.Properties.¬fstʷₘ.

  ¬fstʷₘ :
    ¬ 𝟙 ≤ 𝟘 →
    ¬ (∀ {γ : Conₘ 1} {t : Term 1} {p m′} m →
       γ ▸[ m ᵐ· p ] t →
       m ᵐ· p PE.≡ m′ →
       (m′ PE.≡ 𝟙ᵐ → p ≤ 𝟙) →
       γ ▸[ m′ ] fstʷ p A t)
  ¬fstʷₘ = ¬fstʷ′ₘ

------------------------------------------------------------------------
-- Inversion lemmas for usage for sndʷ

opaque

  -- An inversion lemma for sndʷ.

  inv-usage-sndʷ :
    m ᵐ· (𝟘 ∧ 𝟙) PE.≡ m →
    ∀ B →
    γ ▸[ m ] sndʷ p q A B t →
    ∃₂ λ η δ →
      γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ m ] t ×
      δ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] B [ fstʷ p (wk1 A) (var x0) ]↑ ×
      Prodrec-allowed m (𝟘 ∧ 𝟙) p q
  inv-usage-sndʷ {γ = γ} ≡m _ ▸sndʷ =
    case inv-usage-prodrec ▸sndʷ of λ {
      (invUsageProdrec {δ = δ} {η = η} {θ = θ} ▸t ▸var ▸B ok γ≤[𝟘∧𝟙]δ+η) →
    case inv-usage-var ▸var of λ {
      (η≤𝟘 ∙ _ ∙ _) →
      δ
    , θ
    , (begin
         γ                   ≤⟨ γ≤[𝟘∧𝟙]δ+η ⟩
         (𝟘 ∧ 𝟙) ·ᶜ δ +ᶜ η   ≤⟨ +ᶜ-monotoneʳ η≤𝟘 ⟩
         (𝟘 ∧ 𝟙) ·ᶜ δ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
         (𝟘 ∧ 𝟙) ·ᶜ δ        ≡⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
         𝟘ᶜ ∧ᶜ δ             ∎)
    , ▸-cong ≡m ▸t
    , ▸B
    , ok }}
    where
    open ≤ᶜ-reasoning

opaque

  -- An inversion lemma for sndʷ with the mode set to 𝟘ᵐ.

  inv-usage-sndʷ-𝟘ᵐ :
    ¬ Trivialᵐ →
    ∀ B →
    γ ▸[ 𝟘ᵐ ] sndʷ p q A B t →
    ∃ λ δ →
      γ ≤ᶜ 𝟘ᶜ × 𝟘ᶜ ▸[ 𝟘ᵐ ] t ×
      δ ∙ 𝟘 ▸[ 𝟘ᵐ ] B [ fstʷ p (wk1 A) (var x0) ]↑
  inv-usage-sndʷ-𝟘ᵐ {γ = γ} {q = q} 𝟙ᵐ≢𝟘ᵐ B ▸sndʷ =
    case inv-usage-sndʷ ᵐ·-zeroˡ B ▸sndʷ of λ
      (η , δ , leq , ▸t , ▸B , _) →
      _
    , (begin
         γ        ≤⟨ leq ⟩
         𝟘ᶜ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
         η        ≤⟨ ▸-𝟘ᵐ 𝟙ᵐ≢𝟘ᵐ ▸t ⟩
         𝟘ᶜ       ∎)
    , ▸-𝟘′ 𝟙ᵐ≢𝟘ᵐ ▸t
    , (sub ▸B $ begin
         δ ∙ 𝟘            ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
         δ ∙ 𝟘 · q        ≈˘⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ) ⟩
         δ ∙ ⌜ 𝟘ᵐ ⌝ · q  ∎)
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- Usage lemmas for sndʷ

opaque

  -- A usage lemma for sndʷ.

  sndʷₘ :
    m ᵐ· (𝟘 ∧ 𝟙) PE.≡ m →
    Prodrec-allowed m (𝟘 ∧ 𝟙) p q →
    ∀ B →
    γ ▸[ m ] t →
    δ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] B [ fstʷ p (wk1 A) (var x0) ]↑ →
    𝟘ᶜ ∧ᶜ γ ▸[ m ] sndʷ p q A B t
  sndʷₘ {m = m} {p = p} {γ = γ} ≡m ok _ ▸t ▸B = sub
    (prodrecₘ
       (▸-cong (PE.sym ≡m) ▸t)
       (sub var $ begin
          𝟘ᶜ ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙) · p ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙)  ≈⟨ ≈ᶜ-refl ∙ ·[𝟘∧𝟙]·≡𝟘∧· ∙ ·[𝟘∧𝟙]≡𝟘∧ ⟩
          𝟘ᶜ ∙ 𝟘 ∧ ⌜ m ⌝ · p ∙ 𝟘 ∧ ⌜ m ⌝              ≤⟨ ≤ᶜ-refl ∙ ∧-decreasingˡ _ _ ∙ ∧-decreasingʳ _ _ ⟩
          𝟘ᶜ ∙ 𝟘 ∙ ⌜ m ⌝                              ∎)
       ▸B
       ok)
    (begin
       𝟘ᶜ ∧ᶜ γ             ≡˘⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
       (𝟘 ∧ 𝟙) ·ᶜ γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       (𝟘 ∧ 𝟙) ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning

opaque

  -- A usage lemma for sndʷ with the mode set to 𝟘ᵐ.

  sndʷₘ-𝟘ᵐ :
    ¬ Trivialᵐ →
    Prodrec-allowed 𝟘ᵐ (𝟘 ∧ 𝟙) p q →
    ∀ B →
    γ ▸[ 𝟘ᵐ ] t →
    δ ∙ 𝟘 ▸[ 𝟘ᵐ ] B [ fstʷ p (wk1 A) (var x0) ]↑ →
    γ ▸[ 𝟘ᵐ ] sndʷ p q A B t
  sndʷₘ-𝟘ᵐ {q} {γ} {δ} 𝟙ᵐ≢𝟘ᵐ ok B ▸t ▸B = sub
    (sndʷₘ
       ᵐ·-zeroˡ
       ok
       B
       ▸t
       (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
        sub ▸B $ begin
          δ ∙ ⌜ 𝟘ᵐ ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ) ⟩
          δ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
          δ ∙ 𝟘            ∎))
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       γ        ≤⟨ ∧ᶜ-greatest-lower-bound (▸-𝟘ᵐ 𝟙ᵐ≢𝟘ᵐ ▸t) ≤ᶜ-refl ⟩
       𝟘ᶜ ∧ᶜ γ  ∎)

opaque

  -- A usage lemma for sndʷ with the mode set to 𝟙ᵐ and the assumption
  -- that 𝟘 is the largest quantity.

  sndʷₘ-𝟙ᵐ-≤𝟘 :
    (∀ p → p ≤ 𝟘) →
    Prodrec-allowed 𝟙ᵐ (𝟘 ∧ 𝟙) p q →
    ∀ B →
    γ ▸[ 𝟙ᵐ ] t →
    δ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] B [ fstʷ p (wk1 A) (var x0) ]↑ →
    γ ▸[ 𝟙ᵐ ] sndʷ p q A B t
  sndʷₘ-𝟙ᵐ-≤𝟘 {γ = γ} ≤𝟘 ok B ▸t ▸B = sub
    (sndʷₘ
       (let open Tools.Reasoning.PropositionalEquality in begin
         𝟙ᵐ ᵐ· (𝟘 ∧ 𝟙) ≡⟨ ᵐ·-identityˡ ⟩
         ⌞ 𝟘 ∧ 𝟙 ⌟     ≡⟨ ⌞⌟-cong (∧-comm _ _) ⟩
         ⌞ 𝟙 ∧ 𝟘 ⌟     ≡˘⟨ ⌞⌟-cong (≤𝟘 𝟙) ⟩
         ⌞ 𝟙 ⌟         ≡⟨ ⌞𝟙⌟ ⟩
         𝟙ᵐ            ∎)
       ok
       B
       ▸t
       ▸B)
    (let open ≤ᶜ-reasoning in begin
       γ        ≤⟨ ∧ᶜ-greatest-lower-bound (≤ᶜ𝟘ᶜ (≤𝟘 _)) ≤ᶜ-refl ⟩
       𝟘ᶜ ∧ᶜ γ  ∎)

opaque

  -- A usage lemma for sndʷ with the mode set to 𝟙ᵐ and the assumption
  -- that _+_ is pointwise bounded by _∧_.

  sndʷₘ-𝟙ᵐ-+≤∧ :
    (∀ p q → p + q ≤ p ∧ q) →
    Prodrec-allowed 𝟙ᵐ (𝟘 ∧ 𝟙) p q →
    ∀ B →
    γ ▸[ 𝟙ᵐ ] t →
    δ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] B [ fstʷ p (wk1 A) (var x0) ]↑ →
    γ ▸[ 𝟙ᵐ ] sndʷ p q A B t
  sndʷₘ-𝟙ᵐ-+≤∧ +≤∧ = sndʷₘ-𝟙ᵐ-≤𝟘 (+≤∧→≤𝟘 +≤∧)

opaque

  -- If a certain usage rule holds for sndʷ p q A B (where A has type
  -- Term 1), then 𝟙 ≤ 𝟘.

  sndʷₘ→𝟙≤𝟘 :
    {A : Term 1} (B : Term 2) →
    (∀ {γ t} →
     γ ▸[ 𝟙ᵐ ] t →
     γ ▸[ 𝟙ᵐ ] sndʷ p q A B t) →
    𝟙 ≤ 𝟘
  sndʷₘ→𝟙≤𝟘 {p = p} {q = q} {A = A} B =
    (∀ {γ t} → γ ▸[ 𝟙ᵐ ] t → γ ▸[ 𝟙ᵐ ] sndʷ p q A B t)  →⟨ _$ var ⟩
    γ′ ▸[ 𝟙ᵐ ] sndʷ p q A B t′                          →⟨ lemma ⟩
    𝟙 ≤ 𝟘                                               □
    where
    γ′ : Conₘ 1
    γ′ = ε ∙ ⌜ 𝟙ᵐ ⌝
    t′ : Term 1
    t′ = var x0

    lemma : γ′ ▸[ 𝟙ᵐ ] sndʷ p q A B t′ → 𝟙 ≤ 𝟘
    lemma ▸snd-t =
      case inv-usage-prodrec ▸snd-t of λ {
        (invUsageProdrec
           {δ = ε ∙ r} {η = ε ∙ s} ▸t ▸var _ _ (ε ∙ 𝟙≤[𝟘∧𝟙]r+s)) →
      case inv-usage-var ▸var of λ {
        (ε ∙ s≤𝟘 ∙ _ ∙ _) →
      case inv-usage-var ▸t of λ {
        (ε ∙ r≤⌜⌞𝟘∧𝟙⌟⌝) →
      begin
        𝟙                            ≡˘⟨ ⌜𝟙ᵐ⌝ ⟩
        ⌜ 𝟙ᵐ ⌝                       ≤⟨ 𝟙≤[𝟘∧𝟙]r+s ⟩
        (𝟘 ∧ 𝟙) · r + s              ≤⟨ +-monotoneʳ s≤𝟘 ⟩
        (𝟘 ∧ 𝟙) · r + 𝟘              ≡⟨ +-identityʳ _ ⟩
        (𝟘 ∧ 𝟙) · r                  ≤⟨ ·-monotoneʳ r≤⌜⌞𝟘∧𝟙⌟⌝ ⟩
        (𝟘 ∧ 𝟙) · ⌜ 𝟙ᵐ ᵐ· (𝟘 ∧ 𝟙) ⌝  ≡⟨ ·-congˡ (⌜⌝-cong ᵐ·-identityˡ) ⟩
        (𝟘 ∧ 𝟙) · ⌜ ⌞ 𝟘 ∧ 𝟙 ⌟ ⌝      ≡⟨ ·⌜⌞⌟⌝ ⟩
        𝟘 ∧ 𝟙                        ≤⟨ ∧-decreasingˡ _ _ ⟩
        𝟘                            ∎ }}}
      where
      open Tools.Reasoning.PartialOrder ≤-poset

opaque

  -- If 𝟙 is not bounded by 𝟘, then a certain usage rule for
  -- sndʷ p q A B (where A has type Term 1) does not hold.
  --
  -- Note that the assumption 𝟙 ≰ 𝟘 is satisfied by, for instance, the
  -- linearity modality, see
  -- Graded.Modality.Instances.Linearity.Properties.¬sndʷₘ.

  ¬sndʷₘ :
    {A : Term 1} (B : Term 2) →
    ¬ 𝟙 ≤ 𝟘 →
    ¬ ({γ : Conₘ 1} {t : Term 1} →
       γ ▸[ 𝟙ᵐ ] t →
       γ ▸[ 𝟙ᵐ ] sndʷ p q A B t)
  ¬sndʷₘ B 𝟙≰𝟘 hyp = 𝟙≰𝟘 (sndʷₘ→𝟙≤𝟘 B hyp)

------------------------------------------------------------------------
-- Usage lemmas for fst⟨_⟩ and snd⟨_⟩

opaque
  unfolding fst⟨_⟩

  -- A usage lemma for fst⟨_⟩.

  ▸fst⟨⟩ :
    (s PE.≡ 𝕨 → m PE.≡ m ᵐ· (𝟘 ∧ 𝟙)) →
    (s PE.≡ 𝕨 → Prodrec-allowed m (𝟘 ∧ 𝟙) p 𝟘) →
    (⌜ m ⌝ PE.≢ 𝟘 → p ≤ 𝟙) →
    (s PE.≡ 𝕤 → ⌜ m ⌝ PE.≢ 𝟘 → m ᵐ· p PE.≡ m) →
    (s PE.≡ 𝕤 → ⌜ m ⌝ PE.≢ 𝟘 → 𝟙 ≤ ⌜ ⌞ p ⌟ ⌝) →
    γ ▸[ m ] t →
    (s PE.≡ 𝕨 → δ ▸[ 𝟘ᵐ ] A) →
    𝟘ᶜ ∧ᶜ γ ▸[ m ] fst⟨ s ⟩ p A t
  ▸fst⟨⟩ {s = 𝕨} {m} {p} hyp₁ hyp₂ hyp₃ _ _ ▸t ▸A =
    fstʷₘ (hyp₁ PE.refl)
      (begin
         𝟘 ∧ ⌜ m ⌝ · p ≤⟨ ∧-decreasingʳ _ _ ⟩
         ⌜ m ⌝ · p     ≤⟨ lemma ⟩
         ⌜ m ⌝         ∎)
      (hyp₂ PE.refl) ▸t (▸A PE.refl)
      where
      open ≤-reasoning
      lemma : ⌜ m ⌝ · p ≤ ⌜ m ⌝
      lemma = ⌜⌝≡𝟘-elim {m′ = 𝟙ᵐ} (λ m → ⌜ m ⌝ · p ≤ ⌜ m ⌝) m
        ≡-trivial
        (λ 𝟙ᵐ≢𝟘ᵐ _ → begin
          ⌜ 𝟘ᵐ ⌝ · p ≡⟨ ·-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ) ⟩
          𝟘 · p      ≡⟨ ·-zeroˡ _ ⟩
          𝟘          ≡˘⟨ ⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ ⟩
          ⌜ 𝟘ᵐ ⌝     ∎)
        (λ ⌜m⌝≢𝟘 → begin
          ⌜ m ⌝ · p ≤⟨ ·-monotoneʳ (hyp₃ ⌜m⌝≢𝟘) ⟩
          ⌜ m ⌝ · 𝟙 ≡⟨ ·-identityʳ _ ⟩
          ⌜ m ⌝     ∎)
  ▸fst⟨⟩ {s = 𝕤} {m} {p} {γ} {t} {A} _ _ hyp₃ hyp₄ hyp₅ ▸t ▸A =
    ⌜⌝≡𝟘-elim {m′ = 𝟙ᵐ} (λ m → 𝟘ᶜ ∧ᶜ γ ▸[ m ] fst⟨ 𝕤 ⟩ p A t) m
      (λ 𝟙≡𝟘 → fstₘ _ (sub (▸-ᵐ· ▸t) (≈ᶜ-trivial 𝟙≡𝟘))
                 (≡-trivialᵐ (Trivial→Trivialᵐ 𝟙≡𝟘)) (λ _ → ≡-trivial 𝟙≡𝟘))
      (λ { 𝟙ᵐ≢𝟘ᵐ PE.refl →
        sub (fstₘ 𝟘ᵐ (▸-cong (PE.sym ᵐ·-zeroˡ) ▸t) ᵐ·-zeroˡ (⊥-elim ∘→ (_$ ⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ)))
          (∧ᶜ-decreasingʳ _ _) })
      λ ⌜m⌝≡𝟘 →
        let open ≤ᶜ-reasoning in
        sub (fstₘ _ (▸-ᵐ· ▸t) (hyp₄ PE.refl ⌜m⌝≡𝟘) hyp₃) $ begin
          𝟘ᶜ ∧ᶜ γ        ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
          γ              ≈˘⟨ ·ᶜ-identityˡ _ ⟩
          𝟙 ·ᶜ γ         ≤⟨ ·ᶜ-monotoneˡ (hyp₅ PE.refl ⌜m⌝≡𝟘) ⟩
          ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ∎

opaque
  unfolding fst⟨_⟩ snd⟨_⟩

  -- A usage lemma for snd⟨_⟩.

  ▸snd⟨⟩ :
    (s PE.≡ 𝕨 → m ᵐ· (𝟘 ∧ 𝟙) PE.≡ m) →
    (s PE.≡ 𝕨 → Prodrec-allowed m (𝟘 ∧ 𝟙) p q) →
    γ ▸[ m ] t →
    (s PE.≡ 𝕨 →
     δ ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] B [ fst⟨ s ⟩ p (wk1 A) (var x0) ]↑) →
    𝟘ᶜ ∧ᶜ γ ▸[ m ] snd⟨ s ⟩ p q A B t
  ▸snd⟨⟩ {s = 𝕨} {B} hyp₁ hyp₂ ▸t ▸B =
    sndʷₘ (hyp₁ PE.refl) (hyp₂ PE.refl) B ▸t (▸B PE.refl)
  ▸snd⟨⟩ {s = 𝕤} {γ} _ _ ▸t _ = sub
    (sndₘ ▸t)
    (begin
       𝟘ᶜ ∧ᶜ γ  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
       γ        ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

------------------------------------------------------------------------
-- Some lemmas related to Σʰ⟨_⟩

opaque
  unfolding prodʰ

  -- A usage lemma for prodʰˢ.

  ▸prodʰˢ :
    γ ▸[ m ᵐ· p ] t →
    δ ▸[ m ] u →
    p ·ᶜ γ ∧ᶜ δ ▸[ m ] prodʰˢ p t u
  ▸prodʰˢ ▸t ▸u = prodˢₘ (liftₘ ▸t) (liftₘ ▸u)

opaque
  unfolding fstʰ

  -- A usage lemma for fstʰ.

  ▸fstʰ :
    ∀ m →
    (⌜ m ᵐ· p ⌝ ≢ 𝟘 → p ≤ 𝟙) →
    γ ▸[ m ᵐ· p ] t →
    γ ▸[ m ᵐ· p ] fstʰ p t
  ▸fstʰ m ok ▸t = lowerₘ (fstₘ m ▸t PE.refl ok)

opaque
  unfolding sndʰ

  -- A usage lemma for sndʰ.

  ▸sndʰ :
    γ ▸[ m ] t →
    γ ▸[ m ] sndʰ p t
  ▸sndʰ ▸t = lowerₘ (sndₘ ▸t)

opaque
  unfolding prodʰ

  -- A usage lemma for prodʰʷ.

  ▸prodʰʷ :
    γ ▸[ m ᵐ· p ] t →
    δ ▸[ m ] u →
    p ·ᶜ γ +ᶜ δ ▸[ m ] prodʰʷ p t u
  ▸prodʰʷ ▸t ▸u = prodʷₘ (liftₘ ▸t) (liftₘ ▸u)

opaque
  unfolding prodrecʰ⟨_⟩

  -- A usage lemma for prodrecʰ⟨_⟩.

  ▸prodrecʰ⟨⟩ :
    (s PE.≡ 𝕤 → ⌜ m ᵐ· r · p ⌝ PE.≢ 𝟘 → p ≤ 𝟙) →
    (s PE.≡ 𝕤 → r′ ≤ ⌜ m ⌝ · r · (𝟙 + p)) →
    (s PE.≡ 𝕨 → r′ ≤ r) →
    (s PE.≡ 𝕨 → Prodrec-allowed m r p q) →
    (s PE.≡ 𝕨 → ∃ λ η → η ∙ ⌜ 𝟘ᵐ ⌝ · q ▸[ 𝟘ᵐ ] A) →
    γ ▸[ m ᵐ· r ] t →
    δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
    r′ ·ᶜ γ +ᶜ δ ▸[ m ] prodrecʰ⟨ s ⟩ r p q A t u
  ▸prodrecʰ⟨⟩ {m} {r} {p} {δ} hyp₁ hyp₂ hyp₃ ok ▸A ▸t ▸u =
    ▸prodrec⟨⟩ hyp₁ hyp₂ hyp₃ ok ▸A ▸t
      (sub
         (substₘ-lemma
            (▶-cong _
               (λ where
                  x0        → PE.refl
                  (x0 +1)   → PE.refl
                  (_ +1 +1) → PE.refl) $
             wf-replace₂ₘ
               (lowerₘ $ sub var $ begin
                  ⌜ ⌞ ⌜ m ⌝ · r · p ⌟ ⌝ ·ᶜ (𝟘ᶜ , x1 ≔ 𝟙)  ≈⟨ update-cong {x = x1} (·ᶜ-zeroʳ _) (·-identityʳ _) ⟩
                  𝟘ᶜ , x1 ≔ ⌜ ⌞ ⌜ m ⌝ · r · p ⌟ ⌝         ∎)
               (lowerₘ $ sub var $ begin
                  ⌜ ⌞ ⌜ m ⌝ · r ⌟ ⌝ ·ᶜ (𝟘ᶜ , x0 ≔ 𝟙)  ≈⟨ update-cong {x = x0} (·ᶜ-zeroʳ _) (·-identityʳ _) ⟩
                  𝟘ᶜ , x0 ≔ ⌜ ⌞ ⌜ m ⌝ · r ⌟ ⌝         ∎))
            ▸u)
         (begin
            δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r                      ≈˘⟨ ≈ᶜ-trans (+ᶜ-cong (·ᶜ-zeroʳ _) (+ᶜ-congʳ (·ᶜ-zeroʳ _)))
                                                                     (≈ᶜ-trans (+ᶜ-identityˡ _) (+ᶜ-identityˡ _)) ∙
                                                                   PE.trans
                                                                     (PE.cong₂ _+_
                                                                        (·-identityʳ _)
                                                                        (PE.trans (+-identityʳ _) (·-zeroʳ _)))
                                                                     (+-identityʳ _) ∙
                                                                   PE.trans
                                                                     (PE.cong₂ _+_ (·-zeroʳ _) (+-identityʳ _))
                                                                     (PE.trans (+-identityˡ _) (·-identityʳ _)) ⟩
            (⌜ m ⌝ · r · p) ·ᶜ 𝟘ᶜ +ᶜ (⌜ m ⌝ · r) ·ᶜ 𝟘ᶜ +ᶜ δ ∙
            (⌜ m ⌝ · r · p) · 𝟙 + (⌜ m ⌝ · r) · 𝟘 + 𝟘 ∙
            (⌜ m ⌝ · r · p) · 𝟘 + (⌜ m ⌝ · r) · 𝟙 + 𝟘          ≡⟨⟩

            (⌜ m ⌝ · r · p) ·ᶜ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘) +ᶜ
            (⌜ m ⌝ · r) ·ᶜ (𝟘ᶜ ∙ 𝟙) +ᶜ (δ ∙ 𝟘 ∙ 𝟘)             ≈˘⟨ <*-replace₂ₘ ⟩

            (δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r) <*
              replace₂ₘ (𝟘ᶜ ∙ 𝟙 ∙ 𝟘) (𝟘ᶜ ∙ 𝟙)                  ∎))
    where
    open ≤ᶜ-reasoning
