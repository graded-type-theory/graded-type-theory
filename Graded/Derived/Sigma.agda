------------------------------------------------------------------------
-- An investigation of to what degree weak Σ-types can emulate strong
-- Σ-types, and vice versa
------------------------------------------------------------------------

-- This module contains parts of an investigation of to what degree
-- weak Σ-types can emulate strong Σ-types, and vice versa. This
-- investigation was prompted by a question asked by an anonymous
-- reviewer. See also Definition.Untyped.Sigma, which contains some
-- basic definitions, and
-- Definition.Typed.Consequences.DerivedRules.Sigma, which contains
-- properties related to typing. This module contains properties
-- related to usage.

open import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Derived.Sigma
  {a} {M : Set a}
  (𝕄 : Modality M)
  (UR : Usage-restrictions M)
  where

open Modality 𝕄
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Weakening 𝕄 UR
open import Graded.Substitution.Properties 𝕄 UR

open import Graded.Mode 𝕄

open import Definition.Untyped M
open import Definition.Untyped.Sigma M as Sigma
  using (prodrecₚ; module Fstᵣ-sndᵣ)

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  n     : Nat
  A t u : Term _
  p q r : M
  γ δ   : Conₘ _
  m     : Mode

------------------------------------------------------------------------
-- Some private lemmas related to the modality

private

  -- Some lemmas used below.

  𝟘≰𝟙→𝟘∧𝟙≢𝟘 : ¬ 𝟘 ≤ 𝟙 → 𝟘 ∧ 𝟙 ≢ 𝟘
  𝟘≰𝟙→𝟘∧𝟙≢𝟘 𝟘≰𝟙 =
    𝟘 ∧ 𝟙 PE.≡ 𝟘  →⟨ flip (PE.subst (_≤ _)) (∧-decreasingʳ 𝟘 𝟙) ⟩
    𝟘 ≤ 𝟙         →⟨ 𝟘≰𝟙 ⟩
    ⊥             □

  𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ :
    ∀ m → ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 ⊎ m ≢ 𝟙ᵐ → m ᵐ· (𝟘 ∧ 𝟙) PE.≡ m
  𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ = λ where
    𝟘ᵐ _           → PE.refl
    𝟙ᵐ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ → case 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ of λ where
      (inj₁ 𝟘≰𝟙)        → ≉𝟘→⌞⌟≡𝟙ᵐ (𝟘≰𝟙→𝟘∧𝟙≢𝟘 𝟘≰𝟙)
      (inj₂ (inj₁ 𝟙≡𝟘)) → Mode-propositional-if-𝟙≡𝟘 𝟙≡𝟘
      (inj₂ (inj₂ ≢𝟙ᵐ)) → ⊥-elim (≢𝟙ᵐ PE.refl)

  ≤𝟘→𝟘≰𝟙⊎𝟙≡𝟘 : 𝟙 PE.≡ 𝟘 ⊎ 𝟙 ≢ 𝟘 → (∀ p → p ≤ 𝟘) → ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘
  ≤𝟘→𝟘≰𝟙⊎𝟙≡𝟘 = λ where
    (inj₁ 𝟙≡𝟘) _  → inj₂ 𝟙≡𝟘
    (inj₂ 𝟙≢𝟘) ≤𝟘 → inj₁
      (𝟘 ≤ 𝟙     →⟨ ≤-antisym (≤𝟘 _) ⟩
       𝟙 PE.≡ 𝟘  →⟨ 𝟙≢𝟘 ⟩
       ⊥         □)

  [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ : (𝟘 ∧ 𝟙) ·ᶜ γ PE.≡ 𝟘ᶜ ∧ᶜ γ
  [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ {γ = γ} =
    (𝟘 ∧ 𝟙) ·ᶜ γ      ≡⟨ ≈ᶜ→≡ (·ᶜ-distribʳ-∧ᶜ _ _ _) ⟩
    𝟘 ·ᶜ γ ∧ᶜ 𝟙 ·ᶜ γ  ≡⟨ ≈ᶜ→≡ (∧ᶜ-cong (·ᶜ-zeroˡ _) (·ᶜ-identityˡ _)) ⟩
    𝟘ᶜ ∧ᶜ γ           ∎
    where
    open Tools.Reasoning.PropositionalEquality

  [𝟘∧𝟙]·≡𝟘∧ : (𝟘 ∧ 𝟙) · p PE.≡ 𝟘 ∧ p
  [𝟘∧𝟙]·≡𝟘∧ {p = p} =
    (𝟘 ∧ 𝟙) · p    ≡⟨ ·-distribʳ-∧ _ _ _ ⟩
    𝟘 · p ∧ 𝟙 · p  ≡⟨ ∧-cong (·-zeroˡ _) (·-identityˡ _) ⟩
    𝟘 ∧ p          ∎
    where
    open Tools.Reasoning.PropositionalEquality

  ·[𝟘∧𝟙]≡𝟘∧ : p · (𝟘 ∧ 𝟙) PE.≡ 𝟘 ∧ p
  ·[𝟘∧𝟙]≡𝟘∧ {p = p} =
    p · (𝟘 ∧ 𝟙)    ≡⟨ ·-distribˡ-∧ _ _ _ ⟩
    p · 𝟘 ∧ p · 𝟙  ≡⟨ ∧-cong (·-zeroʳ _) (·-identityʳ _) ⟩
    𝟘 ∧ p          ∎
    where
    open Tools.Reasoning.PropositionalEquality

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

-- If _+_ is pointwise bounded by _∧_, then a usage rule like the one
-- for prodᵣ can be derived for prodₚ.

prodₚᵣₘ :
  (∀ p q → p + q ≤ p ∧ q) →
  γ ▸[ m ᵐ· p ] t →
  δ ▸[ m ] u →
  p ·ᶜ γ +ᶜ δ ▸[ m ] prodₚ p t u
prodₚᵣₘ +≤∧ ▸t ▸u = sub (prodₚₘ ▸t ▸u) (+ᶜ≤ᶜ∧ᶜ +≤∧)

-- If _∧_ is pointwise bounded by _+_, then a usage rule like the one
-- for prodₚ can be derived for prodᵣ.

prodᵣₚₘ :
  (∀ p q → p ∧ q ≤ p + q) →
  γ ▸[ m ᵐ· p ] t →
  δ ▸[ m ] u →
  p ·ᶜ γ ∧ᶜ δ ▸[ m ] prodᵣ p t u
prodᵣₚₘ ∧≤+ ▸t ▸u = sub (prodᵣₘ ▸t ▸u) (∧ᶜ≤ᶜ+ᶜ ∧≤+)

------------------------------------------------------------------------
-- Usage lemmas for prodrecₚ

-- A usage lemma for prodrecₚ.

prodrecₚₘ :
  (m ᵐ· r · p PE.≡ 𝟙ᵐ → p ≤ 𝟙) →
  γ ▸[ m ᵐ· r ] t →
  δ ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
  (⌜ m ⌝ · r · (𝟙 + p)) ·ᶜ γ +ᶜ δ ▸[ m ] prodrecₚ p t u
prodrecₚₘ {m = m} {r = r} {p = p} {γ = γ} {δ = δ} mrp≡𝟙→p≤𝟙 ▸t ▸u = sub
  (doubleSubstₘ-lemma₁ ▸u
     (sndₘ ▸t)
     (fstₘ (m ᵐ· r) (▸-cong (lemma m) (▸-· ▸t)) (ᵐ·-·-assoc m) mrp≡𝟙→p≤𝟙))
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
  lemma : ∀ m → ⌞ p ⌟ ·ᵐ m ᵐ· r PE.≡ (m ᵐ· r) ᵐ· p
  lemma 𝟘ᵐ =
    ⌞ p ⌟ ·ᵐ 𝟘ᵐ  ≡⟨ ·ᵐ-zeroʳ-𝟘ᵐ ⟩
    𝟘ᵐ           ∎
    where
    open Tools.Reasoning.PropositionalEquality
  lemma 𝟙ᵐ =
    ⌞ p ⌟ ·ᵐ ⌞ r ⌟  ≡⟨ ·ᵐ-comm ⌞ _ ⌟ _ ⟩
    ⌞ r ⌟ ·ᵐ ⌞ p ⌟  ≡⟨ ⌞⌟·ᵐ ⟩
    ⌞ r · p ⌟       ≡˘⟨ ⌞⌟ᵐ· ⟩
    ⌞ r ⌟ ᵐ· p      ∎
    where
    open Tools.Reasoning.PropositionalEquality

  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A variant of the main usage lemma for prodrecₚ with the mode set
-- to 𝟘ᵐ.

prodrecₚₘ-𝟘ᵐ :
  ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
  γ ▸[ 𝟘ᵐ ] t →
  δ ∙ 𝟘 ∙ 𝟘 ▸[ 𝟘ᵐ ] u →
  δ ▸[ 𝟘ᵐ ] prodrecₚ p t u
prodrecₚₘ-𝟘ᵐ {γ = γ} {δ = δ} {p = p} ⦃ ok = ok ⦄ ▸t ▸u = sub
  (prodrecₚₘ
     (λ ())
     ▸t
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub ▸u $ begin
        δ ∙ 𝟘 · 𝟘 · p ∙ 𝟘 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
        δ ∙ 𝟘 ∙ 𝟘              ∎))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     δ                            ≈˘⟨ +ᶜ-identityˡ _ ⟩
     𝟘ᶜ +ᶜ δ                      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
     𝟘 ·ᶜ γ +ᶜ δ                  ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (·-zeroˡ _)) ⟩
     (𝟘 · 𝟘 · (𝟙 + p)) ·ᶜ γ +ᶜ δ  ∎)

-- A variant of the main usage lemma for prodrecₚ with the mode set to
-- 𝟙ᵐ and the quantity p to 𝟘.

prodrecₚₘ-𝟙ᵐ-𝟘 :
  𝟘 ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed →
  γ ▸[ ⌞ r ⌟ ] t →
  δ ∙ 𝟘 ∙ r ▸[ 𝟙ᵐ ] u →
  r ·ᶜ γ +ᶜ δ ▸[ 𝟙ᵐ ] prodrecₚ 𝟘 t u
prodrecₚₘ-𝟙ᵐ-𝟘 {γ = γ} {r = r} {δ = δ} ok ▸t ▸u = sub
  (prodrecₚₘ
     (λ ⌞r𝟘⌟≡𝟙 → case ok of λ where
       (inj₁ 𝟘≤𝟙) → 𝟘≤𝟙
       (inj₂ 𝟘ᵐ-ok) → let open Tools.Reasoning.PropositionalEquality in
         case begin
           𝟘ᵐ[ 𝟘ᵐ-ok ] ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
           𝟘ᵐ?         ≡˘⟨ ⌞𝟘⌟≡𝟘ᵐ? ⟩
           ⌞ 𝟘 ⌟       ≡˘⟨ ⌞⌟-cong (·-zeroʳ r) ⟩
           ⌞ r · 𝟘 ⌟   ≡⟨ ⌞r𝟘⌟≡𝟙 ⟩
           𝟙ᵐ          ∎
         of λ ())
     ▸t
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub ▸u $ begin
        δ ∙ 𝟙 · r · 𝟘 ∙ 𝟙 · r  ≈⟨ ≈ᶜ-refl ∙ PE.trans (·-congˡ (·-zeroʳ _)) (·-zeroʳ _) ∙ ·-identityˡ _ ⟩
        δ ∙ 𝟘 ∙ r              ∎))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     r ·ᶜ γ +ᶜ δ                  ≈˘⟨ +ᶜ-congʳ $ ·ᶜ-congʳ $
                                      PE.trans (·-identityˡ _) $
                                      PE.trans (·-congˡ (+-identityʳ _)) $
                                      ·-identityʳ _ ⟩
     (𝟙 · r · (𝟙 + 𝟘)) ·ᶜ γ +ᶜ δ  ∎)

-- A variant of the main usage lemma for prodrecₚ with the mode set to
-- 𝟙ᵐ and the quantity p to 𝟙. Note that the context in the conclusion
-- is (r + r) ·ᶜ γ +ᶜ δ, while the corresponding context in the usage
-- rule for prodrec is r ·ᶜ γ +ᶜ δ.

prodrecₚₘ-𝟙ᵐ-𝟙 :
  γ ▸[ ⌞ r ⌟ ] t →
  δ ∙ r ∙ r ▸[ 𝟙ᵐ ] u →
  (r + r) ·ᶜ γ +ᶜ δ ▸[ 𝟙ᵐ ] prodrecₚ 𝟙 t u
prodrecₚₘ-𝟙ᵐ-𝟙 {γ = γ} {r = r} {δ = δ} ▸t ▸u = sub
  (prodrecₚₘ
     (λ _ → ≤-refl)
     ▸t
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub ▸u $ begin
        δ ∙ 𝟙 · r · 𝟙 ∙ 𝟙 · r  ≈⟨ ≈ᶜ-refl ∙ PE.trans (·-identityˡ _) (·-identityʳ _) ∙ ·-identityˡ _ ⟩
        δ ∙ r ∙ r              ∎))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     (r + r) ·ᶜ γ +ᶜ δ            ≈˘⟨ +ᶜ-congʳ $ ·ᶜ-congʳ $
                                      PE.trans (·-identityˡ _) $
                                      PE.trans (·-distribˡ-+ _ _ _) $
                                      +-cong (·-identityʳ _) (·-identityʳ _) ⟩
     (𝟙 · r · (𝟙 + 𝟙)) ·ᶜ γ +ᶜ δ  ∎)

-- A variant of the previous lemma with the assumption that _∧_ is
-- pointwise bounded by _+_.

prodrecₚₘ-𝟙ᵐ-𝟙-∧≤+ :
  (∀ p q → p ∧ q ≤ p + q) →
  γ ▸[ ⌞ r ⌟ ] t →
  δ ∙ r ∙ r ▸[ 𝟙ᵐ ] u →
  r ·ᶜ γ +ᶜ δ ▸[ 𝟙ᵐ ] prodrecₚ 𝟙 t u
prodrecₚₘ-𝟙ᵐ-𝟙-∧≤+ {γ = γ} {r = r} {δ = δ} ∧≤+ ▸t ▸u = sub
  (prodrecₚₘ-𝟙ᵐ-𝟙 ▸t ▸u)
  (begin
     r ·ᶜ γ +ᶜ δ        ≈˘⟨ +ᶜ-congʳ (·ᶜ-congʳ (∧-idem _)) ⟩
     (r ∧ r) ·ᶜ γ +ᶜ δ  ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ (∧≤+ _ _)) ⟩
     (r + r) ·ᶜ γ +ᶜ δ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

------------------------------------------------------------------------
-- An investigation of different potential implementations of a first
-- projection for weak Σ-types

-- A generalised first projection with two extra quantities.

fstᵣ′ : M → M → M → Term n → Term n → Term n
fstᵣ′ r p q = Fstᵣ-sndᵣ.fstᵣ r q p

-- An inversion lemma for fstᵣ′.

inv-usage-fstᵣ′ :
  γ ▸[ m ] fstᵣ′ r p q A t →
  ∃₂ λ η δ →
    γ ≤ᶜ r ·ᶜ η ×
    η ▸[ m ᵐ· r ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    ⌜ m ⌝ · r · p ≤ ⌜ m ⌝ ×
    ⌜ m ⌝ · r ≤ 𝟘 ×
    Prodrec-allowed r p q
inv-usage-fstᵣ′ {γ = γ} {m = m} {r = r} {p = p} {q = q} ▸fstᵣ′ =
  case inv-usage-prodrec ▸fstᵣ′ of λ {
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

-- An inversion lemma for fstᵣ′ with the mode set to 𝟙ᵐ.

inv-usage-fstᵣ′-𝟙ᵐ :
  γ ▸[ 𝟙ᵐ ] fstᵣ′ r p q A t →
  ∃₂ λ η δ →
    γ ≤ᶜ r ·ᶜ η ×
    η ▸[ ⌞ r ⌟ ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    r · p ≤ 𝟙 ×
    r ≤ 𝟘 ×
    Prodrec-allowed r p q
inv-usage-fstᵣ′-𝟙ᵐ {r = r} {p = p} ▸fstᵣ′ =
  case inv-usage-fstᵣ′ ▸fstᵣ′ of λ {
    (_ , _ , leq₁ , ▸t , ▸A , leq₂ , leq₃ , ok) →
  _ , _ , leq₁ , ▸t , ▸A ,
  (begin
     r · p      ≡˘⟨ ·-identityˡ _ ⟩
     𝟙 · r · p  ≤⟨ leq₂ ⟩
     𝟙          ∎) ,
  (begin
     r      ≡˘⟨ ·-identityˡ _ ⟩
     𝟙 · r  ≤⟨ leq₃ ⟩
     𝟘      ∎) ,
  ok }
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- If 𝟘 ≰ 𝟙 then no application of fstᵣ′ 𝟘 is well-resourced at
-- mode 𝟙ᵐ.

𝟘≰𝟙→fstᵣ′-𝟘-not-ok :
  ¬ 𝟘 ≤ 𝟙 →
  ¬ γ ▸[ 𝟙ᵐ ] fstᵣ′ 𝟘 p q A t
𝟘≰𝟙→fstᵣ′-𝟘-not-ok {γ = γ} {p = p} {q = q} {A = A} {t = t} 𝟘≰𝟙 =
  γ ▸[ 𝟙ᵐ ] fstᵣ′ 𝟘 p q A t  →⟨ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ inv-usage-fstᵣ′-𝟙ᵐ ⟩
  𝟘 · p ≤ 𝟙                  →⟨ ≤-trans (≤-reflexive (PE.sym (·-zeroˡ _))) ⟩
  𝟘 ≤ 𝟙                      →⟨ 𝟘≰𝟙 ⟩
  ⊥                          □

-- If 𝟙 ≰ 𝟘 then no application of fstᵣ′ 𝟙 is well-resourced at
-- mode 𝟙ᵐ.

𝟙≰𝟘→fstᵣ′-𝟙-not-ok :
  ¬ 𝟙 ≤ 𝟘 →
  ¬ γ ▸[ 𝟙ᵐ ] fstᵣ′ 𝟙 p q A t
𝟙≰𝟘→fstᵣ′-𝟙-not-ok {γ = γ} {p = p} {q = q} {A = A} {t = t} 𝟙≰𝟘 =
  γ ▸[ 𝟙ᵐ ] fstᵣ′ 𝟙 p q A t  →⟨ proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ inv-usage-fstᵣ′-𝟙ᵐ ⟩
  𝟙 ≤ 𝟘                      →⟨ 𝟙≰𝟘 ⟩
  ⊥                          □

-- An inversion lemma for fstᵣ′ with the mode set to 𝟙ᵐ and either
-- r ≢ 𝟘 or 𝟙 ≡ 𝟘.

inv-usage-fstᵣ′-≢𝟘-𝟙ᵐ :
  r ≢ 𝟘 ⊎ 𝟙 PE.≡ 𝟘 →
  γ ▸[ 𝟙ᵐ ] fstᵣ′ r p q A t →
  ∃₂ λ η δ →
    γ ≤ᶜ r ·ᶜ η ×
    η ▸[ 𝟙ᵐ ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    r · p ≤ 𝟙 ×
    r ≤ 𝟘 ×
    Prodrec-allowed r p q
inv-usage-fstᵣ′-≢𝟘-𝟙ᵐ r≢𝟘⊎𝟙≡𝟘 ▸fstᵣ′ =
  case inv-usage-fstᵣ′-𝟙ᵐ ▸fstᵣ′ of λ {
    (_ , _ , leq₁ , ▸t , ▸A , leq₂ , leq₃ , ok) →
  _ , _ , leq₁ ,
  ▸-cong
    (case r≢𝟘⊎𝟙≡𝟘 of λ where
       (inj₁ r≢𝟘) → ≉𝟘→⌞⌟≡𝟙ᵐ r≢𝟘
       (inj₂ 𝟙≡𝟘) → Mode-propositional-if-𝟙≡𝟘 𝟙≡𝟘)
    ▸t ,
  ▸A , leq₂ , leq₃ , ok }

-- An inversion lemma for fstᵣ′ with the mode set to 𝟙ᵐ, r set to
-- 𝟘 ∧ 𝟙, and either 𝟘 ≰ 𝟙 or 𝟙 ≡ 𝟘.

inv-usage-fstᵣ′-𝟘∧𝟙-𝟙ᵐ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 →
  γ ▸[ 𝟙ᵐ ] fstᵣ′ (𝟘 ∧ 𝟙) p q A t →
  ∃₂ λ η δ →
    γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ 𝟙ᵐ ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    𝟘 ∧ p ≤ 𝟙 ×
    Prodrec-allowed (𝟘 ∧ 𝟙) p q
inv-usage-fstᵣ′-𝟘∧𝟙-𝟙ᵐ {γ = γ} {p = p} 𝟘≰𝟙⊎𝟙≡𝟘 ▸fstᵣ′ =
  case inv-usage-fstᵣ′-≢𝟘-𝟙ᵐ 𝟘∧𝟙≢𝟘⊎𝟙≡𝟘 ▸fstᵣ′ of λ {
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
  where
  𝟘∧𝟙≢𝟘⊎𝟙≡𝟘 = case 𝟘≰𝟙⊎𝟙≡𝟘 of λ where
    (inj₁ 𝟘≰𝟙) → inj₁ (𝟘≰𝟙→𝟘∧𝟙≢𝟘 𝟘≰𝟙)
    (inj₂ 𝟙≡𝟘) → inj₂ 𝟙≡𝟘

------------------------------------------------------------------------
-- The first and second projections for weak Σ-types

open Fstᵣ-sndᵣ (𝟘 ∧ 𝟙) 𝟘 public using (fstᵣ; sndᵣ)

------------------------------------------------------------------------
-- Inversion lemmas for usage for fstᵣ

-- An inversion lemma for fstᵣ.

inv-usage-fstᵣ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 ⊎ m ≢ 𝟙ᵐ →
  γ ▸[ m ] fstᵣ p A t →
  ∃₂ λ η δ →
    γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ m ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    𝟘 ∧ ⌜ m ⌝ · p ≤ ⌜ m ⌝ ×
    Prodrec-allowed (𝟘 ∧ 𝟙) p 𝟘
inv-usage-fstᵣ {m = m} {γ = γ} {p = p} 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ ▸fstᵣ =
  case inv-usage-fstᵣ′ ▸fstᵣ of λ {
    (η , δ , leq₁ , ▸t , ▸A , leq₂ , leq₃ , ok) →
  _ , _ ,
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     γ             ≤⟨ leq₁ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ η  ≡⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
     𝟘ᶜ ∧ᶜ η       ∎) ,
  ▸-cong (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ) ▸t ,
  ▸A ,
  (let open Tools.Reasoning.PartialOrder ≤-poset in begin
     𝟘 ∧ ⌜ m ⌝ · p        ≡˘⟨ ·[𝟘∧𝟙]·≡𝟘∧· ⟩
     ⌜ m ⌝ · (𝟘 ∧ 𝟙) · p  ≤⟨ leq₂ ⟩
     ⌜ m ⌝                ∎) ,
  ok }

-- An inversion lemma for fstᵣ with the mode set to 𝟘ᵐ.

inv-usage-fstᵣ-𝟘ᵐ :
  ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
  γ ▸[ 𝟘ᵐ ] fstᵣ p A t →
  ∃ λ δ →
    γ ≤ᶜ 𝟘ᶜ × 𝟘ᶜ ▸[ 𝟘ᵐ ] t ×
    δ ▸[ 𝟘ᵐ ] A ×
    Prodrec-allowed (𝟘 ∧ 𝟙) p 𝟘
inv-usage-fstᵣ-𝟘ᵐ {γ = γ} ▸fstᵣ =
  case inv-usage-fstᵣ (inj₂ (inj₂ (λ ()))) ▸fstᵣ of λ {
    (η , _ , leq₁ , ▸t , ▸A , leq₂ , ok) →
  _ ,
  (begin
     γ        ≤⟨ leq₁ ⟩
     𝟘ᶜ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
     η        ≤⟨ ▸-𝟘ᵐ ▸t ⟩
     𝟘ᶜ       ∎) ,
  (sub (▸-· {m′ = 𝟘ᵐ} ▸t) $ begin
     𝟘ᶜ      ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
     𝟘 ·ᶜ η  ∎) ,
  ▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸A , ok }
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for fstᵣ with the mode set to 𝟙ᵐ.

inv-usage-fstᵣ-𝟙ᵐ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 →
  γ ▸[ 𝟙ᵐ ] fstᵣ p A t →
  ∃₂ λ η δ →
    γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ 𝟙ᵐ ] t ×
    δ ▸[ 𝟘ᵐ? ] A ×
    𝟘 ∧ p ≤ 𝟙 ×
    Prodrec-allowed (𝟘 ∧ 𝟙) p 𝟘
inv-usage-fstᵣ-𝟙ᵐ {p = p} 𝟘≰𝟙⊎𝟙≡𝟘 ▸fstᵣ =
  case inv-usage-fstᵣ 𝟘≰𝟙⊎𝟙≡𝟘⊎𝟙ᵐ≢𝟙ᵐ ▸fstᵣ of λ {
    (_ , _ , leq₁ , ▸t , ▸A , leq₂ , ok) →
  _ , _ , leq₁ , ▸t , ▸A ,
  (begin
     𝟘 ∧ p      ≡˘⟨ ∧-congˡ (·-identityˡ _) ⟩
     𝟘 ∧ 𝟙 · p  ≤⟨ leq₂ ⟩
     𝟙          ∎) ,
  ok }
  where
  open Tools.Reasoning.PartialOrder ≤-poset

  𝟘≰𝟙⊎𝟙≡𝟘⊎𝟙ᵐ≢𝟙ᵐ = case 𝟘≰𝟙⊎𝟙≡𝟘 of λ where
    (inj₁ 𝟘≰𝟙) → inj₁ 𝟘≰𝟙
    (inj₂ 𝟙≡𝟘) → inj₂ (inj₁ 𝟙≡𝟘)

------------------------------------------------------------------------
-- Usage lemmas for fstᵣ

-- A usage lemma for fstᵣ.

fstᵣₘ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 ⊎ m ≢ 𝟙ᵐ →
  𝟘 ∧ ⌜ m ⌝ · p ≤ ⌜ m ⌝ →
  Prodrec-allowed (𝟘 ∧ 𝟙) p 𝟘 →
  γ ▸[ m ] t →
  δ ▸[ 𝟘ᵐ? ] A →
  𝟘ᶜ ∧ᶜ γ ▸[ m ] fstᵣ p A t
fstᵣₘ {m = m} {p = p} {γ = γ} {δ = δ} 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ 𝟘∧mp≤m ok ▸t ▸A = sub
  (prodrecₘ
     (▸-cong (PE.sym (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ)) ▸t)
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub var $ begin
        𝟘ᶜ ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙) · p ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙)  ≈⟨ ≈ᶜ-refl ∙ ·[𝟘∧𝟙]·≡𝟘∧· ∙ ·[𝟘∧𝟙]≡𝟘∧ ⟩
        𝟘ᶜ ∙ 𝟘 ∧ ⌜ m ⌝ · p ∙ 𝟘 ∧ ⌜ m ⌝              ≤⟨ ≤ᶜ-refl ∙ 𝟘∧mp≤m ∙ ∧-decreasingˡ _ _ ⟩
        𝟘ᶜ ∙ ⌜ m ⌝ ∙ 𝟘                              ∎)
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (wkUsage (step id) ▸A) $ begin
        δ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
        δ ∙ 𝟘            ∎)
     ok)
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ ∧ᶜ γ             ≡˘⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)

-- A usage lemma for fstᵣ with the mode set to 𝟘ᵐ.

fstᵣₘ-𝟘ᵐ :
  ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
  Prodrec-allowed (𝟘 ∧ 𝟙) p 𝟘 →
  γ ▸[ 𝟘ᵐ ] t →
  δ ▸[ 𝟘ᵐ ] A →
  γ ▸[ 𝟘ᵐ ] fstᵣ p A t
fstᵣₘ-𝟘ᵐ {p = p} {γ = γ} {δ = δ} ok ▸t ▸A = sub
  (fstᵣₘ
     (inj₂ (inj₂ (λ ())))
     (let open Tools.Reasoning.PartialOrder ≤-poset in begin
        𝟘 ∧ 𝟘 · p  ≡⟨ ∧-congˡ (·-zeroˡ _) ⟩
        𝟘 ∧ 𝟘      ≡⟨ ∧-idem _ ⟩
        𝟘          ∎)
     ok
     ▸t
     (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸A))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     γ        ≤⟨ ∧ᶜ-greatest-lower-bound (▸-𝟘ᵐ ▸t) ≤ᶜ-refl ⟩
     𝟘ᶜ ∧ᶜ γ  ∎)

-- A usage lemma for fstᵣ with the mode set to 𝟙ᵐ.

fstᵣₘ-𝟙ᵐ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 →
  𝟘 ∧ p ≤ 𝟙 →
  Prodrec-allowed (𝟘 ∧ 𝟙) p 𝟘 →
  γ ▸[ 𝟙ᵐ ] t →
  δ ▸[ 𝟘ᵐ? ] A →
  𝟘ᶜ ∧ᶜ γ ▸[ 𝟙ᵐ ] fstᵣ p A t
fstᵣₘ-𝟙ᵐ {p = p} 𝟘≰𝟙⊎𝟙≢𝟘 𝟘∧p≤𝟙 = fstᵣₘ
  (case 𝟘≰𝟙⊎𝟙≢𝟘 of λ where
     (inj₁ 𝟘≰𝟙) → inj₁ 𝟘≰𝟙
     (inj₂ 𝟙≢𝟘) → inj₂ (inj₁ 𝟙≢𝟘))
  (begin
     𝟘 ∧ 𝟙 · p  ≡⟨ ∧-congˡ (·-identityˡ _) ⟩
     𝟘 ∧ p      ≤⟨ 𝟘∧p≤𝟙 ⟩
     𝟙          ∎)
  where
  open Tools.Reasoning.PartialOrder ≤-poset

-- A usage lemma for fstᵣ with the mode set to 𝟙ᵐ and the assumption
-- that 𝟘 is the largest quantity.

fstᵣₘ-𝟙ᵐ-≤𝟘 :
  𝟙 PE.≡ 𝟘 ⊎ 𝟙 ≢ 𝟘 →
  (∀ p → p ≤ 𝟘) →
  p ≤ 𝟙 →
  Prodrec-allowed (𝟘 ∧ 𝟙) p 𝟘 →
  γ ▸[ 𝟙ᵐ ] t →
  δ ▸[ 𝟘ᵐ? ] A →
  γ ▸[ 𝟙ᵐ ] fstᵣ p A t
fstᵣₘ-𝟙ᵐ-≤𝟘 {p = p} {γ = γ} 𝟙≡𝟘⊎𝟙≢𝟘 ≤𝟘 p≤𝟙 ok ▸t ▸A = sub
  (fstᵣₘ-𝟙ᵐ
     (≤𝟘→𝟘≰𝟙⊎𝟙≡𝟘 𝟙≡𝟘⊎𝟙≢𝟘 ≤𝟘)
     (let open Tools.Reasoning.PartialOrder ≤-poset in begin
        𝟘 ∧ p  ≤⟨ ∧-decreasingʳ _ _ ⟩
        p      ≤⟨ p≤𝟙 ⟩
        𝟙      ∎)
     ok
     ▸t
     ▸A)
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     γ        ≤⟨ ∧ᶜ-greatest-lower-bound (≤ᶜ𝟘ᶜ (≤𝟘 _)) ≤ᶜ-refl ⟩
     𝟘ᶜ ∧ᶜ γ  ∎)

-- A usage lemma for fstᵣ with the mode set to 𝟙ᵐ and the assumption
-- that _+_ is pointwise bounded by _∧_.

fstᵣₘ-𝟙ᵐ-∧≤+ :
  𝟙 PE.≡ 𝟘 ⊎ 𝟙 ≢ 𝟘 →
  (∀ p q → p + q ≤ p ∧ q) →
  p ≤ 𝟙 →
  Prodrec-allowed (𝟘 ∧ 𝟙) p 𝟘 →
  γ ▸[ 𝟙ᵐ ] t →
  δ ▸[ 𝟘ᵐ? ] A →
  γ ▸[ 𝟙ᵐ ] fstᵣ p A t
fstᵣₘ-𝟙ᵐ-∧≤+ 𝟙≡𝟘⊎𝟙≢𝟘 +≤∧ = fstᵣₘ-𝟙ᵐ-≤𝟘 𝟙≡𝟘⊎𝟙≢𝟘 (+≤∧→≤𝟘 +≤∧)

------------------------------------------------------------------------
-- Inversion lemmas for usage for sndᵣ

-- An inversion lemma for sndᵣ.

inv-usage-sndᵣ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 ⊎ m ≢ 𝟙ᵐ →
  ∀ B →
  γ ▸[ m ] sndᵣ p q A B t →
  ∃₂ λ η δ →
    γ ≤ᶜ 𝟘ᶜ ∧ᶜ η × η ▸[ m ] t ×
    δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fstᵣ p (wk1 A) (var x0) ]↑ ×
    Prodrec-allowed (𝟘 ∧ 𝟙) p q
inv-usage-sndᵣ {γ = γ} 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ _ ▸sndᵣ =
  case inv-usage-prodrec ▸sndᵣ of λ {
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
  , ▸-cong (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ) ▸t
  , ▸B
  , ok }}
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- An inversion lemma for sndᵣ with the mode set to 𝟘ᵐ.

inv-usage-sndᵣ-𝟘ᵐ :
  ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
  ∀ B →
  γ ▸[ 𝟘ᵐ ] sndᵣ p q A B t →
  ∃ λ δ →
    γ ≤ᶜ 𝟘ᶜ × 𝟘ᶜ ▸[ 𝟘ᵐ ] t ×
    δ ∙ 𝟘 ▸[ 𝟘ᵐ ] B [ fstᵣ p (wk1 A) (var x0) ]↑ ×
    Prodrec-allowed (𝟘 ∧ 𝟙) p q
inv-usage-sndᵣ-𝟘ᵐ {γ = γ} {q = q} ⦃ ok = 𝟘ᵐ-ok ⦄ B ▸sndᵣ =
  case inv-usage-sndᵣ (inj₂ (inj₂ (λ ()))) B ▸sndᵣ of λ {
    (η , δ , leq , ▸t , ▸B , ok) →
    _
  , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
       γ        ≤⟨ leq ⟩
       𝟘ᶜ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
       η        ≤⟨ ▸-𝟘ᵐ ▸t ⟩
       𝟘ᶜ       ∎)
  , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
     sub (▸-· {m′ = 𝟘ᵐ} ▸t) $ begin
       𝟘ᶜ      ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
       𝟘 ·ᶜ η  ∎)
  , (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
     sub (▸-cong 𝟘ᵐ?≡𝟘ᵐ ▸B) $ begin
       δ ∙ 𝟘            ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
       δ ∙ 𝟘 · q        ≈˘⟨ ≈ᶜ-refl ∙ ·-congʳ (PE.cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) ⟩
       δ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ∎)
  , ok }

------------------------------------------------------------------------
-- Usage lemmas for sndᵣ

-- A usage lemma for sndᵣ.

sndᵣₘ :
  ¬ 𝟘 ≤ 𝟙 ⊎ 𝟙 PE.≡ 𝟘 ⊎ m ≢ 𝟙ᵐ →
  Prodrec-allowed (𝟘 ∧ 𝟙) p q →
  ∀ B →
  γ ▸[ m ] t →
  δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fstᵣ p (wk1 A) (var x0) ]↑ →
  𝟘ᶜ ∧ᶜ γ ▸[ m ] sndᵣ p q A B t
sndᵣₘ {m = m} {p = p} {γ = γ} 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ ok _ ▸t ▸B = sub
  (prodrecₘ
     (▸-cong (PE.sym (𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ→ᵐ·[𝟘∧𝟙]≡ _ 𝟘≰𝟙⊎𝟙≡𝟘⊎≢𝟙ᵐ)) ▸t)
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub var $ begin
        𝟘ᶜ ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙) · p ∙ ⌜ m ⌝ · (𝟘 ∧ 𝟙)  ≈⟨ ≈ᶜ-refl ∙ ·[𝟘∧𝟙]·≡𝟘∧· ∙ ·[𝟘∧𝟙]≡𝟘∧ ⟩
        𝟘ᶜ ∙ 𝟘 ∧ ⌜ m ⌝ · p ∙ 𝟘 ∧ ⌜ m ⌝              ≤⟨ ≤ᶜ-refl ∙ ∧-decreasingˡ _ _ ∙ ∧-decreasingʳ _ _ ⟩
        𝟘ᶜ ∙ 𝟘 ∙ ⌜ m ⌝                              ∎)
     ▸B
     ok)
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ ∧ᶜ γ             ≡˘⟨ [𝟘∧𝟙]·ᶜ≡𝟘ᶜ∧ᶜ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ γ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
     (𝟘 ∧ 𝟙) ·ᶜ γ +ᶜ 𝟘ᶜ  ∎)

-- A usage lemma for sndᵣ with the mode set to 𝟘ᵐ.

sndᵣₘ-𝟘ᵐ :
  ⦃ ok : T 𝟘ᵐ-allowed ⦄ →
  Prodrec-allowed (𝟘 ∧ 𝟙) p q →
  ∀ B →
  γ ▸[ 𝟘ᵐ ] t →
  δ ∙ 𝟘 ▸[ 𝟘ᵐ ] B [ fstᵣ p (wk1 A) (var x0) ]↑ →
  γ ▸[ 𝟘ᵐ ] sndᵣ p q A B t
sndᵣₘ-𝟘ᵐ {p = p} {q = q} {γ = γ} {δ = δ} ⦃ ok = 𝟘ᵐ-ok ⦄ ok B ▸t ▸B = sub
  (sndᵣₘ
     (inj₂ (inj₂ (λ ())))
     ok
     B
     ▸t
     (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
      sub (▸-cong (PE.sym 𝟘ᵐ?≡𝟘ᵐ) ▸B) $ begin
        δ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (PE.cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) ⟩
        δ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
        δ ∙ 𝟘            ∎))
  (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     γ        ≤⟨ ∧ᶜ-greatest-lower-bound (▸-𝟘ᵐ ▸t) ≤ᶜ-refl ⟩
     𝟘ᶜ ∧ᶜ γ  ∎)

-- A usage lemma for sndᵣ with the mode set to 𝟙ᵐ and the assumption
-- that 𝟘 is the largest quantity.

sndᵣₘ-𝟙ᵐ-≤𝟘 :
  𝟙 PE.≡ 𝟘 ⊎ 𝟙 ≢ 𝟘 →
  (∀ p → p ≤ 𝟘) →
  Prodrec-allowed (𝟘 ∧ 𝟙) p q →
  ∀ B →
  γ ▸[ 𝟙ᵐ ] t →
  δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fstᵣ p (wk1 A) (var x0) ]↑ →
  γ ▸[ 𝟙ᵐ ] sndᵣ p q A B t
sndᵣₘ-𝟙ᵐ-≤𝟘 {γ = γ} 𝟙≡𝟘⊎𝟙≢𝟘 ≤𝟘 ok B ▸t ▸B = sub
  (sndᵣₘ
     (case ≤𝟘→𝟘≰𝟙⊎𝟙≡𝟘 𝟙≡𝟘⊎𝟙≢𝟘 ≤𝟘 of λ where
        (inj₁ 𝟘≰𝟙) → inj₁ 𝟘≰𝟙
        (inj₂ 𝟙≡𝟘) → inj₂ (inj₁ 𝟙≡𝟘))
     ok
     B
     ▸t
     ▸B)
  (begin
     γ        ≤⟨ ∧ᶜ-greatest-lower-bound (≤ᶜ𝟘ᶜ (≤𝟘 _)) ≤ᶜ-refl ⟩
     𝟘ᶜ ∧ᶜ γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A usage lemma for sndᵣ with the mode set to 𝟙ᵐ and the assumption
-- that _+_ is pointwise bounded by _∧_.

sndᵣₘ-𝟙ᵐ-+≤∧ :
  𝟙 PE.≡ 𝟘 ⊎ 𝟙 ≢ 𝟘 →
  (∀ p q → p + q ≤ p ∧ q) →
  Prodrec-allowed (𝟘 ∧ 𝟙) p q →
  ∀ B →
  γ ▸[ 𝟙ᵐ ] t →
  δ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] B [ fstᵣ p (wk1 A) (var x0) ]↑ →
  γ ▸[ 𝟙ᵐ ] sndᵣ p q A B t
sndᵣₘ-𝟙ᵐ-+≤∧ 𝟙≡𝟘⊎𝟙≢𝟘 +≤∧ = sndᵣₘ-𝟙ᵐ-≤𝟘 𝟙≡𝟘⊎𝟙≢𝟘 (+≤∧→≤𝟘 +≤∧)
