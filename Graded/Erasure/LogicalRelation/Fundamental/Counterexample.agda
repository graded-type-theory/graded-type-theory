------------------------------------------------------------------------
-- The fundamental lemma does not hold in general without the
-- assumption that erased matches are disallowed or the context is
-- empty
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Graded.Erasure.LogicalRelation.Fundamental.Counterexample
  {a} {M : Set a}
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (TR : Type-restrictions M)
  (UR : Usage-restrictions M)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  {{eqrel : EqRelSet TR}}
  where

open Type-restrictions TR
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Mode 𝕄

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Properties TR
open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Substitution TR

open import Graded.Erasure.Extraction 𝕄 is-𝟘?
import Graded.Erasure.LogicalRelation 𝕄 TR is-𝟘? as LR
import Graded.Erasure.LogicalRelation.Hidden 𝕄 TR is-𝟘? as LRH

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
open import Tools.Relation

private variable
  p : M

-- If Prodrec-allowed 𝟘 p 𝟘 holds for some p (which means that certain
-- kinds of erased matches are allowed), and if additionally
-- Σᵣ-allowed p 𝟘 holds, then one cannot prove a variant of the
-- fundamental lemma without the assumption "erased matches are not
-- allowed or the context is empty" (assuming that Agda is
-- consistent).

negation-of-fundamental-lemma-with-erased-matches :
  Prodrec-allowed 𝟘 p 𝟘 →
  Σᵣ-allowed p 𝟘 →
  ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
     let open LR ⊢Δ in
     Consistent Δ →
     ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
     Γ ⊢ t ∷ A → γ ▸[ m ] t →
     ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
       γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
negation-of-fundamental-lemma-with-erased-matches
  {p = p} P-ok Σᵣ-ok hyp =
  ¬t®t $ hidden-®-intro-fundamental non-trivial $
  hyp ⊢Δ consistent ⊢t ▸t
  where
  Δ : Con Term 1
  Δ = ε ∙ (Σᵣ p , 𝟘 ▷ ℕ ▹ ℕ)

  t : Term 1
  t = prodrec 𝟘 p 𝟘 ℕ (var x0) zero

  A : Term 1
  A = ℕ

  ⊢Δ : ⊢ Δ
  ⊢Δ = ε ∙ ΠΣⱼ (ℕⱼ ε) (ℕⱼ (ε ∙ ℕⱼ ε)) Σᵣ-ok

  consistent : Consistent Δ
  consistent =
    inhabited-consistent $ singleSubst $
    prodⱼ (ℕⱼ ε) (ℕⱼ (ε ∙ ℕⱼ ε)) (zeroⱼ ε) (zeroⱼ ε) Σᵣ-ok

  ⊢t : Δ ⊢ t ∷ A
  ⊢t = prodrecⱼ′
    (ℕⱼ (⊢Δ ∙ ΠΣⱼ (ℕⱼ ⊢Δ) (ℕⱼ (⊢Δ ∙ ℕⱼ ⊢Δ)) Σᵣ-ok))
    (var ⊢Δ here)
    (zeroⱼ (⊢Δ ∙ ℕⱼ ⊢Δ ∙ ℕⱼ (⊢Δ ∙ ℕⱼ ⊢Δ)))

  ▸t : 𝟘ᶜ ▸[ 𝟙ᵐ ] t
  ▸t = sub
    (prodrecₘ var
       (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
        sub zeroₘ $ begin
          𝟘ᶜ ∙ 𝟙 · 𝟘 · p ∙ 𝟙 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ PE.trans (·-congˡ (·-zeroˡ _)) (·-zeroʳ _) ∙ ·-zeroʳ _ ⟩
          𝟘ᶜ                      ∎)
       (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
        sub ℕₘ $ begin
          𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
          𝟘ᶜ                ∎)
       P-ok)
    (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
     𝟘ᶜ                           ≈˘⟨ +ᶜ-identityˡ _ ⟩
     𝟘ᶜ +ᶜ 𝟘ᶜ                     ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
     𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ 𝟘 ⌟ ⌝) +ᶜ 𝟘ᶜ  ∎)

  open LR ⊢Δ
  open LRH ⊢Δ

  ¬t®t : ¬ t ®⟨ ¹ ⟩ erase t ∷ A
  ¬t®t t®t = case ®-ℕ t®t of λ where
    (zeroᵣ t⇒* _) →
      case whnfRed*Term t⇒* (ne (prodrecₙ (var _))) of λ ()
    (sucᵣ t⇒* _ _) →
      case whnfRed*Term t⇒* (ne (prodrecₙ (var _))) of λ ()
