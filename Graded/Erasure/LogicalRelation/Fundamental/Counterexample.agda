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
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions M)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  {{eqrel : EqRelSet TR}}
  where

open Type-restrictions TR
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Derived.Erased.Untyped 𝕄 as Erased using (Erased)
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
import Graded.Erasure.LogicalRelation TR is-𝟘? as LR
import Graded.Erasure.LogicalRelation.Hidden TR is-𝟘? as LRH

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

negation-of-fundamental-lemma-with-erased-matches₁ :
  Prodrec-allowed 𝟘 p 𝟘 →
  Σᵣ-allowed p 𝟘 →
  ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
     let open LR ⊢Δ in
     Consistent Δ →
     ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
     Γ ⊢ t ∷ A → γ ▸[ m ] t →
     ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
       γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
negation-of-fundamental-lemma-with-erased-matches₁
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

opaque

  -- If []-cong-allowed holds, then one can prove a negation of a
  -- variant of the statement of the fundamental lemma without the
  -- assumption "erased matches are not allowed or the context is
  -- empty".

  negation-of-fundamental-lemma-with-erased-matches₂ :
    []-cong-allowed →
    ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
       let open LR ⊢Δ in
       Consistent Δ →
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       Γ ⊢ t ∷ A → γ ▸[ m ] t →
       ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
         γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
  negation-of-fundamental-lemma-with-erased-matches₂ ok hyp =
    ¬t®t $ hidden-®-intro-fundamental non-trivial $
    hyp ⊢Δ consistent ⊢t ▸t
    where
    Δ : Con Term 1
    Δ = ε ∙ Id ℕ zero zero

    t : Term 1
    t = []-cong ℕ zero zero (var x0)

    A : Term 1
    A = Id (Erased ℕ) Erased.[ zero ] Erased.[ zero ]

    ⊢Δ : ⊢ Δ
    ⊢Δ = ε ∙ Idⱼ (zeroⱼ ε) (zeroⱼ ε)

    consistent : Consistent Δ
    consistent = inhabited-consistent (singleSubst (rflⱼ (zeroⱼ ε)))

    ⊢t : Δ ⊢ t ∷ A
    ⊢t = []-congⱼ′ ok (var ⊢Δ here)

    ▸t : 𝟘ᶜ ▸[ 𝟙ᵐ ] t
    ▸t = []-congₘ ℕₘ zeroₘ zeroₘ var

    open LR ⊢Δ
    open LRH ⊢Δ

    ¬t®t : ¬ t ®⟨ ¹ ⟩ erase t ∷ A
    ¬t®t t®t =
      case ®-Id t®t of λ {
        (rflᵣ t⇒* _) →
      case whnfRed*Term t⇒* (ne ([]-congₙ (var _))) of λ () }

opaque

  -- If Erased-matches-for-J holds, then one can prove a negation of a
  -- variant of the statement of the fundamental lemma without the
  -- assumption "erased matches are not allowed or the context is
  -- empty".

  negation-of-fundamental-lemma-with-erased-matches₃ :
    Erased-matches-for-J →
    ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
       let open LR ⊢Δ in
       Consistent Δ →
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       Γ ⊢ t ∷ A → γ ▸[ m ] t →
       ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
         γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
  negation-of-fundamental-lemma-with-erased-matches₃ ok hyp =
    ¬t®t $ hidden-®-intro-fundamental non-trivial $
    hyp ⊢Δ consistent ⊢t ▸t
    where
    Δ : Con Term 1
    Δ = ε ∙ Id ℕ zero zero

    t : Term 1
    t = J 𝟘 𝟘 ℕ zero ℕ zero zero (var {n = 1} x0)

    A : Term 1
    A = ℕ

    ⊢Δ : ⊢ Δ
    ⊢Δ = ε ∙ Idⱼ (zeroⱼ ε) (zeroⱼ ε)

    consistent : Consistent Δ
    consistent = inhabited-consistent (singleSubst (rflⱼ (zeroⱼ ε)))

    ⊢t : Δ ⊢ t ∷ A
    ⊢t =
      Jⱼ′ (ℕⱼ (J-motive-context (zeroⱼ ⊢Δ))) (zeroⱼ ⊢Δ) (var ⊢Δ here)

    ▸t : 𝟘ᶜ ▸[ 𝟙ᵐ ] t
    ▸t =
      J₀ₘ ok ℕₘ zeroₘ
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
         sub ℕₘ $ begin
           𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘 ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                              ∎)
        zeroₘ zeroₘ var

    open LR ⊢Δ
    open LRH ⊢Δ

    ¬t®t : ¬ t ®⟨ ¹ ⟩ erase t ∷ A
    ¬t®t t®t = case ®-ℕ t®t of λ where
      (zeroᵣ t⇒* _)  → case whnfRed*Term t⇒* (ne (Jₙ (var _))) of λ ()
      (sucᵣ t⇒* _ _) → case whnfRed*Term t⇒* (ne (Jₙ (var _))) of λ ()

opaque

  -- If K-allowed and Erased-matches-for-K hold, then one can prove a
  -- negation of a variant of the statement of the fundamental lemma
  -- without the assumption "erased matches are not allowed or the
  -- context is empty".

  negation-of-fundamental-lemma-with-erased-matches₄ :
    K-allowed →
    Erased-matches-for-K →
    ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
       let open LR ⊢Δ in
       Consistent Δ →
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       Γ ⊢ t ∷ A → γ ▸[ m ] t →
       ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
         γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
  negation-of-fundamental-lemma-with-erased-matches₄ K-ok K₀-ok hyp =
    ¬t®t $ hidden-®-intro-fundamental non-trivial $
    hyp ⊢Δ consistent ⊢t ▸t
    where
    Δ : Con Term 1
    Δ = ε ∙ Id ℕ zero zero

    t : Term 1
    t = K 𝟘 ℕ zero ℕ zero (var {n = 1} x0)

    A : Term 1
    A = ℕ

    ⊢Δ : ⊢ Δ
    ⊢Δ = ε ∙ Idⱼ (zeroⱼ ε) (zeroⱼ ε)

    consistent : Consistent Δ
    consistent = inhabited-consistent (singleSubst (rflⱼ (zeroⱼ ε)))

    ⊢t : Δ ⊢ t ∷ A
    ⊢t =
      Kⱼ′ (ℕⱼ (K-motive-context (zeroⱼ ⊢Δ))) (zeroⱼ ⊢Δ) (var ⊢Δ here)
        K-ok

    ▸t : 𝟘ᶜ ▸[ 𝟙ᵐ ] t
    ▸t =
      K₀ₘ K₀-ok ℕₘ zeroₘ
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
         sub ℕₘ $ begin
           𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
           𝟘ᶜ                ∎)
        zeroₘ var

    open LR ⊢Δ
    open LRH ⊢Δ

    ¬t®t : ¬ t ®⟨ ¹ ⟩ erase t ∷ A
    ¬t®t t®t = case ®-ℕ t®t of λ where
      (zeroᵣ t⇒* _)  → case whnfRed*Term t⇒* (ne (Kₙ (var _))) of λ ()
      (sucᵣ t⇒* _ _) → case whnfRed*Term t⇒* (ne (Kₙ (var _))) of λ ()
