------------------------------------------------------------------------
-- The fundamental lemma does not hold in general without the
-- assumption that erased matches are disallowed or the context is
-- empty
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Graded.Erasure.LogicalRelation.Fundamental.Counterexample
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  {{eqrel : EqRelSet TR}}
  where

open Type-restrictions TR
open Usage-restrictions UR

open import Graded.Context 𝕄
import Graded.Derived.Erased.Untyped 𝕄 as Erased
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches
open import Graded.Mode 𝕄

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Substitution TR
open import Definition.Typed.Properties TR
open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Substitution TR

open import Graded.Erasure.Consequences.Soundness TR UR
open import Graded.Erasure.Extraction 𝕄 is-𝟘?
open import Graded.Erasure.LogicalRelation.Assumptions TR
import Graded.Erasure.LogicalRelation
import Graded.Erasure.LogicalRelation.Hidden
open import Graded.Erasure.Target using (Strictness)

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality using (_≡_; _≢_)
open import Tools.Relation
open import Tools.Sum

private variable
  k   : Nat
  p q : M
  s   : Strength
  sem : Some-erased-matches
  str : Strictness

-- The module LR exports some module instantiations.

private module LR {Δ : Con Term k} (⊢Δ : ⊢ Δ) (str : Strictness) where

  private

    as : Assumptions
    as = record { ⊢Δ = ⊢Δ; str = str }

  open Graded.Erasure.LogicalRelation is-𝟘? as public
  open Graded.Erasure.LogicalRelation.Hidden is-𝟘? as public

-- If Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 holds for some p (which means that
-- certain kinds of erased matches are allowed), and if additionally
-- Σʷ-allowed p 𝟘 holds, then one can prove a negation of a variant of
-- the fundamental lemma without the assumption "erased matches are
-- not allowed or the context is empty" (for any strictness).

negation-of-fundamental-lemma-with-erased-matches₁ :
  Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 →
  Σʷ-allowed p 𝟘 →
  ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
     let open LR ⊢Δ str in
     Consistent Δ →
     ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
     Γ ⊢ t ∷ A → γ ▸[ m ] t →
     ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
       γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
negation-of-fundamental-lemma-with-erased-matches₁
  {p} {str} P-ok Σʷ-ok hyp =
  case soundness-ℕ-only-source-counterexample₁ P-ok Σʷ-ok of λ
    (consistent , ⊢t , ▸t , _) →
  ¬t®t $ hidden-®-intro-fundamental non-trivial $
  hyp ⊢Δ consistent ⊢t ▸t
  where
  Δ : Con Term 1
  Δ = ε ∙ (Σʷ p , 𝟘 ▷ ℕ ▹ ℕ)

  t : Term 1
  t = prodrec 𝟘 p 𝟘 ℕ (var x0) zero

  A : Term 1
  A = ℕ

  ⊢Δ : ⊢ Δ
  ⊢Δ = ε ∙ ΠΣⱼ (ℕⱼ ε) (ℕⱼ (ε ∙ ℕⱼ ε)) Σʷ-ok

  open LR ⊢Δ str

  ¬t®t : ¬ t ®⟨ ¹ ⟩ erase str t ∷ A
  ¬t®t t®t = case ®-ℕ t®t of λ where
    (zeroᵣ t⇒* _) →
      case whnfRed*Term t⇒* (ne (prodrecₙ (var _))) of λ ()
    (sucᵣ t⇒* _ _ _) →
      case whnfRed*Term t⇒* (ne (prodrecₙ (var _))) of λ ()

opaque

  -- If []-cong-allowed holds, then one can prove a negation of a
  -- variant of the statement of the fundamental lemma without the
  -- assumption "erased matches are not allowed or the context is
  -- empty" (for any strictness).

  negation-of-fundamental-lemma-with-erased-matches₂ :
    []-cong-allowed s →
    ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
       let open LR ⊢Δ str in
       Consistent Δ →
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       Γ ⊢ t ∷ A → γ ▸[ m ] t →
       ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
         γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
  negation-of-fundamental-lemma-with-erased-matches₂ {s} {str} ok hyp =
    ¬t®t $ hidden-®-intro-fundamental non-trivial $
    hyp ⊢Δ consistent ⊢t ▸t
    where
    open Erased s
    Δ : Con Term 1
    Δ = ε ∙ Id ℕ zero zero

    t : Term 1
    t = []-cong s ℕ zero zero (var x0)

    A : Term 1
    A = Id (Erased ℕ) ([ zero ]) ([ zero ])

    ⊢Δ : ⊢ Δ
    ⊢Δ = ε ∙ Idⱼ (zeroⱼ ε) (zeroⱼ ε)

    consistent : Consistent Δ
    consistent = inhabited-consistent (singleSubst (rflⱼ (zeroⱼ ε)))

    ⊢t : Δ ⊢ t ∷ A
    ⊢t = []-congⱼ′ ok (var ⊢Δ here)

    ▸t : 𝟘ᶜ ▸[ 𝟙ᵐ ] t
    ▸t = []-congₘ ℕₘ zeroₘ zeroₘ var

    open LR ⊢Δ str

    ¬t®t : ¬ t ®⟨ ¹ ⟩ erase str t ∷ A
    ¬t®t t®t =
      case ®-Id t®t of λ {
        (rflᵣ t⇒* _) →
      case whnfRed*Term t⇒* (ne ([]-congₙ (var _))) of λ () }

opaque

  -- If erased-matches-for-J 𝟙ᵐ is equal to not-none sem, then one can
  -- prove a negation of a variant of the statement of the fundamental
  -- lemma without the assumption "erased matches are not allowed or
  -- the context is empty" (for any strictness).

  negation-of-fundamental-lemma-with-erased-matches₃ :
    erased-matches-for-J 𝟙ᵐ ≡ not-none sem →
    ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
       let open LR ⊢Δ str in
       Consistent Δ →
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       Γ ⊢ t ∷ A → γ ▸[ m ] t →
       ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
         γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
  negation-of-fundamental-lemma-with-erased-matches₃
    {str} ≡not-none hyp =
    case soundness-ℕ-only-source-counterexample₃ ≡not-none of λ
      (consistent , ⊢t , ▸t , _) →
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

    open LR ⊢Δ str

    ¬t®t : ¬ t ®⟨ ¹ ⟩ erase str t ∷ A
    ¬t®t t®t = case ®-ℕ t®t of λ where
      (zeroᵣ t⇒* _)    → case whnfRed*Term t⇒* (ne (Jₙ (var _))) of λ ()
      (sucᵣ t⇒* _ _ _) → case whnfRed*Term t⇒* (ne (Jₙ (var _))) of λ ()

opaque

  -- If the K rule is allowed and erased-matches-for-K 𝟙ᵐ is equal to
  -- not-none sem, then one can prove a negation of a variant of the
  -- statement of the fundamental lemma without the assumption "erased
  -- matches are not allowed or the context is empty" (for any
  -- strictness).

  negation-of-fundamental-lemma-with-erased-matches₄ :
    K-allowed →
    erased-matches-for-K 𝟙ᵐ ≡ not-none sem →
    ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
       let open LR ⊢Δ str in
       Consistent Δ →
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       Γ ⊢ t ∷ A → γ ▸[ m ] t →
       ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
         γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
  negation-of-fundamental-lemma-with-erased-matches₄
    {str} K-ok ≡not-none hyp =
    case soundness-ℕ-only-source-counterexample₄ K-ok ≡not-none of λ
      (consistent , ⊢t , ▸t , _) →
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

    open LR ⊢Δ str

    ¬t®t : ¬ t ®⟨ ¹ ⟩ erase str t ∷ A
    ¬t®t t®t = case ®-ℕ t®t of λ where
      (zeroᵣ t⇒* _)    → case whnfRed*Term t⇒* (ne (Kₙ (var _))) of λ ()
      (sucᵣ t⇒* _ _ _) → case whnfRed*Term t⇒* (ne (Kₙ (var _))) of λ ()

opaque

  -- If Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 holds (which means that certain kinds
  -- of erased matches are allowed), and if additionally Unitʷ-allowed
  -- holds, then one can prove a negation of a variant of the
  -- fundamental lemma without the assumption "erased matches are not
  -- allowed or the context is empty" (for any strictness).

  negation-of-fundamental-lemma-with-erased-matches₅ :
    Unitʷ-allowed →
    Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 →
    ¬ (∀ {k} {Δ : Con Term k} (⊢Δ : ⊢ Δ) →
       let open LR ⊢Δ str in
       Consistent Δ →
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       Γ ⊢ t ∷ A → γ ▸[ m ] t →
       ∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
         γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ m ] A / [Γ] / [A])
  negation-of-fundamental-lemma-with-erased-matches₅
    {str} Unit-ok ok hyp =
    case soundness-ℕ-only-source-counterexample₅ ok Unit-ok of λ
      (consistent , ⊢t , ▸t , _) →
    ¬t®t $ hidden-®-intro-fundamental non-trivial $
    hyp ⊢Δ consistent ⊢t ▸t
    where
    Δ : Con Term 1
    Δ = ε ∙ Unitʷ

    t : Term 1
    t = unitrec 𝟘 𝟘 ℕ (var x0) zero

    A : Term 1
    A = ℕ

    ⊢Δ : ⊢ Δ
    ⊢Δ = ε ∙ Unitⱼ ε Unit-ok

    open LR ⊢Δ str

    ¬t®t : ¬ t ®⟨ ¹ ⟩ erase str t ∷ A
    ¬t®t t®t = case ®-ℕ t®t of λ where
      (zeroᵣ t⇒* _)    → case whnfRed*Term t⇒* (ne (unitrecₙ (var _))) of λ ()
      (sucᵣ t⇒* _ _ _) → case whnfRed*Term t⇒* (ne (unitrecₙ (var _))) of λ ()
