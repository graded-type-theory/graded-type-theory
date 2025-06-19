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
  (UR : Usage-restrictions 𝕄)
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  {{eqrel : EqRelSet TR}}
  where

open EqRelSet eqrel
open Type-restrictions TR
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches
open import Graded.Mode 𝕄
open import Graded.Restrictions 𝕄

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed TR
open import Definition.Typed.Consequences.Admissible TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Substitution TR
open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Substitution TR

open import Graded.Erasure.Consequences.Soundness TR UR
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation.Assumptions TR
import Graded.Erasure.LogicalRelation
open import Graded.Erasure.LogicalRelation.Fundamental TR UR
import Graded.Erasure.LogicalRelation.Hidden
open import Graded.Erasure.Target using (Strictness)

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality using (_≡_; _≢_)
open import Tools.Relation
open import Tools.Sum

private variable
  k kᵈ : Nat
  p q  : M
  s    : Strength
  sem  : Some-erased-matches
  str  : Strictness

private

  -- The module LR exports some module instantiations.

  module LR
    {∇ : DCon (Term 0) kᵈ}
    {Δ : Con Term k}
    (⊢Δ : glassify ∇ »⊢ Δ)
    ⦃ inc : Var-included or-empty Δ ⦄
    (str : Strictness)
    where

    private

      as : Assumptions
      as = assumptions ⊢Δ str

    open Graded.Erasure.LogicalRelation as public
    open Graded.Erasure.LogicalRelation.Hidden as public

  -- A variant of LR.

  module LR′
    {∇ : DCon (Term 0) kᵈ}
    {Δ : Con Term k}
    (⊢Δ : ∇ »⊢ Δ)
    ⦃ inc : Var-included or-empty Δ ⦄
    (str : Strictness)
    where

    private

      as : Assumptions
      as = record
        { ts  = ∇
        ; vs  = eraseDCon str ∇
        ; ⊢Δ  = ⊢Δ
        ; str = str
        }

    open Graded.Erasure.LogicalRelation as public
    open Graded.Erasure.LogicalRelation.Hidden as public

-- Below negations of variants of the statement of the fundamental
-- lemma are proved. In each case the variants are given for the
-- module parameters (𝕄, TR, UR, etc.), and for an arbitrary
-- Strictness. Furthermore the assumption "erased matches are not
-- allowed unless the context is empty" is removed. In most cases the
-- assumption "if erased matches are allowed for emptyrec when the
-- mode is 𝟙ᵐ, then the context is consistent" is replaced by "the
-- context is consistent", but in one case this assumption is instead
-- removed.

-- If Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 holds for some p (which means that
-- certain kinds of erased matches are allowed), and if additionally
-- Σʷ-allowed p 𝟘 and Var-included hold, then one can prove a negation
-- of a variant of the statement of the fundamental lemma.

negation-of-fundamental-lemma-with-erased-matches₁ :
  ⦃ inc : Var-included ⦄ →
  Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 →
  Σʷ-allowed p 𝟘 →
  ¬ (∀ {o k} {Δ : Con Term k} {∇ : DCon (Term 0) o}
     (⊢Δ : glassify ∇ »⊢ Δ) →
     ▸[ 𝟙ᵐ ] (glassify ∇) →
     Consistent (glassify ∇ » Δ) →
     ⦃ inc : Var-included or-empty Δ ⦄ →
     let open LR ⊢Δ str in
     ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
     glassify ∇ » Γ ⊢ t ∷ A → γ ▸[ m ] t →
     γ ▸ Γ ⊩ʳ t ∷[ m ] A)
negation-of-fundamental-lemma-with-erased-matches₁
  {p} {str} P-ok Σʷ-ok hyp =
  case soundness-ℕ-only-source-counterexample₁ P-ok Σʷ-ok of λ
    (consistent , ⊢t , ▸∇ , ▸t , _) →
  ¬t®t $ ▸⊩ʳ∷[𝟙ᵐ]→®∷ $ hyp ⊢Δ ▸∇ consistent ⦃ inc = included ⦄ ⊢t ▸t
  where
  Δ : Cons 0 1
  Δ = ε » ε ∙ (Σʷ p , 𝟘 ▷ ℕ ▹ ℕ)

  t : Term 1
  t = prodrec 𝟘 p 𝟘 ℕ (var x0) zero

  A : Term 1
  A = ℕ

  ⊢Δ : ⊢ Δ
  ⊢Δ = ∙ ΠΣⱼ (ℕⱼ (∙ ℕⱼ εε)) Σʷ-ok

  open LR ⊢Δ ⦃ inc = included ⦄ str

  ¬t®t : ¬ t ® erase str t ∷ A
  ¬t®t t®t = case ®∷ℕ⇔ .proj₁ t®t of λ where
    (zeroᵣ t⇒* _) →
      case whnfRed*Term t⇒* (ne (prodrecₙ (var _ _))) of λ ()
    (sucᵣ t⇒* _ _ _) →
      case whnfRed*Term t⇒* (ne (prodrecₙ (var _ _))) of λ ()

opaque

  -- If []-cong-allowed, []-cong-allowed-mode and Var-included hold,
  -- then one can prove a negation of a variant of the statement of
  -- the fundamental lemma.

  negation-of-fundamental-lemma-with-erased-matches₂ :
    ⦃ inc : Var-included ⦄ →
    []-cong-allowed s →
    []-cong-allowed-mode s 𝟙ᵐ →
    ¬ (∀ {o k} {Δ : Con Term k} {∇ : DCon (Term 0) o}
       (⊢Δ : glassify ∇ »⊢ Δ) →
       ▸[ 𝟙ᵐ ] (glassify ∇) →
       Consistent (glassify ∇ » Δ) →
       ⦃ inc : Var-included or-empty Δ ⦄ →
       let open LR ⊢Δ str in
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       glassify ∇ » Γ ⊢ t ∷ A → γ ▸[ m ] t →
       γ ▸ Γ ⊩ʳ t ∷[ m ] A)
  negation-of-fundamental-lemma-with-erased-matches₂
    {s} {str} ok ok′ hyp =
    ¬t®t $ ▸⊩ʳ∷[𝟙ᵐ]→®∷ $
    hyp ⊢Δ (λ ()) consistent ⦃ inc = included ⦄ ⊢t ▸t
    where
    open Erased s
    Δ : Cons 0 1
    Δ = ε » ε ∙ Id ℕ zero zero

    t : Term 1
    t = []-cong s ℕ zero zero (var x0)

    A : Term 1
    A = Id (Erased ℕ) ([ zero ]) ([ zero ])

    ⊢Δ : ⊢ Δ
    ⊢Δ = ∙ Idⱼ′ (zeroⱼ εε) (zeroⱼ εε)

    consistent : Consistent Δ
    consistent = inhabited-consistent (⊢ˢʷ∷-sgSubst (rflⱼ (zeroⱼ εε)))

    ⊢t : Δ ⊢ t ∷ A
    ⊢t = []-congⱼ′ ok (var ⊢Δ here)

    ▸t : 𝟘ᶜ ▸[ 𝟙ᵐ ] t
    ▸t = []-congₘ ℕₘ zeroₘ zeroₘ var ok′

    open LR ⊢Δ ⦃ inc = included ⦄ str

    ¬t®t : ¬ t ® erase str t ∷ A
    ¬t®t t®t =
      case ®∷Id⇔ .proj₁ t®t of λ {
        (_ , rflᵣ t⇒* _) →
      case whnfRed*Term t⇒* (ne ([]-congₙ (var _ _))) of λ () }

opaque

  -- If erased-matches-for-J 𝟙ᵐ is equal to not-none sem and
  -- Var-included holds, then one can prove a negation of a variant of
  -- the statement of the fundamental lemma.

  negation-of-fundamental-lemma-with-erased-matches₃ :
    ⦃ inc : Var-included ⦄ →
    erased-matches-for-J 𝟙ᵐ ≡ not-none sem →
    ¬ (∀ {o k} {Δ : Con Term k} {∇ : DCon (Term 0) o}
       (⊢Δ : glassify ∇ »⊢ Δ) →
       ▸[ 𝟙ᵐ ] (glassify ∇) →
       Consistent (glassify ∇ » Δ) →
       ⦃ inc : Var-included or-empty Δ ⦄ →
       let open LR ⊢Δ str in
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       glassify ∇ » Γ ⊢ t ∷ A → γ ▸[ m ] t →
       γ ▸ Γ ⊩ʳ t ∷[ m ] A)
  negation-of-fundamental-lemma-with-erased-matches₃
    {str} ≡not-none hyp =
    case soundness-ℕ-only-source-counterexample₃ ≡not-none of λ
      (consistent , ⊢t , ▸∇ , ▸t , _) →
    ¬t®t $ ▸⊩ʳ∷[𝟙ᵐ]→®∷ $ hyp ⊢Δ ▸∇ consistent ⦃ inc = included ⦄ ⊢t ▸t
    where
    Δ : Cons 0 1
    Δ = ε » ε ∙ Id ℕ zero zero

    t : Term 1
    t = J 𝟘 𝟘 ℕ zero ℕ zero zero (var {n = 1} x0)

    A : Term 1
    A = ℕ

    ⊢Δ : ⊢ Δ
    ⊢Δ = ∙ Idⱼ′ (zeroⱼ εε) (zeroⱼ εε)

    open LR ⊢Δ ⦃ inc = included ⦄ str

    ¬t®t : ¬ t ® erase str t ∷ A
    ¬t®t t®t = case ®∷ℕ⇔ .proj₁ t®t of λ where
      (zeroᵣ t⇒* _) →
        case whnfRed*Term t⇒* (ne (Jₙ (var _ _))) of λ ()
      (sucᵣ t⇒* _ _ _) →
        case whnfRed*Term t⇒* (ne (Jₙ (var _ _))) of λ ()

opaque

  -- If the K rule is allowed, erased-matches-for-K 𝟙ᵐ is equal to
  -- not-none sem, and Var-included holds, then one can prove a
  -- negation of a variant of the statement of the fundamental lemma.

  negation-of-fundamental-lemma-with-erased-matches₄ :
    ⦃ inc : Var-included ⦄ →
    K-allowed →
    erased-matches-for-K 𝟙ᵐ ≡ not-none sem →
    ¬ (∀ {o k} {Δ : Con Term k} {∇ : DCon (Term 0) o}
       (⊢Δ : glassify ∇ »⊢ Δ) →
       ▸[ 𝟙ᵐ ] (glassify ∇) →
       Consistent (glassify ∇ » Δ) →
       ⦃ inc : Var-included or-empty Δ ⦄ →
       let open LR ⊢Δ str in
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       glassify ∇ » Γ ⊢ t ∷ A → γ ▸[ m ] t →
       γ ▸ Γ ⊩ʳ t ∷[ m ] A)
  negation-of-fundamental-lemma-with-erased-matches₄
    {str} K-ok ≡not-none hyp =
    case soundness-ℕ-only-source-counterexample₄ K-ok ≡not-none of λ
      (consistent , ⊢t , ▸∇ , ▸t , _) →
    ¬t®t $ ▸⊩ʳ∷[𝟙ᵐ]→®∷ $ hyp ⊢Δ ▸∇ consistent ⦃ inc = included ⦄ ⊢t ▸t
    where
    Δ : Cons 0 1
    Δ = ε » ε ∙ Id ℕ zero zero

    t : Term 1
    t = K 𝟘 ℕ zero ℕ zero (var {n = 1} x0)

    A : Term 1
    A = ℕ

    ⊢Δ : ⊢ Δ
    ⊢Δ = ∙ Idⱼ′ (zeroⱼ εε) (zeroⱼ εε)

    open LR ⊢Δ ⦃ inc = included ⦄ str

    ¬t®t : ¬ t ® erase str t ∷ A
    ¬t®t t®t = case ®∷ℕ⇔ .proj₁ t®t of λ where
      (zeroᵣ t⇒* _)    → case whnfRed*Term t⇒* (ne (Kₙ (var _ _))) of λ ()
      (sucᵣ t⇒* _ _ _) → case whnfRed*Term t⇒* (ne (Kₙ (var _ _))) of λ ()

opaque

  -- If Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 holds and η-equality is not allowed for
  -- weak unit types (which means that certain kinds of erased matches
  -- are allowed), and if additionally Unitʷ-allowed and Var-included
  -- hold, then one can prove a negation of a variant of the statement
  -- of the fundamental lemma.

  negation-of-fundamental-lemma-with-erased-matches₅ :
    ⦃ inc : Var-included ⦄ →
    Unitʷ-allowed →
    Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 →
    ¬ Unitʷ-η →
    ¬ (∀ {o k} {Δ : Con Term k} {∇ : DCon (Term 0) o}
       (⊢Δ : glassify ∇ »⊢ Δ) →
       ▸[ 𝟙ᵐ ] (glassify ∇) →
       Consistent (glassify ∇ » Δ) →
       ⦃ inc : Var-included or-empty Δ ⦄ →
       let open LR ⊢Δ str in
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       glassify ∇ » Γ ⊢ t ∷ A → γ ▸[ m ] t →
       γ ▸ Γ ⊩ʳ t ∷[ m ] A)
  negation-of-fundamental-lemma-with-erased-matches₅
    {str} Unit-ok ok no-η hyp =
    case soundness-ℕ-only-source-counterexample₅ ok Unit-ok no-η of λ
      (consistent , ⊢t , ▸∇ , ▸t , _) →
    ¬t®t $ ▸⊩ʳ∷[𝟙ᵐ]→®∷ $ hyp ⊢Δ ▸∇ consistent ⦃ inc = included ⦄ ⊢t ▸t
    where
    Δ : Cons 0 1
    Δ = ε » ε ∙ Unitʷ 0

    t : Term 1
    t = unitrec 0 𝟘 𝟘 ℕ (var x0) zero

    A : Term 1
    A = ℕ

    ⊢Δ : ⊢ Δ
    ⊢Δ = ∙ Unitⱼ εε Unit-ok

    open LR ⊢Δ ⦃ inc = included ⦄ str

    ¬t®t : ¬ t ® erase str t ∷ A
    ¬t®t t®t = case ®∷ℕ⇔ .proj₁ t®t of λ where
      (zeroᵣ t⇒* _)    →
        case whnfRed*Term t⇒* (ne (unitrecₙ no-η (var _ _))) of λ ()
      (sucᵣ t⇒* _ _ _) →
        case whnfRed*Term t⇒* (ne (unitrecₙ no-η (var _ _))) of λ ()

opaque

  -- If Emptyrec-allowed 𝟙ᵐ 𝟘 and Var-included hold, then one can
  -- prove a negation of a variant of the statement of the fundamental
  -- lemma.

  negation-of-fundamental-lemma-without-consistency₆ :
    ⦃ inc : Var-included ⦄ →
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    ¬ (∀ {o k} {Δ : Con Term k} {∇ : DCon (Term 0) o}
       (⊢Δ : glassify ∇ »⊢ Δ) →
       ▸[ 𝟙ᵐ ] (glassify ∇) →
       ⦃ inc : Var-included or-empty Δ ⦄ →
       let open LR ⊢Δ str in
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       glassify ∇ » Γ ⊢ t ∷ A → γ ▸[ m ] t →
       γ ▸ Γ ⊩ʳ t ∷[ m ] A)
  negation-of-fundamental-lemma-without-consistency₆ {str} ok hyp =
    case soundness-ℕ-counterexample₆ {str = str} ok of λ
      (⊢t , ▸∇ , ▸t , _) →
    ¬t®t $ ▸⊩ʳ∷[𝟙ᵐ]→®∷ $ hyp ⊢Δ ▸∇ ⦃ inc = included ⦄ ⊢t ▸t
    where
    Δ : Cons 0 1
    Δ = ε » ε ∙ Empty

    t : Term 1
    t = emptyrec 𝟘 ℕ (var x0)

    A : Term 1
    A = ℕ

    ⊢Δ : ⊢ Δ
    ⊢Δ = ∙ Emptyⱼ εε

    open LR ⊢Δ ⦃ inc = included ⦄ str

    ¬t®t : ¬ t ® erase str t ∷ A
    ¬t®t t®t = case ®∷ℕ⇔ .proj₁ t®t of λ where
      (zeroᵣ t⇒* _)    → case whnfRed*Term t⇒* (ne (emptyrecₙ (var _ _))) of λ ()
      (sucᵣ t⇒* _ _ _) → case whnfRed*Term t⇒* (ne (emptyrecₙ (var _ _))) of λ ()

opaque

  -- If Opacity-allowed holds, then one can prove a negation of a
  -- variant of the statement of the fundamental lemma.

  negation-of-fundamental-lemma-with-erased-matches₇ :
    Opacity-allowed →
    ¬ (∀ {o k} {Δ : Con Term k} {∇ : DCon (Term 0) o}
       (⊢Δ : ∇ »⊢ Δ) →
       ▸[ 𝟙ᵐ ] ∇ →
       Consistent (∇ » Δ) →
       No-erased-matches TR UR ⊎ Empty-con Δ →
       ⦃ inc : Var-included or-empty Δ ⦄ →
       let open LR′ ⊢Δ str in
       ∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} {m} →
       ∇ » Γ ⊢ t ∷ A → γ ▸[ m ] t →
       γ ▸ Γ ⊩ʳ t ∷[ m ] A)
  negation-of-fundamental-lemma-with-erased-matches₇ {str} ok hyp =
    case soundness-ℕ-only-source-counterexample₇ ok of λ
      (consistent , empty , ⊢t , ▸∇ , ▸t , _) →
    ¬t®t $ ▸⊩ʳ∷[𝟙ᵐ]→®∷ $
    hyp ⊢Δ ▸∇ consistent (inj₂ empty) ⦃ inc = ε ⦄ ⊢t ▸t
    where
    Δ : Cons 1 0
    Δ = Opaque[ zero ∷ ℕ ] » ε

    t : Term 0
    t = defn 0

    A : Term 0
    A = ℕ

    ⊢Δ : ⊢ Δ
    ⊢Δ = ε ∙ᵒ⟨ ok , ε ⟩[ zeroⱼ εε ∷ ℕⱼ εε ]

    open LR′ ⊢Δ ⦃ inc = ε ⦄ str

    ¬t®t : ¬ t ® erase str t ∷ A
    ¬t®t t®t = case ®∷ℕ⇔ .proj₁ t®t of λ where
      (zeroᵣ t⇒* _)    →
        case whnfRed*Term t⇒* (ne (defn here)) of λ ()
      (sucᵣ t⇒* _ _ _) →
        case whnfRed*Term t⇒* (ne (defn here)) of λ ()
