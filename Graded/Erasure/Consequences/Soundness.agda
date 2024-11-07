------------------------------------------------------------------------
-- Soundness of the extraction function.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Erasure.Consequences.Soundness
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Type-restrictions TR
open Usage-restrictions UR

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Sigma 𝕄
open import Definition.Untyped.Unit 𝕄

open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Substitution TR
import Definition.Typed.Consequences.Canonicity TR as TC
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.LogicalRelation TR

open import Graded.Context 𝕄
open import Graded.Derived.Erased.Typed TR
import Graded.Derived.Erased.Untyped 𝕄 as Erased
open import Graded.Derived.Erased.Usage 𝕄 UR
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

open import Graded.Erasure.Target as T
  using (Strictness; strict; non-strict)
import Graded.Erasure.Target.Properties as TP
open import Graded.Erasure.Target.Reasoning
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Non-terminating TR UR
open import Graded.Erasure.SucRed TR
import Graded.Erasure.LogicalRelation
open import Graded.Erasure.LogicalRelation.Assumptions TR
open import Graded.Erasure.LogicalRelation.Fundamental.Assumptions TR UR
import Graded.Erasure.LogicalRelation.Fundamental
import Graded.Erasure.LogicalRelation.Hidden
import Graded.Erasure.LogicalRelation.Irrelevance

open import Tools.Bool using (T; true)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)
open import Tools.Sum

private
  variable
    n : Nat
    Γ Δ : Con Term _
    t t′ u F : Term n
    G : Term (1+ n)
    v v′ w : T.Term n
    p q : M
    s : Strength
    l : Universe-level
    sem : Some-erased-matches
    str : Strictness

-- WH reduction soundness of natural numbers

-- Some results that are proved under the assumption that the
-- modality's zero is well-behaved.

module _
  ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄
  where

  -- The following results make use of some assumptions.

  module Soundness′
    (FA : Fundamental-assumptions Δ)
    {str : Strictness}
    {{eqrel : EqRelSet TR}}
    where

    open Fundamental-assumptions FA

    private

      as : Assumptions
      as = record { ⊢Δ = well-formed; str = str }

    open Graded.Erasure.LogicalRelation as
    open Graded.Erasure.LogicalRelation.Fundamental.Fundamental TR UR FA
    open Graded.Erasure.LogicalRelation.Hidden as
    open Graded.Erasure.LogicalRelation.Irrelevance as

    -- WH reduction soundness of zero
    -- If t ⇒* zero and 𝟘ᶜ ▸ t then erase t ⇒* zero

    soundness-zero :
      Δ ⊢ t ⇒* zero ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t → erase str t T.⇒* T.zero
    soundness-zero {t} t⇒*zero ▸t =
                               $⟨ fundamentalErased-𝟙ᵐ (redFirst*Term t⇒*zero) ▸t ⟩
      t ® erase str t ∷ ℕ      ⇔⟨ ®∷ℕ⇔ ⟩→
      t ® erase str t ∷ℕ       →⟨ (λ { (zeroᵣ _ ⇒*zero)    → ⇒*zero
                                     ; (sucᵣ t⇒*suc _ _ _) →
                                         case whrDet*Term (t⇒*zero , zeroₙ) (t⇒*suc , sucₙ) of λ ()
                                     }) ⟩
      erase str t T.⇒* T.zero  □

    -- WH reduction soundness of suc
    -- If t ⇒* suc t′ and 𝟘ᶜ ▸ t then erase t ⇒* suc v′ and t′ ® v′ ∷ℕ
    -- for some v′

    soundness-suc : Δ ⊢ t ⇒* suc t′ ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t
                  → ∃ λ v′ → erase str t T.⇒* T.suc v′ × t′ ® v′ ∷ℕ
    soundness-suc {t} {t′} t⇒*suc ▸t =                   $⟨ fundamentalErased-𝟙ᵐ (redFirst*Term t⇒*suc) ▸t ⟩
      t ® erase str t ∷ ℕ                                ⇔⟨ ®∷ℕ⇔ ⟩→
      t ® erase str t ∷ℕ                                 →⟨ (λ { (zeroᵣ t⇒*zero _) →
                                                                   case whrDet*Term (t⇒*zero , zeroₙ) (t⇒*suc , sucₙ) of λ ()
                                                               ; (sucᵣ t⇒*suc′ ⇒*suc _ t′®v′) →
                                                                   case whrDet*Term (t⇒*suc , sucₙ) (t⇒*suc′ , sucₙ) of λ {
                                                                     PE.refl →
                                                                   _ , ⇒*suc , t′®v′ }
                                                               }) ⟩
      (∃ λ v′ → erase str t T.⇒* T.suc v′ × t′ ® v′ ∷ℕ)  □

    -- Helper lemma for soundness of natural numbers

    soundness-ℕ′ :
      t ® v ∷ℕ → ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × v ⇒ˢ⟨ str ⟩* T.sucᵏ n
    soundness-ℕ′ (zeroᵣ ⇒*zero ⇒*zero′) =
      0 , whred* ⇒*zero , ⇒*→⇒ˢ⟨⟩* ⇒*zero′
    soundness-ℕ′ {v} (sucᵣ {v′} ⇒*suc ⇒*suc′ num t®v) =
      let n , d , d′ = soundness-ℕ′ t®v
      in  1+ n , ⇒ˢ*∷ℕ-trans (whred* ⇒*suc) (sucred* d) ,
          (case PE.singleton str of λ where
             (non-strict , PE.refl) →
               ⇒ˢ*-trans (whred*′ ⇒*suc′) (sucred*′ d′)
             (strict , PE.refl) →
               v              ⇒*⟨ ⇒*suc′ ⟩
               T.suc v′       ≡˘⟨ PE.cong T.suc $ TP.Value→⇒*→≡ (TP.Numeral→Value num) d′ ⟩⇒
               T.sucᵏ (1+ n)  ∎⇒)

  -- The following results make use of some assumptions.

  module Soundness
    (FA⁻ : Fundamental-assumptions⁻ Δ)
    (str : Strictness)
    where

    private module L (⊢Δ : ⊢ Δ) where

      open import Definition.Typed.EqRelInstance TR public

      FA : Fundamental-assumptions Δ
      FA = record
        { well-formed       = ⊢Δ
        ; other-assumptions = FA⁻
        }

      as : Assumptions
      as = record { ⊢Δ = ⊢Δ; str = str }

      open Soundness′ FA public

      open Graded.Erasure.LogicalRelation as public
      open Graded.Erasure.LogicalRelation.Fundamental.Fundamental
        TR UR FA
        public
      open Graded.Erasure.LogicalRelation.Hidden as public
      open Graded.Erasure.LogicalRelation.Irrelevance as public

    -- Soundness for erasure of natural numbers
    -- Well-typed terms of the natural number type reduce to numerals
    -- if erased matches are disallowed or the term is closed.
    --
    -- Note the assumptions of the local module Soundness.

    soundness-ℕ :
      Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
    soundness-ℕ {t} ⊢t ▸t =                                            $⟨ fundamentalErased-𝟙ᵐ ⊢t ▸t ⟩
      t ® erase str t ∷ ℕ                                              ⇔⟨ ®∷ℕ⇔ ⟩→
      t ® erase str t ∷ℕ                                               →⟨ soundness-ℕ′ ⟩
      (∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)  □
      where
      open L (wfTerm ⊢t)

    -- A variant of soundness-ℕ which only considers the source
    -- language.
    --
    -- Note the assumptions of the local module Soundness.

    soundness-ℕ-only-source :
      Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
    soundness-ℕ-only-source ⊢t ▸t =
      case soundness-ℕ ⊢t ▸t of λ {
        (n , t⇒ˢ*n , _) →
          n , t⇒ˢ*n }

    opaque

      -- Soundness of extraction for unit types.
      --
      -- Note the assumptions of the local module Soundness.

      soundness-Unit :
        Δ ⊢ t ∷ Unit s l → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        Δ ⊢ t ⇒* star s l ∷ Unit s l × erase str t T.⇒* T.star
      soundness-Unit ⊢t ▸t =
        case ®∷Unit⇔ .proj₁ $ fundamentalErased-𝟙ᵐ ⊢t ▸t of λ where
          (starᵣ t⇒*star erase-t⇒*star) →
            t⇒*star , erase-t⇒*star
        where
        open L (wfTerm ⊢t)

  -- If the context is empty, then the results in Soundness hold
  -- without any further assumptions.

  module Soundness₀ (str : Strictness) where

    open Soundness fundamental-assumptions⁻₀ str public

-- If Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 holds for some p (which means that
-- certain kinds of erased matches are allowed), and if additionally
-- Σʷ-allowed p 𝟘 holds, then there is a counterexample to
-- soundness-ℕ-only-source without the assumption "erased matches are
-- not allowed unless the context is empty" (and without the
-- strictness argument as well as the assumption that the modality's
-- zero is well-behaved).

soundness-ℕ-only-source-counterexample₁ :
  Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 →
  Σʷ-allowed p 𝟘 →
  let Δ = ε ∙ (Σʷ p , 𝟘 ▷ ℕ ▹ ℕ)
      t = prodrec 𝟘 p 𝟘 ℕ (var {n = 1} x0) zero
  in
  Consistent Δ ×
  Δ ⊢ t ∷ ℕ ×
  𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
  ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
soundness-ℕ-only-source-counterexample₁ {p = p} P-ok Σʷ-ok =
    inhabited-consistent
      (singleSubst (prodⱼ εℕ⊢ℕ (zeroⱼ ε) (zeroⱼ ε) Σʷ-ok))
  , ⊢prodrec
  , sub
      (prodrecₘ var
         (sub zeroₘ $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ 𝟙 · 𝟘 · p ∙ 𝟙 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-congˡ (·-zeroˡ _) ∙ PE.refl ⟩
            𝟘ᶜ ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘      ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ                      ∎)
         (sub ℕₘ $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ                ∎)
         P-ok)
      (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         𝟘ᶜ                           ≈˘⟨ +ᶜ-identityʳ _ ⟩
         𝟘ᶜ +ᶜ 𝟘ᶜ                     ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroˡ _) ⟩
         𝟘 ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ 𝟘 ⌟ ⌝) +ᶜ 𝟘ᶜ  ∎)
  , λ where
      (0    , whred d ⇨ˢ _) → whnfRedTerm d (ne (prodrecₙ (var _)))
      (1+ _ , whred d ⇨ˢ _) → whnfRedTerm d (ne (prodrecₙ (var _)))
  where
  ε⊢ℕ = ℕⱼ ε
  ⊢εℕ = ∙ ε⊢ℕ
  εℕ⊢ℕ = ℕⱼ ⊢εℕ
  ε⊢Σ = ΠΣⱼ εℕ⊢ℕ Σʷ-ok
  ⊢εΣ = ∙ ε⊢Σ
  ⊢εΣℕ = ∙ ℕⱼ ⊢εΣ
  εΣℕ⊢ℕ = ℕⱼ ⊢εΣℕ
  εΣ⊢Σ = ΠΣⱼ εΣℕ⊢ℕ Σʷ-ok
  ⊢εΣΣ = ∙ εΣ⊢Σ
  εΣΣ⊢ℕ = ℕⱼ ⊢εΣΣ
  ⊢εΣℕℕ = ∙ εΣℕ⊢ℕ
  ⊢prodrec = prodrecⱼ {r = 𝟘} εΣΣ⊢ℕ (var₀ ε⊢Σ) (zeroⱼ ⊢εΣℕℕ) Σʷ-ok

opaque

  -- If []-cong-allowed and []-cong-allowed-mode 𝟙ᵐ hold, then there is
  -- a counterexample to soundness-ℕ-only-source without the assumption
  -- "erased matches are not allowed unless the context is empty" (and
  -- without the strictness argument as well as the assumption that the
  -- modality's zero is well-behaved).

  soundness-ℕ-only-source-counterexample₂ :
    []-cong-allowed s →
    []-cong-allowed-mode s 𝟙ᵐ →
    let Δ = ε ∙ Id ℕ zero zero
        open Erased s
        t = J 𝟘 𝟘 (Erased ℕ) ([ zero ]) ℕ zero ([ zero ])
              ([]-cong s ℕ zero zero (var {n = 1} x0))
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₂ {s = s} ok ok′ =
    case ∙ Idⱼ (zeroⱼ ε) (zeroⱼ ε) of λ {
      ⊢Id →
      inhabited-consistent (singleSubst (rflⱼ (zeroⱼ ε)))
    , Jⱼ′ (ℕⱼ (J-motive-context ([]ⱼ ([]-cong→Erased ok) (zeroⱼ ⊢Id))))
        (zeroⱼ ⊢Id) ([]-congⱼ′ ok (var ⊢Id here))
    , sub
        (Jₘ-generalised (▸Erased s ℕₘ) (▸[] s zeroₘ)
           (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
            sub ℕₘ $ begin
              𝟘ᶜ ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ                  ∎)
           zeroₘ (▸[] s zeroₘ) ([]-congₘ ℕₘ zeroₘ zeroₘ var ok′))
        (≤ᶜ-reflexive (≈ᶜ-sym ω·ᶜ+ᶜ⁵𝟘ᶜ))
    , (λ where
         (0 , whred J⇒ ⇨ˢ _) →
           whnfRedTerm J⇒ (ne (Jₙ ([]-congₙ (var _))))
         (1+ _ , whred J⇒ ⇨ˢ _) →
           whnfRedTerm J⇒ (ne (Jₙ ([]-congₙ (var _))))) }

opaque

  -- If erased-matches-for-J 𝟙ᵐ is equal to not-none sem, then there
  -- is a counterexample to soundness-ℕ-only-source without the
  -- assumption "erased matches are not allowed unless the context is
  -- empty" (and without the strictness argument as well as the
  -- assumption that the modality's zero is well-behaved).

  soundness-ℕ-only-source-counterexample₃ :
    erased-matches-for-J 𝟙ᵐ ≡ not-none sem →
    let Δ = ε ∙ Id ℕ zero zero
        t = J 𝟘 𝟘 ℕ zero ℕ zero zero (var {n = 1} x0)
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₃ ≡not-none =
    case ∙ Idⱼ (zeroⱼ ε) (zeroⱼ ε) of λ {
      ⊢Id →
      inhabited-consistent (singleSubst (rflⱼ (zeroⱼ ε)))
    , Jⱼ′ (ℕⱼ (J-motive-context (zeroⱼ ⊢Id))) (zeroⱼ ⊢Id) (var ⊢Id here)
    , sub
        (J₀ₘ₁-generalised ≡not-none PE.refl PE.refl ℕₘ zeroₘ ℕₘ zeroₘ
           zeroₘ var)
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
    , (λ where
         (0    , whred J⇒ ⇨ˢ _) → whnfRedTerm J⇒ (ne (Jₙ (var _)))
         (1+ _ , whred J⇒ ⇨ˢ _) → whnfRedTerm J⇒ (ne (Jₙ (var _)))) }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- If the K rule is allowed and erased-matches-for-K 𝟙ᵐ is equal to
  -- not-none sem, then there is a counterexample to
  -- soundness-ℕ-only-source without the assumption "erased matches
  -- are not allowed unless the context is empty" (and without the
  -- strictness argument as well as the assumption that the modality's
  -- zero is well-behaved).

  soundness-ℕ-only-source-counterexample₄ :
    K-allowed →
    erased-matches-for-K 𝟙ᵐ ≡ not-none sem →
    let Δ = ε ∙ Id ℕ zero zero
        t = K 𝟘 ℕ zero ℕ zero (var {n = 1} x0)
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₄ K-ok ≡not-none =
    case ∙ Idⱼ (zeroⱼ ε) (zeroⱼ ε) of λ {
      ⊢Id →
      inhabited-consistent (singleSubst (rflⱼ (zeroⱼ ε)))
    , Kⱼ′ (ℕⱼ (K-motive-context (zeroⱼ ⊢Id))) (zeroⱼ ⊢Id) (var ⊢Id here)
        K-ok
    , sub
        (K₀ₘ₁-generalised ≡not-none PE.refl ℕₘ zeroₘ ℕₘ zeroₘ var)
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
    , (λ where
         (0    , whred K⇒ ⇨ˢ _) → whnfRedTerm K⇒ (ne (Kₙ (var _)))
         (1+ _ , whred K⇒ ⇨ˢ _) → whnfRedTerm K⇒ (ne (Kₙ (var _)))) }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- If Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 and Unitʷ-allowed hold and η-equality
  -- is not allowed for weak unit types, then there is a
  -- counterexample to soundness-ℕ-only-source without the assumption
  -- "erased matches are not allowed unless the context is empty" (and
  -- without the strictness argument as well as the assumption that
  -- the modality's zero is well-behaved).

  soundness-ℕ-only-source-counterexample₅ :
    Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 →
    Unitʷ-allowed →
    ¬ Unitʷ-η →
    let Δ = ε ∙ Unitʷ 0
        t = unitrec 0 𝟘 𝟘 ℕ (var {n = 1} x0) zero
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₅ unitrec-ok Unit-ok no-η =
    case Unitⱼ ε Unit-ok of λ
      ⊢Unit →
    case ∙ ⊢Unit of λ
      ⊢∙Unit →
      inhabited-consistent (singleSubst (starⱼ ε Unit-ok))
    , unitrecⱼ (ℕⱼ (⊢∙Unit ∙[ flip Unitⱼ Unit-ok ])) (var₀ ⊢Unit)
        (zeroⱼ ⊢∙Unit) Unit-ok
    , sub
        (unitrecₘ var zeroₘ
           (sub ℕₘ $
            let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
              𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ                ∎)
           unitrec-ok)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ                                ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
           𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ 𝟘 ⌟ ⌝)        ≈˘⟨ +ᶜ-identityʳ _ ⟩
           𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ 𝟘 ⌟ ⌝) +ᶜ 𝟘ᶜ  ∎)
    , (λ where
         (0 , whred unitrec⇒ ⇨ˢ _) →
           whnfRedTerm unitrec⇒ (ne (unitrecₙ no-η (var _)))
         (1+ _ , whred unitrec⇒ ⇨ˢ _) →
           whnfRedTerm unitrec⇒ (ne (unitrecₙ no-η (var _))))

opaque

  -- If Emptyrec-allowed 𝟙ᵐ 𝟘 holds, then there are counterexamples to
  -- both parts of the conclusion of a variant of the statement of
  -- soundness-ℕ without the following assumptions (for any
  -- strictness):
  --
  -- * "if erased matches are allowed for emptyrec when the mode
  --   is 𝟙ᵐ, then the context is consistent",
  -- * "erased matches are not allowed unless the context is empty",
  --   and
  -- * the assumption that the modality's zero is well-behaved.
  --
  -- Note that the counterexample does not make use of any erased
  -- matches (except for emptyrec).

  soundness-ℕ-counterexample₆ :
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    let Δ = ε ∙ Empty
        t = emptyrec 𝟘 ℕ (var x0)
    in
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    (¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ) ×
    (¬ ∃ λ n → erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)
  soundness-ℕ-counterexample₆ emptyrec-ok =
      emptyrecⱼ (ℕⱼ (ε ∙[ Emptyⱼ ])) (var₀ (Emptyⱼ ε))
    , (sub (emptyrecₘ var ℕₘ emptyrec-ok) $ begin
         𝟘ᶜ                          ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ 𝟘 ⌟ ⌝)  ∎)
    , (λ where
         (0 , whred emptyrec⇒ ⇨ˢ _) →
           whnfRedTerm emptyrec⇒ (ne (emptyrecₙ (var _)))
         (1+ _ , whred emptyrec⇒ ⇨ˢ _) →
           whnfRedTerm emptyrec⇒ (ne (emptyrecₙ (var _))))
    , ¬loop⇒ˢ* TP.Value-sucᵏ ∘→ proj₂
    where
    open ≤ᶜ-reasoning

-- Run-time canonicity for a given term with respect to a given
-- context (and strictness).

Run-time-canonicity-for : Strictness → Con Term n → Term n → Set a
Run-time-canonicity-for str Δ t =
  ∃₂ λ n u → Δ ⊢ u ∷ Id ℕ t (sucᵏ n) × erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n

-- Above some counterexamples to variants of soundness-ℕ-only-source
-- are presented. Those counterexamples are (at the time of writing)
-- not counterexamples to "run-time canonicity holds for well-typed,
-- well-resourced terms of type ℕ in consistent contexts".

soundness-ℕ-only-target-not-counterexample₁ :
  Σʷ-allowed p 𝟘 →
  Run-time-canonicity-for str
    (ε ∙ Σʷ p , 𝟘 ▷ ℕ ▹ ℕ)
    (prodrec 𝟘 p 𝟘 ℕ (var {n = 1} x0) zero)
soundness-ℕ-only-target-not-counterexample₁ {p} ok
  with is-𝟘? 𝟘
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
... | yes _ =
    0
  , subst ω ℕ² (Id ℕ pr zero) 0,0 (var x0) η rfl
  , ⊢subst (Idⱼ ⊢pr (zeroⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ])))
      (⊢Σʷ-η-prodʷ-fstʷ-sndʷ (var₀ (⊢ℕ² ε)))
      (rflⱼ′
         (prodrec 𝟘 p 𝟘 ℕ 0,0 zero  ≡⟨ prodrec-β-≡ (ℕⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ]))
                                         (fstʷⱼ (var₀ (⊢ℕ² ε))) (sndʷⱼ (var₀ (⊢ℕ² ε)))
                                         (zeroⱼ (ε ∙[ ⊢ℕ² ] ∙[ ℕⱼ ] ∙[ ℕⱼ ])) ok ⟩⊢∎
          zero                      ∎))
  , refl-⇒ˢ⟨⟩*
  where
  ℕ² : Term n
  ℕ² = Σʷ p , 𝟘 ▷ ℕ ▹ ℕ

  Δ′ : Con Term 1
  Δ′ = ε ∙ ℕ²

  pr : Term 2
  pr = prodrec _ _ _ _ (var x0) zero

  0,0 : Term 1
  0,0 = prodʷ _ (fstʷ _ _ (var x0)) (sndʷ _ _ ℕ ℕ (var x0))

  η : Term 1
  η = Σʷ-η-prodʷ-fstʷ-sndʷ _ _ _ _ (var x0)

  ⊢ℕ² : ⊢ Γ → Γ ⊢ ℕ²
  ⊢ℕ² ⊢Γ = ΠΣⱼ (ℕⱼ (⊢Γ ∙[ ℕⱼ ])) ok

  ⊢pr : Δ′ ∙ ℕ² ⊢ pr ∷ ℕ
  ⊢pr =
    prodrecⱼ′ (ℕⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ]))
      (var₀ (⊢ℕ² (ε ∙[ ⊢ℕ² ])))
      (zeroⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ] ∙[ ℕⱼ ] ∙[ ℕⱼ ]))

opaque

  soundness-ℕ-only-target-not-counterexample₂ :
    []-cong-allowed s →
    let open Erased s in
    Run-time-canonicity-for str
      (ε ∙ Id ℕ zero zero)
      (J 𝟘 𝟘 (Erased ℕ) ([ zero ]) ℕ zero ([ zero ])
         ([]-cong s ℕ zero zero (var {n = 1} x0)))
  soundness-ℕ-only-target-not-counterexample₂ {s} ok =
      _
    , J 𝟘 𝟘 ℕ zero
        (Id ℕ
            (J 𝟘 𝟘 (Erased ℕ) Er.[ zero ] ℕ zero Er.[ var x1 ]
               ([]-cong s ℕ zero (var x1) (var x0)))
            zero)
        rfl zero (var x0)
    , Jⱼ′
        (Idⱼ
           (Jⱼ′ (ℕⱼ (J-motive-context ([]ⱼ Erased-ok ⊢zero))) ⊢zero
              ([]-congⱼ′ ok
                 (var₀ (J-motive-context-type (zeroⱼ ⊢Δ)))))
           ⊢zero)
        (rflⱼ′
           (J 𝟘 𝟘 (Erased ℕ) Er.[ zero ] ℕ zero Er.[ zero ]
              ([]-cong s ℕ zero zero rfl)                        ≡⟨ J-cong′ (refl (Erasedⱼ Erased-ok (ℕⱼ ⊢Δ)))
                                                                      (refl ([]ⱼ Erased-ok (zeroⱼ ⊢Δ))) (refl ⊢ℕ)
                                                                      (refl (zeroⱼ ⊢Δ)) (refl ([]ⱼ Erased-ok (zeroⱼ ⊢Δ)))
                                                                      ([]-cong-β (zeroⱼ ⊢Δ) PE.refl ok) ⟩⊢

            J 𝟘 𝟘 (Erased ℕ) Er.[ zero ] ℕ zero Er.[ zero ] rfl  ≡⟨ J-β-≡ ([]ⱼ Erased-ok (zeroⱼ ⊢Δ)) ⊢ℕ (zeroⱼ ⊢Δ) ⟩⊢∎

            zero                                                 ∎))
        (var₀ ⊢0≡0)
    , refl-⇒ˢ⟨⟩*
    where
    open module Er = Erased s using (Erased)

    Erased-ok : Erased-allowed s
    Erased-ok = []-cong→Erased ok

    Δ′ : Con Term 1
    Δ′ = ε ∙ Id ℕ zero zero

    ⊢0≡0 : ε ⊢ Id ℕ zero zero
    ⊢0≡0 = Idⱼ (zeroⱼ ε) (zeroⱼ ε)

    ⊢Δ : ⊢ Δ′
    ⊢Δ = ∙ ⊢0≡0

    ⊢ℕ : Δ′ ∙ Erased ℕ ∙ Id (Erased ℕ) Er.[ zero ] (var x0) ⊢ ℕ
    ⊢ℕ = ℕⱼ (J-motive-context ([]ⱼ Erased-ok (zeroⱼ ⊢Δ)))

    ⊢zero : Δ′ ∙ ℕ ∙ Id ℕ zero (var x0) ⊢ zero ∷ ℕ
    ⊢zero = zeroⱼ (J-motive-context (zeroⱼ ⊢Δ))

opaque

  soundness-ℕ-only-target-not-counterexample₃ :
    Run-time-canonicity-for str
      (ε ∙ Id ℕ zero zero)
      (J 𝟘 𝟘 ℕ zero ℕ zero zero (var {n = 1} x0))
  soundness-ℕ-only-target-not-counterexample₃ =
      _
    , J 𝟘 𝟘 ℕ zero
        (Id ℕ (J 𝟘 𝟘 ℕ zero ℕ zero (var x1) (var x0)) zero)
        rfl zero (var x0)
    , Jⱼ′
        (Idⱼ
           (Jⱼ′ (ℕⱼ (J-motive-context ⊢zero)) ⊢zero
              (var₀ (J-motive-context-type (zeroⱼ ⊢Δ))))
           ⊢zero)
        (rflⱼ′
           (J 𝟘 𝟘 ℕ zero ℕ zero zero rfl  ≡⟨ J-β-≡ (zeroⱼ ⊢Δ) ⊢ℕ (zeroⱼ ⊢Δ) ⟩⊢∎
            zero                          ∎))
        (var₀ ⊢0≡0)
    , refl-⇒ˢ⟨⟩*
    where
    Δ′ : Con Term 1
    Δ′ = ε ∙ Id ℕ zero zero

    ⊢0≡0 : ε ⊢ Id ℕ zero zero
    ⊢0≡0 = Idⱼ (zeroⱼ ε) (zeroⱼ ε)

    ⊢Δ : ⊢ Δ′
    ⊢Δ = ∙ ⊢0≡0

    ⊢ℕ : Δ′ ∙ ℕ ∙ Id ℕ zero (var x0) ⊢ ℕ
    ⊢ℕ = ℕⱼ (J-motive-context (zeroⱼ ⊢Δ))

    ⊢zero : Δ′ ∙ ℕ ∙ Id ℕ zero (var x0) ⊢ zero ∷ ℕ
    ⊢zero = zeroⱼ (J-motive-context (zeroⱼ ⊢Δ))

opaque

  soundness-ℕ-only-target-not-counterexample₄ :
    K-allowed →
    Run-time-canonicity-for str
      (ε ∙ Id ℕ zero zero)
      (K 𝟘 ℕ zero ℕ zero (var {n = 1} x0))
  soundness-ℕ-only-target-not-counterexample₄ ok =
      _
    , K 𝟘 ℕ zero
        (Id ℕ (K 𝟘 ℕ zero ℕ zero (var x0)) zero)
        rfl (var x0)
    , Kⱼ′
        (Idⱼ
           (Kⱼ′ (ℕⱼ (K-motive-context ⊢zero)) ⊢zero
              (var₀ (K-motive-context-type (zeroⱼ ⊢Δ))) ok)
           ⊢zero)
        (rflⱼ′
           (K 𝟘 ℕ zero ℕ zero rfl  ≡⟨ K-β-≡ ⊢ℕ (zeroⱼ ⊢Δ) ok ⟩⊢∎
            zero                   ∎))
        (var₀ ⊢0≡0)
        ok
    , refl-⇒ˢ⟨⟩*
    where
    Δ′ : Con Term 1
    Δ′ = ε ∙ Id ℕ zero zero

    ⊢0≡0 : ε ⊢ Id ℕ zero zero
    ⊢0≡0 = Idⱼ (zeroⱼ ε) (zeroⱼ ε)

    ⊢Δ : ⊢ Δ′
    ⊢Δ = ∙ ⊢0≡0

    ⊢ℕ : Δ′ ∙ Id ℕ zero zero ⊢ ℕ
    ⊢ℕ = ℕⱼ (K-motive-context (zeroⱼ ⊢Δ))

    ⊢zero : Δ′ ∙ Id ℕ zero zero ⊢ zero ∷ ℕ
    ⊢zero = zeroⱼ (K-motive-context (zeroⱼ ⊢Δ))

opaque

  soundness-ℕ-only-target-not-counterexample₅ :
    Unitʷ-allowed →
    Run-time-canonicity-for str
      (ε ∙ Unitʷ 0)
      (unitrec 0 𝟘 𝟘 ℕ (var {n = 1} x0) zero)
  soundness-ℕ-only-target-not-counterexample₅ Unit-ok with is-𝟘? 𝟘
  … | no 𝟘≢𝟘 = ⊥-elim $ 𝟘≢𝟘 PE.refl
  … | yes _  =
      _
    , subst ω (Unitʷ 0) (Id ℕ (unitrec 0 𝟘 𝟘 ℕ (var x0) zero) zero)
        (starʷ 0) (var x0) (Unit-η 𝕨 0 ω (var x0)) rfl
    , ⊢subst
        (Idⱼ
           (unitrecⱼ (ℕⱼ (ε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ]))
              (var₀ (⊢Unitʷ (ε ∙[ ⊢Unitʷ ])))
              (zeroⱼ (ε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ])) Unit-ok)
           (zeroⱼ (ε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ])))
        (⊢Unit-η (var₀ (⊢Unitʷ ε)))
        (rflⱼ′
           (unitrec 0 𝟘 𝟘 ℕ (starʷ 0) zero  ≡⟨ unitrec-β-≡ (ℕⱼ (ε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ])) (zeroⱼ (ε ∙[ ⊢Unitʷ ])) ⟩⊢∎
            zero                            ∎))
    , refl-⇒ˢ⟨⟩*
    where
    ⊢Unitʷ : ⊢ Γ → Γ ⊢ Unitʷ 0
    ⊢Unitʷ ⊢Γ = Unitⱼ ⊢Γ Unit-ok

-- A variant of run-time canonicity that uses erase′ true instead of
-- erase.

Run-time-canonicity-with-arguments-removed-for :
  Strictness → Con Term n → Term n → Set a
Run-time-canonicity-with-arguments-removed-for str Δ t =
  ∃₂ λ n u →
  Δ ⊢ u ∷ Id ℕ t (sucᵏ n) ×
  erase′ true str t ⇒ˢ⟨ str ⟩* T.sucᵏ n

opaque

  -- Run-time canonicity does not necessarily hold for closed,
  -- well-typed, well-resourced terms of type ℕ if strict applications
  -- are used and erasable arguments are removed entirely, assuming
  -- that certain Π-types are allowed and that the modality's zero is
  -- well-behaved.

  no-run-time-canonicity-if-strict-and-arguments-removed :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    Π-allowed 𝟘 p →
    Π-allowed ω q →
    Π-allowed (ω + ω) q →
    q ≤ 𝟘 →
    ¬ ((t : Term 0) → ε ⊢ t ∷ ℕ → ε ▸[ 𝟙ᵐ ] t →
       Run-time-canonicity-with-arguments-removed-for strict ε t)
  no-run-time-canonicity-if-strict-and-arguments-removed
    emptyrec-ok 𝟘-ok ω-ok ω+ω-ok q≤𝟘 hyp =
    case hyp (loops _) (⊢loops 𝟘-ok ω-ok ω+ω-ok ε)
           (▸loops emptyrec-ok q≤𝟘) of λ
      (_ , _ , _ , ⇒*n) →
    loops-does-not-reduce-to-a-value TP.Value-sucᵏ ⇒*n
