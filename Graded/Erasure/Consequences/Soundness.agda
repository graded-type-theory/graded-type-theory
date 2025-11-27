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
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
open import Definition.Untyped.Unit 𝕄

open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR
import Definition.Typed.Consequences.Canonicity TR as TC
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Substitution TR
open import Definition.Typed.Well-formed TR

open import Graded.Context 𝕄
open import Graded.Derived.Erased.Usage 𝕄 UR
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Erased-matches
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Context.Properties 𝕄
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
open import Tools.Product as Σ
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.PropositionalEquality as PE using (_≢_)

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
    where

    open Fundamental-assumptions FA

    private

      as : Assumptions
      as = record
        { ⊢Δ                    = well-formed
        ; inc                   = no-equality-reflection-or-empty
        ; str                   = str
        ; is-reduction-relation = ⇒*-is-reduction-relation
        }

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

  open import Definition.Typed.EqRelInstance TR

  module Soundness
    (FA⁻ : Fundamental-assumptions⁻ Δ)
    where

    private module L (str : Strictness) (⊢Δ : ⊢ Δ) where

      FA : Fundamental-assumptions Δ
      FA = record
        { well-formed       = ⊢Δ
        ; other-assumptions = FA⁻
        }

      as : Assumptions
      as = record
        { ⊢Δ =
            ⊢Δ
        ; inc =
            Fundamental-assumptions.no-equality-reflection-or-empty FA
        ; str =
            str
        ; is-reduction-relation =
            ⇒*-is-reduction-relation
        }

      open Soundness′ FA public

      open Graded.Erasure.LogicalRelation as public
      open Graded.Erasure.LogicalRelation.Fundamental.Fundamental
        TR UR FA
        public
      open Graded.Erasure.LogicalRelation.Hidden as public
      open Graded.Erasure.LogicalRelation.Irrelevance as public

    private opaque

      -- A preliminary formulation of soundness for ℕ.

      soundness-ℕ″ :
        ∀ str →
        Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
      soundness-ℕ″ {t} str ⊢t ▸t =                                       $⟨ fundamentalErased-𝟙ᵐ ⊢t ▸t ⟩
        t ® erase str t ∷ ℕ                                              ⇔⟨ ®∷ℕ⇔ ⟩→
        t ® erase str t ∷ℕ                                               →⟨ soundness-ℕ′ ⟩
        (∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ × erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)  □
        where
        open L str (wfTerm ⊢t)

    opaque

      -- Soundness of erasure for natural numbers.
      --
      -- Note the assumptions of the local module Soundness.

      soundness-ℕ :
        Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ ×
          (∀ str → erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)
      soundness-ℕ ⊢t ▸t =
        let n , t⇒*₁ , erase-t⇒*₁ = soundness-ℕ″ non-strict ⊢t ▸t
            _ , t⇒*₂ , erase-t⇒*₂ = soundness-ℕ″     strict ⊢t ▸t
        in
        n , t⇒*₁ , λ where
          non-strict → erase-t⇒*₁
          strict     →
            PE.subst (_⇒ˢ⟨_⟩*_ _ _)
              (PE.cong T.sucᵏ $ sucᵏ-PE-injectivity $
               deterministic-⊢⇒ˢ*∷ℕ t⇒*₂ t⇒*₁
                 (sucᵏ-Numeral _) (sucᵏ-Numeral _))
              erase-t⇒*₂

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

    private opaque

      -- A preliminary formulation of soundness for Unit.

      soundness-Unit′ :
        ∀ str →
        Δ ⊢ t ∷ Unit s → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        Δ ⊢ t ⇒* star s ∷ Unit s × erase str t T.⇒* T.star
      soundness-Unit′ str ⊢t ▸t =
        case ®∷Unit⇔ .proj₁ $ fundamentalErased-𝟙ᵐ ⊢t ▸t of λ where
          (starᵣ t⇒*star erase-t⇒*star) →
            t⇒*star ,
            erase-t⇒*star
        where
        open L str (wfTerm ⊢t)

    opaque

      -- Soundness of extraction for unit types.
      --
      -- Note the assumptions of the local module Soundness.

      soundness-Unit :
        Δ ⊢ t ∷ Unit s → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        Δ ⊢ t ⇒* star s ∷ Unit s × (∀ str → erase str t T.⇒* T.star)
      soundness-Unit ⊢t ▸t =
        let t⇒* , erase-t⇒*₁ = soundness-Unit′     strict ⊢t ▸t
            _   , erase-t⇒*₂ = soundness-Unit′ non-strict ⊢t ▸t
        in
        t⇒* , λ where
          strict     → erase-t⇒*₁
          non-strict → erase-t⇒*₂

  -- If the context is empty, then the results in Soundness hold
  -- without any further assumptions.

  module Soundness₀ where

    private
      module S = Soundness fundamental-assumptions⁻₀

    opaque

      -- Soundness of extraction for natural numbers.

      soundness-ℕ :
        ε ⊢ t ∷ ℕ → ε ▸[ 𝟙ᵐ ] t →
        ∃ λ n → ε ⊢ t ⇒ˢ* sucᵏ n ∷ℕ ×
          (∀ str → erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)
      soundness-ℕ = S.soundness-ℕ

    opaque

      -- A variant of soundness-ℕ which only considers the source
      -- language.

      soundness-ℕ-only-source :
        ε ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        ∃ λ n → ε ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
      soundness-ℕ-only-source = S.soundness-ℕ-only-source

    opaque

      -- Soundness of extraction for unit types.

      soundness-Unit :
        ε ⊢ t ∷ Unit s → ε ▸[ 𝟙ᵐ ] t →
        ε ⊢ t ⇒* star s ∷ Unit s × (∀ str → erase str t T.⇒* T.star)
      soundness-Unit = S.soundness-Unit

-- If Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 and Σʷ-allowed p 𝟘 hold for some p,
-- then there is a counterexample to soundness-ℕ-only-source without
-- the assumption "erased matches are not allowed unless the context
-- is empty" (and without the assumption that the modality's zero is
-- well-behaved).

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
      (⊢ˢʷ∷-sgSubst (prodⱼ εℕ⊢ℕ (zeroⱼ ε) (zeroⱼ ε) Σʷ-ok))
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
      (0    , whred d ⇨ˢ _) → whnfRedTerm d (ne! (prodrecₙ (var _)))
      (1+ _ , whred d ⇨ˢ _) → whnfRedTerm d (ne! (prodrecₙ (var _)))
  where
  ε⊢ℕ = ⊢ℕ ε
  ⊢εℕ = ∙ ε⊢ℕ
  εℕ⊢ℕ = ⊢ℕ ⊢εℕ
  ε⊢Σ = ΠΣⱼ εℕ⊢ℕ Σʷ-ok
  ⊢εΣ = ∙ ε⊢Σ
  ⊢εΣℕ = ∙ ⊢ℕ ⊢εΣ
  εΣℕ⊢ℕ = ⊢ℕ ⊢εΣℕ
  εΣ⊢Σ = ΠΣⱼ εΣℕ⊢ℕ Σʷ-ok
  ⊢εΣΣ = ∙ εΣ⊢Σ
  εΣΣ⊢ℕ = ⊢ℕ ⊢εΣΣ
  ⊢εΣℕℕ = ∙ εΣℕ⊢ℕ
  ⊢prodrec = prodrecⱼ {r = 𝟘} εΣΣ⊢ℕ (var₀ ε⊢Σ) (zeroⱼ ⊢εΣℕℕ) Σʷ-ok

opaque

  -- If []-cong-allowed and []-cong-allowed-mode 𝟙ᵐ hold, then there
  -- is a counterexample to soundness-ℕ-only-source without the
  -- assumption "erased matches are not allowed unless the context is
  -- empty" (and without the assumption that the modality's zero is
  -- well-behaved).

  soundness-ℕ-only-source-counterexample₂ :
    []-cong-allowed s →
    []-cong-allowed-mode s 𝟙ᵐ →
    let Δ = ε ∙ Id ℕ zero zero
        open Erased s
        t = J 𝟘 𝟘 (Erased zeroᵘ ℕ) ([ zero ]) ℕ zero ([ zero ])
              ([]-cong s zeroᵘ ℕ zero zero (var {n = 1} x0))
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₂ {s = s} ok ok′ =
    let ⊢Id = ∙ Idⱼ′ (zeroⱼ ε) (zeroⱼ ε) in
    inhabited-consistent (⊢ˢʷ∷-sgSubst (rflⱼ (zeroⱼ ε))) ,
    Jⱼ′
      (⊢ℕ $ J-motive-context $
       []ⱼ ([]-cong→Erased ok) (⊢zeroᵘ ⊢Id) (zeroⱼ ⊢Id))
      (zeroⱼ ⊢Id) ([]-congⱼ′ ok (⊢zeroᵘ ⊢Id) (var ⊢Id here)) ,
    sub
      (Jₘ-generalised (▸Erased s zeroᵘₘ ℕₘ) (▸[] s zeroₘ)
         (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
          sub ℕₘ $ begin
            𝟘ᶜ ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ                  ∎)
         zeroₘ (▸[] s zeroₘ) ([]-congₘ zeroᵘₘ ℕₘ zeroₘ zeroₘ var ok′))
      (≤ᶜ-reflexive (≈ᶜ-sym ω·ᶜ+ᶜ⁵𝟘ᶜ)) ,
    (λ where
       (0 , whred J⇒ ⇨ˢ _) →
         whnfRedTerm J⇒ (ne! (Jₙ ([]-congₙ (var _))))
       (1+ _ , whred J⇒ ⇨ˢ _) →
         whnfRedTerm J⇒ (ne! (Jₙ ([]-congₙ (var _)))))

opaque

  -- If erased-matches-for-J 𝟙ᵐ is equal to not-none sem, then there
  -- is a counterexample to soundness-ℕ-only-source without the
  -- assumption "erased matches are not allowed unless the context is
  -- empty" (and without the assumption that the modality's zero is
  -- well-behaved).

  soundness-ℕ-only-source-counterexample₃ :
    erased-matches-for-J 𝟙ᵐ PE.≡ not-none sem →
    let Δ = ε ∙ Id ℕ zero zero
        t = J 𝟘 𝟘 ℕ zero ℕ zero zero (var {n = 1} x0)
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₃ ≡not-none =
    case ∙ Idⱼ′ (zeroⱼ ε) (zeroⱼ ε) of λ {
      ⊢Id →
      inhabited-consistent (⊢ˢʷ∷-sgSubst (rflⱼ (zeroⱼ ε)))
    , Jⱼ′ (⊢ℕ (J-motive-context (zeroⱼ ⊢Id))) (zeroⱼ ⊢Id) (var ⊢Id here)
    , sub
        (J₀ₘ₁-generalised ≡not-none PE.refl PE.refl ℕₘ zeroₘ ℕₘ zeroₘ
           zeroₘ var)
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
    , (λ where
         (0    , whred J⇒ ⇨ˢ _) → whnfRedTerm J⇒ (ne! (Jₙ (var _)))
         (1+ _ , whred J⇒ ⇨ˢ _) → whnfRedTerm J⇒ (ne! (Jₙ (var _)))) }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- If the K rule is allowed and erased-matches-for-K 𝟙ᵐ is equal to
  -- not-none sem, then there is a counterexample to
  -- soundness-ℕ-only-source without the assumption "erased matches
  -- are not allowed unless the context is empty" (and without the
  -- assumption that the modality's zero is well-behaved).

  soundness-ℕ-only-source-counterexample₄ :
    K-allowed →
    erased-matches-for-K 𝟙ᵐ PE.≡ not-none sem →
    let Δ = ε ∙ Id ℕ zero zero
        t = K 𝟘 ℕ zero ℕ zero (var {n = 1} x0)
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₄ K-ok ≡not-none =
    case ∙ Idⱼ′ (zeroⱼ ε) (zeroⱼ ε) of λ {
      ⊢Id →
      inhabited-consistent (⊢ˢʷ∷-sgSubst (rflⱼ (zeroⱼ ε)))
    , Kⱼ (⊢ℕ (K-motive-context (zeroⱼ ⊢Id))) (zeroⱼ ⊢Id) (var ⊢Id here)
        K-ok
    , sub
        (K₀ₘ₁-generalised ≡not-none PE.refl ℕₘ zeroₘ ℕₘ zeroₘ var)
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
    , (λ where
         (0    , whred K⇒ ⇨ˢ _) → whnfRedTerm K⇒ (ne! (Kₙ (var _)))
         (1+ _ , whred K⇒ ⇨ˢ _) → whnfRedTerm K⇒ (ne! (Kₙ (var _)))) }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- If Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 and Unitʷ-allowed hold and η-equality
  -- is not allowed for weak unit types, then there is a
  -- counterexample to soundness-ℕ-only-source without the assumption
  -- "erased matches are not allowed unless the context is empty" (and
  -- without the assumption that the modality's zero is well-behaved).

  soundness-ℕ-only-source-counterexample₅ :
    Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 →
    Unitʷ-allowed →
    ¬ Unitʷ-η →
    let Δ = ε ∙ Unitʷ
        t = unitrec 𝟘 𝟘 ℕ (var {n = 1} x0) zero
    in
    Consistent Δ ×
    Δ ⊢ t ∷ ℕ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ n → Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
  soundness-ℕ-only-source-counterexample₅ unitrec-ok Unit-ok no-η =
    let ε⊢Unit = ⊢Unit ε Unit-ok
    in
      inhabited-consistent (⊢ˢʷ∷-sgSubst (starⱼ ε Unit-ok))
    , unitrecⱼ (⊢ℕ (∙ ⊢Unit (∙ ε⊢Unit) Unit-ok)) (var₀ ε⊢Unit)
        (zeroⱼ (∙ ε⊢Unit)) Unit-ok
    , sub
        (unitrecₘ
           (sub ℕₘ $
            let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
              𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ                ∎)
           var zeroₘ unitrec-ok)
        (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
           𝟘ᶜ                                ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
           𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ 𝟘 ⌟ ⌝)        ≈˘⟨ +ᶜ-identityʳ _ ⟩
           𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ 𝟘 ⌟ ⌝) +ᶜ 𝟘ᶜ  ∎)
    , (λ where
         (0 , whred unitrec⇒ ⇨ˢ _) →
           whnfRedTerm unitrec⇒ (ne! (unitrecₙ no-η (var _)))
         (1+ _ , whred unitrec⇒ ⇨ˢ _) →
           whnfRedTerm unitrec⇒ (ne! (unitrecₙ no-η (var _))))

opaque

  -- If Emptyrec-allowed 𝟙ᵐ 𝟘 holds, then there are counterexamples to
  -- both parts of the conclusion of a variant of the statement of
  -- soundness-ℕ without the following assumptions:
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
    (¬ ∃ λ n → ∀ str → erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n) ×
    (∀ str → ¬ ∃ λ n → erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)
  soundness-ℕ-counterexample₆ emptyrec-ok =
      emptyrecⱼ (⊢ℕ (ε ∙[ ⊢Empty ])) (var₀ (⊢Empty ε))
    , (sub (emptyrecₘ var ℕₘ emptyrec-ok) $ begin
         𝟘ᶜ                          ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ 𝟘 ⌟ ⌝)  ∎)
    , (λ where
         (0 , whred emptyrec⇒ ⇨ˢ _) →
           whnfRedTerm emptyrec⇒ (ne! (emptyrecₙ (var _)))
         (1+ _ , whred emptyrec⇒ ⇨ˢ _) →
           whnfRedTerm emptyrec⇒ (ne! (emptyrecₙ (var _))))
    , let ce = λ _ → ¬loop⇒ˢ* TP.Value-sucᵏ ∘→ proj₂ in
      ce strict ∘→ Σ.map idᶠ (_$ strict)
    , ce
    where
    open ≤ᶜ-reasoning

-- Run-time canonicity for a given term with respect to a given
-- context.

Run-time-canonicity-for : Con Term n → Term n → Set a
Run-time-canonicity-for Δ t =
  ∃₂ λ n u →
  Δ ⊢ u ∷ Id ℕ t (sucᵏ n) ×
  (∀ str → erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)

-- Above some counterexamples to variants of soundness-ℕ-only-source
-- are presented. Some of those counterexamples are (at the time of
-- writing) not counterexamples to "run-time canonicity holds for
-- well-typed, well-resourced terms of type ℕ in consistent contexts".

soundness-ℕ-only-target-not-counterexample₁ :
  Σʷ-allowed p 𝟘 →
  Run-time-canonicity-for
    (ε ∙ Σʷ p , 𝟘 ▷ ℕ ▹ ℕ)
    (prodrec 𝟘 p 𝟘 ℕ (var {n = 1} x0) zero)
soundness-ℕ-only-target-not-counterexample₁ {p} ok
  with is-𝟘? 𝟘
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
... | yes _ =
    0
  , subst ω ℕ² (Id ℕ pr zero) 0,0 (var x0) η rfl
  , ⊢subst (Idⱼ′ ⊢pr (zeroⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ])))
      (⊢Σʷ-η-prodʷ-fstʷ-sndʷ (var₀ (⊢ℕ² ε)))
      (rflⱼ′
         (prodrec 𝟘 p 𝟘 ℕ 0,0 zero  ≡⟨ prodrec-β-≡ (⊢ℕ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ]))
                                         (fstʷⱼ (var₀ (⊢ℕ² ε))) (sndʷⱼ (var₀ (⊢ℕ² ε)))
                                         (zeroⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ ] ∙[ ⊢ℕ ])) ⟩⊢∎
          zero                      ∎))
  , (λ _ → refl-⇒ˢ⟨⟩*)
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
  ⊢ℕ² ⊢Γ = ΠΣⱼ (⊢ℕ (⊢Γ ∙[ ⊢ℕ ])) ok

  ⊢pr : Δ′ ∙ ℕ² ⊢ pr ∷ ℕ
  ⊢pr =
    prodrecⱼ′ (⊢ℕ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ]))
      (var₀ (⊢ℕ² (ε ∙[ ⊢ℕ² ])))
      (zeroⱼ (ε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ] ∙[ ⊢ℕ ] ∙[ ⊢ℕ ]))

opaque

  soundness-ℕ-only-target-not-counterexample₂ :
    []-cong-allowed s →
    let open Erased s in
    Run-time-canonicity-for
      (ε ∙ Id ℕ zero zero)
      (J 𝟘 𝟘 (Erased zeroᵘ ℕ) ([ zero ]) ℕ zero ([ zero ])
         ([]-cong s zeroᵘ ℕ zero zero (var {n = 1} x0)))
  soundness-ℕ-only-target-not-counterexample₂ {s} ok =
      _
    , J 𝟘 𝟘 ℕ zero
        (Id ℕ
            (J 𝟘 𝟘 (Erased zeroᵘ ℕ) Er.[ zero ] ℕ zero Er.[ var x1 ]
               ([]-cong s zeroᵘ ℕ zero (var x1) (var x0)))
            zero)
        rfl zero (var x0)
    , PE.subst (_⊢_∷_ _ _)
        (PE.cong (flip (Id _) _) $
         PE.cong₆ (J _ _)
           Er.Erased-[] Er.[]-[] PE.refl PE.refl Er.[]-[] PE.refl)
        (Jⱼ′
           (Idⱼ′
              (Jⱼ′ (⊢ℕ (J-motive-context ([]ⱼ Erased-ok ⊢0 ⊢zero)))
                 ⊢zero
                 ([]-congⱼ′ ok ⊢0 $
                  var₀ (J-motive-context-type (zeroⱼ ⊢Δ))))
              ⊢zero)
           (rflⱼ′
              (J 𝟘 𝟘 (Erased zeroᵘ ℕ) Er.[ zero ] ℕ zero Er.[ var x1 ]
                 ([]-cong s zeroᵘ ℕ zero (var x1) (var x0))
                 [ zero , rfl ]₁₀                                         ≡⟨ PE.cong₆ (J _ _) Er.Erased-[] Er.[]-[] PE.refl PE.refl Er.[]-[]
                                                                               PE.refl ⟩⊢≡
               J 𝟘 𝟘 (Erased zeroᵘ ℕ) Er.[ zero ] ℕ zero Er.[ zero ]
                 ([]-cong s zeroᵘ ℕ zero zero rfl)                        ≡⟨ J-cong′ (refl (Erasedⱼ Erased-ok (⊢zeroᵘ ⊢Δ) (⊢ℕ ⊢Δ)))
                                                                               (refl ⊢[zero]) (refl ⊢ℕ′)
                                                                               (refl (zeroⱼ ⊢Δ)) (refl ⊢[zero])
                                                                               ([]-cong-β-≡ (⊢zeroᵘ ⊢Δ) (refl (zeroⱼ ⊢Δ)) ok) ⟩⊢

               J 𝟘 𝟘 (Erased zeroᵘ ℕ) Er.[ zero ] ℕ zero Er.[ zero ] rfl  ≡⟨ J-β-≡ ⊢[zero] ⊢ℕ′ (zeroⱼ ⊢Δ) ⟩⊢∎

            zero                                                 ∎))
        (var₀ ⊢0≡0))
    , (λ _ → refl-⇒ˢ⟨⟩*)
    where
    open module Er = Erased s using (Erased)

    Erased-ok : Erased-allowed s
    Erased-ok = []-cong→Erased ok

    Δ′ : Con Term 1
    Δ′ = ε ∙ Id ℕ zero zero

    ⊢0≡0 : ε ⊢ Id ℕ zero zero
    ⊢0≡0 = Idⱼ′ (zeroⱼ ε) (zeroⱼ ε)

    ⊢Δ : ⊢ Δ′
    ⊢Δ = ∙ ⊢0≡0

    ⊢ℕ′ :
      Δ′ ∙ Erased zeroᵘ ℕ ∙
      Id (wk1 (Erased zeroᵘ ℕ)) (wk1 Er.[ zero ]) (var x0) ⊢
      ℕ
    ⊢ℕ′ = ⊢ℕ (J-motive-context ([]ⱼ Erased-ok (⊢zeroᵘ ⊢Δ) (zeroⱼ ⊢Δ)))

    ⊢0 : Δ′ ∙ ℕ ∙ Id ℕ zero (var x0) ⊢ zeroᵘ ∷Level
    ⊢0 = ⊢zeroᵘ (J-motive-context (zeroⱼ ⊢Δ))

    ⊢zero : Δ′ ∙ ℕ ∙ Id ℕ zero (var x0) ⊢ zero ∷ ℕ
    ⊢zero = zeroⱼ (J-motive-context (zeroⱼ ⊢Δ))

    ⊢[zero] : Δ′ ⊢ Er.[ zero ] ∷ Erased zeroᵘ ℕ
    ⊢[zero] = []ⱼ Erased-ok (⊢zeroᵘ ⊢Δ) (zeroⱼ ⊢Δ)

opaque

  soundness-ℕ-only-target-not-counterexample₃ :
    Run-time-canonicity-for
      (ε ∙ Id ℕ zero zero)
      (J 𝟘 𝟘 ℕ zero ℕ zero zero (var {n = 1} x0))
  soundness-ℕ-only-target-not-counterexample₃ =
      _
    , J 𝟘 𝟘 ℕ zero
        (Id ℕ (J 𝟘 𝟘 ℕ zero ℕ zero (var x1) (var x0)) zero)
        rfl zero (var x0)
    , Jⱼ′
        (Idⱼ′
           (Jⱼ′ (⊢ℕ (J-motive-context ⊢zero)) ⊢zero
              (var₀ (J-motive-context-type (zeroⱼ ⊢Δ))))
           ⊢zero)
        (rflⱼ′
           (J 𝟘 𝟘 ℕ zero ℕ zero zero rfl  ≡⟨ J-β-≡ (zeroⱼ ⊢Δ) ⊢ℕ′ (zeroⱼ ⊢Δ) ⟩⊢∎
            zero                          ∎))
        (var₀ ⊢0≡0)
    , (λ _ → refl-⇒ˢ⟨⟩*)
    where
    Δ′ : Con Term 1
    Δ′ = ε ∙ Id ℕ zero zero

    ⊢0≡0 : ε ⊢ Id ℕ zero zero
    ⊢0≡0 = Idⱼ′ (zeroⱼ ε) (zeroⱼ ε)

    ⊢Δ : ⊢ Δ′
    ⊢Δ = ∙ ⊢0≡0

    ⊢ℕ′ : Δ′ ∙ ℕ ∙ Id ℕ zero (var x0) ⊢ ℕ
    ⊢ℕ′ = ⊢ℕ (J-motive-context (zeroⱼ ⊢Δ))

    ⊢zero : Δ′ ∙ ℕ ∙ Id ℕ zero (var x0) ⊢ zero ∷ ℕ
    ⊢zero = zeroⱼ (J-motive-context (zeroⱼ ⊢Δ))

opaque

  soundness-ℕ-only-target-not-counterexample₄ :
    K-allowed →
    Run-time-canonicity-for
      (ε ∙ Id ℕ zero zero)
      (K 𝟘 ℕ zero ℕ zero (var {n = 1} x0))
  soundness-ℕ-only-target-not-counterexample₄ ok =
      _
    , K 𝟘 ℕ zero
        (Id ℕ (K 𝟘 ℕ zero ℕ zero (var x0)) zero)
        rfl (var x0)
    , Kⱼ
        (Idⱼ′
           (Kⱼ (⊢ℕ (K-motive-context ⊢zero)) ⊢zero
              (var₀ (K-motive-context-type (zeroⱼ ⊢Δ))) ok)
           ⊢zero)
        (rflⱼ′
           (K 𝟘 ℕ zero ℕ zero rfl  ≡⟨ K-β ⊢ℕ′ (zeroⱼ ⊢Δ) ok ⟩⊢∎
            zero                   ∎))
        (var₀ ⊢0≡0)
        ok
    , (λ _ → refl-⇒ˢ⟨⟩*)
    where
    Δ′ : Con Term 1
    Δ′ = ε ∙ Id ℕ zero zero

    ⊢0≡0 : ε ⊢ Id ℕ zero zero
    ⊢0≡0 = Idⱼ′ (zeroⱼ ε) (zeroⱼ ε)

    ⊢Δ : ⊢ Δ′
    ⊢Δ = ∙ ⊢0≡0

    ⊢ℕ′ : Δ′ ∙ Id ℕ zero zero ⊢ ℕ
    ⊢ℕ′ = ⊢ℕ (K-motive-context (zeroⱼ ⊢Δ))

    ⊢zero : Δ′ ∙ Id ℕ zero zero ⊢ zero ∷ ℕ
    ⊢zero = zeroⱼ (K-motive-context (zeroⱼ ⊢Δ))

opaque

  soundness-ℕ-only-target-not-counterexample₅ :
    Unitʷ-allowed →
    Run-time-canonicity-for
      (ε ∙ Unitʷ)
      (unitrec 𝟘 𝟘 ℕ (var {n = 1} x0) zero)
  soundness-ℕ-only-target-not-counterexample₅ Unit-ok with is-𝟘? 𝟘
  … | no 𝟘≢𝟘 = ⊥-elim $ 𝟘≢𝟘 PE.refl
  … | yes _  =
      _
    , subst ω Unitʷ
        (Id ℕ (unitrec 𝟘 𝟘 ℕ (var x0) zero) zero)
        starʷ (var x0) (Unit-η 𝕨 ω (var x0)) rfl
    , ⊢subst
        (Idⱼ′
           (unitrecⱼ
              (⊢ℕ (ε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ]))
              (var₀ (⊢Unitʷ (ε ∙[ ⊢Unitʷ ])))
              (zeroⱼ (ε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ])) Unit-ok)
           (zeroⱼ (ε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ])))
        (⊢Unit-η (var₀ (⊢Unitʷ ε)))
        (rflⱼ′
           (unitrec 𝟘 𝟘 ℕ starʷ zero  ≡⟨ unitrec-β-≡ (⊢ℕ (ε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ])) (zeroⱼ (ε ∙[ ⊢Unitʷ ])) ⟩⊢∎
            zero                      ∎))
    , (λ _ → refl-⇒ˢ⟨⟩*)
    where
    ⊢Unitʷ : ⊢ Γ → Γ ⊢ Unitʷ
    ⊢Unitʷ ⊢Γ = ⊢Unit ⊢Γ Unit-ok

-- A variant of run-time canonicity that uses erase′ true instead of
-- erase and a given strictness.

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
