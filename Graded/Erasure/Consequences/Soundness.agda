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
open import Definition.Untyped.Omega M using (Ω)
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sigma 𝕄
open import Definition.Untyped.Unit 𝕄
open import Definition.Untyped.Whnf M type-variant

open import Definition.Typed TR
open import Definition.Typed.Consequences.Consistency TR
import Definition.Typed.Consequences.Canonicity TR as TC
open import Definition.Typed.Consequences.Inequality TR
open import Definition.Typed.EqRelInstance TR
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Term TR
open import Definition.Typed.Substitution TR
open import Definition.Typed.Weakening.Definition TR
open import Definition.Typed.Well-formed TR

open import Graded.Context 𝕄
open import Graded.Derived.Erased.Usage 𝕄 UR
open import Graded.Derived.Omega UR
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
open import Graded.Erasure.Extraction.Properties 𝕄
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
import Tools.Level as TL
open import Tools.Nat using (Nat; 1+)
open import Tools.Product as Σ
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.PropositionalEquality as PE using (_≢_)
open import Tools.Sum
open import Tools.Unit
open import Tools.Vec using (ε)

private
  variable
    m n : Nat
    ∇ : DCon (Term 0) _
    Δ : Con Term _
    Γ : Cons _ _
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

  module Soundness
    (FA⁻ : Fundamental-assumptions⁻ (glassify ∇ » Δ))
    where

    private module L (str : Strictness) (⊢Δ : glassify ∇ »⊢ Δ) where

      open Graded.Erasure.LogicalRelation.Fundamental TR UR

      FA : Fundamental-assumptions (glassify ∇ » Δ)
      FA = record
        { well-formed       = ⊢Δ
        ; other-assumptions = FA⁻
        }

      as : Assumptions
      as =
        assumptions ⦃ ok = no-equality-reflection-or-empty ⦄ ⊢Δ str
          ⇒*-is-reduction-relation
        where
        open Fundamental-assumptions FA

      open Fundamental FA public
      open Graded.Erasure.LogicalRelation as public
      open Graded.Erasure.LogicalRelation.Hidden as public
      open Graded.Erasure.LogicalRelation.Irrelevance as public

    private opaque

      -- A preliminary formulation of soundness for ℕ.

      soundness-ℕ′ :
        ∀ str →
        ∇ » Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        ∃ λ n →
        glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ ×
        eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n
      soundness-ℕ′ {t} str ⊢t ▸t =                           $⟨ fundamentalErased-𝟙ᵐ ⊢t′ ▸t ⟩

        t ® erase str t ∷ ℕ                                  ⇔⟨ ®∷ℕ⇔ ⟩→

        t ® erase str t ∷ℕ                                   →⟨ soundness-ℕ″ ⟩

        (∃ λ n →
         glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ ×
         eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)  □
        where
        ⊢t′ : glassify ∇ » Δ ⊢ t ∷ ℕ
        ⊢t′ = glassify-⊢∷ ⊢t

        open L str (wfTerm ⊢t′)

        soundness-ℕ″ :
          u ® v ∷ℕ →
          ∃ λ n →
          glassify ∇ » Δ ⊢ u ⇒ˢ* sucᵏ n ∷ℕ ×
          eraseDCon str ∇ ⊢ v ⇒ˢ⟨ str ⟩* T.sucᵏ n
        soundness-ℕ″ (zeroᵣ ⇒*zero ⇒*zero′) =
          0 , whred* ⇒*zero , ⇒*→⇒ˢ⟨⟩* ⇒*zero′
        soundness-ℕ″ {v} (sucᵣ {v′} ⇒*suc ⇒*suc′ num u®v) =
          let n , d , d′ = soundness-ℕ″ u®v
          in  1+ n , ⇒ˢ*∷ℕ-trans (whred* ⇒*suc) (sucred* d) ,
              (case PE.singleton str of λ where
                 (non-strict , PE.refl) →
                   ⇒ˢ*-trans (whred*′ ⇒*suc′) (sucred*′ d′)
                 (strict , PE.refl) →
                   v              ⇒*⟨ ⇒*suc′ ⟩
                   T.suc v′       ≡˘⟨ PE.cong T.suc $ TP.Value→⇒*→≡ (TP.Numeral→Value num) d′ ⟩⇒
                   T.sucᵏ (1+ n)  ∎⇒)

    opaque

      -- Soundness of erasure for natural numbers.
      --
      -- Note the assumptions of the local module Soundness.

      soundness-ℕ :
        ∇ » Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        ∃ λ n →
        glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ ×
        (∀ str → eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)
      soundness-ℕ ⊢t ▸t =
        let n , t⇒*₁ , erase-t⇒*₁ = soundness-ℕ′ non-strict ⊢t ▸t
            _ , t⇒*₂ , erase-t⇒*₂ = soundness-ℕ′     strict ⊢t ▸t
        in
        n , t⇒*₁ , λ where
          non-strict → erase-t⇒*₁
          strict     →
            PE.subst (_⊢_⇒ˢ⟨_⟩*_ _ _ _)
              (PE.cong T.sucᵏ $ sucᵏ-PE-injectivity $
               deterministic-⊢⇒ˢ*∷ℕ t⇒*₂ t⇒*₁
                 (sucᵏ-Numeral _) (sucᵏ-Numeral _))
              erase-t⇒*₂

    -- A variant of soundness-ℕ which only considers the source
    -- language.
    --
    -- Note the assumptions of the local module Soundness.

    soundness-ℕ-only-source :
      ∇ » Δ ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
      ∃ λ n → glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
    soundness-ℕ-only-source ⊢t ▸t =
      case soundness-ℕ ⊢t ▸t of λ {
        (n , t⇒ˢ*n , _) →
          n , t⇒ˢ*n }

    private opaque

      -- A preliminary formulation of soundness for Unit.

      soundness-Unit′ :
        ∀ str →
        ∇ » Δ ⊢ t ∷ Unit s → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        glassify ∇ » Δ ⊢ t ⇒* star s ∷ Unit s ×
        eraseDCon str ∇ T.⊢ erase str t ⇒* T.star
      soundness-Unit′ {t} {s} str ⊢t ▸t =
        case ®∷Unit⇔ .proj₁ $ fundamentalErased-𝟙ᵐ ⊢t′ ▸t of λ where
          (starᵣ t⇒*star erase-t⇒*star) →
            t⇒*star ,
            erase-t⇒*star
        where
        ⊢t′ : glassify ∇ » Δ ⊢ t ∷ Unit s
        ⊢t′ = glassify-⊢∷ ⊢t

        open L str (wfTerm ⊢t′)

    opaque

      -- Soundness of extraction for unit types.
      --
      -- Note the assumptions of the local module Soundness.

      soundness-Unit :
        ∇ » Δ ⊢ t ∷ Unit s → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        glassify ∇ » Δ ⊢ t ⇒* star s ∷ Unit s ×
        (∀ str → eraseDCon str ∇ T.⊢ erase str t ⇒* T.star)
      soundness-Unit ⊢t ▸t =
        let t⇒* , erase-t⇒*₁ = soundness-Unit′     strict ⊢t ▸t
            _   , erase-t⇒*₂ = soundness-Unit′ non-strict ⊢t ▸t
        in
        t⇒* , λ where
          strict     → erase-t⇒*₁
          non-strict → erase-t⇒*₂

  -- If the variable context is empty, then the results in Soundness
  -- hold without any further assumptions related to the variable
  -- context.

  module Soundness₀
    (▸∇ : ▸[ 𝟙ᵐ ] glassify ∇)
    where

    private
      module S »∇ = Soundness (fundamental-assumptions⁻₀ »∇ ▸∇)

    opaque

      -- Soundness of extraction for natural numbers.

      soundness-ℕ :
        ∇ » ε ⊢ t ∷ ℕ → ε ▸[ 𝟙ᵐ ] t →
        ∃ λ n →
        glassify ∇ » ε ⊢ t ⇒ˢ* sucᵏ n ∷ℕ ×
        (∀ str → eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)
      soundness-ℕ ⊢t =
        S.soundness-ℕ (glassify-» (defn-wf (wfTerm ⊢t))) ⊢t

    opaque

      -- A variant of soundness-ℕ which only considers the source
      -- language.

      soundness-ℕ-only-source :
        ∇ » ε ⊢ t ∷ ℕ → 𝟘ᶜ ▸[ 𝟙ᵐ ] t →
        ∃ λ n → glassify ∇ » ε ⊢ t ⇒ˢ* sucᵏ n ∷ℕ
      soundness-ℕ-only-source ⊢t =
        S.soundness-ℕ-only-source (glassify-» (defn-wf (wfTerm ⊢t))) ⊢t

    opaque

      -- Soundness of extraction for unit types.

      soundness-Unit :
        ∇ » ε ⊢ t ∷ Unit s → ε ▸[ 𝟙ᵐ ] t →
        glassify ∇ » ε ⊢ t ⇒* star s ∷ Unit s ×
        (∀ str → eraseDCon str ∇ T.⊢ erase str t ⇒* T.star)
      soundness-Unit ⊢t =
        S.soundness-Unit (glassify-» (defn-wf (wfTerm ⊢t))) ⊢t

opaque

  -- If Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 and Σʷ-allowed p 𝟘 hold for some p,
  -- then there is a counterexample to soundness-ℕ-only-source without
  -- the assumption "erased matches are not allowed unless the context
  -- is empty" (and without the strictness argument, the assumption
  -- that the modality's zero is well-behaved, and the assumption that
  -- No-equality-reflection holds or the variable context is empty).
  --
  -- If equality reflection is not allowed, then the counterexample
  -- also works for a variant of the statement with reduction replaced
  -- by judgemental equality.

  soundness-ℕ-only-source-counterexample₁ :
    Prodrec-allowed 𝟙ᵐ 𝟘 p 𝟘 →
    Σʷ-allowed p 𝟘 →
    let ∇ = ε
        Δ = ε ∙ (Σʷ p , 𝟘 ▷ ℕ ▹ ℕ)
        t = prodrec 𝟘 p 𝟘 ℕ (var {n = 1} x0) zero
    in
    Consistent (glassify ∇ » Δ) ×
    ∇ » Δ ⊢ t ∷ ℕ ×
    ▸[ 𝟙ᵐ ] glassify ∇ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    (¬ ∃ λ n → glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ) ×
    (⦃ ok : No-equality-reflection ⦄ →
     ¬ ∃ λ n → glassify ∇ » Δ ⊢ t ≡ sucᵏ n ∷ ℕ)
  soundness-ℕ-only-source-counterexample₁ {p = p} P-ok Σʷ-ok =
      inhabited-consistent
        (⊢ˢʷ∷-sgSubst (prodⱼ ℕ⊢ℕ (zeroⱼ εε) (zeroⱼ εε) Σʷ-ok))
    , prodrecⱼ′ (⊢ℕ (∙ ΠΣⱼ Σℕ⊢ℕ Σʷ-ok)) (var₀ ⊢Σ) (zeroⱼ (∙ Σℕ⊢ℕ))
    , (λ ())
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
    , (λ where
         (0    , whred d ⇨ˢ _) → whnfRedTerm d (ne (prodrecₙ (var _ _)))
         (1+ _ , whred d ⇨ˢ _) → whnfRedTerm d (ne (prodrecₙ (var _ _))))
    , sucᵏ≢ne {V = TL.Lift _ ⊤} ⦃ ok = possibly-nonempty ⦄
        _ (prodrecₙ (var _ _)) ∘→
      sym′ ∘→ proj₂
    where
    ℕ⊢ℕ : ε » ε ∙ ℕ ⊢ ℕ
    ℕ⊢ℕ = ⊢ℕ (∙ ⊢ℕ εε)

    ⊢Σ : ε » ε ⊢ Σʷ p , 𝟘 ▷ ℕ ▹ ℕ
    ⊢Σ = ΠΣⱼ ℕ⊢ℕ Σʷ-ok

    Σℕ⊢ℕ : ε » ε ∙ Σʷ p , 𝟘 ▷ ℕ ▹ ℕ ∙ ℕ ⊢ ℕ
    Σℕ⊢ℕ = ⊢ℕ (∙ ⊢ℕ (∙ ⊢Σ))

opaque

  -- If []-cong-allowed and []-cong-allowed-mode 𝟙ᵐ hold, then there
  -- is a counterexample to soundness-ℕ-only-source without the
  -- assumption "erased matches are not allowed unless the context is
  -- empty" (and without the strictness argument, the assumption that
  -- the modality's zero is well-behaved, and the assumption that
  -- No-equality-reflection holds or the variable context is empty).
  --
  -- If equality reflection is not allowed, then the counterexample
  -- also works for a variant of the statement with reduction replaced
  -- by judgemental equality.

  soundness-ℕ-only-source-counterexample₂ :
    []-cong-allowed s →
    []-cong-allowed-mode s 𝟙ᵐ →
    let ∇ = ε
        Δ = ε ∙ Id ℕ zero zero
        open Erased s
        t = J 𝟘 𝟘 (Erased zeroᵘ ℕ) ([ zero ]) ℕ zero ([ zero ])
              ([]-cong s zeroᵘ ℕ zero zero (var {n = 1} x0))
    in
    Consistent (glassify ∇ » Δ) ×
    ∇ » Δ ⊢ t ∷ ℕ ×
    ▸[ 𝟙ᵐ ] glassify ∇ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    (¬ ∃ λ n → glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ) ×
    (⦃ ok : No-equality-reflection ⦄ →
     ¬ ∃ λ n → glassify ∇ » Δ ⊢ t ≡ sucᵏ n ∷ ℕ)
  soundness-ℕ-only-source-counterexample₂ {s = s} ok ok′ =
    let ⊢Id = ∙ Idⱼ′ (zeroⱼ εε) (zeroⱼ εε) in
    inhabited-consistent (⊢ˢʷ∷-sgSubst (rflⱼ (zeroⱼ εε))) ,
    Jⱼ′
      (⊢ℕ $ J-motive-context $
       []ⱼ ([]-cong→Erased ok) (⊢zeroᵘ ⊢Id) (zeroⱼ ⊢Id))
      (zeroⱼ ⊢Id) ([]-congⱼ′ ok (⊢zeroᵘ ⊢Id) (var ⊢Id here)) ,
    (λ ()) ,
    sub-≈ᶜ
      (Jₘ-generalised (▸Erased s zeroᵘₘ ℕₘ) (▸[] s zeroₘ)
         (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in
          sub ℕₘ $ begin
            𝟘ᶜ ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ                  ∎)
         zeroₘ (▸[] s zeroₘ) ([]-congₘ zeroᵘₘ ℕₘ zeroₘ zeroₘ var ok′))
      (≈ᶜ-sym ω·ᶜ+ᶜ⁵𝟘ᶜ) ,
    (λ where
       (0 , whred J⇒ ⇨ˢ _) →
         whnfRedTerm J⇒ (ne (Jₙ ([]-congₙ (var _ _))))
       (1+ _ , whred J⇒ ⇨ˢ _) →
         whnfRedTerm J⇒ (ne (Jₙ ([]-congₙ (var _ _))))) ,
    sucᵏ≢ne {V = TL.Lift _ ⊤} ⦃ ok = possibly-nonempty ⦄
      _ (Jₙ ([]-congₙ (var _ _))) ∘→
    sym′ ∘→ proj₂

opaque

  -- If erased-matches-for-J 𝟙ᵐ is equal to not-none sem, then there
  -- is a counterexample to soundness-ℕ-only-source without the
  -- assumption "erased matches are not allowed unless the context is
  -- empty" (and without the strictness argument, the assumption that
  -- the modality's zero is well-behaved, and the assumption that
  -- No-equality-reflection holds or the variable context is empty).
  --
  -- If equality reflection is not allowed, then the counterexample
  -- also works for a variant of the statement with reduction replaced
  -- by judgemental equality.

  soundness-ℕ-only-source-counterexample₃ :
    erased-matches-for-J 𝟙ᵐ PE.≡ not-none sem →
    let ∇ = ε
        Δ = ε ∙ Id ℕ zero zero
        t = J 𝟘 𝟘 ℕ zero ℕ zero zero (var {n = 1} x0)
    in
    Consistent (glassify ∇ » Δ) ×
    ∇ » Δ ⊢ t ∷ ℕ ×
    ▸[ 𝟙ᵐ ] glassify ∇ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    (¬ ∃ λ n → glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ) ×
    (⦃ ok : No-equality-reflection ⦄ →
     ¬ ∃ λ n → glassify ∇ » Δ ⊢ t ≡ sucᵏ n ∷ ℕ)
  soundness-ℕ-only-source-counterexample₃ ≡not-none =
    case ∙ Idⱼ′ (zeroⱼ εε) (zeroⱼ εε) of λ {
      ⊢Id →
      inhabited-consistent (⊢ˢʷ∷-sgSubst (rflⱼ (zeroⱼ εε)))
    , Jⱼ′ (⊢ℕ (J-motive-context (zeroⱼ ⊢Id))) (zeroⱼ ⊢Id) (var ⊢Id here)
    , (λ ())
    , sub
        (J₀ₘ₁-generalised ≡not-none PE.refl PE.refl ℕₘ zeroₘ ℕₘ zeroₘ
           zeroₘ var)
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
    , (λ where
         (0    , whred J⇒ ⇨ˢ _) → whnfRedTerm J⇒ (ne (Jₙ (var _ _)))
         (1+ _ , whred J⇒ ⇨ˢ _) → whnfRedTerm J⇒ (ne (Jₙ (var _ _))))
    , sucᵏ≢ne {V = TL.Lift _ ⊤} ⦃ ok = possibly-nonempty ⦄
        _ (Jₙ (var _ _)) ∘→
      sym′ ∘→ proj₂ }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- If the K rule is allowed and erased-matches-for-K 𝟙ᵐ is equal to
  -- not-none sem, then there is a counterexample to
  -- soundness-ℕ-only-source without the assumption "erased matches
  -- are not allowed unless the context is empty" (and without the
  -- strictness argument, the assumption that the modality's zero is
  -- well-behaved, and the assumption that No-equality-reflection
  -- holds or the variable context is empty).
  --
  -- If equality reflection is not allowed, then the counterexample
  -- also works for a variant of the statement with reduction replaced
  -- by judgemental equality.

  soundness-ℕ-only-source-counterexample₄ :
    K-allowed →
    erased-matches-for-K 𝟙ᵐ PE.≡ not-none sem →
    let ∇ = ε
        Δ = ε ∙ Id ℕ zero zero
        t = K 𝟘 ℕ zero ℕ zero (var {n = 1} x0)
    in
    Consistent (glassify ∇ » Δ) ×
    ∇ » Δ ⊢ t ∷ ℕ ×
    ▸[ 𝟙ᵐ ] glassify ∇ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    (¬ ∃ λ n → glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ) ×
    (⦃ ok : No-equality-reflection ⦄ →
     ¬ ∃ λ n → glassify ∇ » Δ ⊢ t ≡ sucᵏ n ∷ ℕ)
  soundness-ℕ-only-source-counterexample₄ K-ok ≡not-none =
    case ∙ Idⱼ′ (zeroⱼ εε) (zeroⱼ εε) of λ {
      ⊢Id →
      inhabited-consistent (⊢ˢʷ∷-sgSubst (rflⱼ (zeroⱼ εε)))
    , Kⱼ (⊢ℕ (K-motive-context (zeroⱼ ⊢Id))) (zeroⱼ ⊢Id) (var ⊢Id here)
        K-ok
    , (λ ())
    , sub
        (K₀ₘ₁-generalised ≡not-none PE.refl ℕₘ zeroₘ ℕₘ zeroₘ var)
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
    , (λ where
         (0    , whred K⇒ ⇨ˢ _) → whnfRedTerm K⇒ (ne (Kₙ (var _ _)))
         (1+ _ , whred K⇒ ⇨ˢ _) → whnfRedTerm K⇒ (ne (Kₙ (var _ _))))
    , sucᵏ≢ne {V = TL.Lift _ ⊤} ⦃ ok = possibly-nonempty ⦄
        _ (Kₙ (var _ _)) ∘→
      sym′ ∘→ proj₂ }
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

opaque

  -- If Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 and Unitʷ-allowed hold and η-equality
  -- is not allowed for weak unit types, then there is a
  -- counterexample to soundness-ℕ-only-source without the assumption
  -- "erased matches are not allowed unless the context is empty" (and
  -- without the strictness argument, the assumption that the
  -- modality's zero is well-behaved, and the assumption that
  -- No-equality-reflection holds or the variable context is empty).
  --
  -- If equality reflection is not allowed, then the counterexample
  -- also works for a variant of the statement with reduction replaced
  -- by judgemental equality.

  soundness-ℕ-only-source-counterexample₅ :
    Unitrec-allowed 𝟙ᵐ 𝟘 𝟘 →
    Unitʷ-allowed →
    ¬ Unitʷ-η →
    let ∇ = ε
        Δ = ε ∙ Unitʷ
        t = unitrec 𝟘 𝟘 ℕ (var {n = 1} x0) zero
    in
    Consistent (glassify ∇ » Δ) ×
    ∇ » Δ ⊢ t ∷ ℕ ×
    ▸[ 𝟙ᵐ ] glassify ∇ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    (¬ ∃ λ n → glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ) ×
    (⦃ ok : No-equality-reflection ⦄ →
     ¬ ∃ λ n → glassify ∇ » Δ ⊢ t ≡ sucᵏ n ∷ ℕ)
  soundness-ℕ-only-source-counterexample₅ unitrec-ok Unit-ok no-η =
    let ε⊢Unit = ⊢Unit εε Unit-ok in
      inhabited-consistent (⊢ˢʷ∷-sgSubst (starⱼ εε Unit-ok))
    , unitrecⱼ (⊢ℕ (∙ ⊢Unit (∙ ε⊢Unit) Unit-ok)) (var₀ ε⊢Unit)
        (zeroⱼ (∙ ε⊢Unit)) Unit-ok
    , (λ ())
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
           whnfRedTerm unitrec⇒ (ne (unitrecₙ no-η (var _ _)))
         (1+ _ , whred unitrec⇒ ⇨ˢ _) →
           whnfRedTerm unitrec⇒ (ne (unitrecₙ no-η (var _ _))))
    , sucᵏ≢ne {V = TL.Lift _ ⊤} ⦃ ok = possibly-nonempty ⦄
        _ (unitrecₙ no-η (var _ _)) ∘→
      sym′ ∘→ proj₂

opaque

  -- If Emptyrec-allowed 𝟙ᵐ 𝟘 holds, then there are counterexamples to
  -- both parts of the conclusion of a variant of the statement of
  -- soundness-ℕ without the following assumptions:
  --
  -- * "if erased matches are allowed for emptyrec, then the context
  --   is consistent",
  -- * "erased matches are not allowed unless the context is empty",
  -- * the assumption that the modality's zero is well-behaved, and
  -- * the assumption that No-equality-reflection holds or the
  --   variable context is empty.
  --
  -- Note that the counterexample does not make use of any erased
  -- matches (except for emptyrec).
  --
  -- If equality reflection is not allowed, then the counterexample
  -- also works for a variant of the statement with reduction (in the
  -- source language) replaced by judgemental equality.

  soundness-ℕ-counterexample₆ :
    Emptyrec-allowed 𝟙ᵐ 𝟘 →
    let ∇ = ε
        Δ = ε ∙ Empty
        t = emptyrec 𝟘 ℕ (var x0)
    in
    ∇ » Δ ⊢ t ∷ ℕ ×
    ▸[ 𝟙ᵐ ] glassify ∇ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    (¬ ∃ λ n → glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ) ×
    (¬ ∃ λ n →
       ∀ str → eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n) ×
    (∀ str →
     ¬ ∃ λ n → eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n) ×
    (⦃ ok : No-equality-reflection ⦄ →
     ¬ ∃ λ n → glassify ∇ » Δ ⊢ t ≡ sucᵏ n ∷ ℕ)
  soundness-ℕ-counterexample₆ emptyrec-ok =
      emptyrecⱼ (⊢ℕ (εε ∙[ ⊢Empty ])) (var₀ (⊢Empty εε))
    , (λ ())
    , (sub (emptyrecₘ var ℕₘ emptyrec-ok) $ begin
         𝟘ᶜ                          ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
         𝟘 ·ᶜ (𝟘ᶜ , x0 ≔ ⌜ ⌞ 𝟘 ⌟ ⌝)  ∎)
    , (λ where
         (0 , whred emptyrec⇒ ⇨ˢ _) →
           whnfRedTerm emptyrec⇒ (ne (emptyrecₙ (var _ _)))
         (1+ _ , whred emptyrec⇒ ⇨ˢ _) →
           whnfRedTerm emptyrec⇒ (ne (emptyrecₙ (var _ _))))
    , let ce = λ _ → ¬loop⇒ˢ* TP.Value-sucᵏ ∘→ proj₂ in
      ce strict ∘→ Σ.map idᶠ (_$ strict)
    , ce
    , sucᵏ≢ne {V = TL.Lift _ ⊤} ⦃ ok = possibly-nonempty ⦄
        _ (emptyrecₙ (var _ _)) ∘→
      sym′ ∘→ proj₂
    where
    open ≤ᶜ-reasoning

opaque
  unfolding Trans

  -- If opacity is allowed, then there is a counterexample to
  -- soundness-ℕ-only-source with glassify ∇ replaced by ∇ (and
  -- without the strictness argument and the assumption that the
  -- modality's zero is well-behaved).
  --
  -- The counterexample also works for a variant of the statement with
  -- reduction replaced by judgemental equality.

  soundness-ℕ-only-source-counterexample₇ :
    Opacity-allowed →
    let ∇ = Opaque[ zero ∷ ℕ ]
        Δ = ε
        t = defn 0
    in
    Consistent (∇ » Δ) ×
    Empty-con Δ ×
    ∇ » Δ ⊢ t ∷ ℕ ×
    ▸[ 𝟙ᵐ ] ∇ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    (¬ ∃ λ n → ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ) ×
    (¬ ∃ λ n → ∇ » Δ ⊢ t ≡ sucᵏ n ∷ ℕ)
  soundness-ℕ-only-source-counterexample₇ ok =
    let ∇»⊢Δ = ε ∙ᵒ⟨ ok ⟩[ zeroⱼ εε ∷ ⊢ℕ εε ] in
    inhabited-consistent (⊢ˢʷ∷-idSubst ∇»⊢Δ) ,
    ε ,
    defn ∇»⊢Δ here PE.refl ,
    (λ { (there ()) }) ,
    defn ,
    (λ where
       (0 , whred emptyrec⇒ ⇨ˢ _) →
         whnfRedTerm emptyrec⇒ (ne (defn here))
       (1+ _ , whred emptyrec⇒ ⇨ˢ _) →
         whnfRedTerm emptyrec⇒ (ne (defn here))) ,
    sucᵏ≢ne {V = TL.Lift _ ⊤}
      ⦃ ok = possibly-nonempty
               ⦃ ok = Opacity-allowed→No-equality-reflection ok ⦄ ⦄
      _ (defn here) ∘→
    sym′ ∘→ proj₂

opaque

  -- If equality reflection is allowed and Π p , q is allowed for some
  -- grade p that satisfies p ≤ 1 + p, then there is a counterexample
  -- to soundness-ℕ without the assumption "No-equality-reflection
  -- holds or the context is empty" (and without the strictness
  -- argument, the assumption that the modality's zero is
  -- well-behaved, the assumption "erased matches are not allowed
  -- unless the context is empty", and the assumption "if erased
  -- matches are allowed for emptyrec, then the context is
  -- consistent").

  soundness-ℕ-counterexample₈ :
    Equality-reflection →
    Π-allowed p q →
    p ≤ 𝟙 + p →
    let ∇ = ε
        Δ = ε ∙ Empty
        t = Ω p
    in
    ∇ » Δ ⊢ t ∷ ℕ ×
    ▸[ 𝟙ᵐ ] glassify ∇ ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    (¬ ∃ λ n → glassify ∇ » Δ ⊢ t ⇒ˢ* sucᵏ n ∷ℕ) ×
    (¬ ∃ λ n →
       ∀ str → eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n) ×
    (∀ str →
     ¬ ∃ λ n → eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n)
  soundness-ℕ-counterexample₈ {p} ok Π-ok p≤𝟙+p =
    (let ⊢E = ⊢Empty εε in
     ⊢Ω∷ ok Π-ok (var₀ ⊢E) (ℕⱼ (∙ ⊢E))) ,
    (λ ()) ,
    ▸Ω (λ _ → p≤𝟙+p) ,
    (λ (n , Ω⇒) → case ⇒ˢ*∷ℕ→⇒*⊎⇒*suc Ω⇒ of λ where
       (inj₂ (_ , Ω⇒)) → Ω-does-not-reduce-to-WHNF-⊢∷ sucₙ Ω⇒
       (inj₁ Ω⇒)       →
         Ω-does-not-reduce-to-WHNF-⊢∷
           (naturalWhnf (Numeral→Natural (sucᵏ-Numeral _))) Ω⇒) ,
    let ce = λ where
          strict (n , erase-Ω⇒) →
            erase-Ω-does-not-have-a-value TP.Value-sucᵏ erase-Ω⇒
          non-strict (n , erase-Ω⇒) →
            case ⇒ˢ*→⇒*⊎⇒*suc erase-Ω⇒ of λ where
              (inj₂ (_ , erase-Ω⇒)) →
                erase-Ω-does-not-have-a-value T.suc erase-Ω⇒
              (inj₁ erase-Ω⇒) →
                erase-Ω-does-not-have-a-value TP.Value-sucᵏ erase-Ω⇒
    in
    (λ (n , erase-Ω⇒) → ce strict (n , erase-Ω⇒ strict)) ,
    ce
    where
    lemma : ∀ m → p ≤ ⌜ m ⌝ + p
    lemma 𝟙ᵐ = p≤𝟙+p
    lemma 𝟘ᵐ = begin
      p      ≡˘⟨ +-identityˡ _ ⟩
      𝟘 + p  ∎
      where
      open Tools.Reasoning.PartialOrder ≤-poset

    open ≤ᶜ-reasoning

-- Run-time canonicity for a given term with respect to given
-- contexts. Run-time canonicity holds if there is a numeral n such
-- that
--
-- * the extracted term reduces to n (under the extracted context and
--   any strictness), and
--
-- * there is a proof showing that the term is equal to the numeral.
--
-- The proof is allowed to use an extended definition context (which
-- might contain new opaque definitions, see
-- soundness-ℕ-only-target-not-counterexample₇ below).

Run-time-canonicity-for :
  DCon (Term 0) m → Con Term n → Term n → Set a
Run-time-canonicity-for ∇ Δ t =
  ∃ λ n →
  (∀ str → eraseDCon str ∇ ⊢ erase str t ⇒ˢ⟨ str ⟩* T.sucᵏ n) ×
  ∃₃ λ u m (∇′ : DCon (Term 0) m) →
  » ∇′ ⊇ ∇ ×
  ∇′ » Δ ⊢ u ∷ Id ℕ t (sucᵏ n)

-- Above some counterexamples to variants of soundness-ℕ-only-source
-- are presented. Some of those counterexamples are (at the time of
-- writing) not counterexamples to "run-time canonicity holds for
-- well-typed, well-resourced terms of type ℕ in consistent contexts".

soundness-ℕ-only-target-not-counterexample₁ :
  Σʷ-allowed p 𝟘 →
  Run-time-canonicity-for
    ε
    (ε ∙ Σʷ p , 𝟘 ▷ ℕ ▹ ℕ)
    (prodrec 𝟘 p 𝟘 ℕ (var {n = 1} x0) zero)
soundness-ℕ-only-target-not-counterexample₁ {p} ok
  with is-𝟘? 𝟘
... | no 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 PE.refl)
... | yes _ =
    0
  , (λ _ → refl-⇒ˢ⟨⟩*)
  , subst ω ℕ² (Id ℕ pr zero) 0,0 (var x0) η rfl
  , 0 , ε , id⊇
  , ⊢subst (Idⱼ′ ⊢pr (zeroⱼ (εε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ])))
      (⊢Σʷ-η-prodʷ-fstʷ-sndʷ (var₀ (⊢ℕ² εε)))
      (rflⱼ′
         (prodrec 𝟘 p 𝟘 ℕ 0,0 zero  ≡⟨ prodrec-β-≡ (⊢ℕ (εε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ]))
                                         (fstʷⱼ (var₀ (⊢ℕ² εε))) (sndʷⱼ (var₀ (⊢ℕ² εε)))
                                         (zeroⱼ (εε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ ] ∙[ ⊢ℕ ])) ⟩⊢∎
          zero                      ∎))
  where
  ℕ² : Term n
  ℕ² = Σʷ p , 𝟘 ▷ ℕ ▹ ℕ

  Δ′ : Cons 0 1
  Δ′ = ε » ε ∙ ℕ²

  pr : Term 2
  pr = prodrec _ _ _ _ (var x0) zero

  0,0 : Term 1
  0,0 = prodʷ _ (fstʷ _ _ (var x0)) (sndʷ _ _ ℕ ℕ (var x0))

  η : Term 1
  η = Σʷ-η-prodʷ-fstʷ-sndʷ _ _ _ _ (var x0)

  ⊢ℕ² : ⊢ Γ → Γ ⊢ ℕ²
  ⊢ℕ² ⊢Γ = ΠΣⱼ (⊢ℕ (⊢Γ ∙[ ⊢ℕ ])) ok

  ⊢pr : Δ′ »∙ ℕ² ⊢ pr ∷ ℕ
  ⊢pr =
    prodrecⱼ′ (⊢ℕ (εε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ]))
      (var₀ (⊢ℕ² (εε ∙[ ⊢ℕ² ])))
      (zeroⱼ (εε ∙[ ⊢ℕ² ] ∙[ ⊢ℕ² ] ∙[ ⊢ℕ ] ∙[ ⊢ℕ ]))

opaque

  soundness-ℕ-only-target-not-counterexample₂ :
    []-cong-allowed s →
    let open Erased s in
    Run-time-canonicity-for
      ε
      (ε ∙ Id ℕ zero zero)
      (J 𝟘 𝟘 (Erased zeroᵘ ℕ) ([ zero ]) ℕ zero ([ zero ])
         ([]-cong s zeroᵘ ℕ zero zero (var {n = 1} x0)))
  soundness-ℕ-only-target-not-counterexample₂ {s} ok =
      _
    , (λ _ → refl-⇒ˢ⟨⟩*)
    , J 𝟘 𝟘 ℕ zero
        (Id ℕ
            (J 𝟘 𝟘 (Erased zeroᵘ ℕ) Er.[ zero ] ℕ zero Er.[ var x1 ]
               ([]-cong s zeroᵘ ℕ zero (var x1) (var x0)))
            zero)
        rfl zero (var x0)
    , 0 , ε , id⊇
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

               zero                                                       ∎))
           (var₀ ⊢0≡0))
    where
    open module Er = Erased s using (Erased)

    Erased-ok : Erased-allowed s
    Erased-ok = []-cong→Erased ok

    Δ′ : Cons 0 1
    Δ′ = ε » ε ∙ Id ℕ zero zero

    ⊢0≡0 : ε » ε ⊢ Id ℕ zero zero
    ⊢0≡0 = Idⱼ′ (zeroⱼ εε) (zeroⱼ εε)

    ⊢Δ : ⊢ Δ′
    ⊢Δ = ∙ ⊢0≡0

    ⊢ℕ′ :
      Δ′ »∙ Erased zeroᵘ ℕ »∙
      Id (wk1 (Erased zeroᵘ ℕ)) (wk1 Er.[ zero ]) (var x0) ⊢
      ℕ
    ⊢ℕ′ = ⊢ℕ (J-motive-context ([]ⱼ Erased-ok (⊢zeroᵘ ⊢Δ) (zeroⱼ ⊢Δ)))

    ⊢0 : Δ′ »∙ ℕ »∙ Id ℕ zero (var x0) ⊢ zeroᵘ ∷Level
    ⊢0 = ⊢zeroᵘ (J-motive-context (zeroⱼ ⊢Δ))

    ⊢zero : Δ′ »∙ ℕ »∙ Id ℕ zero (var x0) ⊢ zero ∷ ℕ
    ⊢zero = zeroⱼ (J-motive-context (zeroⱼ ⊢Δ))

    ⊢[zero] : Δ′ ⊢ Er.[ zero ] ∷ Erased zeroᵘ ℕ
    ⊢[zero] = []ⱼ Erased-ok (⊢zeroᵘ ⊢Δ) (zeroⱼ ⊢Δ)

opaque

  soundness-ℕ-only-target-not-counterexample₃ :
    Run-time-canonicity-for
      ε
      (ε ∙ Id ℕ zero zero)
      (J 𝟘 𝟘 ℕ zero ℕ zero zero (var {n = 1} x0))
  soundness-ℕ-only-target-not-counterexample₃ =
      _
    , (λ _ → refl-⇒ˢ⟨⟩*)
    , J 𝟘 𝟘 ℕ zero
        (Id ℕ (J 𝟘 𝟘 ℕ zero ℕ zero (var x1) (var x0)) zero)
        rfl zero (var x0)
    , 0 , ε , id⊇
    , Jⱼ′
        (Idⱼ′
           (Jⱼ′ (⊢ℕ (J-motive-context ⊢zero)) ⊢zero
              (var₀ (J-motive-context-type (zeroⱼ ⊢Δ))))
           ⊢zero)
        (rflⱼ′
           (J 𝟘 𝟘 ℕ zero ℕ zero zero rfl  ≡⟨ J-β-≡ (zeroⱼ ⊢Δ) ⊢ℕ′ (zeroⱼ ⊢Δ) ⟩⊢∎
            zero                          ∎))
        (var₀ ⊢0≡0)
    where
    Δ′ : Cons 0 1
    Δ′ = ε » ε ∙ Id ℕ zero zero

    ⊢0≡0 : ε » ε ⊢ Id ℕ zero zero
    ⊢0≡0 = Idⱼ′ (zeroⱼ εε) (zeroⱼ εε)

    ⊢Δ : ⊢ Δ′
    ⊢Δ = ∙ ⊢0≡0

    ⊢ℕ′ : Δ′ »∙ ℕ »∙ Id ℕ zero (var x0) ⊢ ℕ
    ⊢ℕ′ = ⊢ℕ (J-motive-context (zeroⱼ ⊢Δ))

    ⊢zero : Δ′ »∙ ℕ »∙ Id ℕ zero (var x0) ⊢ zero ∷ ℕ
    ⊢zero = zeroⱼ (J-motive-context (zeroⱼ ⊢Δ))

opaque

  soundness-ℕ-only-target-not-counterexample₄ :
    K-allowed →
    Run-time-canonicity-for
      ε
      (ε ∙ Id ℕ zero zero)
      (K 𝟘 ℕ zero ℕ zero (var {n = 1} x0))
  soundness-ℕ-only-target-not-counterexample₄ ok =
      _
    , (λ _ → refl-⇒ˢ⟨⟩*)
    , K 𝟘 ℕ zero
        (Id ℕ (K 𝟘 ℕ zero ℕ zero (var x0)) zero)
        rfl (var x0)
    , 0 , ε , id⊇
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
    where
    Δ′ : Cons 0 1
    Δ′ = ε » ε ∙ Id ℕ zero zero

    ⊢0≡0 : ε » ε ⊢ Id ℕ zero zero
    ⊢0≡0 = Idⱼ′ (zeroⱼ εε) (zeroⱼ εε)

    ⊢Δ : ⊢ Δ′
    ⊢Δ = ∙ ⊢0≡0

    ⊢ℕ′ : Δ′ »∙ Id ℕ zero zero ⊢ ℕ
    ⊢ℕ′ = ⊢ℕ (K-motive-context (zeroⱼ ⊢Δ))

    ⊢zero : Δ′ »∙ Id ℕ zero zero ⊢ zero ∷ ℕ
    ⊢zero = zeroⱼ (K-motive-context (zeroⱼ ⊢Δ))

opaque

  soundness-ℕ-only-target-not-counterexample₅ :
    Unitʷ-allowed →
    Run-time-canonicity-for
      ε
      (ε ∙ Unitʷ)
      (unitrec 𝟘 𝟘 ℕ (var {n = 1} x0) zero)
  soundness-ℕ-only-target-not-counterexample₅ Unit-ok with is-𝟘? 𝟘
  … | no 𝟘≢𝟘 = ⊥-elim $ 𝟘≢𝟘 PE.refl
  … | yes _  =
      _
    , (λ _ → refl-⇒ˢ⟨⟩*)
    , subst ω Unitʷ
        (Id ℕ (unitrec 𝟘 𝟘 ℕ (var x0) zero) zero)
        starʷ (var x0) (Unit-η 𝕨 ω (var x0)) rfl
    , 0 , ε , id⊇
    , ⊢subst
        (Idⱼ′
           (unitrecⱼ
              (⊢ℕ (εε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ]))
              (var₀ (⊢Unitʷ (εε ∙[ ⊢Unitʷ ])))
              (zeroⱼ (εε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ])) Unit-ok)
           (zeroⱼ (εε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ])))
        (⊢Unit-η (var₀ (⊢Unitʷ εε)))
        (rflⱼ′
           (unitrec 𝟘 𝟘 ℕ starʷ zero  ≡⟨ unitrec-β-≡ (⊢ℕ (εε ∙[ ⊢Unitʷ ] ∙[ ⊢Unitʷ ])) (zeroⱼ (εε ∙[ ⊢Unitʷ ])) ⟩⊢∎
            zero                      ∎))
    where
    ⊢Unitʷ : ⊢ Γ → Γ ⊢ Unitʷ
    ⊢Unitʷ ⊢Γ = ⊢Unit ⊢Γ Unit-ok

opaque
  unfolding Trans eraseDCon′

  soundness-ℕ-only-target-not-counterexample₇ :
    Opacity-allowed →
    Run-time-canonicity-for
      Opaque[ zero ∷ ℕ ]
      ε
      (defn 0)
  soundness-ℕ-only-target-not-counterexample₇ ok =
    let ∇»⊢ε = ε ∙ᵒ⟨ ok ⟩[ zeroⱼ εε ∷ ⊢ℕ εε ]
        ⊢Id  = Idⱼ′ (defn ∇»⊢ε here PE.refl) (zeroⱼ ∇»⊢ε)
        ⊢rfl = rflⱼ′ $ δ-red (glassify-⊢′ ∇»⊢ε) here PE.refl PE.refl
    in
    0 ,
    (λ _ → ⇒*→⇒ˢ⟨⟩* (T.trans (T.δ-red T.here) T.refl)) ,
    defn 1 ,
    2 ,
    Opaque[ zero ∷ ℕ ] ∙⟨ opa (ε ¹) ⟩[ rfl ∷ Id ℕ (defn 0) zero ] ,
    stepᵒ₁ ok ⊢Id ⊢rfl ,
    defn (ε ∙ᵒ⟨ ok ⟩[ ⊢rfl ∷ ⊢Id ]) here PE.refl

-- A variant of run-time canonicity that uses erase′ true instead of
-- erase (and eraseDCon′ true instead of eraseDCon), and a given
-- strictness.

Run-time-canonicity-with-arguments-removed-for :
  Strictness → DCon (Term 0) m → Con Term n → Term n → Set a
Run-time-canonicity-with-arguments-removed-for str ∇ Δ t =
  ∃ λ n →
  eraseDCon′ true str ∇ ⊢ erase′ true str t ⇒ˢ⟨ str ⟩* T.sucᵏ n ×
  ∃₃ λ u m (∇′ : DCon (Term 0) m) →
  » ∇′ ⊇ ∇ ×
  ∇′ » Δ ⊢ u ∷ Id ℕ t (sucᵏ n)

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
    ¬ ((t : Term 0) → ε » ε ⊢ t ∷ ℕ → ε ▸[ 𝟙ᵐ ] t →
       Run-time-canonicity-with-arguments-removed-for strict ε ε t)
  no-run-time-canonicity-if-strict-and-arguments-removed
    emptyrec-ok 𝟘-ok ω-ok ω+ω-ok q≤𝟘 hyp =
    case hyp (loops _) (⊢loops 𝟘-ok ω-ok ω+ω-ok εε)
           (▸loops emptyrec-ok q≤𝟘) of λ
      (_ , ⇒*n , _) →
    loops-does-not-reduce-to-a-value TP.Value-sucᵏ ⇒*n
