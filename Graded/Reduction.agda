-----------------------------------------------------------------------
-- Properties related to the usage relation and reduction.
-- Notably, subject reduction.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Reduction
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  {𝐌 : IsMode Mode 𝕄}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Type-restrictions TR
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Context.Weakening 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Substitution.Properties UR
open import Graded.Usage UR
open import Graded.Usage.Inversion UR
open import Graded.Usage.Properties UR
open import Graded.Usage.Restrictions.Instance UR
open import Graded.Usage.Restrictions.Satisfied UR
open import Graded.Usage.Weakening UR
open import Definition.Typed TR
open import Definition.Typed.Eta-long-normal-form TR
open import Definition.Typed.Properties TR
open import Definition.Untyped M
open import Definition.Untyped.Normal-form M type-variant
open import Definition.Untyped.Whnf M type-variant

open import Tools.Bool using (T; true; false)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private
  variable
    n : Nat
    Γ : Cons _ _
    γ : Conₘ n
    t u A B : Term n
    m : Mode
    p q r : M
    s : Strength

------------------------------------------------------------------------
-- A counterexample to subject reduction

opaque

  -- If η-equality is allowed for weak unit types, weak unit types are
  -- allowed, and Unitrec-allowed 𝟙ᵐ 𝟙 𝟘 holds, then subject reduction
  -- does not hold for modalities for which 𝟙 is not bounded by 𝟘.
  -- Note that 𝟙 ≤ 𝟘 does not hold for the linear types modalities in
  -- Graded.Modality.Instances.Linearity.

  no-subject-reduction :
    Unitʷ-η →
    Unitʷ-allowed →
    Unitrec-allowed 𝟙ᵐ 𝟙 𝟘 →
    ¬ 𝟙 ≤ 𝟘 →
    ¬ (∀ {n₁ n₂} {Γ : Cons n₁ n₂} {γ m t u A} →
       ▸[ m ] Γ .defs → γ ▸[ m ] t → Γ ⊢ t ⇒ u ∷ A → γ ▸[ m ] u)
  no-subject-reduction η ok unitrec-ok 𝟙≰𝟘 subject-reduction =
    ¬▸u′ (subject-reduction (λ ()) ▸t′ t′⇒u′)
    where
    open ≤ᶜ-reasoning

    Γ′ : Con Term 1
    Γ′ = ε ∙ Unitʷ 0

    γ′ : Conₘ 1
    γ′ = ε ∙ 𝟙

    A′ t′ u′ : Term 1
    A′ = ℕ
    t′ = unitrec 0 𝟙 𝟘 ℕ (var x0) zero
    u′ = zero

    ⊢Γ′ : ε »⊢ Γ′
    ⊢Γ′ = ∙ Unitⱼ (ε ε) ok

    t′⇒u′ : ε » Γ′ ⊢ t′ ⇒ u′ ∷ A′
    t′⇒u′ =
      unitrec-β-η (ℕⱼ (∙ Unitⱼ ⊢Γ′ ok)) (var₀ (Unitⱼ (ε ε) ok))
        (zeroⱼ ⊢Γ′) ok η

    ▸t′ : γ′ ▸[ 𝟙ᵐ ] t′
    ▸t′ = sub
      (unitrecₘ var zeroₘ
         (sub ℕₘ $ begin
            𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ               ∎)
         unitrec-ok)
      (begin
         ε ∙ 𝟙                   ≈˘⟨ ε ∙ ·⌜⌞⌟⌝ ⟩
         ε ∙ 𝟙 · ⌜ ⌞ 𝟙 ⌟ ⌝       ≈˘⟨ ε ∙ ·-congˡ (⌜⌝-cong ᵐ·-identityˡ) ⟩
         ε ∙ 𝟙 · ⌜ 𝟙ᵐ ᵐ· 𝟙 ⌝     ≈˘⟨ ε ∙ +-identityʳ _ ⟩
         ε ∙ 𝟙 · ⌜ 𝟙ᵐ ᵐ· 𝟙 ⌝ + 𝟘 ∎)

    ¬▸u′ : ¬ γ′ ▸[ 𝟙ᵐ ] u′
    ¬▸u′ =
      ε ∙ 𝟙 ▸[ 𝟙ᵐ ] zero  →⟨ inv-usage-zero ⟩
      ε ∙ 𝟙 ≤ᶜ 𝟘ᶜ         →⟨ headₘ-monotone ⟩
      𝟙 ≤ 𝟘               →⟨ 𝟙≰𝟘 ⟩
      ⊥                   □

------------------------------------------------------------------------
-- Subject reduction properties for modality usage

-- These results are proved under the assumption that, if weak unit
-- types are allowed, η-equality is allowed for them, and
-- Unitrec-allowed m p q holds for some p and q, and ⌜ m ⌝ ≢ 𝟘 then
-- p ≤ 𝟘.
--
-- Maybe things could be changed so that, if Unitʷ-η holds, then
-- η-equality for weak unit types is only allowed for 𝟘ᵐ. In that
-- case this assumption could perhaps be removed.

module _
  (Unitʷ-η→ :
     ∀ {m p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed m p q → ⌜ m ⌝ PE.≢ 𝟘 →
     p ≤ 𝟘)
  where

  -- Term reduction preserves usage (for well-resourced definition
  -- contexts).
  --
  -- Proof by induction on the reduction relation using the inversion
  -- and substitution lemmata for the usage relation.

  usagePresTerm :
    ▸[ m ] Γ .defs → γ ▸[ m ] t → Γ ⊢ t ⇒ u ∷ A → γ ▸[ m ] u
  usagePresTerm ▸∇ γ▸t (conv t⇒u x) = usagePresTerm ▸∇ γ▸t t⇒u
  usagePresTerm {γ} ▸∇ γ▸defn (δ-red _ α↦t′ PE.refl PE.refl) =
    sub (wkUsage wk₀ (▸∇ α↦t′)) $ begin
      γ             ≤⟨ inv-usage-defn γ▸defn ⟩
      𝟘ᶜ            ≡˘⟨ wk-𝟘ᶜ wk₀ ⟩
      wkConₘ wk₀ ε  ∎
    where
    open ≤ᶜ-reasoning
  usagePresTerm ▸∇ γ▸t (app-subst t⇒u x) =
    let invUsageApp δ▸t η▸a γ≤δ+pη = inv-usage-app γ▸t
    in  sub ((usagePresTerm ▸∇ δ▸t t⇒u) ∘ₘ η▸a) γ≤δ+pη
  usagePresTerm {m} _ γ▸λta (β-red x₁ x₂ x₃ x₄ _) =
    let invUsageApp δ▸λt η▸a γ≤δ′+pη = inv-usage-app γ▸λta
        invUsageLam δ▸t δ′≤δ = inv-usage-lam δ▸λt
    in sub (sgSubstₘ-lemma₂ δ▸t (▸-cong (ᵐ·-congˡ (PE.sym x₄)) η▸a))
            (≤ᶜ-trans γ≤δ′+pη
               (+ᶜ-monotone δ′≤δ
                  (·ᶜ-monotoneˡ (≤-reflexive (PE.sym x₄)))))
  usagePresTerm ▸∇ γ▸t (fst-subst x₁ t⇒u) =
    let invUsageFst m m≡ ▸t γ≤ ok = inv-usage-fst γ▸t in
    sub (fstₘ m (▸-cong m≡ (usagePresTerm ▸∇ ▸t t⇒u)) (PE.sym m≡) ok) γ≤
  usagePresTerm ▸∇ γ▸t (snd-subst x₁ t⇒u) =
    let invUsageSnd ▸t γ≤ = inv-usage-snd γ▸t
    in  sub (sndₘ (usagePresTerm ▸∇ ▸t t⇒u)) γ≤
  usagePresTerm {m = m′} {γ} _ ▸t′ (Σ-β₁ {t} {p} _ _ _ PE.refl _) =
    case inv-usage-fst ▸t′ of λ where
      (invUsageFst {δ = δ} m PE.refl ▸tu γ≤δ fst-ok) →
        case inv-usage-prodˢ ▸tu of λ where
          (invUsageProdˢ {δ = ζ} {η = η} ▸t ▸u δ≤pζ∧η) →
           let γ≤pζ =
                  begin
                    γ            ≤⟨ γ≤δ ⟩
                    δ            ≤⟨ δ≤pζ∧η ⟩
                    p ·ᶜ ζ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
                    p ·ᶜ ζ       ∎
           in  ⌜⌝≡𝟘-elim {m′ = m} (λ m → γ ▸[ m ] t) (m ᵐ· p)
             (λ 𝟙≡𝟘 → sub (▸-trivial 𝟙≡𝟘 ▸t) (≈ᶜ-trivial 𝟙≡𝟘))
             (λ 𝟙ᵐ≢𝟘ᵐ mp≡𝟘ᵐ →
               let ▸t′ = ▸-cong (PE.trans (ᵐ·-congʳ mp≡𝟘ᵐ) ᵐ·-zeroˡ) ▸t
               in  sub (▸-𝟘′ 𝟙ᵐ≢𝟘ᵐ ▸t) (begin
                     γ        ≤⟨ γ≤pζ ⟩
                     p ·ᶜ ζ   ≤⟨ (·ᶜ-monotoneʳ $ ▸-𝟘ᵐ 𝟙ᵐ≢𝟘ᵐ ▸t′) ⟩
                     p ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
                     𝟘ᶜ       ∎))
             λ mp≢𝟘 → sub (▸-cong (ᵐ·-idem _) ▸t) $ begin
                        γ      ≤⟨ γ≤pζ ⟩
                        p ·ᶜ ζ ≤⟨ ·ᶜ-monotoneˡ (fst-ok mp≢𝟘) ⟩
                        𝟙 ·ᶜ ζ ≈⟨ ·ᶜ-identityˡ _ ⟩
                        ζ      ∎
           where
           open ≤ᶜ-reasoning

  usagePresTerm {γ} _ ▸t′ (Σ-β₂ {p} _ _ _ PE.refl _) =
    case inv-usage-snd ▸t′ of λ where
      (invUsageSnd {δ = δ} ▸tu γ≤δ) →
        case inv-usage-prodˢ ▸tu of λ where
          (invUsageProdˢ {δ = ζ} {η = η} ▸t ▸u δ≤pζ∧η) → sub ▸u (begin
            γ            ≤⟨ γ≤δ ⟩
            δ            ≤⟨ δ≤pζ∧η ⟩
            p ·ᶜ ζ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
            η            ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset

  usagePresTerm ▸∇ γ▸natrec (natrec-subst x₁ x₂ t⇒u) =
    case inv-usage-natrec γ▸natrec of λ {
      (invUsageNatrec δ▸z η▸s θ▸n φ▸A γ≤ extra) →
    case extra of λ where
      invUsageNatrecNr →
        sub (natrecₘ δ▸z η▸s (usagePresTerm ▸∇ θ▸n t⇒u) φ▸A) γ≤
      (invUsageNatrecNoNr χ≤γ χ≤δ χ≤η fix) →
        sub
          (natrec-no-nrₘ δ▸z η▸s (usagePresTerm ▸∇ θ▸n t⇒u)
             φ▸A χ≤γ χ≤δ χ≤η fix)
          γ≤
      (invUsageNatrecNoNrGLB x≤ χ≤) →
        sub
          (natrec-no-nr-glbₘ δ▸z η▸s (usagePresTerm ▸∇ θ▸n t⇒u) φ▸A x≤
             χ≤)
          γ≤ }

  usagePresTerm {γ} _ ▸natrec (natrec-zero {p} {r} _ _) =
    case inv-usage-natrec ▸natrec of λ {
      (invUsageNatrec {δ = δ} {η = η} {θ = θ} {χ = χ}
         ▸z _ ▸zero _ γ≤ extra) →
    case extra of λ where
      invUsageNatrecNr →
        sub ▸z $ begin
          γ              ≤⟨ γ≤ ⟩
          nrᶜ p r δ η θ  ≤⟨ nrᶜ-zero (inv-usage-zero ▸zero) ⟩
          δ              ∎
      (invUsageNatrecNoNr χ≤δ _ _ _) →
        sub ▸z $ begin
          γ  ≤⟨ γ≤ ⟩
          χ  ≤⟨ χ≤δ ⟩
          δ  ∎
      (invUsageNatrecNoNrGLB {χ = χ′} {x} x≤ χ≤) →
        sub ▸z $ begin
          γ  ≤⟨ γ≤ ⟩
          x ·ᶜ θ +ᶜ χ′   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ (inv-usage-zero ▸zero)) ⟩
          x ·ᶜ 𝟘ᶜ +ᶜ χ′  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
          𝟘ᶜ +ᶜ χ′       ≈⟨ +ᶜ-identityˡ _ ⟩
          χ′             ≤⟨ χ≤ .proj₁ 0 ⟩
          nrᵢᶜ r δ η 0   ≈⟨ nrᵢᶜ-zero ⟩
          δ              ∎}
    where
    open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

  usagePresTerm {γ} _ ▸natrec (natrec-suc {p} {r} _ _ _) =
    case inv-usage-natrec ▸natrec of λ {
      (invUsageNatrec {δ = δ} {η = η} {θ = θ} {χ = χ}
         ▸z ▸s ▸suc ▸A γ≤ extra) →
    case inv-usage-suc ▸suc of λ {
      (invUsageSuc {δ = θ′} ▸n θ≤θ′) →
    case extra of λ where
      invUsageNatrecNr →
        sub (doubleSubstₘ-lemma₃ ▸s
               (natrecₘ ▸z ▸s (sub ▸n θ≤θ′) ▸A) ▸n) $ begin
          γ                                   ≤⟨ γ≤ ⟩
          nrᶜ p r δ η θ                       ≤⟨ nrᶜ-suc ⟩
          η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ nrᶜ p r δ η θ   ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
          η +ᶜ r ·ᶜ nrᶜ p r δ η θ +ᶜ p ·ᶜ θ   ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneʳ θ≤θ′)) ⟩
          η +ᶜ r ·ᶜ nrᶜ p r δ η θ +ᶜ p ·ᶜ θ′  ∎
      (invUsageNatrecNoNr χ≤γ χ≤δ χ≤η fix) →
        sub (doubleSubstₘ-lemma₃ ▸s
               (natrec-no-nrₘ ▸z ▸s (sub ▸n θ≤θ′) ▸A χ≤γ χ≤δ χ≤η fix)
               ▸n) $ begin
          γ                       ≤⟨ γ≤ ⟩
          χ                       ≤⟨ fix ⟩
          η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ χ   ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ θ≤θ′)) ⟩
          η +ᶜ p ·ᶜ θ′ +ᶜ r ·ᶜ χ  ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
          η +ᶜ r ·ᶜ χ +ᶜ p ·ᶜ θ′  ∎
      (invUsageNatrecNoNrGLB {χ} {x} x≤ χ≤) →
        let _ , ≤p+rx = +-GLBˡ {q = p} (·-GLBˡ {q = r} x≤)
            _ , ≤η+rχ = +ᶜ-GLBᶜˡ {δ = η} (·ᶜ-GLBᶜˡ {p = r} χ≤)
            x≤p+rx = ≤p+rx x λ i → x≤ .proj₁ (1+ i)
            χ≤η+rχ = ≤η+rχ χ λ i → ≤ᶜ-trans (χ≤ .proj₁ (1+ i)) (≤ᶜ-reflexive nrᵢᶜ-suc)
        in  sub (doubleSubstₘ-lemma₃ ▸s
              (natrec-no-nr-glbₘ ▸z ▸s (sub ▸n θ≤θ′) ▸A x≤ χ≤)
              ▸n) $ begin
          γ                                         ≤⟨ γ≤ ⟩
          x ·ᶜ θ +ᶜ χ                               ≤⟨ +ᶜ-monotone (·ᶜ-monotoneˡ x≤p+rx) χ≤η+rχ ⟩
          (p + r · x) ·ᶜ θ +ᶜ (η +ᶜ r ·ᶜ χ)         ≈⟨ +ᶜ-congʳ (·ᶜ-distribʳ-+ᶜ _ _ _) ⟩
          (p ·ᶜ θ +ᶜ (r · x) ·ᶜ θ) +ᶜ (η +ᶜ r ·ᶜ χ) ≈⟨ +ᶜ-comm _ _ ⟩
          (η +ᶜ r ·ᶜ χ) +ᶜ (p ·ᶜ θ +ᶜ (r · x) ·ᶜ θ) ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
          (η +ᶜ r ·ᶜ χ) +ᶜ ((r · x) ·ᶜ θ +ᶜ p ·ᶜ θ) ≈⟨ +ᶜ-assoc _ _ _ ⟩
          η +ᶜ r ·ᶜ χ +ᶜ ((r · x) ·ᶜ θ +ᶜ p ·ᶜ θ)   ≈˘⟨ +ᶜ-congˡ (+ᶜ-assoc _ _ _) ⟩
          η +ᶜ (r ·ᶜ χ +ᶜ (r · x) ·ᶜ θ) +ᶜ p ·ᶜ θ   ≈⟨ +ᶜ-congˡ (+ᶜ-congʳ (+ᶜ-congˡ (·ᶜ-assoc _ _ _))) ⟩
          η +ᶜ (r ·ᶜ χ +ᶜ r ·ᶜ x ·ᶜ θ) +ᶜ p ·ᶜ θ    ≈˘⟨ +ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-distribˡ-+ᶜ _ _ _)) ⟩
          η +ᶜ r ·ᶜ (χ +ᶜ x ·ᶜ θ) +ᶜ p ·ᶜ θ         ≈⟨ +ᶜ-congˡ (+ᶜ-congʳ (·ᶜ-congˡ (+ᶜ-comm _ _))) ⟩
          η +ᶜ r ·ᶜ (x ·ᶜ θ +ᶜ χ) +ᶜ p ·ᶜ θ         ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneʳ θ≤θ′)) ⟩
          η +ᶜ r ·ᶜ (x ·ᶜ θ +ᶜ χ) +ᶜ p ·ᶜ θ′        ∎}}
    where
    open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

  usagePresTerm ▸∇ γ▸prodrec (prodrec-subst x₂ x₃ x₄ _) =
    let invUsageProdrec δ▸t η▸u θ▸A ok γ≤γ′ =
          inv-usage-prodrec γ▸prodrec
    in
    sub (prodrecₘ (usagePresTerm (▸-ᵐ· ∘→ ▸∇) δ▸t x₄) η▸u θ▸A ok) γ≤γ′
  usagePresTerm
    {m} {γ} _ γ▸prodrec
    (prodrec-β {p} {t} {t′} {u} {r} _ _ _ _ PE.refl _) =
    case inv-usage-prodrec γ▸prodrec of λ where
      (invUsageProdrec {δ = δ} {η = η} ▸t ▸u _ _ γ≤rδ+η) →
        case inv-usage-prodʷ ▸t of λ where
          (invUsageProdʷ {δ = δ′} {η = η′} ▸t₁ ▸t₂ δ≤pδ′+η′) → sub
            (doubleSubstₘ-lemma₂ ▸u ▸t₂ (▸-cong (ᵐ·-·-assoc m) ▸t₁))
            (begin
               γ                              ≤⟨ γ≤rδ+η ⟩
               r ·ᶜ δ +ᶜ η                    ≈⟨ +ᶜ-comm _ _ ⟩
               η +ᶜ r ·ᶜ δ                    ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ δ≤pδ′+η′) ⟩
               η +ᶜ r ·ᶜ (p ·ᶜ δ′ +ᶜ η′)      ≈⟨ +ᶜ-congˡ (·ᶜ-congˡ (+ᶜ-comm _ _)) ⟩
               η +ᶜ r ·ᶜ (η′ +ᶜ p ·ᶜ δ′)      ≈⟨ +ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ _ _ _) ⟩
               η +ᶜ r ·ᶜ η′ +ᶜ r ·ᶜ p ·ᶜ δ′   ≈˘⟨ +ᶜ-congˡ (+ᶜ-congˡ (·ᶜ-assoc _ _ _)) ⟩
               η +ᶜ r ·ᶜ η′ +ᶜ (r · p) ·ᶜ δ′  ∎)
    where
    open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

  usagePresTerm ▸∇ γ▸et (emptyrec-subst x t⇒u) =
    let invUsageEmptyrec δ▸t η▸A ok γ≤δ = inv-usage-emptyrec γ▸et
    in  sub (emptyrecₘ (usagePresTerm (▸-ᵐ· ∘→ ▸∇) δ▸t t⇒u) η▸A ok) γ≤δ

  usagePresTerm ▸∇ γ▸ur (unitrec-subst x x₁ t⇒t′ _ _) =
    let invUsageUnitrec δ▸t η▸u θ▸A ok γ≤γ′ = inv-usage-unitrec γ▸ur
        δ▸t′ = usagePresTerm (▸-ᵐ· ∘→ ▸∇) δ▸t t⇒t′
    in  sub (unitrecₘ δ▸t′ η▸u θ▸A ok) γ≤γ′


  usagePresTerm {γ} _ γ▸ur (unitrec-β {p = p} x x₁ _ _) =
    let invUsageUnitrec {δ = δ} {η = η} δ▸t η▸u θ▸A ok γ≤γ′ =
          inv-usage-unitrec γ▸ur
        δ≤𝟘 = inv-usage-starʷ δ▸t
    in  sub η▸u (begin
      γ             ≤⟨ γ≤γ′ ⟩
      p ·ᶜ δ +ᶜ η   ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneʳ δ≤𝟘) ⟩
      p ·ᶜ 𝟘ᶜ +ᶜ η  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ p) ⟩
      𝟘ᶜ +ᶜ η       ≈⟨ +ᶜ-identityˡ η ⟩
      η             ∎)
    where
    open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

  usagePresTerm
    {m} {γ} _ γ▸ur (unitrec-β-η {u} {p} _ _ _ Unit-ok η-ok) =
    case inv-usage-unitrec γ▸ur of λ
      (invUsageUnitrec {δ} {η} δ▸t η▸u _ unitrec-ok γ≤pδ+η) →
        ⌜⌝≡𝟘-elim (λ m → γ ▸[ m ] u) m
          (λ 𝟙≡𝟘 → sub η▸u (≈ᶜ-trivial 𝟙≡𝟘))
          (λ 𝟙ᵐ≢𝟘ᵐ m≡𝟘ᵐ →
                sub (▸-cong m≡𝟘ᵐ η▸u) $ begin
                  γ             ≤⟨ γ≤pδ+η ⟩
                  p ·ᶜ δ +ᶜ η   ≤⟨ +ᶜ-monotoneˡ $ ·ᶜ-monotoneʳ $
                                    ▸-𝟘ᵐ 𝟙ᵐ≢𝟘ᵐ (▸-cong (PE.trans (ᵐ·-congʳ m≡𝟘ᵐ) ᵐ·-zeroˡ) δ▸t) ⟩
                  p ·ᶜ 𝟘ᶜ +ᶜ η  ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
                  𝟘ᶜ +ᶜ η       ≈⟨ +ᶜ-identityˡ _ ⟩
                  η             ∎)
          λ m≢𝟘 →
            sub η▸u $ begin
              γ            ≤⟨ γ≤pδ+η ⟩
              p ·ᶜ δ +ᶜ η  ≤⟨ +ᶜ-monotoneˡ $ ·ᶜ-monotoneˡ $
                               Unitʷ-η→ η-ok Unit-ok unitrec-ok m≢𝟘 ⟩
              𝟘 ·ᶜ δ +ᶜ η  ≈⟨ +ᶜ-congʳ $ ·ᶜ-zeroˡ δ ⟩
              𝟘ᶜ +ᶜ η      ≈⟨ +ᶜ-identityˡ η ⟩
              η            ∎
    where
    open ≤ᶜ-reasoning

  usagePresTerm ▸∇ γ▸ (J-subst _ _ _ _ v⇒v′) =
    case inv-usage-J γ▸ of λ where
      (invUsageJ ok₁ ok₂ ▸A ▸t ▸B ▸u ▸t′ ▸v γ≤) → sub
        (Jₘ ok₁ ok₂ ▸A ▸t ▸B ▸u ▸t′ (usagePresTerm ▸∇ ▸v v⇒v′))
        γ≤
      (invUsageJ₀₁ ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸t′ ▸v γ≤) → sub
        (J₀ₘ₁ ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸t′
           (usagePresTerm (ε-▸-𝟘ᵐ ∘→ ▸∇) ▸v v⇒v′))
        γ≤
      (invUsageJ₀₂ ok ▸A ▸t ▸B ▸u ▸t′ ▸v γ≤) → sub
        (J₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸t′
           (usagePresTerm (ε-▸-𝟘ᵐ ∘→ ▸∇) ▸v v⇒v′))
        γ≤

  usagePresTerm ▸∇ γ▸ (K-subst _ _ v⇒v′ _) =
    case inv-usage-K γ▸ of λ where
      (invUsageK ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v γ≤) → sub
        (Kₘ ok₁ ok₂ ▸A ▸t ▸B ▸u (usagePresTerm ▸∇ ▸v v⇒v′))
        γ≤
      (invUsageK₀₁ ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v γ≤) → sub
        (K₀ₘ₁ ok p≡𝟘 ▸A ▸t ▸B ▸u
           (usagePresTerm (ε-▸-𝟘ᵐ ∘→ ▸∇) ▸v v⇒v′))
        γ≤
      (invUsageK₀₂ ok ▸A ▸t ▸B ▸u ▸v γ≤) → sub
        (K₀ₘ₂ ok ▸A ▸t ▸B ▸u (usagePresTerm (ε-▸-𝟘ᵐ ∘→ ▸∇) ▸v v⇒v′))
        γ≤

  usagePresTerm ▸∇ γ▸ ([]-cong-subst _ _ _ v⇒v′ _) =
    case inv-usage-[]-cong γ▸ of
      λ (invUsage-[]-cong ▸A ▸t ▸u ▸v ok γ≤) →
    sub ([]-congₘ ▸A ▸t ▸u (usagePresTerm (ε-▸-𝟘ᵐ ∘→ ▸∇) ▸v v⇒v′) ok)
      γ≤

  usagePresTerm {γ} _ γ▸ (J-β _ _ _ _ _ _) =
    case inv-usage-J γ▸ of λ where
      (invUsageJ {γ₂ = γ₂} {γ₃ = γ₃} {γ₄ = γ₄} {γ₅ = γ₅} {γ₆ = γ₆}
         _ _ _ _ _ ▸u _ _ γ≤) → sub
        ▸u
        (begin
           γ                                  ≤⟨ γ≤ ⟩
           ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)  ≤⟨ ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ $
                                                 ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ
                                                 ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
           ω ·ᶜ γ₄                            ≤⟨ ω·ᶜ-decreasing ⟩
           γ₄                                 ∎)
      (invUsageJ₀₁ {γ₃} {γ₄} _ _ _ _ _ _ ▸u _ _ γ≤) → sub
        ▸u
        (begin
           γ                ≤⟨ γ≤ ⟩
           ω ·ᶜ (γ₃ +ᶜ γ₄)  ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
           ω ·ᶜ γ₄          ≤⟨ ω·ᶜ-decreasing ⟩
           γ₄               ∎)
      (invUsageJ₀₂ _ _ _ _ ▸u _ _ γ≤) →
        sub ▸u γ≤
    where
    open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

  usagePresTerm {γ} _ γ▸ (K-β _ _ _) =
    case inv-usage-K γ▸ of λ where
      (invUsageK {γ₂ = γ₂} {γ₃ = γ₃} {γ₄ = γ₄} {γ₅ = γ₅}
         _ _ _ _ _ ▸u _ γ≤) → sub
        ▸u
        (begin
           γ                            ≤⟨ γ≤ ⟩
           ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)  ≤⟨ ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ $
                                           ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ
                                           ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
           ω ·ᶜ γ₄                      ≤⟨ ω·ᶜ-decreasing ⟩
           γ₄                           ∎)
      (invUsageK₀₁ {γ₃} {γ₄} _ _ _ _ _ ▸u _ γ≤) → sub
        ▸u
        (begin
           γ                ≤⟨ γ≤ ⟩
           ω ·ᶜ (γ₃ +ᶜ γ₄)  ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
           ω ·ᶜ γ₄          ≤⟨ ω·ᶜ-decreasing ⟩
           γ₄               ∎)
      (invUsageK₀₂ _ _ _ _ ▸u _ γ≤) →
        sub ▸u γ≤
    where
    open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

  usagePresTerm _ γ▸ ([]-cong-β _ _ _ _ _) =
    case inv-usage-[]-cong γ▸ of
      λ (invUsage-[]-cong _ _ _ _ _ γ≤) →
    sub rflₘ γ≤

  -- Type reduction preserves usage (for well-resourced definition
  -- contexts).

  usagePres : ▸[ m ] Γ .defs → γ ▸[ m ] A → Γ ⊢ A ⇒ B → γ ▸[ m ] B
  usagePres ▸∇ γ▸A (univ A⇒B) = usagePresTerm ▸∇ γ▸A A⇒B

  -- Multi-step term reduction preserves usage (for well-resourced
  -- definition contexts).

  usagePres*Term :
    ▸[ m ] Γ .defs → γ ▸[ m ] t → Γ ⊢ t ⇒* u ∷ A → γ ▸[ m ] u
  usagePres*Term _   γ▸t (id _)      = γ▸t
  usagePres*Term ▸∇ γ▸t (t⇒v ⇨ v⇒u) =
    usagePres*Term ▸∇ (usagePresTerm ▸∇ γ▸t t⇒v) v⇒u

  -- Multi-step type reduction preserves usage (for well-resourced
  -- definition contexts).

  usagePres* : ▸[ m ] Γ .defs → γ ▸[ m ] A → Γ ⊢ A ⇒* B → γ ▸[ m ] B
  usagePres* _   γ▸A (id _)      = γ▸A
  usagePres* ▸∇ γ▸A (A⇒C ⇨ C⇒B) =
    usagePres* ▸∇ (usagePres ▸∇ γ▸A A⇒C) C⇒B

------------------------------------------------------------------------
-- Some results related to η-long normal forms

-- Note that reduction does not include η-expansion (for WHNFs, see
-- no-η-expansion-Unitˢ and no-η-expansion-Σˢ in
-- Definition.Typed.Properties). In Graded.FullReduction it is proved
-- that a well-resourced term has a well-resourced η-long normal form,
-- *given certain assumptions*. Here it is proved that, given certain
-- assumptions, the type
-- Well-resourced-normal-form-without-η-long-normal-form is inhabited:
-- there is a type A and a closed term t such that t is a
-- well-resourced normal form of type A (with respect to the empty
-- definition context), but t does not have any (closed)
-- well-resourced η-long normal form.

Well-resourced-normal-form-without-η-long-normal-form : Set (a ⊔ b)
Well-resourced-normal-form-without-η-long-normal-form =
  ∃₂ λ A t →
    ε » ε ⊢ t ∷ A × Nf ε t × ε ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ u → ε » ε ⊢nf u ∷ A × ε » ε ⊢ t ≡ u ∷ A × ε ▸[ 𝟙ᵐ ] u

-- If Unit s is allowed and comes with η-equality, then variable 0 is
-- well-typed and well-resourced (with respect to the empty definition
-- context, the context ε ∙ Unit s 0, and the usage context ε ∙ 𝟙),
-- and is definitionally equal to the η-long normal form star s 0.
-- However, this η-long normal form is well-resourced with respect to
-- the usage context ε ∙ 𝟙 if and only if either s is 𝕤 and Unitˢ can
-- be used as a sink, or 𝟙 ≤ 𝟘.

η-long-nf-for-0⇔sink⊎𝟙≤𝟘 :
  Unit-allowed s →
  Unit-with-η s →
  let Γ = ε ∙ Unit s 0
      γ = ε ∙ 𝟙
      A = Unit s 0
      t = var x0
      u = star s 0
  in
  ε » Γ ⊢ t ∷ A ×
  γ ▸[ 𝟙ᵐ ] t ×
  ε » Γ ⊢nf u ∷ A ×
  ε » Γ ⊢ t ≡ u ∷ A ×
  (γ ▸[ 𝟙ᵐ ] u ⇔ (s PE.≡ 𝕤 × Starˢ-sink ⊎ 𝟙 ≤ 𝟘))
η-long-nf-for-0⇔sink⊎𝟙≤𝟘 {s} ok η =
    ⊢0
  , sub-≈ᶜ var (≈ᶜ-refl ∙ PE.sym ⌜𝟙ᵐ⌝)
  , starₙ (∙ ⊢Unit) ok
  , sym′ (Unit-η-≡ η ⊢0)
  , (λ ▸* →
       let open Tools.Reasoning.PartialOrder ≤-poset in
       case PE.singleton s of λ where
         (𝕤 , PE.refl) →
           case sink-or-no-sink of λ where
             (inj₁ sink)     → inj₁ (PE.refl , sink)
             (inj₂ not-sink) →
               case inv-usage-starˢ ▸* of λ {
                 (invUsageStarˢ {δ = _ ∙ p} (_ ∙ 𝟙≤𝟙p) 𝟘ᶜ≈) →
               case 𝟘ᶜ≈ not-sink of λ {
                 (_ ∙ 𝟘≡p) →
               inj₂ $ begin
                 𝟙          ≤⟨ 𝟙≤𝟙p ⟩
                 ⌜ 𝟙ᵐ ⌝ · p ≡⟨ ·-congʳ ⌜𝟙ᵐ⌝ ⟩
                 𝟙 · p      ≡˘⟨ PE.cong (_·_ _) 𝟘≡p ⟩
                 𝟙 · 𝟘      ≡⟨ ·-zeroʳ _ ⟩
                 𝟘          ∎ }}
         (𝕨 , PE.refl) →
           case inv-usage-starʷ ▸* of λ {
             (_ ∙ 𝟙≤𝟘) →
           inj₂ 𝟙≤𝟘 })
  , (let open ≤ᶜ-reasoning in
     λ where
       (inj₁ (PE.refl , sink)) →
         sub (starˢₘ (⊥-elim ∘→ not-sink-and-no-sink sink)) $ begin
           ε ∙ 𝟙             ≈˘⟨ ·ᶜ-identityˡ _ ⟩
           𝟙 ·ᶜ (ε ∙ 𝟙)      ≈˘⟨ ·ᶜ-congʳ ⌜𝟙ᵐ⌝ ⟩
           ⌜ 𝟙ᵐ ⌝ ·ᶜ (ε ∙ 𝟙) ∎
       (inj₂ 𝟙≤𝟘) →
         sub starₘ $ begin
           ε ∙ 𝟙  ≤⟨ ε ∙ 𝟙≤𝟘 ⟩
           ε ∙ 𝟘  ∎)
  where
  ⊢Unit = Unitⱼ (ε ε) ok
  ⊢0    = var₀ ⊢Unit

-- If "Π 𝟙 , q" is allowed, and Unit s is allowed and comes with
-- η-equality, then the identity function lam 𝟙 (var x0) has type
-- Π 𝟙 , q ▷ Unit s 0 ▹ Unit s 0, is well-resourced in the empty
-- context, and is definitionally equal to the η-long normal form
-- lam 𝟙 (star s 0), however, this η-long normal form is
-- well-resourced in the empty context if and only if either s is 𝕤
-- and Unitˢ can be used as a sink, or 𝟙 ≤ 𝟘.

η-long-nf-for-id⇔sink⊎𝟙≤𝟘 :
  Π-allowed 𝟙 q →
  Unit-allowed s →
  Unit-with-η s →
  let A = Π 𝟙 , q ▷ Unit s 0 ▹ Unit s 0
      t = lam 𝟙 (var x0)
      u = lam 𝟙 (star s 0)
  in
  ε » ε ⊢ t ∷ A ×
  ε ▸[ 𝟙ᵐ ] t ×
  ε » ε ⊢nf u ∷ A ×
  ε » ε ⊢ t ≡ u ∷ A ×
  (ε ▸[ 𝟙ᵐ ] u ⇔ (s PE.≡ 𝕤 × Starˢ-sink ⊎ 𝟙 ≤ 𝟘))
η-long-nf-for-id⇔sink⊎𝟙≤𝟘 {s} ok₁ ok₂ ok₃ =
  case η-long-nf-for-0⇔sink⊎𝟙≤𝟘 ok₂ ok₃ of λ {
    (⊢t , ▸t , ⊢u , t≡u , ▸u⇔) →
    lamⱼ′ ok₁ ⊢t
  , lamₘ (sub ▸t $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ ⌜ 𝟙ᵐ ⌝ · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
            𝟘ᶜ ∙ ⌜ 𝟙ᵐ ⌝      ≈⟨ ≈ᶜ-refl ∙ ⌜𝟙ᵐ⌝ ⟩
            𝟘ᶜ ∙ 𝟙           ∎)
  , lamₙ ⊢u ok₁
  , lam-cong t≡u ok₁
  , (ε ▸[ 𝟙ᵐ ] lam 𝟙 star!          ⇔⟨ (λ ▸λ* → case inv-usage-lam ▸λ* of λ where
                                         (invUsageLam {δ = ε} ▸* _) → ▸*)
                                     , lamₘ
                                     ⟩
     ε ∙ ⌜ 𝟙ᵐ ⌝ · 𝟙 ▸[ 𝟙ᵐ ] star!   ≡⟨ PE.cong (λ p → _ ∙ p ▸[ _ ] _) (·-identityʳ _) ⟩⇔
     ε ∙ ⌜ 𝟙ᵐ ⌝ ▸[ 𝟙ᵐ ] star!       ≡⟨ PE.cong (λ p → _ ∙ p ▸[ _ ] _) ⌜𝟙ᵐ⌝ ⟩⇔
     ε ∙ 𝟙 ▸[ 𝟙ᵐ ] star!            ⇔⟨ ▸u⇔ ⟩
     s PE.≡ 𝕤 × Starˢ-sink ⊎ 𝟙 ≤ 𝟘  □⇔) }

-- The type Well-resourced-normal-form-without-η-long-normal-form is
-- inhabited if Unit s is allowed and comes with η-equality, s is 𝕨 or
-- Unitˢ is not allowed to be used as a sink, 𝟙 is not bounded by 𝟘,
-- Π-allowed 𝟙 q holds for some q, and equality reflection is not
-- allowed.

well-resourced-normal-form-without-η-long-normal-form-Unit :
  ⦃ not-ok : No-equality-reflection ⦄ →
  ¬ 𝟙 ≤ 𝟘 →
  s PE.≡ 𝕨 ⊎ ¬ Starˢ-sink →
  Unit-allowed s →
  Unit-with-η s →
  Π-allowed 𝟙 q →
  Well-resourced-normal-form-without-η-long-normal-form
well-resourced-normal-form-without-η-long-normal-form-Unit
  {s} 𝟙≰𝟘 ok₁ ok₂ ok₃ ok₄ =
  case η-long-nf-for-id⇔sink⊎𝟙≤𝟘 ok₄ ok₂ ok₃ of λ
    (⊢t , ▸t , ⊢u , t≡u , ▸u→ , _) →
    _ , _
  , ⊢t
  , lamₙ (ne (var _))
  , ▸t
  , λ (v , ⊢v , t≡v , ▸v) →
                                     $⟨ ▸v ⟩
      ε ▸[ 𝟙ᵐ ] v                    →⟨ PE.subst (_▸[_]_ _ _) $
                                        normal-terms-unique ⊢v ⊢u (trans (sym′ t≡v) t≡u) ⟩
      ε ▸[ 𝟙ᵐ ] lam 𝟙 star!          →⟨ ▸u→ ⟩
      s PE.≡ 𝕤 × Starˢ-sink ⊎ 𝟙 ≤ 𝟘  →⟨ (λ where
                                           (inj₂ 𝟙≤𝟘)              → 𝟙≰𝟘 𝟙≤𝟘
                                           (inj₁ (PE.refl , sink)) →
                                             case ok₁ of λ where
                                               (inj₁ ())
                                               (inj₂ ¬sink) → not-sink-and-no-sink sink ¬sink) ⟩
      ⊥                              □
