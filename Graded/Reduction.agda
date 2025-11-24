------------------------------------------------------------------------
-- Properties related to the usage relation and reduction.
-- Notably, subject reduction.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Reduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR
open Usage-restrictions UR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Substitution.Properties 𝕄 UR
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Usage.Restrictions.Instance UR
open import Graded.Usage.Restrictions.Satisfied 𝕄 UR
open import Graded.Mode 𝕄
open import Definition.Typed TR
open import Definition.Typed.Eta-long-normal-form TR
open import Definition.Typed.Properties TR
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Normal-form M type-variant

open import Tools.Bool using (T; true; false)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private
  variable
    n : Nat
    Γ : Con Term n
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
    ¬ (∀ {n} {Γ : Con Term n} {γ m t u A} →
       γ ▸[ m ] t → Γ ⊢ t ⇒ u ∷ A → γ ▸[ m ] u)
  no-subject-reduction η ok unitrec-ok 𝟙≰𝟘 subject-reduction =
    ¬▸u′ (subject-reduction ▸t′ t′⇒u′)
    where
    open ≤ᶜ-reasoning

    Γ′ : Con Term 1
    Γ′ = ε ∙ Unitʷ

    γ′ : Conₘ 1
    γ′ = ε ∙ 𝟙

    A′ t′ u′ : Term 1
    A′ = ℕ
    t′ = unitrec 𝟙 𝟘 ℕ (var x0) zero
    u′ = zero

    ⊢Γ′ : ⊢ Γ′
    ⊢Γ′ = ∙ ⊢Unit ε ok

    t′⇒u′ : Γ′ ⊢ t′ ⇒ u′ ∷ A′
    t′⇒u′ =
      unitrec-β-η (⊢ℕ (∙ ⊢Unit ⊢Γ′ ok)) (var₀ (⊢Unit ε ok))
        (zeroⱼ ⊢Γ′) ok η

    ▸t′ : γ′ ▸[ 𝟙ᵐ ] t′
    ▸t′ = sub
      (unitrecₘ
         (sub ℕₘ $ begin
            𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
            𝟘ᶜ                ∎)
         var zeroₘ
         unitrec-ok)
      (begin
         ε ∙ 𝟙                  ≈˘⟨ ε ∙ ·⌜⌞⌟⌝ ⟩
         ε ∙ 𝟙 · ⌜ ⌞ 𝟙 ⌟ ⌝      ≈˘⟨ ε ∙ +-identityʳ _ ⟩
         ε ∙ 𝟙 · ⌜ ⌞ 𝟙 ⌟ ⌝ + 𝟘  ∎)

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
-- Unitrec-allowed 𝟙ᵐ p q holds for some p and q, then p ≤ 𝟘.
--
-- Maybe things could be changed so that, if Unitʷ-η holds, then
-- η-equality for weak unit types is not allowed for 𝟙ᵐ, but only
-- for 𝟘ᵐ. In that case this assumption could perhaps be removed.

module _
  (Unitʷ-η→ :
     ∀ {p q} →
     Unitʷ-η → Unitʷ-allowed → Unitrec-allowed 𝟙ᵐ p q →
     p ≤ 𝟘)
  where

  -- Term reduction preserves usage.
  --
  -- Proof by induction on the reduction relation using the inversion
  -- and substitution lemmata for the usage relation.

  usagePresTerm : γ ▸[ m ] t → Γ ⊢ t ⇒ u ∷ A → γ ▸[ m ] u
  usagePresTerm γ▸t (conv t⇒u x) = usagePresTerm γ▸t t⇒u
  usagePresTerm γ▸t (app-subst t⇒u x) =
    let invUsageApp δ▸t η▸a γ≤δ+pη = inv-usage-app γ▸t
    in  sub ((usagePresTerm δ▸t t⇒u) ∘ₘ η▸a) γ≤δ+pη
  usagePresTerm {m} γ▸λta (β-red x₁ x₂ x₃ x₄ _) =
    let invUsageApp δ▸λt η▸a γ≤δ′+pη = inv-usage-app γ▸λta
        invUsageLam δ▸t δ′≤δ = inv-usage-lam δ▸λt
    in  sub (sgSubstₘ-lemma₂ δ▸t (▸-cong (ᵐ·-cong m (PE.sym x₄)) η▸a))
            (≤ᶜ-trans γ≤δ′+pη
               (+ᶜ-monotone δ′≤δ
                  (·ᶜ-monotoneˡ (≤-reflexive (PE.sym x₄)))))
  usagePresTerm γ▸t (fst-subst x₁ t⇒u) =
    let invUsageFst m m≡ ▸t γ≤ ok = inv-usage-fst γ▸t
    in  sub (fstₘ m (usagePresTerm (▸-cong m≡ ▸t) t⇒u) (PE.sym m≡) ok)
          γ≤
  usagePresTerm γ▸t (snd-subst x₁ t⇒u) =
    let invUsageSnd ▸t γ≤ = inv-usage-snd γ▸t
    in  sub (sndₘ (usagePresTerm ▸t t⇒u)) γ≤
  usagePresTerm {γ} {m = m′} ▸t′ (Σ-β₁ {t} {p} _ _ _ PE.refl _) =
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
           in  lemma (m ᵐ· p) (▸-cong (ᵐ·-idem m) ▸t) γ≤pζ fst-ok
           where
           open Tools.Reasoning.PartialOrder ≤ᶜ-poset
           lemma : ∀ {γ δ} m → δ ▸[ m ] t
                 → γ ≤ᶜ p ·ᶜ δ
                 → (m PE.≡ 𝟙ᵐ → p ≤ 𝟙)
                 → γ ▸[ m ] t
           lemma {γ = γ} {δ} 𝟘ᵐ δ▸t γ≤pδ fst-ok =
             sub (▸-𝟘 δ▸t)
                 (begin
                   γ       ≤⟨ γ≤pδ ⟩
                   p ·ᶜ δ  ≤⟨ ·ᶜ-monotoneʳ (▸-𝟘ᵐ δ▸t) ⟩
                   p ·ᶜ 𝟘ᶜ ≈⟨ ·ᶜ-zeroʳ p ⟩
                   𝟘ᶜ ∎)
           lemma {γ = γ} {δ} 𝟙ᵐ δ▸t γ≤pδ fst-ok =
             sub δ▸t (begin
               γ      ≤⟨ γ≤pδ ⟩
               p ·ᶜ δ ≤⟨ ·ᶜ-monotoneˡ (fst-ok PE.refl) ⟩
               𝟙 ·ᶜ δ ≈⟨ ·ᶜ-identityˡ δ ⟩
               δ ∎)

  usagePresTerm {γ} ▸t′ (Σ-β₂ {p} _ _ _ PE.refl _) =
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

  usagePresTerm γ▸natrec (natrec-subst x₁ x₂ t⇒u) =
    case inv-usage-natrec γ▸natrec of λ {
      (invUsageNatrec δ▸z η▸s θ▸n φ▸A γ≤ extra) →
    case extra of λ where
      invUsageNatrecNr →
        sub (natrecₘ δ▸z η▸s (usagePresTerm θ▸n t⇒u) φ▸A) γ≤
      (invUsageNatrecNoNr χ≤γ χ≤δ χ≤η fix) →
        sub
          (natrec-no-nrₘ δ▸z η▸s (usagePresTerm θ▸n t⇒u)
             φ▸A χ≤γ χ≤δ χ≤η fix)
          γ≤
      (invUsageNatrecNoNrGLB x≤ χ≤) →
        sub (natrec-no-nr-glbₘ δ▸z η▸s (usagePresTerm θ▸n t⇒u) φ▸A x≤ χ≤) γ≤ }

  usagePresTerm {γ} ▸natrec (natrec-zero {p} {r} _ _) =
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

  usagePresTerm {γ} ▸natrec (natrec-suc {p} {r} _ _ _) =
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

  usagePresTerm γ▸prodrec (prodrec-subst x₂ x₃ x₄ _) =
    let invUsageProdrec δ▸t η▸u θ▸A ok γ≤γ′ =
          inv-usage-prodrec γ▸prodrec
    in  sub (prodrecₘ (usagePresTerm δ▸t x₄) η▸u θ▸A ok) γ≤γ′
  usagePresTerm
    {γ = γ} {m = m} γ▸prodrec
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

  usagePresTerm γ▸et (emptyrec-subst x t⇒u) =
    let invUsageEmptyrec δ▸t η▸A ok γ≤δ = inv-usage-emptyrec γ▸et
    in  sub (emptyrecₘ (usagePresTerm δ▸t t⇒u) η▸A ok) γ≤δ

  usagePresTerm γ▸ur (unitrec-subst x x₁ t⇒t′ _ _) =
    let invUsageUnitrec θ▸A δ▸t η▸u ok γ≤γ′ = inv-usage-unitrec γ▸ur
        δ▸t′ = usagePresTerm δ▸t t⇒t′
    in  sub (unitrecₘ θ▸A δ▸t′ η▸u ok) γ≤γ′


  usagePresTerm {γ = γ} γ▸ur (unitrec-β {p = p} x x₁ _ _) =
    let invUsageUnitrec {γ₃ = δ} {γ₄ = η} θ▸A δ▸t η▸u ok γ≤γ′ =
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

  usagePresTerm {γ} {m} γ▸ur (unitrec-β-η {u} {p} _ _ _ Unit-ok η-ok) =
    case inv-usage-unitrec γ▸ur of λ
      (invUsageUnitrec {γ₃ = δ} {γ₄ = η} _ _ η▸u unitrec-ok γ≤pδ+η) →
    case PE.singleton m of λ where
      (𝟘ᵐ , PE.refl) →                               $⟨ η▸u ⟩
        η ▸[ 𝟘ᵐ ] u                                  →⟨ proj₂ ∘→ ▸[𝟘ᵐ]⇔ .proj₁ ⟩
        Usage-restrictions-satisfied 𝟘ᵐ u            →⟨ ▸[𝟘ᵐ]⇔ .proj₁ γ▸ur .proj₁ ,_ ⟩
        γ ≤ᶜ 𝟘ᶜ × Usage-restrictions-satisfied 𝟘ᵐ u  →⟨ ▸[𝟘ᵐ]⇔ .proj₂ ⟩
        γ ▸[ 𝟘ᵐ ] u                                  □
      (𝟙ᵐ , PE.refl) →
        sub η▸u $ begin
          γ            ≤⟨ γ≤pδ+η ⟩
          p ·ᶜ δ +ᶜ η  ≤⟨ +ᶜ-monotoneˡ $ ·ᶜ-monotoneˡ $ Unitʷ-η→ η-ok Unit-ok unitrec-ok ⟩
          𝟘 ·ᶜ δ +ᶜ η  ≈⟨ +ᶜ-congʳ $ ·ᶜ-zeroˡ δ ⟩
          𝟘ᶜ +ᶜ η      ≈⟨ +ᶜ-identityˡ η ⟩
          η            ∎
    where
    open ≤ᶜ-reasoning

  usagePresTerm γ▸ (J-subst _ _ _ _ v⇒v′) =
    case inv-usage-J γ▸ of λ where
      (invUsageJ ok₁ ok₂ ▸A ▸t ▸B ▸u ▸t′ ▸v γ≤) → sub
        (Jₘ ok₁ ok₂ ▸A ▸t ▸B ▸u ▸t′ (usagePresTerm ▸v v⇒v′))
        γ≤
      (invUsageJ₀₁ ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸t′ ▸v γ≤) → sub
        (J₀ₘ₁ ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸t′ (usagePresTerm ▸v v⇒v′))
        γ≤
      (invUsageJ₀₂ ok ▸A ▸t ▸B ▸u ▸t′ ▸v γ≤) → sub
        (J₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸t′ (usagePresTerm ▸v v⇒v′))
        γ≤

  usagePresTerm γ▸ (K-subst _ _ v⇒v′ _) =
    case inv-usage-K γ▸ of λ where
      (invUsageK ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v γ≤) → sub
        (Kₘ ok₁ ok₂ ▸A ▸t ▸B ▸u (usagePresTerm ▸v v⇒v′))
        γ≤
      (invUsageK₀₁ ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v γ≤) → sub
        (K₀ₘ₁ ok p≡𝟘 ▸A ▸t ▸B ▸u (usagePresTerm ▸v v⇒v′))
        γ≤
      (invUsageK₀₂ ok ▸A ▸t ▸B ▸u ▸v γ≤) → sub
        (K₀ₘ₂ ok ▸A ▸t ▸B ▸u (usagePresTerm ▸v v⇒v′))
        γ≤

  usagePresTerm γ▸ ([]-cong-subst _ _ _ _ v⇒v′ _) =
    case inv-usage-[]-cong γ▸ of
      λ (invUsage-[]-cong ▸l ▸A ▸t ▸u ▸v ok γ≤) →
    sub ([]-congₘ ▸l ▸A ▸t ▸u (usagePresTerm ▸v v⇒v′) ok) γ≤

  usagePresTerm {γ} γ▸ (J-β _ _ _ _ _ _) =
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

  usagePresTerm {γ = γ} γ▸ (K-β _ _ _) =
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

  usagePresTerm γ▸ ([]-cong-β _ _ _ _ _ _) =
    case inv-usage-[]-cong γ▸ of
      λ (invUsage-[]-cong _ _ _ _ _ _ γ≤) →
    sub rflₘ γ≤

  usagePresTerm {γ = γ} γ▸ (supᵘ-substˡ t⇒t′ _) =
    case inv-usage-supᵘ γ▸ of λ (_ , _ , γ≤ , ▸t , ▸u) →
      sub (supᵘₘ (usagePresTerm ▸t t⇒t′) ▸u) γ≤
  usagePresTerm {γ = γ} γ▸ (supᵘ-substʳ _ u⇒u′) =
    case inv-usage-supᵘ γ▸ of λ (_ , _ , γ≤ , ▸t , ▸u) →
      sub (supᵘₘ ▸t (usagePresTerm ▸u u⇒u′)) γ≤
  usagePresTerm {γ = γ} γ▸ (supᵘ-zeroˡ _) =
    case inv-usage-supᵘ γ▸ of λ (δ , η , γ≤ , ▸zeroᵘ , ▸u) →
      sub ▸u (begin
        γ       ≤⟨ γ≤ ⟩
        δ +ᶜ η  ≤⟨ +ᶜ-monotoneˡ (inv-usage-zeroᵘ ▸zeroᵘ) ⟩
        𝟘ᶜ +ᶜ η ≈⟨ +ᶜ-identityˡ η ⟩
        η       ∎)
      where open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  usagePresTerm {γ = γ} γ▸ (supᵘ-zeroʳ _) =
    case inv-usage-supᵘ γ▸ of λ (δ , η , γ≤ , ▸u , ▸zeroᵘ) →
      sub ▸u (begin
        γ       ≤⟨ γ≤ ⟩
        δ +ᶜ η  ≤⟨ +ᶜ-monotoneʳ (inv-usage-zeroᵘ ▸zeroᵘ) ⟩
        δ +ᶜ 𝟘ᶜ ≈⟨ +ᶜ-identityʳ δ ⟩
        δ       ∎)
      where open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  usagePresTerm {γ = γ} γ▸ (supᵘ-sucᵘ _ _) =
    case inv-usage-supᵘ γ▸ of λ (δ , η , γ≤ , ▸t , ▸u) →
      sub (sucᵘₘ (supᵘₘ (inv-usage-sucᵘ ▸t) (inv-usage-sucᵘ ▸u))) γ≤
  usagePresTerm {γ = γ} γ▸ (lower-subst t⇒t′) =
    lowerₘ (usagePresTerm (inv-usage-lower γ▸) t⇒t′)
  usagePresTerm {γ = γ} γ▸ (Lift-β _ _) =
    inv-usage-lift (inv-usage-lower γ▸)

  -- Type reduction preserves usage.

  usagePres : γ ▸[ m ] A → Γ ⊢ A ⇒ B → γ ▸[ m ] B
  usagePres γ▸A (univ A⇒B) = usagePresTerm γ▸A A⇒B

  -- Multi-step term reduction preserves usage.

  usagePres*Term : γ ▸[ m ] t → Γ ⊢ t ⇒* u ∷ A → γ ▸[ m ] u
  usagePres*Term γ▸t (id x) = γ▸t
  usagePres*Term γ▸t (x ⇨ t⇒u) =
    usagePres*Term (usagePresTerm γ▸t x) t⇒u

  -- Multi-step type reduction preserves usage.

  usagePres* : γ ▸[ m ] A → Γ ⊢ A ⇒* B → γ ▸[ m ] B
  usagePres* γ▸A (id x) = γ▸A
  usagePres* γ▸A (x ⇨ A⇒B) = usagePres* (usagePres γ▸A x) A⇒B

------------------------------------------------------------------------
-- Some results related to η-long normal forms

-- Note that reduction does not include η-expansion (for WHNFs, see
-- no-η-expansion-Unitˢ, no-η-expansion-Σˢ and no-η-expansion-Lift in
-- Definition.Typed.Properties). In Graded.FullReduction it is proved
-- that a well-resourced term has a well-resourced η-long normal form,
-- *given certain assumptions*. Here it is proved that, given certain
-- assumptions, the type
-- Well-resourced-normal-form-without-η-long-normal-form is inhabited:
-- there is a type A and a closed term t such that t is a
-- well-resourced normal form of type A, but t does not have any
-- (closed) well-resourced η-long normal form.

Well-resourced-normal-form-without-η-long-normal-form : Set a
Well-resourced-normal-form-without-η-long-normal-form =
  ∃₂ λ A t →
    ε ⊢ t ∷ A × Nf t × ε ▸[ 𝟙ᵐ ] t ×
    ¬ ∃ λ u → ε ⊢nf u ∷ A × ε ⊢ t ≡ u ∷ A × ε ▸[ 𝟙ᵐ ] u

-- If Unit s is allowed and comes with η-equality, then variable 0 is
-- well-typed and well-resourced (with respect to the context
-- ε ∙ Unit s 0 and the usage context ε ∙ 𝟙), and is definitionally
-- equal to the η-long normal form star s 0. However, this η-long
-- normal form is well-resourced with respect to the usage context
-- ε ∙ 𝟙 if and only if either s is 𝕤 and Unitˢ can be used as a sink,
-- or 𝟙 ≤ 𝟘.

η-long-nf-for-0⇔sink⊎𝟙≤𝟘 :
  Unit-allowed s →
  Unit-with-η s →
  let Γ = ε ∙ Unit s
      γ = ε ∙ 𝟙
      A = Unit s
      t = var x0
      u = star s
  in
  Γ ⊢ t ∷ A ×
  γ ▸[ 𝟙ᵐ ] t ×
  Γ ⊢nf u ∷ A ×
  Γ ⊢ t ≡ u ∷ A ×
  (γ ▸[ 𝟙ᵐ ] u ⇔ (s PE.≡ 𝕤 × Starˢ-sink ⊎ 𝟙 ≤ 𝟘))
η-long-nf-for-0⇔sink⊎𝟙≤𝟘 {s} ok η =
    ⊢0
  , var
  , starₙ (∙ ε⊢Unit) ok
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
                 𝟙      ≤⟨ 𝟙≤𝟙p ⟩
                 𝟙 · p  ≡˘⟨ PE.cong (_·_ _) 𝟘≡p ⟩
                 𝟙 · 𝟘  ≡⟨ ·-zeroʳ _ ⟩
                 𝟘      ∎ }}
         (𝕨 , PE.refl) →
           case inv-usage-starʷ ▸* of λ {
             (_ ∙ 𝟙≤𝟘) →
           inj₂ 𝟙≤𝟘 })
  , (let open ≤ᶜ-reasoning in
     λ where
       (inj₁ (PE.refl , sink)) →
         sub (starˢₘ (⊥-elim ∘→ not-sink-and-no-sink sink)) $ begin
           ε ∙ 𝟙         ≈˘⟨ ·ᶜ-identityˡ _ ⟩
           𝟙 ·ᶜ (ε ∙ 𝟙)  ∎
       (inj₂ 𝟙≤𝟘) →
         sub starₘ $ begin
           ε ∙ 𝟙  ≤⟨ ε ∙ 𝟙≤𝟘 ⟩
           ε ∙ 𝟘  ∎)
  where
  ε⊢Unit = ⊢Unit ε ok
  ⊢0     = var₀ ε⊢Unit

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
  let A = Π 𝟙 , q ▷ Unit s ▹ Unit s
      t = lam 𝟙 (var x0)
      u = lam 𝟙 (star s)
  in
  ε ⊢ t ∷ A ×
  ε ▸[ 𝟙ᵐ ] t ×
  ε ⊢nf u ∷ A ×
  ε ⊢ t ≡ u ∷ A ×
  (ε ▸[ 𝟙ᵐ ] u ⇔ (s PE.≡ 𝕤 × Starˢ-sink ⊎ 𝟙 ≤ 𝟘))
η-long-nf-for-id⇔sink⊎𝟙≤𝟘 {s} ok₁ ok₂ ok₃ =
  case η-long-nf-for-0⇔sink⊎𝟙≤𝟘 ok₂ ok₃ of λ {
    (⊢t , ▸t , ⊢u , t≡u , ▸u⇔) →
    lamⱼ′ ok₁ ⊢t
  , lamₘ (sub ▸t $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ 𝟙 · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
            𝟘ᶜ ∙ 𝟙      ∎)
  , lamₙ ⊢u ok₁
  , lam-cong t≡u ok₁
  , (ε ▸[ 𝟙ᵐ ] lam 𝟙 star!          ⇔⟨ (λ ▸λ* → case inv-usage-lam ▸λ* of λ where
                                         (invUsageLam {δ = ε} ▸* _) → ▸*)
                                     , lamₘ
                                     ⟩
     ε ∙ 𝟙 · 𝟙 ▸[ 𝟙ᵐ ] star!        ≡⟨ PE.cong (λ p → _ ∙ p ▸[ _ ] _) (·-identityˡ _) ⟩⇔
     ε ∙ 𝟙 ▸[ 𝟙ᵐ ] star!            ⇔⟨ ▸u⇔ ⟩
     s PE.≡ 𝕤 × Starˢ-sink ⊎ 𝟙 ≤ 𝟘  □⇔) }

-- The type Well-resourced-normal-form-without-η-long-normal-form is
-- inhabited if Unit s is allowed and comes with η-equality, s is 𝕨 or
-- Unitˢ is not allowed to be used as a sink, 𝟙 is not bounded by 𝟘,
-- Π-allowed 𝟙 q holds for some q, and Level and equality reflection
-- are not allowed.

well-resourced-normal-form-without-η-long-normal-form-Unit :
  ⦃ not-ok : No-equality-reflection ⦄ →
  ¬ Level-allowed →
  ¬ 𝟙 ≤ 𝟘 →
  s PE.≡ 𝕨 ⊎ ¬ Starˢ-sink →
  Unit-allowed s →
  Unit-with-η s →
  Π-allowed 𝟙 q →
  Well-resourced-normal-form-without-η-long-normal-form
well-resourced-normal-form-without-η-long-normal-form-Unit
  {s} not-ok 𝟙≰𝟘 ok₁ ok₂ ok₃ ok₄ =
  case η-long-nf-for-id⇔sink⊎𝟙≤𝟘 ok₄ ok₂ ok₃ of λ
    (⊢t , ▸t , ⊢u , t≡u , ▸u→ , _) →
    _ , _
  , ⊢t
  , lamₙ (ne (ne (var _)))
  , ▸t
  , λ (v , ⊢v , t≡v , ▸v) →
                                     $⟨ ▸v ⟩
      ε ▸[ 𝟙ᵐ ] v                    →⟨ PE.subst (_ ▸[ _ ]_) $
                                        normal-terms-unique not-ok ⊢v ⊢u (trans (sym′ t≡v) t≡u) ⟩
      ε ▸[ 𝟙ᵐ ] lam 𝟙 star!          →⟨ ▸u→ ⟩
      s PE.≡ 𝕤 × Starˢ-sink ⊎ 𝟙 ≤ 𝟘  →⟨ (λ where
                                           (inj₂ 𝟙≤𝟘)              → 𝟙≰𝟘 𝟙≤𝟘
                                           (inj₁ (PE.refl , sink)) →
                                             case ok₁ of λ where
                                               (inj₁ ())
                                               (inj₂ ¬sink) → not-sink-and-no-sink sink ¬sink) ⟩
      ⊥                              □

-- If "Σˢ p , q" is allowed, then variable 0 is well-typed and
-- well-resourced (with respect to the usage context ε ∙ 𝟙), and is
-- definitionally equal to the η-long normal form
-- prodˢ p (fst p (var x0)) (snd p (var x0)). However, this η-long
-- normal form is well-resourced with respect to the usage context
-- ε ∙ 𝟙 if and only if either p is 𝟙, or p is 𝟘, 𝟘ᵐ is allowed, and
-- 𝟙 ≤ 𝟘.

η-long-nf-for-0⇔≡𝟙⊎≡𝟘 :
  Σˢ-allowed p q →
  let Γ = ε ∙ (Σˢ p , q ▷ ℕ ▹ ℕ)
      γ = ε ∙ 𝟙
      A = Σˢ p , q ▷ ℕ ▹ ℕ
      t = var x0
      u = prodˢ p (fst p (var x0)) (snd p (var x0))
  in
  Γ ⊢ t ∷ A ×
  γ ▸[ 𝟙ᵐ ] t ×
  Γ ⊢nf u ∷ A ×
  Γ ⊢ t ≡ u ∷ A ×
  (γ ▸[ 𝟙ᵐ ] u ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘))
η-long-nf-for-0⇔≡𝟙⊎≡𝟘 {p = p} ok =
    ⊢0
  , var
  , prodₙ (⊢ℕ ε∙Σℕℕ∙ℕ)
      (neₙ ℕₙ (neₙ (fstₙ Σℕℕ∙ℕ⊢ℕ (varₙ (∙ ⊢Σℕℕ) here))))
      (neₙ ℕₙ (neₙ (sndₙ Σℕℕ∙ℕ⊢ℕ (varₙ (∙ ⊢Σℕℕ) here))))
      ok
  , sym′ (Σ-η-prod-fst-snd ⊢0)
  , (ε ∙ 𝟙 ▸[ 𝟙ᵐ ] u′                              ⇔⟨ lemma₁ ⟩
     (𝟙 ≤ p × (⌞ p ⌟ PE.≡ 𝟙ᵐ → p ≤ 𝟙))             ⇔⟨ id⇔ ×-cong-⇔ ⌞⌟≡𝟙→⇔⊎𝟘ᵐ×≡𝟘 ⟩
     (𝟙 ≤ p × (p ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed × p PE.≡ 𝟘))   ⇔⟨ lemma₂ ⟩
     (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)  □⇔)
  where
  u′      = prodˢ p (fst p (var x0)) (snd p (var x0))
  ⊢Σℕℕ    = ΠΣⱼ (⊢ℕ (∙ ⊢ℕ ε)) ok
  ε∙Σℕℕ∙ℕ = ∙ ⊢ℕ (∙ ⊢Σℕℕ)
  Σℕℕ∙ℕ⊢ℕ = ⊢ℕ ε∙Σℕℕ∙ℕ
  ⊢0      = var₀ ⊢Σℕℕ

  lemma₁ : ε ∙ 𝟙 ▸[ 𝟙ᵐ ] u′ ⇔ (𝟙 ≤ p × (⌞ p ⌟ PE.≡ 𝟙ᵐ → p ≤ 𝟙))
  lemma₁ =
      (λ ▸1,2 →
         let open Tools.Reasoning.PartialOrder ≤-poset in
         case inv-usage-prodˢ ▸1,2 of λ {
           (invUsageProdˢ {δ = _ ∙ q₁} {η = _ ∙ q₂} ▸1 _ (_ ∙ 𝟙≤pq₁∧q₂)) →
         case inv-usage-fst ▸1 of λ {
           (invUsageFst {δ = _ ∙ q₃} _ _ ▸0 (_ ∙ q₁≤q₃) ⌞p⌟≡𝟙ᵐ→p≤𝟙) →
         case inv-usage-var ▸0 of λ {
           (_ ∙ q₃≤⌜⌞p⌟⌝) →
           (begin
              𝟙              ≤⟨ 𝟙≤pq₁∧q₂ ⟩
              p · q₁ ∧ q₂    ≤⟨ ∧-decreasingˡ _ _ ⟩
              p · q₁         ≤⟨ ·-monotoneʳ q₁≤q₃ ⟩
              p · q₃         ≤⟨ ·-monotoneʳ q₃≤⌜⌞p⌟⌝ ⟩
              p · ⌜ ⌞ p ⌟ ⌝  ≡⟨ ·⌜⌞⌟⌝ ⟩
              p              ∎)
         , ⌞p⌟≡𝟙ᵐ→p≤𝟙 }}})
    , (λ (𝟙≤p , ⌞p⌟≡𝟙→≤𝟙) →
         sub
           (prodˢₘ (fstₘ 𝟙ᵐ var PE.refl ⌞p⌟≡𝟙→≤𝟙) (sndₘ var))
           (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
              ε ∙ 𝟙                  ≤⟨ ε ∙ ∧-greatest-lower-bound 𝟙≤p ≤-refl ⟩
              ε ∙ p ∧ 𝟙              ≈˘⟨ ε ∙ ∧-congʳ ·⌜⌞⌟⌝ ⟩
              ε ∙ p · ⌜ ⌞ p ⌟ ⌝ ∧ 𝟙  ∎))

  lemma₂ :
    (𝟙 ≤ p × (p ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed × p PE.≡ 𝟘)) ⇔
    (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)
  lemma₂ =
      (λ where
         (𝟙≤p , inj₁ p≤𝟙) →
           inj₁ (≤-antisym p≤𝟙 𝟙≤p)
         (𝟙≤𝟘 , inj₂ (ok , PE.refl)) →
           inj₂ (PE.refl , ok , 𝟙≤𝟘))
    , (λ where
         (inj₁ PE.refl) →
           ≤-refl , inj₁ ≤-refl
         (inj₂ (PE.refl , ok , 𝟙≤𝟘)) →
           𝟙≤𝟘 , inj₂ (ok , PE.refl))

-- If "Π 𝟙 , r" and "Σˢ p , q" are allowed, then the identity function
-- lam 𝟙 (var x0) has type
-- Π 𝟙 , r ▷ Σˢ p , q ▷ ℕ ▹ ℕ ▹ Σˢ p , q ▷ ℕ ▹ ℕ, is well-resourced in
-- the empty context, and is definitionally equal to the η-long normal
-- form lam 𝟙 (prodˢ p (fst p (var x0)) (snd p (var x0))), however,
-- this η-long normal form is well-resourced in the empty context if
-- and only if either p is 𝟙, or p is 𝟘, 𝟘ᵐ is allowed, and 𝟙 ≤ 𝟘.

η-long-nf-for-id⇔≡𝟙⊎≡𝟘 :
  Π-allowed 𝟙 r →
  Σˢ-allowed p q →
  let A = Π 𝟙 , r ▷ Σˢ p , q ▷ ℕ ▹ ℕ ▹ Σˢ p , q ▷ ℕ ▹ ℕ
      t = lam 𝟙 (var x0)
      u = lam 𝟙 (prodˢ p (fst p (var x0)) (snd p (var x0)))
  in
  ε ⊢ t ∷ A ×
  ε ▸[ 𝟙ᵐ ] t ×
  ε ⊢nf u ∷ A ×
  ε ⊢ t ≡ u ∷ A ×
  (ε ▸[ 𝟙ᵐ ] u ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘))
η-long-nf-for-id⇔≡𝟙⊎≡𝟘 {r = r} {p = p} {q = q} ok₁ ok₂ =
  case η-long-nf-for-0⇔≡𝟙⊎≡𝟘 ok₂ of λ {
    (⊢t , ▸t , ⊢u , t≡u , ▸u⇔) →
    lamⱼ′ ok₁ ⊢t
  , lamₘ (sub ▸t
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               𝟘ᶜ ∙ 𝟙 · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
               𝟘ᶜ ∙ 𝟙      ∎))
  , lamₙ ⊢u ok₁
  , lam-cong t≡u ok₁
  , (ε ▸[ 𝟙ᵐ ] lam 𝟙 u′                            ⇔⟨ (λ ▸λ* → case inv-usage-lam ▸λ* of λ where
                                                         (invUsageLam {δ = ε} ▸* _) → ▸*)
                                                    , lamₘ
                                                    ⟩
     ε ∙ 𝟙 · 𝟙 ▸[ 𝟙ᵐ ] u′                          ≡⟨ PE.cong (λ p → _ ∙ p ▸[ _ ] _) (·-identityˡ _) ⟩⇔
     ε ∙ 𝟙 ▸[ 𝟙ᵐ ] u′                              ⇔⟨ ▸u⇔ ⟩
     (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)  □⇔) }
  where
  u′ = prodˢ p (fst p (var x0)) (snd p (var x0))

-- The type Well-resourced-normal-form-without-η-long-normal-form is
-- inhabited if Level and equality reflection are not allowed and
-- there are quantities p, q and r such that
-- * p is distinct from 𝟙,
-- * "p is 𝟘 and 𝟘ᵐ is allowed and 𝟙 ≤ 𝟘" does not hold,
-- * Σˢ-allowed p q holds, and
-- * Π-allowed 𝟙 r holds.

well-resourced-normal-form-without-η-long-normal-form-Σˢ :
  ⦃ not-ok : No-equality-reflection ⦄ →
  ¬ Level-allowed →
  p ≢ 𝟙 →
  ¬ (p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘) →
  Σˢ-allowed p q →
  Π-allowed 𝟙 r →
  Well-resourced-normal-form-without-η-long-normal-form
well-resourced-normal-form-without-η-long-normal-form-Σˢ
  {p} not-ok p≢𝟙 ¬[p≡𝟘×𝟘ᵐ×𝟙≤𝟘] ok₁ ok₂ =
  case η-long-nf-for-id⇔≡𝟙⊎≡𝟘 ok₂ ok₁ of λ {
    (⊢t , ▸t , ⊢u , t≡u , ▸u→ , _) →
    _ , _
  , ⊢t
  , lamₙ (ne (ne (var _)))
  , ▸t
  , λ (v , ⊢v , t≡v , ▸v) →                                        $⟨ ▸v ⟩
      ε ▸[ 𝟙ᵐ ] v                                                  →⟨ PE.subst (_ ▸[ _ ]_) $
                                                                      normal-terms-unique not-ok ⊢v ⊢u (trans (sym′ t≡v) t≡u) ⟩
      ε ▸[ 𝟙ᵐ ] lam 𝟙 (prodˢ p (fst p (var x0)) (snd p (var x0)))  →⟨ ▸u→ ⟩
      p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘                   →⟨ (λ { (inj₁ p≡𝟙) → p≢𝟙 p≡𝟙; (inj₂ hyp) → ¬[p≡𝟘×𝟘ᵐ×𝟙≤𝟘] hyp }) ⟩
      ⊥                                                            □ }
