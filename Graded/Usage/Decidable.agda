------------------------------------------------------------------------
-- The usage relation can be decided (given certain assumptions)
------------------------------------------------------------------------

import Graded.Modality
import Graded.Modality.Dedicated-nr
open import Graded.Usage.Restrictions
open import Tools.PropositionalEquality
open import Tools.Relation

module Graded.Usage.Decidable
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Graded.Modality.Dedicated-nr 𝕄)
  (R : Usage-restrictions M)
  (open Usage-restrictions R)
  -- Equality is assumed to be decidable for M.
  (_≟_ : Decidable (_≡_ {A = M}))
  -- The Prodrec-allowed relation is assumed to be decidable.
  (Prodrec? : ∀ r p q → Dec (Prodrec-allowed r p q))
  -- The Unitrec-allowed relation is assumed to be decidable.
  (Unitrec? : ∀ p q → Dec (Unitrec-allowed p q))
  -- A dedicated nr function is assumed to exist.
  ⦃ has-nr : Dedicated-nr ⦄
  -- The strong unit type is not allowed to be used as a sink.
  ⦃ no-sink : ¬Starˢ-sink ⦄
  where

open Modality 𝕄 hiding (has-nr)

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Modality.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Mode 𝕄
open import Definition.Untyped M

open import Tools.Bool using (T; true; false)
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

private variable
  n : Nat

private

  -- Inequality is decidable.

  _≤?_ : Decidable _≤_
  _≤?_ = ≡-decidable→≤-decidable _≟_

  -- Context inequality is decidable.

  _≤ᶜ?_ : Decidable (_≤ᶜ_ {n = n})
  _≤ᶜ?_ = ≤ᶜ-decidable _≤?_

-- A given term is either well-resourced with respect to a given mode
-- and the usage context computed by ⌈_⌉, or it is not well-resourced
-- with respect to any usage context (and the given mode).

infix 10 ⌈⌉▸[_]?_

⌈⌉▸[_]?_ : ∀ m (t : Term n) → (⌈ t ⌉ m ▸[ m ] t) ⊎ (∀ γ → ¬ γ ▸[ m ] t)
⌈⌉▸[ m ]? U       = inj₁ Uₘ

⌈⌉▸[ m ]? ℕ       = inj₁ ℕₘ

⌈⌉▸[ m ]? Unit!   = inj₁ Unitₘ

⌈⌉▸[ m ]? Empty   = inj₁ Emptyₘ

⌈⌉▸[ m ]? zero    = inj₁ zeroₘ

⌈⌉▸[ m ]? star!   = inj₁ starₘ

⌈⌉▸[ m ]? var _   = inj₁ var

⌈⌉▸[ m ]? snd _ t = case ⌈⌉▸[ m ]? t of λ where
  (inj₁ ▸t)  → inj₁ (sndₘ ▸t)
  (inj₂ ¬▸t) → inj₂ λ _ ▸snd →
    case inv-usage-snd ▸snd of λ (invUsageSnd ▸t _) →
    ¬▸t _ ▸t

⌈⌉▸[ m ]? suc t = case ⌈⌉▸[ m ]? t of λ where
  (inj₁ ▸t)  → inj₁ (sucₘ ▸t)
  (inj₂ ¬▸t) → inj₂ λ _ ▸suc →
    case inv-usage-suc ▸suc of λ (invUsageSuc ▸t _) →
    ¬▸t _ ▸t

⌈⌉▸[ m ]? emptyrec p A t = case ⌈⌉▸[ m ᵐ· p ]? t of λ where
  (inj₂ ¬▸t) → inj₂ λ _ ▸er →
    case inv-usage-emptyrec ▸er of λ (invUsageemptyrec ▸t _ _) →
    ¬▸t _ ▸t
  (inj₁ ▸t) → case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
    (inj₂ ¬▸A) → inj₂ λ _ ▸er →
      case inv-usage-emptyrec ▸er of λ (invUsageemptyrec _ ▸A _) →
      ¬▸A _ ▸A
    (inj₁ ▸A) → inj₁ (emptyrecₘ ▸t ▸A)

⌈⌉▸[ m ]? lam p t = case ⌈⌉▸[ m ]? t of λ where
    (inj₂ ¬▸t) → inj₂ λ _ ▸lam →
      case inv-usage-lam ▸lam of λ (invUsageLam ▸t _) →
      ¬▸t _ ▸t
    (inj₁ ▸t) → case ⌜ m ⌝ · p ≤? headₘ (⌈ t ⌉ m) of λ where
      (yes mp≤) → inj₁ (lamₘ (sub ▸t (begin
        tailₘ (⌈ t ⌉ m) ∙ ⌜ m ⌝ · p        ≤⟨ ≤ᶜ-refl ∙ mp≤ ⟩
        tailₘ (⌈ t ⌉ m) ∙ headₘ (⌈ t ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩
        ⌈ t ⌉ m                            ∎)))
      (no mp≰) → inj₂ λ _ ▸lam →
        case inv-usage-lam ▸lam of λ (invUsageLam ▸t′ _) →
        mp≰ (headₘ-monotone (usage-upper-bound ▸t′))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

⌈⌉▸[ m ]? t ∘⟨ p ⟩ u = case ⌈⌉▸[ m ]? t of λ where
  (inj₂ ¬▸t) → inj₂ λ _ ▸app →
    case inv-usage-app ▸app of λ (invUsageApp ▸t _ _) →
    ¬▸t _ ▸t
  (inj₁ ▸t) → case ⌈⌉▸[ m ᵐ· p ]? u of λ where
    (inj₁ ▸u)  → inj₁ (▸t ∘ₘ ▸u)
    (inj₂ ¬▸u) → inj₂ λ _ ▸app →
      case inv-usage-app ▸app of λ (invUsageApp _ ▸u _) →
      ¬▸u _ ▸u

⌈⌉▸[ m ]? fst p t =
  case p-ok m of λ where
    (no p-not-ok) → inj₂ λ _ ▸fst →
      case inv-usage-fst ▸fst of λ (invUsageFst _ _ _ _ p-ok) →
      p-not-ok p-ok
    (yes p-ok) → case m-ok m of λ where
      (no m-not-ok) → inj₂ λ _ ▸fst →
        case inv-usage-fst ▸fst of λ (invUsageFst m′ m′-ok _ _ _) →
        m-not-ok (m′ , sym m′-ok)
      (yes (m′ , m′-ok)) →
        case ⌈⌉▸[ m ]? t of λ where
          (inj₁ ▸t) → inj₁ (fstₘ m′ (▸-cong (sym m′-ok) ▸t) m′-ok p-ok)
          (inj₂ ¬▸t) → inj₂ λ _ ▸fst →
            case inv-usage-fst ▸fst of λ (invUsageFst _ _ ▸t _ _) →
            ¬▸t _ ▸t
  where
  p-ok : ∀ m → Dec (m ≡ 𝟙ᵐ → p ≤ 𝟙)
  p-ok 𝟘ᵐ = yes λ ()
  p-ok 𝟙ᵐ = case ≡-decidable→≤-decidable _≟_ p 𝟙 of λ where
    (yes p≤𝟙) → yes λ _ → p≤𝟙
    (no p≰𝟙) → no (λ p≤𝟙 → p≰𝟙 (p≤𝟙 refl))

  m-ok : ∀ m → Dec (∃ λ m′ → m′ ᵐ· p ≡ m)
  m-ok 𝟘ᵐ = yes (𝟘ᵐ , refl)
  m-ok 𝟙ᵐ = case p ≟ 𝟘 of λ where
      (no p≢𝟘)  → yes (𝟙ᵐ , ≢𝟘→⌞⌟≡𝟙ᵐ p≢𝟘)
      (yes p≡𝟘) → 𝟘ᵐ-allowed-elim
        (λ ok → no λ where
          (𝟘ᵐ , ())
          (𝟙ᵐ , ⌞p⌟≡𝟙) →
            case
              𝟘ᵐ[ ok ]  ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
              𝟘ᵐ?       ≡˘⟨ ⌞𝟘⌟≡𝟘ᵐ? ⟩
              ⌞ 𝟘 ⌟     ≡˘⟨ cong ⌞_⌟ p≡𝟘 ⟩
              ⌞ p ⌟     ≡⟨ ⌞p⌟≡𝟙 ⟩
              𝟙ᵐ        ∎
            of λ ())
        (λ not-ok →
           yes (𝟙ᵐ , Mode-propositional-without-𝟘ᵐ not-ok))
    where
    open Tools.Reasoning.PropositionalEquality

⌈⌉▸[ m ]? ΠΣ⟨ b ⟩ p , q ▷ F ▹ G = case ⌈⌉▸[ m ᵐ· p ]? F of λ where
    (inj₂ ¬▸F) → inj₂ λ _ ▸ΠΣ →
      case inv-usage-ΠΣ ▸ΠΣ of λ (invUsageΠΣ ▸F _ _) →
      ¬▸F _ ▸F
    (inj₁ ▸F) → case ⌈⌉▸[ m ]? G of λ where
      (inj₂ ¬▸G) → inj₂ λ _ ▸ΠΣ →
        case inv-usage-ΠΣ ▸ΠΣ of λ (invUsageΠΣ _ ▸G _) →
        ¬▸G _ ▸G
      (inj₁ ▸G) → case ⌜ m ⌝ · q ≤? headₘ (⌈ G ⌉ m) of λ where
        (no mq≰) → inj₂ λ _ ▸ΠΣ →
          case inv-usage-ΠΣ ▸ΠΣ of λ (invUsageΠΣ _ ▸G′ _) →
          mq≰ (headₘ-monotone (usage-upper-bound ▸G′))
        (yes mq≤) →
          let lemma = begin
                tailₘ (⌈ G ⌉ m) ∙ ⌜ m ⌝ · q        ≤⟨ ≤ᶜ-refl ∙ mq≤ ⟩
                tailₘ (⌈ G ⌉ m) ∙ headₘ (⌈ G ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩
                ⌈ G ⌉ m                            ∎
          in inj₁ (ΠΣₘ ▸F (sub ▸G lemma))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

⌈⌉▸[ m ]? prod Σᵣ p t u = case ⌈⌉▸[ m ᵐ· p ]? t of λ where
  (inj₂ ¬▸t) → inj₂ λ _ ▸prod →
    case inv-usage-prodᵣ ▸prod of λ (invUsageProdᵣ ▸t _ _) →
    ¬▸t _ ▸t
  (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
    (inj₂ ¬▸u) → inj₂ λ _ ▸prod →
      case inv-usage-prodᵣ ▸prod of λ (invUsageProdᵣ _ ▸u _) →
      ¬▸u _ ▸u
    (inj₁ ▸u) → inj₁ (prodᵣₘ ▸t ▸u)

⌈⌉▸[ m ]? prod Σₚ p t u = case ⌈⌉▸[ m ᵐ· p ]? t of λ where
  (inj₂ ¬▸t) → inj₂ λ _ ▸prod →
    case inv-usage-prodₚ ▸prod of λ (invUsageProdₚ ▸t _ _) →
    ¬▸t _ ▸t
  (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
    (inj₂ ¬▸u) → inj₂ λ _ ▸prod →
      case inv-usage-prodₚ ▸prod of λ (invUsageProdₚ _ ▸u _) →
      ¬▸u _ ▸u
    (inj₁ ▸u) → inj₁ (prodₚₘ ▸t ▸u)

⌈⌉▸[ m ]? unitrec p q A t u = case Unitrec? p q of λ where
  (no not-ok) → inj₂ λ _ ▸ur →
          case inv-usage-unitrec ▸ur of λ (invUsageUnitrec _ _ _ ok _) →
          not-ok ok
  (yes ok) → case ⌈⌉▸[ m ᵐ· p ]? t of λ where
    (inj₂ ¬▸t) → inj₂ λ _ ▸ur →
      case inv-usage-unitrec ▸ur of λ (invUsageUnitrec ▸t _ _ _ _) →
      ¬▸t _ ▸t
    (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
      (inj₂ ¬▸u) → inj₂ λ _ ▸ur →
          case inv-usage-unitrec ▸ur of λ (invUsageUnitrec _ ▸u _ _ _) →
          ¬▸u _ ▸u
      (inj₁ ▸u) → case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
        (inj₂ ¬▸A) → inj₂ λ _ ▸ur →
          case inv-usage-unitrec ▸ur of λ (invUsageUnitrec _ _ ▸A _ _) →
          ¬▸A _ ▸A
        (inj₁ ▸A) → case ⌜ 𝟘ᵐ? ⌝ · q ≤? headₘ (⌈ A ⌉ 𝟘ᵐ?) of λ where
          (no q≰) → inj₂ λ _ ▸ur →
            case inv-usage-unitrec ▸ur of λ (invUsageUnitrec _ _ ▸A _ _) →
            q≰ (headₘ-monotone (usage-upper-bound ▸A))
          (yes q≤) →
            let lemma =
                  let open Tools.Reasoning.PartialOrder ≤ᶜ-poset
                  in begin
                  tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ (⌜ 𝟘ᵐ? ⌝ · q)      ≤⟨ ≤ᶜ-refl ∙ q≤ ⟩
                  tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ headₘ (⌈ A ⌉ 𝟘ᵐ?)  ≡⟨ headₘ-tailₘ-correct _ ⟩
                  ⌈ A ⌉ 𝟘ᵐ?                              ∎
            in  inj₁ (unitrecₘ ▸t ▸u (sub ▸A lemma) ok)

⌈⌉▸[ m ]? prodrec r p q A t u = case Prodrec? r p q of λ where
  (no not-ok) → inj₂ λ _ ▸pr →
    case inv-usage-prodrec ▸pr of λ (invUsageProdrec _ _ _ ok _) →
    not-ok ok
  (yes ok) → case ⌈⌉▸[ m ᵐ· r ]? t of λ where
    (inj₂ ¬▸t) → inj₂ λ _ ▸pr →
      case inv-usage-prodrec ▸pr of λ (invUsageProdrec ▸t _ _ _ _) →
      ¬▸t _ ▸t
    (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
      (inj₂ ¬▸u) → inj₂ λ _ ▸pr →
        case inv-usage-prodrec ▸pr of λ (invUsageProdrec _ ▸u _ _ _) →
        ¬▸u _ ▸u
      (inj₁ ▸u) →
        case ⌜ m ⌝ · r · p ≤? headₘ (tailₘ (⌈ u ⌉ m)) of λ where
          (no mrp≰) → inj₂ λ _ ▸pr →
            case inv-usage-prodrec ▸pr of
              λ (invUsageProdrec _ ▸u′ _ _ _) →
            mrp≰ (headₘ-monotone
                    (tailₘ-monotone (usage-upper-bound ▸u′)))
          (yes mrp≤) → case ⌜ m ⌝ · r ≤? headₘ (⌈ u ⌉ m) of λ where
            (no mr≰) → inj₂ λ _ ▸pr →
              case inv-usage-prodrec ▸pr of
                λ (invUsageProdrec _ ▸u′ _ _ _) →
              mr≰ (headₘ-monotone (usage-upper-bound ▸u′))
            (yes mr≤) → case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
              (inj₂ ¬▸A) → inj₂ λ _ ▸nr →
                case inv-usage-prodrec ▸nr of
                  λ (invUsageProdrec _ _ ▸A _ _) →
                ¬▸A _ ▸A
              (inj₁ ▸A) →
                case ⌜ 𝟘ᵐ? ⌝ · q ≤? headₘ (⌈ A ⌉ 𝟘ᵐ?) of λ where
                  (no q≰) → inj₂ λ _ ▸nr →
                    case inv-usage-prodrec ▸nr of
                      λ (invUsageProdrec _ _ ▸A′ _ _) →
                    q≰ (headₘ-monotone (usage-upper-bound ▸A′))
                  (yes q≤) →
                    let lemma₁ =
                          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset
                          in begin
                          tailₘ (tailₘ (⌈ u ⌉ m)) ∙
                          ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r          ≤⟨ ≤ᶜ-refl ∙ mrp≤ ∙ mr≤ ⟩

                          tailₘ (tailₘ (⌈ u ⌉ m)) ∙
                          headₘ (tailₘ (⌈ u ⌉ m)) ∙
                          headₘ (⌈ u ⌉ m)                    ≡⟨ cong (_∙ headₘ (⌈ u ⌉ m)) (headₘ-tailₘ-correct _) ⟩

                          tailₘ (⌈ u ⌉ m) ∙ headₘ (⌈ u ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩

                          ⌈ u ⌉ m                            ∎

                        lemma₂ =
                          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset
                          in begin
                          tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ ⌜ 𝟘ᵐ? ⌝ · q        ≤⟨ ≤ᶜ-refl ∙ q≤ ⟩
                          tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ headₘ (⌈ A ⌉ 𝟘ᵐ?)  ≡⟨ headₘ-tailₘ-correct _ ⟩
                          ⌈ A ⌉ 𝟘ᵐ?                              ∎
                    in
                    inj₁ (prodrecₘ ▸t (sub ▸u lemma₁)
                            (sub ▸A lemma₂) ok)

⌈⌉▸[ m ]? natrec p q r A z s n = case ⌈⌉▸[ m ]? z of λ where
  (inj₂ ¬▸z) → inj₂ λ _ ▸nr →
    case inv-usage-natrec ▸nr of λ where
      (invUsageNatrec ▸z _ _ _ _ _) →
        ¬▸z _ ▸z
  (inj₁ ▸z) → case ⌈⌉▸[ m ]? s of λ where
    (inj₂ ¬▸s) → inj₂ λ _ ▸nr →
      case inv-usage-natrec ▸nr of λ where
        (invUsageNatrec _ ▸s _ _ _ _) →
          ¬▸s _ ▸s
    (inj₁ ▸s) → case ⌜ m ⌝ · p ≤? headₘ (tailₘ (⌈ s ⌉ m)) of λ where
      (no mp≰) → inj₂ λ _ ▸nr →
        case inv-usage-natrec ▸nr of λ where
          (invUsageNatrec _ ▸s′ _ _ _ _) →
            mp≰ $ headₘ-monotone $ tailₘ-monotone $
            usage-upper-bound ▸s′
      (yes mp≤) → case ⌜ m ⌝ · r ≤? headₘ (⌈ s ⌉ m) of λ where
        (no mr≰) → inj₂ λ _ ▸nr →
          case inv-usage-natrec ▸nr of λ where
            (invUsageNatrec _ ▸s′ _ _ _ _) →
              mr≰ $ headₘ-monotone $
              usage-upper-bound ▸s′
        (yes mr≤) → case ⌈⌉▸[ m ]? n of λ where
          (inj₂ ¬▸n) → inj₂ λ _ ▸nr →
            case inv-usage-natrec ▸nr of λ where
              (invUsageNatrec _ _ ▸n _ _ _) →
                ¬▸n _ ▸n
          (inj₁ ▸n) → case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
            (inj₂ ¬▸A) → inj₂ λ _ ▸nr →
              case inv-usage-natrec ▸nr of λ where
                (invUsageNatrec _ _ _ ▸A _ _) →
                  ¬▸A _ ▸A
            (inj₁ ▸A) →
              case ⌜ 𝟘ᵐ? ⌝ · q ≤? headₘ (⌈ A ⌉ 𝟘ᵐ?) of λ where
                (no q≰) → inj₂ λ _ ▸nr →
                  case inv-usage-natrec ▸nr of λ where
                    (invUsageNatrec _ _ _ ▸A′ _ _) →
                      q≰ $ headₘ-monotone $
                      usage-upper-bound ▸A′
                (yes q≤) →
                  let lemma₁ =
                        let open Tools.Reasoning.PartialOrder ≤ᶜ-poset
                        in begin
                        tailₘ (tailₘ (⌈ s ⌉ m)) ∙
                        ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r              ≤⟨ ≤ᶜ-refl ∙ mp≤ ∙ mr≤ ⟩

                        tailₘ (tailₘ (⌈ s ⌉ m)) ∙
                        headₘ (tailₘ (⌈ s ⌉ m)) ∙
                        headₘ (⌈ s ⌉ m)                    ≡⟨ cong (_∙ headₘ (⌈ s ⌉ m)) (headₘ-tailₘ-correct _) ⟩

                        tailₘ (⌈ s ⌉ m) ∙ headₘ (⌈ s ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩

                        ⌈ s ⌉ m                            ∎

                      lemma₂ =
                        let open Tools.Reasoning.PartialOrder ≤ᶜ-poset
                        in begin
                        tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ ⌜ 𝟘ᵐ? ⌝ · q        ≤⟨ ≤ᶜ-refl ∙ q≤ ⟩
                        tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ headₘ (⌈ A ⌉ 𝟘ᵐ?)  ≡⟨ headₘ-tailₘ-correct _ ⟩
                        ⌈ A ⌉ 𝟘ᵐ?                              ∎
                  in
                  inj₁ (natrecₘ ▸z (sub ▸s lemma₁) ▸n (sub ▸A lemma₂))

⌈⌉▸[ m ]? Id A t u with Id-erased?
… | yes erased =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
    (inj₂ ¬▸A) → inj₂ λ _ ▸Id →
      case inv-usage-Id ▸Id of λ where
        (invUsageId₀ _ ▸A _ _ _) → ¬▸A _ ▸A
        (invUsageId ok _ _ _ _)  → ok erased
    (inj₁ ▸A) → case ⌈⌉▸[ 𝟘ᵐ? ]? t of λ where
      (inj₂ ¬▸t) → inj₂ λ _ ▸Id →
        case inv-usage-Id ▸Id of λ where
          (invUsageId₀ _ _ ▸t _ _) → ¬▸t _ ▸t
          (invUsageId ok _ _ _ _)  → ok erased
      (inj₁ ▸t) → case ⌈⌉▸[ 𝟘ᵐ? ]? u of λ where
        (inj₂ ¬▸u) → inj₂ λ _ ▸Id →
          case inv-usage-Id ▸Id of λ where
            (invUsageId₀ _ _ _ ▸u _) → ¬▸u _ ▸u
            (invUsageId ok _ _ _ _)  → ok erased
        (inj₁ ▸u) → inj₁ (Id₀ₘ erased ▸A ▸t ▸u)
… | no not-erased =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
    (inj₂ ¬▸A) → inj₂ λ _ ▸Id →
      case inv-usage-Id ▸Id of λ where
        (invUsageId _ ▸A _ _ _)  → ¬▸A _ ▸A
        (invUsageId₀ ok _ _ _ _) → not-erased ok
    (inj₁ ▸A) → case ⌈⌉▸[ m ]? t of λ where
      (inj₂ ¬▸t) → inj₂ λ _ ▸Id →
        case inv-usage-Id ▸Id of λ where
          (invUsageId _ _ ▸t _ _)  → ¬▸t _ ▸t
          (invUsageId₀ ok _ _ _ _) → not-erased ok
      (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
        (inj₂ ¬▸u) → inj₂ λ _ ▸Id →
          case inv-usage-Id ▸Id of λ where
            (invUsageId _ _ _ ▸u _)  → ¬▸u _ ▸u
            (invUsageId₀ ok _ _ _ _) → not-erased ok
        (inj₁ ▸u) → inj₁ (Idₘ not-erased ▸A ▸t ▸u)

⌈⌉▸[ m ]? rfl =
  inj₁ rflₘ

⌈⌉▸[ m ]? J p q A t B u t′ v with Erased-matches-for-J?
… | yes ok =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
    (inj₂ ¬▸A) → inj₂ λ _ ▸J →
      case inv-usage-J ▸J of λ where
        (invUsageJ₀ _ ▸A _ _ _ _ _ _)    → ¬▸A _ ▸A
        (invUsageJ not-ok _ _ _ _ _ _ _) → not-ok ok
    (inj₁ ▸A) → case ⌈⌉▸[ 𝟘ᵐ? ]? t of λ where
      (inj₂ ¬▸t) → inj₂ λ _ ▸J →
        case inv-usage-J ▸J of λ where
          (invUsageJ₀ _ _ ▸t _ _ _ _ _)    → ¬▸t _ ▸t
          (invUsageJ not-ok _ _ _ _ _ _ _) → not-ok ok
      (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
        (inj₂ ¬▸u) → inj₂ λ _ ▸J →
          case inv-usage-J ▸J of λ where
            (invUsageJ₀ _ _ _ _ ▸u _ _ _)    → ¬▸u _ ▸u
            (invUsageJ not-ok _ _ _ _ _ _ _) → not-ok ok
        (inj₁ ▸u) → case ⌈⌉▸[ 𝟘ᵐ? ]? t′ of λ where
          (inj₂ ¬▸t′) → inj₂ λ _ ▸J →
            case inv-usage-J ▸J of λ where
              (invUsageJ₀ _ _ _ _ _ ▸t′ _ _)   → ¬▸t′ _ ▸t′
              (invUsageJ not-ok _ _ _ _ _ _ _) → not-ok ok
          (inj₁ ▸t′) → case ⌈⌉▸[ 𝟘ᵐ? ]? v of λ where
            (inj₂ ¬▸v) → inj₂ λ _ ▸J →
              case inv-usage-J ▸J of λ where
                (invUsageJ₀ _ _ _ _ _ _ ▸v _)    → ¬▸v _ ▸v
                (invUsageJ not-ok _ _ _ _ _ _ _) → not-ok ok
            (inj₁ ▸v) → case ⌈⌉▸[ 𝟘ᵐ? ]? B of λ where
              (inj₂ ¬▸B) → inj₂ λ _ ▸J →
                case inv-usage-J ▸J of λ where
                  (invUsageJ₀ _ _ _ ▸B _ _ _ _)    → ¬▸B _ ▸B
                  (invUsageJ not-ok _ _ _ _ _ _ _) → not-ok ok
              (inj₁ ▸B) → case ⌜ 𝟘ᵐ? ⌝ · p ≤?
                               headₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ?)) of λ where
                (no 𝟘ᵐ?p≰) → inj₂ λ _ ▸J →
                  case inv-usage-J ▸J of λ where
                    (invUsageJ₀ _ _ _ ▸B _ _ _ _) →
                      𝟘ᵐ?p≰ $ headₘ-monotone $ tailₘ-monotone $
                      usage-upper-bound ▸B
                    (invUsageJ not-ok _ _ _ _ _ _ _) → not-ok ok
                (yes 𝟘ᵐ?p≤) → case ⌜ 𝟘ᵐ? ⌝ · q ≤?
                                   headₘ (⌈ B ⌉ 𝟘ᵐ?) of λ where
                  (no 𝟘ᵐ?q≰) → inj₂ λ _ ▸J →
                    case inv-usage-J ▸J of λ where
                      (invUsageJ₀ _ _ _ ▸B _ _ _ _) →
                        𝟘ᵐ?q≰ $ headₘ-monotone $ usage-upper-bound ▸B
                      (invUsageJ not-ok _ _ _ _ _ _ _) → not-ok ok
                  (yes 𝟘ᵐ?q≤) →
                    let lemma = begin
                          tailₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ?)) ∙
                          ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q                      ≤⟨ ≤ᶜ-refl ∙ 𝟘ᵐ?p≤ ∙ 𝟘ᵐ?q≤ ⟩

                          tailₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ?)) ∙
                          headₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ?)) ∙ headₘ (⌈ B ⌉ 𝟘ᵐ?)  ≡⟨ cong (_∙ headₘ (⌈ B ⌉ _)) (headₘ-tailₘ-correct _) ⟩

                          tailₘ (⌈ B ⌉ 𝟘ᵐ?) ∙ headₘ (⌈ B ⌉ 𝟘ᵐ?)          ≡⟨ headₘ-tailₘ-correct _ ⟩

                          ⌈ B ⌉ 𝟘ᵐ?                                      ∎
                    in
                    inj₁ (J₀ₘ ok ▸A ▸t (sub ▸B lemma) ▸u ▸t′ ▸v)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
… | no not-ok =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
    (inj₂ ¬▸A) → inj₂ λ _ ▸J →
      case inv-usage-J ▸J of λ where
        (invUsageJ _ ▸A _ _ _ _ _ _)  → ¬▸A _ ▸A
        (invUsageJ₀ ok _ _ _ _ _ _ _) → not-ok ok
    (inj₁ ▸A) → case ⌈⌉▸[ m ]? t of λ where
      (inj₂ ¬▸t) → inj₂ λ _ ▸J →
        case inv-usage-J ▸J of λ where
          (invUsageJ _ _ ▸t _ _ _ _ _)  → ¬▸t _ ▸t
          (invUsageJ₀ ok _ _ _ _ _ _ _) → not-ok ok
      (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
        (inj₂ ¬▸u) → inj₂ λ _ ▸J →
          case inv-usage-J ▸J of λ where
            (invUsageJ _ _ _ _ ▸u _ _ _)  → ¬▸u _ ▸u
            (invUsageJ₀ ok _ _ _ _ _ _ _) → not-ok ok
        (inj₁ ▸u) → case ⌈⌉▸[ m ]? t′ of λ where
          (inj₂ ¬▸t′) → inj₂ λ _ ▸J →
            case inv-usage-J ▸J of λ where
              (invUsageJ _ _ _ _ _ ▸t′ _ _) → ¬▸t′ _ ▸t′
              (invUsageJ₀ ok _ _ _ _ _ _ _) → not-ok ok
          (inj₁ ▸t′) → case ⌈⌉▸[ m ]? v of λ where
            (inj₂ ¬▸v) → inj₂ λ _ ▸J →
              case inv-usage-J ▸J of λ where
                (invUsageJ _ _ _ _ _ _ ▸v _)  → ¬▸v _ ▸v
                (invUsageJ₀ ok _ _ _ _ _ _ _) → not-ok ok
            (inj₁ ▸v) → case ⌈⌉▸[ m ]? B of λ where
              (inj₂ ¬▸B) → inj₂ λ _ ▸J →
                case inv-usage-J ▸J of λ where
                  (invUsageJ _ _ _ ▸B _ _ _ _)  → ¬▸B _ ▸B
                  (invUsageJ₀ ok _ _ _ _ _ _ _) → not-ok ok
              (inj₁ ▸B) → case ⌜ m ⌝ · p ≤?
                               headₘ (tailₘ (⌈ B ⌉ m)) of λ where
                (no mp≰) → inj₂ λ _ ▸J →
                  case inv-usage-J ▸J of λ where
                    (invUsageJ _ _ _ ▸B _ _ _ _) →
                      mp≰ $ headₘ-monotone $ tailₘ-monotone $
                      usage-upper-bound ▸B
                    (invUsageJ₀ ok _ _ _ _ _ _ _) → not-ok ok
                (yes mp≤) → case ⌜ m ⌝ · q ≤? headₘ (⌈ B ⌉ m) of λ where
                  (no mq≰) → inj₂ λ _ ▸J →
                    case inv-usage-J ▸J of λ where
                      (invUsageJ _ _ _ ▸B _ _ _ _) →
                        mq≰ $ headₘ-monotone $ usage-upper-bound ▸B
                      (invUsageJ₀ ok _ _ _ _ _ _ _) → not-ok ok
                  (yes mq≤) →
                    let lemma = begin
                          tailₘ (tailₘ (⌈ B ⌉ m)) ∙
                          ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q                      ≤⟨ ≤ᶜ-refl ∙ mp≤ ∙ mq≤ ⟩

                          tailₘ (tailₘ (⌈ B ⌉ m)) ∙
                          headₘ (tailₘ (⌈ B ⌉ m)) ∙ headₘ (⌈ B ⌉ m)  ≡⟨ cong (_∙ headₘ (⌈ B ⌉ _)) (headₘ-tailₘ-correct _) ⟩

                          tailₘ (⌈ B ⌉ m) ∙ headₘ (⌈ B ⌉ m)          ≡⟨ headₘ-tailₘ-correct _ ⟩

                          ⌈ B ⌉ m                                    ∎
                    in
                    inj₁ (Jₘ not-ok ▸A ▸t (sub ▸B lemma) ▸u ▸t′ ▸v)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

⌈⌉▸[ m ]? K p A t B u v with Erased-matches-for-K?
… | yes ok =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
    (inj₂ ¬▸A) → inj₂ λ _ ▸K →
      case inv-usage-K ▸K of λ where
        (invUsageK₀ _ ▸A _ _ _ _ _)    → ¬▸A _ ▸A
        (invUsageK not-ok _ _ _ _ _ _) → not-ok ok
    (inj₁ ▸A) → case ⌈⌉▸[ 𝟘ᵐ? ]? t of λ where
      (inj₂ ¬▸t) → inj₂ λ _ ▸K →
        case inv-usage-K ▸K of λ where
          (invUsageK₀ _ _ ▸t _ _ _ _)    → ¬▸t _ ▸t
          (invUsageK not-ok _ _ _ _ _ _) → not-ok ok
      (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
        (inj₂ ¬▸u) → inj₂ λ _ ▸K →
          case inv-usage-K ▸K of λ where
            (invUsageK₀ _ _ _ _ ▸u _ _)    → ¬▸u _ ▸u
            (invUsageK not-ok _ _ _ _ _ _) → not-ok ok
        (inj₁ ▸u) → case ⌈⌉▸[ 𝟘ᵐ? ]? v of λ where
          (inj₂ ¬▸v) → inj₂ λ _ ▸K →
            case inv-usage-K ▸K of λ where
              (invUsageK₀ _ _ _ _ _ ▸v _)    → ¬▸v _ ▸v
              (invUsageK not-ok _ _ _ _ _ _) → not-ok ok
          (inj₁ ▸v) → case ⌈⌉▸[ 𝟘ᵐ? ]? B of λ where
            (inj₂ ¬▸B) → inj₂ λ _ ▸K →
              case inv-usage-K ▸K of λ where
                (invUsageK₀ _ _ _ ▸B _ _ _)    → ¬▸B _ ▸B
                (invUsageK not-ok _ _ _ _ _ _) → not-ok ok
            (inj₁ ▸B) → case ⌜ 𝟘ᵐ? ⌝ · p ≤? headₘ (⌈ B ⌉ 𝟘ᵐ?) of λ where
              (no 𝟘ᵐ?p≰) → inj₂ λ _ ▸K →
                case inv-usage-K ▸K of λ where
                  (invUsageK₀ _ _ _ ▸B _ _ _) →
                    𝟘ᵐ?p≰ $ headₘ-monotone $ usage-upper-bound ▸B
                  (invUsageK not-ok _ _ _ _ _ _) → not-ok ok
              (yes 𝟘ᵐ?p≤) →
                let lemma = begin
                      tailₘ (⌈ B ⌉ 𝟘ᵐ?) ∙ ⌜ 𝟘ᵐ? ⌝ · p        ≤⟨ ≤ᶜ-refl ∙ 𝟘ᵐ?p≤ ⟩
                      tailₘ (⌈ B ⌉ 𝟘ᵐ?) ∙ headₘ (⌈ B ⌉ 𝟘ᵐ?)  ≡⟨ headₘ-tailₘ-correct _ ⟩
                      ⌈ B ⌉ 𝟘ᵐ?                              ∎
                in
                inj₁ (K₀ₘ ok ▸A ▸t (sub ▸B lemma) ▸u ▸v)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
… | no not-ok =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
    (inj₂ ¬▸A) → inj₂ λ _ ▸K →
      case inv-usage-K ▸K of λ where
        (invUsageK _ ▸A _ _ _ _ _)  → ¬▸A _ ▸A
        (invUsageK₀ ok _ _ _ _ _ _) → not-ok ok
    (inj₁ ▸A) → case ⌈⌉▸[ m ]? t of λ where
      (inj₂ ¬▸t) → inj₂ λ _ ▸K →
        case inv-usage-K ▸K of λ where
          (invUsageK _ _ ▸t _ _ _ _)  → ¬▸t _ ▸t
          (invUsageK₀ ok _ _ _ _ _ _) → not-ok ok
      (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
        (inj₂ ¬▸u) → inj₂ λ _ ▸K →
          case inv-usage-K ▸K of λ where
            (invUsageK _ _ _ _ ▸u _ _)  → ¬▸u _ ▸u
            (invUsageK₀ ok _ _ _ _ _ _) → not-ok ok
        (inj₁ ▸u) → case ⌈⌉▸[ m ]? v of λ where
          (inj₂ ¬▸v) → inj₂ λ _ ▸K →
            case inv-usage-K ▸K of λ where
              (invUsageK _ _ _ _ _ ▸v _)  → ¬▸v _ ▸v
              (invUsageK₀ ok _ _ _ _ _ _) → not-ok ok
          (inj₁ ▸v) → case ⌈⌉▸[ m ]? B of λ where
            (inj₂ ¬▸B) → inj₂ λ _ ▸K →
              case inv-usage-K ▸K of λ where
                (invUsageK _ _ _ ▸B _ _ _)  → ¬▸B _ ▸B
                (invUsageK₀ ok _ _ _ _ _ _) → not-ok ok
            (inj₁ ▸B) → case ⌜ m ⌝ · p ≤? headₘ (⌈ B ⌉ m) of λ where
              (no mp≰) → inj₂ λ _ ▸K →
                case inv-usage-K ▸K of λ where
                  (invUsageK _ _ _ ▸B _ _ _) →
                    mp≰ $ headₘ-monotone $ usage-upper-bound ▸B
                  (invUsageK₀ ok _ _ _ _ _ _) → not-ok ok
              (yes mp≤) →
                let lemma = begin
                      tailₘ (⌈ B ⌉ m) ∙ ⌜ m ⌝ · p        ≤⟨ ≤ᶜ-refl ∙ mp≤ ⟩
                      tailₘ (⌈ B ⌉ m) ∙ headₘ (⌈ B ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩
                      ⌈ B ⌉ m                            ∎
                in
                inj₁ (Kₘ not-ok ▸A ▸t (sub ▸B lemma) ▸u ▸v)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

⌈⌉▸[ m ]? []-cong _ A t u v = case ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
  (inj₂ ¬▸A) → inj₂ λ _ ▸bc →
    case inv-usage-[]-cong ▸bc of λ (invUsage-[]-cong ▸A _ _ _ _) →
    ¬▸A _ ▸A
  (inj₁ ▸A) → case ⌈⌉▸[ 𝟘ᵐ? ]? t of λ where
    (inj₂ ¬▸t) → inj₂ λ _ ▸bc →
      case inv-usage-[]-cong ▸bc of λ (invUsage-[]-cong _ ▸t _ _ _) →
      ¬▸t _ ▸t
    (inj₁ ▸t) → case ⌈⌉▸[ 𝟘ᵐ? ]? u of λ where
      (inj₂ ¬▸u) → inj₂ λ _ ▸bc →
        case inv-usage-[]-cong ▸bc of λ (invUsage-[]-cong _ _ ▸u _ _) →
        ¬▸u _ ▸u
      (inj₁ ▸u) → case ⌈⌉▸[ 𝟘ᵐ? ]? v of λ where
        (inj₂ ¬▸v) → inj₂ λ _ ▸bc →
          case inv-usage-[]-cong ▸bc of
            λ (invUsage-[]-cong _ _ _ ▸v _) →
          ¬▸v _ ▸v
        (inj₁ ▸v) → inj₁ ([]-congₘ ▸A ▸t ▸u ▸v)

infix 10 ⌈⌉▸[_]?′_

-- It is decidable whether a term is well-resourced under the inferred
-- context.

⌈⌉▸[_]?′_ : ∀ m (t : Term n) → Dec (⌈ t ⌉ m ▸[ m ] t)
⌈⌉▸[ m ]?′ t = case ⌈⌉▸[ m ]? t of λ where
  (inj₁ ▸t) → yes ▸t
  (inj₂ ¬▸t) → no (λ ▸t → ¬▸t _ ▸t)

-- It is decidable whether a term is well-resourced with respect to a
-- given mode, and in that case a greatest usage context for which the
-- term is well-resourced (with respect to the given mode) can be
-- computed.

infix 10 ▸[_]?_

▸[_]?_ :
  ∀ m (t : Term n) →
  ∃ λ (d : Dec (∃ λ γ → γ ▸[ m ] t)) →
    case d of λ where
      (yes (γ , _)) → ∀ δ → δ ▸[ m ] t → δ ≤ᶜ γ
      (no _)        → Lift _ ⊤
▸[ m ]? t = case ⌈⌉▸[ m ]? t of λ where
  (inj₁ ▸t)  → yes (⌈ t ⌉ m , ▸t) , λ _ → usage-upper-bound
  (inj₂ ¬▸t) → no (λ (_ , ▸t) → ¬▸t _ ▸t) , _

-- It is decidable whether a term is well-resourced with respect to a
-- given context and mode.

infix 10 _▸[_]?_

_▸[_]?_ : ∀ γ m (t : Term n) → Dec (γ ▸[ m ] t)
γ ▸[ m ]? t = case ▸[ m ]? t of λ where
  (no ¬▸t , _)        → no λ ▸t → ¬▸t (_ , ▸t)
  (yes (δ , δ▸) , ≤δ) → case γ ≤ᶜ? δ of λ where
    (no γ≰δ)  → no λ ▸t → γ≰δ (≤δ _ ▸t)
    (yes γ≤δ) → yes (sub δ▸ γ≤δ)
