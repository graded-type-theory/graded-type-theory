------------------------------------------------------------------------
-- The usage relation can be decided (given certain assumptions)
------------------------------------------------------------------------

open import Definition.Modality
open import Tools.PropositionalEquality
open import Tools.Relation

module Definition.Modality.Usage.Decidable
  {a} {M : Set a} (𝕄 : Modality M) (open Modality 𝕄)
  -- Equality is assumed to be decidable for M.
  (_≟_ : Decidable (_≡_ {A = M}))
  -- The Prodrec relation is assumed to be decidable.
  (Prodrec? : Decidable Prodrec)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Modality.Usage.Properties 𝕄
open import Definition.Mode 𝕄
open import Definition.Untyped M

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Nullary
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
  _≤?_ = ≈-decidable→≤-decidable _≟_

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

⌈⌉▸[ m ]? Unit    = inj₁ Unitₘ

⌈⌉▸[ m ]? Empty   = inj₁ Emptyₘ

⌈⌉▸[ m ]? zero    = inj₁ zeroₘ

⌈⌉▸[ m ]? star    = inj₁ starₘ

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

⌈⌉▸[ m ]? Emptyrec p _ t = case ⌈⌉▸[ m ᵐ· p ]? t of λ where
  (inj₁ ▸t)  → inj₁ (Emptyrecₘ ▸t)
  (inj₂ ¬▸t) → inj₂ λ _ ▸er →
    case inv-usage-Emptyrec ▸er of λ (invUsageEmptyrec ▸t δ≤) →
    ¬▸t _ ▸t

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

⌈⌉▸[ m ]? fst p t = case p-ok of λ where
    (no p-not-ok) → inj₂ λ _ ▸fst →
      case inv-usage-fst ▸fst of λ (invUsageFst _ _ _ _ p-ok) →
      p-not-ok p-ok
    (yes p-ok) → case m-ok p-ok m of λ where
      (no m-not-ok) → inj₂ λ _ ▸fst →
        case inv-usage-fst ▸fst of λ (invUsageFst m′ m′-ok _ _ _) →
        m-not-ok (m′ , sym m′-ok)
      (yes (m′ , m′-ok)) →
        case ⌈⌉▸[ m ]? t of λ where
          (inj₁ ▸t)  → inj₁ (fstₘ m′ (▸-cong (sym m′-ok) ▸t) m′-ok p-ok)
          (inj₂ ¬▸t) → inj₂ λ _ ▸fst →
            case inv-usage-fst ▸fst of λ (invUsageFst _ _ ▸t _ _) →
            ¬▸t _ ▸t
  where
  p-ok : Dec (p ≈ 𝟘 → (𝟙 ≈ 𝟘) ⊎ T 𝟘ᵐ-allowed)
  p-ok = case is-𝟘? p of λ where
    (no p≉𝟘)  → yes (λ p≈𝟘 → ⊥-elim (p≉𝟘 p≈𝟘))
    (yes p≈𝟘) → case 𝟙 ≟ 𝟘 of λ where
      (yes 𝟙≈𝟘) → yes (λ _ → inj₁ 𝟙≈𝟘)
      (no 𝟙≉𝟘)  → 𝟘ᵐ-allowed-elim
        (λ ok → yes (λ _ → inj₂ ok))
        (λ not-ok → no λ ok → case ok p≈𝟘 of λ where
          (inj₁ 𝟙≈𝟘) → 𝟙≉𝟘 𝟙≈𝟘
          (inj₂ ok)  → not-ok ok)

  m-ok :
    (p ≈ 𝟘 → (𝟙 ≈ 𝟘) ⊎ T 𝟘ᵐ-allowed) →
    ∀ m → Dec (∃ λ m′ → m′ ᵐ· p ≡ m)
  m-ok _    𝟘ᵐ = yes (𝟘ᵐ , refl)
  m-ok p-ok 𝟙ᵐ = case is-𝟘? p of λ where
      (no p≉𝟘)  → yes (𝟙ᵐ , ≉𝟘→⌞⌟≡𝟙ᵐ p≉𝟘)
      (yes p≈𝟘) → case p-ok p≈𝟘 of λ where
        (inj₁ 𝟙≈𝟘) → yes (𝟙ᵐ , ᵐ·-identityʳ 𝟙≈𝟘)
        (inj₂ ok)  → no λ where
          (𝟘ᵐ , ())
          (𝟙ᵐ , ⌞p⌟≈𝟙) →
            case
              𝟘ᵐ[ ok ]  ≡˘⟨ 𝟘ᵐ?≡𝟘ᵐ ⟩
              𝟘ᵐ?       ≡˘⟨ ⌞𝟘⌟≡𝟘ᵐ? ⟩
              ⌞ 𝟘 ⌟     ≡˘⟨ cong ⌞_⌟ p≈𝟘 ⟩
              ⌞ p ⌟     ≡⟨ ⌞p⌟≈𝟙 ⟩
              𝟙ᵐ        ∎
            of λ ()
    where
    open Tools.Reasoning.PropositionalEquality

⌈⌉▸[ m ]? Π p , q ▷ F ▹ G = case ⌈⌉▸[ m ᵐ· p ]? F of λ where
    (inj₂ ¬▸F) → inj₂ λ _ ▸Π →
      case inv-usage-Π ▸Π of λ (invUsageΠΣ ▸F _ _) →
      ¬▸F _ ▸F
    (inj₁ ▸F) → case ⌈⌉▸[ m ]? G of λ where
      (inj₂ ¬▸G) → inj₂ λ _ ▸Π →
        case inv-usage-Π ▸Π of λ (invUsageΠΣ _ ▸G _) →
        ¬▸G _ ▸G
      (inj₁ ▸G) → case ⌜ m ⌝ · q ≤? headₘ (⌈ G ⌉ m) of λ where
        (no mq≰) → inj₂ λ _ ▸Π →
          case inv-usage-Π ▸Π of λ (invUsageΠΣ _ ▸G′ _) →
          mq≰ (headₘ-monotone (usage-upper-bound ▸G′))
        (yes mq≤) → inj₁ (Πₘ ▸F (sub ▸G (begin
          tailₘ (⌈ G ⌉ m) ∙ ⌜ m ⌝ · q        ≤⟨ ≤ᶜ-refl ∙ mq≤ ⟩
          tailₘ (⌈ G ⌉ m) ∙ headₘ (⌈ G ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩
          ⌈ G ⌉ m                            ∎)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

⌈⌉▸[ m ]? Σ p , q ▷ F ▹ G = case ⌈⌉▸[ m ᵐ· p ]? F of λ where
    (inj₂ ¬▸F) → inj₂ λ _ ▸Σ →
      case inv-usage-Σ ▸Σ of λ (invUsageΠΣ ▸F _ _) →
      ¬▸F _ ▸F
    (inj₁ ▸F) → case ⌈⌉▸[ m ]? G of λ where
      (inj₂ ¬▸G) → inj₂ λ _ ▸Σ →
        case inv-usage-Σ ▸Σ of λ (invUsageΠΣ _ ▸G _) →
        ¬▸G _ ▸G
      (inj₁ ▸G) → case ⌜ m ⌝ · q ≤? headₘ (⌈ G ⌉ m) of λ where
        (no mq≰) → inj₂ λ _ ▸Σ →
          case inv-usage-Σ ▸Σ of λ (invUsageΠΣ _ ▸G′ _) →
          mq≰ (headₘ-monotone (usage-upper-bound ▸G′))
        (yes mq≤) → inj₁ (Σₘ ▸F (sub ▸G (begin
          tailₘ (⌈ G ⌉ m) ∙ ⌜ m ⌝ · q        ≤⟨ ≤ᶜ-refl ∙ mq≤ ⟩
          tailₘ (⌈ G ⌉ m) ∙ headₘ (⌈ G ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩
          ⌈ G ⌉ m                            ∎)))
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

⌈⌉▸[ m ]? prod Σᵣ p t u = case ⌈⌉▸[ m ᵐ· p ]? t of λ where
  (inj₂ ¬▸t) → inj₂ λ _ ▸prod →
    case inv-usage-prodᵣ ▸prod of λ (invUsageProdᵣ ▸t _ _ _) →
    ¬▸t _ ▸t
  (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
    (inj₂ ¬▸u) → inj₂ λ _ ▸prod →
      case inv-usage-prodᵣ ▸prod of λ (invUsageProdᵣ _ ▸u _ _) →
      ¬▸u _ ▸u
    (inj₁ ▸u) → inj₁ (prodᵣₘ ▸t ▸u refl)

⌈⌉▸[ m ]? prod Σₚ p t u = case ⌈⌉▸[ m ᵐ· p ]? t of λ where
  (inj₂ ¬▸t) → inj₂ λ _ ▸prod →
    case inv-usage-prodₚ ▸prod of λ (invUsageProdₚ ▸t _ _) →
    ¬▸t _ ▸t
  (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
    (inj₂ ¬▸u) → inj₂ λ _ ▸prod →
      case inv-usage-prodₚ ▸prod of λ (invUsageProdₚ _ ▸u _) →
      ¬▸u _ ▸u
    (inj₁ ▸u) → inj₁ (prodₚₘ ▸t ▸u)

⌈⌉▸[ m ]? prodrec r p _ t u = case Prodrec? r p of λ where
    (no not-ok) → inj₂ λ _ ▸pr →
      case inv-usage-prodrec ▸pr of λ (invUsageProdrec _ _ ok _) →
      not-ok ok
    (yes ok) → case ⌈⌉▸[ m ᵐ· r ]? t of λ where
      (inj₂ ¬▸t) → inj₂ λ _ ▸pr →
        case inv-usage-prodrec ▸pr of λ (invUsageProdrec ▸t _ _ _) →
        ¬▸t _ ▸t
      (inj₁ ▸t) → case ⌈⌉▸[ m ]? u of λ where
        (inj₂ ¬▸u) → inj₂ λ _ ▸pr →
          case inv-usage-prodrec ▸pr of λ (invUsageProdrec _ ▸u _ _) →
          ¬▸u _ ▸u
        (inj₁ ▸u) →
          case ⌜ m ⌝ · r · p ≤? headₘ (tailₘ (⌈ u ⌉ m)) of λ where
            (no mrp≰) → inj₂ λ _ ▸pr →
              case inv-usage-prodrec ▸pr of
                λ (invUsageProdrec _ ▸u′ _ _) →
              mrp≰ (headₘ-monotone
                      (tailₘ-monotone (usage-upper-bound ▸u′)))
            (yes mrp≤) → case ⌜ m ⌝ · r ≤? headₘ (⌈ u ⌉ m) of λ where
              (no mr≰) → inj₂ λ _ ▸pr →
                case inv-usage-prodrec ▸pr of
                  λ (invUsageProdrec _ ▸u′ _ _) →
                mr≰ (headₘ-monotone (usage-upper-bound ▸u′))
              (yes mr≤) →
                let lemma = begin
                      tailₘ (tailₘ (⌈ u ⌉ m)) ∙ ⌜ m ⌝ · r · p ∙
                      ⌜ m ⌝ · r                                            ≤⟨ ≤ᶜ-refl ∙ mrp≤ ∙ mr≤ ⟩

                      tailₘ (tailₘ (⌈ u ⌉ m)) ∙ headₘ (tailₘ (⌈ u ⌉ m)) ∙
                      headₘ (⌈ u ⌉ m)                                      ≡⟨ cong (_∙ headₘ (⌈ u ⌉ m)) (headₘ-tailₘ-correct _) ⟩

                      tailₘ (⌈ u ⌉ m) ∙ headₘ (⌈ u ⌉ m)                    ≡⟨ headₘ-tailₘ-correct _ ⟩

                      ⌈ u ⌉ m                                              ∎
                in inj₁ (prodrecₘ ▸t (sub ▸u lemma) ok)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

⌈⌉▸[ m ]? natrec p r _ z s n = case ⌈⌉▸[ m ]? z of λ where
    (inj₂ ¬▸z) → inj₂ λ _ ▸nr →
      case inv-usage-natrec ▸nr of λ (invUsageNatrec ▸z _ _ _) →
      ¬▸z _ ▸z
    (inj₁ ▸z) → case ⌈⌉▸[ m ]? s of λ where
      (inj₂ ¬▸s) → inj₂ λ _ ▸nr →
        case inv-usage-natrec ▸nr of λ (invUsageNatrec _ ▸s _ _) →
        ¬▸s _ ▸s
      (inj₁ ▸s) → case ⌜ m ⌝ · p ≤? headₘ (tailₘ (⌈ s ⌉ m)) of λ where
        (no mp≰) → inj₂ λ _ ▸nr →
          case inv-usage-natrec ▸nr of λ (invUsageNatrec _ ▸s′ _ _) →
          mp≰ (headₘ-monotone
                 (tailₘ-monotone (usage-upper-bound ▸s′)))
        (yes mp≤) → case ⌜ m ⌝ · r ≤? headₘ (⌈ s ⌉ m) of λ where
          (no mr≰) → inj₂ λ _ ▸nr →
            case inv-usage-natrec ▸nr of λ (invUsageNatrec _ ▸s′ _ _) →
            mr≰ (headₘ-monotone (usage-upper-bound ▸s′))
          (yes mr≤) → case ⌈⌉▸[ m ]? n of λ where
            (inj₂ ¬▸n) → inj₂ λ _ ▸nr →
              case inv-usage-natrec ▸nr of λ (invUsageNatrec _ _ ▸n _) →
              ¬▸n _ ▸n
            (inj₁ ▸n) →
              let lemma = begin
                    tailₘ (tailₘ (⌈ s ⌉ m)) ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r      ≤⟨ ≤ᶜ-refl ∙ mp≤ ∙ mr≤ ⟩

                    tailₘ (tailₘ (⌈ s ⌉ m)) ∙ headₘ (tailₘ (⌈ s ⌉ m)) ∙
                    headₘ (⌈ s ⌉ m)                                      ≡⟨ cong (_∙ headₘ (⌈ s ⌉ m)) (headₘ-tailₘ-correct _) ⟩

                    tailₘ (⌈ s ⌉ m) ∙ headₘ (⌈ s ⌉ m)                    ≡⟨ headₘ-tailₘ-correct _ ⟩

                    ⌈ s ⌉ m                                              ∎
              in inj₁ (natrecₘ ▸z (sub ▸s lemma) ▸n)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

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
