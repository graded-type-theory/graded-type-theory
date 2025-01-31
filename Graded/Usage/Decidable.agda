------------------------------------------------------------------------
-- The usage relation can be decided (given certain assumptions)
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Graded.Usage.Decidable.Assumptions

module Graded.Usage.Decidable
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Usage-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as
open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Erased-matches
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Properties 𝕄 R
open import Graded.Usage.Restrictions.Natrec 𝕄
open import Graded.Mode 𝕄 hiding (_≟_)
open import Definition.Untyped M

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

private variable
  n : Nat

-- A given term is either well-resourced with respect to a given mode
-- and the usage context computed by ⌈_⌉, or it is not well-resourced
-- with respect to any usage context (and the given mode).

infix 10 ⌈⌉▸[_]?_

⌈⌉▸[_]?_ : ∀ m (t : Term n) → (⌈ t ⌉ m ▸[ m ] t) ⊎ (∀ γ → ¬ γ ▸[ m ] t)
⌈⌉▸[ m ]? U _     = inj₁ Uₘ

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

⌈⌉▸[ m ]? emptyrec p A t =
  case Dec→Dec-∀ (Emptyrec-allowed? m p) ×-Dec-∀
       ⌈⌉▸[ m ᵐ· p ]? t ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? A of λ where
    (inj₁ (ok , ▸t , ▸A)) → inj₁ (emptyrecₘ ▸t ▸A ok)
    (inj₂ problem)        → inj₂ λ _ ▸er →
      let invUsageEmptyrec ▸t ▸A ok _ = inv-usage-emptyrec ▸er in
      problem _ (ok , ▸t , ▸A)

⌈⌉▸[ m ]? lam p t =
  case ⌈⌉▸[ m ]? t ×-Dec-∀
       Dec→Dec-∀ (⌜ m ⌝ · p ≤? headₘ (⌈ t ⌉ m)) of λ where
    (inj₁ (▸t , mp≤)) → inj₁ $ lamₘ $ sub ▸t $ begin
        tailₘ (⌈ t ⌉ m) ∙ ⌜ m ⌝ · p        ≤⟨ ≤ᶜ-refl ∙ mp≤ ⟩
        tailₘ (⌈ t ⌉ m) ∙ headₘ (⌈ t ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩
        ⌈ t ⌉ m                            ∎
    (inj₂ problem) → inj₂ λ _ ▸lam →
      let invUsageLam ▸t _ = inv-usage-lam ▸lam in
      problem _
        (▸t , headₘ-monotone (usage-upper-bound no-sink-or-≤𝟘 ▸t))
  where
  open ≤ᶜ-reasoning

⌈⌉▸[ m ]? t ∘⟨ p ⟩ u =
  case ⌈⌉▸[ m ]? t ×-Dec-∀ ⌈⌉▸[ m ᵐ· p ]? u of λ where
    (inj₁ (▸t , ▸u)) → inj₁ (▸t ∘ₘ ▸u)
    (inj₂ problem)   → inj₂ λ _ ▸app →
      let invUsageApp ▸t ▸u _ = inv-usage-app ▸app in
      problem _ (▸t , ▸u)

⌈⌉▸[ m ]? fst p t =
  case Dec→Dec-∀ (p-ok m ×-dec m-ok m) ×-Dec-∀ ⌈⌉▸[ m ]? t of λ where
    (inj₁ ((p-ok , (m′ , m′-ok)) , ▸t)) →
      inj₁ (fstₘ m′ (▸-cong (sym m′-ok) ▸t) m′-ok p-ok)
    (inj₂ problem) → inj₂ λ _ ▸fst →
      let invUsageFst m′ m′-ok ▸t _ p-ok = inv-usage-fst ▸fst in
      problem _ ((p-ok , (m′ , sym m′-ok)) , ▸t)
  where
  p-ok : ∀ m → Dec (m ≡ 𝟙ᵐ → p ≤ 𝟙)
  p-ok 𝟘ᵐ = yes λ ()
  p-ok 𝟙ᵐ = case p ≤? 𝟙 of λ where
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

⌈⌉▸[ m ]? ΠΣ⟨ b ⟩ p , q ▷ A ▹ B =
  case ⌈⌉▸[ m ᵐ· p ]? A ×-Dec-∀ ⌈⌉▸[ m ]? B ×-Dec-∀
       Dec→Dec-∀ (⌜ m ⌝ · q ≤? headₘ (⌈ B ⌉ m)) of λ where
    (inj₁ (▸A , ▸B , mq≤)) →
      let lemma = begin
            tailₘ (⌈ B ⌉ m) ∙ ⌜ m ⌝ · q        ≤⟨ ≤ᶜ-refl ∙ mq≤ ⟩
            tailₘ (⌈ B ⌉ m) ∙ headₘ (⌈ B ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩
            ⌈ B ⌉ m                            ∎
      in inj₁ (ΠΣₘ ▸A (sub ▸B lemma))
    (inj₂ problem) → inj₂ λ _ ▸ΠΣ →
      let invUsageΠΣ ▸A ▸B _ = inv-usage-ΠΣ ▸ΠΣ in
      problem _
        (▸A , ▸B , headₘ-monotone (usage-upper-bound no-sink-or-≤𝟘 ▸B))
  where
  open ≤ᶜ-reasoning

⌈⌉▸[ m ]? prodʷ p t u =
  case ⌈⌉▸[ m ᵐ· p ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u of λ where
    (inj₁ (▸t , ▸u)) → inj₁ (prodʷₘ ▸t ▸u)
    (inj₂ problem)   → inj₂ λ _ ▸prod →
      let invUsageProdʷ ▸t ▸u _ = inv-usage-prodʷ ▸prod in
      problem _ (▸t , ▸u)

⌈⌉▸[ m ]? prodˢ p t u =
  case ⌈⌉▸[ m ᵐ· p ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u of λ where
    (inj₁ (▸t , ▸u)) → inj₁ (prodˢₘ ▸t ▸u)
    (inj₂ problem)   → inj₂ λ _ ▸prod →
      let invUsageProdˢ ▸t ▸u _ = inv-usage-prodˢ ▸prod in
      problem _ (▸t , ▸u)

⌈⌉▸[ m ]? unitrec _ p q A t u =
  case Dec→Dec-∀ (Unitrec-allowed? m p q) ×-Dec-∀
       ⌈⌉▸[ m ᵐ· p ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u ×-Dec-∀
       ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀
       Dec→Dec-∀ (⌜ 𝟘ᵐ? ⌝ · q ≤? headₘ (⌈ A ⌉ 𝟘ᵐ?)) of λ where
    (inj₁ (ok , ▸t , ▸u , ▸A , q≤)) →
      let lemma = begin
            tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ (⌜ 𝟘ᵐ? ⌝ · q)      ≤⟨ ≤ᶜ-refl ∙ q≤ ⟩
            tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ headₘ (⌈ A ⌉ 𝟘ᵐ?)  ≡⟨ headₘ-tailₘ-correct _ ⟩
            ⌈ A ⌉ 𝟘ᵐ?                              ∎
      in
      inj₁ (unitrecₘ ▸t ▸u (sub ▸A lemma) ok)
    (inj₂ problem) → inj₂ λ _ ▸ur →
      let invUsageUnitrec ▸t ▸u ▸A ok _ = inv-usage-unitrec ▸ur in
      problem _
        (ok , ▸t , ▸u , ▸A ,
         headₘ-monotone (usage-upper-bound no-sink-or-≤𝟘 ▸A))
  where
  open ≤ᶜ-reasoning

⌈⌉▸[ m ]? prodrec r p q A t u =
  case Dec→Dec-∀ (Prodrec-allowed? m r p q) ×-Dec-∀
       ⌈⌉▸[ m ᵐ· r ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u ×-Dec-∀
       Dec→Dec-∀ (⌜ m ⌝ · r · p ≤? headₘ (tailₘ (⌈ u ⌉ m))) ×-Dec-∀
       Dec→Dec-∀ (⌜ m ⌝ · r ≤? headₘ (⌈ u ⌉ m)) ×-Dec-∀
       ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀
       Dec→Dec-∀ (⌜ 𝟘ᵐ? ⌝ · q ≤? headₘ (⌈ A ⌉ 𝟘ᵐ?)) of λ where
    (inj₁ (ok , ▸t , ▸u , mrp≤ , mr≤ , ▸A , q≤)) →
      let lemma₁ = begin
            tailₘ (tailₘ (⌈ u ⌉ m)) ∙ ⌜ m ⌝ · r · p ∙ ⌜ m ⌝ · r  ≤⟨ ≤ᶜ-refl ∙ mrp≤ ∙ mr≤ ⟩

            tailₘ (tailₘ (⌈ u ⌉ m)) ∙ headₘ (tailₘ (⌈ u ⌉ m)) ∙
            headₘ (⌈ u ⌉ m)                                      ≡⟨ cong (_∙ headₘ (⌈ u ⌉ m)) (headₘ-tailₘ-correct _) ⟩

            tailₘ (⌈ u ⌉ m) ∙ headₘ (⌈ u ⌉ m)                    ≡⟨ headₘ-tailₘ-correct _ ⟩

            ⌈ u ⌉ m                                              ∎

          lemma₂ = begin
            tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ ⌜ 𝟘ᵐ? ⌝ · q        ≤⟨ ≤ᶜ-refl ∙ q≤ ⟩
            tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ headₘ (⌈ A ⌉ 𝟘ᵐ?)  ≡⟨ headₘ-tailₘ-correct _ ⟩
            ⌈ A ⌉ 𝟘ᵐ?                              ∎
      in
      inj₁ (prodrecₘ ▸t (sub ▸u lemma₁) (sub ▸A lemma₂) ok)
    (inj₂ problem) → inj₂ λ _ ▸pr →
      let invUsageProdrec ▸t ▸u ▸A ok _ = inv-usage-prodrec ▸pr
          ≤⌈u⌉m                         =
            usage-upper-bound no-sink-or-≤𝟘 ▸u
      in
      problem _
        ( ok , ▸t , ▸u , headₘ-monotone (tailₘ-monotone ≤⌈u⌉m)
        , headₘ-monotone ≤⌈u⌉m , ▸A
        , headₘ-monotone (usage-upper-bound no-sink-or-≤𝟘 ▸A)
        )
  where
  open ≤ᶜ-reasoning

⌈⌉▸[ m ]? natrec p q r A t u v =
  case ⌈⌉▸[ m ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u ×-Dec-∀
       Dec→Dec-∀ (⌜ m ⌝ · p ≤? headₘ (tailₘ (⌈ u ⌉ m))) ×-Dec-∀
       Dec→Dec-∀ (⌜ m ⌝ · r ≤? headₘ (⌈ u ⌉ m)) ×-Dec-∀
       ⌈⌉▸[ m ]? v ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀
       Dec→Dec-∀ (⌜ 𝟘ᵐ? ⌝ · q ≤? headₘ (⌈ A ⌉ 𝟘ᵐ?)) of λ where
    (inj₁ (▸t , ▸u , mp≤ , mr≤ , ▸v , ▸A , q≤)) →
      let lemma₁ = begin
            tailₘ (tailₘ (⌈ u ⌉ m)) ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r      ≤⟨ ≤ᶜ-refl ∙ mp≤ ∙ mr≤ ⟩

            tailₘ (tailₘ (⌈ u ⌉ m)) ∙ headₘ (tailₘ (⌈ u ⌉ m)) ∙
            headₘ (⌈ u ⌉ m)                                      ≡⟨ cong (_∙ headₘ (⌈ u ⌉ m)) (headₘ-tailₘ-correct _) ⟩

            tailₘ (⌈ u ⌉ m) ∙ headₘ (⌈ u ⌉ m)                    ≡⟨ headₘ-tailₘ-correct _ ⟩

            ⌈ u ⌉ m                                              ∎

          lemma₂ = begin
            tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ ⌜ 𝟘ᵐ? ⌝ · q        ≤⟨ ≤ᶜ-refl ∙ q≤ ⟩
            tailₘ (⌈ A ⌉ 𝟘ᵐ?) ∙ headₘ (⌈ A ⌉ 𝟘ᵐ?)  ≡⟨ headₘ-tailₘ-correct _ ⟩
            ⌈ A ⌉ 𝟘ᵐ?                              ∎
      in  inj₁ (natrec-nr-or-no-nrₘ ▸t (sub ▸u lemma₁) ▸v (sub ▸A lemma₂)
            (λ ⦃ has-nr ⦄ → lemma-nr has-nr inference-ok)
            (λ ⦃ no-nr ⦄ → ⊥-elim (lemma-no-nr no-nr inference-ok))
            λ ⦃ no-nr ⦄ → lemma-no-nr-glb no-nr inference-ok)
    (inj₂ problem) → inj₂ λ _ ▸nr →
      case inv-usage-natrec ▸nr of λ {
        (invUsageNatrec ▸t ▸u ▸v ▸A _ _) →
      let ≤⌈u⌉m = usage-upper-bound no-sink-or-≤𝟘 ▸u in
      problem _
        ( ▸t , ▸u , headₘ-monotone (tailₘ-monotone ≤⌈u⌉m)
        , headₘ-monotone ≤⌈u⌉m , ▸v , ▸A
        , headₘ-monotone (usage-upper-bound no-sink-or-≤𝟘 ▸A)
        ) }
  where
  open ≤ᶜ-reasoning
  lemma-nr :
    ∀ {nm} → (has-nr : Natrec-mode-has-nr nm) (ok : Natrec-mode-supports-usage-inference nm) →
    ⌈⌉-natrec ⦃ ok = ok ⦄ p r (⌈ t ⌉ m) (tailₘ (tailₘ (⌈ u ⌉ m))) (⌈ v ⌉ m) ≤ᶜ
    nrᶜ ⦃ has-nr = Natrec-mode-Has-nr has-nr ⦄ p r (⌈ t ⌉ m) (tailₘ (tailₘ (⌈ u ⌉ m))) (⌈ v ⌉ m)
  lemma-nr Nr Nr = ≤ᶜ-refl
  lemma-no-nr :
    ∀ {nm} → Natrec-mode-no-nr nm → Natrec-mode-supports-usage-inference nm → ⊥
  lemma-no-nr No-nr ()
  lemma-no-nr-glb :
    ∀ {nm} → Natrec-mode-no-nr-glb nm → (ok : Natrec-mode-supports-usage-inference nm) →
    ∃₂ λ x χ → Greatest-lower-bound x (nrᵢ r 𝟙 p) ×
    Greatest-lower-boundᶜ χ (nrᵢᶜ r (⌈ t ⌉ m) (tailₘ (tailₘ (⌈ u ⌉ m)))) ×
    ⌈⌉-natrec ⦃ ok = ok ⦄ p r (⌈ t ⌉ m) (tailₘ (tailₘ (⌈ u ⌉ m))) (⌈ v ⌉ m) ≤ᶜ x ·ᶜ ⌈ v ⌉ m +ᶜ χ
  lemma-no-nr-glb No-nr-glb (No-nr-glb has-GLB) =
    let x , x-glb = has-GLB r 𝟙 p
        χ , χ-glb = nrᵢᶜ-has-GLBᶜ has-GLB r (⌈ t ⌉ m) (tailₘ (tailₘ (⌈ u ⌉ m)))
    in  x , χ , x-glb , χ-glb , ≤ᶜ-refl

⌈⌉▸[ m ]? Id A t u with Id-erased?
… | yes erased =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? t ×-Dec-∀
       ⌈⌉▸[ 𝟘ᵐ? ]? u of λ where
    (inj₁ (▸A , ▸t , ▸u)) → inj₁ (Id₀ₘ erased ▸A ▸t ▸u)
    (inj₂ problem)        → inj₂ λ _ ▸Id →
      case inv-usage-Id ▸Id of λ where
        (invUsageId not-erased _ _ _ _) → not-erased erased
        (invUsageId₀ _ ▸A ▸t ▸u _)      → problem _ (▸A , ▸t , ▸u)
… | no not-erased =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀ ⌈⌉▸[ m ]? t ×-Dec-∀
       ⌈⌉▸[ m ]? u of λ where
    (inj₁ (▸A , ▸t , ▸u)) → inj₁ (Idₘ not-erased ▸A ▸t ▸u)
    (inj₂ problem)        → inj₂ λ _ ▸Id →
      case inv-usage-Id ▸Id of λ where
        (invUsageId _ ▸A ▸t ▸u _)    → problem _ (▸A , ▸t , ▸u)
        (invUsageId₀ erased _ _ _ _) → not-erased erased

⌈⌉▸[ m ]? rfl =
  inj₁ rflₘ

⌈⌉▸[ m ]? J p q A t B u v w with J-view p q m
… | is-all ≡all =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u ×-Dec-∀
       ⌈⌉▸[ 𝟘ᵐ? ]? v ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? w ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? B ×-Dec-∀
       Dec→Dec-∀ (⌜ 𝟘ᵐ? ⌝ · p ≤? headₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ?))) ×-Dec-∀
       Dec→Dec-∀ (⌜ 𝟘ᵐ? ⌝ · q ≤? headₘ (⌈ B ⌉ 𝟘ᵐ?)) of λ where
    (inj₁ (▸A , ▸t , ▸u , ▸v , ▸w , ▸B , 𝟘ᵐ?p≤ , 𝟘ᵐ?q≤)) →
      let lemma = begin
            tailₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ?)) ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q    ≤⟨ ≤ᶜ-refl ∙ 𝟘ᵐ?p≤ ∙ 𝟘ᵐ?q≤ ⟩

            tailₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ?)) ∙ headₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ?)) ∙
            headₘ (⌈ B ⌉ 𝟘ᵐ?)                                        ≡⟨ cong (_∙ headₘ (⌈ B ⌉ _)) (headₘ-tailₘ-correct _) ⟩

            tailₘ (⌈ B ⌉ 𝟘ᵐ?) ∙ headₘ (⌈ B ⌉ 𝟘ᵐ?)                    ≡⟨ headₘ-tailₘ-correct _ ⟩

            ⌈ B ⌉ 𝟘ᵐ?                                                ∎
      in
      inj₁ (J₀ₘ₂ ≡all ▸A ▸t (sub ▸B lemma) ▸u ▸v ▸w)
    (inj₂ problem) → inj₂ λ _ ▸J →
      case inv-usage-J ▸J of λ where
        (invUsageJ₀₂ _ ▸A ▸t ▸B ▸u ▸v ▸w _) →
          let ≤⌈B⌉𝟘ᵐ? = usage-upper-bound no-sink-or-≤𝟘 ▸B in
          problem _
            ( ▸A , ▸t , ▸u , ▸v , ▸w , ▸B
            , headₘ-monotone (tailₘ-monotone ≤⌈B⌉𝟘ᵐ?)
            , headₘ-monotone ≤⌈B⌉𝟘ᵐ?
            )
        (invUsageJ ≤some _ _ _ _ _ _ _ _) →
          case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
        (invUsageJ₀₁ ≡some _ _ _ _ _ _ _ _ _) →
          case trans (sym ≡some) ≡all of λ ()
  where
  open ≤ᶜ-reasoning
… | is-some-yes ≡some (refl , refl) =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u ×-Dec-∀
       ⌈⌉▸[ 𝟘ᵐ? ]? v ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? w ×-Dec-∀ ⌈⌉▸[ m ]? B ×-Dec-∀
       Dec→Dec-∀ (𝟘 ≤? headₘ (tailₘ (⌈ B ⌉ m))) ×-Dec-∀
       Dec→Dec-∀ (𝟘 ≤? headₘ (⌈ B ⌉ m)) of λ where
    (inj₁ (▸A , ▸t , ▸u , ▸v , ▸w , ▸B , 𝟘≤₁ , 𝟘≤₂)) →
      let lemma = begin
            tailₘ (tailₘ (⌈ B ⌉ m)) ∙ 𝟘 ∙ 𝟘                      ≤⟨ ≤ᶜ-refl ∙ 𝟘≤₁ ∙ 𝟘≤₂ ⟩

            tailₘ (tailₘ (⌈ B ⌉ m)) ∙ headₘ (tailₘ (⌈ B ⌉ m)) ∙
            headₘ (⌈ B ⌉ m)                                      ≡⟨ cong (_∙ headₘ (⌈ B ⌉ _)) (headₘ-tailₘ-correct _) ⟩

            tailₘ (⌈ B ⌉ m) ∙ headₘ (⌈ B ⌉ m)                    ≡⟨ headₘ-tailₘ-correct _ ⟩

            ⌈ B ⌉ m                                              ∎
      in
      inj₁ (J₀ₘ₁ ≡some refl refl ▸A ▸t (sub ▸B lemma) ▸u ▸v ▸w)
    (inj₂ problem) → inj₂ λ _ ▸J →
      case inv-usage-J ▸J of λ where
        (invUsageJ₀₁ _ _ _ ▸A ▸t ▸B ▸u ▸v ▸w _) →
          let ≤⌈B⌉m = usage-upper-bound no-sink-or-≤𝟘 ▸B in
          problem _
            ( ▸A , ▸t , ▸u , ▸v , ▸w , ▸B
            , headₘ-monotone (tailₘ-monotone ≤⌈B⌉m)
            , headₘ-monotone ≤⌈B⌉m
            )
        (invUsageJ _ ≢𝟘 _ _ _ _ _ _ _) →
          ⊥-elim $ ≢𝟘 ≡some (refl , refl)
        (invUsageJ₀₂ ≡all _ _ _ _ _ _ _) →
          case trans (sym ≡all) ≡some of λ ()
  where
  open ≤ᶜ-reasoning
… | is-other ≤some ≢𝟘 =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀ ⌈⌉▸[ m ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u ×-Dec-∀
       ⌈⌉▸[ m ]? v ×-Dec-∀ ⌈⌉▸[ m ]? w ×-Dec-∀ ⌈⌉▸[ m ]? B ×-Dec-∀
       Dec→Dec-∀ (⌜ m ⌝ · p ≤? headₘ (tailₘ (⌈ B ⌉ m))) ×-Dec-∀
       Dec→Dec-∀ (⌜ m ⌝ · q ≤? headₘ (⌈ B ⌉ m)) of λ where
    (inj₁ (▸A , ▸t , ▸u , ▸v , ▸w , ▸B , mp≤ , mq≤)) →
      let lemma = begin
            tailₘ (tailₘ (⌈ B ⌉ m)) ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q      ≤⟨ ≤ᶜ-refl ∙ mp≤ ∙ mq≤ ⟩

            tailₘ (tailₘ (⌈ B ⌉ m)) ∙ headₘ (tailₘ (⌈ B ⌉ m)) ∙
            headₘ (⌈ B ⌉ m)                                      ≡⟨ cong (_∙ headₘ (⌈ B ⌉ _)) (headₘ-tailₘ-correct _) ⟩

            tailₘ (⌈ B ⌉ m) ∙ headₘ (⌈ B ⌉ m)                    ≡⟨ headₘ-tailₘ-correct _ ⟩

            ⌈ B ⌉ m                                              ∎
      in
      inj₁ (Jₘ ≤some ≢𝟘 ▸A ▸t (sub ▸B lemma) ▸u ▸v ▸w)
    (inj₂ problem) → inj₂ λ _ ▸J →
      case inv-usage-J ▸J of λ where
        (invUsageJ _ _ ▸A ▸t ▸B ▸u ▸v ▸w _) →
          let ≤⌈B⌉m = usage-upper-bound no-sink-or-≤𝟘 ▸B in
          problem _
            ( ▸A , ▸t , ▸u , ▸v , ▸w , ▸B
            , headₘ-monotone (tailₘ-monotone ≤⌈B⌉m)
            , headₘ-monotone ≤⌈B⌉m
            )
        (invUsageJ₀₁ ≡some p≡𝟘 q≡𝟘 _ _ _ _ _ _ _) →
          ⊥-elim $ ≢𝟘 ≡some (p≡𝟘 , q≡𝟘)
        (invUsageJ₀₂ ≡all _ _ _ _ _ _ _) →
          case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
  where
  open ≤ᶜ-reasoning

⌈⌉▸[ m ]? K p A t B u v with K-view p m
… | is-all ≡all =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u ×-Dec-∀
       ⌈⌉▸[ 𝟘ᵐ? ]? v ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? B ×-Dec-∀
       Dec→Dec-∀ (⌜ 𝟘ᵐ? ⌝ · p ≤? headₘ (⌈ B ⌉ 𝟘ᵐ?)) of λ where
    (inj₁ (▸A , ▸t , ▸u , ▸v , ▸B , 𝟘ᵐ?p≤)) →
      let lemma = begin
            tailₘ (⌈ B ⌉ 𝟘ᵐ?) ∙ ⌜ 𝟘ᵐ? ⌝ · p        ≤⟨ ≤ᶜ-refl ∙ 𝟘ᵐ?p≤ ⟩
            tailₘ (⌈ B ⌉ 𝟘ᵐ?) ∙ headₘ (⌈ B ⌉ 𝟘ᵐ?)  ≡⟨ headₘ-tailₘ-correct _ ⟩
            ⌈ B ⌉ 𝟘ᵐ?                              ∎
      in
      inj₁ (K₀ₘ₂ ≡all ▸A ▸t (sub ▸B lemma) ▸u ▸v)
    (inj₂ problem) → inj₂ λ _ ▸K →
      case inv-usage-K ▸K of λ where
        (invUsageK₀₂ _ ▸A ▸t ▸B ▸u ▸v _) →
          problem _
            ( ▸A , ▸t , ▸u , ▸v , ▸B
            , headₘ-monotone (usage-upper-bound no-sink-or-≤𝟘 ▸B)
            )
        (invUsageK ≤some _ _ _ _ _ _ _) →
          case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
        (invUsageK₀₁ ≡some _ _ _ _ _ _ _) →
          case trans (sym ≡some) ≡all of λ ()
  where
  open ≤ᶜ-reasoning
… | is-some-yes ≡some refl =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u ×-Dec-∀
       ⌈⌉▸[ 𝟘ᵐ? ]? v ×-Dec-∀ ⌈⌉▸[ m ]? B ×-Dec-∀
       Dec→Dec-∀ (𝟘 ≤? headₘ (⌈ B ⌉ m)) of λ where
    (inj₁ (▸A , ▸t , ▸u , ▸v , ▸B , 𝟘≤)) →
      let lemma = begin
            tailₘ (⌈ B ⌉ m) ∙ 𝟘                ≤⟨ ≤ᶜ-refl ∙ 𝟘≤ ⟩
            tailₘ (⌈ B ⌉ m) ∙ headₘ (⌈ B ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩
            ⌈ B ⌉ m                            ∎
      in
      inj₁ (K₀ₘ₁ ≡some refl ▸A ▸t (sub ▸B lemma) ▸u ▸v)
    (inj₂ problem) → inj₂ λ _ ▸K →
      case inv-usage-K ▸K of λ where
        (invUsageK₀₁ _ _ ▸A ▸t ▸B ▸u ▸v _) →
          problem _
            ( ▸A , ▸t , ▸u , ▸v , ▸B
            , headₘ-monotone (usage-upper-bound no-sink-or-≤𝟘 ▸B)
            )
        (invUsageK _ ≢𝟘 _ _ _ _ _ _) →
          ⊥-elim $ ≢𝟘 ≡some refl
        (invUsageK₀₂ ≡all _ _ _ _ _ _) →
          case trans (sym ≡all) ≡some of λ ()
  where
  open ≤ᶜ-reasoning
… | is-other ≤some ≢𝟘 =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀ ⌈⌉▸[ m ]? t ×-Dec-∀ ⌈⌉▸[ m ]? u ×-Dec-∀
       ⌈⌉▸[ m ]? v ×-Dec-∀ ⌈⌉▸[ m ]? B ×-Dec-∀
       Dec→Dec-∀ (⌜ m ⌝ · p ≤? headₘ (⌈ B ⌉ m)) of λ where
    (inj₁ (▸A , ▸t , ▸u , ▸v , ▸B , mp≤)) →
      let lemma = begin
            tailₘ (⌈ B ⌉ m) ∙ ⌜ m ⌝ · p        ≤⟨ ≤ᶜ-refl ∙ mp≤ ⟩
            tailₘ (⌈ B ⌉ m) ∙ headₘ (⌈ B ⌉ m)  ≡⟨ headₘ-tailₘ-correct _ ⟩
            ⌈ B ⌉ m                            ∎
      in
      inj₁ (Kₘ ≤some ≢𝟘 ▸A ▸t (sub ▸B lemma) ▸u ▸v)
    (inj₂ problem) → inj₂ λ _ ▸K →
      case inv-usage-K ▸K of λ where
        (invUsageK _ _ ▸A ▸t ▸B ▸u ▸v ▸w) →
          problem _
            ( ▸A , ▸t , ▸u , ▸v , ▸B
            , headₘ-monotone (usage-upper-bound no-sink-or-≤𝟘 ▸B)
            )
        (invUsageK₀₁ ≡some p≡𝟘 _ _ _ _ _ _) →
          ⊥-elim $ ≢𝟘 ≡some p≡𝟘
        (invUsageK₀₂ ≡all _ _ _ _ _ _) →
          case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
  where
  open ≤ᶜ-reasoning

⌈⌉▸[ m ]? []-cong s A t u v =
  case ⌈⌉▸[ 𝟘ᵐ? ]? A ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? t ×-Dec-∀ ⌈⌉▸[ 𝟘ᵐ? ]? u ×-Dec-∀
       ⌈⌉▸[ 𝟘ᵐ? ]? v ×-Dec-∀
       Dec→Dec-∀ ([]-cong-allowed-mode? s m) of λ where
    (inj₁ (▸A , ▸t , ▸u , ▸v , ok)) →
      inj₁ ([]-congₘ ▸A ▸t ▸u ▸v ok)
    (inj₂ problem) → inj₂ λ _ ▸bc →
      let invUsage-[]-cong ▸A ▸t ▸u ▸v ok _ = inv-usage-[]-cong ▸bc in
      problem _ (▸A , ▸t , ▸u , ▸v , ok)

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
  (inj₁ ▸t)  → yes (⌈ t ⌉ m , ▸t) ,
               λ _ → usage-upper-bound no-sink-or-≤𝟘
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
