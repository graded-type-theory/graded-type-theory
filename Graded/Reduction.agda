------------------------------------------------------------------------
-- Properties related to the usage relation and reduction.
-- Notably, subject reduction.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Reduction
  {a} {M : Set a}
  (𝕄 : Modality M)
  (TR : Type-restrictions M)
  (UR : Usage-restrictions M)
  where

open Modality 𝕄
open Type-restrictions TR

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Substitution.Properties 𝕄 UR
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Inversion 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR
open import Graded.Mode 𝕄
open import Definition.Typed TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Eta-long-normal-form TR
open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Normal-form M

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PartialOrder
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private
  variable
    n : Nat
    Γ : Con Term n
    γ : Conₘ n
    t u A B : Term n
    m : Mode
    p q r : M

-- Subject reduction properties for modality usage

-- Term reduction preserves usage.
--
-- Proof by induction on the reduction relation using the inversion
-- and substitution lemmata for the usage relation.

usagePresTerm : γ ▸[ m ] t → Γ ⊢ t ⇒ u ∷ A → γ ▸[ m ] u
usagePresTerm γ▸t (conv t⇒u x) = usagePresTerm γ▸t t⇒u
usagePresTerm γ▸t (app-subst t⇒u x) =
  let invUsageApp δ▸t η▸a γ≤δ+pη = inv-usage-app γ▸t
  in  sub ((usagePresTerm δ▸t t⇒u) ∘ₘ η▸a) γ≤δ+pη
usagePresTerm {m = m} γ▸λta (β-red x x₁ x₂ x₃ x₄ _) =
  let invUsageApp δ▸λt η▸a γ≤δ′+pη = inv-usage-app γ▸λta
      invUsageLam δ▸t δ′≤δ = inv-usage-lam δ▸λt
  in  sub (sgSubstₘ-lemma₂ δ▸t (▸-cong (ᵐ·-cong m (PE.sym x₄)) η▸a))
          (≤ᶜ-trans γ≤δ′+pη
             (+ᶜ-monotone δ′≤δ
                (·ᶜ-monotoneˡ (≤-reflexive (PE.sym x₄)))))
usagePresTerm γ▸t (fst-subst x x₁ t⇒u) =
  let invUsageFst m m≡ ▸t γ≤ ok = inv-usage-fst γ▸t
  in  sub (fstₘ m (usagePresTerm (▸-cong m≡ ▸t) t⇒u) (PE.sym m≡) ok) γ≤
usagePresTerm γ▸t (snd-subst x x₁ t⇒u) =
  let invUsageSnd ▸t γ≤ = inv-usage-snd γ▸t
  in  sub (sndₘ (usagePresTerm ▸t t⇒u)) γ≤
usagePresTerm
  {γ = γ} {m′} ▸t′ (Σ-β₁ {t = t} {p = p} _ _ _ _ PE.refl _) =
  case inv-usage-fst ▸t′ of λ where
    (invUsageFst {δ = δ} m PE.refl ▸tu γ≤δ fst-ok) →
      case inv-usage-prodₚ ▸tu of λ where
        (invUsageProdₚ {δ = ζ} {η = η} ▸t ▸u δ≤pζ∧η) →
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

usagePresTerm {γ = γ} ▸t′ (Σ-β₂ {p = p} _ _ _ _ PE.refl _) =
  case inv-usage-snd ▸t′ of λ where
    (invUsageSnd {δ = δ} ▸tu γ≤δ) → case inv-usage-prodₚ ▸tu of λ where
      (invUsageProdₚ {δ = ζ} {η = η} ▸t ▸u δ≤pζ∧η) → sub ▸u (begin
        γ            ≤⟨ γ≤δ ⟩
        δ            ≤⟨ δ≤pζ∧η ⟩
        p ·ᶜ ζ ∧ᶜ η  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
        η            ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

usagePresTerm γ▸natrec (natrec-subst x x₁ x₂ t⇒u) =
  case inv-usage-natrec γ▸natrec of λ {
    (invUsageNatrec δ▸z η▸s θ▸n φ▸A γ≤ extra) →
  case extra of λ where
    invUsageNatrecStar →
      sub (natrecₘ δ▸z η▸s (usagePresTerm θ▸n t⇒u) φ▸A) γ≤
    (invUsageNatrecNoStar fix) →
      sub (natrec-no-starₘ δ▸z η▸s (usagePresTerm θ▸n t⇒u) φ▸A fix) γ≤ }

usagePresTerm {γ = γ} ▸natrec (natrec-zero {p = p} {r = r} _ _ _) =
  case inv-usage-natrec ▸natrec of λ {
    (invUsageNatrec {δ = δ} {η = η} {θ = θ} {χ = χ} ▸z _ _ _ γ≤ extra) →
  case extra of λ where
    invUsageNatrecStar →
      sub ▸z $ begin
        γ                            ≤⟨ γ≤ ⟩
        (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ p ·ᶜ θ ▷ r  ≤⟨ ⊛ᶜ-ineq₂ _ _ _ ⟩
        δ ∧ᶜ θ                       ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
        δ                            ∎
    (invUsageNatrecNoStar fix) →
      sub ▸z $ begin
        γ                                ≤⟨ γ≤ ⟩
        χ                                ≤⟨ fix ⟩
        δ ∧ᶜ θ ∧ᶜ η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ χ  ≤⟨ ∧ᶜ-decreasingˡ _ _ ⟩
        δ                                ∎ }
  where
  open import Graded.Modality.Dedicated-star.Instance
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

usagePresTerm {γ = γ} ▸natrec (natrec-suc {p = p} {r = r} _ _ _ _) =
  case inv-usage-natrec ▸natrec of λ {
    (invUsageNatrec {δ = δ} {η = η} {θ = θ} {χ = χ}
       ▸z ▸s ▸suc ▸A γ≤ extra) →
  case inv-usage-suc ▸suc of λ {
    (invUsageSuc {δ = θ′} ▸n θ≤θ′) →
  case extra of λ where
    invUsageNatrecStar →
      sub (doubleSubstₘ-lemma₃ ▸s
             (natrecₘ ▸z ▸s (sub ▸n θ≤θ′) ▸A) ▸n) $ begin
        γ                                                  ≤⟨ γ≤ ⟩
        (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ p ·ᶜ θ ▷ r                        ≤⟨ ⊛ᶜ-ineq₁ _ _ _ ⟩
        (η +ᶜ p ·ᶜ θ) +ᶜ r ·ᶜ (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ p ·ᶜ θ ▷ r  ≈⟨ +ᶜ-assoc _ _ _ ⟩
        η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ p ·ᶜ θ ▷ r    ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
        η +ᶜ r ·ᶜ (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ p ·ᶜ θ ▷ r +ᶜ p ·ᶜ θ    ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneʳ θ≤θ′)) ⟩
        η +ᶜ r ·ᶜ (δ ∧ᶜ θ) ⊛ᶜ η +ᶜ p ·ᶜ θ ▷ r +ᶜ p ·ᶜ θ′   ∎
    (invUsageNatrecNoStar fix) →
      sub (doubleSubstₘ-lemma₃ ▸s
             (natrec-no-starₘ ▸z ▸s (sub ▸n θ≤θ′) ▸A fix) ▸n) $ begin
        γ                                  ≤⟨ γ≤ ⟩
        χ                                  ≤⟨ fix ⟩
        δ ∧ᶜ θ ∧ᶜ (η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ χ)  ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
        θ ∧ᶜ (η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ χ)       ≤⟨ ∧ᶜ-decreasingʳ _ _ ⟩
        η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ χ              ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ θ≤θ′)) ⟩
        η +ᶜ p ·ᶜ θ′ +ᶜ r ·ᶜ χ             ≈⟨ +ᶜ-congˡ (+ᶜ-comm _ _) ⟩
        η +ᶜ r ·ᶜ χ +ᶜ p ·ᶜ θ′             ∎ }}
  where
  open import Graded.Modality.Dedicated-star.Instance
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

usagePresTerm γ▸prodrec (prodrec-subst x x₁ x₂ x₃ x₄ _) =
  let invUsageProdrec δ▸t η▸u θ▸A ok γ≤γ′ = inv-usage-prodrec γ▸prodrec
  in  sub (prodrecₘ (usagePresTerm δ▸t x₄) η▸u θ▸A ok) γ≤γ′
usagePresTerm
  {γ = γ} {m = m} γ▸prodrec
  (prodrec-β {p = p} {t = t} {t′ = t′} {u = u} {r = r}
     _ _ _ _ _ _ PE.refl _) =
  case inv-usage-prodrec γ▸prodrec of λ where
    (invUsageProdrec {δ = δ} {η = η} ▸t ▸u _ _ γ≤rδ+η) →
      case inv-usage-prodᵣ ▸t of λ where
        (invUsageProdᵣ {δ = δ′} {η = η′} ▸t₁ ▸t₂ δ≤pδ′+η′) → sub
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
  let invUsageemptyrec δ▸t η▸A γ≤δ = inv-usage-emptyrec γ▸et
  in  sub (emptyrecₘ (usagePresTerm δ▸t t⇒u) η▸A) γ≤δ

-- Type reduction preserves usage.

usagePres : γ ▸[ m ] A → Γ ⊢ A ⇒ B → γ ▸[ m ] B
usagePres γ▸A (univ A⇒B) = usagePresTerm γ▸A A⇒B

-- Multi-step term reduction preserves usage.

usagePres*Term : γ ▸[ m ] t → Γ ⊢ t ⇒* u ∷ A → γ ▸[ m ] u
usagePres*Term γ▸t (id x) = γ▸t
usagePres*Term γ▸t (x ⇨ t⇒u) = usagePres*Term (usagePresTerm γ▸t x) t⇒u

-- Multi-step type reduction preserves usage.

usagePres* : γ ▸[ m ] A → Γ ⊢ A ⇒* B → γ ▸[ m ] B
usagePres* γ▸A (id x) = γ▸A
usagePres* γ▸A (x ⇨ A⇒B) = usagePres* (usagePres γ▸A x) A⇒B

-- Note that reduction does not include η-expansion (for WHNFs, see
-- no-η-expansion-Unit and no-η-expansion-Σₚ in
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

-- If "Unit" is allowed, then variable 0 is well-typed and
-- well-resourced (with respect to the usage context ε ∙ 𝟙), and is
-- definitionally equal to the η-long normal form star. However, this
-- η-long normal form is well-resourced with respect to the usage
-- context ε ∙ 𝟙 if and only if 𝟙 ≤ 𝟘.

η-long-nf-for-0⇔𝟙≤𝟘 :
  Unit-allowed →
  let Γ = ε ∙ Unit
      γ = ε ∙ 𝟙
      A = Unit
      t = var x0
      u = star
  in
  Γ ⊢ t ∷ A ×
  γ ▸[ 𝟙ᵐ ] t ×
  Γ ⊢nf u ∷ A ×
  Γ ⊢ t ≡ u ∷ A ×
  (γ ▸[ 𝟙ᵐ ] u ⇔ 𝟙 ≤ 𝟘)
η-long-nf-for-0⇔𝟙≤𝟘 ok =
    ⊢0
  , var
  , starₙ (ε ∙ ⊢Unit) ok
  , sym (Unit-η ⊢0)
  , (λ ▸* →
       case inv-usage-star ▸* of λ {
         (_ ∙ 𝟙≤𝟘) →
       𝟙≤𝟘 })
  , (λ 𝟙≤𝟘 →
       sub starₘ $
       let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
         ε ∙ 𝟙  ≤⟨ ε ∙ 𝟙≤𝟘 ⟩
         ε ∙ 𝟘  ∎)
  where
  ⊢Unit = Unitⱼ ε ok
  ⊢0    = var (ε ∙ ⊢Unit) here

-- If "Π 𝟙 , p" and "Unit" are allowed, then the identity function
-- lam 𝟙 (var x0) has type Π 𝟙 , p ▷ Unit ▹ Unit, is well-resourced in
-- the empty context, and is definitionally equal to the η-long normal
-- form lam 𝟙 star, however, this η-long normal form is well-resourced
-- in the empty context if and only if 𝟙 ≤ 𝟘.

η-long-nf-for-id⇔𝟙≤𝟘 :
  Π-allowed 𝟙 p →
  Unit-allowed →
  let A = Π 𝟙 , p ▷ Unit ▹ Unit
      t = lam 𝟙 (var x0)
      u = lam 𝟙 star
  in
  ε ⊢ t ∷ A ×
  ε ▸[ 𝟙ᵐ ] t ×
  ε ⊢nf u ∷ A ×
  ε ⊢ t ≡ u ∷ A ×
  (ε ▸[ 𝟙ᵐ ] u ⇔ 𝟙 ≤ 𝟘)
η-long-nf-for-id⇔𝟙≤𝟘 ok₁ ok₂ =
  case η-long-nf-for-0⇔𝟙≤𝟘 ok₂ of λ {
    (⊢t , ▸t , ⊢u , t≡u , ▸u⇔) →
    lamⱼ ⊢Unit ⊢t ok₁
  , lamₘ (sub ▸t $
          let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
            𝟘ᶜ ∙ 𝟙 · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
            𝟘ᶜ ∙ 𝟙      ∎)
  , lamₙ ⊢Unit ⊢u ok₁
  , lam-cong t≡u ok₁
  , (ε ▸[ 𝟙ᵐ ] lam 𝟙 star    ⇔⟨ (λ ▸λ* → case inv-usage-lam ▸λ* of λ where
                                   (invUsageLam {δ = ε} ▸* _) → ▸*)
                              , lamₘ
                              ⟩
     ε ∙ 𝟙 · 𝟙 ▸[ 𝟙ᵐ ] star  ≡⟨ PE.cong (λ p → _ ∙ p ▸[ _ ] _) (·-identityˡ _) ⟩⇔
     ε ∙ 𝟙 ▸[ 𝟙ᵐ ] star      ⇔⟨ ▸u⇔ ⟩
     𝟙 ≤ 𝟘                   □⇔) }
  where
  ⊢Unit = Unitⱼ ε ok₂

-- The type
-- Well-resourced-normal-form-without-η-long-normal-form is
-- inhabited if the Unit type with η-equality is allowed, 𝟙 is not
-- bounded by 𝟘, and Π-allowed 𝟙 q holds for some q.

well-resourced-normal-form-without-η-long-normal-form-Unit :
  ¬ 𝟙 ≤ 𝟘 →
  Unit-allowed →
  Π-allowed 𝟙 q →
  Well-resourced-normal-form-without-η-long-normal-form
well-resourced-normal-form-without-η-long-normal-form-Unit 𝟙≰𝟘 ok₁ ok₂ =
  case η-long-nf-for-id⇔𝟙≤𝟘 ok₂ ok₁ of λ {
    (⊢t , ▸t , ⊢u , t≡u , ▸u→ , _) →
    _ , _
  , ⊢t
  , lamₙ (ne (var _))
  , ▸t
  , λ (v , ⊢v , t≡v , ▸v) →
                            $⟨ ▸v ⟩
      ε ▸[ 𝟙ᵐ ] v           →⟨ PE.subst (_ ▸[ _ ]_) (normal-terms-unique ⊢v ⊢u (trans (sym t≡v) t≡u)) ⟩
      ε ▸[ 𝟙ᵐ ] lam 𝟙 star  →⟨ ▸u→ ⟩
      𝟙 ≤ 𝟘                 →⟨ 𝟙≰𝟘 ⟩
      ⊥                     □ }

-- If "Σₚ p , q" is allowed, then variable 0 is well-typed and
-- well-resourced (with respect to the usage context ε ∙ 𝟙), and is
-- definitionally equal to the η-long normal form
-- prodₚ p (fst p (var x0)) (snd p (var x0)). However, this η-long
-- normal form is well-resourced with respect to the usage context
-- ε ∙ 𝟙 if and only if either p is 𝟙, or p is 𝟘, 𝟘ᵐ is allowed, and
-- 𝟙 ≤ 𝟘.

η-long-nf-for-0⇔≡𝟙⊎≡𝟘 :
  Σₚ-allowed p q →
  let Γ = ε ∙ (Σₚ p , q ▷ ℕ ▹ ℕ)
      γ = ε ∙ 𝟙
      A = Σₚ p , q ▷ ℕ ▹ ℕ
      t = var x0
      u = prodₚ p (fst p (var x0)) (snd p (var x0))
  in
  Γ ⊢ t ∷ A ×
  γ ▸[ 𝟙ᵐ ] t ×
  Γ ⊢nf u ∷ A ×
  Γ ⊢ t ≡ u ∷ A ×
  (γ ▸[ 𝟙ᵐ ] u ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘))
η-long-nf-for-0⇔≡𝟙⊎≡𝟘 {p = p} ok =
    ⊢0
  , var
  , prodₙ Σℕℕ⊢ℕ (ℕⱼ ε∙Σℕℕ∙ℕ)
      (neₙ ℕₙ (fstₙ Σℕℕ⊢ℕ Σℕℕ∙ℕ⊢ℕ (varₙ (ε ∙ ⊢Σℕℕ) here)))
      (neₙ ℕₙ (sndₙ Σℕℕ⊢ℕ Σℕℕ∙ℕ⊢ℕ (varₙ (ε ∙ ⊢Σℕℕ) here)))
      ok
  , sym (Σ-η-prod-fst-snd ⊢0)
  , (ε ∙ 𝟙 ▸[ 𝟙ᵐ ] u′                              ⇔⟨ lemma₁ ⟩
     (𝟙 ≤ p × (⌞ p ⌟ PE.≡ 𝟙ᵐ → p ≤ 𝟙))             ⇔⟨ id⇔ ×-cong-⇔ ⌞⌟≡𝟙→⇔⊎𝟘ᵐ×≡𝟘 ⟩
     (𝟙 ≤ p × (p ≤ 𝟙 ⊎ T 𝟘ᵐ-allowed × p PE.≡ 𝟘))   ⇔⟨ lemma₂ ⟩
     (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)  □⇔)
  where
  u′      = prodₚ p (fst p (var x0)) (snd p (var x0))
  ⊢Σℕℕ    = ΠΣⱼ (ℕⱼ ε) (ℕⱼ (ε ∙ ℕⱼ ε)) ok
  Σℕℕ⊢ℕ   = ℕⱼ (ε ∙ ⊢Σℕℕ)
  ε∙Σℕℕ∙ℕ = ε ∙ ⊢Σℕℕ ∙ Σℕℕ⊢ℕ
  Σℕℕ∙ℕ⊢ℕ = ℕⱼ ε∙Σℕℕ∙ℕ
  ⊢0      = var (ε ∙ ⊢Σℕℕ) here

  lemma₁ : ε ∙ 𝟙 ▸[ 𝟙ᵐ ] u′ ⇔ (𝟙 ≤ p × (⌞ p ⌟ PE.≡ 𝟙ᵐ → p ≤ 𝟙))
  lemma₁ =
      (λ ▸1,2 →
         let open Tools.Reasoning.PartialOrder ≤-poset in
         case inv-usage-prodₚ ▸1,2 of λ {
           (invUsageProdₚ {δ = _ ∙ q₁} {η = _ ∙ q₂} ▸1 _ (_ ∙ 𝟙≤pq₁∧q₂)) →
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
           (prodₚₘ (fstₘ 𝟙ᵐ var PE.refl ⌞p⌟≡𝟙→≤𝟙) (sndₘ var))
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

-- If "Π 𝟙 , r" and "Σₚ p , q" are allowed, then the identity function
-- lam 𝟙 (var x0) has type
-- Π 𝟙 , r ▷ Σₚ p , q ▷ ℕ ▹ ℕ ▹ Σₚ p , q ▷ ℕ ▹ ℕ, is well-resourced in
-- the empty context, and is definitionally equal to the η-long normal
-- form lam 𝟙 (prodₚ p (fst p (var x0)) (snd p (var x0))), however,
-- this η-long normal form is well-resourced in the empty context if
-- and only if either p is 𝟙, or p is 𝟘, 𝟘ᵐ is allowed, and 𝟙 ≤ 𝟘.

η-long-nf-for-id⇔≡𝟙⊎≡𝟘 :
  Π-allowed 𝟙 r →
  Σₚ-allowed p q →
  let A = Π 𝟙 , r ▷ Σₚ p , q ▷ ℕ ▹ ℕ ▹ Σₚ p , q ▷ ℕ ▹ ℕ
      t = lam 𝟙 (var x0)
      u = lam 𝟙 (prodₚ p (fst p (var x0)) (snd p (var x0)))
  in
  ε ⊢ t ∷ A ×
  ε ▸[ 𝟙ᵐ ] t ×
  ε ⊢nf u ∷ A ×
  ε ⊢ t ≡ u ∷ A ×
  (ε ▸[ 𝟙ᵐ ] u ⇔ (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘))
η-long-nf-for-id⇔≡𝟙⊎≡𝟘 {r = r} {p = p} {q = q} ok₁ ok₂ =
  case η-long-nf-for-0⇔≡𝟙⊎≡𝟘 ok₂ of λ {
    (⊢t , ▸t , ⊢u , t≡u , ▸u⇔) →
    lamⱼ ⊢Σℕℕ ⊢t ok₁
  , lamₘ (sub ▸t
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               𝟘ᶜ ∙ 𝟙 · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
               𝟘ᶜ ∙ 𝟙      ∎))
  , lamₙ ⊢Σℕℕ ⊢u ok₁
  , lam-cong t≡u ok₁
  , (ε ▸[ 𝟙ᵐ ] lam 𝟙 u′                            ⇔⟨ (λ ▸λ* → case inv-usage-lam ▸λ* of λ where
                                                         (invUsageLam {δ = ε} ▸* _) → ▸*)
                                                    , lamₘ
                                                    ⟩
     ε ∙ 𝟙 · 𝟙 ▸[ 𝟙ᵐ ] u′                          ≡⟨ PE.cong (λ p → _ ∙ p ▸[ _ ] _) (·-identityˡ _) ⟩⇔
     ε ∙ 𝟙 ▸[ 𝟙ᵐ ] u′                              ⇔⟨ ▸u⇔ ⟩
     (p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘)  □⇔) }
  where
  u′   = prodₚ p (fst p (var x0)) (snd p (var x0))
  ⊢Σℕℕ = ΠΣⱼ (ℕⱼ ε) (ℕⱼ (ε ∙ ℕⱼ ε)) ok₂

-- The type
-- Well-resourced-normal-form-without-η-long-normal-form is
-- inhabited if there are quantities p, q and r such that
-- * p is distinct from 𝟙,
-- * "p is 𝟘 and 𝟘ᵐ is allowed and 𝟙 ≤ 𝟘" does not hold,
-- * Σₚ-allowed p q holds, and
-- * Π-allowed 𝟙 r holds.

well-resourced-normal-form-without-η-long-normal-form-Σₚ :
  p ≢ 𝟙 →
  ¬ (p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘) →
  Σₚ-allowed p q →
  Π-allowed 𝟙 r →
  Well-resourced-normal-form-without-η-long-normal-form
well-resourced-normal-form-without-η-long-normal-form-Σₚ
  {p = p} p≢𝟙 ¬[p≡𝟘×𝟘ᵐ×𝟙≤𝟘] ok₁ ok₂ =
  case η-long-nf-for-id⇔≡𝟙⊎≡𝟘 ok₂ ok₁ of λ {
    (⊢t , ▸t , ⊢u , t≡u , ▸u→ , _) →
    _ , _
  , ⊢t
  , lamₙ (ne (var _))
  , ▸t
  , λ (v , ⊢v , t≡v , ▸v) →                                        $⟨ ▸v ⟩
      ε ▸[ 𝟙ᵐ ] v                                                  →⟨ PE.subst (_ ▸[ _ ]_) (normal-terms-unique ⊢v ⊢u (trans (sym t≡v) t≡u)) ⟩
      ε ▸[ 𝟙ᵐ ] lam 𝟙 (prodₚ p (fst p (var x0)) (snd p (var x0)))  →⟨ ▸u→ ⟩
      p PE.≡ 𝟙 ⊎ p PE.≡ 𝟘 × T 𝟘ᵐ-allowed × 𝟙 ≤ 𝟘                   →⟨ (λ { (inj₁ p≡𝟙) → p≢𝟙 p≡𝟙; (inj₂ hyp) → ¬[p≡𝟘×𝟘ᵐ×𝟙≤𝟘] hyp }) ⟩
      ⊥                                                            □ }
