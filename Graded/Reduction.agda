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

open import Definition.Conversion.FullReduction TR
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

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE
  using (≈-sym)
import Tools.Reasoning.PartialOrder

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
  in  sub (sgSubstₘ-lemma₂ δ▸t (▸-cong (ᵐ·-cong m (≈-sym x₄)) η▸a))
          (≤ᶜ-trans γ≤δ′+pη (+ᶜ-monotone δ′≤δ (·ᶜ-monotoneˡ (≤-reflexive (≈-sym x₄)))))
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
  let invUsageNatrec δ▸z η▸s θ▸n φ▸A γ≤X = inv-usage-natrec γ▸natrec
  in  sub (natrecₘ δ▸z η▸s (usagePresTerm θ▸n t⇒u) φ▸A) γ≤X

usagePresTerm γ▸natrec (natrec-zero {p = p} {r = r} x x₁ x₂) =
  let invUsageNatrec {δ = δ} {θ = θ} δ▸z η▸s θ▸n φ▸A γ≤γ′ = inv-usage-natrec γ▸natrec
      θ≤𝟘 = inv-usage-zero θ▸n
      γ′≤δ = begin
        (δ ∧ᶜ θ) ⊛ᶜ (_ +ᶜ p ·ᶜ _) ▷ r ≤⟨ ⊛ᶜ-ineq₂ (δ ∧ᶜ θ) _ r ⟩
        δ ∧ᶜ θ                        ≤⟨ ∧ᶜ-decreasingˡ δ θ ⟩
        δ                             ∎
  in  sub δ▸z (≤ᶜ-trans γ≤γ′ γ′≤δ)
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

usagePresTerm {γ = γ} γ▸natrec (natrec-suc {p = p} {r = r} x x₁ x₂ x₃) =
  let invUsageNatrec {δ = δ} {η} {θ} δ▸z η▸s θ▸sn φ▸A γ≤γ′ = inv-usage-natrec γ▸natrec
      invUsageSuc {δ = θ′} θ′▸n θ≤θ′ = inv-usage-suc θ▸sn
      γ′ = (δ ∧ᶜ θ) ⊛ᶜ (η +ᶜ p ·ᶜ θ) ▷ r
      γ≤γ″ = begin
        γ       ≤⟨ γ≤γ′ ⟩
        γ′      ≤⟨ ⊛ᶜ-ineq₁ _ _ _ ⟩
        (η +ᶜ p ·ᶜ θ) +ᶜ r ·ᶜ γ′
                ≈⟨ +ᶜ-assoc η (p ·ᶜ θ) (r ·ᶜ (δ ∧ᶜ θ) ⊛ᶜ (η +ᶜ (p ·ᶜ θ)) ▷ r) ⟩
        η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ γ′
               ≈⟨ +ᶜ-congˡ (+ᶜ-comm (p ·ᶜ θ) (r ·ᶜ (δ ∧ᶜ θ) ⊛ᶜ (η +ᶜ (p ·ᶜ θ)) ▷ r)) ⟩
        η +ᶜ r ·ᶜ γ′ +ᶜ p ·ᶜ θ
               ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneʳ θ≤θ′)) ⟩
        η +ᶜ r ·ᶜ γ′ +ᶜ p ·ᶜ θ′ ∎
  in  sub (doubleSubstₘ-lemma₃ η▸s
             (natrecₘ δ▸z η▸s (sub θ′▸n θ≤θ′) φ▸A) θ′▸n)
        γ≤γ″
  where
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

usagePresTerm γ▸et (Emptyrec-subst x t⇒u) =
  let invUsageEmptyrec δ▸t η▸A γ≤δ = inv-usage-Emptyrec γ▸et
  in  sub (Emptyrecₘ (usagePresTerm δ▸t t⇒u) η▸A) γ≤δ

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
-- Definition.Typed.Properties). In Definition.Modality.FullReduction
-- it is proved that a well-resourced term has a well-resourced η-long
-- normal form, *given certain assumptions*. Here it is proved that,
-- given certain assumptions, the type
-- Well-resourced-normal-form-ill-resourced-η-long-normal-form is
-- inhabited: there is a type A and two closed terms t and u such that
-- t is a normal form of type A, u is an η-long normal form of type A,
-- t is definitionally equal to u, t is well-resourced, and u is *not*
-- well-resourced.

Well-resourced-normal-form-ill-resourced-η-long-normal-form : Set a
Well-resourced-normal-form-ill-resourced-η-long-normal-form =
  ∃₃ λ A t u →
    ε ⊢ t ∷ A × Nf t ×
    ε ⊢nf u ∷ A ×
    ε ⊢ t ≡ u ∷ A ×
    ε ▸[ 𝟙ᵐ ] t ×
    ¬ ε ▸[ 𝟙ᵐ ] u

-- The type
-- Well-resourced-normal-form-ill-resourced-η-long-normal-form is
-- inhabited if the Unit type with η-equality is allowed, 𝟙 is not
-- bounded by 𝟘, and Π-restriction 𝟙 q holds for some q.

well-resourced-normal-form-ill-resourced-η-long-normal-form-Unit :
  ¬ 𝟙 ≤ 𝟘 →
  Unit-restriction →
  Π-restriction 𝟙 q →
  Well-resourced-normal-form-ill-resourced-η-long-normal-form
well-resourced-normal-form-ill-resourced-η-long-normal-form-Unit
  {q = q} 𝟙≰𝟘 ok₁ ok₂ =
    Π 𝟙 , q ▷ Unit ▹ Unit
  , lam 𝟙 (var x0)
  , lam 𝟙 star
  , lamⱼ ⊢Unit ⊢0 ok₂
  , lamₙ (ne (var _))
  , lamₙ ⊢Unit (starₙ (ε ∙ ⊢Unit) ok₁) ok₂
  , lam-cong (sym (Unit-η ⊢0)) ok₂
  , lamₘ (sub var
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               𝟘ᶜ ∙ 𝟙 · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
               𝟘ᶜ ∙ 𝟙      ∎))
  , (λ ▸λ* →
       case inv-usage-lam ▸λ* of λ {
         (invUsageLam ▸* _) →
       case inv-usage-star ▸* of λ {
         (_ ∙ 𝟙·𝟙≤𝟘) →
           let open Tools.Reasoning.PartialOrder ≤-poset in
           𝟙≰𝟘 (begin
             𝟙      ≡˘⟨ ·-identityˡ _ ⟩
             𝟙 · 𝟙  ≤⟨ 𝟙·𝟙≤𝟘 ⟩
             𝟘      ∎) }})
  where
  ⊢Unit = Unitⱼ ε ok₁
  ⊢0    = var (ε ∙ ⊢Unit) here

-- The type
-- Well-resourced-normal-form-ill-resourced-η-long-normal-form is
-- inhabited if Σₚ-restriction p q holds for a quantity p that is not
-- an upper bound of 𝟙, and furthermore Π-restriction 𝟙 r holds.

well-resourced-normal-form-ill-resourced-η-long-normal-form-Σₚ :
  ¬ 𝟙 ≤ p →
  Σₚ-restriction p q →
  Π-restriction 𝟙 r →
  Well-resourced-normal-form-ill-resourced-η-long-normal-form
well-resourced-normal-form-ill-resourced-η-long-normal-form-Σₚ
  {p = p} {q = q} {r = r} 𝟙≰p ok₁ ok₂ =
    Π 𝟙 , r ▷ Σₚ p , q ▷ ℕ ▹ ℕ ▹ Σₚ p , q ▷ ℕ ▹ ℕ
  , lam 𝟙 (var x0)
  , lam 𝟙 (prodₚ p (fst p (var x0)) (snd p (var x0)))
  , lamⱼ ⊢Σℕℕ ⊢0 ok₂
  , lamₙ (ne (var _))
  , lamₙ ⊢Σℕℕ
      (prodₙ Σℕℕ⊢ℕ (ℕⱼ ε∙Σℕℕ∙ℕ)
         (neₙ ℕₙ (fstₙ Σℕℕ⊢ℕ Σℕℕ∙ℕ⊢ℕ (varₙ (ε ∙ ⊢Σℕℕ) here)))
         (neₙ ℕₙ (sndₙ Σℕℕ⊢ℕ Σℕℕ∙ℕ⊢ℕ (varₙ (ε ∙ ⊢Σℕℕ) here)))
         ok₁)
      ok₂
  , lam-cong (sym (Σ-η-prod-fst-snd ⊢0)) ok₂
  , lamₘ (sub var
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               𝟘ᶜ ∙ 𝟙 · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
               𝟘ᶜ ∙ 𝟙      ∎))
  , (λ ▸λ1,2 →
       let open Tools.Reasoning.PartialOrder ≤-poset in
       case inv-usage-lam ▸λ1,2 of λ {
         (invUsageLam ▸1,2 _) →
       case inv-usage-prodₚ ▸1,2 of λ {
         (invUsageProdₚ {δ = _ ∙ q₁} {η = _ ∙ q₂} ▸1 _ (_ ∙ 𝟙𝟙≤pq₁∧q₂)) →
       case inv-usage-fst ▸1 of λ {
         (invUsageFst {δ = _ ∙ q₃} _ _ ▸0 (_ ∙ q₁≤q₃) _) →
       case inv-usage-var ▸0 of λ {
         (_ ∙ q₃≤⌜⌞p⌟⌝) →
              $⟨ begin
                   𝟙              ≡˘⟨ ·-identityˡ _ ⟩
                   𝟙 · 𝟙          ≤⟨ 𝟙𝟙≤pq₁∧q₂ ⟩
                   p · q₁ ∧ q₂    ≤⟨ ∧-decreasingˡ _ _ ⟩
                   p · q₁         ≤⟨ ·-monotoneʳ q₁≤q₃ ⟩
                   p · q₃         ≤⟨ ·-monotoneʳ q₃≤⌜⌞p⌟⌝ ⟩
                   p · ⌜ ⌞ p ⌟ ⌝  ≡⟨ ·⌜⌞⌟⌝ ⟩
                   p              ∎ ⟩
       𝟙 ≤ p  →⟨ 𝟙≰p ⟩
       ⊥      □ }}}})
  where
  ⊢Σℕℕ    = ΠΣⱼ (ℕⱼ ε) (ℕⱼ (ε ∙ ℕⱼ ε)) ok₁
  Σℕℕ⊢ℕ   = ℕⱼ (ε ∙ ⊢Σℕℕ)
  ε∙Σℕℕ∙ℕ = ε ∙ ⊢Σℕℕ ∙ Σℕℕ⊢ℕ
  Σℕℕ∙ℕ⊢ℕ = ℕⱼ ε∙Σℕℕ∙ℕ
  ⊢0      = var (ε ∙ ⊢Σℕℕ) here
