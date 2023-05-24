open import Definition.Modality

module Definition.Typed.Usage
  {a} {M : Set a} (𝕄 : Modality M) where

open Modality 𝕄

open import Definition.Conversion.FullReduction M
open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Substitution.Properties 𝕄
open import Definition.Modality.Usage 𝕄
import Definition.Modality.Usage.Erased 𝕄 as EU
import Definition.Modality.Usage.Unrestricted.Eta 𝕄 as UU
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Modality.Usage.Properties 𝕄
open import Definition.Mode 𝕄
open import Definition.Typed M
open import Definition.Typed.Consequences.DerivedRules M
import Definition.Typed.Erased 𝕄 as ET
import Definition.Typed.Unrestricted.Eta 𝕄 as UT
open import Definition.Untyped M hiding (_∷_; _[_])
open import Definition.Untyped.Erased 𝕄 as E using (Erased)
import Definition.Untyped.Unrestricted.Eta 𝕄 as U

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE
  using (≈-sym)
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  variable
    n : Nat
    Γ : Con Term n
    γ δ : Conₘ n
    t u A B : Term n
    m : Mode

-- Subject reduction properties for modality usage

-- Term reduction preserves usage.

usagePresTerm : γ ▸[ m ] t → Γ ⊢ t ⇒ u ∷ A → γ ▸[ m ] u
usagePresTerm γ▸t (conv t⇒u x) = usagePresTerm γ▸t t⇒u
usagePresTerm γ▸t (app-subst t⇒u x) =
  let invUsageApp δ▸t η▸a γ≤δ+pη = inv-usage-app γ▸t
  in  sub ((usagePresTerm δ▸t t⇒u) ∘ₘ η▸a) γ≤δ+pη
usagePresTerm {m = m} γ▸λta (β-red x x₁ x₂ x₃ x₄) =
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
usagePresTerm {γ = γ} {m′} ▸t′ (Σ-β₁ {p = p} {t = t} _ _ _ _ PE.refl) =
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

usagePresTerm {γ = γ} ▸t′ (Σ-β₂ {p = p} _ _ _ _ PE.refl) =
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

usagePresTerm γ▸prodrec (prodrec-subst x x₁ x₂ x₃ x₄) =
  let invUsageProdrec δ▸t η▸u θ▸A P γ≤γ′ = inv-usage-prodrec γ▸prodrec
  in  sub (prodrecₘ (usagePresTerm δ▸t x₄) η▸u θ▸A P) γ≤γ′
usagePresTerm
  {γ = γ} {m = m} γ▸prodrec
  (prodrec-β {p = p} {r = r} {t = t} {t′ = t′} {u = u}
     _ _ _ _ _ _ PE.refl) =
  case inv-usage-prodrec γ▸prodrec of λ where
    (invUsageProdrec {δ = δ} {η = η} ▸t ▸u _ ok γ≤rδ+η) →
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

-- Note that reduction does not include η-expansion. If 𝟙 ≰ 𝟘, then
-- there is a well-resourced, closed term in normal form which is
-- definitionally equal to a term in normal form which is not
-- well-resourced.

counterexample₁ :
  ¬ 𝟙 ≤ 𝟘 →
  ∃₂ λ t u →
    (∀ p → ε ⊢ t ∷ Π 𝟙 , p ▷ Erased ℕ ▹ Erased ℕ) ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    Nf t ×
    Nf u ×
    (∀ p → ε ⊢ t ≡ u ∷ Π 𝟙 , p ▷ Erased ℕ ▹ Erased ℕ) ×
    ¬ ∃ λ γ → γ ▸[ 𝟙ᵐ ] u
counterexample₁ 𝟙≰𝟘 =
    lam 𝟙 (var x0)
  , lam 𝟙 [ erased (var x0) ]
  , (λ _ → lamⱼ ⊢E-ℕ ⊢0)
  , lamₘ (sub var
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               𝟘ᶜ ∙ 𝟙 · 𝟙  ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
               𝟘ᶜ ∙ 𝟙      ∎))
  , lamₙ (ne (var _))
  , lamₙ (prodₙ (ne (fstₙ (var _))) starₙ)
  , (λ _ → lam-cong (_⊢_≡_∷_.sym ([erased] ⊢0)))
  , (λ (_ , ▸λ[e0]) →
       case inv-usage-lam ▸λ[e0] of
         λ (invUsageLam ▸[e0] _) →
       case inv-usage-[] ▸[e0] of λ where
         (_ , _ ∙ 𝟙·𝟙≤𝟘) →
           let open Tools.Reasoning.PartialOrder ≤-poset in
           𝟙≰𝟘 (begin
             𝟙      ≡˘⟨ ·-identityʳ _ ⟩
             𝟙 · 𝟙  ≤⟨ 𝟙·𝟙≤𝟘 ⟩
             𝟘      ∎))
  where
  open E
  open ET
  open EU

  ⊢E-ℕ = Erasedⱼ (ℕⱼ ε)
  ⊢0   = var (ε ∙ ⊢E-ℕ) here

-- A variant of the previous property. If there is some quantity
-- strictly below both 𝟘 and some quantity that is bounded by 𝟙, then
-- there is a well-resourced, closed term in normal form which is
-- definitionally equal to a term in normal form which is not
-- well-resourced.

counterexample₂ :
  ∀ ω → ω < 𝟘 →
  ∀ p → ω < p → p ≤ 𝟙 →
  let open U ω in
  ∃₂ λ t u →
    (∀ q → ε ⊢ t ∷ Π p , q ▷ Unrestricted ℕ ▹ Unrestricted ℕ) ×
    𝟘ᶜ ▸[ 𝟙ᵐ ] t ×
    Nf t ×
    Nf u ×
    (∀ q → ε ⊢ t ≡ u ∷ Π p , q ▷ Unrestricted ℕ ▹ Unrestricted ℕ) ×
    ¬ ∃ λ γ → γ ▸[ 𝟙ᵐ ] u
counterexample₂ ω ω<𝟘 p ω<p p≤𝟙 =
    lam p (var x0)
  , lam p [ unbox (var x0) ]
  , (λ _ → lamⱼ ⊢E-ℕ ⊢0)
  , lamₘ (sub var
            (let open Tools.Reasoning.PartialOrder ≤ᶜ-poset in begin
               𝟘ᶜ ∙ 𝟙 · p  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
               𝟘ᶜ ∙ p      ≤⟨ ≤ᶜ-refl ∙ p≤𝟙 ⟩
               𝟘ᶜ ∙ 𝟙      ∎))
  , lamₙ (ne (var _))
  , lamₙ (prodₙ (ne (fstₙ (var _))) starₙ)
  , (λ _ → lam-cong (_⊢_≡_∷_.sym ([unbox] ⊢0)))
  , (λ (_ , ▸λ[e0]) →
       let open Tools.Reasoning.PartialOrder ≤-poset in
       case inv-usage-lam ▸λ[e0] of
         λ (invUsageLam ▸[e0] _) →
       case inv-usage-[] ▸[e0] of λ {
         (_ ∙ q , ▸unbox , _ ∙ 𝟙·p≤ω·q) →
              $⟨ begin
                   p      ≈˘⟨ ·-identityˡ _ ⟩
                   𝟙 · p  ≤⟨ 𝟙·p≤ω·q ⟩
                   ω · q  ≤⟨ ·-monotoneʳ (headₘ-monotone (inv-usage-var (inv-usage-unbox ▸unbox))) ⟩
                   ω · 𝟙  ≈⟨ ·-identityʳ _ ⟩
                   ω      ∎ ⟩
       p ≤ ω  →⟨ <→≰ ω<p ⟩
       ⊥      □ })
  where
  ω≤𝟙 = begin
    ω  ≤⟨ ω<p .proj₁ ⟩
    p  ≤⟨ p≤𝟙 ⟩
    𝟙  ∎
    where
    open Tools.Reasoning.PartialOrder ≤-poset

  open U ω
  open UT ω
  open UU ω ω<𝟘 ω≤𝟙

  ⊢E-ℕ = Unrestrictedⱼ (ℕⱼ ε)
  ⊢0   = var (ε ∙ ⊢E-ℕ) here
