{-# OPTIONS --without-K --safe #-}

open import Tools.Relation
open import Definition.Modality

module Definition.Typed.Usage {a ℓ}
  {M′ : Setoid a ℓ} (𝕄 : Modality M′)
  where

open Modality 𝕄
open Setoid M′ renaming (Carrier to M)

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Properties 𝕄
open import Definition.Modality.Substitution.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Typed M′
open import Definition.Untyped M hiding (_∷_)

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE


private
  variable
    n : Nat
    Γ : Con Term n
    γ δ : Conₘ n
    t u A B : Term n

-- Subject reduction properties for modality usage

-- Term reduction preserves resource usage
-- If γ ▸ t and Γ ⊢ t ⇒ u ∷ A, then γ ▸ u

usagePresTerm : γ ▸ t → Γ ⊢ t ⇒ u ∷ A → γ ▸ u
usagePresTerm γ▸t (conv t⇒u x) = usagePresTerm γ▸t t⇒u
usagePresTerm γ▸t (app-subst t⇒u x) =
  let invUsageApp δ▸t η▸a γ≤δ+pη = inv-usage-app γ▸t
  in  sub ((usagePresTerm δ▸t t⇒u) ∘ₘ η▸a) γ≤δ+pη
usagePresTerm γ▸λta (β-red x x₁ x₂ x₃ x₄) =
  let invUsageApp δ▸λt η▸a γ≤δ′+pη = inv-usage-app γ▸λta
      invUsageLam δ▸t δ′≤δ = inv-usage-lam δ▸λt
  in  sub (sgSubstₘ-lemma δ▸t η▸a)
          (≤ᶜ-trans γ≤δ′+pη (+ᶜ-monotone δ′≤δ (·ᶜ-monotoneˡ (≤-reflexive (≈-sym x₄)))))
usagePresTerm γ▸t (fst-subst x x₁ t⇒u) =
  let invUsageProj 𝟘▸t γ≤𝟘 = inv-usage-fst γ▸t
  in  sub (fstₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t (snd-subst x x₁ t⇒u) =
  let invUsageProj 𝟘▸t γ≤𝟘 = inv-usage-snd γ▸t
  in  sub (sndₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t′ (Σ-β₁ x x₁ x₂ x₃ x₄) =
  let invUsageProj δ▸tu γ≤δ = inv-usage-fst γ▸t′
      invUsageProdₚ η▸t η▸u δ≤η = inv-usage-prodₚ δ▸tu
  in  sub η▸t (≤ᶜ-trans γ≤δ δ≤η)
usagePresTerm γ▸t′ (Σ-β₂ x x₁ x₂ x₃ x₄) =
  let invUsageProj δ▸tu γ≤δ = inv-usage-snd γ▸t′
      invUsageProdₚ η▸t η▸u δ≤η = inv-usage-prodₚ δ▸tu
  in  sub η▸u (≤ᶜ-trans γ≤δ δ≤η)

usagePresTerm γ▸natrec (natrec-subst x x₁ x₂ t⇒u) =
  let invUsageNatrec δ▸z η▸s θ▸n γ≤X = inv-usage-natrec γ▸natrec
  in  sub (natrecₘ δ▸z η▸s (usagePresTerm θ▸n t⇒u)) γ≤X

usagePresTerm γ▸natrec (natrec-zero {p = p} {r = r} x x₁ x₂) =
  let invUsageNatrec {δ = δ} {θ = θ} δ▸z η▸s θ▸n γ≤γ′ = inv-usage-natrec γ▸natrec
      θ≤𝟘 = inv-usage-zero θ▸n
      γ′≤δ = begin
        (δ ∧ᶜ θ) ⊛ᶜ (_ +ᶜ p ·ᶜ _) ▷ r ≤⟨ ⊛ᶜ-ineq₂ (δ ∧ᶜ θ) _ r ⟩
        δ ∧ᶜ θ                        ≤⟨ ∧ᶜ-decreasingˡ δ θ ⟩
        δ                             ∎
  in  sub δ▸z (≤ᶜ-trans γ≤γ′ γ′≤δ)
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

usagePresTerm {γ = γ} γ▸natrec (natrec-suc {p = p} {r = r} x x₁ x₂ x₃) =
  let invUsageNatrec {δ = δ} {η} {θ} δ▸z η▸s θ▸sn γ≤γ′ = inv-usage-natrec γ▸natrec
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
  in  sub (doubleSubstₘ-lemma η▸s (natrecₘ δ▸z η▸s (sub θ′▸n θ≤θ′)) θ′▸n) γ≤γ″
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

usagePresTerm γ▸prodrec (prodrec-subst x x₁ x₂ x₃ x₄) =
  let invUsageProdrec δ▸t η▸u γ≤γ′ = inv-usage-prodrec γ▸prodrec
  in  sub (prodrecₘ (usagePresTerm δ▸t x₄) η▸u) γ≤γ′
usagePresTerm {γ = γ} γ▸prodrec (prodrec-β {p = p} {t = t} {t′} {u} x x₁ x₂ x₃ x₄ x₅) =
  let invUsageProdrec {δ = δ} {η} δ▸t η▸u γ≤pδ+η = inv-usage-prodrec γ▸prodrec
      invUsageProdᵣ {δ = δ′} {η′} {θ} δ′▸t₁ η′▸t₂ γ″≡δ′+η′ γ′≤γ″ = inv-usage-prodᵣ δ▸t
      le = begin
        γ                      ≤⟨ γ≤pδ+η ⟩
        p ·ᶜ δ +ᶜ η            ≈⟨ +ᶜ-comm (p ·ᶜ δ) η ⟩
        η +ᶜ p ·ᶜ δ            ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ γ′≤γ″) ⟩
        η +ᶜ (p ·ᶜ θ)          ≡⟨ PE.cong (λ γ → η +ᶜ p ·ᶜ γ) γ″≡δ′+η′ ⟩
        η +ᶜ p ·ᶜ (δ′ +ᶜ η′)   ≈⟨ +ᶜ-congˡ (·ᶜ-distribˡ-+ᶜ p δ′ η′) ⟩
        η +ᶜ p ·ᶜ δ′ +ᶜ p ·ᶜ η′ ≈⟨ +ᶜ-congˡ (+ᶜ-comm (p ·ᶜ δ′) (p ·ᶜ η′)) ⟩
        η +ᶜ p ·ᶜ η′ +ᶜ p ·ᶜ δ′ ∎
  in  sub (doubleSubstₘ-lemma η▸u η′▸t₂ δ′▸t₁) le
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset

usagePresTerm γ▸et (Emptyrec-subst x t⇒u) =
  let invUsageEmptyrec δ▸t γ≤δ = inv-usage-Emptyrec γ▸et
  in  sub (Emptyrecₘ (usagePresTerm δ▸t t⇒u)) γ≤δ

-- Type reduction preserves modality usage
-- If γ ▸ A and Γ ⊢ A ⇒ B, then γ ▸ B

usagePres : γ ▸ A → Γ ⊢ A ⇒ B → γ ▸ B
usagePres γ▸A (univ A⇒B) = usagePresTerm γ▸A A⇒B

-- Term reduction closeure preserves modality usage
-- If γ ▸ t and Γ ⊢ t ⇒* u ∷ A then γ ▸ u

usagePres*Term : γ ▸ t → Γ ⊢ t ⇒* u ∷ A → γ ▸ u
usagePres*Term γ▸t (id x) = γ▸t
usagePres*Term γ▸t (x ⇨ t⇒u) = usagePres*Term (usagePresTerm γ▸t x) t⇒u

-- Type reduction closeure preserves modality usage
-- If γ ▸ A and Γ ⊢ A ⇒* B then γ ▸ B

usagePres* : γ ▸ A → Γ ⊢ A ⇒* B → γ ▸ B
usagePres* γ▸A (id x) = γ▸A
usagePres* γ▸A (x ⇨ A⇒B) = usagePres* (usagePres γ▸A x) A⇒B
