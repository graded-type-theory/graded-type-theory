{-# OPTIONS --without-K --safe #-}

open import Tools.Level
open import Tools.Relation
open import Definition.Modality

module Definition.Typed.Usage
  {M : Set} {_≈_ : Rel M ℓ₀}
  (𝕄 : Modality M _≈_)
  where

open import Definition.Modality.Context 𝕄
open import Definition.Modality.Context.Properties 𝕄
open import Definition.Modality.Substitution.Properties 𝕄
open import Definition.Modality.Usage 𝕄
open import Definition.Modality.Usage.Inversion 𝕄
open import Definition.Typed M
open import Definition.Untyped M hiding (_∷_)
open import Definition.Usage 𝕄

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
usagePresTerm γ▸t (app-subst t⇒u x) with inv-usage-app γ▸t
... | invUsageApp δ▸t η▸a γ≤δ+pη = sub ((usagePresTerm δ▸t t⇒u) ∘ₘ η▸a) γ≤δ+pη
usagePresTerm γ▸λta (β-red x x₁ x₂ refl) with inv-usage-app γ▸λta
... | invUsageApp δ▸λt η▸a γ≤δ′+pη with inv-usage-lam δ▸λt
... | invUsageLam δ▸t δ′≤δ = sub
  (sgSubstₘ-lemma δ▸t η▸a)
  (≤ᶜ-trans γ≤δ′+pη (+ᶜ-monotoneˡ δ′≤δ))
usagePresTerm γ▸t (fst-subst x x₁ t⇒u) with inv-usage-fst γ▸t
... | invUsageProj 𝟘▸t γ≤𝟘 = sub (fstₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t (snd-subst x x₁ t⇒u) with inv-usage-snd γ▸t
... | invUsageProj 𝟘▸t γ≤𝟘 = sub (sndₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t′ (Σ-β₁ x x₁ x₂ x₃ x₄) with inv-usage-fst γ▸t′
... | invUsageProj 𝟘▸tu γ≤𝟘 with inv-usage-prod 𝟘▸tu
... | invUsageProd {δ = δ} {η} δ▸t η▸u refl 𝟘≤δ+η = sub δ▸t
  (≤ᶜ-trans γ≤𝟘 (proj₁ (+ᶜ-positive δ η 𝟘≤δ+η)))
usagePresTerm γ▸u′ (Σ-β₂ x x₁ x₂ x₃ x₄) with inv-usage-snd γ▸u′
... | invUsageProj 𝟘▸tu γ≤𝟘 with inv-usage-prod 𝟘▸tu
... | invUsageProd {δ = δ} {η} δ▸t η▸u refl 𝟘≤δ+η = sub η▸u
  (≤ᶜ-trans γ≤𝟘 (proj₂ (+ᶜ-positive δ η 𝟘≤δ+η)))
usagePresTerm γ▸ptu (prodrec-subst x x₁ x₂ x₃ t⇒t′) with inv-usage-prodrec γ▸ptu
... | invUsageProdrec δ▸t η▸u γ≤pδ+η = sub (prodrecₘ (usagePresTerm δ▸t t⇒t′) η▸u) γ≤pδ+η
usagePresTerm {γ = γ} γ▸ptu (prodrec-β {p = p} x x₁ x₂ x₃ x₄ x₅) with inv-usage-prodrec γ▸ptu
... | invUsageProdrec {δ} {η} δ▸tt′ η▸u γ≤pδ+η with inv-usage-prod δ▸tt′
... | invUsageProd {δ = δ′} {η = η′} δ′▸t η′▸t′ refl δ≤δ′+η′ = sub
  (doubleSubstₘ-lemma η▸u η′▸t′ δ′▸t)
  le
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  le = begin
      γ                       ≤⟨ γ≤pδ+η ⟩
      p ·ᶜ δ +ᶜ η             ≈⟨ +ᶜ-comm (p ·ᶜ δ) η ⟩
      η +ᶜ p ·ᶜ δ             ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ δ≤δ′+η′) ⟩
      η +ᶜ p ·ᶜ (δ′ +ᶜ η′)    ≈⟨ +ᶜ-cong ≈ᶜ-refl (·ᶜ-distribˡ-+ᶜ p δ′ η′) ⟩
      η +ᶜ p ·ᶜ δ′ +ᶜ p ·ᶜ η′ ≈⟨ +ᶜ-cong ≈ᶜ-refl (+ᶜ-comm (p ·ᶜ δ′) (p ·ᶜ η′)) ⟩
      η +ᶜ p ·ᶜ η′ +ᶜ p ·ᶜ δ′ ∎

usagePresTerm γ▸natrec (natrec-subst x x₁ x₂ t⇒u) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z η▸s θ▸n γ≤X = sub (natrecₘ δ▸z η▸s (usagePresTerm θ▸n t⇒u)) γ≤X

usagePresTerm γ▸natrec (natrec-zero {p = p} {r = r} x x₁ x₂) with inv-usage-natrec γ▸natrec
... | invUsageNatrec {δ = δ} {θ = θ} δ▸z η▸s θ▸n γ≤nr with inv-usage-zero θ▸n
... | θ≤𝟘 = sub δ▸z (≤ᶜ-trans γ≤nr nr≤δ)
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  nr≤δ = begin
    nrᶜ (δ ∧ᶜ θ) (_ +ᶜ p ·ᶜ _) r ≈⟨ nrᶜ-rec (δ ∧ᶜ θ) _ r ⟩
    (δ ∧ᶜ θ) ∧ᶜ _                ≤⟨ ∧ᶜ-decreasingˡ (δ ∧ᶜ θ) _ ⟩
    δ ∧ᶜ θ                       ≤⟨ ∧ᶜ-decreasingˡ δ θ ⟩
    δ                            ∎

usagePresTerm {γ = γ} γ▸natrec (natrec-suc {p = p} {r = r} x x₁ x₂ x₃) with inv-usage-natrec γ▸natrec
... | invUsageNatrec {δ = δ} {η} {θ} δ▸z η▸s θ▸sn γ≤γ′ with inv-usage-suc θ▸sn
... | invUsageSuc {δ = θ′} θ′▸n θ≤θ′ = sub
  (doubleSubstₘ-lemma η▸s (natrecₘ δ▸z η▸s (sub θ′▸n θ≤θ′)) θ′▸n)
  le
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  NR = nrᶜ (δ ∧ᶜ θ) (η +ᶜ p ·ᶜ θ) r
  le = begin
      γ       ≤⟨ γ≤γ′ ⟩
      NR      ≈⟨ nrᶜ-rec _ _ _ ⟩
      (δ ∧ᶜ θ) ∧ᶜ ((η +ᶜ p ·ᶜ θ) +ᶜ r ·ᶜ NR)
              ≤⟨ ∧ᶜ-decreasingʳ (δ ∧ᶜ θ) _ ⟩
      (η +ᶜ p ·ᶜ θ) +ᶜ r ·ᶜ NR
              ≈⟨ +ᶜ-assoc η (p ·ᶜ θ) (r ·ᶜ nrᶜ (δ ∧ᶜ θ) (η +ᶜ (p ·ᶜ θ)) r) ⟩
      η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ NR
              ≈⟨ +ᶜ-cong ≈ᶜ-refl (+ᶜ-comm (p ·ᶜ θ) (r ·ᶜ nrᶜ (δ ∧ᶜ θ) (η +ᶜ (p ·ᶜ θ)) r)) ⟩
      η +ᶜ r ·ᶜ NR +ᶜ p ·ᶜ θ
              ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneʳ θ≤θ′)) ⟩
      η +ᶜ r ·ᶜ NR +ᶜ p ·ᶜ θ′ ∎


usagePresTerm γ▸et (Emptyrec-subst x t⇒u) with inv-usage-Emptyrec γ▸et
... | invUsageEmptyrec δ▸t γ≤δ = sub (Emptyrecₘ (usagePresTerm δ▸t t⇒u)) γ≤δ

-- Type reduction preserves modality usage
-- If γ ▸ A and Γ ⊢ A ⇒ B, then γ ▸ B

usagePres : γ ▸ A → Γ ⊢ A ⇒ B → γ ▸ B
usagePres γ▸A (univ A⇒B) = usagePresTerm γ▸A A⇒B
