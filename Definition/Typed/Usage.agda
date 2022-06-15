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
usagePresTerm γ▸t (app-subst t⇒u x) with inv-usage-app γ▸t
... | invUsageApp δ▸t η▸a γ≤δ+pη =
  sub ((usagePresTerm δ▸t t⇒u) ∘ₘ η▸a) γ≤δ+pη
usagePresTerm γ▸λta (β-red x x₁ x₂ x₃ x₄) with inv-usage-app γ▸λta
... | invUsageApp δ▸λt η▸a γ≤δ′+pη with inv-usage-lam δ▸λt
... | invUsageLam δ▸t δ′≤δ =
  sub (sgSubstₘ-lemma δ▸t η▸a)
      (≤ᶜ-trans γ≤δ′+pη
                (+ᶜ-monotone δ′≤δ (·ᶜ-monotoneˡ (≤-reflexive (≈-sym x₄)))))
usagePresTerm γ▸t (fst-subst x x₁ t⇒u) with inv-usage-fst γ▸t
... | invUsageProj 𝟘▸t γ≤𝟘 =
  sub (fstₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t (snd-subst x x₁ t⇒u) with inv-usage-snd γ▸t
... | invUsageProj 𝟘▸t γ≤𝟘 =
  sub (sndₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t′ (Σ-β₁ x x₁ x₂ x₃ x₄) with inv-usage-fst γ▸t′
... | invUsageProj 𝟘▸tu γ≤𝟘 with inv-usage-prod 𝟘▸tu
... | invUsageProd {δ = δ} {η} δ▸t η▸u refl 𝟘≤δ+η =
  sub δ▸t (≤ᶜ-trans γ≤𝟘 (proj₁ (+ᶜ-positive δ η 𝟘≤δ+η)))
usagePresTerm γ▸u′ (Σ-β₂ x x₁ x₂ x₃ x₄) with inv-usage-snd γ▸u′
... | invUsageProj 𝟘▸tu γ≤𝟘 with inv-usage-prod 𝟘▸tu
... | invUsageProd {δ = δ} {η} δ▸t η▸u refl 𝟘≤δ+η =
  sub η▸u (≤ᶜ-trans γ≤𝟘 (proj₂ (+ᶜ-positive δ η 𝟘≤δ+η)))

usagePresTerm γ▸natrec (natrec-subst x x₁ x₂ t⇒u) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z η▸s θ▸n γ≤X = sub (natrecₘ δ▸z η▸s (usagePresTerm θ▸n t⇒u)) γ≤X

usagePresTerm γ▸natrec (natrec-zero {p = p} {r = r} x x₁ x₂) with inv-usage-natrec γ▸natrec
... | invUsageNatrec {δ = δ} {θ = θ} δ▸z η▸s θ▸n γ≤γ′ with inv-usage-zero θ▸n
... | θ≤𝟘 = sub δ▸z (≤ᶜ-trans γ≤γ′ γ′≤δ)
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  γ′≤δ = begin
    (δ ∧ᶜ θ) ⊛ᶜ (_ +ᶜ p ·ᶜ _) ▷ r ≤⟨ ⊛ᶜ-ineq₂ (δ ∧ᶜ θ) _ r ⟩
    δ ∧ᶜ θ                        ≤⟨ ∧ᶜ-decreasingˡ δ θ ⟩
    δ                             ∎

usagePresTerm {γ = γ} γ▸natrec (natrec-suc {p = p} {r = r} x x₁ x₂ x₃) with inv-usage-natrec γ▸natrec
... | invUsageNatrec {δ = δ} {η} {θ} δ▸z η▸s θ▸sn γ≤γ′ with inv-usage-suc θ▸sn
... | invUsageSuc {δ = θ′} θ′▸n θ≤θ′ =
  sub (doubleSubstₘ-lemma η▸s (natrecₘ δ▸z η▸s (sub θ′▸n θ≤θ′)) θ′▸n) γ≤γ″
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  γ′ = (δ ∧ᶜ θ) ⊛ᶜ (η +ᶜ p ·ᶜ θ) ▷ r
  γ≤γ″ = begin
      γ       ≤⟨ γ≤γ′ ⟩
      γ′      ≤⟨ ⊛ᶜ-ineq₁ _ _ _ ⟩
      (η +ᶜ p ·ᶜ θ) +ᶜ r ·ᶜ γ′
              ≈⟨ +ᶜ-assoc η (p ·ᶜ θ) (r ·ᶜ (δ ∧ᶜ θ) ⊛ᶜ (η +ᶜ (p ·ᶜ θ)) ▷ r) ⟩
      η +ᶜ p ·ᶜ θ +ᶜ r ·ᶜ γ′
              ≈⟨ +ᶜ-cong ≈ᶜ-refl (+ᶜ-comm (p ·ᶜ θ) (r ·ᶜ (δ ∧ᶜ θ) ⊛ᶜ (η +ᶜ (p ·ᶜ θ)) ▷ r)) ⟩
      η +ᶜ r ·ᶜ γ′ +ᶜ p ·ᶜ θ
              ≤⟨ +ᶜ-monotoneʳ (+ᶜ-monotoneʳ (·ᶜ-monotoneʳ θ≤θ′)) ⟩
      η +ᶜ r ·ᶜ γ′ +ᶜ p ·ᶜ θ′ ∎

usagePresTerm γ▸prodrec (prodrec-subst x x₁ x₂ x₃ x₄) with inv-usage-prodrec γ▸prodrec
... | invUsageProdrec δ▸t η▸u γ≤γ′ = sub (prodrecₘ (usagePresTerm δ▸t x₄) η▸u) γ≤γ′
usagePresTerm {γ = γ} γ▸prodrec (prodrec-β {p = p} {t = t} {t′} {u} x x₁ x₂ x₃ x₄ x₅)
  with inv-usage-prodrec γ▸prodrec
... | invUsageProdrec {δ = δ} {η} δ▸t η▸u γ≤γ′ with inv-usage-prod δ▸t
... | invUsageProd {δ = δ′} {η′} δ▸t₁ η▸t₂ PE.refl γ′≤γ″ =
  sub (doubleSubstₘ-lemma η▸u η▸t₂ δ▸t₁) le
  where
  open import Tools.Reasoning.PartialOrder ≤ᶜ-poset
  le = begin
    γ                      ≤⟨ γ≤γ′ ⟩
    p ·ᶜ δ +ᶜ η            ≈⟨ +ᶜ-comm (p ·ᶜ δ) η ⟩
    η +ᶜ p ·ᶜ δ            ≤⟨ +ᶜ-monotoneʳ (·ᶜ-monotoneʳ γ′≤γ″) ⟩
    η +ᶜ p ·ᶜ (δ′ +ᶜ η′)   ≈⟨ +ᶜ-cong ≈ᶜ-refl (·ᶜ-distribˡ-+ᶜ p δ′ η′) ⟩
    η +ᶜ p ·ᶜ δ′ +ᶜ p ·ᶜ η′ ≈⟨ +ᶜ-cong ≈ᶜ-refl (+ᶜ-comm (p ·ᶜ δ′) (p ·ᶜ η′)) ⟩
    η +ᶜ p ·ᶜ η′ +ᶜ p ·ᶜ δ′ ∎

usagePresTerm γ▸et (Emptyrec-subst x t⇒u) with inv-usage-Emptyrec γ▸et
... | invUsageEmptyrec δ▸t γ≤δ = sub (Emptyrecₘ (usagePresTerm δ▸t t⇒u)) γ≤δ

-- Type reduction preserves modality usage
-- If γ ▸ A and Γ ⊢ A ⇒ B, then γ ▸ B

usagePres : γ ▸ A → Γ ⊢ A ⇒ B → γ ▸ B
usagePres γ▸A (univ A⇒B) = usagePresTerm γ▸A A⇒B

open import Tools.Fin
fst′ : Term (1+ n) → Term n → Term n
fst′ A t = prodrec 𝟙 A t (var (x0 +1))

snd′ : Term n
snd′ = lam {!!} (lam {!!} (lam 𝟙 (prodrec 𝟙 (var (x0 +1 +1)) (var x0) (var x0))))


foo : γ ▸ t → γ ▸ fst′ A t
foo ▸t = sub (prodrecₘ ▸t (sub var {!!})) {!!} --prodrecₘ ▸t (sub var ((? ∙ ≤-refl) ∙ {!𝟙≤𝟘!})) -- ε ∙ 𝟙 ∙ 𝟙 ≤ 𝟘ᶜ , x1 ≔ 𝟙

⊢snd′ : ⊢ Γ → Γ ⊢ snd′ ∷ (Π 𝟘 , 𝟙 ▷ U ▹ (Π 𝟘 , 𝟙 ▷ U ▹ (Π 𝟙 , 𝟙 ▷ Σ _ ▷ (var (x0 +1)) ▹ (var (x0 +1)) ▹ var (x0 +1))))
-- (Π {!!} , {!!} ▷ U ▹ (Π {!!} , {!!} ▷ U ▹ (Π {!!} , {!!} ▷ (Σ {!!} ▷ (var (x0 +1 +1)) ▹ (var x0 +1)) ▹ (var (x0 +1)))))
⊢snd′ ⊢Γ =
  let
      Γ⊢U = Uⱼ ⊢Γ
      ⊢ΓU = ⊢Γ ∙ Γ⊢U
      ΓU⊢U = Uⱼ ⊢ΓU
      ⊢ΓUU = ⊢ΓU ∙ ΓU⊢U
      ΓUU⊢x₁ = univ (var ⊢ΓUU (there here))
      ΓUUx₁⊢x₁ = univ (var (⊢ΓUU ∙ ΓUU⊢x₁) (there here))
      ΓUU⊢Σ = Σⱼ ΓUU⊢x₁ ▹ ΓUUx₁⊢x₁
      ⊢ΓUUΣ = ⊢ΓUU ∙ ΓUU⊢Σ
      ΓUUΣ⊢x₂ = var ⊢ΓUUΣ (there (there here))
  in  lamⱼ Γ⊢U (lamⱼ ΓU⊢U (lamⱼ ΓUU⊢Σ
           (prodrecⱼ (univ ΓUUΣ⊢x₂)
                     (univ (var (⊢ΓUUΣ ∙ univ ΓUUΣ⊢x₂) (there (there here))))
                     (univ (var (⊢ΓUUΣ ∙ (Σⱼ (univ ΓUUΣ⊢x₂) ▹ (univ (var (⊢ΓUUΣ ∙ univ ΓUUΣ⊢x₂) (there (there here)))))) (there (there here))))
                     (var ⊢ΓUUΣ here)
                     (var (⊢ΓUUΣ ∙ univ ΓUUΣ⊢x₂ ∙ univ (var (⊢ΓUUΣ ∙ univ ΓUUΣ⊢x₂) (there (there here)))) here))))

bound : ∀ p → p ≤ 𝟘
bound = {!!}

boundᶜ : γ ≤ᶜ 𝟘ᶜ
boundᶜ = {!!}

▸snd′ : ∃ λ γ → γ ▸ snd′
▸snd′ = 𝟘ᶜ , (lamₘ (lamₘ (lamₘ (sub (prodrecₘ var (sub var ((boundᶜ ∙ bound 𝟙) ∙ ≤-refl))) ({!!} ∙ {!!} ∙ {!!})))))
