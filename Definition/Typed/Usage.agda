{- #OPTIONS --without-K --safe #-}
module Definition.Typed.Usage where

open import Definition.Modality
open import Definition.Modality.Context
open import Definition.Modality.Context.Properties
open import Definition.Modality.Properties
open import Definition.Modality.Substitution.Properties
open import Definition.Modality.Usage
open import Definition.Modality.Usage.Inversion
open import Definition.Typed
open import Definition.Untyped hiding (_∷_)

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE


private
  variable
    n : Nat
    M : Set

-- Reduction preserves resource usage

usagePresTerm : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {Γ : Con (Term M) n} {t u A : Term M n}
              → γ ▸ t → Γ ⊢ t ⇒ u ∷ A → γ ▸ u
usagePresTerm γ▸t (conv t⇒u x) = usagePresTerm γ▸t t⇒u
usagePresTerm γ▸t (app-subst t⇒u x) with inv-usage-app γ▸t
... | invUsageApp δ▸t η▸a γ≤δ+pη = sub ((usagePresTerm δ▸t t⇒u) ∘ₘ η▸a) γ≤δ+pη
usagePresTerm γ▸λta (β-red x x₁ x₂ refl) with inv-usage-app γ▸λta
... | invUsageApp δ▸λt η▸a γ≤δ′+pη with inv-usage-lam δ▸λt
... | invUsageLam δ▸t δ′≤δ = sub (sgSubstₘ-lemma δ▸t η▸a) (≤ᶜ-transitive γ≤δ′+pη (+ᶜ-monotone δ′≤δ))
usagePresTerm γ▸t (fst-subst x x₁ t⇒u) with inv-usage-fst γ▸t
... | invUsageProj 𝟘▸t γ≤𝟘 = sub (fstₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t (snd-subst x x₁ t⇒u) with inv-usage-snd γ▸t
... | invUsageProj 𝟘▸t γ≤𝟘 = sub (sndₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t′ (Σ-β₁ x x₁ x₂ x₃) with inv-usage-fst γ▸t′
... | invUsageProj 𝟘▸tu γ≤𝟘 with inv-usage-prod 𝟘▸tu
... | invUsageProd {δ = δ} {η} δ▸t η▸u refl 𝟘≤δ+η = sub δ▸t
  (subst₂ _≤ᶜ_ refl
          (PE.sym (proj₁ (+ᶜ-noInverse δ η (≤ᶜ-antisymmetric 𝟘ᶜ-max 𝟘≤δ+η))))
          γ≤𝟘)
usagePresTerm γ▸u′ (Σ-β₂ x x₁ x₂ x₃) with inv-usage-snd γ▸u′
... | invUsageProj 𝟘▸tu γ≤𝟘 with inv-usage-prod 𝟘▸tu
... | invUsageProd {δ = δ} {η} δ▸t η▸u refl 𝟘≤δ+η = sub η▸u
  (subst₂ _≤ᶜ_ refl
          (PE.sym (proj₂ (+ᶜ-noInverse δ η (≤ᶜ-antisymmetric 𝟘ᶜ-max 𝟘≤δ+η))))
          γ≤𝟘)
usagePresTerm γ▸ptu (prodrec-subst x x₁ x₂ x₃ t⇒t′) with inv-usage-prodrec γ▸ptu
... | invUsageProdrec δ▸t η▸u γ≤pδ+η = sub (prodrecₘ (usagePresTerm δ▸t t⇒t′) η▸u) γ≤pδ+η
usagePresTerm γ▸ptu (prodrec-β {p} x x₁ x₂ x₃ x₄ x₅) with inv-usage-prodrec γ▸ptu
... | invUsageProdrec {δ} {η} δ▸tt′ η▸u γ≤pδ+η with inv-usage-prod δ▸tt′
... | invUsageProd {δ = δ′} {η = η′} δ′▸t η′▸t′ refl δ≤δ′+η′ = sub
  (doubleSubstₘ-lemma η▸u η′▸t′ δ′▸t)
  (≤ᶜ-transitive γ≤pδ+η (subst₂ _≤ᶜ_ refl eq (+ᶜ-monotone (·ᶜ-monotone δ≤δ′+η′))))
    where
    eq = begin
       p ·ᶜ (δ′ +ᶜ η′) +ᶜ η    ≡⟨ +ᶜ-comm (p ·ᶜ (δ′ +ᶜ η′)) η ⟩
       η +ᶜ p ·ᶜ (δ′ +ᶜ η′)    ≡⟨ cong₂ _+ᶜ_ refl (·ᶜ-distribˡ-+ᶜ p δ′ η′) ⟩
       η +ᶜ p ·ᶜ δ′ +ᶜ p ·ᶜ η′ ≡⟨ cong₂ _+ᶜ_ refl (+ᶜ-comm (p ·ᶜ δ′) (p ·ᶜ η′)) ⟩
       η +ᶜ p ·ᶜ η′ +ᶜ p ·ᶜ δ′ ∎
usagePresTerm γ▸natrec (natrec-subst x x₁ x₂ t⇒u) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z δ▸s η▸n γ≤γ′ = sub (natrecₘ δ▸z δ▸s (usagePresTerm η▸n t⇒u)) γ≤γ′
usagePresTerm {𝕄 = 𝕄} γ▸natrec (natrec-zero {r = r} x x₁ x₂) with inv-usage-natrec γ▸natrec
... | invUsageNatrec {δ = δ} δ▸z δ▸s η▸n γ≤γ′ = sub δ▸z
  (≤ᶜ-transitive γ≤γ′
    (subst₂ _≤ᶜ_ refl
            (subst₂ _≡_ (PE.sym (·ᶜ-identityˡ (δ +ᶜ 𝟘ᶜ))) (+ᶜ-identityʳ δ) refl)
            (·ᶜ-monotone₂ (+ᶜ-monotone₂ ≤ᶜ-reflexive 𝟘ᶜ-max)
                          (subst₂ (Modality._≤_ 𝕄)
                                  (PE.sym (Modality.*-StarSemiring 𝕄 r))
                                  (proj₂ (Modality.+-Identity 𝕄) (Modality.𝟙 𝕄))
                                  (+-monotone₂ {𝕄 = 𝕄} (≤-reflexive {𝕄 = 𝕄})
                                               (Modality.𝟘-max 𝕄 ((𝕄 Modality.· r) (Modality._* 𝕄 r ))))))))

usagePresTerm {𝕄 = 𝕄} γ▸natrec (natrec-suc {p = p} {r = r} x x₁ x₂ x₃) with inv-usage-natrec γ▸natrec
... | invUsageNatrec {δ = δ} {η} δ▸z δ▸s η▸sn γ≤γ′ with inv-usage-suc η▸sn
... | invUsageSuc {δ = η′} η′▸n η≤η′ = sub
  (doubleSubstₘ-lemma δ▸s (natrecₘ δ▸z δ▸s η′▸n) η′▸n)
  (≤ᶜ-transitive γ≤γ′ (subst₂ _≤ᶜ_ refl eq (·ᶜ-monotone
    (+ᶜ-monotone₂ ≤ᶜ-reflexive (·ᶜ-monotone η≤η′)))))
  where
  r* = Modality._* 𝕄 r
  eq = begin
     r* ·ᶜ (δ +ᶜ p ·ᶜ η′)
       ≡⟨ cong₂ _·ᶜ_ (Modality.*-StarSemiring 𝕄 r) refl ⟩
     _ ≡⟨ ·ᶜ-distribʳ-+ᶜ (Modality.𝟙 𝕄) (Modality._·_ 𝕄 r r*) (δ +ᶜ p ·ᶜ η′) ⟩
     _ ≡⟨ cong₂ _+ᶜ_ (·ᶜ-identityˡ (δ +ᶜ p ·ᶜ η′)) (·ᶜ-assoc r r* (δ +ᶜ p ·ᶜ η′)) ⟩
     _ ≡⟨ +ᶜ-assoc δ (p ·ᶜ η′) _ ⟩
     _ ≡⟨ cong₂ _+ᶜ_ refl (+ᶜ-comm (p ·ᶜ η′) _) ⟩
     _ ∎
usagePresTerm γ▸et (Emptyrec-subst x t⇒u) with inv-usage-Emptyrec γ▸et
... | invUsageEmptyrec δ▸t γ≤δ = sub (Emptyrecₘ (usagePresTerm δ▸t t⇒u)) γ≤δ

usagePres : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {Γ : Con (Term M) n} {A B : Term M n}
          → γ ▸ A → Γ ⊢ A ⇒ B → γ ▸ B
usagePres γ▸A (univ A⇒B) = usagePresTerm γ▸A A⇒B
