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

-- Term reduction preserves resource usage
-- If γ ▸ t and Γ ⊢ t ⇒ u ∷ A, then γ ▸ u

usagePresTerm : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {Γ : Con (Term M) n} {t u A : Term M n}
              → γ ▸ t → Γ ⊢ t ⇒ u ∷ A → γ ▸ u
usagePresTerm γ▸t (conv t⇒u x) = usagePresTerm γ▸t t⇒u
usagePresTerm γ▸t (app-subst t⇒u x) with inv-usage-app γ▸t
... | invUsageApp δ▸t η▸a γ≤δ+pη = sub ((usagePresTerm δ▸t t⇒u) ∘ₘ η▸a) γ≤δ+pη
usagePresTerm γ▸λta (β-red x x₁ x₂ refl) with inv-usage-app γ▸λta
... | invUsageApp δ▸λt η▸a γ≤δ′+pη with inv-usage-lam δ▸λt
... | invUsageLam δ▸t δ′≤δ = sub (sgSubstₘ-lemma δ▸t η▸a) (≤ᶜ-transitive γ≤δ′+pη (+ᶜ-monotoneˡ δ′≤δ))
usagePresTerm γ▸t (fst-subst x x₁ t⇒u) with inv-usage-fst γ▸t
... | invUsageProj 𝟘▸t γ≤𝟘 = sub (fstₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t (snd-subst x x₁ t⇒u) with inv-usage-snd γ▸t
... | invUsageProj 𝟘▸t γ≤𝟘 = sub (sndₘ (usagePresTerm 𝟘▸t t⇒u)) γ≤𝟘
usagePresTerm γ▸t′ (Σ-β₁ x x₁ x₂ x₃) with inv-usage-fst γ▸t′
... | invUsageProj 𝟘▸tu γ≤𝟘 with inv-usage-prod 𝟘▸tu
... | invUsageProd {δ = δ} {η} δ▸t η▸u refl 𝟘≤δ+η = sub δ▸t (≤ᶜ-transitive γ≤𝟘 (proj₁ (+ᶜ-Positive δ η 𝟘≤δ+η)))
usagePresTerm γ▸u′ (Σ-β₂ x x₁ x₂ x₃) with inv-usage-snd γ▸u′
... | invUsageProj 𝟘▸tu γ≤𝟘 with inv-usage-prod 𝟘▸tu
... | invUsageProd {δ = δ} {η} δ▸t η▸u refl 𝟘≤δ+η = sub η▸u (≤ᶜ-transitive γ≤𝟘 (proj₂ (+ᶜ-Positive δ η 𝟘≤δ+η)))
usagePresTerm γ▸ptu (prodrec-subst x x₁ x₂ x₃ t⇒t′) with inv-usage-prodrec γ▸ptu
... | invUsageProdrec δ▸t η▸u γ≤pδ+η = sub (prodrecₘ (usagePresTerm δ▸t t⇒t′) η▸u) γ≤pδ+η
usagePresTerm γ▸ptu (prodrec-β {p} x x₁ x₂ x₃ x₄ x₅) with inv-usage-prodrec γ▸ptu
... | invUsageProdrec {δ} {η} δ▸tt′ η▸u γ≤pδ+η with inv-usage-prod δ▸tt′
... | invUsageProd {δ = δ′} {η = η′} δ′▸t η′▸t′ refl δ≤δ′+η′ = sub
  (doubleSubstₘ-lemma η▸u η′▸t′ δ′▸t)
  (≤ᶜ-transitive γ≤pδ+η (subst₂ _≤ᶜ_ refl eq (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ δ≤δ′+η′))))
    where
    eq = begin
       p ·ᶜ (δ′ +ᶜ η′) +ᶜ η    ≡⟨ +ᶜ-comm (p ·ᶜ (δ′ +ᶜ η′)) η ⟩
       η +ᶜ p ·ᶜ (δ′ +ᶜ η′)    ≡⟨ cong₂ _+ᶜ_ refl (·ᶜ-distribˡ-+ᶜ p δ′ η′) ⟩
       η +ᶜ p ·ᶜ δ′ +ᶜ p ·ᶜ η′ ≡⟨ cong₂ _+ᶜ_ refl (+ᶜ-comm (p ·ᶜ δ′) (p ·ᶜ η′)) ⟩
       η +ᶜ p ·ᶜ η′ +ᶜ p ·ᶜ δ′ ∎
usagePresTerm γ▸natrec (natrec-subst x x₁ x₂ t⇒u) with inv-usage-natrec γ▸natrec
... | invUsageNatrec δ▸z δ▸s η▸n r≤0 γ≤γ′ = sub (natrecₘ δ▸z δ▸s (usagePresTerm η▸n t⇒u) r≤0) γ≤γ′

usagePresTerm {𝕄 = 𝕄} γ▸natrec (natrec-zero {p = p} {r = r} x x₁ x₂) with inv-usage-natrec γ▸natrec
... | invUsageNatrec {δ = δ} δ▸z δ▸s η▸n r≤0 γ≤γ′ with inv-usage-zero η▸n
... | η≤𝟘 = sub δ▸z (≤ᶜ-transitive γ≤γ′ (subst₂ _≤ᶜ_ (cong₂ _·ᶜ_ refl (+ᶜ-comm _ _)) eq γ′≤δ))
  where
  rr*≤0 = subst₂ (Modality._≤_ 𝕄) refl
                 (proj₁ (Modality.·-Zero 𝕄) (Modality._* 𝕄 r))
                 (·-monotoneˡ {𝕄 = 𝕄} r≤0)
  r*≤1 = subst₂ (Modality._≤_ 𝕄)
                (PE.sym (Modality.*-StarSemiring 𝕄 r))
                (proj₂ (Modality.+-Identity 𝕄) (Modality.𝟙 𝕄))
                (+-monotone {𝕄 = 𝕄} (≤-reflexive {𝕄 = 𝕄}) rr*≤0)
  γ′≤δ = ·ᶜ-monotone (+ᶜ-monotoneˡ (·ᶜ-monotoneʳ η≤𝟘)) r*≤1
  eq = begin
     (Modality.𝟙 𝕄) ·ᶜ (p ·ᶜ 𝟘ᶜ +ᶜ δ) ≡⟨ ·ᶜ-identityˡ (p ·ᶜ 𝟘ᶜ +ᶜ δ) ⟩
     p ·ᶜ 𝟘ᶜ +ᶜ δ                      ≡⟨ cong₂ _+ᶜ_ (·ᶜ-zeroʳ p) refl ⟩
     𝟘ᶜ +ᶜ δ                           ≡⟨ +ᶜ-identityˡ δ ⟩
     δ                                 ∎


usagePresTerm {𝕄 = 𝕄} γ▸natrec (natrec-suc {p = p} {r = r} x x₁ x₂ x₃) with inv-usage-natrec γ▸natrec
... | invUsageNatrec {δ = δ} {η} δ▸z δ▸s η▸sn r≤0 γ≤γ′ with inv-usage-suc η▸sn
... | invUsageSuc {δ = η′} η′▸n η≤η′ = sub
  (doubleSubstₘ-lemma δ▸s (natrecₘ δ▸z δ▸s η′▸n r≤0) η′▸n)
  (≤ᶜ-transitive γ≤γ′ (subst₂ _≤ᶜ_ refl eq (·ᶜ-monotoneʳ (+ᶜ-monotone ≤ᶜ-reflexive (·ᶜ-monotoneʳ η≤η′)))))
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

-- Type reduction preserves modality usage
-- If γ ▸ A and Γ ⊢ A ⇒ B, then γ ▸ B

usagePres : {𝕄 : Modality M} {γ : Conₘ 𝕄 n} {Γ : Con (Term M) n} {A B : Term M n}
          → γ ▸ A → Γ ⊢ A ⇒ B → γ ▸ B
usagePres γ▸A (univ A⇒B) = usagePresTerm γ▸A A⇒B
