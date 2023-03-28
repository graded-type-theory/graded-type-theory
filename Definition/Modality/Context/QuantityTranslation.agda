------------------------------------------------------------------------
-- A function that replaces quantities in contexts, and some related
-- properties
------------------------------------------------------------------------

open import Definition.Modality

module Definition.Modality.Context.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr : M₁ → M₂)
  where

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Sum

open import Definition.Modality.Context using (Conₘ; ε; _∙_)
import Definition.Modality.Context.Properties
open import Definition.Modality.Morphism as M
  using (Is-morphism; Is-order-embedding)
  hiding (module Is-morphism; module Is-order-embedding)

private
  module C₁  = Definition.Modality.Context 𝕄₁
  module C₂  = Definition.Modality.Context 𝕄₂
  module CP₁ = Definition.Modality.Context.Properties 𝕄₁
  module CP₂ = Definition.Modality.Context.Properties 𝕄₂
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂

private variable
  n              : Nat
  x              : Fin _
  γ δ δ₁ δ₂ δ₃ η : Conₘ _ _
  p q r          : M₁

------------------------------------------------------------------------
-- Translation

-- Translation of usage contexts.

tr-Conₘ : C₁.Conₘ n → C₂.Conₘ n
tr-Conₘ ε       = ε
tr-Conₘ (γ ∙ p) = tr-Conₘ γ ∙ tr p

------------------------------------------------------------------------
-- Some lemmas

-- Translation preserves context equality.

tr-≈ᶜ : γ C₁.≈ᶜ δ → tr-Conₘ γ C₂.≈ᶜ tr-Conₘ δ
tr-≈ᶜ ε       = ε
tr-≈ᶜ (γ ∙ p) = tr-≈ᶜ γ ∙ cong tr p

-- Translation commutes with _,_≔_.

tr-,≔ : tr-Conₘ (γ C₁., x ≔ p) ≡ tr-Conₘ γ C₂., x ≔ tr p
tr-,≔ {γ = _ ∙ _} {x = x0}   = refl
tr-,≔ {γ = _ ∙ _} {x = _ +1} = cong (_∙ _) tr-,≔

-- Translation commutes with _⟨_⟩.

tr-⟨⟩ : ∀ γ → tr (γ C₁.⟨ x ⟩) ≡ tr-Conₘ γ C₂.⟨ x ⟩
tr-⟨⟩ {x = x0}   (_ ∙ _) = refl
tr-⟨⟩ {x = _ +1} (γ ∙ _) = tr-⟨⟩ γ

-- If the translation of 𝟘 is 𝟘, then the translation of 𝟘ᶜ is 𝟘ᶜ.

tr-Conₘ-𝟘ᶜ-≈ᶜ : tr M₁.𝟘 ≡ M₂.𝟘 → tr-Conₘ C₁.𝟘ᶜ C₂.≈ᶜ C₂.𝟘ᶜ {n = n}
tr-Conₘ-𝟘ᶜ-≈ᶜ {n = 0}    _    = ε
tr-Conₘ-𝟘ᶜ-≈ᶜ {n = 1+ _} tr-𝟘 = tr-Conₘ-𝟘ᶜ-≈ᶜ tr-𝟘 ∙ tr-𝟘

------------------------------------------------------------------------
-- Lemmas that hold if the translation is a morphism

module Is-morphism (m : Is-morphism 𝕄₁ 𝕄₂ tr) where

  open M.Is-morphism m

  open C₂ using (_≈ᶜ_; _≤ᶜ_)

  -- Translation preserves the ordering relation.

  tr-Conₘ-monotone : γ C₁.≤ᶜ δ → tr-Conₘ γ C₂.≤ᶜ tr-Conₘ δ
  tr-Conₘ-monotone {γ = ε}     {δ = ε}     ε       = ε
  tr-Conₘ-monotone {γ = _ ∙ _} {δ = _ ∙ _} (γ ∙ p) =
    tr-Conₘ-monotone γ ∙ tr-monotone p

  -- If 𝟘ᵐ is allowed in the target modality but not the source
  -- modality, then usage contexts are translated to contexts that are
  -- bounded by 𝟘ᶜ.

  tr-Conₘ-≤ᶜ-𝟘ᶜ :
    ¬ T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed → tr-Conₘ γ ≤ᶜ C₂.𝟘ᶜ
  tr-Conₘ-≤ᶜ-𝟘ᶜ {γ = ε}     _      _  = ε
  tr-Conₘ-≤ᶜ-𝟘ᶜ {γ = _ ∙ _} not-ok ok =
    tr-Conₘ-≤ᶜ-𝟘ᶜ not-ok ok ∙ tr-<-𝟘 not-ok ok .proj₁

  -- Translation commutes with 𝟘ᶜ up to _≤_.

  tr-Conₘ-𝟘ᶜ-≤ᶜ : tr-Conₘ C₁.𝟘ᶜ ≤ᶜ C₂.𝟘ᶜ {n = n}
  tr-Conₘ-𝟘ᶜ-≤ᶜ {n = 0}    = CP₂.≤ᶜ-refl
  tr-Conₘ-𝟘ᶜ-≤ᶜ {n = 1+ _} = tr-Conₘ-𝟘ᶜ-≤ᶜ ∙ tr-𝟘-≤

  -- Translation commutes with _+ᶜ_ up to _≤ᶜ_.

  tr-Conₘ-+ᶜ : tr-Conₘ (γ C₁.+ᶜ δ) ≤ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ
  tr-Conₘ-+ᶜ {γ = ε}     {δ = ε}     = ε
  tr-Conₘ-+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} = tr-Conₘ-+ᶜ ∙ tr-+

  -- Translation commutes with _·ᶜ_.

  tr-Conₘ-·ᶜ : tr-Conₘ (p C₁.·ᶜ γ) ≈ᶜ tr p C₂.·ᶜ tr-Conₘ γ
  tr-Conₘ-·ᶜ {γ = ε}     = ε
  tr-Conₘ-·ᶜ {γ = _ ∙ _} = tr-Conₘ-·ᶜ ∙ tr-·

  -- Translation commutes with _∧ᶜ_ up to _≤ᶜ_.

  tr-Conₘ-∧ᶜ : tr-Conₘ (γ C₁.∧ᶜ δ) ≤ᶜ tr-Conₘ γ C₂.∧ᶜ tr-Conₘ δ
  tr-Conₘ-∧ᶜ {γ = ε}     {δ = ε}     = ε
  tr-Conₘ-∧ᶜ {γ = _ ∙ _} {δ = _ ∙ _} = tr-Conₘ-∧ᶜ ∙ tr-∧

  -- Translation commutes with _⊛ᶜ_▷_ up to _≤ᶜ_.

  tr-Conₘ-⊛ᶜ :
    tr-Conₘ (γ C₁.⊛ᶜ δ ▷ r) ≤ᶜ tr-Conₘ γ C₂.⊛ᶜ tr-Conₘ δ ▷ tr r
  tr-Conₘ-⊛ᶜ {γ = ε}     {δ = ε}     = ε
  tr-Conₘ-⊛ᶜ {γ = _ ∙ _} {δ = _ ∙ _} = tr-Conₘ-⊛ᶜ ∙ tr-⊛

------------------------------------------------------------------------
-- Lemmas that hold if the translation is an order embedding

module Is-order-embedding (m : Is-order-embedding 𝕄₁ 𝕄₂ tr) where

  open M.Is-order-embedding m

  open Is-morphism tr-morphism public

  -- The function tr-Conₘ is order-reflecting.

  tr-Conₘ-order-reflecting : tr-Conₘ γ C₂.≤ᶜ tr-Conₘ δ → γ C₁.≤ᶜ δ
  tr-Conₘ-order-reflecting {γ = ε}     {δ = ε}     ε       = ε
  tr-Conₘ-order-reflecting {γ = _ ∙ _} {δ = _ ∙ _} (γ ∙ p) =
    tr-Conₘ-order-reflecting γ ∙ tr-order-reflecting p

  -- A variant of trivial-⊎-tr-𝟘 for usage contexts.

  trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ :
    (∀ {n} {γ δ : C₁.Conₘ n} → γ C₁.≈ᶜ δ) ⊎
    (∀ {n} → tr-Conₘ C₁.𝟘ᶜ C₂.≈ᶜ C₂.𝟘ᶜ {n = n})
  trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ = case trivial-⊎-tr-𝟘 of λ where
    (inj₁ trivial) → inj₁ (λ {_ _ _} → CP₁.≈ᶜ-trivial trivial)
    (inj₂ tr-𝟘)    → inj₂ (λ {_} → tr-Conₘ-𝟘ᶜ-≈ᶜ tr-𝟘)

  -- If the translation of γ is bounded by 𝟘ᶜ, then γ is bounded by
  -- 𝟘ᶜ.

  tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ : tr-Conₘ γ C₂.≤ᶜ C₂.𝟘ᶜ → γ C₁.≤ᶜ C₁.𝟘ᶜ
  tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ {γ = γ} ≤𝟘 =
    case trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ of λ where
      (inj₁ trivial) → trivial
      (inj₂ tr-𝟘)    → tr-Conₘ-order-reflecting (begin
        tr-Conₘ γ      ≤⟨ ≤𝟘 ⟩
        C₂.𝟘ᶜ          ≈˘⟨ tr-𝟘 ⟩
        tr-Conₘ C₁.𝟘ᶜ  ∎)
    where
    open Tools.Reasoning.PartialOrder CP₂.≤ᶜ-poset

  -- A variant of tr-≤ for usage contexts.

  tr-Conₘ-≤ᶜ : ∃ λ δ → tr-Conₘ δ C₂.≤ᶜ γ
  tr-Conₘ-≤ᶜ {γ = ε}     = ε , ε
  tr-Conₘ-≤ᶜ {γ = _ ∙ _} =
    case tr-Conₘ-≤ᶜ of λ (_ , ≤γ) →
    case tr-≤ of λ (_ , ≤p) →
    _ , ≤γ ∙ ≤p

  -- A variant of tr-≤-+ for usage contexts.

  tr-Conₘ-≤ᶜ-+ᶜ :
    tr-Conₘ γ C₂.≤ᶜ δ C₂.+ᶜ η →
    ∃₂ λ δ′ η′ →
       tr-Conₘ δ′ C₂.≤ᶜ δ × tr-Conₘ η′ C₂.≤ᶜ η × γ C₁.≤ᶜ δ′ C₁.+ᶜ η′
  tr-Conₘ-≤ᶜ-+ᶜ {γ = ε} {δ = ε} {η = ε} _ =
    ε , ε , ε , ε , ε
  tr-Conₘ-≤ᶜ-+ᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (hyp₁ ∙ hyp₂) =
    case tr-Conₘ-≤ᶜ-+ᶜ hyp₁ of λ (_ , _ , ≤δ , ≤η , γ≤) →
    case tr-≤-+ hyp₂ of λ (_ , _ , ≤q , ≤r , p≤) →
    _ , _ , ≤δ ∙ ≤q , ≤η ∙ ≤r , γ≤ ∙ p≤

  -- A variant of tr-≤-· for usage contexts.

  tr-Conₘ-≤ᶜ-·ᶜ :
    tr-Conₘ γ C₂.≤ᶜ tr p C₂.·ᶜ δ →
    ∃ λ δ′ → tr-Conₘ δ′ C₂.≤ᶜ δ × γ C₁.≤ᶜ p C₁.·ᶜ δ′
  tr-Conₘ-≤ᶜ-·ᶜ {γ = ε}     {δ = ε}     _             = ε , ε , ε
  tr-Conₘ-≤ᶜ-·ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (hyp₁ ∙ hyp₂) =
    case tr-Conₘ-≤ᶜ-·ᶜ hyp₁ of λ (_ , ≤δ , γ≤) →
    case tr-≤-· hyp₂ of λ (_ , ≤q , p≤) →
    _ , ≤δ ∙ ≤q , γ≤ ∙ p≤

  -- A variant of tr-≤-∧ for usage contexts.

  tr-Conₘ-≤ᶜ-∧ᶜ :
    tr-Conₘ γ C₂.≤ᶜ δ C₂.∧ᶜ η →
    ∃₂ λ δ′ η′ →
       tr-Conₘ δ′ C₂.≤ᶜ δ × tr-Conₘ η′ C₂.≤ᶜ η × γ C₁.≤ᶜ δ′ C₁.∧ᶜ η′
  tr-Conₘ-≤ᶜ-∧ᶜ {γ = ε} {δ = ε} {η = ε} _ =
    ε , ε , ε , ε , ε
  tr-Conₘ-≤ᶜ-∧ᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (hyp₁ ∙ hyp₂) =
    case tr-Conₘ-≤ᶜ-∧ᶜ hyp₁ of λ (_ , _ , ≤δ , ≤η , γ≤) →
    case tr-≤-∧ hyp₂ of λ (_ , _ , ≤q , ≤r , p≤) →
    _ , _ , ≤δ ∙ ≤q , ≤η ∙ ≤r , γ≤ ∙ p≤

  -- A variant of tr-≤-⊛ for usage contexts.

  tr-Conₘ-≤ᶜ-⊛ᶜ :
    tr-Conₘ γ C₂.≤ᶜ (δ₁ C₂.∧ᶜ δ₂) C₂.⊛ᶜ δ₃ C₂.+ᶜ tr p C₂.·ᶜ δ₂ ▷ tr q →
    ∃₃ λ δ₁′ δ₂′ δ₃′ →
       tr-Conₘ δ₁′ C₂.≤ᶜ δ₁ × tr-Conₘ δ₂′ C₂.≤ᶜ δ₂ × tr-Conₘ δ₃′ C₂.≤ᶜ δ₃ ×
       γ C₁.≤ᶜ (δ₁′ C₁.∧ᶜ δ₂′) C₁.⊛ᶜ δ₃′ C₁.+ᶜ p C₁.·ᶜ δ₂′ ▷ q
  tr-Conₘ-≤ᶜ-⊛ᶜ {γ = ε} {δ₁ = ε} {δ₂ = ε} {δ₃ = ε} _ =
    ε , ε , ε , ε , ε , ε , ε
  tr-Conₘ-≤ᶜ-⊛ᶜ
    {γ = _ ∙ _} {δ₁ = _ ∙ _} {δ₂ = _ ∙ _} {δ₃ = _ ∙ _} (hyp₁ ∙ hyp₂) =
    case tr-Conₘ-≤ᶜ-⊛ᶜ hyp₁ of λ (_ , _ , _ , ≤δ₁ , ≤δ₂ , ≤δ₃ , γ≤) →
    case tr-≤-⊛ hyp₂ of λ (_ , _ , _ , ≤q₁ , ≤q₂ , ≤q₃ , p≤) →
    _ , _ , _ , ≤δ₁ ∙ ≤q₁ , ≤δ₂ ∙ ≤q₂ , ≤δ₃ ∙ ≤q₃ , γ≤ ∙ p≤
