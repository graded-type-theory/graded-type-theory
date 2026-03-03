------------------------------------------------------------------------
-- A function that replaces quantities in contexts, and some related
-- properties
------------------------------------------------------------------------

open import Graded.Modality

module Graded.Context.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr : M₁ → M₂)
  where

open import Tools.Bool
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.Equivalence
open import Tools.Relation
open import Tools.Sum

open import Graded.Context using (Conₘ; ε; _∙_)
import Graded.Context.Properties
open import Graded.Modality.Morphism as M
  using (Is-morphism; Is-order-embedding; Is-Σ-order-embedding)
  hiding (module Is-morphism; module Is-order-embedding;
          module Is-Σ-order-embedding)
import Graded.Modality.Properties

private
  module C₁  = Graded.Context 𝕄₁
  module C₂  = Graded.Context 𝕄₂
  module CP₁ = Graded.Context.Properties 𝕄₁
  module CP₂ = Graded.Context.Properties 𝕄₂
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module MP₁ = Graded.Modality.Properties 𝕄₁
  module MP₂ = Graded.Modality.Properties 𝕄₂

private variable
  n i                          : Nat
  x                            : Fin _
  γ γ₁ δ δ₁ δ₂ δ₃ δ₄ δ₅ η η₁ θ : Conₘ _ _
  p q r                        : M₁
  𝟘ᵐ-allowed₁ 𝟘ᵐ-allowed₂      : Bool

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
tr-,≔ {γ = ε}     {x = ()}
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

  -- Translation commutes with 𝟘ᶜ up to _≤_.

  tr-Conₘ-𝟘ᶜ-≤ᶜ : tr-Conₘ C₁.𝟘ᶜ ≤ᶜ C₂.𝟘ᶜ {n = n}
  tr-Conₘ-𝟘ᶜ-≤ᶜ {n = 0}    = CP₂.≤ᶜ-refl
  tr-Conₘ-𝟘ᶜ-≤ᶜ {n = 1+ _} = tr-Conₘ-𝟘ᶜ-≤ᶜ ∙ tr-𝟘-≤

  opaque

    -- A variant of trivial-⊎-tr-𝟘 for usage contexts.

    trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ :
      (∀ {n} {γ δ : C₁.Conₘ n} → γ C₁.≈ᶜ δ) ⊎
      (∀ {n} → tr-Conₘ C₁.𝟘ᶜ C₂.≈ᶜ C₂.𝟘ᶜ {n = n})
    trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ = case trivial-⊎-tr-𝟘 of λ where
      (inj₁ trivial) → inj₁ (λ {_ _ _} → CP₁.≈ᶜ-trivial trivial)
      (inj₂ tr-𝟘)    → inj₂ (λ {_} → tr-Conₘ-𝟘ᶜ-≈ᶜ tr-𝟘)

  -- Translation commutes with _+ᶜ_.

  tr-Conₘ-+ᶜ : tr-Conₘ (γ C₁.+ᶜ δ) ≈ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ
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

  opaque

    -- Translation commutes with nrᵢᶜ.

    tr-Conₘ-nrᵢᶜ : tr-Conₘ (CP₁.nrᵢᶜ r γ δ i) ≈ᶜ CP₂.nrᵢᶜ (tr r) (tr-Conₘ γ) (tr-Conₘ δ) i
    tr-Conₘ-nrᵢᶜ {γ = ε} {(ε)} = ε
    tr-Conₘ-nrᵢᶜ {γ = _ ∙ _} {_ ∙ _} {i} = tr-Conₘ-nrᵢᶜ ∙ tr-nrᵢ i


module Is-nr-preserving-morphism
  ⦃ has-nr₁ : Has-nr M₁ M₁.semiring-with-meet ⦄
  ⦃ has-nr₂ : Has-nr M₂ M₂.semiring-with-meet ⦄
  (m : M.Is-nr-preserving-morphism 𝕄₁ 𝕄₂ tr) where

  open M.Is-nr-preserving-morphism m
  open C₂ using (_≤ᶜ_)

  opaque

    -- Translation commutes with nrᶜ up to _≤ᶜ_.

    tr-Conₘ-nrᶜ :
      tr-Conₘ (C₁.nrᶜ p r γ δ η) ≤ᶜ
      C₂.nrᶜ (tr p) (tr r) (tr-Conₘ γ) (tr-Conₘ δ) (tr-Conₘ η)
    tr-Conₘ-nrᶜ {γ = ε}     {δ = ε}     {η = ε}     = ε
    tr-Conₘ-nrᶜ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} = tr-Conₘ-nrᶜ ∙ tr-nr

module Is-no-nr-glb-preserving-morphism
  (m : M.Is-no-nr-glb-preserving-morphism 𝕄₁ 𝕄₂ tr) where

  open M.Is-no-nr-glb-preserving-morphism m

  opaque

    -- Translation preserves greatest lower bounds in a certain sense.

    tr-Conₘ-nrᵢᶜ-GLBᶜ :
      C₁.Greatest-lower-boundᶜ γ (CP₁.nrᵢᶜ r δ η) →
      ∃ λ γ′ → C₂.Greatest-lower-boundᶜ γ′ (CP₂.nrᵢᶜ (tr r) (tr-Conₘ δ) (tr-Conₘ η))
    tr-Conₘ-nrᵢᶜ-GLBᶜ {γ = ε} {δ = ε} {(ε)} γ-glb =
      ε , CP₂.ε-GLB
    tr-Conₘ-nrᵢᶜ-GLBᶜ {γ = γ ∙ p} {δ = δ ∙ p₁} {η ∙ p₂} γp-glb =
      let γ-glb , p-glb = CP₁.GLBᶜ-pointwise γp-glb
          γ′ , γ′-glb = tr-Conₘ-nrᵢᶜ-GLBᶜ γ-glb
          p′ , p′-glb = tr-nrᵢ-GLB p-glb
      in  γ′ ∙ p′ , CP₂.GLBᶜ-pointwise′ γ′-glb p′-glb

module Is-nr-reflecting-morphism
  ⦃ has-nr₁ : Has-nr M₁ M₁.semiring-with-meet ⦄
  ⦃ has-nr₂ : Has-nr M₂ M₂.semiring-with-meet ⦄
  (m : M.Is-nr-reflecting-morphism 𝕄₁ 𝕄₂ tr) where

  open M.Is-nr-reflecting-morphism m

  -- A variant of tr-≤-nr for usage contexts.

  tr-Conₘ-≤ᶜ-nrᶜ :
    tr-Conₘ θ C₂.≤ᶜ C₂.nrᶜ (tr p) (tr r) γ₁ δ₁ η₁ →
    ∃₃ λ γ₂ δ₂ η₂ →
       tr-Conₘ γ₂ C₂.≤ᶜ γ₁ × tr-Conₘ δ₂ C₂.≤ᶜ δ₁ × tr-Conₘ η₂ C₂.≤ᶜ η₁ ×
       θ C₁.≤ᶜ C₁.nrᶜ p r γ₂ δ₂ η₂
  tr-Conₘ-≤ᶜ-nrᶜ {θ = ε} {γ₁ = ε} {δ₁ = ε} {η₁ = ε} _ =
    ε , ε , ε , ε , ε , ε , ε
  tr-Conₘ-≤ᶜ-nrᶜ
    {θ = _ ∙ _} {γ₁ = _ ∙ _} {δ₁ = _ ∙ _} {η₁ = _ ∙ _} (hyp₁ ∙ hyp₂) =
    case tr-Conₘ-≤ᶜ-nrᶜ hyp₁ of λ (_ , _ , _ , ≤γ₁ , ≤δ₁ , ≤η₁ , θ≤) →
    case tr-≤-nr hyp₂ of λ (_ , _ , _ , ≤z₁ , ≤s₁ , ≤n₁ , q≤) →
    _ , _ , _ , ≤γ₁ ∙ ≤z₁ , ≤δ₁ ∙ ≤s₁ , ≤η₁ ∙ ≤n₁ , θ≤ ∙ q≤

module Is-no-nr-glb-reflecting-morphism
  (m : M.Is-no-nr-glb-reflecting-morphism 𝕄₁ 𝕄₂ tr) where

  open M.Is-no-nr-glb-reflecting-morphism m

  opaque

    -- A variant of tr-≤-no-nr for usage contexts.

    tr-Conₘ-≤ᶜ-no-nr :
      ∀ {θ η χ x} →
      tr-Conₘ θ C₂.≤ᶜ x C₂.·ᶜ η C₂.+ᶜ χ →
      M₂.Greatest-lower-bound x (M₂.nrᵢ (tr r) M₂.𝟙 (tr p)) →
      C₂.Greatest-lower-boundᶜ χ (CP₂.nrᵢᶜ (tr r) γ δ) →
      ∃₅ λ γ′ δ′ η′ x′ χ′ → tr-Conₘ γ′ C₂.≤ᶜ γ × tr-Conₘ δ′ C₂.≤ᶜ δ × tr-Conₘ η′ C₂.≤ᶜ η ×
         M₁.Greatest-lower-bound x′ (M₁.nrᵢ r M₁.𝟙 p) ×
         C₁.Greatest-lower-boundᶜ χ′ (CP₁.nrᵢᶜ r γ′ δ′) ×
         θ C₁.≤ᶜ x′ C₁.·ᶜ η′ C₁.+ᶜ χ′
    tr-Conₘ-≤ᶜ-no-nr {γ = ε} {(ε)} {(ε)} {(ε)} {(ε)} θ≤ x-glb χ-glb =
      _ , _ , _ , _ , _ , ε , ε , ε , tr-nrᵢ-glb x-glb .proj₂ , CP₁.ε-GLB , ε
    tr-Conₘ-≤ᶜ-no-nr {γ = γ ∙ p} {δ ∙ p₁} {θ ∙ r} {η ∙ p₂} {χ ∙ q} (θ≤ ∙ r≤) x-glb χq-glb =
      let χ-glb , q-glb = CP₂.GLBᶜ-pointwise χq-glb
          _ , _ , _ , x′ , _ , ≤γ , ≤δ , ≤η
            , x′-glb , χ′-glb , θ≤′ = tr-Conₘ-≤ᶜ-no-nr θ≤ x-glb χ-glb
          _ , _ , _ , x″ , _ , ≤p , ≤p₁ , ≤p₂
            , x″-glb , q′-glb , r≤′ = tr-≤-no-nr r≤ x-glb q-glb
      in  _ , _ , _ , _ , _ , ≤γ ∙ ≤p , ≤δ ∙ ≤p₁ , ≤η ∙ ≤p₂ , x′-glb
            , CP₁.GLBᶜ-pointwise′ χ′-glb q′-glb
            , θ≤′ ∙ MP₁.≤-trans r≤′ (MP₁.≤-reflexive
                    (M₁.+-congʳ (M₁.·-congʳ (MP₁.GLB-unique x″-glb x′-glb))))

------------------------------------------------------------------------
-- Lemmas that hold if there is a function that is an order embedding
-- for Σ with respect to tr

module Is-Σ-order-embedding
  {tr-Σ : M₁ → M₂}
  (m : Is-Σ-order-embedding 𝕄₁ 𝕄₂ tr tr-Σ)
  where

  open M.Is-Σ-order-embedding m

  -- A variant of tr-≤-tr-Σ-→ for usage contexts.

  tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ :
    tr-Conₘ γ C₂.≤ᶜ tr-Σ p C₂.·ᶜ δ →
    ∃ λ δ′ → tr-Conₘ δ′ C₂.≤ᶜ δ × γ C₁.≤ᶜ p C₁.·ᶜ δ′
  tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ {γ = ε}     {δ = ε}     _             = ε , ε , ε
  tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ {γ = _ ∙ _} {δ = _ ∙ _} (hyp₁ ∙ hyp₂) =
    case tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ hyp₁ of λ (_ , ≤δ , γ≤) →
    case tr-≤-tr-Σ-→ hyp₂ of λ (_ , ≤q , p≤) →
    _ , ≤δ ∙ ≤q , γ≤ ∙ p≤

------------------------------------------------------------------------
-- Lemmas that hold if the translation is an order embedding

module Is-order-embedding (m : Is-order-embedding 𝕄₁ 𝕄₂ tr) where

  open M.Is-order-embedding m

  open Is-morphism tr-morphism public
  open Is-Σ-order-embedding
         (M.Is-order-embedding→Is-Σ-order-embedding m)
    public
    renaming (tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ to tr-Conₘ-≤ᶜ-·ᶜ)

  -- The function tr-Conₘ is order-reflecting.

  tr-Conₘ-order-reflecting : tr-Conₘ γ C₂.≤ᶜ tr-Conₘ δ → γ C₁.≤ᶜ δ
  tr-Conₘ-order-reflecting {γ = ε}     {δ = ε}     ε       = ε
  tr-Conₘ-order-reflecting {γ = _ ∙ _} {δ = _ ∙ _} (γ ∙ p) =
    tr-Conₘ-order-reflecting γ ∙ tr-order-reflecting p

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

  opaque

    -- A variant of tr-≤-ω·+ for usage contexts.

    tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ :
      tr-Conₘ γ C₂.≤ᶜ M₂.ω C₂.·ᶜ (δ C₂.+ᶜ η) →
      ∃₂ λ δ′ η′ →
        tr-Conₘ δ′ C₂.≤ᶜ δ × tr-Conₘ η′ C₂.≤ᶜ η ×
        γ C₁.≤ᶜ M₁.ω C₁.·ᶜ (δ′ C₁.+ᶜ η′)
    tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ {γ = ε} {δ = ε} {η = ε} _ =
      ε , ε , ε , ε , ε
    tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ
      {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (hyp₁ ∙ hyp₂) =
      case tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ hyp₁ of λ (_ , _ , ≤δ , ≤η , γ≤) →
      case tr-≤-ω·+ hyp₂ of λ (_ , _ , ≤q , ≤r , p≤) →
      _ , _ , ≤δ ∙ ≤q , ≤η ∙ ≤r , γ≤ ∙ p≤

  opaque

    -- A variant of tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ.

    tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ³ :
      tr-Conₘ γ C₂.≤ᶜ M₂.ω C₂.·ᶜ (δ₁ C₂.+ᶜ δ₂ C₂.+ᶜ δ₃ C₂.+ᶜ δ₄) →
      ∃₄ λ δ₁′ δ₂′ δ₃′ δ₄′ →
        tr-Conₘ δ₁′ C₂.≤ᶜ δ₁ × tr-Conₘ δ₂′ C₂.≤ᶜ δ₂ ×
        tr-Conₘ δ₃′ C₂.≤ᶜ δ₃ × tr-Conₘ δ₄′ C₂.≤ᶜ δ₄ ×
        γ C₁.≤ᶜ M₁.ω C₁.·ᶜ (δ₁′ C₁.+ᶜ δ₂′ C₁.+ᶜ δ₃′ C₁.+ᶜ δ₄′)
    tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ³ {γ} γ≤ =
      case tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ γ≤ of λ
        (δ₁′ , δ′ , δ₁′≤ , δ′≤ , γ≤) →
      case tr-Conₘ-≤ᶜ-+ᶜ δ′≤ of λ
        (δ₂′ , δ″ , δ₂′≤ , δ″≤ , δ′≤′) →
      case tr-Conₘ-≤ᶜ-+ᶜ δ″≤ of λ
        (δ₃′ , δ₄′ , δ₃′≤ , δ₄′≤ , δ″≤′) →
      δ₁′ , δ₂′ , δ₃′ , δ₄′ , δ₁′≤ , δ₂′≤ , δ₃′≤ , δ₄′≤ , (begin
        γ                                               ≤⟨ γ≤ ⟩
        M₁.ω C₁.·ᶜ (δ₁′ C₁.+ᶜ δ′)                       ≤⟨ CP₁.·ᶜ-monotoneʳ $ CP₁.+ᶜ-monotoneʳ δ′≤′ ⟩
        M₁.ω C₁.·ᶜ (δ₁′ C₁.+ᶜ δ₂′ C₁.+ᶜ δ″)             ≤⟨ CP₁.·ᶜ-monotoneʳ $ CP₁.+ᶜ-monotoneʳ $ CP₁.+ᶜ-monotoneʳ δ″≤′ ⟩
        M₁.ω C₁.·ᶜ (δ₁′ C₁.+ᶜ δ₂′ C₁.+ᶜ δ₃′ C₁.+ᶜ δ₄′)  ∎)
      where
      open CP₁.≤ᶜ-reasoning

  opaque

    -- Another variant of tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ.

    tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ⁴ :
      tr-Conₘ γ C₂.≤ᶜ
      M₂.ω C₂.·ᶜ (δ₁ C₂.+ᶜ δ₂ C₂.+ᶜ δ₃ C₂.+ᶜ δ₄ C₂.+ᶜ δ₅) →
      ∃₅ λ δ₁′ δ₂′ δ₃′ δ₄′ δ₅′ →
        tr-Conₘ δ₁′ C₂.≤ᶜ δ₁ × tr-Conₘ δ₂′ C₂.≤ᶜ δ₂ ×
        tr-Conₘ δ₃′ C₂.≤ᶜ δ₃ × tr-Conₘ δ₄′ C₂.≤ᶜ δ₄ ×
        tr-Conₘ δ₅′ C₂.≤ᶜ δ₅ ×
        γ C₁.≤ᶜ M₁.ω C₁.·ᶜ (δ₁′ C₁.+ᶜ δ₂′ C₁.+ᶜ δ₃′ C₁.+ᶜ δ₄′ C₁.+ᶜ δ₅′)
    tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ⁴ {γ} γ≤ =
      case tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ³ γ≤ of λ
        (δ₁′ , δ₂′ , δ₃′ , δ′ , δ₁′≤ , δ₂′≤ , δ₃′≤ , δ′≤ , γ≤) →
      case tr-Conₘ-≤ᶜ-+ᶜ δ′≤ of λ
        (δ₄′ , δ₅′ , δ₄′≤ , δ₅′≤ , δ′≤′) →
        δ₁′ , δ₂′ , δ₃′ , δ₄′ , δ₅′ , δ₁′≤ , δ₂′≤ , δ₃′≤ , δ₄′≤ , δ₅′≤
      , (begin
           γ                                                         ≤⟨ γ≤ ⟩
           M₁.ω C₁.·ᶜ (δ₁′ C₁.+ᶜ δ₂′ C₁.+ᶜ δ₃′ C₁.+ᶜ δ′)             ≤⟨ CP₁.·ᶜ-monotoneʳ $ CP₁.+ᶜ-monotoneʳ $ CP₁.+ᶜ-monotoneʳ $ CP₁.+ᶜ-monotoneʳ
                                                                        δ′≤′ ⟩
           M₁.ω C₁.·ᶜ (δ₁′ C₁.+ᶜ δ₂′ C₁.+ᶜ δ₃′ C₁.+ᶜ δ₄′ C₁.+ᶜ δ₅′)  ∎)
      where
      open CP₁.≤ᶜ-reasoning

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
