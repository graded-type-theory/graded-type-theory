------------------------------------------------------------------------
-- Some definitions and properties related to functions that translates
-- modes.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Mode.Instances.Zero-one.Variant

module Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive where

open import Graded.Context
open import Graded.Modality.Morphism as M
  hiding (module Is-morphism)
open import Graded.Mode.Instances.Zero-one
import Graded.Context.QuantityTranslation as CQ
  hiding (module Is-morphism)
import Graded.Modality.Properties

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  a₁ a₂ a₃ : Level
  M₁ M₂ M₃ : Set _
  γ δ₁ δ₂ δ₃ δ₄ : Conₘ _ _
  p q : M₁
  𝕄 𝕄₁ 𝕄₂ 𝕄₃ : Modality _
  v₁ v₂ v₃ : Mode-variant _

------------------------------------------------------------------------
-- The property of being "no-nr-preserving" (related to
-- the usage rule for natrec without an nr function).

record Is-no-nr-preserving
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (v₁ : Mode-variant 𝕄₁) (v₂ : Mode-variant 𝕄₂) :
  Set (a₁ ⊔ a₂) where

  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module V₁ = Mode-variant v₁
    module V₂ = Mode-variant v₂

  field

    -- If 𝟘ᵐ is allowed in the target modality, then 𝟘ᵐ is allowed in
    -- the source modality or the source modality is trivial.
    𝟘ᵐ-in-first-if-in-second :
      T V₂.𝟘ᵐ-allowed → T V₁.𝟘ᵐ-allowed ⊎ M₁.Trivial

    -- If the target modality has a well-behaved zero, then the source
    -- modality has a well-behaved zero or is trivial.
    𝟘-well-behaved-in-first-if-in-second :
      Has-well-behaved-zero M₂ M₂.semiring-with-meet →
      Has-well-behaved-zero M₁ M₁.semiring-with-meet ⊎ M₁.Trivial

opaque

  -- The property Is-no-nr-preserving is reflexive.

  Is-no-nr-preserving-reflexive :
    {v : Mode-variant 𝕄} →
    Is-no-nr-preserving 𝕄 𝕄 v v
  Is-no-nr-preserving-reflexive = λ where
      .𝟘ᵐ-in-first-if-in-second → inj₁
      .𝟘-well-behaved-in-first-if-in-second → inj₁
    where
    open Is-no-nr-preserving

opaque

  -- The property Is-no-nr-preserving is transitive given
  -- a certain assumption.

  Is-no-nr-preserving-transitive :
    {M₁ : Set a₁} {M₂ : Set a₂} {M₃ : Set a₃}
    {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
    {𝕄₃ : Modality M₃} {v₁ : Mode-variant 𝕄₁}
    {v₂ : Mode-variant 𝕄₂} {v₃ : Mode-variant 𝕄₃} →
    (Modality.Trivial 𝕄₂ → Modality.Trivial 𝕄₁) →
    Is-no-nr-preserving 𝕄₂ 𝕄₃ v₂ v₃ →
    Is-no-nr-preserving 𝕄₁ 𝕄₂ v₁ v₂ →
    Is-no-nr-preserving 𝕄₁ 𝕄₃ v₁ v₃
  Is-no-nr-preserving-transitive hyp f g = λ where
      .𝟘ᵐ-in-first-if-in-second ok →
        case F.𝟘ᵐ-in-first-if-in-second ok of λ where
          (inj₁ ok) → G.𝟘ᵐ-in-first-if-in-second ok
          (inj₂ trivial) →
            inj₂ (hyp trivial)
      .𝟘-well-behaved-in-first-if-in-second ok →
        case F.𝟘-well-behaved-in-first-if-in-second ok of λ where
          (inj₁ ok) → G.𝟘-well-behaved-in-first-if-in-second ok
          (inj₂ trivial) →
            inj₂ (hyp trivial)
    where
    module F = Is-no-nr-preserving f
    module G = Is-no-nr-preserving g
    open Is-no-nr-preserving

------------------------------------------------------------------------
-- The property of being a "no-nr-reflecting" morphism (related to
-- the usage rule for natrec without an nr function).

record Is-no-nr-reflecting-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (v₁ : Mode-variant 𝕄₁) (v₂ : Mode-variant 𝕄₂)
  (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where

  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module V₁ = Mode-variant v₁
    module V₂ = Mode-variant v₂

  field

    -- A variant of the properties of order embeddings for the
    -- alternative usage rule for natrec.

    tr-≤-no-nr :
      ∀ {p q₁ q₂ q₃ q₄ r s} →
      tr p M₂.≤ q₁ →
      q₁ M₂.≤ q₂ →
      (T V₂.𝟘ᵐ-allowed →
       q₁ M₂.≤ q₃) →
      (⦃ 𝟘-well-behaved :
           Has-well-behaved-zero M₂ M₂.semiring-with-meet ⦄ →
       q₁ M₂.≤ q₄) →
      q₁ M₂.≤ q₃ M₂.+ tr r M₂.· q₄ M₂.+ tr s M₂.· q₁ →
      ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
         tr q₂′ M₂.≤ q₂ ×
         tr q₃′ M₂.≤ q₃ ×
         tr q₄′ M₂.≤ q₄ ×
         p M₁.≤ q₁′ ×
         q₁′ M₁.≤ q₂′ ×
         (T V₁.𝟘ᵐ-allowed →
          q₁′ M₁.≤ q₃′) ×
         (⦃ 𝟘-well-behaved :
              Has-well-behaved-zero M₁ M₁.semiring-with-meet ⦄ →
          q₁′ M₁.≤ q₄′) ×
         q₁′ M₁.≤ q₃′ M₁.+ r M₁.· q₄′ M₁.+ s M₁.· q₁′

  open CQ 𝕄₁ 𝕄₂ tr
  private
    module C₁ = Graded.Context 𝕄₁
    module C₂ = Graded.Context 𝕄₂

  opaque

    -- A variant of tr-≤-no-nr for usage contexts.

    tr-≤ᶜ-no-nr :
      tr-Conₘ γ C₂.≤ᶜ δ₁ →
      δ₁ C₂.≤ᶜ δ₂ →
      (T V₂.𝟘ᵐ-allowed → δ₁ C₂.≤ᶜ δ₃) →
      (⦃ 𝟘-well-behaved :
           Has-well-behaved-zero M₂ M₂.semiring-with-meet ⦄ →
       δ₁ C₂.≤ᶜ δ₄) →
      δ₁ C₂.≤ᶜ δ₃ C₂.+ᶜ tr p C₂.·ᶜ δ₄ C₂.+ᶜ tr q C₂.·ᶜ δ₁ →
      ∃₄ λ δ₁′ δ₂′ δ₃′ δ₄′ →
         tr-Conₘ δ₂′ C₂.≤ᶜ δ₂ ×
         tr-Conₘ δ₃′ C₂.≤ᶜ δ₃ ×
         tr-Conₘ δ₄′ C₂.≤ᶜ δ₄ ×
         γ C₁.≤ᶜ δ₁′ ×
         δ₁′ C₁.≤ᶜ δ₂′ ×
         (T V₁.𝟘ᵐ-allowed → δ₁′ C₁.≤ᶜ δ₃′) ×
         (⦃ 𝟘-well-behaved :
              Has-well-behaved-zero M₁ M₁.semiring-with-meet ⦄ →
          δ₁′ C₁.≤ᶜ δ₄′) ×
         δ₁′ C₁.≤ᶜ δ₃′ C₁.+ᶜ p C₁.·ᶜ δ₄′ C₁.+ᶜ q C₁.·ᶜ δ₁′
    tr-≤ᶜ-no-nr {γ = ε} {δ₁ = ε} {δ₂ = ε} {δ₃ = ε} {δ₄ = ε} _ _ _ _ _ =
      _ , _ , _ , _ , ε , ε , ε , ε , ε , (λ _ → ε) , ε , ε
    tr-≤ᶜ-no-nr
      {γ = _ ∙ _} {δ₁ = _ ∙ _} {δ₂ = _ ∙ _} {δ₃ = _ ∙ _} {δ₄ = _ ∙ _}
      (hyp₁₁ ∙ hyp₁₂) (hyp₂₁ ∙ hyp₂₂) hyp₃ hyp₄ (hyp₅₁ ∙ hyp₅₂) =
      case tr-≤ᶜ-no-nr
             hyp₁₁ hyp₂₁
             (λ ok → case hyp₃ ok of λ {
                (le ∙ _) → le })
             (case hyp₄ of λ {
                (le ∙ _) → le })
             hyp₅₁ of λ {
        (_ , _ , _ , _ ,
         le₁₁ , le₂₁ , le₃₁ , le₄₁ , le₅₁ , le₆₁ , le₇₁ , le₈₁) →
      case tr-≤-no-nr
             hyp₁₂ hyp₂₂
             (λ ok → case hyp₃ ok of λ {
                (_ ∙ le) → le })
             (case hyp₄ of λ {
                (_ ∙ le) → le })
             hyp₅₂ of λ {
        (_ , _ , _ , _ ,
         le₁₂ , le₂₂ , le₃₂ , le₄₂ , le₅₂ , le₆₂ , le₇₂ , le₈₂) →
        _ , _ , _ , _
      , le₁₁ ∙ le₁₂ , le₂₁ ∙ le₂₂ , le₃₁ ∙ le₃₂ , le₄₁ ∙ le₄₂
      , le₅₁ ∙ le₅₂
      , (λ ok → le₆₁ ok ∙ le₆₂ ok)
      , (λ ⦃ _ ⦄ → le₇₁ ∙ le₇₂)
      , le₈₁ ∙ le₈₂ }}

opaque

  Is-no-nr-reflecting-morphism-id :
    {v : Mode-variant 𝕄} →
    Is-no-nr-reflecting-morphism 𝕄 𝕄 v v idᶠ
  Is-no-nr-reflecting-morphism-id {𝕄} = λ where
      .tr-≤-no-nr p≤q₁ q₁≤q₂ q₁≤q₃ q₁≤q₄ fix →
        _ , _ , _ , _ , ≤-refl , ≤-refl , ≤-refl
          , p≤q₁ , q₁≤q₂ , q₁≤q₃ , q₁≤q₄ , fix
    where
    open Is-no-nr-reflecting-morphism
    open Graded.Modality.Properties 𝕄

opaque

  Is-no-nr-reflecting-morphism-∘ :
    {M₁ : Set a₁} {M₂ : Set a₂} {M₃ : Set a₃}
    {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
    {𝕄₃ : Modality M₃} {v₁ : Mode-variant 𝕄₁}
    {v₂ : Mode-variant 𝕄₂} {v₃ : Mode-variant 𝕄₃}
    {tr₁ : M₂ → M₃} {tr₂ : M₁ → M₂} →
    Is-morphism 𝕄₂ 𝕄₃ tr₁ →
    Is-no-nr-reflecting-morphism 𝕄₂ 𝕄₃ v₂ v₃ tr₁ →
    Is-no-nr-reflecting-morphism 𝕄₁ 𝕄₂ v₁ v₂ tr₂ →
    Is-no-nr-reflecting-morphism 𝕄₁ 𝕄₃ v₁ v₃ (tr₁ ∘→ tr₂)
  Is-no-nr-reflecting-morphism-∘ {𝕄₃} {tr₁} {tr₂} m f g = λ where
      .tr-≤-no-nr {q₁} {q₂} {q₃} {q₄}
        p≤q₁ q₁≤q₂ q₁≤q₃ q₁≤q₄ fix →
        let open ≤-reasoning in
            case F.tr-≤-no-nr p≤q₁ q₁≤q₂ q₁≤q₃ q₁≤q₄ fix of λ {
          (q₁′ , q₂′ , q₃′ , q₄′ , q₂′≤q₂ , q₃′≤q₃ , q₄′≤q₄ ,
           p≤q₁′ , q₁′≤q₂′ , q₁′≤q₃′ , q₁′≤q₄′ , fix′) →
        case G.tr-≤-no-nr p≤q₁′ q₁′≤q₂′ q₁′≤q₃′ q₁′≤q₄′ fix′ of λ {
          (q₁″ , q₂″ , q₃″ , q₄″ , q₂″≤q₂′ , q₃″≤q₃′ , q₄″≤q₄′ ,
           p≤q₁″ , q₁″≤q₂″ , q₁″≤q₃″ , q₁″≤q₄″ , fix″) →
          q₁″ , q₂″ , q₃″ , q₄″
        , (begin
             tr₁ (tr₂ q₂″)  ≤⟨ tr-monotone q₂″≤q₂′ ⟩
             tr₁ q₂′        ≤⟨ q₂′≤q₂ ⟩
             q₂             ∎)
        , (begin
             tr₁ (tr₂ q₃″)  ≤⟨ tr-monotone q₃″≤q₃′ ⟩
             tr₁ q₃′        ≤⟨ q₃′≤q₃ ⟩
             q₃             ∎)
        , (begin
             tr₁ (tr₂ q₄″)  ≤⟨ tr-monotone q₄″≤q₄′ ⟩
             tr₁ q₄′        ≤⟨ q₄′≤q₄ ⟩
             q₄             ∎)
        , p≤q₁″ , q₁″≤q₂″ , q₁″≤q₃″ , (λ ⦃ _ ⦄ → q₁″≤q₄″) , fix″ }}

    where
    open Is-no-nr-reflecting-morphism
    module F = Is-no-nr-reflecting-morphism f
    module G = Is-no-nr-reflecting-morphism g
    open Graded.Modality.Properties 𝕄₃
    open M.Is-morphism m

------------------------------------------------------------------------
-- The property of being mode respecting morphisms

record Are-mode-respecting-morphisms
  {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  (v₁ : Mode-variant 𝕄₁) (v₂ : Mode-variant 𝕄₂)
  (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private module C₂ = Graded.Context 𝕄₂
  open CQ 𝕄₁ 𝕄₂ tr

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module V₁ = Mode-variant v₁
    module V₂ = Mode-variant v₂

  field

    -- If 𝟘ᵐ is allowed in the source modality, then it is allowed in
    -- the target modality.
    𝟘ᵐ-in-second-if-in-first : T V₁.𝟘ᵐ-allowed → T V₂.𝟘ᵐ-allowed

    -- If 𝟘ᵐ is allowed in the target modality but not the source
    -- modality, then quantities are translated to quantities that are
    -- strictly below 𝟘.
    tr-<-𝟘 : ∀ {p} → ¬ T V₁.𝟘ᵐ-allowed → T V₂.𝟘ᵐ-allowed → tr p M₂.< M₂.𝟘

    -- If 𝟘ᵐ is allowed in the target modality and tr-Σ p is equal
    -- to 𝟘, then 𝟘ᵐ is allowed in the source modality and p is equal
    -- to 𝟘.
    tr-Σ-≡-𝟘-→ :
      ∀ {p} →
      T V₂.𝟘ᵐ-allowed → tr-Σ p ≡ M₂.𝟘 → T V₁.𝟘ᵐ-allowed × p ≡ M₁.𝟘

  opaque

    -- If 𝟘ᵐ is allowed in the target modality but not the source
    -- modality, then usage contexts are translated to contexts that are
    -- bounded by 𝟘ᶜ.

    tr-Conₘ-≤ᶜ-𝟘ᶜ :
      ¬ T V₁.𝟘ᵐ-allowed → T V₂.𝟘ᵐ-allowed →
      tr-Conₘ γ C₂.≤ᶜ C₂.𝟘ᶜ
    tr-Conₘ-≤ᶜ-𝟘ᶜ {γ = ε}     _      _  = ε
    tr-Conₘ-≤ᶜ-𝟘ᶜ {γ = _ ∙ _} not-ok ok =
      tr-Conₘ-≤ᶜ-𝟘ᶜ not-ok ok ∙ tr-<-𝟘 not-ok ok .proj₁

------------------------------------------------------------------------
-- Properties that are made under the assumptions that tr is a
-- morphism and that tr-Σ is a Σ-morphism with respect to tr

module Is-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  (v₁ : Mode-variant 𝕄₁) (v₂ : Mode-variant 𝕄₂)
  {tr tr-Σ : M₁ → M₂}
  (tr-morphism   : Is-morphism 𝕄₁ 𝕄₂ tr)
  (tr-Σ-morphism : Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ)
  where

  open M.Is-morphism tr-morphism
  open M.Is-Σ-morphism tr-Σ-morphism

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module Mo₁ = Graded.Mode.Instances.Zero-one v₁
    module Mo₂ = Graded.Mode.Instances.Zero-one v₂
    module V₁ = Mode-variant v₁

  opaque

    -- If 𝟘ᵐ is allowed in the source modality, then 𝟘 is translated
    -- to 𝟘.

    tr-𝟘-≡-𝟘ᵐ : T V₁.𝟘ᵐ-allowed → tr M₁.𝟘 ≡ M₂.𝟘
    tr-𝟘-≡-𝟘ᵐ = tr-𝟘-≡ ∘→ Mo₁.𝟘ᵐ.non-trivial

  opaque

    -- If 𝟘ᵐ is allowed in the source modality, then tr-Σ translates 𝟘
    -- to 𝟘.

    tr-Σ-𝟘-≡-𝟘ᵐ : T V₁.𝟘ᵐ-allowed → tr-Σ M₁.𝟘 ≡ M₂.𝟘
    tr-Σ-𝟘-≡-𝟘ᵐ = tr-Σ-𝟘-≡ ∘→ Mo₁.𝟘ᵐ.non-trivial
