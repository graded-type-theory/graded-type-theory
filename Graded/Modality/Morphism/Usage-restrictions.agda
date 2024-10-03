------------------------------------------------------------------------
-- Preserving/reflecting usage restrictions
------------------------------------------------------------------------

module Graded.Modality.Morphism.Usage-restrictions where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

open import Graded.Modality
import Graded.Modality.Properties
open import Graded.Mode
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions

open import Definition.Untyped.NotParametrised

private variable
  a₁ a₂ p₁ p₂ p₃           : Level
  M M₁ M₂                  : Set _
  P P₃                     : M → Set _
  f f₃ tr₁ tr₂ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q r                    : M
  𝕄 𝕄₁ 𝕄₂ 𝕄₃               : Modality _
  R R₁ R₂ R₃               : Usage-restrictions _
  m₁ m₂ m₃                 : Mode _
  s                        : Strength
  ⦃ ok₁ ok₂ ⦄              : T _

------------------------------------------------------------------------
-- The relations _≈ᵐ_ and _≳ᵐ_

-- Two modes from two possibly different modalities are equivalent if
-- they are both 𝟙ᵐ or both 𝟘ᵐ (with arbitrary proofs).

infix 4 _≈ᵐ_

data _≈ᵐ_
       {M₁ : Set a₁} {M₂ : Set a₂}
       {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂} :
       Mode 𝕄₁ → Mode 𝕄₂ → Set (a₁ ⊔ a₂) where
  𝟘ᵐ : 𝟘ᵐ[ ok₁ ] ≈ᵐ 𝟘ᵐ[ ok₂ ]
  𝟙ᵐ : 𝟙ᵐ        ≈ᵐ 𝟙ᵐ

-- A variant of _≈ᵐ_. 𝟙ᵐ ≳ᵐ 𝟘ᵐ[ ok₂ ] is allowed if the "first"
-- modality is trivial.

infix 4 _≳ᵐ_

data _≳ᵐ_
       {M₁ : Set a₁} {M₂ : Set a₂}
       {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂} :
       Mode 𝕄₁ → Mode 𝕄₂ → Set (a₁ ⊔ a₂) where
  [_]   : m₁ ≈ᵐ m₂ → m₁ ≳ᵐ m₂
  𝟙ᵐ≳𝟘ᵐ : Modality.Trivial 𝕄₁ → 𝟙ᵐ ≳ᵐ 𝟘ᵐ[ ok₂ ]

opaque

  -- The relation _≈ᵐ_ is symmetric.

  ≈ᵐ-symmetric : m₁ ≈ᵐ m₂ → m₂ ≈ᵐ m₁
  ≈ᵐ-symmetric 𝟘ᵐ = 𝟘ᵐ
  ≈ᵐ-symmetric 𝟙ᵐ = 𝟙ᵐ

opaque

  -- If m₁ ≈ᵐ m₂ holds, then m₂ ≡ 𝟙ᵐ implies m₁ ≡ 𝟙ᵐ.

  ≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ : m₁ ≈ᵐ m₂ → m₂ ≡ 𝟙ᵐ → m₁ ≡ 𝟙ᵐ
  ≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ 𝟙ᵐ refl = refl

opaque

  -- If m₁ ≈ᵐ m₂ holds, then m₁ ≡ 𝟙ᵐ implies m₂ ≡ 𝟙ᵐ.

  ≈ᵐ→≡𝟙ᵐ←≡𝟙ᵐ : m₁ ≈ᵐ m₂ → m₁ ≡ 𝟙ᵐ → m₂ ≡ 𝟙ᵐ
  ≈ᵐ→≡𝟙ᵐ←≡𝟙ᵐ = ≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ ∘→ ≈ᵐ-symmetric

private opaque

  -- Some lemmas used below.

  ≈ᵐ→≤ᵉᵐ₁ : m₁ ≈ᵐ m₂ → f m₁ ≤ᵉᵐ f m₂
  ≈ᵐ→≤ᵉᵐ₁     𝟙ᵐ = ≤ᵉᵐ-reflexive
  ≈ᵐ→≤ᵉᵐ₁ {f} 𝟘ᵐ = subst (_≤ᵉᵐ_ _) (cong f (𝟘ᵐ-cong _)) ≤ᵉᵐ-reflexive

  ≈ᵐ→→₁ : m₁ ≈ᵐ m₂ → P m₁ → P m₂
  ≈ᵐ→→₁     𝟙ᵐ           = idᶠ
  ≈ᵐ→→₁ {P} (𝟘ᵐ ⦃ ok₁ ⦄) =
    subst (λ ok → P 𝟘ᵐ[ ok₁ ] → P 𝟘ᵐ[ ok ]) T-propositional idᶠ

  ≳ᵐ→←₁ :
    {P : Mode 𝕄 → Set p} →
    m₁ ≳ᵐ m₂ → P m₂ → P m₁
  ≳ᵐ→←₁ [ m₁≈m₂ ] =
    ≈ᵐ→→₁ $ ≈ᵐ-symmetric m₁≈m₂
  ≳ᵐ→←₁ {𝕄} (𝟙ᵐ≳𝟘ᵐ ⦃ ok₂ = ok ⦄ trivial) =
    ⊥-elim $ MP.𝟘ᵐ.non-trivial ok trivial
    where
    module MP = Graded.Modality.Properties 𝕄

  ≈ᵐ→≤ᵉᵐ₂ :
    {f₁ : Mode 𝕄₁ → Erased-matches}
    {f₂ : Mode 𝕄₂ → Erased-matches} →
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed) →
    (∀ {m₁ m₂} → m₁ ≈ᵐ m₂ → f₁ m₁ ≤ᵉᵐ f₂ m₂) →
    (∀ {m₂ m₃} → m₂ ≈ᵐ m₃ → f₂ m₂ ≤ᵉᵐ f₃ m₃) →
    m₁ ≈ᵐ m₃ → f₁ m₁ ≤ᵉᵐ f₃ m₃
  ≈ᵐ→≤ᵉᵐ₂ _ hyp₁ hyp₂ 𝟙ᵐ =
    ≤ᵉᵐ-transitive (hyp₁ 𝟙ᵐ) (hyp₂ 𝟙ᵐ)
  ≈ᵐ→≤ᵉᵐ₂ 𝟘ᵐ→𝟘ᵐ hyp₁ hyp₂ (𝟘ᵐ ⦃ ok₁ ⦄) =
    case 𝟘ᵐ→𝟘ᵐ ok₁ of λ
      ok₂ →
    ≤ᵉᵐ-transitive (hyp₁ (𝟘ᵐ ⦃ ok₂ = ok₂ ⦄)) (hyp₂ (𝟘ᵐ ⦃ ok₁ = ok₂ ⦄))

  ≈ᵐ→→₂ :
    {P₁ : Mode 𝕄₁ → Set p₁}
    {P₂ : Mode 𝕄₂ → Set p₂} →
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed) →
    (∀ {m₁ m₂} → m₁ ≈ᵐ m₂ → P₁ m₁ → P₂ m₂) →
    (∀ {m₂ m₃} → m₂ ≈ᵐ m₃ → P₂ m₂ → P₃ m₃) →
    m₁ ≈ᵐ m₃ → P₁ m₁ → P₃ m₃
  ≈ᵐ→→₂ _ hyp₁ hyp₂ 𝟙ᵐ =
    hyp₂ 𝟙ᵐ ∘→ hyp₁ 𝟙ᵐ
  ≈ᵐ→→₂ 𝟘ᵐ→𝟘ᵐ hyp₁ hyp₂ (𝟘ᵐ ⦃ ok₁ ⦄) =
    case 𝟘ᵐ→𝟘ᵐ ok₁ of λ
      ok₂ →
    hyp₂ (𝟘ᵐ ⦃ ok₁ = ok₂ ⦄) ∘→ hyp₁ (𝟘ᵐ ⦃ ok₂ = ok₂ ⦄)

  ≈ᵐ→≥ᵉᵐ₂ :
    {f₁ : Mode 𝕄₁ → Erased-matches}
    {f₂ : Mode 𝕄₂ → Erased-matches} →
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed) →
    (∀ {m₂ m₃} → m₂ ≈ᵐ m₃ → f₃ m₃ ≤ᵉᵐ f₂ m₂) →
    (∀ {m₁ m₂} → m₁ ≈ᵐ m₂ → f₂ m₂ ≤ᵉᵐ f₁ m₁) →
    m₁ ≈ᵐ m₃ → f₃ m₃ ≤ᵉᵐ f₁ m₁
  ≈ᵐ→≥ᵉᵐ₂ _ hyp₁ hyp₂ 𝟙ᵐ =
    ≤ᵉᵐ-transitive (hyp₁ 𝟙ᵐ) (hyp₂ 𝟙ᵐ)
  ≈ᵐ→≥ᵉᵐ₂ 𝟘ᵐ→𝟘ᵐ hyp₁ hyp₂ (𝟘ᵐ ⦃ ok₁ ⦄ ⦃ ok₂ = ok₃ ⦄) =
    case 𝟘ᵐ→𝟘ᵐ ok₁ of λ
      ok₂ →
    ≤ᵉᵐ-transitive (hyp₁ (𝟘ᵐ ⦃ ok₁ = ok₂ ⦄)) (hyp₂ (𝟘ᵐ ⦃ ok₂ = ok₂ ⦄))

  ≳ᵐ→←₂ :
    {P₁ : Mode 𝕄₁ → Set p₁}
    {P₂ : Mode 𝕄₂ → Set p₂}
    {P₃ : Mode 𝕄₃ → Set p₃} →
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
        module M₃ = Modality 𝕄₃
    in
    (T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed) →
    (T M₃.𝟘ᵐ-allowed ⊎ M₃.Trivial → T M₂.𝟘ᵐ-allowed ⊎ M₂.Trivial) →
    (∀ {m₂ m₃} → m₂ ≳ᵐ m₃ → P₃ m₃ → P₂ m₂) →
    (∀ {m₁ m₂} → m₁ ≳ᵐ m₂ → P₂ m₂ → P₁ m₁) →
    m₁ ≳ᵐ m₃ → P₃ m₃ → P₁ m₁
  ≳ᵐ→←₂ _ _ hyp₁ hyp₂ [ 𝟙ᵐ ] =
    hyp₂ [ 𝟙ᵐ ] ∘→ hyp₁ [ 𝟙ᵐ ]
  ≳ᵐ→←₂ 𝟘ᵐ→𝟘ᵐ _ hyp₁ hyp₂ [ 𝟘ᵐ ⦃ ok₁ ⦄ ⦃ ok₂ = ok₃ ⦄ ] =
    case 𝟘ᵐ→𝟘ᵐ ok₁ of λ
      ok₂ →
    hyp₂ [ 𝟘ᵐ ⦃ ok₂ = ok₂ ⦄ ] ∘→ hyp₁ [ 𝟘ᵐ ⦃ ok₁ = ok₂ ⦄ ]
  ≳ᵐ→←₂
    {𝕄₂} {m₁ = 𝟙ᵐ} {m₃ = 𝟘ᵐ[ ok₃ ]}
    _ 𝟘ᵐ←𝟘ᵐ hyp₁ hyp₂ (𝟙ᵐ≳𝟘ᵐ ⦃ ok₂ = ok₃ ⦄ trivial₁) =
    case 𝟘ᵐ←𝟘ᵐ (inj₁ ok₃) of λ where
      (inj₁ ok₂) →
        hyp₂ (𝟙ᵐ≳𝟘ᵐ ⦃ ok₂ = ok₂ ⦄ trivial₁) ∘→
        hyp₁ [ 𝟘ᵐ ⦃ ok₁ = ok₂ ⦄ ]
      (inj₂ trivial₂) →
        hyp₂ [ 𝟙ᵐ ] ∘→ hyp₁ (𝟙ᵐ≳𝟘ᵐ trivial₂)

------------------------------------------------------------------------
-- Common-properties

-- Properties common to Are-preserving-usage-restrictions and
-- Are-reflecting-usage-restrictions.

record Common-properties
  {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  (R₁ : Usage-restrictions 𝕄₁) (R₂ : Usage-restrictions 𝕄₂) :
  Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂

  field
    -- If 𝟘ᵐ is allowed for 𝕄₁, then 𝟘ᵐ is allowed for 𝕄₂.
    --
    -- Note that this property is also (at the time of writing) part
    -- of Is-morphism.
    𝟘ᵐ-preserved : T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed

    -- The property that strong unit types act as sinks is preserved.
    starˢ-sink-preserved : R₁.starˢ-sink ≡ R₂.starˢ-sink

    -- R₁.Id-erased holds if and only if R₂.Id-erased holds.
    Id-erased-preserved : R₁.Id-erased ⇔ R₂.Id-erased

    -- If m₁ ≈ᵐ m₂, then R₁.erased-matches-for-J m₁ is bounded by
    -- R₂.erased-matches-for-J m₂.
    erased-matches-for-J-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.erased-matches-for-J m₁ ≤ᵉᵐ R₂.erased-matches-for-J m₂

    -- If m₁ ≈ᵐ m₂, then R₁.erased-matches-for-K m₁ is bounded by
    -- R₂.erased-matches-for-K m₂.
    erased-matches-for-K-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.erased-matches-for-K m₁ ≤ᵉᵐ R₂.erased-matches-for-K m₂

opaque

  -- The relation Common-properties is reflexive.

  Common-properties-reflexive : Common-properties R R
  Common-properties-reflexive = λ where
      .𝟘ᵐ-preserved                   → idᶠ
      .starˢ-sink-preserved           → refl
      .Id-erased-preserved            → id⇔
      .erased-matches-for-J-preserved → ≈ᵐ→≤ᵉᵐ₁
      .erased-matches-for-K-preserved → ≈ᵐ→≤ᵉᵐ₁
    where
    open Common-properties

opaque

  -- The relation Common-properties is transitive.

  Common-properties-transitive :
    Common-properties R₁ R₂ → Common-properties R₂ R₃ →
    Common-properties R₁ R₃
  Common-properties-transitive cp₁ cp₂ = λ where
      .𝟘ᵐ-preserved →
        CP₂.𝟘ᵐ-preserved ∘→ CP₁.𝟘ᵐ-preserved
      .starˢ-sink-preserved →
        trans CP₁.starˢ-sink-preserved CP₂.starˢ-sink-preserved
      .Id-erased-preserved →
        CP₂.Id-erased-preserved ∘⇔ CP₁.Id-erased-preserved
      .erased-matches-for-J-preserved →
        ≈ᵐ→≤ᵉᵐ₂ CP₁.𝟘ᵐ-preserved CP₁.erased-matches-for-J-preserved
          CP₂.erased-matches-for-J-preserved
      .erased-matches-for-K-preserved →
        ≈ᵐ→≤ᵉᵐ₂ CP₁.𝟘ᵐ-preserved CP₁.erased-matches-for-K-preserved
          CP₂.erased-matches-for-K-preserved
    where
    open Common-properties
    module CP₁ = Common-properties cp₁
    module CP₂ = Common-properties cp₂

------------------------------------------------------------------------
-- Are-preserving-usage-restrictions

-- The property of preserving Usage-restrictions.

record Are-preserving-usage-restrictions
         {M₁ : Set a₁} {M₂ : Set a₂}
         {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
         (R₁ : Usage-restrictions 𝕄₁) (R₂ : Usage-restrictions 𝕄₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂

  field
    -- Common properties.
    common-properties : Common-properties R₁ R₂

    -- The functions tr and tr-Σ preserve the Prodrec-allowed
    -- property in a certain way.
    Prodrec-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.Prodrec-allowed m₁ r p q →
      R₂.Prodrec-allowed m₂ (tr r) (tr-Σ p) (tr q)

    -- The function tr preserves the Unitrec-allowed property in a
    -- certain way.
    Unitrec-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.Unitrec-allowed m₁ p q →
      R₂.Unitrec-allowed m₂ (tr p) (tr q)

    -- The function tr preserves the Emptyrec-allowed property in a
    -- certain way.
    Emptyrec-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.Emptyrec-allowed m₁ p →
      R₂.Emptyrec-allowed m₂ (tr p)

    -- The []-cong-allowed-mode property respects equivalent modes
    []-cong-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.[]-cong-allowed-mode s m₁ →
      R₂.[]-cong-allowed-mode s m₂

  open Common-properties common-properties public

opaque

  -- For every value R the identity function preserves
  -- Usage-restrictions for R and R.

  Are-preserving-usage-restrictions-id :
    Are-preserving-usage-restrictions R R idᶠ idᶠ
  Are-preserving-usage-restrictions-id = λ where
      .common-properties  → Common-properties-reflexive
      .Prodrec-preserved  → ≈ᵐ→→₁
      .Unitrec-preserved  → ≈ᵐ→→₁
      .Emptyrec-preserved → ≈ᵐ→→₁
      .[]-cong-preserved  → ≈ᵐ→→₁
    where
    open Are-preserving-usage-restrictions

opaque

  -- Composition preserves Are-preserving-usage-restrictions (in a
  -- certain sense).

  Are-preserving-usage-restrictions-∘ :
    Are-preserving-usage-restrictions R₂ R₃ tr₁ tr-Σ₁ →
    Are-preserving-usage-restrictions R₁ R₂ tr₂ tr-Σ₂ →
    Are-preserving-usage-restrictions
      R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
  Are-preserving-usage-restrictions-∘ m₁ m₂ = λ where
      .common-properties →
        Common-properties-transitive P₂.common-properties
          P₁.common-properties
      .Prodrec-preserved →
        ≈ᵐ→→₂ P₂.𝟘ᵐ-preserved P₂.Prodrec-preserved P₁.Prodrec-preserved
      .Unitrec-preserved →
        ≈ᵐ→→₂ P₂.𝟘ᵐ-preserved P₂.Unitrec-preserved P₁.Unitrec-preserved
      .Emptyrec-preserved →
        ≈ᵐ→→₂ P₂.𝟘ᵐ-preserved P₂.Emptyrec-preserved
          P₁.Emptyrec-preserved
      .[]-cong-preserved →
        ≈ᵐ→→₂ P₂.𝟘ᵐ-preserved P₂.[]-cong-preserved
          P₁.[]-cong-preserved
    where
    open Are-preserving-usage-restrictions
    module P₁ = Are-preserving-usage-restrictions m₁
    module P₂ = Are-preserving-usage-restrictions m₂

------------------------------------------------------------------------
-- Are-reflecting-usage-restrictions

-- The property of reflecting Usage-restrictions.

record Are-reflecting-usage-restrictions
         {M₁ : Set a₁} {M₂ : Set a₂}
         {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
         (R₁ : Usage-restrictions 𝕄₁) (R₂ : Usage-restrictions 𝕄₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂

  field
    -- Common properties.
    common-properties : Common-properties R₁ R₂

    -- If 𝟘ᵐ is allowed for 𝕄₂ or 𝕄₂ is trivial, then 𝟘ᵐ is allowed
    -- for 𝕄₁ or 𝕄₁ is trivial.
    𝟘ᵐ-reflected :
      T M₂.𝟘ᵐ-allowed ⊎ M₂.Trivial → T M₁.𝟘ᵐ-allowed ⊎ M₁.Trivial

    -- The functions tr and tr-Σ reflect the Prodrec-allowed property
    -- in a certain way.
    Prodrec-reflected :
      m₁ ≳ᵐ m₂ →
      R₂.Prodrec-allowed m₂ (tr r) (tr-Σ p) (tr q) →
      R₁.Prodrec-allowed m₁ r p q

    -- The function tr reflects the Unitrec-allowed property in a
    -- certain way.
    Unitrec-reflected :
      m₁ ≳ᵐ m₂ →
      R₂.Unitrec-allowed m₂ (tr p) (tr q) →
      R₁.Unitrec-allowed m₁ p q

    -- The function tr reflects the Emptyrec-allowed property in a
    -- certain way.
    Emptyrec-reflected :
      m₁ ≳ᵐ m₂ →
      R₂.Emptyrec-allowed m₂ (tr p) →
      R₁.Emptyrec-allowed m₁ p

    -- The []-cong-allowed-mode property is reflected in a certain way.
    []-cong-reflected :
      m₁ ≳ᵐ m₂ →
      R₂.[]-cong-allowed-mode s m₂ →
      R₁.[]-cong-allowed-mode s m₁


    -- If m₁ ≈ᵐ m₂ holds, then R₂.Erased-matches-for-J m₂ is bounded
    -- by R₁.erased-matches-for-J m₁.
    erased-matches-for-J-reflected :
      m₁ ≈ᵐ m₂ →
      R₂.erased-matches-for-J m₂ ≤ᵉᵐ R₁.erased-matches-for-J m₁

    -- If m₁ ≈ᵐ m₂ holds, then R₂.Erased-matches-for-K m₂ is bounded
    -- by R₁.erased-matches-for-K m₁.
    erased-matches-for-K-reflected :
      m₁ ≈ᵐ m₂ →
      R₂.erased-matches-for-K m₂ ≤ᵉᵐ R₁.erased-matches-for-K m₁

  open Common-properties common-properties public

opaque

  -- For every value R the identity function reflects
  -- Usage-restrictions for R and R.

  Are-reflecting-usage-restrictions-id :
    Are-reflecting-usage-restrictions R R idᶠ idᶠ
  Are-reflecting-usage-restrictions-id = λ where
      .common-properties              → Common-properties-reflexive
      .𝟘ᵐ-reflected                   → idᶠ
      .Prodrec-reflected              → ≳ᵐ→←₁
      .Unitrec-reflected              → ≳ᵐ→←₁
      .Emptyrec-reflected             → ≳ᵐ→←₁
      .[]-cong-reflected              → ≳ᵐ→←₁
      .erased-matches-for-J-reflected → ≈ᵐ→≤ᵉᵐ₁ ∘→ ≈ᵐ-symmetric
      .erased-matches-for-K-reflected → ≈ᵐ→≤ᵉᵐ₁ ∘→ ≈ᵐ-symmetric
    where
    open Are-reflecting-usage-restrictions

opaque

  -- Composition preserves Are-reflecting-usage-restrictions (in a
  -- certain sense).

  Are-reflecting-usage-restrictions-∘ :
    Are-reflecting-usage-restrictions R₂ R₃ tr₁ tr-Σ₁ →
    Are-reflecting-usage-restrictions R₁ R₂ tr₂ tr-Σ₂ →
    Are-reflecting-usage-restrictions
      R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
  Are-reflecting-usage-restrictions-∘ m₁ m₂ = λ where
      .common-properties →
        Common-properties-transitive R₂.common-properties
          R₁.common-properties
      .𝟘ᵐ-reflected →
        R₂.𝟘ᵐ-reflected ∘→ R₁.𝟘ᵐ-reflected
      .Prodrec-reflected →
        ≳ᵐ→←₂ R₂.𝟘ᵐ-preserved R₁.𝟘ᵐ-reflected R₁.Prodrec-reflected
          R₂.Prodrec-reflected
      .Unitrec-reflected →
        ≳ᵐ→←₂ R₂.𝟘ᵐ-preserved R₁.𝟘ᵐ-reflected R₁.Unitrec-reflected
          R₂.Unitrec-reflected
      .Emptyrec-reflected →
        ≳ᵐ→←₂ R₂.𝟘ᵐ-preserved R₁.𝟘ᵐ-reflected R₁.Emptyrec-reflected
          R₂.Emptyrec-reflected
      .[]-cong-reflected →
        ≳ᵐ→←₂ R₂.𝟘ᵐ-preserved R₁.𝟘ᵐ-reflected R₁.[]-cong-reflected
          R₂.[]-cong-reflected
      .erased-matches-for-J-reflected →
        ≈ᵐ→≥ᵉᵐ₂ R₂.𝟘ᵐ-preserved R₁.erased-matches-for-J-reflected
          R₂.erased-matches-for-J-reflected
      .erased-matches-for-K-reflected →
        ≈ᵐ→≥ᵉᵐ₂ R₂.𝟘ᵐ-preserved R₁.erased-matches-for-K-reflected
          R₂.erased-matches-for-K-reflected
    where
    open Are-reflecting-usage-restrictions
    module R₁ = Are-reflecting-usage-restrictions m₁
    module R₂ = Are-reflecting-usage-restrictions m₂
