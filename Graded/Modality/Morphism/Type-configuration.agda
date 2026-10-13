------------------------------------------------------------------------
-- Some relations between type configurations
------------------------------------------------------------------------

module Graded.Modality.Morphism.Type-configuration where

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎

open import Configuration-types
import Configuration-types.Instance.Type-configuration
open import Configuration-types.Omega

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised
open import Definition.Untyped.QuantityTranslation

open import Graded.Modality
open import Graded.Modality.Morphism
import Graded.Modality.Properties

private variable
  trp trp₁ trp₂       : Bool
  TC TC₁ TC₂ TC₃      : Type-configuration _
  b                   : BinderMode
  M M₁ M₂             : Set _
  𝕄₂ 𝕄₃               : Modality _
  tr₁ tr₂ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q                 : M
  s                   : Strength

------------------------------------------------------------------------
-- Is-Σ-morphism-TC and Is-Σ-order-embedding-TC

-- A collection of properties relating the type configurations and
-- functions. The type is called "Is-Σ-morphism-TC" because it is used
-- together with Is-morphism and Is-Σ-morphism, see
-- Definition.Typed.QuantityTranslation.

record Is-Σ-morphism-TC
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
         (transparent : Bool)
         (TC₁ : Type-configuration 𝕄₁) (TC₂ : Type-configuration 𝕄₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module M₁  = Modality 𝕄₁
    module M₂  = Modality 𝕄₂
    module TC₁ = Type-configuration TC₁
    module TC₂ = Type-configuration TC₂

  open Configuration-types.Instance.Type-configuration TC₁
  open Configuration-types.Instance.Type-configuration TC₂

  field
    -- The flag TC₁.unfolding-mode is equal to TC₂.unfolding-mode.
    unfolding-mode-preserved :
      TC₁.unfolding-mode ≡ TC₂.unfolding-mode

    -- TC₁.level-support is bounded by TC₂.level-support.
    level-support-preserved :
      TC₁.level-support ≤LS TC₂.level-support

    -- If TC₁.Omega-plus-allowed holds, then TC₂.Omega-plus-allowed
    -- holds.
    Omega-plus-preserved :
      TC₁.Omega-plus-allowed → TC₂.Omega-plus-allowed

    -- TC₁.Unitʷ-η implies TC₂.Unitʷ-η.
    Unitʷ-η-preserved :
      TC₁.Unitʷ-η → TC₂.Unitʷ-η

    -- If TC₁.Unit-allowed s holds, then TC₂.Unit-allowed s holds.
    Unit-preserved :
      TC₁.Unit-allowed s → TC₂.Unit-allowed s

    -- The functions tr and tr-Σ preserve the ΠΣ-allowed property in a
    -- certain way.
    ΠΣ-preserved :
      TC₁.ΠΣ-allowed b p q →
      TC₂.ΠΣ-allowed b (tr-BinderMode transparent tr tr-Σ b p) (tr q)

    -- If the translation does not make every definition transparent
    -- and TC₁.Opacity-allowed holds, then TC₂.Opacity-allowed holds.
    Opacity-preserved :
      ¬ T transparent → TC₁.Opacity-allowed → TC₂.Opacity-allowed

    -- If TC₁.K-allowed holds, then TC₂.K-allowed holds.
    K-preserved :
      TC₁.K-allowed → TC₂.K-allowed

    -- If TC₁.[]-cong-allowed holds, then TC₂.[]-cong-allowed holds.
    []-cong-preserved :
      TC₁.[]-cong-allowed s → TC₂.[]-cong-allowed s

    -- If TC₁.Equality-reflection holds, then TC₂.Equality-reflection
    -- holds.
    Equality-reflection-preserved :
      TC₁.Equality-reflection → TC₂.Equality-reflection

    -- If TC₁.Quot-allowed holds, then TC₂.Quot-allowed holds.
    Quot-preserved :
      TC₁.Quot-allowed → TC₂.Quot-allowed

    -- If TC₁.Quot-allowed holds, then 𝟘 is translated to 𝟘.
    Quot-allowed→tr-𝟘≡𝟘 :
      TC₁.Quot-allowed → tr M₁.𝟘 ≡ M₂.𝟘

    -- If TC₁.Omega-allowed holds, then TC₂.Omega-allowed holds.
    Omega-allowed-preserved :
      TC₁.Omega-allowed → TC₂.Omega-allowed

    -- If both modalities support a dedicated ω grade, then the
    -- morphism must be omega-preserving.
    omega-preserving :
      ⦃ ok₁ : TC₁.Omega-allowed ⦄ ⦃ ok₂ : TC₂.Omega-allowed ⦄ →
      Is-omega-preserving-morphism 𝕄₁ 𝕄₂ tr

  private
    open
      module OP ⦃ ok₁ : TC₁.Omega-allowed ⦄
                ⦃ ok₂ : TC₂.Omega-allowed ⦄ =
        Is-omega-preserving-morphism omega-preserving
      public

  opaque
    unfolding Type-configuration.Level-is-small

    -- TC₁.Level-is-small implies TC₂.Level-is-small.

    Level-is-small-preserved : TC₁.Level-is-small → TC₂.Level-is-small
    Level-is-small-preserved = ≤LS→≡small→≡small level-support-preserved

  opaque
    unfolding Type-configuration.Level-allowed

    -- TC₁.Level-allowed holds iff TC₂.Level-allowed holds.

    Level-allowed⇔ : TC₁.Level-allowed ⇔ TC₂.Level-allowed
    Level-allowed⇔ =
      ≤LS→≢only-literals⇔≢only-literals level-support-preserved

-- A collection of properties relating the type configurations and
-- functions.

record Is-Σ-order-embedding-TC
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
         (transparent : Bool)
         (TC₁ : Type-configuration 𝕄₁) (TC₂ : Type-configuration 𝕄₂)
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module M₁  = Modality 𝕄₁
    module M₂  = Modality 𝕄₂
    module TC₁ = Type-configuration TC₁
    module TC₂ = Type-configuration TC₂

  field
    -- "Order embeddings" have to be "morphisms".
    --
    -- The contents of this record type are not re-exported, because
    -- the type
    -- Graded.Modality.Morphism.Configuration.Is-Σ-order-embedding-C
    -- includes two values of this type, reachable via different
    -- fields.
    is-Σ-morphism-TC : Is-Σ-morphism-TC transparent TC₁ TC₂ tr tr-Σ

    -- The flag TC₁.unfolding-mode is equal to TC₂.unfolding-mode.
    unfolding-mode-reflected :
      TC₁.unfolding-mode ≡ TC₂.unfolding-mode

    -- TC₂.level-support is bounded by TC₁.level-support.
    level-support-reflected :
      TC₂.level-support ≤LS TC₁.level-support

    -- TC₂.Unitʷ-η implies TC₁.Unitʷ-η.
    Unitʷ-η-reflected :
      TC₂.Unitʷ-η → TC₁.Unitʷ-η

    -- If TC₂.Unit-allowed s holds, then TC₁.Unit-allowed s holds.
    Unit-reflected :
      TC₂.Unit-allowed s → TC₁.Unit-allowed s

    -- The functions tr and tr-Σ reflect the ΠΣ-allowed property in a
    -- certain way.
    ΠΣ-reflected :
      TC₂.ΠΣ-allowed b (tr-BinderMode transparent tr tr-Σ b p) (tr q) →
      TC₁.ΠΣ-allowed b p q

    -- If TC₂.Opacity-allowed holds, then TC₁.Opacity-allowed holds.
    Opacity-reflected :
      TC₂.Opacity-allowed → TC₁.Opacity-allowed

    -- If TC₂.K-allowed holds, then TC₁.K-allowed holds.
    K-reflected :
      TC₂.K-allowed → TC₁.K-allowed

    -- If TC₂.[]-cong-allowed s holds or 𝕄₂ is trivial, then
    -- TC₁.[]-cong-allowed s holds or 𝕄₁ is trivial.
    []-cong-reflected :
      TC₂.[]-cong-allowed s ⊎ M₂.Trivial →
      TC₁.[]-cong-allowed s ⊎ M₁.Trivial

    -- If TC₂.Equality-reflection holds, then TC₁.Equality-reflection
    -- holds.
    Equality-reflection-reflected :
      TC₂.Equality-reflection → TC₁.Equality-reflection

    -- If TC₂.Quot-allowed s holds or 𝕄₂ is trivial, then
    -- TC₁.Quot-allowed s holds or 𝕄₁ is trivial.
    Quot-reflected :
      TC₂.Quot-allowed ⊎ M₂.Trivial → TC₁.Quot-allowed ⊎ M₁.Trivial

    -- If TC₂.Omega-allowed holds, then TC₁.Omega-allowed holds.
    Omega-allowed-reflected :
      TC₂.Omega-allowed → TC₁.Omega-allowed

  opaque
    unfolding Type-configuration.Level-is-small

    -- TC₂.Level-is-small implies TC₁.Level-is-small.

    Level-is-small-reflected : TC₂.Level-is-small → TC₁.Level-is-small
    Level-is-small-reflected = ≤LS→≡small→≡small level-support-reflected

  opaque

    -- A variant of Quot-reflected.

    Quot-reflected′ :
      TC₂.Quot-allowed →
      TC₁.Quot-allowed × ¬ M₁.Trivial ⊎ M₁.Trivial
    Quot-reflected′ ok with Graded.Modality.Properties.trivial? 𝕄₁
    … | yes triv = inj₂ triv
    … | no not   = ⊎.map (_, not) idᶠ (Quot-reflected (inj₁ ok))

------------------------------------------------------------------------
-- Identity

-- An identity lemma for Is-Σ-morphism-TC.

Is-Σ-morphism-TC-id : Is-Σ-morphism-TC trp TC TC idᶠ idᶠ
Is-Σ-morphism-TC-id {TC} = λ where
    .unfolding-mode-preserved         → refl
    .level-support-preserved          → refl-≤LS
    .Omega-plus-preserved             → idᶠ
    .Unitʷ-η-preserved                → idᶠ
    .Unit-preserved                   → idᶠ
    .ΠΣ-preserved {b = BMΠ}           → idᶠ
    .ΠΣ-preserved {b = BMΣ _}         → idᶠ
    .Opacity-preserved                → λ _ → idᶠ
    .K-preserved                      → idᶠ
    .[]-cong-preserved                → idᶠ
    .Equality-reflection-preserved    → idᶠ
    .Quot-preserved                   → idᶠ
    .Quot-allowed→tr-𝟘≡𝟘              → λ _ → refl
    .Omega-allowed-preserved          → idᶠ
    .omega-preserving ⦃ ok₁ ⦄ ⦃ ok₂ ⦄ →
      case With-omega-propositional _ ok₁ ok₂ of λ {
        refl →
      Is-omega-preserving-morphism-id }
  where
  open Configuration-types.Instance.Type-configuration TC
  open Is-Σ-morphism-TC
  open Type-configuration TC

-- An identity lemma for Is-Σ-order-embedding-TC.

Is-Σ-order-embedding-TC-id : Is-Σ-order-embedding-TC trp TC TC idᶠ idᶠ
Is-Σ-order-embedding-TC-id {TC} = λ where
    .is-Σ-morphism-TC              → Is-Σ-morphism-TC-id
    .unfolding-mode-reflected      → refl
    .level-support-reflected       → refl-≤LS
    .Unitʷ-η-reflected             → idᶠ
    .Unit-reflected                → idᶠ
    .ΠΣ-reflected {b = BMΠ}        → idᶠ
    .ΠΣ-reflected {b = BMΣ _}      → idᶠ
    .Opacity-reflected             → idᶠ
    .K-reflected                   → idᶠ
    .[]-cong-reflected             → idᶠ
    .Equality-reflection-reflected → idᶠ
    .Quot-reflected                → idᶠ
    .Omega-allowed-reflected       → idᶠ
  where
  open Is-Σ-order-embedding-TC
  open Type-configuration TC

------------------------------------------------------------------------
-- Composition

-- A composition lemma for Is-Σ-morphism-TC.

Is-Σ-morphism-TC-∘ :
  {TC₂ : Type-configuration 𝕄₂}
  {TC₃ : Type-configuration 𝕄₃} →
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-Σ-morphism-TC trp₁ TC₂ TC₃ tr₁ tr-Σ₁ →
  Is-Σ-morphism-TC trp₂ TC₁ TC₂ tr₂ tr-Σ₂ →
  Is-Σ-morphism-TC (trp₁ ∨ trp₂) TC₁ TC₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Is-Σ-morphism-TC-∘ {tr₁} {TC₂} m m₁ m₂ = λ where
    .unfolding-mode-preserved →
       trans M₂.unfolding-mode-preserved M₁.unfolding-mode-preserved
    .level-support-preserved →
      trans-≤LS M₂.level-support-preserved M₁.level-support-preserved
    .Omega-plus-preserved →
      M₁.Omega-plus-preserved ∘→ M₂.Omega-plus-preserved
    .Unitʷ-η-preserved →
      M₁.Unitʷ-η-preserved ∘→ M₂.Unitʷ-η-preserved
    .Unit-preserved →
      M₁.Unit-preserved ∘→ M₂.Unit-preserved
    .ΠΣ-preserved {b = BMΠ} →
      M₁.ΠΣ-preserved ∘→ M₂.ΠΣ-preserved
    .ΠΣ-preserved {b = BMΣ _} →
      M₁.ΠΣ-preserved ∘→ M₂.ΠΣ-preserved
    .Opacity-preserved ok →
      let ok = ok ∘→ T-∨ .proj₂ in
      M₁.Opacity-preserved (ok ∘→ inj₁) ∘→
      M₂.Opacity-preserved (ok ∘→ inj₂)
    .K-preserved →
      M₁.K-preserved ∘→ M₂.K-preserved
    .[]-cong-preserved →
      M₁.[]-cong-preserved ∘→ M₂.[]-cong-preserved
    .Equality-reflection-preserved →
      M₁.Equality-reflection-preserved ∘→
      M₂.Equality-reflection-preserved
    .Quot-preserved →
      M₁.Quot-preserved ∘→ M₂.Quot-preserved
    .Quot-allowed→tr-𝟘≡𝟘 ok →
      trans (cong tr₁ (M₂.Quot-allowed→tr-𝟘≡𝟘 ok))
        (M₁.Quot-allowed→tr-𝟘≡𝟘 (M₂.Quot-preserved ok))
    .Omega-allowed-preserved →
      M₁.Omega-allowed-preserved ∘→ M₂.Omega-allowed-preserved
    .omega-preserving ⦃ ok₁ ⦄ ⦃ ok₂ = ok₃ ⦄ →
      let ok₂ = M₂.Omega-allowed-preserved ok₁ in
      Is-omega-preserving-morphism-∘ ⦃ has-ω₁ = _ ⦄
        ⦃ has-ω₂ = Omega-allowed→Has-omega ⦃ ok = ok₂ ⦄ ⦄ ⦃ has-ω₃ = _ ⦄
        m (M₁.omega-preserving ⦃ ok₁ = ok₂ ⦄)
        (M₂.omega-preserving ⦃ ok₂ = ok₂ ⦄)
  where
  open Configuration-types.Instance.Type-configuration TC₂
  open Is-Σ-morphism-TC
  module M₁ = Is-Σ-morphism-TC m₁
  module M₂ = Is-Σ-morphism-TC m₂

-- A composition lemma for Is-Σ-order-embedding-TC.

Is-Σ-order-embedding-TC-∘ :
  {TC₂ : Type-configuration 𝕄₂}
  {TC₃ : Type-configuration 𝕄₃} →
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-Σ-order-embedding-TC trp₁ TC₂ TC₃ tr₁ tr-Σ₁ →
  Is-Σ-order-embedding-TC trp₂ TC₁ TC₂ tr₂ tr-Σ₂ →
  Is-Σ-order-embedding-TC (trp₁ ∨ trp₂) TC₁ TC₃ (tr₁ ∘→ tr₂)
    (tr-Σ₁ ∘→ tr-Σ₂)
Is-Σ-order-embedding-TC-∘ m m₁ m₂ = λ where
    .is-Σ-morphism-TC →
      Is-Σ-morphism-TC-∘ m M₁.is-Σ-morphism-TC M₂.is-Σ-morphism-TC
    .unfolding-mode-reflected →
       trans M₂.unfolding-mode-reflected M₁.unfolding-mode-reflected
    .level-support-reflected →
      trans-≤LS M₁.level-support-reflected M₂.level-support-reflected
    .Unitʷ-η-reflected →
      M₂.Unitʷ-η-reflected ∘→ M₁.Unitʷ-η-reflected
    .Unit-reflected →
      M₂.Unit-reflected ∘→ M₁.Unit-reflected
    .ΠΣ-reflected {b = BMΠ} →
      M₂.ΠΣ-reflected ∘→ M₁.ΠΣ-reflected
    .ΠΣ-reflected {b = BMΣ _} →
      M₂.ΠΣ-reflected ∘→ M₁.ΠΣ-reflected
    .Opacity-reflected →
      M₂.Opacity-reflected ∘→ M₁.Opacity-reflected
    .K-reflected →
      M₂.K-reflected ∘→ M₁.K-reflected
    .[]-cong-reflected →
      M₂.[]-cong-reflected ∘→ M₁.[]-cong-reflected
    .Equality-reflection-reflected →
      M₂.Equality-reflection-reflected ∘→
      M₁.Equality-reflection-reflected
    .Quot-reflected →
      M₂.Quot-reflected ∘→ M₁.Quot-reflected
    .Omega-allowed-reflected →
      M₂.Omega-allowed-reflected ∘→ M₁.Omega-allowed-reflected
  where
  open Is-Σ-order-embedding-TC
  module M₁ = Is-Σ-order-embedding-TC m₁
  module M₂ = Is-Σ-order-embedding-TC m₂
