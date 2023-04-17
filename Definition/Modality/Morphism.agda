------------------------------------------------------------------------
-- Modality morphisms
------------------------------------------------------------------------

-- It might make sense to replace some of the proofs below with a lot
-- of cases with automated proofs.

module Definition.Modality.Morphism where

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

open import Definition.Modality
open import Definition.Modality.Instances.Affine as A
  using (Affine; affineModality)
open import Definition.Modality.Instances.Erasure as E
  using (Erasure; 𝟘; ω)
open import Definition.Modality.Instances.Erasure.Modality
  using (ErasureModality)
open import Definition.Modality.Instances.Linear-or-affine as LA
  using (Linear-or-affine; 𝟘; 𝟙; ≤𝟙; ≤ω; linear-or-affine)
open import Definition.Modality.Instances.Linearity as L
  using (Linearity; linearityModality)
open import Definition.Modality.Instances.Unit using (UnitModality)
open import Definition.Modality.Instances.Zero-one-many as ZOM
  using (Zero-one-many; 𝟘; 𝟙; ω; zero-one-many-greatest)
import Definition.Modality.Properties
open import Definition.Modality.Restrictions
open import Definition.Modality.Restrictions.Definitions

open import Definition.Mode as Mode hiding (module Mode)

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.QuantityTranslation

private variable
  a₁ a₂                          : Level
  𝟙≤𝟘 ok                         : Bool
  not-ok                         : ¬ T _
  rt rt₁ rt₂ rt₃                 : Term-restrictions _
  r r₁ r₂                        : Restrictions _
  M₁ M₂                          : Set _
  𝕄 𝕄₁ 𝕄₂ 𝕄₃                     : Modality _
  b                              : BinderMode
  tr tr₁ tr₂ tr-Σₚ tr-Σₚ₁ tr-Σₚ₂ : M₁ → M₂

------------------------------------------------------------------------
-- Morphisms

-- The definitions in this section have been tailored mainly to make
-- it possible to prove the theorems in
-- Definition.Modality.Usage.QuantityTranslation for certain
-- translations between certain modalities. Perhaps other definitions
-- are more suitable for other applications.

-- The property of being a Modality morphism.

record Is-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module M₁ = Modality 𝕄₁
    open module M₂ = Modality 𝕄₂ using (_≤_; _<_)

  field
    -- If 𝟘ᵐ is allowed in the source modality, then it is allowed in
    -- the target modality.
    𝟘ᵐ-in-second-if-in-first : T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed

    -- The translation of 𝟘 is bounded by 𝟘.
    tr-𝟘-≤ : tr M₁.𝟘 ≤ M₂.𝟘

    -- If 𝟘ᵐ is allowed in the source modality, then a quantity p is
    -- mapped to 𝟘 exactly when p itself is 𝟘.
    tr-≡-𝟘-⇔ : ∀ {p} → T M₁.𝟘ᵐ-allowed → tr p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘

    -- If 𝟘ᵐ is allowed in the target modality but not the source
    -- modality, then quantities are translated to quantities that are
    -- strictly below 𝟘.
    tr-<-𝟘 : ∀ {p} → ¬ T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed → tr p < M₂.𝟘

    -- The translation of 𝟙 is bounded by 𝟙.
    tr-𝟙 : tr M₁.𝟙 ≤ M₂.𝟙

    -- The translation commutes with addition up to _≤_.
    tr-+ : ∀ {p q} → tr (p M₁.+ q) ≤ tr p M₂.+ tr q

    -- The translation commutes with multiplication.
    tr-· : ∀ {p q} → tr (p M₁.· q) ≡ tr p M₂.· tr q

    -- The translation commutes with meet up to _≤_.
    tr-∧ : ∀ {p q} → tr (p M₁.∧ q) ≤ tr p M₂.∧ tr q

    -- The translation commutes with star up to _≤_.
    tr-⊛ : ∀ {p q r} → tr (p M₁.⊛ q ▷ r) ≤ tr p M₂.⊛ tr q ▷ tr r

  -- If 𝟘ᵐ is allowed in the source modality, then 𝟘 is translated to
  -- 𝟘.

  tr-𝟘-≡ : T M₁.𝟘ᵐ-allowed → tr M₁.𝟘 ≡ M₂.𝟘
  tr-𝟘-≡ ok = tr-≡-𝟘-⇔ ok .proj₂ refl

  -- The translation is monotone.

  tr-monotone : ∀ {p q} → p M₁.≤ q → tr p M₂.≤ tr q
  tr-monotone {p = p} {q = q} p≤q = ≤-antisym
    (begin
       tr p            ≡⟨ cong tr p≤q ⟩
       tr (p M₁.∧ q)   ≤⟨ tr-∧ ⟩
       tr p M₂.∧ tr q  ∎)
    (begin
       (tr p M₂.∧ tr q)  ≤⟨ ∧-decreasingˡ _ _ ⟩
       tr p              ∎)
    where
    open Definition.Modality.Properties 𝕄₂
    open Tools.Reasoning.PartialOrder ≤-poset

  -- If tr is injective and commutes with _∧_, then it is
  -- order-reflecting.

  tr-injective×∧→order-reflecting :
    (∀ {p q} → tr p ≡ tr q → p ≡ q) →
    (∀ {p q} → tr (p M₁.∧ q) ≡ tr p M₂.∧ tr q) →
    ∀ {p q} → tr p M₂.≤ tr q → p M₁.≤ q
  tr-injective×∧→order-reflecting
    tr-inj tr-∧ {p = p} {q = q} tr-p≤tr-q = tr-inj (
    tr p            ≡⟨ tr-p≤tr-q ⟩
    tr p M₂.∧ tr q  ≡˘⟨ tr-∧ ⟩
    tr (p M₁.∧ q)   ∎)
    where
    open Tools.Reasoning.PropositionalEquality

-- The property of being an order embedding.

record Is-order-embedding
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂

  field
    -- The translation tr is a morphism.
    tr-morphism : Is-morphism 𝕄₁ 𝕄₂ tr

    -- The translation is order-reflecting.
    tr-order-reflecting : ∀ {p q} → tr p M₂.≤ tr q → p M₁.≤ q

    -- If 𝟘ᵐ is allowed in the target modality but not the source
    -- modality, then the source modality is trivial.
    trivial : ¬ T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed → M₁.𝟙 ≡ M₁.𝟘

    -- Either the source modality is trivial, or the translation of 𝟘
    -- is equal to 𝟘.
    trivial-⊎-tr-𝟘 : (M₁.𝟙 ≡ M₁.𝟘) ⊎ (tr M₁.𝟘 ≡ M₂.𝟘)

    -- For every target quantity p there is a source quantity p′ such
    -- that the translation of p′ is bounded by p.
    tr-≤ : ∀ {p} → ∃ λ p′ → tr p′ M₂.≤ p

    -- If the translation of p is bounded by 𝟙, then p is bounded by
    -- 𝟙.
    tr-≤-𝟙 : ∀ {p} → tr p M₂.≤ M₂.𝟙 → p M₁.≤ M₁.𝟙

    -- If the translation of p is bounded by q + r, then there are q′
    -- and r′ such that the translation of q′ is bounded by q, the
    -- translation of r′ is bounded by r, and p is bounded by q′ + r′.
    tr-≤-+ :
      ∀ {p q r} →
      tr p M₂.≤ q M₂.+ r →
      ∃₂ λ q′ r′ → tr q′ M₂.≤ q × tr r′ M₂.≤ r × p M₁.≤ q′ M₁.+ r′

    -- If the translation of p is bounded by tr q · r, then there is
    -- an r′ such that the translation of r′ is bounded by r, and p is
    -- bounded by q · r′.
    tr-≤-· :
      ∀ {p q r} →
      tr p M₂.≤ tr q M₂.· r →
      ∃ λ r′ → tr r′ M₂.≤ r × p M₁.≤ q M₁.· r′

    -- If the translation of p is bounded by q ∧ r, then there are q′
    -- and r′ such that the translation of q′ is bounded by q, the
    -- translation of r′ is bounded by r, and p is bounded by q′ ∧ r′.
    tr-≤-∧ :
      ∀ {p q r} →
      tr p M₂.≤ q M₂.∧ r →
      ∃₂ λ q′ r′ → tr q′ M₂.≤ q × tr r′ M₂.≤ r × p M₁.≤ q′ M₁.∧ r′

    -- A variant of the last properties above for the function that is
    -- used in the usage rule for natrec.
    tr-≤-⊛ :
      ∀ {p q₁ q₂ q₃ r s} →
      tr p M₂.≤ (q₁ M₂.∧ q₂) M₂.⊛ q₃ M₂.+ tr r M₂.· q₂ ▷ tr s →
      ∃₃ λ q₁′ q₂′ q₃′ →
         tr q₁′ M₂.≤ q₁ × tr q₂′ M₂.≤ q₂ × tr q₃′ M₂.≤ q₃ ×
         p M₁.≤ (q₁′ M₁.∧ q₂′) M₁.⊛ q₃′ M₁.+ r M₁.· q₂′ ▷ s

  open Is-morphism tr-morphism public

  -- The translation is injective.

  tr-injective : ∀ {p q} → tr p ≡ tr q → p ≡ q
  tr-injective tr-p≡tr-q = P₁.≤-antisym
    (tr-order-reflecting (P₂.≤-reflexive tr-p≡tr-q))
    (tr-order-reflecting (P₂.≤-reflexive (sym tr-p≡tr-q)))
    where
    module P₁ = Definition.Modality.Properties 𝕄₁
    module P₂ = Definition.Modality.Properties 𝕄₂

-- The property of being a Σₚ-morphism (with respect to a given
-- function).
--
-- Note that Σₚ-morphisms do not have to be morphisms (see
-- Σₚ-order-embedding-but-not-order-embedding below).

record Is-Σₚ-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr tr-Σₚ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂

  field
    -- The regular translation function tr is bounded by the
    -- Σₚ-translation tr-Σₚ.
    tr-≤-tr-Σₚ : ∀ {p} → tr p M₂.≤ tr-Σₚ p

    -- If 𝟘ᵐ is allowed in the target modality and tr-Σₚ p is equal
    -- to 𝟘, then 𝟘ᵐ is allowed in the source modality and p is equal
    -- to 𝟘.
    tr-Σₚ-≡-𝟘-→ :
      ∀ {p} →
      T M₂.𝟘ᵐ-allowed → tr-Σₚ p ≡ M₂.𝟘 → T M₁.𝟘ᵐ-allowed × p ≡ M₁.𝟘

    -- If p is bounded by 𝟙, then tr-Σₚ p is bounded by 𝟙.
    tr-Σₚ-≤-𝟙 : ∀ {p} → p M₁.≤ M₁.𝟙 → tr-Σₚ p M₂.≤ M₂.𝟙

  -- If 𝟘ᵐ is allowed in the target modality but not the source
  -- modality, then tr-Σₚ translates quantities to quantities that are
  -- not equal to 𝟘.

  tr-Σₚ-≢-𝟘 :
    ∀ {p} → ¬ T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed → tr-Σₚ p ≢ M₂.𝟘
  tr-Σₚ-≢-𝟘 not-ok ok tr-p≡𝟘 = not-ok (tr-Σₚ-≡-𝟘-→ ok tr-p≡𝟘 .proj₁)

  -- If 𝟘ᵐ is allowed in the source and target modalities, then tr-Σₚ
  -- translates 𝟘 to 𝟘 (assuming that tr is a morphism from 𝕄₁ to 𝕄₂).

  tr-Σₚ-𝟘-≡ :
    Is-morphism 𝕄₁ 𝕄₂ tr →
    T M₁.𝟘ᵐ-allowed → tr-Σₚ M₁.𝟘 ≡ M₂.𝟘
  tr-Σₚ-𝟘-≡ m ok = 𝟘≮ (𝟘ᵐ-in-second-if-in-first ok) (begin
    M₂.𝟘        ≡˘⟨ tr-𝟘-≡ ok ⟩
    tr M₁.𝟘     ≤⟨ tr-≤-tr-Σₚ ⟩
    tr-Σₚ M₁.𝟘  ∎)
    where
    open Is-morphism m
    open Definition.Modality.Properties 𝕄₂
    open Tools.Reasoning.PartialOrder ≤-poset

  -- If tr-Σₚ p is bounded by 𝟙, then p is bounded by 𝟙 (assuming that
  -- tr is an order embedding from 𝕄₁ to 𝕄₂).

  tr-Σₚ-≤-𝟙-→ :
    ∀ {p} →
    Is-order-embedding 𝕄₁ 𝕄₂ tr →
    tr-Σₚ p M₂.≤ M₂.𝟙 → p M₁.≤ M₁.𝟙
  tr-Σₚ-≤-𝟙-→ {p = p} m tr-Σₚ-p≤𝟙 = Is-order-embedding.tr-≤-𝟙 m (begin
    tr p     ≤⟨ tr-≤-tr-Σₚ ⟩
    tr-Σₚ p  ≤⟨ tr-Σₚ-p≤𝟙 ⟩
    M₂.𝟙     ∎)
    where
    open Definition.Modality.Properties 𝕄₂
    open Tools.Reasoning.PartialOrder ≤-poset

-- The property of being an order embedding for Σₚ (with respect to a
-- given function).
--
-- Note that these "order embeddings" do not need to be order
-- embeddings (see Σₚ-order-embedding-but-not-order-embedding below).

record Is-Σₚ-order-embedding
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr tr-Σₚ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂

  field
    -- The translation function tr-Σₚ is a Σₚ-morphism with respect to
    -- tr.
    tr-Σₚ-morphism : Is-Σₚ-morphism 𝕄₁ 𝕄₂ tr tr-Σₚ

    -- If the regular translation of p is bounded by tr-Σₚ q · r, then
    -- there is some r′ such that the regular translation of r′ is r
    -- and p is bounded by q · r′.
    tr-≤-tr-Σₚ-→ :
      ∀ {p q r} →
      tr p M₂.≤ tr-Σₚ q M₂.· r → ∃ λ r′ → tr r′ M₂.≤ r × p M₁.≤ q M₁.· r′

  open Is-Σₚ-morphism tr-Σₚ-morphism public

-- The property of preserving Term-restrictions.

record Are-preserving-term-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (r₁ : Term-restrictions M₁) (r₂ : Term-restrictions M₂)
         (tr tr-Σₚ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Term-restrictions r₁
    module R₂ = Term-restrictions r₂

  field
    -- The functions tr and tr-Σₚ preserve the Binder property in a
    -- certain way.
    Binder-preserved :
      ∀ {p q} →
      R₁.Binder b p q → R₂.Binder b (tr-BinderMode tr tr-Σₚ b p) (tr q)

    -- The function tr preserves the Prodrec property.
    Prodrec-preserved :
      ∀ {p q r} → R₁.Prodrec p q r → R₂.Prodrec (tr p) (tr q) (tr r)

-- The property of reflecting Term-restrictions.

record Are-reflecting-term-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (r₁ : Term-restrictions M₁) (r₂ : Term-restrictions M₂)
         (tr tr-Σₚ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Term-restrictions r₁
    module R₂ = Term-restrictions r₂

  field
    -- The functions tr and tr-Σₚ reflect the Binder property in a
    -- certain way.
    Binder-reflected :
      ∀ {p q} →
      R₂.Binder b (tr-BinderMode tr tr-Σₚ b p) (tr q) → R₁.Binder b p q

    -- The function tr reflects the Prodrec property.
    Prodrec-reflected :
      ∀ {p q r} → R₂.Prodrec (tr p) (tr q) (tr r) → R₁.Prodrec p q r

------------------------------------------------------------------------
-- Morphisms are Σₚ-morphisms with respect to themselves, and order
-- embeddings are order embeddings for Σₚ with respect to themselves

-- If tr is a morphism, then it is a Σₚ-morphism with respect to
-- itself.

Is-morphism→Is-Σₚ-morphism :
  Is-morphism 𝕄₁ 𝕄₂ tr →
  Is-Σₚ-morphism 𝕄₁ 𝕄₂ tr tr
Is-morphism→Is-Σₚ-morphism {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} {tr = tr} m = λ where
    .Is-Σₚ-morphism.tr-≤-tr-Σₚ →
      MP₂.≤-refl
    .Is-Σₚ-morphism.tr-Σₚ-≡-𝟘-→ ok tr-p≡𝟘 →
      𝟘ᵐ-allowed-elim 𝕄₁
        (λ ok → ok , tr-≡-𝟘-⇔ ok .proj₁ tr-p≡𝟘)
        (λ not-ok → ⊥-elim (tr-<-𝟘 not-ok ok .proj₂ tr-p≡𝟘))
    .Is-Σₚ-morphism.tr-Σₚ-≤-𝟙 {p = p} p≤𝟙 → begin
      tr p     ≤⟨ tr-monotone p≤𝟙 ⟩
      tr M₁.𝟙  ≤⟨ tr-𝟙 ⟩
      M₂.𝟙     ∎
  where
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module MP₂ = Definition.Modality.Properties 𝕄₂
  open Is-morphism m
  open Tools.Reasoning.PartialOrder MP₂.≤-poset

-- If tr is an order embedding, then it is an order embedding for Σₚ
-- with respect to itself.

Is-order-embedding→Is-Σₚ-order-embedding :
  Is-order-embedding 𝕄₁ 𝕄₂ tr →
  Is-Σₚ-order-embedding 𝕄₁ 𝕄₂ tr tr
Is-order-embedding→Is-Σₚ-order-embedding m = λ where
    .Is-Σₚ-order-embedding.tr-Σₚ-morphism →
      Is-morphism→Is-Σₚ-morphism tr-morphism
    .Is-Σₚ-order-embedding.tr-≤-tr-Σₚ-→ →
      tr-≤-·
  where
  open Is-order-embedding m

------------------------------------------------------------------------
-- Identity

-- The identity function is an order embedding for every modality.

Is-order-embedding-id : Is-order-embedding 𝕄 𝕄 idᶠ
Is-order-embedding-id {𝕄 = 𝕄} = λ where
    .tr-order-reflecting → idᶠ
    .trivial-⊎-tr-𝟘      → inj₂ refl
    .trivial not-ok ok   → ⊥-elim (not-ok ok)
    .tr-≤                → _ , ≤-refl
    .tr-≤-𝟙              → idᶠ
    .tr-≤-+ hyp          → _ , _ , ≤-refl , ≤-refl , hyp
    .tr-≤-· hyp          → _ , ≤-refl , hyp
    .tr-≤-∧ hyp          → _ , _ , ≤-refl , ≤-refl , hyp
    .tr-≤-⊛ hyp          →
      _ , _ , _ , ≤-refl , ≤-refl , ≤-refl , hyp
    .tr-morphism → λ where
      .tr-<-𝟘 not-ok ok            → ⊥-elim (not-ok ok)
      .tr-𝟙                        → ≤-refl
      .tr-𝟘-≤                      → ≤-refl
      .tr-≡-𝟘-⇔ _                  → idᶠ , idᶠ
      .tr-+                        → ≤-refl
      .tr-·                        → refl
      .tr-∧                        → ≤-refl
      .tr-⊛                        → ≤-refl
      .𝟘ᵐ-in-second-if-in-first    → idᶠ
  where
  open Definition.Modality.Properties 𝕄
  open Is-morphism
  open Is-order-embedding

-- For every value rt of type Term-restrictions the identity function
-- preserves Term-restrictions for rt and rt.

Are-preserving-term-restrictions-id :
  Are-preserving-term-restrictions rt rt idᶠ idᶠ
Are-preserving-term-restrictions-id {rt = rt} = λ where
    .Prodrec-preserved             → idᶠ
    .Binder-preserved {b = BMΠ}    → idᶠ
    .Binder-preserved {b = BMΣ Σₚ} → idᶠ
    .Binder-preserved {b = BMΣ Σᵣ} → idᶠ
  where
  open Are-preserving-term-restrictions
  open Term-restrictions rt

-- For every value rt of type Term-restrictions the identity function
-- reflects Term-restrictions for rt and rt.

Are-reflecting-term-restrictions-id :
  Are-reflecting-term-restrictions rt rt idᶠ idᶠ
Are-reflecting-term-restrictions-id {rt = rt} = λ where
    .Prodrec-reflected             → idᶠ
    .Binder-reflected {b = BMΠ}    → idᶠ
    .Binder-reflected {b = BMΣ Σₚ} → idᶠ
    .Binder-reflected {b = BMΣ Σᵣ} → idᶠ
  where
  open Are-reflecting-term-restrictions
  open Term-restrictions rt

------------------------------------------------------------------------
-- Composition

-- Composition preserves Is-morphism.

Is-morphism-∘ :
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-morphism 𝕄₁ 𝕄₂ tr₂ →
  Is-morphism 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂)
Is-morphism-∘
  {𝕄₂ = 𝕄₂} {𝕄₃ = 𝕄₃} {tr₁ = tr₁} {𝕄₁ = 𝕄₁} {tr₂ = tr₂} f g = λ where
    .Is-morphism.𝟘ᵐ-in-second-if-in-first →
      F.𝟘ᵐ-in-second-if-in-first ∘→ G.𝟘ᵐ-in-second-if-in-first
    .Is-morphism.tr-𝟘-≤ → let open R in begin
       tr₁ (tr₂ M₁.𝟘)  ≤⟨ F.tr-monotone G.tr-𝟘-≤ ⟩
       tr₁ M₂.𝟘        ≤⟨ F.tr-𝟘-≤ ⟩
       M₃.𝟘            ∎
    .Is-morphism.tr-≡-𝟘-⇔ ok →
      G.tr-≡-𝟘-⇔ ok ∘⇔ F.tr-≡-𝟘-⇔ (G.𝟘ᵐ-in-second-if-in-first ok)
    .Is-morphism.tr-<-𝟘 {p = p} not-ok₁ ok₃ →
      let open R in
      Mo₂.𝟘ᵐ-allowed-elim
        (λ ok₂ →
             (begin
                tr₁ (tr₂ p)  ≤⟨ F.tr-monotone (G.tr-<-𝟘 not-ok₁ ok₂ .proj₁) ⟩
                tr₁ M₂.𝟘     ≤⟨ F.tr-𝟘-≤ ⟩
                M₃.𝟘         ∎)
           , G.tr-<-𝟘 not-ok₁ ok₂ .proj₂ ∘→
             F.tr-≡-𝟘-⇔ ok₂ .proj₁)
        (λ not-ok₂ →
             (begin
                tr₁ (tr₂ p)  ≤⟨ F.tr-<-𝟘 not-ok₂ ok₃ .proj₁ ⟩
                M₃.𝟘         ∎)
           , F.tr-<-𝟘 not-ok₂ ok₃ .proj₂)
    .Is-morphism.tr-𝟙 → let open R in begin
       tr₁ (tr₂ M₁.𝟙)  ≤⟨ F.tr-monotone G.tr-𝟙 ⟩
       tr₁ M₂.𝟙        ≤⟨ F.tr-𝟙 ⟩
       M₃.𝟙            ∎
    .Is-morphism.tr-+ {p = p} {q = q} → let open R in begin
      tr₁ (tr₂ (p M₁.+ q))          ≤⟨ F.tr-monotone G.tr-+ ⟩
      tr₁ (tr₂ p M₂.+ tr₂ q)        ≤⟨ F.tr-+ ⟩
      tr₁ (tr₂ p) M₃.+ tr₁ (tr₂ q)  ∎
    .Is-morphism.tr-· {p = p} {q = q} →
      let open Tools.Reasoning.PropositionalEquality in
      tr₁ (tr₂ (p M₁.· q))          ≡⟨ cong tr₁ G.tr-· ⟩
      tr₁ (tr₂ p M₂.· tr₂ q)        ≡⟨ F.tr-· ⟩
      tr₁ (tr₂ p) M₃.· tr₁ (tr₂ q)  ∎
    .Is-morphism.tr-∧ {p = p} {q = q} → let open R in begin
      tr₁ (tr₂ (p M₁.∧ q))          ≤⟨ F.tr-monotone G.tr-∧ ⟩
      tr₁ (tr₂ p M₂.∧ tr₂ q)        ≤⟨ F.tr-∧ ⟩
      tr₁ (tr₂ p) M₃.∧ tr₁ (tr₂ q)  ∎
    .Is-morphism.tr-⊛ {p = p} {q = q} {r = r} → let open R in begin
      tr₁ (tr₂ (p M₁.⊛ q ▷ r))                    ≤⟨ F.tr-monotone G.tr-⊛ ⟩
      tr₁ (tr₂ p M₂.⊛ tr₂ q ▷ tr₂ r)              ≤⟨ F.tr-⊛ ⟩
      tr₁ (tr₂ p) M₃.⊛ tr₁ (tr₂ q) ▷ tr₁ (tr₂ r)  ∎
  where
  module Mo₂ = Mode 𝕄₂
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module M₃  = Modality 𝕄₃
  module F   = Is-morphism f
  module G   = Is-morphism g
  open Definition.Modality.Properties 𝕄₃
  module R = Tools.Reasoning.PartialOrder ≤-poset

-- Composition preserves Is-order-embedding.

Is-order-embedding-∘ :
  Is-order-embedding 𝕄₂ 𝕄₃ tr₁ →
  Is-order-embedding 𝕄₁ 𝕄₂ tr₂ →
  Is-order-embedding 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂)
Is-order-embedding-∘
  {𝕄₂ = 𝕄₂} {𝕄₃ = 𝕄₃} {tr₁ = tr₁} {𝕄₁ = 𝕄₁} {tr₂ = tr₂} f g = λ where
    .Is-order-embedding.tr-morphism →
      Is-morphism-∘ F.tr-morphism G.tr-morphism
    .Is-order-embedding.tr-order-reflecting →
      G.tr-order-reflecting ∘→ F.tr-order-reflecting
    .Is-order-embedding.trivial not-ok₁ ok₃ →
      let open Tools.Reasoning.PropositionalEquality in
      𝟘ᵐ-allowed-elim 𝕄₂
        (λ ok₂     → G.trivial not-ok₁ ok₂)
        (λ not-ok₂ → G.tr-injective (
           tr₂ M₁.𝟙  ≡⟨ MP₂.≈-trivial (F.trivial not-ok₂ ok₃) ⟩
           tr₂ M₁.𝟘  ∎))
    .Is-order-embedding.trivial-⊎-tr-𝟘 →
      let open Tools.Reasoning.PropositionalEquality in
      case F.trivial-⊎-tr-𝟘 of λ where
        (inj₁ triv)    → inj₁ (G.tr-injective (MP₂.≈-trivial triv))
        (inj₂ tr₁-𝟘≡𝟘) → case G.trivial-⊎-tr-𝟘 of λ where
          (inj₁ triv)    → inj₁ triv
          (inj₂ tr₂-𝟘≡𝟘) → inj₂ (
            tr₁ (tr₂ M₁.𝟘)  ≡⟨ cong tr₁ tr₂-𝟘≡𝟘 ⟩
            tr₁ M₂.𝟘        ≡⟨ tr₁-𝟘≡𝟘 ⟩
            M₃.𝟘            ∎)
    .Is-order-embedding.tr-≤ {p = p} →
      let open Tools.Reasoning.PartialOrder MP₃.≤-poset in
      case F.tr-≤ of λ (p′ , tr₁-p′≤p) →
      case G.tr-≤ of λ (p″ , tr₂-p″≤p′) →
        p″
      , (begin
           tr₁ (tr₂ p″)  ≤⟨ F.tr-monotone tr₂-p″≤p′ ⟩
           tr₁ p′        ≤⟨ tr₁-p′≤p ⟩
           p             ∎)
    .Is-order-embedding.tr-≤-𝟙 →
      G.tr-≤-𝟙 ∘→ F.tr-≤-𝟙
    .Is-order-embedding.tr-≤-+ {q = q} {r = r} tr-p≤q+r →
      case F.tr-≤-+ tr-p≤q+r of
        λ (q′ , r′ , tr-q′≤q , tr-r′≤r , tr-p≤q′+r′) →
      case G.tr-≤-+ tr-p≤q′+r′ of
        λ (q″ , r″ , tr-q″≤q′ , tr-r″≤r′ , p≤q″+r″) →
      let open Tools.Reasoning.PartialOrder MP₃.≤-poset in
        q″ , r″
      , (begin
           tr₁ (tr₂ q″)  ≤⟨ F.tr-monotone tr-q″≤q′ ⟩
           tr₁ q′        ≤⟨ tr-q′≤q ⟩
           q             ∎)
      , (begin
           tr₁ (tr₂ r″)  ≤⟨ F.tr-monotone tr-r″≤r′ ⟩
           tr₁ r′        ≤⟨ tr-r′≤r ⟩
           r             ∎)
      , p≤q″+r″
    .Is-order-embedding.tr-≤-· {r = r} tr-p≤tr-q·r →
      case F.tr-≤-· tr-p≤tr-q·r of
        λ (r′ , tr-r′≤r , tr-p≤tr-q·r′) →
      case G.tr-≤-· tr-p≤tr-q·r′ of
        λ (r″ , tr-r″≤r′ , p≤q·r″) →
      let open Tools.Reasoning.PartialOrder MP₃.≤-poset in
        r″
      , (begin
           tr₁ (tr₂ r″)  ≤⟨ F.tr-monotone tr-r″≤r′ ⟩
           tr₁ r′        ≤⟨ tr-r′≤r ⟩
           r             ∎)
      , p≤q·r″
    .Is-order-embedding.tr-≤-∧ {q = q} {r = r} tr-p≤q∧r →
      case F.tr-≤-∧ tr-p≤q∧r of
        λ (q′ , r′ , tr-q′≤q , tr-r′≤r , tr-p≤q′∧r′) →
      case G.tr-≤-∧ tr-p≤q′∧r′ of
        λ (q″ , r″ , tr-q″≤q′ , tr-r″≤r′ , p≤q″∧r″) →
      let open Tools.Reasoning.PartialOrder MP₃.≤-poset in
        q″ , r″
      , (begin
           tr₁ (tr₂ q″)  ≤⟨ F.tr-monotone tr-q″≤q′ ⟩
           tr₁ q′        ≤⟨ tr-q′≤q ⟩
           q             ∎)
      , (begin
           tr₁ (tr₂ r″)  ≤⟨ F.tr-monotone tr-r″≤r′ ⟩
           tr₁ r′        ≤⟨ tr-r′≤r ⟩
           r             ∎)
      , p≤q″∧r″
    .Is-order-embedding.tr-≤-⊛ {q₁ = q₁} {q₂ = q₂} {q₃ = q₃} tr-p≤ →
      let open Tools.Reasoning.PartialOrder MP₃.≤-poset in
      case F.tr-≤-⊛ tr-p≤ of
        λ (q₁′ , q₂′ , q₃′ , ≤q₁ , ≤q₂ , ≤q₃ , tr-p≤′) →
      case G.tr-≤-⊛ tr-p≤′ of
        λ (q₁″ , q₂″ , q₃″ , ≤q₁′ , ≤q₂′ , ≤q₃′ , p≤) →
        q₁″ , q₂″ , q₃″
      , (begin
           tr₁ (tr₂ q₁″)  ≤⟨ F.tr-monotone ≤q₁′ ⟩
           tr₁ q₁′        ≤⟨ ≤q₁ ⟩
           q₁             ∎)
      , (begin
           tr₁ (tr₂ q₂″)  ≤⟨ F.tr-monotone ≤q₂′ ⟩
           tr₁ q₂′        ≤⟨ ≤q₂ ⟩
           q₂             ∎)
      , (begin
           tr₁ (tr₂ q₃″)  ≤⟨ F.tr-monotone ≤q₃′ ⟩
           tr₁ q₃′        ≤⟨ ≤q₃ ⟩
           q₃             ∎)
      , p≤
  where
  module MP₂ = Definition.Modality.Properties 𝕄₂
  module MP₃ = Definition.Modality.Properties 𝕄₃
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module M₃  = Modality 𝕄₃
  module F   = Is-order-embedding f
  module G   = Is-order-embedding g

-- Composition preserves Is-Σₚ-morphism given a certain assumption.

Is-Σₚ-morphism-∘ :
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-Σₚ-morphism 𝕄₂ 𝕄₃ tr₁ tr-Σₚ₁ →
  Is-Σₚ-morphism 𝕄₁ 𝕄₂ tr₂ tr-Σₚ₂ →
  Is-Σₚ-morphism 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂) (tr-Σₚ₁ ∘→ tr-Σₚ₂)
Is-Σₚ-morphism-∘
  {𝕄₃ = 𝕄₃} {tr₁ = tr₁} {tr-Σₚ₁ = tr-Σₚ₁} {tr₂ = tr₂} {tr-Σₚ₂ = tr-Σₚ₂}
  m f g = record
  { tr-≤-tr-Σₚ = λ {p = p} → begin
      tr₁ (tr₂ p)        ≤⟨ Is-morphism.tr-monotone m G.tr-≤-tr-Σₚ ⟩
      tr₁ (tr-Σₚ₂ p)     ≤⟨ F.tr-≤-tr-Σₚ ⟩
      tr-Σₚ₁ (tr-Σₚ₂ p)  ∎
  ; tr-Σₚ-≡-𝟘-→ =
      curry (uncurry G.tr-Σₚ-≡-𝟘-→ ∘→ uncurry F.tr-Σₚ-≡-𝟘-→)
  ; tr-Σₚ-≤-𝟙 =
      F.tr-Σₚ-≤-𝟙 ∘→ G.tr-Σₚ-≤-𝟙
  }
  where
  module F = Is-Σₚ-morphism f
  module G = Is-Σₚ-morphism g
  open Definition.Modality.Properties 𝕄₃
  open Tools.Reasoning.PartialOrder ≤-poset

-- Composition preserves Is-Σₚ-order-embedding given a certain
-- assumption.

Is-Σₚ-order-embedding-∘ :
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-Σₚ-order-embedding 𝕄₂ 𝕄₃ tr₁ tr-Σₚ₁ →
  Is-Σₚ-order-embedding 𝕄₁ 𝕄₂ tr₂ tr-Σₚ₂ →
  Is-Σₚ-order-embedding 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂) (tr-Σₚ₁ ∘→ tr-Σₚ₂)
Is-Σₚ-order-embedding-∘
  {𝕄₃ = 𝕄₃} {tr₁ = tr₁} {tr-Σₚ₁ = tr-Σₚ₁} {tr₂ = tr₂} {tr-Σₚ₂ = tr-Σₚ₂}
  m f g = record
  { tr-Σₚ-morphism =
      Is-Σₚ-morphism-∘ m F.tr-Σₚ-morphism G.tr-Σₚ-morphism
  ; tr-≤-tr-Σₚ-→ = λ {p = _} {q = _} {r = r} tr-p≤tr-q·r →
      case F.tr-≤-tr-Σₚ-→ tr-p≤tr-q·r of
        λ (r′ , tr-r′≤r , tr-p≤tr-q·r′) →
      case G.tr-≤-tr-Σₚ-→ tr-p≤tr-q·r′ of
        λ (r″ , tr-r″≤r′ , p≤q·r″) →
        r″
      , (begin
           tr₁ (tr₂ r″)  ≤⟨ Is-morphism.tr-monotone m tr-r″≤r′ ⟩
           tr₁ r′        ≤⟨ tr-r′≤r ⟩
           r             ∎)
      , p≤q·r″
  }
  where
  module F = Is-Σₚ-order-embedding f
  module G = Is-Σₚ-order-embedding g
  open Definition.Modality.Properties 𝕄₃
  open Tools.Reasoning.PartialOrder ≤-poset

-- Composition preserves Are-preserving-term-restrictions.

Are-preserving-term-restrictions-∘ :
  Are-preserving-term-restrictions rt₂ rt₃ tr₁ tr-Σₚ₁ →
  Are-preserving-term-restrictions rt₁ rt₂ tr₂ tr-Σₚ₂ →
  Are-preserving-term-restrictions
    rt₁ rt₃ (tr₁ ∘→ tr₂) (tr-Σₚ₁ ∘→ tr-Σₚ₂)
Are-preserving-term-restrictions-∘ m₁ m₂ = λ where
    .Prodrec-preserved →
      M₁.Prodrec-preserved ∘→ M₂.Prodrec-preserved
    .Binder-preserved {b = BMΠ} →
      M₁.Binder-preserved ∘→ M₂.Binder-preserved
    .Binder-preserved {b = BMΣ Σₚ} →
      M₁.Binder-preserved ∘→ M₂.Binder-preserved
    .Binder-preserved {b = BMΣ Σᵣ} →
      M₁.Binder-preserved ∘→ M₂.Binder-preserved
  where
  open Are-preserving-term-restrictions
  module M₁ = Are-preserving-term-restrictions m₁
  module M₂ = Are-preserving-term-restrictions m₂

-- Composition preserves Are-reflecting-term-restrictions.

Are-reflecting-term-restrictions-∘ :
  Are-reflecting-term-restrictions rt₂ rt₃ tr₁ tr-Σₚ₁ →
  Are-reflecting-term-restrictions rt₁ rt₂ tr₂ tr-Σₚ₂ →
  Are-reflecting-term-restrictions
    rt₁ rt₃ (tr₁ ∘→ tr₂) (tr-Σₚ₁ ∘→ tr-Σₚ₂)
Are-reflecting-term-restrictions-∘ m₁ m₂ = λ where
    .Prodrec-reflected →
      M₂.Prodrec-reflected ∘→ M₁.Prodrec-reflected
    .Binder-reflected {b = BMΠ} →
      M₂.Binder-reflected ∘→ M₁.Binder-reflected
    .Binder-reflected {b = BMΣ Σₚ} →
      M₂.Binder-reflected ∘→ M₁.Binder-reflected
    .Binder-reflected {b = BMΣ Σᵣ} →
      M₂.Binder-reflected ∘→ M₁.Binder-reflected
  where
  open Are-reflecting-term-restrictions
  module M₁ = Are-reflecting-term-restrictions m₁
  module M₂ = Are-reflecting-term-restrictions m₂

------------------------------------------------------------------------
-- Preserving/reflecting term restrictions

-- If tr preserves term restrictions for rt₁ and rt₂, then it also
-- does this for equal-binder-quantities M₁ rt₁ and
-- equal-binder-quantities M₂ rt₂.

Are-preserving-term-restrictions-equal-binder-quantities :
  Are-preserving-term-restrictions rt₁ rt₂ tr tr →
  Are-preserving-term-restrictions
    (equal-binder-quantities rt₁)
    (equal-binder-quantities rt₂)
    tr tr
Are-preserving-term-restrictions-equal-binder-quantities {tr = tr} r =
  record
    { Prodrec-preserved = R.Prodrec-preserved
    ; Binder-preserved  = λ {b = b} → λ where
        (bn , refl) →
            R.Binder-preserved bn
          , tr-BinderMode-one-function _ _ refl b
    }
  where
  module R = Are-preserving-term-restrictions r

-- If tr reflects term restrictions for rt₁ and rt₂, then it also does
-- this for equal-binder-quantities M₁ rt₁ and
-- equal-binder-quantities M₂ rt₂, assuming that the function is
-- injective.

Are-reflecting-term-restrictions-equal-binder-quantities :
  (∀ {p q} → tr p ≡ tr q → p ≡ q) →
  Are-reflecting-term-restrictions rt₁ rt₂ tr tr →
  Are-reflecting-term-restrictions
    (equal-binder-quantities rt₁)
    (equal-binder-quantities rt₂)
    tr tr
Are-reflecting-term-restrictions-equal-binder-quantities
  {tr = tr} inj r = record
  { Prodrec-reflected = Prodrec-reflected
  ; Binder-reflected  = λ {b = b} {p = p} {q = q} (bn , eq) →
        Binder-reflected bn
      , inj (
          tr p                     ≡˘⟨ tr-BinderMode-one-function _ _ refl b ⟩
          tr-BinderMode tr tr b p  ≡⟨ eq ⟩
          tr q                     ∎)
  }
  where
  open Are-reflecting-term-restrictions r
  open Tools.Reasoning.PropositionalEquality

-- If the functions tr and tr-Σₚ preserve term restrictions for two
-- modalities, then they also do this for certain term restrictions
-- obtained using second-ΠΣ-quantities-𝟘, assuming that tr maps 𝟘
-- to 𝟘.

Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘 :
  tr (Modality.𝟘 𝕄₁) ≡ Modality.𝟘 𝕄₂ →
  Are-preserving-term-restrictions
    (Modality.term-restrictions 𝕄₁)
    (Modality.term-restrictions 𝕄₂)
    tr tr-Σₚ →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘 𝕄₁)
    (second-ΠΣ-quantities-𝟘 𝕄₂)
    tr tr-Σₚ
Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘 tr-𝟘 r = record
  { Prodrec-preserved = Prodrec-preserved
  ; Binder-preserved  = λ where
      (b , refl) → Binder-preserved b , tr-𝟘
  }
  where
  open Are-preserving-term-restrictions r

-- If the functions tr and tr-Σₚ reflect term restrictions for two
-- modalities, then they also do this for certain term restrictions
-- obtained using second-ΠΣ-quantities-𝟘, assuming that tr only maps 𝟘
-- to 𝟘.

Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘 :
  (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) →
  Are-reflecting-term-restrictions
    (Modality.term-restrictions 𝕄₁)
    (Modality.term-restrictions 𝕄₂)
    tr tr-Σₚ →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘 𝕄₁)
    (second-ΠΣ-quantities-𝟘 𝕄₂)
    tr tr-Σₚ
Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘 tr-𝟘 r = record
  { Prodrec-reflected = Prodrec-reflected
  ; Binder-reflected  = λ (b , eq) → Binder-reflected b , tr-𝟘 eq
  }
  where
  open Are-reflecting-term-restrictions r

-- If the functions tr and tr-Σₚ preserve term restrictions for two
-- modalities, then they also do this for certain term restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω, given that certain
-- assumptions hold.

Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ {ω₁ ω₂} →
  Is-morphism 𝕄₁ 𝕄₂ tr →
  Is-Σₚ-morphism 𝕄₁ 𝕄₂ tr tr-Σₚ →
  (¬ T (Modality.𝟘ᵐ-allowed 𝕄₁) →
   (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ ⇔ p ≡ Modality.𝟘 𝕄₁) ×
   (∀ {p} → tr-Σₚ p ≡ Modality.𝟘 𝕄₂ ⇔ p ≡ Modality.𝟘 𝕄₁)) →
  tr ω₁ ≡ ω₂ →
  Are-preserving-term-restrictions
    (Modality.term-restrictions 𝕄₁)
    (Modality.term-restrictions 𝕄₂)
    tr tr-Σₚ →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω₁ 𝕄₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω₂ 𝕄₂)
    tr tr-Σₚ
Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
  {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} {tr = tr} {tr-Σₚ = tr-Σₚ} {ω₁ = ω₁} {ω₂ = ω₂}
  m m-Σₚ tr-𝟘 tr-ω r = record
  { Prodrec-preserved = Prodrec-preserved
  ; Binder-preserved  = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      Binder-preserved bn , lemma₂ b is-𝟘 , lemma₄ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-preserving-term-restrictions r
  open Definition.Modality.Properties 𝕄₁
  open Is-morphism m
  open Is-Σₚ-morphism m-Σₚ

  tr-≡-𝟘-⇔′ : ∀ {p} → tr p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘
  tr-≡-𝟘-⇔′ = Mode.𝟘ᵐ-allowed-elim 𝕄₁
    tr-≡-𝟘-⇔
    (λ not-ok → tr-𝟘 not-ok .proj₁)

  tr-Σₚ-≡-𝟘-⇔ : ∀ {p} → tr-Σₚ p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘
  tr-Σₚ-≡-𝟘-⇔ = Mode.𝟘ᵐ-allowed-elim 𝕄₁
    (λ ok →
         (λ hyp → tr-Σₚ-≡-𝟘-→ (𝟘ᵐ-in-second-if-in-first ok) hyp .proj₂)
       , (λ { refl → tr-Σₚ-𝟘-≡ m ok }))
    (λ not-ok → tr-𝟘 not-ok .proj₂)

  lemma₁ :
    ∀ {p q} →
    (p ≡ M₁.𝟘 → q ≡ M₁.𝟘) →
    tr p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘
  lemma₁ {p = p} {q = q} hyp =
    tr p ≡ M₂.𝟘  →⟨ tr-≡-𝟘-⇔′ .proj₁ ⟩
    p ≡ M₁.𝟘     →⟨ hyp ⟩
    q ≡ M₁.𝟘     →⟨ tr-≡-𝟘-⇔′ .proj₂ ⟩
    tr q ≡ M₂.𝟘  □

  lemma₂ :
    ∀ {p q} b →
    (p ≡ M₁.𝟘 → q ≡ M₁.𝟘) →
    tr-BinderMode tr tr-Σₚ b p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘
  lemma₂                 BMΠ      = lemma₁
  lemma₂                 (BMΣ Σᵣ) = lemma₁
  lemma₂ {p = p} {q = q} (BMΣ Σₚ) = λ hyp →
    tr-Σₚ p ≡ M₂.𝟘  →⟨ tr-Σₚ-≡-𝟘-⇔ .proj₁ ⟩
    p ≡ M₁.𝟘        →⟨ hyp ⟩
    q ≡ M₁.𝟘        →⟨ tr-≡-𝟘-⇔′ .proj₂ ⟩
    tr q ≡ M₂.𝟘     □

  lemma₃ :
    ∀ {p q} →
    (p ≢ M₁.𝟘 → q ≡ ω₁) →
    tr p ≢ M₂.𝟘 → tr q ≡ ω₂
  lemma₃ {p = p} {q = q} hyp =
    tr p ≢ M₂.𝟘  →⟨ _∘→ tr-≡-𝟘-⇔′ .proj₂ ⟩
    p ≢ M₁.𝟘     →⟨ hyp ⟩
    q ≡ ω₁       →⟨ (λ { refl → tr-ω }) ⟩
    tr q ≡ ω₂    □

  lemma₄ :
    ∀ {p q} b →
    (p ≢ M₁.𝟘 → q ≡ ω₁) →
    tr-BinderMode tr tr-Σₚ b p ≢ M₂.𝟘 → tr q ≡ ω₂
  lemma₄                 BMΠ      = lemma₃
  lemma₄                 (BMΣ Σᵣ) = lemma₃
  lemma₄ {p = p} {q = q} (BMΣ Σₚ) = λ hyp →
    tr-Σₚ p ≢ M₂.𝟘  →⟨ _∘→ tr-Σₚ-≡-𝟘-⇔ .proj₂ ⟩
    p ≢ M₁.𝟘        →⟨ hyp ⟩
    q ≡ ω₁          →⟨ (λ { refl → tr-ω }) ⟩
    tr q ≡ ω₂       □

-- A variant of
-- Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω with
-- different assumptions.

Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′ :
  ∀ {ω₁ ω₂} →
  Is-order-embedding 𝕄₁ 𝕄₂ tr →
  Is-Σₚ-morphism 𝕄₁ 𝕄₂ tr tr-Σₚ →
  (¬ T (Modality.𝟘ᵐ-allowed 𝕄₁) → ∀ {p} → tr-Σₚ p ≡ tr p) →
  tr ω₁ ≡ ω₂ →
  Are-preserving-term-restrictions
    (Modality.term-restrictions 𝕄₁)
    (Modality.term-restrictions 𝕄₂)
    tr tr-Σₚ →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω₁ 𝕄₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω₂ 𝕄₂)
    tr tr-Σₚ
Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
  {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} {tr = tr} {tr-Σₚ = tr-Σₚ} {ω₁ = ω₁} {ω₂ = ω₂}
  emb m tr-Σₚ≡tr tr-ω r = record
  { Prodrec-preserved = Prodrec-preserved
  ; Binder-preserved  = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      Binder-preserved bn , lemma₂ b is-𝟘 , lemma₄ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-preserving-term-restrictions r
  open Definition.Modality.Properties 𝕄₁
  open Is-order-embedding emb
  open Is-Σₚ-morphism m

  lemma₁ :
    ∀ {p q} →
    (p ≡ M₁.𝟘 → q ≡ M₁.𝟘) →
    tr p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘
  lemma₁ {p = p} {q = q} hyp =
    case trivial-⊎-tr-𝟘 of λ where
      (inj₁ 𝟙≡𝟘) →
        tr p ≡ M₂.𝟘  ≡⟨ cong (λ p → tr p ≡ _) (≈-trivial 𝟙≡𝟘) ⟩→
        tr q ≡ M₂.𝟘  □
      (inj₂ tr-𝟘) →
        tr p ≡ M₂.𝟘     ≡⟨ cong (_ ≡_) (sym tr-𝟘) ⟩→
        tr p ≡ tr M₁.𝟘  →⟨ tr-injective ⟩
        p ≡ M₁.𝟘        →⟨ hyp ⟩
        q ≡ M₁.𝟘        →⟨ (λ { refl → tr-𝟘 }) ⟩
        tr q ≡ M₂.𝟘     □

  lemma₂ :
    ∀ {p q} b →
    (p ≡ M₁.𝟘 → q ≡ M₁.𝟘) →
    tr-BinderMode tr tr-Σₚ b p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘
  lemma₂                 BMΠ      = lemma₁
  lemma₂                 (BMΣ Σᵣ) = lemma₁
  lemma₂ {p = p} {q = q} (BMΣ Σₚ) = λ hyp →
    Mode.𝟘ᵐ-allowed-elim 𝕄₁
      (λ ok →
         tr-Σₚ p ≡ M₂.𝟘  →⟨ (λ hyp → tr-Σₚ-≡-𝟘-→ (𝟘ᵐ-in-second-if-in-first ok) hyp .proj₂) ⟩
         p ≡ M₁.𝟘        →⟨ hyp ⟩
         q ≡ M₁.𝟘        →⟨ tr-≡-𝟘-⇔ ok .proj₂ ⟩
         tr q ≡ M₂.𝟘     □)
      (λ not-ok →
         tr-Σₚ p ≡ M₂.𝟘  ≡⟨ cong (_≡ _) (tr-Σₚ≡tr not-ok) ⟩→
         tr p ≡ M₂.𝟘     →⟨ lemma₁ hyp ⟩
         tr q ≡ M₂.𝟘     □)

  lemma₃ :
    ∀ {p q} →
    (p ≢ M₁.𝟘 → q ≡ ω₁) →
    tr p ≢ M₂.𝟘 → tr q ≡ ω₂
  lemma₃ {p = p} {q = q} hyp =
    case trivial-⊎-tr-𝟘 of λ where
      (inj₁ 𝟙≡𝟘) →
        tr p ≢ M₂.𝟘  →⟨ (λ _ → ≈-trivial 𝟙≡𝟘) ⟩
        q ≡ ω₁       →⟨ (λ { refl → tr-ω }) ⟩
        tr q ≡ ω₂    □
      (inj₂ tr-𝟘) →
        tr p ≢ M₂.𝟘     ≡⟨ cong (_ ≢_) (sym tr-𝟘) ⟩→
        tr p ≢ tr M₁.𝟘  →⟨ _∘→ cong tr ⟩
        p ≢ M₁.𝟘        →⟨ hyp ⟩
        q ≡ ω₁          →⟨ (λ { refl → tr-ω }) ⟩
        tr q ≡ ω₂       □

  lemma₄ :
    ∀ {p q} b →
    (p ≢ M₁.𝟘 → q ≡ ω₁) →
    tr-BinderMode tr tr-Σₚ b p ≢ M₂.𝟘 → tr q ≡ ω₂
  lemma₄                 BMΠ      = lemma₃
  lemma₄                 (BMΣ Σᵣ) = lemma₃
  lemma₄ {p = p} {q = q} (BMΣ Σₚ) = λ hyp →
    Mode.𝟘ᵐ-allowed-elim 𝕄₁
      (λ ok →
         tr-Σₚ p ≢ M₂.𝟘  →⟨ _∘→ (λ { refl → tr-Σₚ-𝟘-≡ tr-morphism ok }) ⟩
         p ≢ M₁.𝟘        →⟨ hyp ⟩
         q ≡ ω₁          →⟨ (λ { refl → tr-ω }) ⟩
         tr q ≡ ω₂       □)
      (λ not-ok →
         tr-Σₚ p ≢ M₂.𝟘  ≡⟨ cong (_≢ _) (tr-Σₚ≡tr not-ok) ⟩→
         tr p ≢ M₂.𝟘     →⟨ lemma₃ hyp ⟩
         tr q ≡ ω₂       □)

-- If the functions tr and tr-Σₚ reflect term restrictions for two
-- modalities, then they also do this for certain term restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω, given that certain
-- assumptions hold.

Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω :
  ∀ {ω₁ ω₂} →
  Is-morphism 𝕄₁ 𝕄₂ tr →
  Is-Σₚ-morphism 𝕄₁ 𝕄₂ tr tr-Σₚ →
  (¬ T (Modality.𝟘ᵐ-allowed 𝕄₁) →
   (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ ⇔ p ≡ Modality.𝟘 𝕄₁) ×
   (∀ {p} → tr-Σₚ p ≡ Modality.𝟘 𝕄₂ ⇔ p ≡ Modality.𝟘 𝕄₁)) →
  (∀ {p} → tr p ≡ ω₂ → p ≡ ω₁) →
  Are-reflecting-term-restrictions
    (Modality.term-restrictions 𝕄₁)
    (Modality.term-restrictions 𝕄₂)
    tr tr-Σₚ →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω₁ 𝕄₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω₂ 𝕄₂)
    tr tr-Σₚ
Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
  {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} {tr = tr} {tr-Σₚ = tr-Σₚ} {ω₁ = ω₁} {ω₂ = ω₂}
  m m-Σₚ tr-𝟘 tr-ω r = record
  { Prodrec-reflected = Prodrec-reflected
  ; Binder-reflected  = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      Binder-reflected bn , lemma₂ b is-𝟘 , lemma₄ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-reflecting-term-restrictions r
  open Definition.Modality.Properties 𝕄₁
  open Is-morphism m
  open Is-Σₚ-morphism m-Σₚ

  tr-≡-𝟘-⇔′ : ∀ {p} → tr p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘
  tr-≡-𝟘-⇔′ = Mode.𝟘ᵐ-allowed-elim 𝕄₁
    tr-≡-𝟘-⇔
    (λ not-ok → tr-𝟘 not-ok .proj₁)

  tr-Σₚ-≡-𝟘-⇔ : ∀ {p} → tr-Σₚ p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘
  tr-Σₚ-≡-𝟘-⇔ = Mode.𝟘ᵐ-allowed-elim 𝕄₁
    (λ ok →
         (λ hyp → tr-Σₚ-≡-𝟘-→ (𝟘ᵐ-in-second-if-in-first ok) hyp .proj₂)
       , (λ { refl → tr-Σₚ-𝟘-≡ m ok }))
    (λ not-ok → tr-𝟘 not-ok .proj₂)

  lemma₁ :
    ∀ {p q} →
    (tr p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘) →
    p ≡ M₁.𝟘 → q ≡ M₁.𝟘
  lemma₁ {p = p} {q = q} hyp =
    p ≡ M₁.𝟘     →⟨ tr-≡-𝟘-⇔′ .proj₂ ⟩
    tr p ≡ M₂.𝟘  →⟨ hyp ⟩
    tr q ≡ M₂.𝟘  →⟨ tr-≡-𝟘-⇔′ .proj₁ ⟩
    q ≡ M₁.𝟘     □

  lemma₂ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σₚ b p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘) →
    p ≡ M₁.𝟘 → q ≡ M₁.𝟘
  lemma₂                 BMΠ      = lemma₁
  lemma₂                 (BMΣ Σᵣ) = lemma₁
  lemma₂ {p = p} {q = q} (BMΣ Σₚ) = λ hyp →
    p ≡ M₁.𝟘        →⟨ tr-Σₚ-≡-𝟘-⇔ .proj₂ ⟩
    tr-Σₚ p ≡ M₂.𝟘  →⟨ hyp ⟩
    tr q ≡ M₂.𝟘     →⟨ tr-≡-𝟘-⇔′ .proj₁ ⟩
    q ≡ M₁.𝟘        □

  lemma₃ :
    ∀ {p q} →
    (tr p ≢ M₂.𝟘 → tr q ≡ ω₂) →
    p ≢ M₁.𝟘 → q ≡ ω₁
  lemma₃ {p = p} {q = q} hyp =
    p ≢ M₁.𝟘     →⟨ _∘→ tr-≡-𝟘-⇔′ .proj₁ ⟩
    tr p ≢ M₂.𝟘  →⟨ hyp ⟩
    tr q ≡ ω₂    →⟨ tr-ω ⟩
    q ≡ ω₁       □

  lemma₄ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σₚ b p ≢ M₂.𝟘 → tr q ≡ ω₂) →
    p ≢ M₁.𝟘 → q ≡ ω₁
  lemma₄                 BMΠ      = lemma₃
  lemma₄                 (BMΣ Σᵣ) = lemma₃
  lemma₄ {p = p} {q = q} (BMΣ Σₚ) = λ hyp →
    p ≢ M₁.𝟘        →⟨ _∘→ tr-Σₚ-≡-𝟘-⇔ .proj₁ ⟩
    tr-Σₚ p ≢ M₂.𝟘  →⟨ hyp ⟩
    tr q ≡ ω₂       →⟨ tr-ω ⟩
    q ≡ ω₁          □

-- A variant of
-- Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω with
-- different assumptions.

Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′ :
  ∀ {ω₁ ω₂} →
  Is-order-embedding 𝕄₁ 𝕄₂ tr →
  Is-Σₚ-morphism 𝕄₁ 𝕄₂ tr tr-Σₚ →
  (¬ T (Modality.𝟘ᵐ-allowed 𝕄₁) → ∀ {p} → tr-Σₚ p ≡ tr p) →
  (∀ {p} → tr p ≡ ω₂ → p ≡ ω₁) →
  Are-reflecting-term-restrictions
    (Modality.term-restrictions 𝕄₁)
    (Modality.term-restrictions 𝕄₂)
    tr tr-Σₚ →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω₁ 𝕄₁)
    (second-ΠΣ-quantities-𝟘-or-ω ω₂ 𝕄₂)
    tr tr-Σₚ
Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
  {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} {tr = tr} {tr-Σₚ = tr-Σₚ} {ω₁ = ω₁} {ω₂ = ω₂}
  emb m tr-Σₚ≡tr tr-ω r = record
  { Prodrec-reflected = Prodrec-reflected
  ; Binder-reflected  = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      Binder-reflected bn , lemma₂ b is-𝟘 , lemma₄ b not-𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Are-reflecting-term-restrictions r
  open Definition.Modality.Properties 𝕄₁
  open Is-order-embedding emb
  open Is-Σₚ-morphism m

  lemma₁ :
    ∀ {p q} →
    (tr p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘) →
    p ≡ M₁.𝟘 → q ≡ M₁.𝟘
  lemma₁ {p = p} {q = q} hyp =
    case trivial-⊎-tr-𝟘 of λ where
      (inj₁ 𝟙≡𝟘) →
        p ≡ M₁.𝟘  →⟨ (λ _ → ≈-trivial 𝟙≡𝟘) ⟩
        q ≡ M₁.𝟘  □
      (inj₂ tr-𝟘) →
        p ≡ M₁.𝟘        →⟨ (λ { refl → tr-𝟘 }) ⟩
        tr p ≡ M₂.𝟘     →⟨ hyp ⟩
        tr q ≡ M₂.𝟘     ≡⟨ cong (_ ≡_) (sym tr-𝟘) ⟩→
        tr q ≡ tr M₁.𝟘  →⟨ tr-injective ⟩
        q ≡ M₁.𝟘        □

  lemma₂ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σₚ b p ≡ M₂.𝟘 → tr q ≡ M₂.𝟘) →
    p ≡ M₁.𝟘 → q ≡ M₁.𝟘
  lemma₂                 BMΠ      = lemma₁
  lemma₂                 (BMΣ Σᵣ) = lemma₁
  lemma₂ {p = p} {q = q} (BMΣ Σₚ) = λ hyp →
    Mode.𝟘ᵐ-allowed-elim 𝕄₁
      (λ ok →
         p ≡ M₁.𝟘        →⟨ (λ { refl → tr-Σₚ-𝟘-≡ tr-morphism ok }) ⟩
         tr-Σₚ p ≡ M₂.𝟘  →⟨ hyp ⟩
         tr q ≡ M₂.𝟘     →⟨ tr-≡-𝟘-⇔ ok .proj₁ ⟩
         q ≡ M₁.𝟘        □)
      (λ not-ok → lemma₁ (
         tr p ≡ M₂.𝟘     ≡⟨ cong (_≡ _) (sym (tr-Σₚ≡tr not-ok)) ⟩→
         tr-Σₚ p ≡ M₂.𝟘  →⟨ hyp ⟩
         tr q ≡ M₂.𝟘     □))

  lemma₃ :
    ∀ {p q} →
    (tr p ≢ M₂.𝟘 → tr q ≡ ω₂) →
    p ≢ M₁.𝟘 → q ≡ ω₁
  lemma₃ {p = p} {q = q} hyp =
    case trivial-⊎-tr-𝟘 of λ where
      (inj₁ 𝟙≡𝟘) →
        p ≢ M₁.𝟘  →⟨ (λ _ → ≈-trivial 𝟙≡𝟘) ⟩
        q ≡ ω₁    □
      (inj₂ tr-𝟘) →
        p ≢ M₁.𝟘        →⟨ _∘→ tr-injective ⟩
        tr p ≢ tr M₁.𝟘  ≡⟨ cong (_ ≢_) tr-𝟘 ⟩→
        tr p ≢ M₂.𝟘     →⟨ hyp ⟩
        tr q ≡ ω₂       →⟨ tr-ω ⟩
        q ≡ ω₁          □

  lemma₄ :
    ∀ {p q} b →
    (tr-BinderMode tr tr-Σₚ b p ≢ M₂.𝟘 → tr q ≡ ω₂) →
    p ≢ M₁.𝟘 → q ≡ ω₁
  lemma₄                 BMΠ      = lemma₃
  lemma₄                 (BMΣ Σᵣ) = lemma₃
  lemma₄ {p = p} {q = q} (BMΣ Σₚ) = λ hyp →
    Mode.𝟘ᵐ-allowed-elim 𝕄₁
      (λ ok →
         p ≢ M₁.𝟘        →⟨ _∘→ (λ hyp → tr-Σₚ-≡-𝟘-→ (𝟘ᵐ-in-second-if-in-first ok) hyp .proj₂) ⟩
         tr-Σₚ p ≢ M₂.𝟘  →⟨ hyp ⟩
         tr q ≡ ω₂       →⟨ tr-ω ⟩
         q ≡ ω₁          □)
      (λ not-ok → lemma₃ (
         tr p ≢ M₂.𝟘     ≡⟨ cong (_≢ _) (sym (tr-Σₚ≡tr not-ok)) ⟩→
         tr-Σₚ p ≢ M₂.𝟘  →⟨ hyp ⟩
         tr q ≡ ω₂       □))

------------------------------------------------------------------------
-- Some translation functions

-- A translation from ⊤ to Erasure.

unit→erasure : ⊤ → Erasure
unit→erasure _ = ω

-- A translation from Erasure to ⊤.

erasure→unit : Erasure → ⊤
erasure→unit = _

-- A translation from Erasure to Zero-one-many.

erasure→zero-one-many : Erasure → Zero-one-many 𝟙≤𝟘
erasure→zero-one-many = λ where
  𝟘 → 𝟘
  ω → ω

-- A translation from Erasure to Zero-one-many, intended to be used
-- for the first components of Σ-types with η-equality.

erasure→zero-one-many-Σₚ : Erasure → Zero-one-many 𝟙≤𝟘
erasure→zero-one-many-Σₚ = λ where
  𝟘 → 𝟘
  ω → 𝟙

-- A translation from Zero-one-many to Erasure.

zero-one-many→erasure : Zero-one-many 𝟙≤𝟘 → Erasure
zero-one-many→erasure = λ where
  𝟘 → 𝟘
  _ → ω

-- A translation from Linearity to Linear-or-affine.

linearity→linear-or-affine : Linearity → Linear-or-affine
linearity→linear-or-affine = λ where
  𝟘 → 𝟘
  𝟙 → 𝟙
  ω → ≤ω

-- A translation from Linear-or-affine to Linearity.

linear-or-affine→linearity : Linear-or-affine → Linearity
linear-or-affine→linearity = λ where
  𝟘  → 𝟘
  𝟙  → 𝟙
  ≤𝟙 → ω
  ≤ω → ω

-- A translation from Affine to Linear-or-affine.

affine→linear-or-affine : Affine → Linear-or-affine
affine→linear-or-affine = λ where
  𝟘 → 𝟘
  𝟙 → ≤𝟙
  ω → ≤ω

-- A translation from Affine to Linear-or-affine, intended to be used
-- for the first components of Σ-types with η-equality.

affine→linear-or-affine-Σₚ : Affine → Linear-or-affine
affine→linear-or-affine-Σₚ = λ where
  𝟘 → 𝟘
  𝟙 → 𝟙
  ω → ≤ω

-- A translation from Linear-or-affine to Affine.

linear-or-affine→affine : Linear-or-affine → Affine
linear-or-affine→affine = λ where
  𝟘  → 𝟘
  𝟙  → 𝟙
  ≤𝟙 → 𝟙
  ≤ω → ω

-- A translation from Affine to Linearity.

affine→linearity : Affine → Linearity
affine→linearity =
  linear-or-affine→linearity ∘→ affine→linear-or-affine

-- A translation from Affine to Linearity.

affine→linearity-Σₚ : Affine → Linearity
affine→linearity-Σₚ =
  linear-or-affine→linearity ∘→ affine→linear-or-affine-Σₚ

-- A translation from Linearity to Affine.

linearity→affine : Linearity → Affine
linearity→affine =
  linear-or-affine→affine ∘→ linearity→linear-or-affine

------------------------------------------------------------------------
-- Morphisms and order embeddings

-- The function unit→erasure is an order embedding from a unit
-- modality to an erasure modality.

unit⇨erasure :
  Is-order-embedding (UnitModality rt) (ErasureModality r) unit→erasure
unit⇨erasure = λ where
    .tr-order-reflecting _    → refl
    .trivial _ _              → refl
    .trivial-⊎-tr-𝟘           → inj₁ refl
    .tr-≤                     → _ , refl
    .tr-≤-𝟙 _                 → refl
    .tr-≤-+ _                 → _ , _ , refl , refl , refl
    .tr-≤-· _                 → _ , refl , refl
    .tr-≤-∧ _                 → _ , _ , refl , refl , refl
    .tr-≤-⊛ _                 → _ , _ , _ , refl , refl , refl , refl
    .tr-morphism → λ where
      .tr-𝟘-≤     → refl
      .tr-<-𝟘 _ _ → refl , λ ()
      .tr-𝟙       → refl
      .tr-+       → refl
      .tr-·       → refl
      .tr-∧       → refl
      .tr-⊛       → refl
  where
  open Is-morphism
  open Is-order-embedding

-- The function erasure→unit is a morphism from a unit modality to an
-- erasure modality, given that the erasure modality does not
-- allow 𝟘ᵐ.

erasure⇨unit :
  ¬ T (Restrictions.𝟘ᵐ-allowed r) →
  Is-morphism (ErasureModality r) (UnitModality rt) erasure→unit
erasure⇨unit not-ok = λ where
    .tr-𝟘-≤                      → refl
    .tr-≡-𝟘-⇔ ok                 → ⊥-elim (not-ok ok)
    .tr-𝟙                        → refl
    .tr-+                        → refl
    .tr-·                        → refl
    .tr-∧                        → refl
    .tr-⊛                        → refl
    .𝟘ᵐ-in-second-if-in-first ok → ⊥-elim (not-ok ok)
  where
  open Is-morphism

-- The function erasure→unit is not an order embedding from an erasure
-- modality to a unit modality.

¬erasure⇨unit :
  ¬ Is-order-embedding (ErasureModality r) (UnitModality rt)
      erasure→unit
¬erasure⇨unit m =
  case Is-order-embedding.tr-injective m {p = 𝟘} {q = ω} refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a zero-one-many-greatest modality, given that
-- either both modalities allow 𝟘ᵐ, or none of them do. The
-- zero-one-many-greatest modality can be defined with either 𝟙 ≤ 𝟘 or
-- 𝟙 ≰ 𝟘.

erasure⇨zero-one-many :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-order-embedding
    (ErasureModality r₁)
    (zero-one-many-greatest 𝟙≤𝟘 r₂)
    erasure→zero-one-many
erasure⇨zero-one-many {𝟙≤𝟘 = 𝟙≤𝟘} {r₂ = r₂} refl = λ where
    .Is-order-embedding.trivial not-ok ok   → ⊥-elim (not-ok ok)
    .Is-order-embedding.trivial-⊎-tr-𝟘      → inj₂ refl
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-≤-⊛ {s = s}      → tr-≤-⊛ _ _ _ _ _ s
    .Is-order-embedding.tr-order-reflecting →
      tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism → λ where
      .Is-morphism.tr-𝟘-≤                   → refl
      .Is-morphism.tr-≡-𝟘-⇔ _               → tr-≡-𝟘 _
                                            , λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok         → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                     → refl
      .Is-morphism.tr-+ {p = p}             → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-· {p = p}             → tr-· p _
      .Is-morphism.tr-∧ {p = p}             → ≤-reflexive (tr-∧ p _)
      .Is-morphism.tr-⊛ {p = p} {r = r}     → ≤-reflexive (tr-⊛ p _ r)
      .Is-morphism.𝟘ᵐ-in-second-if-in-first → idᶠ
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘
  open Definition.Modality.Properties (zero-one-many-greatest 𝟙≤𝟘 r₂)
  open Tools.Reasoning.PartialOrder ≤-poset

  tr′ = erasure→zero-one-many

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-≤-𝟙 : ∀ p → tr′ p 𝟘𝟙ω.≤ 𝟙 → p E.≤ ω
  tr-≤-𝟙 𝟘 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-𝟙 ω _     = refl

  tr-+ : ∀ p q → tr′ (p E.+ q) ≡ tr′ p 𝟘𝟙ω.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p E.· q) ≡ tr′ p 𝟘𝟙ω.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p E.∧ q) ≡ tr′ p 𝟘𝟙ω.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω ω = refl

  tr-⊛ : ∀ p q r → tr′ (p E.⊛ q ▷ r) ≡ tr′ p 𝟘𝟙ω.⊛ tr′ q ▷ tr′ r
  tr-⊛ 𝟘 𝟘 𝟘 = refl
  tr-⊛ 𝟘 𝟘 ω = refl
  tr-⊛ 𝟘 ω 𝟘 = refl
  tr-⊛ 𝟘 ω ω = refl
  tr-⊛ ω 𝟘 𝟘 = refl
  tr-⊛ ω 𝟘 ω = refl
  tr-⊛ ω ω 𝟘 = refl
  tr-⊛ ω ω ω = refl

  tr-order-reflecting : ∀ p q → tr′ p 𝟘𝟙ω.≤ tr′ q → p E.≤ q
  tr-order-reflecting 𝟘 𝟘 _ = refl
  tr-order-reflecting ω 𝟘 _ = refl
  tr-order-reflecting ω ω _ = refl

  tr-≤-+ :
    ∀ p q r →
    tr′ p 𝟘𝟙ω.≤ q 𝟘𝟙ω.+ r →
    ∃₂ λ q′ r′ → tr′ q′ 𝟘𝟙ω.≤ q × tr′ r′ 𝟘𝟙ω.≤ r × p E.≤ q′ E.+ r′
  tr-≤-+ 𝟘 𝟘 𝟘 _     = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟘 𝟘 𝟙 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-+ 𝟘 𝟙 𝟘 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-+ ω _ _ _     = ω , ω , refl , refl , refl

  tr-≤-· :
    ∀ p q r →
    tr′ p 𝟘𝟙ω.≤ tr′ q 𝟘𝟙ω.· r →
    ∃ λ r′ → tr′ r′ 𝟘𝟙ω.≤ r × p E.≤ q E.· r′
  tr-≤-· 𝟘 𝟘 _ _ = ω , refl , refl
  tr-≤-· 𝟘 ω 𝟘 _ = 𝟘 , refl , refl
  tr-≤-· ω _ _ _ = ω , refl , refl

  tr-≤-∧ :
    ∀ p q r →
    tr′ p 𝟘𝟙ω.≤ q 𝟘𝟙ω.∧ r →
    ∃₂ λ q′ r′ → tr′ q′ 𝟘𝟙ω.≤ q × tr′ r′ 𝟘𝟙ω.≤ r × p E.≤ q′ E.∧ r′
  tr-≤-∧ 𝟘 𝟘 𝟘 _     = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-∧ 𝟘 𝟘 𝟙 𝟘≤𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘≰𝟘∧𝟙 𝟘≤𝟘∧𝟙)
  tr-≤-∧ 𝟘 𝟙 𝟘 𝟘≤𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘≰𝟘∧𝟙 𝟘≤𝟘∧𝟙)
  tr-≤-∧ 𝟘 𝟙 𝟙 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-∧ ω _ _ _     = ω , ω , refl , refl , refl

  𝟘≰ω·𝟘∧𝟙 : ¬ 𝟘 𝟘𝟙ω.≤ ω 𝟘𝟙ω.· 𝟘𝟙ω.𝟘∧𝟙
  𝟘≰ω·𝟘∧𝟙 𝟘≤ω·𝟘∧𝟙 =
    case begin
      𝟘                ≤⟨ 𝟘≤ω·𝟘∧𝟙 ⟩
      ω 𝟘𝟙ω.· 𝟘𝟙ω.𝟘∧𝟙  ≡⟨ 𝟘𝟙ω.ω·≢𝟘 𝟘𝟙ω.𝟘∧𝟙≢𝟘 ⟩
      ω                ∎
    of λ ()

  tr-≤-⊛ :
    ∀ p q₁ q₂ q₃ r s →
    tr′ p 𝟘𝟙ω.≤ (q₁ 𝟘𝟙ω.∧ q₂) 𝟘𝟙ω.⊛ q₃ 𝟘𝟙ω.+ tr′ r 𝟘𝟙ω.· q₂ ▷ tr′ s →
    ∃₃ λ q₁′ q₂′ q₃′ →
       tr′ q₁′ 𝟘𝟙ω.≤ q₁ × tr′ q₂′ 𝟘𝟙ω.≤ q₂ × tr′ q₃′ 𝟘𝟙ω.≤ q₃ ×
       p E.≤ (q₁′ E.∧ q₂′) E.⊛ q₃′ E.+ r E.· q₂′ ▷ s
  tr-≤-⊛ = tr-≤-⊛′ 𝟙≤𝟘
    where
    tr-≤-⊛′ :
      ∀ 𝟙≤𝟘 →
      let module 𝟘𝟙ω′ = ZOM 𝟙≤𝟘 in
      ∀ p q₁ q₂ q₃ r s →
      tr′ p 𝟘𝟙ω′.≤
        (q₁ 𝟘𝟙ω′.∧ q₂) 𝟘𝟙ω′.⊛ q₃ 𝟘𝟙ω′.+ tr′ r 𝟘𝟙ω′.· q₂ ▷ tr′ s →
      ∃₃ λ q₁′ q₂′ q₃′ →
         tr′ q₁′ 𝟘𝟙ω′.≤ q₁ × tr′ q₂′ 𝟘𝟙ω′.≤ q₂ × tr′ q₃′ 𝟘𝟙ω′.≤ q₃ ×
         p E.≤ (q₁′ E.∧ q₂′) E.⊛ q₃′ E.+ r E.· q₂′ ▷ s
    tr-≤-⊛′ _     𝟘 𝟘 𝟘 𝟘 𝟘 _ _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    tr-≤-⊛′ _     𝟘 𝟘 𝟘 𝟘 ω _ _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    tr-≤-⊛′ _     ω _ _ _ _ _ _  = ω , ω , ω , refl , refl , refl , refl
    tr-≤-⊛′ false 𝟘 𝟘 𝟘 𝟙 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟘 𝟙 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟘 𝟙 ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟘 𝟙 ω ω ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟘 ω 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟘 ω 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟘 ω ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟘 ω ω ω ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 𝟘 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 𝟘 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 𝟘 ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 𝟘 ω ω ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 𝟙 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 𝟙 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 𝟙 ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 𝟙 ω ω ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 ω 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 ω 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 ω ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟘 𝟙 ω ω ω ()
    tr-≤-⊛′ false 𝟘 𝟘 ω 𝟘 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 𝟘 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 𝟘 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 𝟘 ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 𝟘 ω ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 𝟙 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 𝟙 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 𝟙 ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 𝟙 ω ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 ω 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 ω 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 ω ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟘 ω ω ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 𝟘 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 𝟘 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 𝟘 ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 𝟘 ω ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 𝟙 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 𝟙 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 𝟙 ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 𝟙 ω ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 ω 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 ω 𝟘 ω ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 ω ω 𝟘 ()
    tr-≤-⊛′ false 𝟘 𝟙 𝟙 ω ω ω ()
    tr-≤-⊛′ false 𝟘 𝟙 ω 𝟘 𝟘 𝟘 ()
    tr-≤-⊛′ false 𝟘 ω 𝟘 𝟘 𝟘 𝟘 ()

-- The function zero-one-many→erasure is a morphism from a
-- zero-one-many-greatest modality to an erasure modality, given that
-- either both modalities allow 𝟘ᵐ, or none of them do. The
-- zero-one-many-greatest modality can be defined with either 𝟙 ≤ 𝟘 or
-- 𝟙 ≰ 𝟘.

zero-one-many⇨erasure :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (zero-one-many-greatest 𝟙≤𝟘 r₁) (ErasureModality r₂)
    zero-one-many→erasure
zero-one-many⇨erasure {𝟙≤𝟘 = 𝟙≤𝟘} {r₂ = r₂} refl = λ where
    .Is-morphism.tr-𝟘-≤                   → refl
    .Is-morphism.tr-≡-𝟘-⇔ _               → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok         → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                     → refl
    .Is-morphism.tr-+ {p = p}             → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-· {p = p}             → tr-· p _
    .Is-morphism.tr-∧ {p = p}             → ≤-reflexive (tr-∧ p _)
    .Is-morphism.tr-⊛ {p = p} {r = r}     → ≤-reflexive (tr-⊛ p _ r)
    .Is-morphism.𝟘ᵐ-in-second-if-in-first → idᶠ
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘
  open Definition.Modality.Properties (ErasureModality r₂)

  tr′ = zero-one-many→erasure

  tr-𝟘∧𝟙 : tr′ 𝟘𝟙ω.𝟘∧𝟙 ≡ ω
  tr-𝟘∧𝟙 = 𝟘𝟙ω.𝟘∧𝟙-elim
    (λ p → tr′ p ≡ ω)
    (λ _ → refl)
    (λ _ → refl)

  tr-ω[𝟘∧𝟙] : tr′ (ω 𝟘𝟙ω.· 𝟘𝟙ω.𝟘∧𝟙) ≡ ω
  tr-ω[𝟘∧𝟙] = cong tr′ (𝟘𝟙ω.ω·≢𝟘 𝟘𝟙ω.𝟘∧𝟙≢𝟘)

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-+ : ∀ p q → tr′ (p 𝟘𝟙ω.+ q) ≡ tr′ p E.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 𝟙 = refl
  tr-+ 𝟘 ω = refl
  tr-+ 𝟙 𝟘 = refl
  tr-+ 𝟙 𝟙 = refl
  tr-+ 𝟙 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω 𝟙 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p 𝟘𝟙ω.· q) ≡ tr′ p E.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 𝟙 = refl
  tr-· 𝟘 ω = refl
  tr-· 𝟙 𝟘 = refl
  tr-· 𝟙 𝟙 = refl
  tr-· 𝟙 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω 𝟙 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p 𝟘𝟙ω.∧ q) ≡ tr′ p E.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 𝟙 = tr-𝟘∧𝟙
  tr-∧ 𝟘 ω = refl
  tr-∧ 𝟙 𝟘 = tr-𝟘∧𝟙
  tr-∧ 𝟙 𝟙 = refl
  tr-∧ 𝟙 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω 𝟙 = refl
  tr-∧ ω ω = refl

  tr-⊛ : ∀ p q r → tr′ (p 𝟘𝟙ω.⊛ q ▷ r) ≡ tr′ p E.⊛ tr′ q ▷ tr′ r
  tr-⊛ 𝟘 𝟘 𝟘 = refl
  tr-⊛ 𝟘 𝟘 𝟙 = refl
  tr-⊛ 𝟘 𝟘 ω = refl
  tr-⊛ 𝟘 𝟙 𝟘 = tr-𝟘∧𝟙
  tr-⊛ 𝟘 𝟙 𝟙 = refl
  tr-⊛ 𝟘 𝟙 ω = tr-ω[𝟘∧𝟙]
  tr-⊛ 𝟘 ω 𝟘 = refl
  tr-⊛ 𝟘 ω 𝟙 = refl
  tr-⊛ 𝟘 ω ω = refl
  tr-⊛ 𝟙 𝟘 𝟘 = tr-𝟘∧𝟙
  tr-⊛ 𝟙 𝟘 𝟙 = refl
  tr-⊛ 𝟙 𝟘 ω = tr-ω[𝟘∧𝟙]
  tr-⊛ 𝟙 𝟙 𝟘 = refl
  tr-⊛ 𝟙 𝟙 𝟙 = refl
  tr-⊛ 𝟙 𝟙 ω = refl
  tr-⊛ 𝟙 ω 𝟘 = refl
  tr-⊛ 𝟙 ω 𝟙 = refl
  tr-⊛ 𝟙 ω ω = refl
  tr-⊛ ω 𝟘 𝟘 = refl
  tr-⊛ ω 𝟘 𝟙 = refl
  tr-⊛ ω 𝟘 ω = refl
  tr-⊛ ω 𝟙 𝟘 = refl
  tr-⊛ ω 𝟙 𝟙 = refl
  tr-⊛ ω 𝟙 ω = refl
  tr-⊛ ω ω 𝟘 = refl
  tr-⊛ ω ω 𝟙 = refl
  tr-⊛ ω ω ω = refl

-- The function zero-one-many→erasure is not an order embedding from a
-- zero-one-many-greatest modality to an erasure modality.

¬zero-one-many⇨erasure :
  ¬ Is-order-embedding
      (zero-one-many-greatest 𝟙≤𝟘 r₁)
      (ErasureModality r₂)
      zero-one-many→erasure
¬zero-one-many⇨erasure m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ω} refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a linear types modality, given that either both
-- modalities allow 𝟘ᵐ, or none of them do.

erasure⇨linearity :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-order-embedding (ErasureModality r₁) (linearityModality r₂)
    erasure→zero-one-many
erasure⇨linearity = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from a linear
-- types modality to an erasure modality, given that either both
-- modalities allow 𝟘ᵐ, or none of them do.

linearity⇨erasure :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (linearityModality r₁) (ErasureModality r₂)
    zero-one-many→erasure
linearity⇨erasure = zero-one-many⇨erasure

-- The function zero-one-many→erasure is not an order embedding from a
-- linear types modality to an erasure modality.

¬linearity⇨erasure :
  ¬ Is-order-embedding (linearityModality r₁) (ErasureModality r₂)
      zero-one-many→erasure
¬linearity⇨erasure = ¬zero-one-many⇨erasure

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to an affine types modality, given that either
-- both modalities allow 𝟘ᵐ, or none of them do.

erasure⇨affine :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-order-embedding (ErasureModality r₁) (affineModality r₂)
    erasure→zero-one-many
erasure⇨affine = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from an affine
-- types modality to an erasure modality, given that either both
-- modalities allow 𝟘ᵐ, or none of them do.

affine⇨erasure :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (affineModality r₁) (ErasureModality r₂)
    zero-one-many→erasure
affine⇨erasure = zero-one-many⇨erasure

-- The function zero-one-many→erasure is not an order embedding from
-- an affine types modality to an erasure modality.

¬affine⇨erasure :
  ¬ Is-order-embedding (affineModality r₁) (ErasureModality r₂)
      zero-one-many→erasure
¬affine⇨erasure = ¬zero-one-many⇨erasure

-- The function linearity→linear-or-affine is an order embedding from
-- a linear types modality to a linear or affine types modality, given
-- that either both modalities allow 𝟘ᵐ, or none of them do.

linearity⇨linear-or-affine :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-order-embedding (linearityModality r₁) (linear-or-affine r₂)
    linearity→linear-or-affine
linearity⇨linear-or-affine {r₂ = r₂} refl = λ where
    .Is-order-embedding.trivial not-ok ok   → ⊥-elim (not-ok ok)
    .Is-order-embedding.trivial-⊎-tr-𝟘      → inj₂ refl
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-≤-⊛ {s = s}      → tr-≤-⊛ _ _ _ _ _ s
    .Is-order-embedding.tr-order-reflecting → tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism         → λ where
      .Is-morphism.tr-𝟘-≤                   → refl
      .Is-morphism.tr-≡-𝟘-⇔ _               →   tr-≡-𝟘 _ ,
                                              λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok         → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                     → refl
      .Is-morphism.tr-+ {p = p}             → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-·                     → tr-· _ _
      .Is-morphism.tr-∧                     → tr-∧ _ _
      .Is-morphism.tr-⊛ {r = r}             → tr-⊛ _ _ r
      .Is-morphism.𝟘ᵐ-in-second-if-in-first → idᶠ
  where
  open Definition.Modality.Properties (linear-or-affine r₂)

  tr′ = linearity→linear-or-affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-≤-𝟙 : ∀ p → tr′ p LA.≤ 𝟙 → p L.≤ 𝟙
  tr-≤-𝟙 𝟙 _ = refl
  tr-≤-𝟙 ω _ = refl

  tr-+ : ∀ p q → tr′ (p L.+ q) ≡ tr′ p LA.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 𝟙 = refl
  tr-+ 𝟘 ω = refl
  tr-+ 𝟙 𝟘 = refl
  tr-+ 𝟙 𝟙 = refl
  tr-+ 𝟙 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω 𝟙 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p L.· q) ≡ tr′ p LA.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 𝟙 = refl
  tr-· 𝟘 ω = refl
  tr-· 𝟙 𝟘 = refl
  tr-· 𝟙 𝟙 = refl
  tr-· 𝟙 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω 𝟙 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p L.∧ q) LA.≤ tr′ p LA.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 𝟙 = ≤-refl
  tr-∧ 𝟘 ω = refl
  tr-∧ 𝟙 𝟘 = ≤-refl
  tr-∧ 𝟙 𝟙 = refl
  tr-∧ 𝟙 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω 𝟙 = refl
  tr-∧ ω ω = refl

  tr-⊛ : ∀ p q r → tr′ (p L.⊛ q ▷ r) LA.≤ tr′ p LA.⊛ tr′ q ▷ tr′ r
  tr-⊛ 𝟘 𝟘 𝟘 = refl
  tr-⊛ 𝟘 𝟘 𝟙 = refl
  tr-⊛ 𝟘 𝟘 ω = refl
  tr-⊛ 𝟘 𝟙 𝟘 = ≤-refl
  tr-⊛ 𝟘 𝟙 𝟙 = refl
  tr-⊛ 𝟘 𝟙 ω = refl
  tr-⊛ 𝟘 ω 𝟘 = refl
  tr-⊛ 𝟘 ω 𝟙 = refl
  tr-⊛ 𝟘 ω ω = refl
  tr-⊛ 𝟙 𝟘 𝟘 = ≤-refl
  tr-⊛ 𝟙 𝟘 𝟙 = refl
  tr-⊛ 𝟙 𝟘 ω = refl
  tr-⊛ 𝟙 𝟙 𝟘 = refl
  tr-⊛ 𝟙 𝟙 𝟙 = refl
  tr-⊛ 𝟙 𝟙 ω = refl
  tr-⊛ 𝟙 ω 𝟘 = refl
  tr-⊛ 𝟙 ω 𝟙 = refl
  tr-⊛ 𝟙 ω ω = refl
  tr-⊛ ω 𝟘 𝟘 = refl
  tr-⊛ ω 𝟘 𝟙 = refl
  tr-⊛ ω 𝟘 ω = refl
  tr-⊛ ω 𝟙 𝟘 = refl
  tr-⊛ ω 𝟙 𝟙 = refl
  tr-⊛ ω 𝟙 ω = refl
  tr-⊛ ω ω 𝟘 = refl
  tr-⊛ ω ω 𝟙 = refl
  tr-⊛ ω ω ω = refl

  tr-order-reflecting : ∀ p q → tr′ p LA.≤ tr′ q → p L.≤ q
  tr-order-reflecting 𝟘 𝟘 _ = refl
  tr-order-reflecting 𝟙 𝟙 _ = refl
  tr-order-reflecting ω 𝟘 _ = refl
  tr-order-reflecting ω 𝟙 _ = refl
  tr-order-reflecting ω ω _ = refl

  tr-≤-+ :
    ∀ p q r →
    tr′ p LA.≤ q LA.+ r →
    ∃₂ λ q′ r′ → tr′ q′ LA.≤ q × tr′ r′ LA.≤ r × p L.≤ q′ L.+ r′
  tr-≤-+ 𝟘 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟙 𝟘  𝟙  _  = 𝟘 , 𝟙 , refl , refl , refl
  tr-≤-+ 𝟙 𝟙  𝟘  _  = 𝟙 , 𝟘 , refl , refl , refl
  tr-≤-+ ω _  _  _  = ω , ω , refl , refl , refl
  tr-≤-+ 𝟘 𝟙  𝟙  ()
  tr-≤-+ 𝟘 ≤𝟙 𝟙  ()
  tr-≤-+ 𝟘 ≤ω 𝟙  ()
  tr-≤-+ 𝟙 ≤ω ≤𝟙 ()
  tr-≤-+ 𝟙 ≤ω ≤ω ()

  tr-≤-· :
    ∀ p q r →
    tr′ p LA.≤ tr′ q LA.· r →
    ∃ λ r′ → tr′ r′ LA.≤ r × p L.≤ q L.· r′
  tr-≤-· 𝟘 𝟘 𝟘  _   = ω , refl , refl
  tr-≤-· 𝟘 𝟘 𝟙  _   = ω , refl , refl
  tr-≤-· 𝟘 𝟘 ≤𝟙 _   = ω , refl , refl
  tr-≤-· 𝟘 𝟘 ≤ω _   = ω , refl , refl
  tr-≤-· 𝟘 𝟙 𝟘  _   = 𝟘 , refl , refl
  tr-≤-· 𝟘 ω 𝟘  _   = 𝟘 , refl , refl
  tr-≤-· 𝟙 𝟙 𝟙  _   = 𝟙 , refl , refl
  tr-≤-· ω _ _  _   = ω , refl , refl
  tr-≤-· 𝟙 ω  ≤ω ()

  tr-≤-∧ :
    ∀ p q r →
    tr′ p LA.≤ q LA.∧ r →
    ∃₂ λ q′ r′ → tr′ q′ LA.≤ q × tr′ r′ LA.≤ r × p L.≤ q′ L.∧ r′
  tr-≤-∧ 𝟘 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟙  𝟙  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ ω _  _  _  = ω , ω , refl , refl , refl
  tr-≤-∧ 𝟘 𝟙  𝟙  ()
  tr-≤-∧ 𝟘 ≤𝟙 𝟙  ()
  tr-≤-∧ 𝟙 ≤ω ≤𝟙 ()
  tr-≤-∧ 𝟙 ≤ω ≤ω ()
  tr-≤-∧ 𝟙 ≤ω 𝟘  ()

  tr-≤-⊛ :
    ∀ p q₁ q₂ q₃ r s →
    tr′ p LA.≤ (q₁ LA.∧ q₂) LA.⊛ q₃ LA.+ tr′ r LA.· q₂ ▷ tr′ s →
    ∃₃ λ q₁′ q₂′ q₃′ →
       tr′ q₁′ LA.≤ q₁ × tr′ q₂′ LA.≤ q₂ × tr′ q₃′ LA.≤ q₃ ×
       p L.≤ (q₁′ L.∧ q₂′) L.⊛ q₃′ L.+ r L.· q₂′ ▷ s
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟘 𝟘 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟘 𝟙 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟘 ω _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟙 𝟘 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟙 𝟙 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟙 ω _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  ω 𝟘 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  ω 𝟙 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  ω ω _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟘 𝟙 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟙 𝟘 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ ω _  _  _  _ _ _  = ω , ω , ω , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟘  𝟘 𝟘 ()

-- The function linear-or-affine→linearity is a morphism from a linear
-- or affine types modality to a linear types modality, given that
-- either both modalities allow 𝟘ᵐ, or none of them do.

linear-or-affine⇨linearity :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (linear-or-affine r₁) (linearityModality r₂)
    linear-or-affine→linearity
linear-or-affine⇨linearity {r₂ = r₂} refl = λ where
    .Is-morphism.tr-𝟘-≤                   → refl
    .Is-morphism.tr-≡-𝟘-⇔ _               → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok         → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                     → refl
    .Is-morphism.tr-+ {p = p}             → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                     → tr-· _ _
    .Is-morphism.tr-∧                     → ≤-reflexive (tr-∧ _ _)
    .Is-morphism.tr-⊛ {r = r}             → ≤-reflexive (tr-⊛ _ _ r)
    .Is-morphism.𝟘ᵐ-in-second-if-in-first → idᶠ
  where
  open Definition.Modality.Properties (linearityModality r₂)

  tr′ = linear-or-affine→linearity

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-+ : ∀ p q → tr′ (p LA.+ q) ≡ tr′ p L.+ tr′ q
  tr-+ 𝟘  𝟘  = refl
  tr-+ 𝟘  𝟙  = refl
  tr-+ 𝟘  ≤𝟙 = refl
  tr-+ 𝟘  ≤ω = refl
  tr-+ 𝟙  𝟘  = refl
  tr-+ 𝟙  𝟙  = refl
  tr-+ 𝟙  ≤𝟙 = refl
  tr-+ 𝟙  ≤ω = refl
  tr-+ ≤𝟙 𝟘  = refl
  tr-+ ≤𝟙 𝟙  = refl
  tr-+ ≤𝟙 ≤𝟙 = refl
  tr-+ ≤𝟙 ≤ω = refl
  tr-+ ≤ω 𝟘  = refl
  tr-+ ≤ω 𝟙  = refl
  tr-+ ≤ω ≤𝟙 = refl
  tr-+ ≤ω ≤ω = refl

  tr-· : ∀ p q → tr′ (p LA.· q) ≡ tr′ p L.· tr′ q
  tr-· 𝟘  𝟘  = refl
  tr-· 𝟘  𝟙  = refl
  tr-· 𝟘  ≤𝟙 = refl
  tr-· 𝟘  ≤ω = refl
  tr-· 𝟙  𝟘  = refl
  tr-· 𝟙  𝟙  = refl
  tr-· 𝟙  ≤𝟙 = refl
  tr-· 𝟙  ≤ω = refl
  tr-· ≤𝟙 𝟘  = refl
  tr-· ≤𝟙 𝟙  = refl
  tr-· ≤𝟙 ≤𝟙 = refl
  tr-· ≤𝟙 ≤ω = refl
  tr-· ≤ω 𝟘  = refl
  tr-· ≤ω 𝟙  = refl
  tr-· ≤ω ≤𝟙 = refl
  tr-· ≤ω ≤ω = refl

  tr-∧ : ∀ p q → tr′ (p LA.∧ q) ≡ tr′ p L.∧ tr′ q
  tr-∧ 𝟘  𝟘  = refl
  tr-∧ 𝟘  𝟙  = refl
  tr-∧ 𝟘  ≤𝟙 = refl
  tr-∧ 𝟘  ≤ω = refl
  tr-∧ 𝟙  𝟘  = refl
  tr-∧ 𝟙  𝟙  = refl
  tr-∧ 𝟙  ≤𝟙 = refl
  tr-∧ 𝟙  ≤ω = refl
  tr-∧ ≤𝟙 𝟘  = refl
  tr-∧ ≤𝟙 𝟙  = refl
  tr-∧ ≤𝟙 ≤𝟙 = refl
  tr-∧ ≤𝟙 ≤ω = refl
  tr-∧ ≤ω 𝟘  = refl
  tr-∧ ≤ω 𝟙  = refl
  tr-∧ ≤ω ≤𝟙 = refl
  tr-∧ ≤ω ≤ω = refl

  tr-⊛ : ∀ p q r → tr′ (p LA.⊛ q ▷ r) ≡ tr′ p L.⊛ tr′ q ▷ tr′ r
  tr-⊛ 𝟘  𝟘  𝟘  = refl
  tr-⊛ 𝟘  𝟘  𝟙  = refl
  tr-⊛ 𝟘  𝟘  ≤𝟙 = refl
  tr-⊛ 𝟘  𝟘  ≤ω = refl
  tr-⊛ 𝟘  𝟙  𝟘  = refl
  tr-⊛ 𝟘  𝟙  𝟙  = refl
  tr-⊛ 𝟘  𝟙  ≤𝟙 = refl
  tr-⊛ 𝟘  𝟙  ≤ω = refl
  tr-⊛ 𝟘  ≤𝟙 𝟘  = refl
  tr-⊛ 𝟘  ≤𝟙 𝟙  = refl
  tr-⊛ 𝟘  ≤𝟙 ≤𝟙 = refl
  tr-⊛ 𝟘  ≤𝟙 ≤ω = refl
  tr-⊛ 𝟘  ≤ω 𝟘  = refl
  tr-⊛ 𝟘  ≤ω 𝟙  = refl
  tr-⊛ 𝟘  ≤ω ≤𝟙 = refl
  tr-⊛ 𝟘  ≤ω ≤ω = refl
  tr-⊛ 𝟙  𝟘  𝟘  = refl
  tr-⊛ 𝟙  𝟘  𝟙  = refl
  tr-⊛ 𝟙  𝟘  ≤𝟙 = refl
  tr-⊛ 𝟙  𝟘  ≤ω = refl
  tr-⊛ 𝟙  𝟙  𝟘  = refl
  tr-⊛ 𝟙  𝟙  𝟙  = refl
  tr-⊛ 𝟙  𝟙  ≤𝟙 = refl
  tr-⊛ 𝟙  𝟙  ≤ω = refl
  tr-⊛ 𝟙  ≤𝟙 𝟘  = refl
  tr-⊛ 𝟙  ≤𝟙 𝟙  = refl
  tr-⊛ 𝟙  ≤𝟙 ≤𝟙 = refl
  tr-⊛ 𝟙  ≤𝟙 ≤ω = refl
  tr-⊛ 𝟙  ≤ω 𝟘  = refl
  tr-⊛ 𝟙  ≤ω 𝟙  = refl
  tr-⊛ 𝟙  ≤ω ≤𝟙 = refl
  tr-⊛ 𝟙  ≤ω ≤ω = refl
  tr-⊛ ≤𝟙 𝟘  𝟘  = refl
  tr-⊛ ≤𝟙 𝟘  𝟙  = refl
  tr-⊛ ≤𝟙 𝟘  ≤𝟙 = refl
  tr-⊛ ≤𝟙 𝟘  ≤ω = refl
  tr-⊛ ≤𝟙 𝟙  𝟘  = refl
  tr-⊛ ≤𝟙 𝟙  𝟙  = refl
  tr-⊛ ≤𝟙 𝟙  ≤𝟙 = refl
  tr-⊛ ≤𝟙 𝟙  ≤ω = refl
  tr-⊛ ≤𝟙 ≤𝟙 𝟘  = refl
  tr-⊛ ≤𝟙 ≤𝟙 𝟙  = refl
  tr-⊛ ≤𝟙 ≤𝟙 ≤𝟙 = refl
  tr-⊛ ≤𝟙 ≤𝟙 ≤ω = refl
  tr-⊛ ≤𝟙 ≤ω 𝟘  = refl
  tr-⊛ ≤𝟙 ≤ω 𝟙  = refl
  tr-⊛ ≤𝟙 ≤ω ≤𝟙 = refl
  tr-⊛ ≤𝟙 ≤ω ≤ω = refl
  tr-⊛ ≤ω 𝟘  𝟘  = refl
  tr-⊛ ≤ω 𝟘  𝟙  = refl
  tr-⊛ ≤ω 𝟘  ≤𝟙 = refl
  tr-⊛ ≤ω 𝟘  ≤ω = refl
  tr-⊛ ≤ω 𝟙  𝟘  = refl
  tr-⊛ ≤ω 𝟙  𝟙  = refl
  tr-⊛ ≤ω 𝟙  ≤𝟙 = refl
  tr-⊛ ≤ω 𝟙  ≤ω = refl
  tr-⊛ ≤ω ≤𝟙 𝟘  = refl
  tr-⊛ ≤ω ≤𝟙 𝟙  = refl
  tr-⊛ ≤ω ≤𝟙 ≤𝟙 = refl
  tr-⊛ ≤ω ≤𝟙 ≤ω = refl
  tr-⊛ ≤ω ≤ω 𝟘  = refl
  tr-⊛ ≤ω ≤ω 𝟙  = refl
  tr-⊛ ≤ω ≤ω ≤𝟙 = refl
  tr-⊛ ≤ω ≤ω ≤ω = refl

-- The function linear-or-affine→linearity is not an order embedding
-- from a linear or affine types modality to a linear types modality.

¬linear-or-affine⇨linearity :
  ¬ Is-order-embedding (linear-or-affine r₁) (linearityModality r₂)
      linear-or-affine→linearity
¬linear-or-affine⇨linearity m =
  case Is-order-embedding.tr-injective m {p = ≤𝟙} {q = ≤ω} refl of λ ()

-- The function affine→linear-or-affine is an order embedding from an
-- affine types modality to a linear or affine types modality, given
-- that either both modalities allow 𝟘ᵐ, or none of them do.

affine⇨linear-or-affine :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-order-embedding (affineModality r₁) (linear-or-affine r₂)
    affine→linear-or-affine
affine⇨linear-or-affine {r₂ = r₂} refl = λ where
    .Is-order-embedding.trivial not-ok ok   → ⊥-elim (not-ok ok)
    .Is-order-embedding.trivial-⊎-tr-𝟘      → inj₂ refl
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-≤-⊛ {s = s}      → tr-≤-⊛ _ _ _ _ _ s
    .Is-order-embedding.tr-order-reflecting → tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism         → λ where
      .Is-morphism.tr-𝟘-≤                   → refl
      .Is-morphism.tr-≡-𝟘-⇔ _               → tr-≡-𝟘 _
                                            , λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok         → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                     → refl
      .Is-morphism.tr-+ {p = p}             → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-·                     → tr-· _ _
      .Is-morphism.tr-∧                     → ≤-reflexive (tr-∧ _ _)
      .Is-morphism.tr-⊛ {r = r}             → ≤-reflexive (tr-⊛ _ _ r)
      .Is-morphism.𝟘ᵐ-in-second-if-in-first → idᶠ
  where
  open Definition.Modality.Properties (linear-or-affine r₂)

  tr′ = affine→linear-or-affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-≤-𝟙 : ∀ p → tr′ p LA.≤ 𝟙 → p A.≤ 𝟙
  tr-≤-𝟙 𝟙 _ = refl
  tr-≤-𝟙 ω _ = refl

  tr-+ : ∀ p q → tr′ (p A.+ q) ≡ tr′ p LA.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 𝟙 = refl
  tr-+ 𝟘 ω = refl
  tr-+ 𝟙 𝟘 = refl
  tr-+ 𝟙 𝟙 = refl
  tr-+ 𝟙 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω 𝟙 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p A.· q) ≡ tr′ p LA.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 𝟙 = refl
  tr-· 𝟘 ω = refl
  tr-· 𝟙 𝟘 = refl
  tr-· 𝟙 𝟙 = refl
  tr-· 𝟙 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω 𝟙 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p A.∧ q) ≡ tr′ p LA.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 𝟙 = refl
  tr-∧ 𝟘 ω = refl
  tr-∧ 𝟙 𝟘 = refl
  tr-∧ 𝟙 𝟙 = refl
  tr-∧ 𝟙 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω 𝟙 = refl
  tr-∧ ω ω = refl

  tr-⊛ : ∀ p q r → tr′ (p A.⊛ q ▷ r) ≡ tr′ p LA.⊛ tr′ q ▷ tr′ r
  tr-⊛ 𝟘 𝟘 𝟘 = refl
  tr-⊛ 𝟘 𝟘 𝟙 = refl
  tr-⊛ 𝟘 𝟘 ω = refl
  tr-⊛ 𝟘 𝟙 𝟘 = refl
  tr-⊛ 𝟘 𝟙 𝟙 = refl
  tr-⊛ 𝟘 𝟙 ω = refl
  tr-⊛ 𝟘 ω 𝟘 = refl
  tr-⊛ 𝟘 ω 𝟙 = refl
  tr-⊛ 𝟘 ω ω = refl
  tr-⊛ 𝟙 𝟘 𝟘 = refl
  tr-⊛ 𝟙 𝟘 𝟙 = refl
  tr-⊛ 𝟙 𝟘 ω = refl
  tr-⊛ 𝟙 𝟙 𝟘 = refl
  tr-⊛ 𝟙 𝟙 𝟙 = refl
  tr-⊛ 𝟙 𝟙 ω = refl
  tr-⊛ 𝟙 ω 𝟘 = refl
  tr-⊛ 𝟙 ω 𝟙 = refl
  tr-⊛ 𝟙 ω ω = refl
  tr-⊛ ω 𝟘 𝟘 = refl
  tr-⊛ ω 𝟘 𝟙 = refl
  tr-⊛ ω 𝟘 ω = refl
  tr-⊛ ω 𝟙 𝟘 = refl
  tr-⊛ ω 𝟙 𝟙 = refl
  tr-⊛ ω 𝟙 ω = refl
  tr-⊛ ω ω 𝟘 = refl
  tr-⊛ ω ω 𝟙 = refl
  tr-⊛ ω ω ω = refl

  tr-order-reflecting : ∀ p q → tr′ p LA.≤ tr′ q → p A.≤ q
  tr-order-reflecting 𝟘 𝟘 _ = refl
  tr-order-reflecting 𝟙 𝟘 _ = refl
  tr-order-reflecting 𝟙 𝟙 _ = refl
  tr-order-reflecting ω 𝟘 _ = refl
  tr-order-reflecting ω 𝟙 _ = refl
  tr-order-reflecting ω ω _ = refl

  tr-≤-+ :
    ∀ p q r →
    tr′ p LA.≤ q LA.+ r →
    ∃₂ λ q′ r′ → tr′ q′ LA.≤ q × tr′ r′ LA.≤ r × p A.≤ q′ A.+ r′
  tr-≤-+ 𝟘 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟙 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟙 𝟘  𝟙  _  = 𝟘 , 𝟙 , refl , refl , refl
  tr-≤-+ 𝟙 𝟘  ≤𝟙 _  = 𝟘 , 𝟙 , refl , refl , refl
  tr-≤-+ 𝟙 𝟙  𝟘  _  = 𝟙 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟙 ≤𝟙 𝟘  _  = 𝟙 , 𝟘 , refl , refl , refl
  tr-≤-+ ω _  _  _  = ω , ω , refl , refl , refl
  tr-≤-+ 𝟘 𝟙  𝟙  ()
  tr-≤-+ 𝟘 ≤𝟙 𝟙  ()
  tr-≤-+ 𝟘 ≤ω 𝟙  ()
  tr-≤-+ 𝟙 ≤ω ≤ω ()

  tr-≤-· :
    ∀ p q r →
    tr′ p LA.≤ tr′ q LA.· r →
    ∃ λ r′ → tr′ r′ LA.≤ r × p A.≤ q A.· r′
  tr-≤-· 𝟘 𝟘 𝟘  _ = ω , refl , refl
  tr-≤-· 𝟘 𝟘 𝟙  _ = ω , refl , refl
  tr-≤-· 𝟘 𝟘 ≤𝟙 _ = ω , refl , refl
  tr-≤-· 𝟘 𝟘 ≤ω _ = ω , refl , refl
  tr-≤-· 𝟘 𝟙 𝟘  _ = 𝟘 , refl , refl
  tr-≤-· 𝟘 ω 𝟘  _ = 𝟘 , refl , refl
  tr-≤-· 𝟙 𝟘 𝟘  _ = ω , refl , refl
  tr-≤-· 𝟙 𝟘 𝟙  _ = ω , refl , refl
  tr-≤-· 𝟙 𝟘 ≤𝟙 _ = ω , refl , refl
  tr-≤-· 𝟙 𝟘 ≤ω _ = ω , refl , refl
  tr-≤-· 𝟙 𝟙 𝟘  _ = 𝟙 , refl , refl
  tr-≤-· 𝟙 𝟙 𝟙  _ = 𝟙 , refl , refl
  tr-≤-· 𝟙 𝟙 ≤𝟙 _ = 𝟙 , refl , refl
  tr-≤-· 𝟙 ω 𝟘  _ = 𝟘 , refl , refl
  tr-≤-· ω _ _  _ = ω , refl , refl

  tr-≤-∧ :
    ∀ p q r →
    tr′ p LA.≤ q LA.∧ r →
    ∃₂ λ q′ r′ → tr′ q′ LA.≤ q × tr′ r′ LA.≤ r × p A.≤ q′ A.∧ r′
  tr-≤-∧ 𝟘 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟘  𝟘  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟘  𝟙  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟘  ≤𝟙 _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟙  𝟘  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟙  𝟙  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟙  ≤𝟙 _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 ≤𝟙 𝟘  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 ≤𝟙 𝟙  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 ≤𝟙 ≤𝟙 _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ ω _  _  _  = ω , ω , refl , refl , refl
  tr-≤-∧ 𝟘 𝟙  𝟙  ()
  tr-≤-∧ 𝟘 ≤𝟙 𝟙  ()

  tr-≤-⊛ :
    ∀ p q₁ q₂ q₃ r s →
    tr′ p LA.≤ (q₁ LA.∧ q₂) LA.⊛ q₃ LA.+ tr′ r LA.· q₂ ▷ tr′ s →
    ∃₃ λ q₁′ q₂′ q₃′ →
       tr′ q₁′ LA.≤ q₁ × tr′ q₂′ LA.≤ q₂ × tr′ q₃′ LA.≤ q₃ ×
       p A.≤ (q₁′ A.∧ q₂′) A.⊛ q₃′ A.+ r A.· q₂′ ▷ s
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟘 𝟘 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟘 𝟙 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟘 ω _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟙 𝟘 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟙 𝟙 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  𝟙 ω _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  ω 𝟘 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  ω 𝟙 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟘  ω ω _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟘 𝟘 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟘 𝟙 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟘 ω _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟙 𝟘 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟙 𝟙 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  𝟙 ω _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  ω 𝟘 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  ω 𝟙 _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟘  ω ω _  = 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟘 𝟘 _  = 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟙 𝟘 _  = 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  ω 𝟘 _  = 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟘 𝟘 _  = 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟙 𝟘 _  = 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 ω 𝟘 _  = 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟘 𝟘 _  = 𝟘 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟘 𝟙 _  = 𝟘 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟙 𝟘 _  = 𝟘 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟘 𝟘 _  = 𝟘 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟘 𝟘 _  = 𝟘 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟘 𝟘 _  = 𝟘 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟘 𝟙 _  = 𝟘 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟙 𝟘 _  = 𝟘 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟘 𝟘 _  = 𝟘 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘 𝟘 _  = 𝟘 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟘 𝟘 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟘 𝟙 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟙 𝟘 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟙 𝟙 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  ω 𝟘 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  ω 𝟙 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟘 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟙 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  ω 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟘 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟙 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 ω 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟘 𝟙 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟙 𝟘 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟘 𝟙 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟙 𝟘 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟘 𝟘 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟘 𝟙 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟙 𝟘 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟙 𝟙 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  ω 𝟘 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  ω 𝟙 _  = 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟘 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟙 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  ω 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 ω 𝟘 _  = 𝟙 , 𝟘 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟘 𝟙 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟙 𝟘 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘 𝟙 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙 𝟘 _  = 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 𝟘 _  = 𝟙 , 𝟙 , 𝟙 , refl , refl , refl , refl
  tr-≤-⊛ ω _  _  _  _ _ _  = ω , ω , ω , refl , refl , refl , refl
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟘  ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 𝟙  ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤𝟙 ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω 𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟘 ≤ω ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟘  ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 𝟙  ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤𝟙 ≤ω ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟘  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω 𝟙  ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤𝟙 ≤ω ω ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟘  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟘  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟘  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟘  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟘  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟘  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟘  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟘  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟘  ω ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟙  𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟙  𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟙  𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟙  𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟙  𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟙  𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟙  ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟙  ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω 𝟙  ω ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤𝟙 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤𝟙 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤𝟙 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤𝟙 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤𝟙 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤𝟙 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤𝟙 ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤𝟙 ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤𝟙 ω ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤ω 𝟘 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤ω 𝟘 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤ω 𝟘 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤ω 𝟙 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤ω 𝟙 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤ω 𝟙 ω ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤ω ω 𝟘 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤ω ω 𝟙 ()
  tr-≤-⊛ 𝟙 ≤ω ≤ω ≤ω ω ω ()

-- The function linear-or-affine→affine is a morphism from a linear or
-- affine types modality to an affine types modality, given that
-- either both modalities allow 𝟘ᵐ, or none of them do.

linear-or-affine⇨affine :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (linear-or-affine r₁) (affineModality r₂)
    linear-or-affine→affine
linear-or-affine⇨affine {r₂ = r₂} refl = λ where
    .Is-morphism.tr-𝟘-≤                   → refl
    .Is-morphism.tr-≡-𝟘-⇔ _               → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok         → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                     → refl
    .Is-morphism.tr-+ {p = p}             → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                     → tr-· _ _
    .Is-morphism.tr-∧                     → ≤-reflexive (tr-∧ _ _)
    .Is-morphism.tr-⊛ {r = r}             → ≤-reflexive (tr-⊛ _ _ r)
    .Is-morphism.𝟘ᵐ-in-second-if-in-first → idᶠ
  where
  open Definition.Modality.Properties (affineModality r₂)

  tr′ = linear-or-affine→affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-+ : ∀ p q → tr′ (p LA.+ q) ≡ tr′ p A.+ tr′ q
  tr-+ 𝟘  𝟘  = refl
  tr-+ 𝟘  𝟙  = refl
  tr-+ 𝟘  ≤𝟙 = refl
  tr-+ 𝟘  ≤ω = refl
  tr-+ 𝟙  𝟘  = refl
  tr-+ 𝟙  𝟙  = refl
  tr-+ 𝟙  ≤𝟙 = refl
  tr-+ 𝟙  ≤ω = refl
  tr-+ ≤𝟙 𝟘  = refl
  tr-+ ≤𝟙 𝟙  = refl
  tr-+ ≤𝟙 ≤𝟙 = refl
  tr-+ ≤𝟙 ≤ω = refl
  tr-+ ≤ω 𝟘  = refl
  tr-+ ≤ω 𝟙  = refl
  tr-+ ≤ω ≤𝟙 = refl
  tr-+ ≤ω ≤ω = refl

  tr-· : ∀ p q → tr′ (p LA.· q) ≡ tr′ p A.· tr′ q
  tr-· 𝟘  𝟘  = refl
  tr-· 𝟘  𝟙  = refl
  tr-· 𝟘  ≤𝟙 = refl
  tr-· 𝟘  ≤ω = refl
  tr-· 𝟙  𝟘  = refl
  tr-· 𝟙  𝟙  = refl
  tr-· 𝟙  ≤𝟙 = refl
  tr-· 𝟙  ≤ω = refl
  tr-· ≤𝟙 𝟘  = refl
  tr-· ≤𝟙 𝟙  = refl
  tr-· ≤𝟙 ≤𝟙 = refl
  tr-· ≤𝟙 ≤ω = refl
  tr-· ≤ω 𝟘  = refl
  tr-· ≤ω 𝟙  = refl
  tr-· ≤ω ≤𝟙 = refl
  tr-· ≤ω ≤ω = refl

  tr-∧ : ∀ p q → tr′ (p LA.∧ q) ≡ tr′ p A.∧ tr′ q
  tr-∧ 𝟘  𝟘  = refl
  tr-∧ 𝟘  𝟙  = refl
  tr-∧ 𝟘  ≤𝟙 = refl
  tr-∧ 𝟘  ≤ω = refl
  tr-∧ 𝟙  𝟘  = refl
  tr-∧ 𝟙  𝟙  = refl
  tr-∧ 𝟙  ≤𝟙 = refl
  tr-∧ 𝟙  ≤ω = refl
  tr-∧ ≤𝟙 𝟘  = refl
  tr-∧ ≤𝟙 𝟙  = refl
  tr-∧ ≤𝟙 ≤𝟙 = refl
  tr-∧ ≤𝟙 ≤ω = refl
  tr-∧ ≤ω 𝟘  = refl
  tr-∧ ≤ω 𝟙  = refl
  tr-∧ ≤ω ≤𝟙 = refl
  tr-∧ ≤ω ≤ω = refl

  tr-⊛ : ∀ p q r → tr′ (p LA.⊛ q ▷ r) ≡ tr′ p A.⊛ tr′ q ▷ tr′ r
  tr-⊛ 𝟘  𝟘  𝟘  = refl
  tr-⊛ 𝟘  𝟘  𝟙  = refl
  tr-⊛ 𝟘  𝟘  ≤𝟙 = refl
  tr-⊛ 𝟘  𝟘  ≤ω = refl
  tr-⊛ 𝟘  𝟙  𝟘  = refl
  tr-⊛ 𝟘  𝟙  𝟙  = refl
  tr-⊛ 𝟘  𝟙  ≤𝟙 = refl
  tr-⊛ 𝟘  𝟙  ≤ω = refl
  tr-⊛ 𝟘  ≤𝟙 𝟘  = refl
  tr-⊛ 𝟘  ≤𝟙 𝟙  = refl
  tr-⊛ 𝟘  ≤𝟙 ≤𝟙 = refl
  tr-⊛ 𝟘  ≤𝟙 ≤ω = refl
  tr-⊛ 𝟘  ≤ω 𝟘  = refl
  tr-⊛ 𝟘  ≤ω 𝟙  = refl
  tr-⊛ 𝟘  ≤ω ≤𝟙 = refl
  tr-⊛ 𝟘  ≤ω ≤ω = refl
  tr-⊛ 𝟙  𝟘  𝟘  = refl
  tr-⊛ 𝟙  𝟘  𝟙  = refl
  tr-⊛ 𝟙  𝟘  ≤𝟙 = refl
  tr-⊛ 𝟙  𝟘  ≤ω = refl
  tr-⊛ 𝟙  𝟙  𝟘  = refl
  tr-⊛ 𝟙  𝟙  𝟙  = refl
  tr-⊛ 𝟙  𝟙  ≤𝟙 = refl
  tr-⊛ 𝟙  𝟙  ≤ω = refl
  tr-⊛ 𝟙  ≤𝟙 𝟘  = refl
  tr-⊛ 𝟙  ≤𝟙 𝟙  = refl
  tr-⊛ 𝟙  ≤𝟙 ≤𝟙 = refl
  tr-⊛ 𝟙  ≤𝟙 ≤ω = refl
  tr-⊛ 𝟙  ≤ω 𝟘  = refl
  tr-⊛ 𝟙  ≤ω 𝟙  = refl
  tr-⊛ 𝟙  ≤ω ≤𝟙 = refl
  tr-⊛ 𝟙  ≤ω ≤ω = refl
  tr-⊛ ≤𝟙 𝟘  𝟘  = refl
  tr-⊛ ≤𝟙 𝟘  𝟙  = refl
  tr-⊛ ≤𝟙 𝟘  ≤𝟙 = refl
  tr-⊛ ≤𝟙 𝟘  ≤ω = refl
  tr-⊛ ≤𝟙 𝟙  𝟘  = refl
  tr-⊛ ≤𝟙 𝟙  𝟙  = refl
  tr-⊛ ≤𝟙 𝟙  ≤𝟙 = refl
  tr-⊛ ≤𝟙 𝟙  ≤ω = refl
  tr-⊛ ≤𝟙 ≤𝟙 𝟘  = refl
  tr-⊛ ≤𝟙 ≤𝟙 𝟙  = refl
  tr-⊛ ≤𝟙 ≤𝟙 ≤𝟙 = refl
  tr-⊛ ≤𝟙 ≤𝟙 ≤ω = refl
  tr-⊛ ≤𝟙 ≤ω 𝟘  = refl
  tr-⊛ ≤𝟙 ≤ω 𝟙  = refl
  tr-⊛ ≤𝟙 ≤ω ≤𝟙 = refl
  tr-⊛ ≤𝟙 ≤ω ≤ω = refl
  tr-⊛ ≤ω 𝟘  𝟘  = refl
  tr-⊛ ≤ω 𝟘  𝟙  = refl
  tr-⊛ ≤ω 𝟘  ≤𝟙 = refl
  tr-⊛ ≤ω 𝟘  ≤ω = refl
  tr-⊛ ≤ω 𝟙  𝟘  = refl
  tr-⊛ ≤ω 𝟙  𝟙  = refl
  tr-⊛ ≤ω 𝟙  ≤𝟙 = refl
  tr-⊛ ≤ω 𝟙  ≤ω = refl
  tr-⊛ ≤ω ≤𝟙 𝟘  = refl
  tr-⊛ ≤ω ≤𝟙 𝟙  = refl
  tr-⊛ ≤ω ≤𝟙 ≤𝟙 = refl
  tr-⊛ ≤ω ≤𝟙 ≤ω = refl
  tr-⊛ ≤ω ≤ω 𝟘  = refl
  tr-⊛ ≤ω ≤ω 𝟙  = refl
  tr-⊛ ≤ω ≤ω ≤𝟙 = refl
  tr-⊛ ≤ω ≤ω ≤ω = refl

-- The function linear-or-affine→affine is not an order embedding from
-- a linear or affine types modality to an affine types modality.

¬linear-or-affine⇨affine :
  ¬ Is-order-embedding (linear-or-affine r₁) (affineModality r₂)
      linear-or-affine→affine
¬linear-or-affine⇨affine m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ≤𝟙} refl of λ ()

-- The function affine→linearity is a morphism from an affine types
-- modality to a linear types modality, given that either both
-- modalities allow 𝟘ᵐ, or none of them do.

affine⇨linearity :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (affineModality r₁) (linearityModality r₂)
    affine→linearity
affine⇨linearity {r₂ = r₂} refl = λ where
    .Is-morphism.tr-𝟘-≤                   → refl
    .Is-morphism.tr-≡-𝟘-⇔ _               → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok         → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                     → refl
    .Is-morphism.tr-+ {p = p}             → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                     → tr-· _ _
    .Is-morphism.tr-∧ {p = p}             → ≤-reflexive (tr-∧ p _)
    .Is-morphism.tr-⊛ {r = r}             → ≤-reflexive (tr-⊛ _ _ r)
    .Is-morphism.𝟘ᵐ-in-second-if-in-first → idᶠ
  where
  open Definition.Modality.Properties (linearityModality r₂)

  tr′ = affine→linearity

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-+ : ∀ p q → tr′ (p A.+ q) ≡ tr′ p L.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 𝟙 = refl
  tr-+ 𝟘 ω = refl
  tr-+ 𝟙 𝟘 = refl
  tr-+ 𝟙 𝟙 = refl
  tr-+ 𝟙 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω 𝟙 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p A.· q) ≡ tr′ p L.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 𝟙 = refl
  tr-· 𝟘 ω = refl
  tr-· 𝟙 𝟘 = refl
  tr-· 𝟙 𝟙 = refl
  tr-· 𝟙 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω 𝟙 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p A.∧ q) ≡ tr′ p L.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 𝟙 = refl
  tr-∧ 𝟘 ω = refl
  tr-∧ 𝟙 𝟘 = refl
  tr-∧ 𝟙 𝟙 = refl
  tr-∧ 𝟙 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω 𝟙 = refl
  tr-∧ ω ω = refl

  tr-⊛ : ∀ p q r → tr′ (p A.⊛ q ▷ r) ≡ tr′ p L.⊛ tr′ q ▷ tr′ r
  tr-⊛ 𝟘 𝟘 𝟘 = refl
  tr-⊛ 𝟘 𝟘 𝟙 = refl
  tr-⊛ 𝟘 𝟘 ω = refl
  tr-⊛ 𝟘 𝟙 𝟘 = refl
  tr-⊛ 𝟘 𝟙 𝟙 = refl
  tr-⊛ 𝟘 𝟙 ω = refl
  tr-⊛ 𝟘 ω 𝟘 = refl
  tr-⊛ 𝟘 ω 𝟙 = refl
  tr-⊛ 𝟘 ω ω = refl
  tr-⊛ 𝟙 𝟘 𝟘 = refl
  tr-⊛ 𝟙 𝟘 𝟙 = refl
  tr-⊛ 𝟙 𝟘 ω = refl
  tr-⊛ 𝟙 𝟙 𝟘 = refl
  tr-⊛ 𝟙 𝟙 𝟙 = refl
  tr-⊛ 𝟙 𝟙 ω = refl
  tr-⊛ 𝟙 ω 𝟘 = refl
  tr-⊛ 𝟙 ω 𝟙 = refl
  tr-⊛ 𝟙 ω ω = refl
  tr-⊛ ω 𝟘 𝟘 = refl
  tr-⊛ ω 𝟘 𝟙 = refl
  tr-⊛ ω 𝟘 ω = refl
  tr-⊛ ω 𝟙 𝟘 = refl
  tr-⊛ ω 𝟙 𝟙 = refl
  tr-⊛ ω 𝟙 ω = refl
  tr-⊛ ω ω 𝟘 = refl
  tr-⊛ ω ω 𝟙 = refl
  tr-⊛ ω ω ω = refl

-- The function affine→linearity is not an order embedding from an
-- affine types modality to a linear types modality.

¬affine⇨linearity :
  ¬ Is-order-embedding (affineModality r₁) (linearityModality r₂)
      affine→linearity
¬affine⇨linearity m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ω} refl of λ ()

-- The function linearity→affine is a morphism from a linear types
-- modality to an affine types modality, given that either both
-- modalities allow 𝟘ᵐ, or none of them do.

linearity⇨affine :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (linearityModality r₁) (affineModality r₂)
    linearity→affine
linearity⇨affine {r₂ = r₂} refl = λ where
    .Is-morphism.tr-𝟘-≤                   → refl
    .Is-morphism.tr-≡-𝟘-⇔ _               → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok         → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                     → refl
    .Is-morphism.tr-+ {p = p}             → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                     → tr-· _ _
    .Is-morphism.tr-∧ {p = p}             → tr-∧ p _
    .Is-morphism.tr-⊛ {r = r}             → tr-⊛ _ _ r
    .Is-morphism.𝟘ᵐ-in-second-if-in-first → idᶠ
  where
  open Definition.Modality.Properties (affineModality r₂)

  tr′ = linearity→affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-+ : ∀ p q → tr′ (p L.+ q) ≡ tr′ p A.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 𝟙 = refl
  tr-+ 𝟘 ω = refl
  tr-+ 𝟙 𝟘 = refl
  tr-+ 𝟙 𝟙 = refl
  tr-+ 𝟙 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω 𝟙 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p L.· q) ≡ tr′ p A.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 𝟙 = refl
  tr-· 𝟘 ω = refl
  tr-· 𝟙 𝟘 = refl
  tr-· 𝟙 𝟙 = refl
  tr-· 𝟙 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω 𝟙 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p L.∧ q) A.≤ tr′ p A.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 𝟙 = ≤-refl
  tr-∧ 𝟘 ω = refl
  tr-∧ 𝟙 𝟘 = ≤-refl
  tr-∧ 𝟙 𝟙 = refl
  tr-∧ 𝟙 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω 𝟙 = refl
  tr-∧ ω ω = refl

  tr-⊛ : ∀ p q r → tr′ (p L.⊛ q ▷ r) A.≤ tr′ p A.⊛ tr′ q ▷ tr′ r
  tr-⊛ 𝟘 𝟘 𝟘 = refl
  tr-⊛ 𝟘 𝟘 𝟙 = refl
  tr-⊛ 𝟘 𝟘 ω = refl
  tr-⊛ 𝟘 𝟙 𝟘 = ≤-refl
  tr-⊛ 𝟘 𝟙 𝟙 = refl
  tr-⊛ 𝟘 𝟙 ω = refl
  tr-⊛ 𝟘 ω 𝟘 = refl
  tr-⊛ 𝟘 ω 𝟙 = refl
  tr-⊛ 𝟘 ω ω = refl
  tr-⊛ 𝟙 𝟘 𝟘 = ≤-refl
  tr-⊛ 𝟙 𝟘 𝟙 = refl
  tr-⊛ 𝟙 𝟘 ω = refl
  tr-⊛ 𝟙 𝟙 𝟘 = refl
  tr-⊛ 𝟙 𝟙 𝟙 = refl
  tr-⊛ 𝟙 𝟙 ω = refl
  tr-⊛ 𝟙 ω 𝟘 = refl
  tr-⊛ 𝟙 ω 𝟙 = refl
  tr-⊛ 𝟙 ω ω = refl
  tr-⊛ ω 𝟘 𝟘 = refl
  tr-⊛ ω 𝟘 𝟙 = refl
  tr-⊛ ω 𝟘 ω = refl
  tr-⊛ ω 𝟙 𝟘 = refl
  tr-⊛ ω 𝟙 𝟙 = refl
  tr-⊛ ω 𝟙 ω = refl
  tr-⊛ ω ω 𝟘 = refl
  tr-⊛ ω ω 𝟙 = refl
  tr-⊛ ω ω ω = refl

-- The function linearity→affine is not an order embedding from a
-- linear types modality to an affine types modality.

¬linearity⇨affine :
  ¬ Is-order-embedding (linearityModality r₁) (affineModality r₂)
      linearity→affine
¬linearity⇨affine m =
  case Is-order-embedding.tr-order-reflecting m {p = 𝟙} {q = 𝟘} refl of
    λ ()

------------------------------------------------------------------------
-- Σₚ-morphisms and order embeddings for Σₚ

-- The function erasure→zero-one-many-Σₚ is an order embedding for Σₚ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- a zero-one-many-greatest modality, given that if the second
-- modality allows 𝟘ᵐ, then the first also does this. The
-- zero-one-many-greatest modality can be defined with either 𝟙 ≤ 𝟘 or
-- 𝟙 ≰ 𝟘.

erasure⇨zero-one-many-Σₚ :
  (T (Restrictions.𝟘ᵐ-allowed r₂) → T (Restrictions.𝟘ᵐ-allowed r₁)) →
  Is-Σₚ-order-embedding
    (ErasureModality r₁)
    (zero-one-many-greatest 𝟙≤𝟘 r₂)
    erasure→zero-one-many
    erasure→zero-one-many-Σₚ
erasure⇨zero-one-many-Σₚ {𝟙≤𝟘 = 𝟙≤𝟘} ok₂₁ = record
  { tr-Σₚ-morphism = record
    { tr-≤-tr-Σₚ = λ where
        {p = 𝟘} → refl
        {p = ω} → refl
    ; tr-Σₚ-≡-𝟘-→ = λ where
        {p = 𝟘} ok₂ _ → ok₂₁ ok₂ , refl
    ; tr-Σₚ-≤-𝟙 = λ where
        {p = ω} _ → refl
    }
  ; tr-≤-tr-Σₚ-→ = λ where
      {p = 𝟘} {q = 𝟘}         _     → ω , refl , refl
      {p = 𝟘} {q = ω} {r = 𝟘} _     → 𝟘 , refl , refl
      {p = 𝟘} {q = ω} {r = 𝟙} 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
      {p = ω}                 _     → ω , refl , refl
  }
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘

-- The function erasure→zero-one-many-Σₚ is an order embedding for Σₚ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- a linear types modality, given that if the second modality allows
-- 𝟘ᵐ, then the first also does this.

erasure⇨linearity-Σₚ :
  (T (Restrictions.𝟘ᵐ-allowed r₂) → T (Restrictions.𝟘ᵐ-allowed r₁)) →
  Is-Σₚ-order-embedding (ErasureModality r₁) (linearityModality r₂)
    erasure→zero-one-many erasure→zero-one-many-Σₚ
erasure⇨linearity-Σₚ = erasure⇨zero-one-many-Σₚ

-- The function erasure→zero-one-many-Σₚ is not monotone with respect
-- to the erasure and linear types orderings.

erasure⇨linearity-Σₚ-not-monotone :
  ¬ (∀ {p q} →
     p E.≤ q →
     erasure→zero-one-many-Σₚ p L.≤ erasure→zero-one-many-Σₚ q)
erasure⇨linearity-Σₚ-not-monotone mono =
  case mono {p = ω} {q = 𝟘} refl of λ ()

-- The function erasure→zero-one-many-Σₚ is an order embedding for Σₚ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- an affine types modality, given that if the second modality allows
-- 𝟘ᵐ, then the first also does this.

erasure⇨affine-Σₚ :
  (T (Restrictions.𝟘ᵐ-allowed r₂) → T (Restrictions.𝟘ᵐ-allowed r₁)) →
  Is-Σₚ-order-embedding (ErasureModality r₁) (affineModality r₂)
    erasure→zero-one-many erasure→zero-one-many-Σₚ
erasure⇨affine-Σₚ = erasure⇨zero-one-many-Σₚ

-- The function affine→linear-or-affine-Σₚ is an order embedding for
-- Σₚ (with respect to affine→linear-or-affine) from an affine types
-- modality to a linear or affine types modality, given that if the
-- second modality allows 𝟘ᵐ, then the first also does this.

affine⇨linear-or-affine-Σₚ :
  (T (Restrictions.𝟘ᵐ-allowed r₂) → T (Restrictions.𝟘ᵐ-allowed r₁)) →
  Is-Σₚ-order-embedding (affineModality r₁) (linear-or-affine r₂)
    affine→linear-or-affine affine→linear-or-affine-Σₚ
affine⇨linear-or-affine-Σₚ {r₂ = r₂} ok₂₁ = record
  { tr-Σₚ-morphism = record
    { tr-≤-tr-Σₚ = λ where
        {p = 𝟘} → refl
        {p = 𝟙} → refl
        {p = ω} → refl
    ; tr-Σₚ-≡-𝟘-→ = λ where
        {p = 𝟘} ok₂ _ → ok₂₁ ok₂ , refl
    ; tr-Σₚ-≤-𝟙 = λ where
        {p = 𝟙} _ → refl
        {p = ω} _ → refl
    }
  ; tr-≤-tr-Σₚ-→ = λ where
      {p = 𝟘} {q = 𝟘}          _ → ω , refl , refl
      {p = 𝟘} {q = 𝟙} {r = 𝟘}  _ → 𝟘 , refl , refl
      {p = 𝟘} {q = ω} {r = 𝟘}  _ → 𝟘 , refl , refl
      {p = 𝟙} {q = 𝟘}          _ → ω , refl , refl
      {p = 𝟙} {q = 𝟙} {r = 𝟘}  _ → 𝟙 , refl , refl
      {p = 𝟙} {q = 𝟙} {r = 𝟙}  _ → 𝟙 , refl , refl
      {p = 𝟙} {q = 𝟙} {r = ≤𝟙} _ → 𝟙 , refl , refl
      {p = 𝟙} {q = ω} {r = 𝟘}  _ → 𝟘 , refl , refl
      {p = ω}                  _ → ω , refl , refl
  }

-- The function affine→linear-or-affine-Σₚ is not monotone with
-- respect to the affine types and linear or affine types orderings.

affine→linear-or-affine-Σₚ-not-monotone :
  ¬ (∀ {p q} →
     p A.≤ q →
     affine→linear-or-affine-Σₚ p LA.≤ affine→linear-or-affine-Σₚ q)
affine→linear-or-affine-Σₚ-not-monotone mono =
  case mono {p = 𝟙} {q = 𝟘} refl of λ ()

-- There is a function tr-Σₚ that is a Σₚ-morphism and an order
-- embedding for Σₚ for two modalities (with respect to a function
-- that is an order embedding for those modalities), but neither a
-- morphism nor an order embedding for those modalities.

Σₚ-order-embedding-but-not-order-embedding :
  ∃₂ λ (M₁ M₂ : Set) →
  ∃₂ λ (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂) →
  ∃₂ λ (tr tr-Σₚ : M₁ → M₂) →
  Is-order-embedding 𝕄₁ 𝕄₂ tr ×
  Is-Σₚ-morphism 𝕄₁ 𝕄₂ tr tr-Σₚ ×
  Is-Σₚ-order-embedding 𝕄₁ 𝕄₂ tr tr-Σₚ ×
  ¬ Is-morphism 𝕄₁ 𝕄₂ tr-Σₚ ×
  ¬ Is-order-embedding 𝕄₁ 𝕄₂ tr-Σₚ
Σₚ-order-embedding-but-not-order-embedding =
    Affine , Linear-or-affine
  , affineModality no-restrictions
  , linear-or-affine no-restrictions
  , affine→linear-or-affine , affine→linear-or-affine-Σₚ
  , affine⇨linear-or-affine refl
  , Is-Σₚ-order-embedding.tr-Σₚ-morphism (affine⇨linear-or-affine-Σₚ _)
  , affine⇨linear-or-affine-Σₚ _
  , affine→linear-or-affine-Σₚ-not-monotone ∘→ Is-morphism.tr-monotone
  , affine→linear-or-affine-Σₚ-not-monotone ∘→
    Is-order-embedding.tr-monotone

-- The function affine→linearity-Σₚ is a Σₚ-morphism (with respect to
-- affine→linearity) from an affine types modality to a linear types
-- modality, given that if the second modality allows 𝟘ᵐ, then the
-- first also does this.

affine⇨linearity-Σₚ :
  (T (Restrictions.𝟘ᵐ-allowed r₂) → T (Restrictions.𝟘ᵐ-allowed r₁)) →
  Is-Σₚ-morphism (affineModality r₁) (linearityModality r₂)
    affine→linearity affine→linearity-Σₚ
affine⇨linearity-Σₚ {r₂ = r₂} ok₂₁ = record
  { tr-≤-tr-Σₚ = λ where
      {p = 𝟘} → refl
      {p = 𝟙} → refl
      {p = ω} → refl
  ; tr-Σₚ-≡-𝟘-→ = λ where
      {p = 𝟘} ok₂ _ → ok₂₁ ok₂ , refl
  ; tr-Σₚ-≤-𝟙 = λ where
      {p = 𝟙} _ → refl
      {p = ω} _ → refl
  }

-- The function affine→linearity-Σₚ is not monotone with respect to
-- the affine types and linear types orderings.

affine→linearity-Σₚ-not-monotone :
  ¬ (∀ {p q} →
     p A.≤ q →
     affine→linearity-Σₚ p L.≤ affine→linearity-Σₚ q)
affine→linearity-Σₚ-not-monotone mono =
  case mono {p = 𝟙} {q = 𝟘} refl of λ ()

-- The function affine→linearity-Σₚ is not an order embedding for Σₚ
-- (with respect to affine→linearity) from an affine types modality to
-- a linear types modality.

¬affine⇨linearity-Σₚ :
  ¬ Is-Σₚ-order-embedding (affineModality r₁) (linearityModality r₂)
      affine→linearity affine→linearity-Σₚ
¬affine⇨linearity-Σₚ m =
  case
    Is-Σₚ-order-embedding.tr-≤-tr-Σₚ-→ m {p = 𝟙} {q = ω} {r = ω} refl
  of λ where
    (𝟘 , () , _)
    (𝟙 , _  , ())
    (ω , _  , ())

------------------------------------------------------------------------
-- Some lemmas related to equal-binder-quantities and concrete
-- translation functions

-- The functions erasure→zero-one-many and erasure→zero-one-many-Σₚ do
-- not preserve certain term restrictions obtained using
-- equal-binder-quantities.

¬-erasure→zero-one-many-Σₚ-preserves-equal-binder-quantities :
  ¬ Are-preserving-term-restrictions
      (equal-binder-quantities no-term-restrictions)
      (equal-binder-quantities rt)
      erasure→zero-one-many erasure→zero-one-many-Σₚ
¬-erasure→zero-one-many-Σₚ-preserves-equal-binder-quantities r =
  case Binder-preserved {b = BMΣ Σₚ} {p = ω} (_ , refl) .proj₂ of λ ()
  where
  open Are-preserving-term-restrictions r

-- The functions affine→linear-or-affine and
-- affine→linear-or-affine-Σₚ do not preserve certain term
-- restrictions obtained using equal-binder-quantities.

¬-affine→linear-or-affine-Σₚ-preserves-equal-binder-quantities :
  ¬ Are-preserving-term-restrictions
      (equal-binder-quantities no-term-restrictions)
      (equal-binder-quantities rt)
      affine→linear-or-affine affine→linear-or-affine-Σₚ
¬-affine→linear-or-affine-Σₚ-preserves-equal-binder-quantities r =
  case Binder-preserved {b = BMΣ Σₚ} {p = 𝟙} (_ , refl) .proj₂ of λ ()
  where
  open Are-preserving-term-restrictions r

------------------------------------------------------------------------
-- Some lemmas related to second-ΠΣ-quantities-𝟘-or-ω and concrete
-- translation functions

-- If the function unit→erasure preserves term restrictions for a unit
-- modality and an erasure modality, then it also does this for
-- certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

unit→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Are-preserving-term-restrictions
    rt (Restrictions.term-restrictions r) unit→erasure unit→erasure →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω tt (UnitModality rt))
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality r))
    unit→erasure unit→erasure
unit→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω {r = r} =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    {𝕄₂ = ErasureModality r}
    unit⇨erasure
    (Is-morphism→Is-Σₚ-morphism $
     Is-order-embedding.tr-morphism unit⇨erasure)
    (λ _ → refl)
    refl

-- If the function unit→erasure reflects term restrictions for a unit
-- modality and an erasure modality, then it also does this for
-- certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  Are-reflecting-term-restrictions
    rt (Restrictions.term-restrictions r) unit→erasure unit→erasure →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω tt (UnitModality rt))
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality r))
    unit→erasure unit→erasure
unit→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω {r = r} =
  Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    {𝕄₂ = ErasureModality r}
    unit⇨erasure
    (Is-morphism→Is-Σₚ-morphism $
     Is-order-embedding.tr-morphism unit⇨erasure)
    (λ _ → refl)
    (λ _ → refl)

-- If the function erasure→unit preserves term restrictions for an
-- erasure modality and a unit modality, then it also does this for
-- certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

erasure→unit-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r) rt erasure→unit erasure→unit →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality r))
    (second-ΠΣ-quantities-𝟘-or-ω tt (UnitModality rt))
    erasure→unit erasure→unit
erasure→unit-preserves-second-ΠΣ-quantities-𝟘-or-ω r =
  record
    { Prodrec-preserved = Prodrec-preserved
    ; Binder-preserved  = λ (b , _) →
        Binder-preserved b , (λ _ → refl) , (λ _ → refl)
    }
  where
  open Are-preserving-term-restrictions r

-- The function erasure→unit does not reflect certain term
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-erasure→unit-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ¬ Are-reflecting-term-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality r))
      (second-ΠΣ-quantities-𝟘-or-ω tt
         (UnitModality no-term-restrictions))
      erasure→unit erasure→unit
¬-erasure→unit-reflects-second-ΠΣ-quantities-𝟘-or-ω r =
  case
    Binder-reflected {b = BMΠ} {p = 𝟘} {q = ω}
      (_ , (λ _ → refl) , (λ _ → refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Are-reflecting-term-restrictions r

-- If the function erasure→zero-one-many preserves term restrictions
-- for an erasure modality and a zero-one-many-greatest modality, and
-- 𝟘ᵐ is either allowed in both modalities or none, then the function
-- preserves certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    erasure→zero-one-many erasure→zero-one-many →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 r₂))
    erasure→zero-one-many erasure→zero-one-many
erasure→zero-one-many-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σₚ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    refl
  where
  m = erasure⇨zero-one-many eq

-- If the function erasure→zero-one-many reflects term restrictions
-- for an erasure modality and a zero-one-many-greatest modality, and
-- 𝟘ᵐ is either allowed in both modalities or none, then the function
-- reflects certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-reflecting-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    erasure→zero-one-many erasure→zero-one-many →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 r₂))
    erasure→zero-one-many erasure→zero-one-many
erasure→zero-one-many-reflects-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σₚ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    (λ where
       {p = ω} _ → refl)
  where
  m = erasure⇨zero-one-many eq

-- If the functions erasure→zero-one-many and erasure→zero-one-many-Σₚ
-- preserve term restrictions for an erasure modality and a
-- zero-one-many-greatest modality, and 𝟘ᵐ is either allowed in both
-- modalities or none, then the functions preserve certain term
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

erasure→zero-one-many-Σₚ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    erasure→zero-one-many erasure→zero-one-many-Σₚ →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 r₂))
    erasure→zero-one-many erasure→zero-one-many-Σₚ
erasure→zero-one-many-Σₚ-preserves-second-ΠΣ-quantities-𝟘-or-ω
 {r₁ = r₁} refl =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝕄₁ = ErasureModality r₁}
    (Is-order-embedding.tr-morphism $ erasure⇨zero-one-many refl)
    (Is-Σₚ-order-embedding.tr-Σₚ-morphism
       (erasure⇨zero-one-many-Σₚ idᶠ))
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = ω} → (λ ()) , (λ ())))
    refl

-- If the functions erasure→zero-one-many and erasure→zero-one-many-Σₚ
-- reflect term restrictions for an erasure modality and a
-- zero-one-many-greatest modality, and 𝟘ᵐ is either allowed in both
-- modalities or none, then the functions reflect certain term
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

erasure→zero-one-many-Σₚ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-reflecting-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    erasure→zero-one-many erasure→zero-one-many-Σₚ →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 r₂))
    erasure→zero-one-many erasure→zero-one-many-Σₚ
erasure→zero-one-many-Σₚ-reflects-second-ΠΣ-quantities-𝟘-or-ω
  {r₁ = r₁} refl =
  Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝕄₁ = ErasureModality r₁}
    (Is-order-embedding.tr-morphism $ erasure⇨zero-one-many refl)
    (Is-Σₚ-order-embedding.tr-Σₚ-morphism $
     erasure⇨zero-one-many-Σₚ idᶠ)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = ω} → (λ ()) , (λ ())))
    (λ where
       {p = ω} _ → refl)

-- If the function zero-one-many→erasure preserves term restrictions
-- for a zero-one-many-greatest modality and an erasure modality, and
-- 𝟘ᵐ is either allowed in both modalities or none, then the function
-- also preserves term restrictions for certain term restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

zero-one-many→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    zero-one-many→erasure zero-one-many→erasure →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (ErasureModality r₂))
    zero-one-many→erasure zero-one-many→erasure
zero-one-many→erasure-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σₚ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    refl
  where
  m = zero-one-many⇨erasure eq

-- The function zero-one-many→erasure does not reflect certain term
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-zero-one-many→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ¬ Are-reflecting-term-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (zero-one-many-greatest 𝟙≤𝟘 r))
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (ErasureModality (𝟘ᵐ-allowed-if ok)))
      zero-one-many→erasure zero-one-many→erasure
¬-zero-one-many→erasure-reflects-second-ΠΣ-quantities-𝟘-or-ω r =
  case
    Binder-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ ()) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Are-reflecting-term-restrictions r

-- If the function linearity→linear-or-affine preserves term
-- restrictions for a linear types modality and a linear or affine
-- types modality, and 𝟘ᵐ is either allowed in both modalities or
-- none, then the function preserves certain term restrictions
-- obtained using second-ΠΣ-quantities-𝟘-or-ω.

linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    linearity→linear-or-affine linearity→linear-or-affine →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine r₂))
    linearity→linear-or-affine linearity→linear-or-affine
linearity→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σₚ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    refl
  where
  m = linearity⇨linear-or-affine eq

-- If the function linearity→linear-or-affine reflects term
-- restrictions for a linear types modality and a linear or affine
-- types modality, and 𝟘ᵐ is either allowed in both modalities or
-- none, then the function reflects certain term restrictions obtained
-- using second-ΠΣ-quantities-𝟘-or-ω.

linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-reflecting-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    linearity→linear-or-affine linearity→linear-or-affine →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine r₂))
    linearity→linear-or-affine linearity→linear-or-affine
linearity→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σₚ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    (λ where
       {p = ω} _ → refl)
  where
  m = linearity⇨linear-or-affine eq

-- If the function linear-or-affine→linearity preserves term
-- restrictions for a linear or affine types modality and a linear
-- types modality, and 𝟘ᵐ is either allowed in both modalities or
-- none, then the function also preserves term restrictions for
-- certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

linear-or-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    linear-or-affine→linearity linear-or-affine→linearity →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality r₂))
    linear-or-affine→linearity linear-or-affine→linearity
linear-or-affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σₚ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ())))
    refl
  where
  m = linear-or-affine⇨linearity eq

-- The function linear-or-affine→linearity does not reflect certain
-- term restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-linear-or-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ¬ Are-reflecting-term-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine r))
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (linearityModality (𝟘ᵐ-allowed-if ok)))
      linear-or-affine→linearity linear-or-affine→linearity
¬-linear-or-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω r =
  case
    Binder-reflected {b = BMΠ} {p = ≤ω} {q = ≤𝟙}
      (_ , (λ ()) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Are-reflecting-term-restrictions r

-- If the function affine→linear-or-affine preserves term restrictions
-- for an affine types modality and a linear or affine types modality,
-- and 𝟘ᵐ is either allowed in both modalities or none, then the
-- function preserves certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    affine→linear-or-affine affine→linear-or-affine →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine r₂))
    affine→linear-or-affine affine→linear-or-affine
affine→linear-or-affine-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σₚ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    refl
  where
  m = affine⇨linear-or-affine eq

-- If the function affine→linear-or-affine reflects term restrictions
-- for an affine types modality and a linear or affine types modality,
-- and 𝟘ᵐ is either allowed in both modalities or none, then the
-- function reflects certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-reflecting-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    affine→linear-or-affine affine→linear-or-affine →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine r₂))
    affine→linear-or-affine affine→linear-or-affine
affine→linear-or-affine-reflects-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω′
    m
    (Is-morphism→Is-Σₚ-morphism $ Is-order-embedding.tr-morphism m)
    (λ _ → refl)
    (λ where
       {p = ω} _ → refl)
  where
  m = affine⇨linear-or-affine eq

-- If the functions affine→linear-or-affine and
-- affine→linear-or-affine-Σₚ preserve term restrictions for an affine
-- types modality and a linear or affine types modality, and 𝟘ᵐ is
-- either allowed in both modalities or none, then the functions
-- preserve certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-Σₚ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    affine→linear-or-affine affine→linear-or-affine-Σₚ →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine r₂))
    affine→linear-or-affine affine→linear-or-affine-Σₚ
affine→linear-or-affine-Σₚ-preserves-second-ΠΣ-quantities-𝟘-or-ω
  {r₁ = r₁} refl =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝕄₁ = affineModality r₁}
    (Is-order-embedding.tr-morphism $ affine⇨linear-or-affine refl)
    (Is-Σₚ-order-embedding.tr-Σₚ-morphism $
     affine⇨linear-or-affine-Σₚ idᶠ)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    refl

-- If the functions affine→linear-or-affine and
-- affine→linear-or-affine-Σₚ reflect term restrictions for an affine
-- types modality and a linear or affine types modality, and 𝟘ᵐ is
-- either allowed in both modalities or none, then the functions
-- reflect certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

affine→linear-or-affine-Σₚ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-reflecting-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    affine→linear-or-affine affine→linear-or-affine-Σₚ →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine r₂))
    affine→linear-or-affine affine→linear-or-affine-Σₚ
affine→linear-or-affine-Σₚ-reflects-second-ΠΣ-quantities-𝟘-or-ω
  {r₁ = r₁} refl =
  Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝕄₁ = affineModality r₁}
    (Is-order-embedding.tr-morphism $ affine⇨linear-or-affine refl)
    (Is-Σₚ-order-embedding.tr-Σₚ-morphism $
     affine⇨linear-or-affine-Σₚ idᶠ)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    (λ where
       {p = ω} _ → refl)

-- If the function linear-or-affine→affine preserves term restrictions
-- for a linear or affine types modality and an affine types modality,
-- and 𝟘ᵐ is either allowed in both modalities or none, then the
-- function also preserves term restrictions for certain term
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

linear-or-affine→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    linear-or-affine→affine linear-or-affine→affine →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r₂))
    linear-or-affine→affine linear-or-affine→affine
linear-or-affine→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σₚ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ())))
    refl
  where
  m = linear-or-affine⇨affine eq

-- If the function linear-or-affine→affine reflects term restrictions
-- for a linear or affine types modality and an affine types modality,
-- and 𝟘ᵐ is either allowed in both modalities or none, then the
-- function also reflects term restrictions for certain term
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

linear-or-affine→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-reflecting-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    linear-or-affine→affine linear-or-affine→affine →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ≤ω (linear-or-affine r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r₂))
    linear-or-affine→affine linear-or-affine→affine
linear-or-affine→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σₚ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘}  → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙}  → (λ ()) , (λ ())
            {p = ≤𝟙} → (λ ()) , (λ ())
            {p = ≤ω} → (λ ()) , (λ ())))
    (λ where
       {p = ≤ω} _ → refl)
  where
  m = linear-or-affine⇨affine eq

-- If the function affine→linearity preserves term restrictions for an
-- affine types modality and a linear types modality, and 𝟘ᵐ is either
-- allowed in both modalities or none, then the function preserves
-- certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    affine→linearity affine→linearity →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality r₂))
    affine→linearity affine→linearity
affine→linearity-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σₚ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    refl
  where
  m = affine⇨linearity eq

-- The function affine→linearity does not reflect certain term
-- restrictions obtained using second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ¬ Are-reflecting-term-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r))
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (linearityModality (𝟘ᵐ-allowed-if ok)))
      affine→linearity affine→linearity
¬-affine→linearity-reflects-second-ΠΣ-quantities-𝟘-or-ω r =
  case
    Binder-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ ()) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Are-reflecting-term-restrictions r

-- If the functions affine→linearity and affine→linearity-Σₚ preserve
-- term restrictions for an affine types modality and a linear types
-- modality, and 𝟘ᵐ is either allowed in both modalities or none, then
-- the functions preserve certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

affine→linearity-Σₚ-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    affine→linearity affine→linearity-Σₚ →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality r₂))
    affine→linearity affine→linearity-Σₚ
affine→linearity-Σₚ-preserves-second-ΠΣ-quantities-𝟘-or-ω
  {r₁ = r₁} refl =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    {𝕄₁ = affineModality r₁}
    (affine⇨linearity refl)
    (affine⇨linearity-Σₚ idᶠ)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    refl

-- The functions affine→linearity and affine→linearity-Σₚ do not
-- reflect certain term restrictions obtained using
-- second-ΠΣ-quantities-𝟘-or-ω.

¬-affine→linearity-Σₚ-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  ¬ Are-reflecting-term-restrictions
      (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r))
      (second-ΠΣ-quantities-𝟘-or-ω ω
         (linearityModality (𝟘ᵐ-allowed-if ok)))
      affine→linearity affine→linearity-Σₚ
¬-affine→linearity-Σₚ-reflects-second-ΠΣ-quantities-𝟘-or-ω r =
  case
    Binder-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ ()) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Are-reflecting-term-restrictions r

-- If the function linearity→affine preserves term restrictions for a
-- linear types modality and an affine types modality, and 𝟘ᵐ is
-- either allowed in both modalities or none, then the function also
-- preserves term restrictions for certain term restrictions obtained
-- using second-ΠΣ-quantities-𝟘-or-ω.

linearity→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-preserving-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    linearity→affine linearity→affine →
  Are-preserving-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r₂))
    linearity→affine linearity→affine
linearity→affine-preserves-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-preserving-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σₚ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    refl
  where
  m = linearity⇨affine eq

-- If the function linearity→affine reflects term restrictions for a
-- linear types modality and an affine types modality, and 𝟘ᵐ is
-- either allowed in both modalities or none, then the function also
-- reflects term restrictions for certain term restrictions obtained
-- using second-ΠΣ-quantities-𝟘-or-ω.

linearity→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω :
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Are-reflecting-term-restrictions
    (Restrictions.term-restrictions r₁)
    (Restrictions.term-restrictions r₂)
    linearity→affine linearity→affine →
  Are-reflecting-term-restrictions
    (second-ΠΣ-quantities-𝟘-or-ω ω (linearityModality r₁))
    (second-ΠΣ-quantities-𝟘-or-ω ω (affineModality r₂))
    linearity→affine linearity→affine
linearity→affine-reflects-second-ΠΣ-quantities-𝟘-or-ω eq =
  Are-reflecting-term-restrictions-second-ΠΣ-quantities-𝟘-or-ω
    m
    (Is-morphism→Is-Σₚ-morphism m)
    (λ _ →
         (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ()))
       , (λ where
            {p = 𝟘} → (λ _ → refl) , (λ _ → refl)
            {p = 𝟙} → (λ ()) , (λ ())
            {p = ω} → (λ ()) , (λ ())))
    (λ where
       {p = ω} _ → refl)
  where
  m = linearity⇨affine eq
