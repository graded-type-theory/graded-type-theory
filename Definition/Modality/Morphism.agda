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

open import Definition.Mode.Restrictions

open Mode-restrictions

open import Definition.Mode as Mode hiding (module Mode)

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.QuantityTranslation

private variable
  a₁ a₂                       : Level
  𝟙≤𝟘 ok                      : Bool
  not-ok                      : ¬ T _
  rs rs₁ rs₂                  : Mode-restrictions
  M₁ M₂                       : Set _
  𝕄 𝕄₁ 𝕄₂ 𝕄₃                  : Modality _
  b                           : BinderMode
  tr tr₁ tr₂ tr-Σ tr-Σ₁ tr-Σ₂ : M₁ → M₂

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

-- The property of being a Σ-morphism (with respect to a given
-- function).
--
-- Note that Σ-morphisms do not have to be morphisms (see
-- Σ-order-embedding-but-not-order-embedding below).

record Is-Σ-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂

  field
    -- The regular translation function tr is bounded by the
    -- Σ-translation tr-Σ.
    tr-≤-tr-Σ : ∀ {p} → tr p M₂.≤ tr-Σ p

    -- If 𝟘ᵐ is allowed in the target modality and tr-Σ p is equal
    -- to 𝟘, then 𝟘ᵐ is allowed in the source modality and p is equal
    -- to 𝟘.
    tr-Σ-≡-𝟘-→ :
      ∀ {p} →
      T M₂.𝟘ᵐ-allowed → tr-Σ p ≡ M₂.𝟘 → T M₁.𝟘ᵐ-allowed × p ≡ M₁.𝟘

    -- If p is bounded by 𝟙, then tr-Σ p is bounded by 𝟙.
    tr-Σ-≤-𝟙 : ∀ {p} → p M₁.≤ M₁.𝟙 → tr-Σ p M₂.≤ M₂.𝟙

    -- The quantity tr p · tr-Σ q is bounded by the translation of
    -- p · q.
    tr-·-tr-Σ-≤ : ∀ {p q} → tr p M₂.· tr-Σ q M₂.≤ tr (p M₁.· q)

  -- If 𝟘ᵐ is allowed in the target modality but not the source
  -- modality, then tr-Σ translates quantities to quantities that are
  -- not equal to 𝟘.

  tr-Σ-≢-𝟘 :
    ∀ {p} → ¬ T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed → tr-Σ p ≢ M₂.𝟘
  tr-Σ-≢-𝟘 not-ok ok tr-p≡𝟘 = not-ok (tr-Σ-≡-𝟘-→ ok tr-p≡𝟘 .proj₁)

  -- If 𝟘ᵐ is allowed in the source and target modalities, then tr-Σ
  -- translates 𝟘 to 𝟘 (assuming that tr is a morphism from 𝕄₁ to 𝕄₂).

  tr-Σ-𝟘-≡ :
    Is-morphism 𝕄₁ 𝕄₂ tr →
    T M₁.𝟘ᵐ-allowed → tr-Σ M₁.𝟘 ≡ M₂.𝟘
  tr-Σ-𝟘-≡ m ok = 𝟘≮ (𝟘ᵐ-in-second-if-in-first ok) (begin
    M₂.𝟘       ≡˘⟨ tr-𝟘-≡ ok ⟩
    tr M₁.𝟘    ≤⟨ tr-≤-tr-Σ ⟩
    tr-Σ M₁.𝟘  ∎)
    where
    open Is-morphism m
    open Definition.Modality.Properties 𝕄₂
    open Tools.Reasoning.PartialOrder ≤-poset

  -- If tr-Σ p is bounded by 𝟙, then p is bounded by 𝟙 (assuming that
  -- tr is an order embedding from 𝕄₁ to 𝕄₂).

  tr-Σ-≤-𝟙-→ :
    ∀ {p} →
    Is-order-embedding 𝕄₁ 𝕄₂ tr →
    tr-Σ p M₂.≤ M₂.𝟙 → p M₁.≤ M₁.𝟙
  tr-Σ-≤-𝟙-→ {p = p} m tr-Σ-p≤𝟙 = Is-order-embedding.tr-≤-𝟙 m (begin
    tr p    ≤⟨ tr-≤-tr-Σ ⟩
    tr-Σ p  ≤⟨ tr-Σ-p≤𝟙 ⟩
    M₂.𝟙    ∎)
    where
    open Definition.Modality.Properties 𝕄₂
    open Tools.Reasoning.PartialOrder ≤-poset

  -- The quantity tr p · tr-Σ q is equal to the translation of p · q
  -- (assuming that tr is a morphism from 𝕄₁ to 𝕄₂).

  tr-·-tr-Σ-≡ :
    ∀ {p q} →
    Is-morphism 𝕄₁ 𝕄₂ tr →
    tr p M₂.· tr-Σ q ≡ tr (p M₁.· q)
  tr-·-tr-Σ-≡ {p = p} {q = q} m = ≤-antisym
    tr-·-tr-Σ-≤
    (begin
       tr (p M₁.· q)     ≡⟨ Is-morphism.tr-· m ⟩
       tr p M₂.· tr q    ≤⟨ ·-monotoneʳ tr-≤-tr-Σ ⟩
       tr p M₂.· tr-Σ q  ∎)
    where
    open Definition.Modality.Properties 𝕄₂
    open Tools.Reasoning.PartialOrder ≤-poset

-- The property of being an order embedding for Σ (with respect to a
-- given function).
--
-- Note that these "order embeddings" do not need to be order
-- embeddings (see Σ-order-embedding-but-not-order-embedding below).

record Is-Σ-order-embedding
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂

  field
    -- The translation function tr-Σ is a Σ-morphism with respect to
    -- tr.
    tr-Σ-morphism : Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ

    -- If the regular translation of p is bounded by tr-Σ q · r, then
    -- there is some r′ such that the regular translation of r′ is r
    -- and p is bounded by q · r′.
    tr-≤-tr-Σ-→ :
      ∀ {p q r} →
      tr p M₂.≤ tr-Σ q M₂.· r → ∃ λ r′ → tr r′ M₂.≤ r × p M₁.≤ q M₁.· r′

  open Is-Σ-morphism tr-Σ-morphism public

------------------------------------------------------------------------
-- Morphisms are Σ-morphisms with respect to themselves, and order
-- embeddings are order embeddings for Σ with respect to themselves

-- If tr is a morphism, then it is a Σ-morphism with respect to
-- itself.

Is-morphism→Is-Σ-morphism :
  Is-morphism 𝕄₁ 𝕄₂ tr →
  Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr
Is-morphism→Is-Σ-morphism {𝕄₁ = 𝕄₁} {𝕄₂ = 𝕄₂} {tr = tr} m = λ where
    .Is-Σ-morphism.tr-≤-tr-Σ →
      MP₂.≤-refl
    .Is-Σ-morphism.tr-Σ-≡-𝟘-→ ok tr-p≡𝟘 →
      𝟘ᵐ-allowed-elim 𝕄₁
        (λ ok → ok , tr-≡-𝟘-⇔ ok .proj₁ tr-p≡𝟘)
        (λ not-ok → ⊥-elim (tr-<-𝟘 not-ok ok .proj₂ tr-p≡𝟘))
    .Is-Σ-morphism.tr-Σ-≤-𝟙 {p = p} p≤𝟙 → begin
      tr p     ≤⟨ tr-monotone p≤𝟙 ⟩
      tr M₁.𝟙  ≤⟨ tr-𝟙 ⟩
      M₂.𝟙     ∎
    .Is-Σ-morphism.tr-·-tr-Σ-≤ {p = p} {q = q} → begin
      tr p M₂.· tr q  ≡˘⟨ tr-· ⟩
      tr (p M₁.· q)   ∎
  where
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module MP₂ = Definition.Modality.Properties 𝕄₂
  open Is-morphism m
  open Tools.Reasoning.PartialOrder MP₂.≤-poset

-- If tr is an order embedding, then it is an order embedding for Σ
-- with respect to itself.

Is-order-embedding→Is-Σ-order-embedding :
  Is-order-embedding 𝕄₁ 𝕄₂ tr →
  Is-Σ-order-embedding 𝕄₁ 𝕄₂ tr tr
Is-order-embedding→Is-Σ-order-embedding m = λ where
    .Is-Σ-order-embedding.tr-Σ-morphism →
      Is-morphism→Is-Σ-morphism tr-morphism
    .Is-Σ-order-embedding.tr-≤-tr-Σ-→ →
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

-- Composition preserves Is-Σ-morphism given a certain assumption.

Is-Σ-morphism-∘ :
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-Σ-morphism 𝕄₂ 𝕄₃ tr₁ tr-Σ₁ →
  Is-Σ-morphism 𝕄₁ 𝕄₂ tr₂ tr-Σ₂ →
  Is-Σ-morphism 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Is-Σ-morphism-∘
  {𝕄₂ = 𝕄₂} {𝕄₃ = 𝕄₃} {tr₁ = tr₁} {tr-Σ₁ = tr-Σ₁} {𝕄₁ = 𝕄₁} {tr₂ = tr₂}
  {tr-Σ₂ = tr-Σ₂} m f g = record
  { tr-≤-tr-Σ = λ {p = p} → begin
      tr₁ (tr₂ p)      ≤⟨ Is-morphism.tr-monotone m G.tr-≤-tr-Σ ⟩
      tr₁ (tr-Σ₂ p)    ≤⟨ F.tr-≤-tr-Σ ⟩
      tr-Σ₁ (tr-Σ₂ p)  ∎
  ; tr-Σ-≡-𝟘-→ =
      curry (uncurry G.tr-Σ-≡-𝟘-→ ∘→ uncurry F.tr-Σ-≡-𝟘-→)
  ; tr-Σ-≤-𝟙 =
      F.tr-Σ-≤-𝟙 ∘→ G.tr-Σ-≤-𝟙
  ; tr-·-tr-Σ-≤ = λ {p = p} {q = q} → begin
      tr₁ (tr₂ p) M₃.· tr-Σ₁ (tr-Σ₂ q)  ≤⟨ F.tr-·-tr-Σ-≤ ⟩
      tr₁ (tr₂ p M₂.· tr-Σ₂ q)          ≤⟨ Is-morphism.tr-monotone m G.tr-·-tr-Σ-≤ ⟩
      tr₁ (tr₂ (p M₁.· q))              ∎
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  module M₃ = Modality 𝕄₃
  module F  = Is-Σ-morphism f
  module G  = Is-Σ-morphism g
  open Definition.Modality.Properties 𝕄₃
  open Tools.Reasoning.PartialOrder ≤-poset

-- Composition preserves Is-Σ-order-embedding given a certain
-- assumption.

Is-Σ-order-embedding-∘ :
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-Σ-order-embedding 𝕄₂ 𝕄₃ tr₁ tr-Σ₁ →
  Is-Σ-order-embedding 𝕄₁ 𝕄₂ tr₂ tr-Σ₂ →
  Is-Σ-order-embedding 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Is-Σ-order-embedding-∘
  {𝕄₃ = 𝕄₃} {tr₁ = tr₁} {tr-Σ₁ = tr-Σ₁} {tr₂ = tr₂} {tr-Σ₂ = tr-Σ₂}
  m f g = record
  { tr-Σ-morphism =
      Is-Σ-morphism-∘ m F.tr-Σ-morphism G.tr-Σ-morphism
  ; tr-≤-tr-Σ-→ = λ {p = _} {q = _} {r = r} tr-p≤tr-q·r →
      case F.tr-≤-tr-Σ-→ tr-p≤tr-q·r of
        λ (r′ , tr-r′≤r , tr-p≤tr-q·r′) →
      case G.tr-≤-tr-Σ-→ tr-p≤tr-q·r′ of
        λ (r″ , tr-r″≤r′ , p≤q·r″) →
        r″
      , (begin
           tr₁ (tr₂ r″)  ≤⟨ Is-morphism.tr-monotone m tr-r″≤r′ ⟩
           tr₁ r′        ≤⟨ tr-r′≤r ⟩
           r             ∎)
      , p≤q·r″
  }
  where
  module F = Is-Σ-order-embedding f
  module G = Is-Σ-order-embedding g
  open Definition.Modality.Properties 𝕄₃
  open Tools.Reasoning.PartialOrder ≤-poset

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
-- for the first components of Σ-types.

erasure→zero-one-many-Σ : Erasure → Zero-one-many 𝟙≤𝟘
erasure→zero-one-many-Σ = λ where
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
-- for the first components of Σ-types.

affine→linear-or-affine-Σ : Affine → Linear-or-affine
affine→linear-or-affine-Σ = λ where
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

affine→linearity-Σ : Affine → Linearity
affine→linearity-Σ =
  linear-or-affine→linearity ∘→ affine→linear-or-affine-Σ

-- A translation from Linearity to Affine.

linearity→affine : Linearity → Affine
linearity→affine =
  linear-or-affine→affine ∘→ linearity→linear-or-affine

------------------------------------------------------------------------
-- Morphisms and order embeddings

-- The function unit→erasure is an order embedding from a unit
-- modality to an erasure modality.

unit⇨erasure :
  Is-order-embedding UnitModality (ErasureModality rs) unit→erasure
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
  ¬ T (Mode-restrictions.𝟘ᵐ-allowed rs) →
  Is-morphism (ErasureModality rs) UnitModality erasure→unit
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
  ¬ Is-order-embedding (ErasureModality rs) UnitModality erasure→unit
¬erasure⇨unit m =
  case Is-order-embedding.tr-injective m {p = 𝟘} {q = ω} refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a zero-one-many-greatest modality, given that
-- either both modalities allow 𝟘ᵐ, or none of them do. The
-- zero-one-many-greatest modality can be defined with either 𝟙 ≤ 𝟘 or
-- 𝟙 ≰ 𝟘.

erasure⇨zero-one-many :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-order-embedding
    (ErasureModality rs₁)
    (zero-one-many-greatest 𝟙≤𝟘 rs₂)
    erasure→zero-one-many
erasure⇨zero-one-many {rs₂ = rs₂} {𝟙≤𝟘 = 𝟙≤𝟘} refl = λ where
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
  open Definition.Modality.Properties (zero-one-many-greatest 𝟙≤𝟘 rs₂)
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
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-morphism (zero-one-many-greatest 𝟙≤𝟘 rs₁) (ErasureModality rs₂)
    zero-one-many→erasure
zero-one-many⇨erasure {rs₂ = rs₂} {𝟙≤𝟘 = 𝟙≤𝟘} refl = λ where
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
  open Definition.Modality.Properties (ErasureModality rs₂)

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
      (zero-one-many-greatest 𝟙≤𝟘 rs₁)
      (ErasureModality rs₂)
      zero-one-many→erasure
¬zero-one-many⇨erasure m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ω} refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a linear types modality, given that either both
-- modalities allow 𝟘ᵐ, or none of them do.

erasure⇨linearity :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-order-embedding (ErasureModality rs₁) (linearityModality rs₂)
    erasure→zero-one-many
erasure⇨linearity = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from a linear
-- types modality to an erasure modality, given that either both
-- modalities allow 𝟘ᵐ, or none of them do.

linearity⇨erasure :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-morphism (linearityModality rs₁) (ErasureModality rs₂)
    zero-one-many→erasure
linearity⇨erasure = zero-one-many⇨erasure

-- The function zero-one-many→erasure is not an order embedding from a
-- linear types modality to an erasure modality.

¬linearity⇨erasure :
  ¬ Is-order-embedding (linearityModality rs₁) (ErasureModality rs₂)
      zero-one-many→erasure
¬linearity⇨erasure = ¬zero-one-many⇨erasure

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to an affine types modality, given that either
-- both modalities allow 𝟘ᵐ, or none of them do.

erasure⇨affine :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-order-embedding (ErasureModality rs₁) (affineModality rs₂)
    erasure→zero-one-many
erasure⇨affine = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from an affine
-- types modality to an erasure modality, given that either both
-- modalities allow 𝟘ᵐ, or none of them do.

affine⇨erasure :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-morphism (affineModality rs₁) (ErasureModality rs₂)
    zero-one-many→erasure
affine⇨erasure = zero-one-many⇨erasure

-- The function zero-one-many→erasure is not an order embedding from
-- an affine types modality to an erasure modality.

¬affine⇨erasure :
  ¬ Is-order-embedding (affineModality rs₁) (ErasureModality rs₂)
      zero-one-many→erasure
¬affine⇨erasure = ¬zero-one-many⇨erasure

-- The function linearity→linear-or-affine is an order embedding from
-- a linear types modality to a linear or affine types modality, given
-- that either both modalities allow 𝟘ᵐ, or none of them do.

linearity⇨linear-or-affine :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-order-embedding (linearityModality rs₁) (linear-or-affine rs₂)
    linearity→linear-or-affine
linearity⇨linear-or-affine {rs₂ = rs₂} refl = λ where
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
  open Definition.Modality.Properties (linear-or-affine rs₂)

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
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-morphism (linear-or-affine rs₁) (linearityModality rs₂)
    linear-or-affine→linearity
linear-or-affine⇨linearity {rs₂ = rs₂} refl = λ where
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
  open Definition.Modality.Properties (linearityModality rs₂)

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
  ¬ Is-order-embedding (linear-or-affine rs₁) (linearityModality rs₂)
      linear-or-affine→linearity
¬linear-or-affine⇨linearity m =
  case Is-order-embedding.tr-injective m {p = ≤𝟙} {q = ≤ω} refl of λ ()

-- The function affine→linear-or-affine is an order embedding from an
-- affine types modality to a linear or affine types modality, given
-- that either both modalities allow 𝟘ᵐ, or none of them do.

affine⇨linear-or-affine :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-order-embedding (affineModality rs₁) (linear-or-affine rs₂)
    affine→linear-or-affine
affine⇨linear-or-affine {rs₂ = rs₂} refl = λ where
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
  open Definition.Modality.Properties (linear-or-affine rs₂)

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
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-morphism (linear-or-affine rs₁) (affineModality rs₂)
    linear-or-affine→affine
linear-or-affine⇨affine {rs₂ = rs₂} refl = λ where
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
  open Definition.Modality.Properties (affineModality rs₂)

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
  ¬ Is-order-embedding (linear-or-affine rs₁) (affineModality rs₂)
      linear-or-affine→affine
¬linear-or-affine⇨affine m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ≤𝟙} refl of λ ()

-- The function affine→linearity is a morphism from an affine types
-- modality to a linear types modality, given that either both
-- modalities allow 𝟘ᵐ, or none of them do.

affine⇨linearity :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-morphism (affineModality rs₁) (linearityModality rs₂)
    affine→linearity
affine⇨linearity {rs₂ = rs₂} refl = λ where
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
  open Definition.Modality.Properties (linearityModality rs₂)

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
  ¬ Is-order-embedding (affineModality rs₁) (linearityModality rs₂)
      affine→linearity
¬affine⇨linearity m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ω} refl of λ ()

-- The function linearity→affine is a morphism from a linear types
-- modality to an affine types modality, given that either both
-- modalities allow 𝟘ᵐ, or none of them do.

linearity⇨affine :
  𝟘ᵐ-allowed rs₁ ≡ 𝟘ᵐ-allowed rs₂ →
  Is-morphism (linearityModality rs₁) (affineModality rs₂)
    linearity→affine
linearity⇨affine {rs₂ = rs₂} refl = λ where
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
  open Definition.Modality.Properties (affineModality rs₂)

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
  ¬ Is-order-embedding (linearityModality rs₁) (affineModality rs₂)
      linearity→affine
¬linearity⇨affine m =
  case Is-order-embedding.tr-order-reflecting m {p = 𝟙} {q = 𝟘} refl of
    λ ()

------------------------------------------------------------------------
-- Σ-morphisms and order embeddings for Σ

-- The function erasure→zero-one-many-Σ is an order embedding for Σ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- a zero-one-many-greatest modality, given that if the second
-- modality allows 𝟘ᵐ, then the first also does this. The
-- zero-one-many-greatest modality can be defined with either 𝟙 ≤ 𝟘 or
-- 𝟙 ≰ 𝟘.

erasure⇨zero-one-many-Σ :
  (T (𝟘ᵐ-allowed rs₂) → T (𝟘ᵐ-allowed rs₁)) →
  Is-Σ-order-embedding
    (ErasureModality rs₁)
    (zero-one-many-greatest 𝟙≤𝟘 rs₂)
    erasure→zero-one-many
    erasure→zero-one-many-Σ
erasure⇨zero-one-many-Σ {𝟙≤𝟘 = 𝟙≤𝟘} ok₂₁ = record
  { tr-Σ-morphism = record
    { tr-≤-tr-Σ = λ where
        {p = 𝟘} → refl
        {p = ω} → refl
    ; tr-Σ-≡-𝟘-→ = λ where
        {p = 𝟘} ok₂ _ → ok₂₁ ok₂ , refl
    ; tr-Σ-≤-𝟙 = λ where
        {p = ω} _ → refl
    ; tr-·-tr-Σ-≤ = λ where
        {p = 𝟘} {q = _} → refl
        {p = ω} {q = 𝟘} → refl
        {p = ω} {q = ω} → refl
    }
  ; tr-≤-tr-Σ-→ = λ where
      {p = 𝟘} {q = 𝟘}         _     → ω , refl , refl
      {p = 𝟘} {q = ω} {r = 𝟘} _     → 𝟘 , refl , refl
      {p = 𝟘} {q = ω} {r = 𝟙} 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
      {p = ω}                 _     → ω , refl , refl
  }
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘

-- The function erasure→zero-one-many-Σ is an order embedding for Σ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- a linear types modality, given that if the second modality allows
-- 𝟘ᵐ, then the first also does this.

erasure⇨linearity-Σ :
  (T (𝟘ᵐ-allowed rs₂) → T (𝟘ᵐ-allowed rs₁)) →
  Is-Σ-order-embedding (ErasureModality rs₁) (linearityModality rs₂)
    erasure→zero-one-many erasure→zero-one-many-Σ
erasure⇨linearity-Σ = erasure⇨zero-one-many-Σ

-- The function erasure→zero-one-many-Σ is not monotone with respect
-- to the erasure and linear types orderings.

erasure⇨linearity-Σ-not-monotone :
  ¬ (∀ {p q} →
     p E.≤ q →
     erasure→zero-one-many-Σ p L.≤ erasure→zero-one-many-Σ q)
erasure⇨linearity-Σ-not-monotone mono =
  case mono {p = ω} {q = 𝟘} refl of λ ()

-- The function erasure→zero-one-many-Σ is an order embedding for Σ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- an affine types modality, given that if the second modality allows
-- 𝟘ᵐ, then the first also does this.

erasure⇨affine-Σ :
  (T (𝟘ᵐ-allowed rs₂) → T (𝟘ᵐ-allowed rs₁)) →
  Is-Σ-order-embedding (ErasureModality rs₁) (affineModality rs₂)
    erasure→zero-one-many erasure→zero-one-many-Σ
erasure⇨affine-Σ = erasure⇨zero-one-many-Σ

-- The function affine→linear-or-affine-Σ is an order embedding for Σ
-- (with respect to affine→linear-or-affine) from an affine types
-- modality to a linear or affine types modality, given that if the
-- second modality allows 𝟘ᵐ, then the first also does this.

affine⇨linear-or-affine-Σ :
  (T (𝟘ᵐ-allowed rs₂) → T (𝟘ᵐ-allowed rs₁)) →
  Is-Σ-order-embedding (affineModality rs₁) (linear-or-affine rs₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
affine⇨linear-or-affine-Σ ok₂₁ = record
  { tr-Σ-morphism = record
    { tr-≤-tr-Σ = λ where
        {p = 𝟘} → refl
        {p = 𝟙} → refl
        {p = ω} → refl
    ; tr-Σ-≡-𝟘-→ = λ where
        {p = 𝟘} ok₂ _ → ok₂₁ ok₂ , refl
    ; tr-Σ-≤-𝟙 = λ where
        {p = 𝟙} _ → refl
        {p = ω} _ → refl
    ; tr-·-tr-Σ-≤ = λ where
        {p = 𝟘} {q = _} → refl
        {p = 𝟙} {q = 𝟘} → refl
        {p = 𝟙} {q = 𝟙} → refl
        {p = 𝟙} {q = ω} → refl
        {p = ω} {q = 𝟘} → refl
        {p = ω} {q = 𝟙} → refl
        {p = ω} {q = ω} → refl
    }
  ; tr-≤-tr-Σ-→ = λ where
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

-- The function affine→linear-or-affine-Σ is not monotone with respect
-- to the affine types and linear or affine types orderings.

affine→linear-or-affine-Σ-not-monotone :
  ¬ (∀ {p q} →
     p A.≤ q →
     affine→linear-or-affine-Σ p LA.≤ affine→linear-or-affine-Σ q)
affine→linear-or-affine-Σ-not-monotone mono =
  case mono {p = 𝟙} {q = 𝟘} refl of λ ()

-- There is a function tr-Σ that is a Σ-morphism and an order
-- embedding for Σ for two modalities (with respect to a function that
-- is an order embedding for those modalities), but neither a morphism
-- nor an order embedding for those modalities.

Σ-order-embedding-but-not-order-embedding :
  ∃₂ λ (M₁ M₂ : Set) →
  ∃₂ λ (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂) →
  ∃₂ λ (tr tr-Σ : M₁ → M₂) →
  Is-order-embedding 𝕄₁ 𝕄₂ tr ×
  Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ ×
  Is-Σ-order-embedding 𝕄₁ 𝕄₂ tr tr-Σ ×
  ¬ Is-morphism 𝕄₁ 𝕄₂ tr-Σ ×
  ¬ Is-order-embedding 𝕄₁ 𝕄₂ tr-Σ
Σ-order-embedding-but-not-order-embedding =
    Affine , Linear-or-affine
  , affineModality (𝟘ᵐ-allowed-if true)
  , linear-or-affine (𝟘ᵐ-allowed-if true)
  , affine→linear-or-affine , affine→linear-or-affine-Σ
  , affine⇨linear-or-affine refl
  , Is-Σ-order-embedding.tr-Σ-morphism (affine⇨linear-or-affine-Σ _)
  , affine⇨linear-or-affine-Σ _
  , affine→linear-or-affine-Σ-not-monotone ∘→ Is-morphism.tr-monotone
  , affine→linear-or-affine-Σ-not-monotone ∘→
    Is-order-embedding.tr-monotone

-- The function affine→linearity-Σ is a Σ-morphism (with respect to
-- affine→linearity) from an affine types modality to a linear types
-- modality, given that if the second modality allows 𝟘ᵐ, then the
-- first also does this.

affine⇨linearity-Σ :
  (T (𝟘ᵐ-allowed rs₂) → T (𝟘ᵐ-allowed rs₁)) →
  Is-Σ-morphism (affineModality rs₁) (linearityModality rs₂)
    affine→linearity affine→linearity-Σ
affine⇨linearity-Σ ok₂₁ = record
  { tr-≤-tr-Σ = λ where
      {p = 𝟘} → refl
      {p = 𝟙} → refl
      {p = ω} → refl
  ; tr-Σ-≡-𝟘-→ = λ where
      {p = 𝟘} ok₂ _ → ok₂₁ ok₂ , refl
  ; tr-Σ-≤-𝟙 = λ where
      {p = 𝟙} _ → refl
      {p = ω} _ → refl
  ; tr-·-tr-Σ-≤ = λ where
      {p = 𝟘} {q = _} → refl
      {p = 𝟙} {q = 𝟘} → refl
      {p = 𝟙} {q = 𝟙} → refl
      {p = 𝟙} {q = ω} → refl
      {p = ω} {q = 𝟘} → refl
      {p = ω} {q = 𝟙} → refl
      {p = ω} {q = ω} → refl
  }

-- The function affine→linearity-Σ is not monotone with respect to the
-- affine types and linear types orderings.

affine→linearity-Σ-not-monotone :
  ¬ (∀ {p q} →
     p A.≤ q →
     affine→linearity-Σ p L.≤ affine→linearity-Σ q)
affine→linearity-Σ-not-monotone mono =
  case mono {p = 𝟙} {q = 𝟘} refl of λ ()

-- The function affine→linearity-Σ is not an order embedding for Σ
-- (with respect to affine→linearity) from an affine types modality to
-- a linear types modality.

¬affine⇨linearity-Σ :
  ¬ Is-Σ-order-embedding (affineModality rs₁) (linearityModality rs₂)
      affine→linearity affine→linearity-Σ
¬affine⇨linearity-Σ m =
  case
    Is-Σ-order-embedding.tr-≤-tr-Σ-→ m {p = 𝟙} {q = ω} {r = ω} refl
  of λ where
    (𝟘 , () , _)
    (𝟙 , _  , ())
    (ω , _  , ())
