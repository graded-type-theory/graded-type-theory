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

open import Definition.Mode

open import Definition.Untyped.NotParametrised using (BinderMode)

private variable
  a₁ a₂      : Level
  𝟙≤𝟘 ok     : Bool
  not-ok     : ¬ T _
  r r₁ r₂ r₃ : Restrictions _
  M₁ M₂      : Set _
  𝕄 𝕄₁ 𝕄₂ 𝕄₃ : Modality _
  b          : BinderMode
  tr tr₁ tr₂ : M₁ → M₂

------------------------------------------------------------------------
-- Morphisms

-- The definitions in this section have been tailored mainly to make
-- it possible to prove the theorems in
-- Definition.Modality.Usage.QuantityTranslation for certain
-- translations between certain modalities. Perhaps other definitions
-- are more suitable for other applications.

-- The property of being a restrictions morphism.

record Is-restrictions-morphism
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (r₁ : Restrictions M₁) (r₂ : Restrictions M₂)
         (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Restrictions r₁
    module R₂ = Restrictions r₂

  field
    -- If 𝟘ᵐ is allowed in the source modality, then it is allowed in
    -- the target modality.
    𝟘ᵐ-in-second-if-in-first : T R₁.𝟘ᵐ-allowed → T R₂.𝟘ᵐ-allowed

    -- The function tr respects the Binder property.
    tr-Binder : ∀ {p q} → R₁.Binder b p q → R₂.Binder b (tr p) (tr q)

    -- The function tr respects the Prodrec property.
    tr-Prodrec :
      ∀ {p q r} → R₁.Prodrec p q r → R₂.Prodrec (tr p) (tr q) (tr r)

-- The property of being a Modality morphism.

record Is-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module M₁ = Modality 𝕄₁
    open module M₂ = Modality 𝕄₂ using (_≤_; _<_)

  field
    -- The translation tr is a restrictions morphism.
    tr-is-restrictions-morphism :
      Is-restrictions-morphism M₁.restrictions M₂.restrictions tr

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

  open Is-restrictions-morphism tr-is-restrictions-morphism public

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

-- The property of reflecting restrictions.

record Is-reflecting-restrictions
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (r₁ : Restrictions M₁) (r₂ : Restrictions M₂)
         (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  private
    module R₁ = Restrictions r₁
    module R₂ = Restrictions r₂

  field
    -- The function tr reflects the Binder property.
    tr-reflects-Binder :
      ∀ {p q} → R₂.Binder b (tr p) (tr q) → R₁.Binder b p q

    -- The function tr reflects the Prodrec property.
    tr-reflects-Prodrec :
      ∀ {p q r} → R₂.Prodrec (tr p) (tr q) (tr r) → R₁.Prodrec p q r

-- The property of being a reflecting restrictions-morphism.

record Is-reflecting-restrictions-morphism
         {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
         (r₁ : Restrictions M₁) (r₂ : Restrictions M₂)
         (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  field
    tr-is-restrictions-morphism : Is-restrictions-morphism   r₁ r₂ tr
    tr-reflects-restrictions    : Is-reflecting-restrictions r₁ r₂ tr

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

    -- The translation tr reflects restrictions.
    tr-reflects-restrictions :
      Is-reflecting-restrictions M₁.restrictions M₂.restrictions tr

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
  open Is-reflecting-restrictions tr-reflects-restrictions public

  -- The translation is injective.

  tr-injective : ∀ {p q} → tr p ≡ tr q → p ≡ q
  tr-injective tr-p≡tr-q = P₁.≤-antisym
    (tr-order-reflecting (P₂.≤-reflexive tr-p≡tr-q))
    (tr-order-reflecting (P₂.≤-reflexive (sym tr-p≡tr-q)))
    where
    module P₁ = Definition.Modality.Properties 𝕄₁
    module P₂ = Definition.Modality.Properties 𝕄₂

------------------------------------------------------------------------
-- Identity and composition

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
    .tr-reflects-restrictions → λ where
      .tr-reflects-Binder  → idᶠ
      .tr-reflects-Prodrec → idᶠ
    .tr-morphism → λ where
      .tr-<-𝟘 not-ok ok            → ⊥-elim (not-ok ok)
      .tr-𝟙                        → ≤-refl
      .tr-𝟘-≤                      → ≤-refl
      .tr-≡-𝟘-⇔ _                  → idᶠ , idᶠ
      .tr-+                        → ≤-refl
      .tr-·                        → refl
      .tr-∧                        → ≤-refl
      .tr-⊛                        → ≤-refl
      .tr-is-restrictions-morphism → λ where
        .𝟘ᵐ-in-second-if-in-first → idᶠ
        .tr-Binder                → idᶠ
        .tr-Prodrec               → idᶠ
  where
  open Definition.Modality.Properties 𝕄
  open Is-restrictions-morphism
  open Is-morphism
  open Is-order-embedding
  open Is-reflecting-restrictions

-- Composition preserves Is-restrictions-morphism.

Is-restrictions-morphism-∘ :
  Is-restrictions-morphism r₂ r₃ tr₁ →
  Is-restrictions-morphism r₁ r₂ tr₂ →
  Is-restrictions-morphism r₁ r₃ (tr₁ ∘→ tr₂)
Is-restrictions-morphism-∘ m₁ m₂ = λ where
    .Is-restrictions-morphism.𝟘ᵐ-in-second-if-in-first →
      M₁.𝟘ᵐ-in-second-if-in-first ∘→ M₂.𝟘ᵐ-in-second-if-in-first
    .Is-restrictions-morphism.tr-Binder →
      M₁.tr-Binder ∘→ M₂.tr-Binder
    .Is-restrictions-morphism.tr-Prodrec →
      M₁.tr-Prodrec ∘→ M₂.tr-Prodrec
  where
  module M₁ = Is-restrictions-morphism m₁
  module M₂ = Is-restrictions-morphism m₂

-- Composition preserves Is-morphism.

Is-morphism-∘ :
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-morphism 𝕄₁ 𝕄₂ tr₂ →
  Is-morphism 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂)
Is-morphism-∘
  {𝕄₂ = 𝕄₂} {𝕄₃ = 𝕄₃} {tr₁ = tr₁} {𝕄₁ = 𝕄₁} {tr₂ = tr₂} f g = λ where
    .Is-morphism.tr-is-restrictions-morphism →
      Is-restrictions-morphism-∘
        F.tr-is-restrictions-morphism
        G.tr-is-restrictions-morphism
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
  module Mo₂ = Definition.Mode 𝕄₂
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module M₃  = Modality 𝕄₃
  module F   = Is-morphism f
  module G   = Is-morphism g
  open Definition.Modality.Properties 𝕄₃
  module R = Tools.Reasoning.PartialOrder ≤-poset

-- Composition preserves Is-reflecting-restrictions.

Is-reflecting-restrictions-∘ :
  Is-reflecting-restrictions r₂ r₃ tr₁ →
  Is-reflecting-restrictions r₁ r₂ tr₂ →
  Is-reflecting-restrictions r₁ r₃ (tr₁ ∘→ tr₂)
Is-reflecting-restrictions-∘ f g = λ where
    .Is-reflecting-restrictions.tr-reflects-Binder →
      G.tr-reflects-Binder ∘→ F.tr-reflects-Binder
    .Is-reflecting-restrictions.tr-reflects-Prodrec →
      G.tr-reflects-Prodrec ∘→ F.tr-reflects-Prodrec
  where
  module F = Is-reflecting-restrictions f
  module G = Is-reflecting-restrictions g

-- Composition preserves Is-reflecting-restrictions-morphism.

Is-reflecting-restrictions-morphism-∘ :
  Is-reflecting-restrictions-morphism r₂ r₃ tr₁ →
  Is-reflecting-restrictions-morphism r₁ r₂ tr₂ →
  Is-reflecting-restrictions-morphism r₁ r₃ (tr₁ ∘→ tr₂)
Is-reflecting-restrictions-morphism-∘ f g = λ where
    .Is-reflecting-restrictions-morphism.tr-is-restrictions-morphism →
      Is-restrictions-morphism-∘ F.tr-is-restrictions-morphism
        G.tr-is-restrictions-morphism
    .Is-reflecting-restrictions-morphism.tr-reflects-restrictions →
      Is-reflecting-restrictions-∘
        F.tr-reflects-restrictions G.tr-reflects-restrictions
  where
  module F = Is-reflecting-restrictions-morphism f
  module G = Is-reflecting-restrictions-morphism g

-- Composition preserves Is-order-embedding.

Is-order-embedding-∘ :
  Is-order-embedding 𝕄₂ 𝕄₃ tr₁ →
  Is-order-embedding 𝕄₁ 𝕄₂ tr₂ →
  Is-order-embedding 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂)
Is-order-embedding-∘
  {𝕄₂ = 𝕄₂} {𝕄₃ = 𝕄₃} {tr₁ = tr₁} {𝕄₁ = 𝕄₁} {tr₂ = tr₂} f g = λ where
    .Is-order-embedding.tr-morphism →
      Is-morphism-∘ F.tr-morphism G.tr-morphism
    .Is-order-embedding.tr-reflects-restrictions →
      Is-reflecting-restrictions-∘
        F.tr-reflects-restrictions G.tr-reflects-restrictions
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

-- A translation from Linearity to Affine.

linearity→affine : Linearity → Affine
linearity→affine =
  linear-or-affine→affine ∘→ linearity→linear-or-affine

------------------------------------------------------------------------
-- Restrictions morphisms and order embeddings

-- The identity function is a reflecting restrictions morphism from r
-- to r with 𝟘ᵐ-allowed equal to true.

⇨𝟘ᵐ-allowed :
  Is-reflecting-restrictions-morphism
    r (record r { 𝟘ᵐ-allowed = true }) idᶠ
⇨𝟘ᵐ-allowed = λ where
  .Is-reflecting-restrictions-morphism.tr-is-restrictions-morphism →
    λ where
      .Is-restrictions-morphism.𝟘ᵐ-in-second-if-in-first → _
      .Is-restrictions-morphism.tr-Binder                → idᶠ
      .Is-restrictions-morphism.tr-Prodrec               → idᶠ
  .Is-reflecting-restrictions-morphism.tr-reflects-restrictions →
    λ where
      .Is-reflecting-restrictions.tr-reflects-Binder  → idᶠ
      .Is-reflecting-restrictions.tr-reflects-Prodrec → idᶠ

-- Any function is a reflecting restrictions morphism from
-- 𝟘ᵐ-allowed-if M₁ ok to 𝟘ᵐ-allowed-if M₂ ok.

𝟘ᵐ-allowed-if⇨𝟘ᵐ-allowed-if :
  Is-reflecting-restrictions-morphism
    (𝟘ᵐ-allowed-if M₁ ok) (𝟘ᵐ-allowed-if M₂ ok) tr
𝟘ᵐ-allowed-if⇨𝟘ᵐ-allowed-if = λ where
  .Is-reflecting-restrictions-morphism.tr-is-restrictions-morphism →
    λ where
      .Is-restrictions-morphism.𝟘ᵐ-in-second-if-in-first → idᶠ
      .Is-restrictions-morphism.tr-Binder                → _
      .Is-restrictions-morphism.tr-Prodrec               → _
  .Is-reflecting-restrictions-morphism.tr-reflects-restrictions →
    λ where
      .Is-reflecting-restrictions.tr-reflects-Binder  → _
      .Is-reflecting-restrictions.tr-reflects-Prodrec → _

-- If tr is a restrictions morphism from r₁ to r₂, then tr is also a
-- restrictions morphism from equal-binder-quantities M₁ r₁ to
-- equal-binder-quantities M₂ r₂.

Is-restrictions-morphism-equal-binder-quantities :
  Is-restrictions-morphism r₁ r₂ tr →
  Is-restrictions-morphism
    (equal-binder-quantities M₁ r₁) (equal-binder-quantities M₂ r₂) tr
Is-restrictions-morphism-equal-binder-quantities {tr = tr} m = λ where
    .𝟘ᵐ-in-second-if-in-first → M.𝟘ᵐ-in-second-if-in-first
    .tr-Binder (b , eq)       → M.tr-Binder b , cong tr eq
    .tr-Prodrec               → M.tr-Prodrec
  where
  module M = Is-restrictions-morphism m
  open Is-restrictions-morphism

-- If tr is injective and satisfies Is-reflecting-restrictions r₁ r₂,
-- then it also satisfies
-- Is-reflecting-restrictions (equal-binder-quantities M₁ r₁)
-- (equal-binder-quantities M₂ r₂).

Is-reflecting-restrictions-equal-binder-quantities :
  (∀ {p q} → tr p ≡ tr q → p ≡ q) →
  Is-reflecting-restrictions r₁ r₂ tr →
  Is-reflecting-restrictions
    (equal-binder-quantities M₁ r₁) (equal-binder-quantities M₂ r₂) tr
Is-reflecting-restrictions-equal-binder-quantities inj r = λ where
    .tr-reflects-Binder (b , eq) → R.tr-reflects-Binder b , inj eq
    .tr-reflects-Prodrec         → R.tr-reflects-Prodrec
  where
  module R = Is-reflecting-restrictions r
  open Is-reflecting-restrictions

-- If tr is a reflecting restrictions morphism from r₁ to r₂ which is
-- injective, then tr is also a reflecting restrictions morphism from
-- equal-binder-quantities M₁ r₁ to equal-binder-quantities M₂ r₂.

Is-reflecting-restrictions-morphism-equal-binder-quantities :
  (∀ {p q} → tr p ≡ tr q → p ≡ q) →
  Is-reflecting-restrictions-morphism r₁ r₂ tr →
  Is-reflecting-restrictions-morphism
    (equal-binder-quantities M₁ r₁) (equal-binder-quantities M₂ r₂) tr
Is-reflecting-restrictions-morphism-equal-binder-quantities inj m =
  λ where
    .tr-is-restrictions-morphism →
      Is-restrictions-morphism-equal-binder-quantities
        M.tr-is-restrictions-morphism
    .tr-reflects-restrictions →
      Is-reflecting-restrictions-equal-binder-quantities
        inj M.tr-reflects-restrictions
  where
  module M = Is-reflecting-restrictions-morphism m
  open Is-reflecting-restrictions-morphism

------------------------------------------------------------------------
-- Morphisms and order embeddings

-- The function unit→erasure is an order embedding from a unit
-- modality to an erasure modality, given that the restrictions r₁ and
-- r₂ of the modalities satisfy the following properties: unit→erasure
-- must be a reflecting restrictions-morphism from r₁ to r₂, and r₁
-- must not allow 𝟘ᵐ.

unit⇨erasure :
  Is-reflecting-restrictions-morphism r₁ r₂ unit→erasure →
  (not-ok : ¬ T (Restrictions.𝟘ᵐ-allowed r₁)) →
  Is-order-embedding (UnitModality r₁ not-ok) (ErasureModality r₂)
    unit→erasure
unit⇨erasure m not-ok = λ where
    .tr-order-reflecting _    → refl
    .trivial _ _              → refl
    .trivial-⊎-tr-𝟘           → inj₁ refl
    .tr-≤                     → _ , refl
    .tr-≤-𝟙 _                 → refl
    .tr-≤-+ _                 → _ , _ , refl , refl , refl
    .tr-≤-· _                 → _ , refl , refl
    .tr-≤-∧ _                 → _ , _ , refl , refl , refl
    .tr-≤-⊛ _                 → _ , _ , _ , refl , refl , refl , refl
    .tr-reflects-restrictions → R.tr-reflects-restrictions
    .tr-morphism → λ where
      .tr-𝟘-≤                      → refl
      .tr-≡-𝟘-⇔ ok                 → ⊥-elim (not-ok ok)
      .tr-<-𝟘 _ _                  → refl , λ ()
      .tr-𝟙                        → refl
      .tr-+                        → refl
      .tr-·                        → refl
      .tr-∧                        → refl
      .tr-⊛                        → refl
      .tr-is-restrictions-morphism → R.tr-is-restrictions-morphism
  where
  module R = Is-reflecting-restrictions-morphism m
  open Is-morphism
  open Is-order-embedding

-- The function erasure→unit is a morphism from a unit modality to an
-- erasure modality, given that the restrictions r₁ and r₂ of the
-- modalities satisfy the following properties: erasure→unit must be a
-- restrictions-morphism from r₁ to r₂, and neither r₁ nor r₂ must
-- allow 𝟘ᵐ.

erasure⇨unit :
  Is-restrictions-morphism r₁ r₂ erasure→unit →
  ¬ T (Restrictions.𝟘ᵐ-allowed r₁) →
  (not-ok : ¬ T (Restrictions.𝟘ᵐ-allowed r₂)) →
  Is-morphism (ErasureModality r₁) (UnitModality r₂ not-ok) erasure→unit
erasure⇨unit m not-ok₁ not-ok₂ = λ where
    .tr-𝟘-≤                      → refl
    .tr-≡-𝟘-⇔ ok₁                → ⊥-elim (not-ok₁ ok₁)
    .tr-<-𝟘 _ ok₂                → ⊥-elim (not-ok₂ ok₂)
    .tr-𝟙                        → refl
    .tr-+                        → refl
    .tr-·                        → refl
    .tr-∧                        → refl
    .tr-⊛                        → refl
    .tr-is-restrictions-morphism → m
  where
  open Is-morphism

-- The function erasure→unit is not an order embedding from an erasure
-- modality to a unit modality.

¬erasure⇨unit :
  ¬ Is-order-embedding (ErasureModality r₁) (UnitModality r₂ not-ok)
      erasure→unit
¬erasure⇨unit m =
  case Is-order-embedding.tr-injective m {p = 𝟘} {q = ω} refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a zero-one-many-greatest modality, given that
-- the restrictions r₁ and r₂ of the modalities satisfy the following
-- properties: erasure→zero-one-many must be a reflecting
-- restrictions-morphism from r₁ to r₂, and either both of r₁ and r₂
-- allow 𝟘ᵐ, or none of them do. The zero-one-many-greatest modality
-- can be defined with either 𝟙 ≤ 𝟘 or 𝟙 ≰ 𝟘.

erasure⇨zero-one-many :
  Is-reflecting-restrictions-morphism r₁ r₂ erasure→zero-one-many →
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-order-embedding
    (ErasureModality r₁)
    (zero-one-many-greatest 𝟙≤𝟘 r₂)
    erasure→zero-one-many
erasure⇨zero-one-many {𝟙≤𝟘 = 𝟙≤𝟘} {r₂ = r₂} m refl = λ where
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
    .Is-order-embedding.tr-reflects-restrictions →
      R.tr-reflects-restrictions
    .Is-order-embedding.tr-morphism → λ where
      .Is-morphism.tr-𝟘-≤               → refl
      .Is-morphism.tr-≡-𝟘-⇔ _           → tr-≡-𝟘 _ , λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok     → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                 → refl
      .Is-morphism.tr-+ {p = p}         → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-· {p = p}         → tr-· p _
      .Is-morphism.tr-∧ {p = p}         → ≤-reflexive (tr-∧ p _)
      .Is-morphism.tr-⊛ {p = p} {r = r} →
        ≤-reflexive (tr-⊛ p _ r)
      .Is-morphism.tr-is-restrictions-morphism →
        R.tr-is-restrictions-morphism
  where
  module R   = Is-reflecting-restrictions-morphism m
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
-- the restrictions r₁ and r₂ of the modalities satisfy the following
-- properties: zero-one-many→erasure must be a restrictions-morphism
-- from r₁ to r₂, and either both of r₁ and r₂ allow 𝟘ᵐ, or none of
-- them do. The zero-one-many-greatest modality can be defined with
-- either 𝟙 ≤ 𝟘 or 𝟙 ≰ 𝟘.

zero-one-many⇨erasure :
  Is-restrictions-morphism r₁ r₂ zero-one-many→erasure →
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (zero-one-many-greatest 𝟙≤𝟘 r₁) (ErasureModality r₂)
    zero-one-many→erasure
zero-one-many⇨erasure {𝟙≤𝟘 = 𝟙≤𝟘} {r₂ = r₂} m refl = λ where
    .Is-morphism.tr-𝟘-≤                      → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                  → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok            → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                        → refl
    .Is-morphism.tr-+ {p = p}                → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-· {p = p}                → tr-· p _
    .Is-morphism.tr-∧ {p = p}                → ≤-reflexive (tr-∧ p _)
    .Is-morphism.tr-⊛ {p = p} {r = r}        → ≤-reflexive (tr-⊛ p _ r)
    .Is-morphism.tr-is-restrictions-morphism → m
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
-- erasure modality to a linear types modality, given that the
-- restrictions r₁ and r₂ of the modalities satisfy the following
-- properties: erasure→zero-one-many must be a reflecting
-- restrictions-morphism from r₁ to r₂, and either both of r₁ and r₂
-- allow 𝟘ᵐ, or none of them do.

erasure⇨linearity :
  Is-reflecting-restrictions-morphism r₁ r₂ erasure→zero-one-many →
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-order-embedding (ErasureModality r₁) (linearityModality r₂)
    erasure→zero-one-many
erasure⇨linearity = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from a linear
-- types modality to an erasure modality, given that the restrictions
-- r₁ and r₂ of the modalities satisfy the following properties:
-- zero-one-many→erasure must be a restrictions-morphism from r₁ to
-- r₂, and either both of r₁ and r₂ allow 𝟘ᵐ, or none of them do.

linearity⇨erasure :
  Is-restrictions-morphism r₁ r₂ zero-one-many→erasure →
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
-- erasure modality to an affine types modality, given that the
-- restrictions r₁ and r₂ of the modalities satisfy the following
-- properties: erasure→zero-one-many must be a reflecting
-- restrictions-morphism from r₁ to r₂, and either both of r₁ and r₂
-- allow 𝟘ᵐ, or none of them do.

erasure⇨affine :
  Is-reflecting-restrictions-morphism r₁ r₂ erasure→zero-one-many →
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-order-embedding (ErasureModality r₁) (affineModality r₂)
    erasure→zero-one-many
erasure⇨affine = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from an affine
-- types modality to an erasure modality, given that the restrictions
-- r₁ and r₂ of the modalities satisfy the following properties:
-- zero-one-many→erasure must be a restrictions-morphism from r₁ to
-- r₂, and either both of r₁ and r₂ allow 𝟘ᵐ, or none of them do.

affine⇨erasure :
  Is-restrictions-morphism r₁ r₂ zero-one-many→erasure →
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
-- that the restrictions r₁ and r₂ of the modalities satisfy the
-- following properties: linearity→linear-or-affine must be a
-- reflecting restrictions-morphism from r₁ to r₂, and either both of
-- r₁ and r₂ allow 𝟘ᵐ, or none of them do.

linearity⇨linear-or-affine :
  Is-reflecting-restrictions-morphism r₁ r₂ linearity→linear-or-affine →
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-order-embedding (linearityModality r₁) (linear-or-affine r₂)
    linearity→linear-or-affine
linearity⇨linear-or-affine {r₂ = r₂} m refl = λ where
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
    .Is-order-embedding.tr-reflects-restrictions →
      R.tr-reflects-restrictions
    .Is-order-embedding.tr-morphism → λ where
      .Is-morphism.tr-𝟘-≤                      → refl
      .Is-morphism.tr-≡-𝟘-⇔ _                  →   tr-≡-𝟘 _ ,
                                                 λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok            → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                        → refl
      .Is-morphism.tr-+ {p = p}                → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-·                        → tr-· _ _
      .Is-morphism.tr-∧                        → tr-∧ _ _
      .Is-morphism.tr-⊛ {r = r}                → tr-⊛ _ _ r
      .Is-morphism.tr-is-restrictions-morphism →
        R.tr-is-restrictions-morphism
  where
  module R = Is-reflecting-restrictions-morphism m
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
-- or affine types modality to a linear types modality, given that the
-- restrictions r₁ and r₂ of the modalities satisfy the following
-- properties: linear-or-affine→linearity must be a
-- restrictions-morphism from r₁ to r₂, and either both of r₁ and r₂
-- allow 𝟘ᵐ, or none of them do.

linear-or-affine⇨linearity :
  Is-restrictions-morphism r₁ r₂ linear-or-affine→linearity →
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (linear-or-affine r₁) (linearityModality r₂)
    linear-or-affine→linearity
linear-or-affine⇨linearity {r₂ = r₂} m refl = λ where
    .Is-morphism.tr-𝟘-≤                      → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                  → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok            → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                        → refl
    .Is-morphism.tr-+ {p = p}                → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                        → tr-· _ _
    .Is-morphism.tr-∧                        → ≤-reflexive (tr-∧ _ _)
    .Is-morphism.tr-⊛ {r = r}                → ≤-reflexive (tr-⊛ _ _ r)
    .Is-morphism.tr-is-restrictions-morphism → m
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
-- that the restrictions r₁ and r₂ of the modalities satisfy the
-- following properties: affine→linear-or-affine must be a reflecting
-- restrictions-morphism from r₁ to r₂, and either both of r₁ and r₂
-- allow 𝟘ᵐ, or none of them do.

affine⇨linear-or-affine :
  Is-reflecting-restrictions-morphism r₁ r₂ affine→linear-or-affine →
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-order-embedding (affineModality r₁) (linear-or-affine r₂)
    affine→linear-or-affine
affine⇨linear-or-affine {r₂ = r₂} m refl = λ where
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
    .Is-order-embedding.tr-reflects-restrictions →
      R.tr-reflects-restrictions
    .Is-order-embedding.tr-morphism → λ where
      .Is-morphism.tr-𝟘-≤           → refl
      .Is-morphism.tr-≡-𝟘-⇔ _       → tr-≡-𝟘 _ , λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙             → refl
      .Is-morphism.tr-+ {p = p}     → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-·             → tr-· _ _
      .Is-morphism.tr-∧             → ≤-reflexive (tr-∧ _ _)
      .Is-morphism.tr-⊛ {r = r}     →
        ≤-reflexive (tr-⊛ _ _ r)
      .Is-morphism.tr-is-restrictions-morphism →
        R.tr-is-restrictions-morphism
  where
  module R = Is-reflecting-restrictions-morphism m
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
-- affine types modality to an affine types modality, given that the
-- restrictions r₁ and r₂ of the modalities satisfy the following
-- properties: linear-or-affine→affine must be a restrictions-morphism
-- from r₁ to r₂, and either both of r₁ and r₂ allow 𝟘ᵐ, or none of
-- them do.

linear-or-affine⇨affine :
  Is-restrictions-morphism r₁ r₂ linear-or-affine→affine →
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (linear-or-affine r₁) (affineModality r₂)
    linear-or-affine→affine
linear-or-affine⇨affine {r₂ = r₂} m refl = λ where
    .Is-morphism.tr-𝟘-≤                      → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                  → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok            → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                        → refl
    .Is-morphism.tr-+ {p = p}                → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                        → tr-· _ _
    .Is-morphism.tr-∧                        → ≤-reflexive (tr-∧ _ _)
    .Is-morphism.tr-⊛ {r = r}                → ≤-reflexive (tr-⊛ _ _ r)
    .Is-morphism.tr-is-restrictions-morphism → m
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
-- modality to a linear types modality, given that the restrictions r₁
-- and r₂ of the modalities satisfy the following properties:
-- affine→linearity must be a restrictions-morphism from r₁ to r₂, and
-- either both of r₁ and r₂ allow 𝟘ᵐ, or none of them do.

affine⇨linearity :
  Is-restrictions-morphism r₁ r₂ affine→linearity →
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (affineModality r₁) (linearityModality r₂)
    affine→linearity
affine⇨linearity {r₂ = r₂} m refl = λ where
    .Is-morphism.tr-𝟘-≤                      → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                  → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok            → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                        → refl
    .Is-morphism.tr-+ {p = p}                → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                        → tr-· _ _
    .Is-morphism.tr-∧ {p = p}                → ≤-reflexive (tr-∧ p _)
    .Is-morphism.tr-⊛ {r = r}                → ≤-reflexive (tr-⊛ _ _ r)
    .Is-morphism.tr-is-restrictions-morphism → m
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
-- modality to an affine types modality, given that the restrictions
-- r₁ and r₂ of the modalities satisfy the following properties:
-- linearity→affine must be a restrictions-morphism from r₁ to r₂, and
-- either both of r₁ and r₂ allow 𝟘ᵐ, or none of them do.

linearity⇨affine :
  Is-restrictions-morphism r₁ r₂ linearity→affine →
  Restrictions.𝟘ᵐ-allowed r₁ ≡ Restrictions.𝟘ᵐ-allowed r₂ →
  Is-morphism (linearityModality r₁) (affineModality r₂)
    linearity→affine
linearity⇨affine {r₂ = r₂} m refl = λ where
    .Is-morphism.tr-𝟘-≤                      → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                  → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok            → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                        → refl
    .Is-morphism.tr-+ {p = p}                → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                        → tr-· _ _
    .Is-morphism.tr-∧ {p = p}                → tr-∧ p _
    .Is-morphism.tr-⊛ {r = r}                → tr-⊛ _ _ r
    .Is-morphism.tr-is-restrictions-morphism → m
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
