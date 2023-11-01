------------------------------------------------------------------------
-- Modality morphisms
------------------------------------------------------------------------

module Graded.Modality.Morphism where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

open import Graded.Modality
open import Graded.Modality.Dedicated-nr
open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Modality.Nr-instances
import Graded.Modality.Properties

open import Graded.Mode as Mode hiding (module Mode)

private variable
  a₁ a₂                  : Level
  M M₁ M₂                : Set _
  𝕄 𝕄₁ 𝕄₂ 𝕄₃             : Modality _
  tr tr₁ tr₂ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q₁ q₂ q₃ q₄ r s      : M

------------------------------------------------------------------------
-- Morphisms

-- The definitions in this section have been tailored mainly to make
-- it possible to prove the theorems in
-- Graded.Usage.QuantityTranslation for certain
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

    -- If the source modality does not have a dedicated nr function
    -- and 𝟘ᵐ is allowed in the target modality or the target modality
    -- is trivial, then 𝟘ᵐ is allowed in the source modality or the
    -- source modality is trivial.
    𝟘ᵐ-in-first-if-in-second :
      ⦃ no-nr : No-dedicated-nr 𝕄₁ ⦄ →
      T M₂.𝟘ᵐ-allowed ⊎ M₂.Trivial → T M₁.𝟘ᵐ-allowed ⊎ M₁.Trivial

    -- If the source modality does not have a dedicated nr function
    -- and the target modality has a well-behaved zero or is trivial,
    -- then the source modality has a well-behaved zero or is trivial.
    𝟘-well-behaved-in-first-if-in-second :
      ⦃ no-nr : No-dedicated-nr 𝕄₁ ⦄ →
      Has-well-behaved-zero M₂ M₂.semiring-with-meet ⊎ M₂.Trivial →
      Has-well-behaved-zero M₁ M₁.semiring-with-meet ⊎ M₁.Trivial

    -- The source modality has a dedicated nr function if and only if
    -- the target modality also has one.
    nr-in-first-iff-in-second : Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂

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

    -- The translation commutes with nr up to _≤_.
    tr-nr :
      ∀ {p r z s n}
        ⦃ has-nr₁ : Dedicated-nr 𝕄₁ ⦄
        ⦃ has-nr₂ : Dedicated-nr 𝕄₂ ⦄ →
      tr (nr p r z s n) ≤ nr (tr p) (tr r) (tr z) (tr s) (tr n)

  -- If the source modality has a dedicated nr function, then the
  -- target modality also has one.

  nr-in-second-if-in-first :
    ⦃ has-nr : Dedicated-nr 𝕄₁ ⦄ →
    Dedicated-nr 𝕄₂
  nr-in-second-if-in-first ⦃ has-nr = n ⦄ =
    nr-in-first-iff-in-second .proj₁ n

  -- If the target modality has a dedicated nr function, then the
  -- source modality also has one.

  nr-in-first-if-in-second :
    ⦃ has-nr : Dedicated-nr 𝕄₂ ⦄ →
    Dedicated-nr 𝕄₁
  nr-in-first-if-in-second ⦃ has-nr = n ⦄ =
    nr-in-first-iff-in-second .proj₂ n

  -- The source modality does not have a dedicated nr function if and
  -- only if the target modality does not have one.

  no-nr-in-first-iff-in-second :
    No-dedicated-nr 𝕄₁ ⇔ No-dedicated-nr 𝕄₂
  no-nr-in-first-iff-in-second =
      (λ nr → no-dedicated-nr $ T-not⇔¬-T .proj₂
           (M₂.Nr-available  →⟨ Dedicated-nr.nr ∘→ nr-in-first-iff-in-second .proj₂ ∘→ dedicated-nr ⟩
            M₁.Nr-available  →⟨ No-dedicated-nr.no-nr nr ⟩
            ⊥                □))
    , (λ nr → no-dedicated-nr $ T-not⇔¬-T .proj₂
           (M₁.Nr-available  →⟨ Dedicated-nr.nr ∘→ nr-in-first-iff-in-second .proj₁ ∘→ dedicated-nr ⟩
            M₂.Nr-available  →⟨ No-dedicated-nr.no-nr nr ⟩
            ⊥                □))

  -- If the source modality does not have a dedicated nr function,
  -- then neither does the target modality.

  no-nr-in-second-if-in-first :
    ⦃ no-nr : No-dedicated-nr 𝕄₁ ⦄ →
    No-dedicated-nr 𝕄₂
  no-nr-in-second-if-in-first ⦃ no-nr = nn ⦄ =
    no-nr-in-first-iff-in-second .proj₁ nn

  -- If the target modality does not have a dedicated nr function,
  -- then neither does the source modality.

  no-nr-in-first-if-in-second :
    ⦃ no-nr : No-dedicated-nr 𝕄₂ ⦄ →
    No-dedicated-nr 𝕄₁
  no-nr-in-first-if-in-second ⦃ no-nr = nn ⦄ =
    no-nr-in-first-iff-in-second .proj₂ nn

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
    open Graded.Modality.Properties 𝕄₂
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
    trivial : ¬ T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed → M₁.Trivial

    -- Either the source modality is trivial, or the translation of 𝟘
    -- is equal to 𝟘.
    trivial-⊎-tr-𝟘 : M₁.Trivial ⊎ (tr M₁.𝟘 ≡ M₂.𝟘)

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

    -- A variant of the last properties above for nr.
    tr-≤-nr :
      ∀ {q p r z₁ s₁ n₁}
        ⦃ has-nr₁ : Dedicated-nr 𝕄₁ ⦄
        ⦃ has-nr₂ : Dedicated-nr 𝕄₂ ⦄ →
      tr q M₂.≤ nr (tr p) (tr r) z₁ s₁ n₁ →
      ∃₃ λ z₂ s₂ n₂ →
         tr z₂ M₂.≤ z₁ × tr s₂ M₂.≤ s₁ × tr n₂ M₂.≤ n₁ ×
         q M₁.≤ nr p r z₂ s₂ n₂

    -- A variant of the previous property for the alternative usage
    -- rule for natrec.
    tr-≤-no-nr :
      ∀ {p q₁ q₂ q₃ q₄ r s} ⦃ no-nr : No-dedicated-nr 𝕄₁ ⦄ →
      tr p M₂.≤ q₁ →
      q₁ M₂.≤ q₂ →
      (T M₂.𝟘ᵐ-allowed →
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
         (T M₁.𝟘ᵐ-allowed →
          q₁′ M₁.≤ q₃′) ×
         (⦃ 𝟘-well-behaved :
              Has-well-behaved-zero M₁ M₁.semiring-with-meet ⦄ →
          q₁′ M₁.≤ q₄′) ×
         q₁′ M₁.≤ q₃′ M₁.+ r M₁.· q₄′ M₁.+ s M₁.· q₁′

  open Is-morphism tr-morphism public

  -- The translation is injective.

  tr-injective : ∀ {p q} → tr p ≡ tr q → p ≡ q
  tr-injective tr-p≡tr-q = P₁.≤-antisym
    (tr-order-reflecting (P₂.≤-reflexive tr-p≡tr-q))
    (tr-order-reflecting (P₂.≤-reflexive (sym tr-p≡tr-q)))
    where
    module P₁ = Graded.Modality.Properties 𝕄₁
    module P₂ = Graded.Modality.Properties 𝕄₂

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
  tr-Σ-𝟘-≡ m ok = 𝟘ᵐ.𝟘≮ (𝟘ᵐ-in-second-if-in-first ok) (begin
    M₂.𝟘       ≡˘⟨ tr-𝟘-≡ ok ⟩
    tr M₁.𝟘    ≤⟨ tr-≤-tr-Σ ⟩
    tr-Σ M₁.𝟘  ∎)
    where
    open Is-morphism m
    open Graded.Modality.Properties 𝕄₂
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
    open Graded.Modality.Properties 𝕄₂
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
    open Graded.Modality.Properties 𝕄₂
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
  module MP₂ = Graded.Modality.Properties 𝕄₂
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
    .tr-morphism         → λ where
      .tr-<-𝟘 not-ok ok                        → ⊥-elim (not-ok ok)
      .tr-𝟙                                    → ≤-refl
      .tr-𝟘-≤                                  → ≤-refl
      .tr-≡-𝟘-⇔ _                              → idᶠ , idᶠ
      .tr-+                                    → ≤-refl
      .tr-·                                    → refl
      .tr-∧                                    → ≤-refl
      .𝟘ᵐ-in-second-if-in-first                → idᶠ
      .𝟘ᵐ-in-first-if-in-second                → idᶠ
      .𝟘-well-behaved-in-first-if-in-second    → idᶠ
      .nr-in-first-iff-in-second               → id⇔
      .tr-nr ⦃ has-nr₁ = n₁ ⦄ ⦃ has-nr₂ = n₂ ⦄ →
        case Dedicated-nr-propositional _ n₁ n₂ of λ {
          refl →
        ≤-refl }
    .tr-≤-nr ⦃ has-nr₁ = n₁ ⦄ ⦃ has-nr₂ = n₂ ⦄ hyp →
      case Dedicated-nr-propositional _ n₁ n₂ of λ {
        refl →
      _ , _ , _ , ≤-refl , ≤-refl , ≤-refl , hyp }
    .tr-≤-no-nr p≤q₁ q₁≤q₂ q₁≤q₃ q₁≤q₄ fix →
        _ , _ , _ , _ , ≤-refl , ≤-refl , ≤-refl
      , p≤q₁ , q₁≤q₂ , q₁≤q₃ , q₁≤q₄ , fix
  where
  open Graded.Modality.Properties 𝕄
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
    .Is-morphism.𝟘ᵐ-in-first-if-in-second →
      let instance
            no-nr : No-dedicated-nr 𝕄₂
            no-nr = G.no-nr-in-second-if-in-first
      in
      G.𝟘ᵐ-in-first-if-in-second ∘→ F.𝟘ᵐ-in-first-if-in-second
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second →
      let instance
            no-nr : No-dedicated-nr 𝕄₂
            no-nr = G.no-nr-in-second-if-in-first
      in
      G.𝟘-well-behaved-in-first-if-in-second ∘→
      F.𝟘-well-behaved-in-first-if-in-second
    .Is-morphism.nr-in-first-iff-in-second →
      F.nr-in-first-iff-in-second ∘⇔ G.nr-in-first-iff-in-second
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
    .Is-morphism.tr-nr {p = p} {r = r} {z = z} {s = s} {n = n} →
      let open R

          instance
            has-nr : Dedicated-nr 𝕄₂
            has-nr = G.nr-in-second-if-in-first
      in begin
      tr₁ (tr₂ (nr p r z s n))                          ≤⟨ F.tr-monotone G.tr-nr ⟩

      tr₁ (nr (tr₂ p) (tr₂ r) (tr₂ z) (tr₂ s) (tr₂ n))  ≤⟨ F.tr-nr ⟩

      nr (tr₁ (tr₂ p)) (tr₁ (tr₂ r)) (tr₁ (tr₂ z))
        (tr₁ (tr₂ s)) (tr₁ (tr₂ n))                     ∎
  where
  module Mo₂ = Mode 𝕄₂
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module M₃  = Modality 𝕄₃
  module F   = Is-morphism f
  module G   = Is-morphism g
  open Graded.Modality.Properties 𝕄₃
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
           tr₂ M₁.𝟙  ≡⟨ MP₂.≡-trivial (F.trivial not-ok₂ ok₃) ⟩
           tr₂ M₁.𝟘  ∎))
    .Is-order-embedding.trivial-⊎-tr-𝟘 →
      let open Tools.Reasoning.PropositionalEquality in
      case F.trivial-⊎-tr-𝟘 of λ where
        (inj₁ triv)    → inj₁ (G.tr-injective (MP₂.≡-trivial triv))
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
    .Is-order-embedding.tr-≤-nr {z₁ = z₁} {s₁ = s₁} {n₁ = n₁} tr-q≤ →
      let open Tools.Reasoning.PartialOrder MP₃.≤-poset

          instance
            has-nr : Dedicated-nr 𝕄₂
            has-nr = G.nr-in-second-if-in-first
      in
      case F.tr-≤-nr tr-q≤ of
        λ (z₂ , s₂ , n₂ , ≤z₁ , ≤s₁ , ≤n₁ , tr-q≤′) →
      case G.tr-≤-nr tr-q≤′ of
        λ (z₃ , s₃ , n₃ , ≤z₂ , ≤s₂ , ≤n₂ , q≤) →
        z₃ , s₃ , n₃
      , (begin
           tr₁ (tr₂ z₃)  ≤⟨ F.tr-monotone ≤z₂ ⟩
           tr₁ z₂        ≤⟨ ≤z₁ ⟩
           z₁            ∎)
      , (begin
           tr₁ (tr₂ s₃)  ≤⟨ F.tr-monotone ≤s₂ ⟩
           tr₁ s₂        ≤⟨ ≤s₁ ⟩
           s₁            ∎)
      , (begin
           tr₁ (tr₂ n₃)  ≤⟨ F.tr-monotone ≤n₂ ⟩
           tr₁ n₂        ≤⟨ ≤n₁ ⟩
           n₁            ∎)
      , q≤
    .Is-order-embedding.tr-≤-no-nr
      {q₁ = q₁} {q₂ = q₂} {q₃ = q₃} {q₄ = q₄}
      p≤q₁ q₁≤q₂ q₁≤q₃ q₁≤q₄ fix →
      let open Tools.Reasoning.PartialOrder MP₃.≤-poset

          instance
            no-nr : No-dedicated-nr 𝕄₂
            no-nr = G.no-nr-in-second-if-in-first
      in
      case F.tr-≤-no-nr p≤q₁ q₁≤q₂ q₁≤q₃ q₁≤q₄ fix of λ {
        (q₁′ , q₂′ , q₃′ , q₄′ , q₂′≤q₂ , q₃′≤q₃ , q₄′≤q₄ ,
         p≤q₁′ , q₁′≤q₂′ , q₁′≤q₃′ , q₁′≤q₄′ , fix′) →
      case G.tr-≤-no-nr p≤q₁′ q₁′≤q₂′ q₁′≤q₃′ q₁′≤q₄′ fix′ of λ {
        (q₁″ , q₂″ , q₃″ , q₄″ , q₂″≤q₂′ , q₃″≤q₃′ , q₄″≤q₄′ ,
         p≤q₁″ , q₁″≤q₂″ , q₁″≤q₃″ , q₁″≤q₄″ , fix″) →
        q₁″ , q₂″ , q₃″ , q₄″
      , (begin
           tr₁ (tr₂ q₂″)  ≤⟨ F.tr-monotone q₂″≤q₂′ ⟩
           tr₁ q₂′        ≤⟨ q₂′≤q₂ ⟩
           q₂             ∎)
      , (begin
           tr₁ (tr₂ q₃″)  ≤⟨ F.tr-monotone q₃″≤q₃′ ⟩
           tr₁ q₃′        ≤⟨ q₃′≤q₃ ⟩
           q₃             ∎)
      , (begin
           tr₁ (tr₂ q₄″)  ≤⟨ F.tr-monotone q₄″≤q₄′ ⟩
           tr₁ q₄′        ≤⟨ q₄′≤q₄ ⟩
           q₄             ∎)
      , p≤q₁″ , q₁″≤q₂″ , q₁″≤q₃″ , (λ ⦃ _ ⦄ → q₁″≤q₄″) , fix″ }}
  where
  module MP₂ = Graded.Modality.Properties 𝕄₂
  module MP₃ = Graded.Modality.Properties 𝕄₃
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
  open Graded.Modality.Properties 𝕄₃
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
  open Graded.Modality.Properties 𝕄₃
  open Tools.Reasoning.PartialOrder ≤-poset

------------------------------------------------------------------------
-- A lemma

-- The property tr-≤-no-nr follows from other properties.

→tr-≤-no-nr :
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂) →
  let
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
  in
  (T M₁.𝟘ᵐ-allowed → T M₂.𝟘ᵐ-allowed) →
  (⦃ 𝟘-well-behaved :
       Has-well-behaved-zero M₁ M₁.semiring-with-meet ⦄ →
   Has-well-behaved-zero M₂ M₂.semiring-with-meet) →
  (tr : M₁ → M₂)
  (tr⁻¹ : M₂ → M₁) →
  (∀ p q → p M₂.≤ q → tr⁻¹ p M₁.≤ tr⁻¹ q) →
  (∀ p q → tr p M₂.≤ q → p M₁.≤ tr⁻¹ q) →
  (∀ p → tr (tr⁻¹ p) M₂.≤ p) →
  (∀ p q → tr⁻¹ (p M₂.+ q) M₁.≤ tr⁻¹ p M₁.+ tr⁻¹ q) →
  (∀ p q → tr⁻¹ (p M₂.∧ q) M₁.≤ tr⁻¹ p M₁.∧ tr⁻¹ q) →
  (∀ p q → tr⁻¹ (tr p M₂.· q) M₁.≤ p M₁.· tr⁻¹ q) →
  tr p M₂.≤ q₁ →
  q₁ M₂.≤ q₂ →
  (T M₂.𝟘ᵐ-allowed →
   q₁ M₂.≤ q₃) →
  (⦃ 𝟘-well-behaved : Has-well-behaved-zero M₂ M₂.semiring-with-meet ⦄ →
   q₁ M₂.≤ q₄) →
  q₁ M₂.≤ q₃ M₂.+ tr r M₂.· q₄ M₂.+ tr s M₂.· q₁ →
  ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
     tr q₂′ M₂.≤ q₂ ×
     tr q₃′ M₂.≤ q₃ ×
     tr q₄′ M₂.≤ q₄ ×
     p M₁.≤ q₁′ ×
     q₁′ M₁.≤ q₂′ ×
     (T M₁.𝟘ᵐ-allowed →
      q₁′ M₁.≤ q₃′) ×
     (⦃ 𝟘-well-behaved :
          Has-well-behaved-zero M₁ M₁.semiring-with-meet ⦄ →
      q₁′ M₁.≤ q₄′) ×
     q₁′ M₁.≤ q₃′ M₁.+ r M₁.· q₄′ M₁.+ s M₁.· q₁′
→tr-≤-no-nr
  {q₁ = q₁} {q₂ = q₂} {q₃ = q₃} {q₄ = q₄} {r = r} {s = s}
  𝕄₁ 𝕄₂ 𝟘ᵐ-in-second-if-in-first 𝟘-well-behaved-in-second-if-in-first
  tr tr⁻¹ tr⁻¹-monotone tr≤→≤tr⁻¹ tr-tr⁻¹≤ tr⁻¹-+ tr⁻¹-∧ tr⁻¹-·
  hyp₁ hyp₂ hyp₃ hyp₄ hyp₅ =
    tr⁻¹ q₁
  , tr⁻¹ q₂
  , tr⁻¹ q₃
  , tr⁻¹ q₄
  , tr-tr⁻¹≤ _
  , tr-tr⁻¹≤ _
  , tr-tr⁻¹≤ _
  , tr≤→≤tr⁻¹ _ _ hyp₁
  , tr⁻¹-monotone _ _ hyp₂
  , tr⁻¹-monotone _ _ ∘→ hyp₃ ∘→ 𝟘ᵐ-in-second-if-in-first
  , tr⁻¹-monotone _ _
      (hyp₄ ⦃ 𝟘-well-behaved = 𝟘-well-behaved-in-second-if-in-first ⦄)
  , (begin
       tr⁻¹ q₁                                                    ≤⟨ tr⁻¹-monotone _ _ hyp₅ ⟩
       tr⁻¹ (q₃ M₂.+ tr r M₂.· q₄ M₂.+ tr s M₂.· q₁)              ≤⟨ ≤-trans (tr⁻¹-+ _ _) $ +-monotoneʳ $ tr⁻¹-+ _ _ ⟩
       tr⁻¹ q₃ M₁.+ tr⁻¹ (tr r M₂.· q₄) M₁.+ tr⁻¹ (tr s M₂.· q₁)  ≤⟨ +-monotoneʳ $ +-monotone (tr⁻¹-· _ _) (tr⁻¹-· _ _) ⟩
       tr⁻¹ q₃ M₁.+ r M₁.· tr⁻¹ q₄ M₁.+ s M₁.· tr⁻¹ q₁            ∎)
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Graded.Modality.Properties 𝕄₁
  open Tools.Reasoning.PartialOrder ≤-poset
