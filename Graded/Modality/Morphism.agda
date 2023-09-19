------------------------------------------------------------------------
-- Modality morphisms
------------------------------------------------------------------------

-- It might make sense to replace some of the proofs below with a lot
-- of cases with automated proofs.

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
open import Tools.Unit

open import Graded.Modality
open import Graded.Modality.Dedicated-nr
open import Graded.Modality.Dedicated-nr.Instance
open import Graded.Modality.Instances.Affine as A
  using (Affine; affineModality)
open import Graded.Modality.Instances.Erasure as E
  using (Erasure; 𝟘; ω)
open import Graded.Modality.Instances.Erasure.Modality as E
  using (ErasureModality)
open import Graded.Modality.Instances.Linear-or-affine as LA
  using (Linear-or-affine; 𝟘; 𝟙; ≤𝟙; ≤ω; linear-or-affine)
open import Graded.Modality.Instances.Linearity as L
  using (Linearity; linearityModality)
open import Graded.Modality.Instances.Unit using (UnitModality)
open import Graded.Modality.Instances.Zero-one-many as ZOM
  using (Zero-one-many; 𝟘; 𝟙; ω; zero-one-many-modality)
open import Graded.Modality.Nr-instances
import Graded.Modality.Properties
open import Graded.Modality.Variant
open import Graded.Restrictions

open Modality-variant

open import Graded.Mode as Mode hiding (module Mode)

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.QuantityTranslation

private variable
  a₁ a₂                       : Level
  𝟙≤𝟘 ok                      : Bool
  not-ok                      : ¬ T _
  v v₁ v₂                     : Modality-variant _
  A M M₁ M₂                   : Set _
  𝕄 𝕄₁ 𝕄₂ 𝕄₃                  : Modality _
  b                           : BinderMode
  tr tr₁ tr₂ tr-Σ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  v₁-ok v₂-ok                 : A
  p q₁ q₂ q₃ q₄ r s           : M

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
      T M₂.𝟘ᵐ-allowed ⊎ M₂.𝟙 ≡ M₂.𝟘 → T M₁.𝟘ᵐ-allowed ⊎ M₁.𝟙 ≡ M₁.𝟘

    -- If the source modality does not have a dedicated nr function
    -- and the target modality has a well-behaved zero or is trivial,
    -- then the source modality has a well-behaved zero or is trivial.
    𝟘-well-behaved-in-first-if-in-second :
      ⦃ no-nr : No-dedicated-nr 𝕄₁ ⦄ →
      Has-well-behaved-zero M₂ M₂.semiring-with-meet ⊎ M₂.𝟙 ≡ M₂.𝟘 →
      Has-well-behaved-zero M₁ M₁.semiring-with-meet ⊎ M₁.𝟙 ≡ M₁.𝟘

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
      (Has-well-behaved-zero M₂ M₂.semiring-with-meet →
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
         (Has-well-behaved-zero M₁ M₁.semiring-with-meet →
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
  tr-Σ-𝟘-≡ m ok = 𝟘≮ (𝟘ᵐ-in-second-if-in-first ok) (begin
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
      , p≤q₁″ , q₁″≤q₂″ , q₁″≤q₃″ , q₁″≤q₄″ , fix″ }}
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
  (Has-well-behaved-zero M₁ M₁.semiring-with-meet →
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
  (Has-well-behaved-zero M₂ M₂.semiring-with-meet →
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
     (Has-well-behaved-zero M₁ M₁.semiring-with-meet →
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
  , tr⁻¹-monotone _ _ ∘→ hyp₄ ∘→ 𝟘-well-behaved-in-second-if-in-first
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
-- modality to an erasure modality if a certain assumption holds.

unit⇨erasure :
  let 𝕄₁ = UnitModality v₁ v₁-ok
      𝕄₂ = ErasureModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ unit→erasure
unit⇨erasure {v₁-ok = v₁-ok} s⇔s = λ where
    .tr-order-reflecting _ → refl
    .trivial _ _           → refl
    .trivial-⊎-tr-𝟘        → inj₁ refl
    .tr-≤                  → _ , refl
    .tr-≤-𝟙 _              → refl
    .tr-≤-+ _              → _ , _ , refl , refl , refl
    .tr-≤-· _              → _ , refl , refl
    .tr-≤-∧ _              → _ , _ , refl , refl , refl
    .tr-≤-nr _             → _ , _ , _ , refl , refl , refl , refl
    .tr-≤-no-nr _ _ _ _ _  → _ , _ , _ , _ , refl , refl , refl , refl
                           , refl , (λ _ → refl) , (λ _ → refl) , refl
    .tr-morphism           → λ where
      .𝟘ᵐ-in-second-if-in-first             → ⊥-elim ∘→ v₁-ok
      .𝟘ᵐ-in-first-if-in-second _           → inj₂ refl
      .𝟘-well-behaved-in-first-if-in-second → λ _ → inj₂ refl
      .nr-in-first-iff-in-second            → s⇔s
      .tr-𝟘-≤                               → refl
      .tr-≡-𝟘-⇔                             → ⊥-elim ∘→ v₁-ok
      .tr-<-𝟘 _ _                           → refl , λ ()
      .tr-𝟙                                 → refl
      .tr-+                                 → refl
      .tr-·                                 → refl
      .tr-∧                                 → refl
      .tr-nr                                → refl
  where
  open Is-morphism
  open Is-order-embedding

-- The function erasure→unit is a morphism from an erasure modality to
-- a unit modality if certain assumptions hold.

erasure⇨unit :
  ¬ T (𝟘ᵐ-allowed v₁) →
  let 𝕄₁ = ErasureModality v₁
      𝕄₂ = UnitModality v₂ v₂-ok
  in
  ⦃ has-nr₁ : Dedicated-nr 𝕄₁ ⦄
  ⦃ has-nr₂ : Dedicated-nr 𝕄₂ ⦄ →
  Is-morphism 𝕄₁ 𝕄₂ erasure→unit
erasure⇨unit
  {v₂-ok = v₂-ok} not-ok₁ ⦃ has-nr₁ = has-nr₁ ⦄ ⦃ has-nr₂ = has-nr₂ ⦄ =
  λ where
    .tr-𝟘-≤                                 → refl
    .tr-≡-𝟘-⇔                               → ⊥-elim ∘→ not-ok₁
    .tr-<-𝟘 _                               → ⊥-elim ∘→ v₂-ok
    .tr-𝟙                                   → refl
    .tr-+                                   → refl
    .tr-·                                   → refl
    .tr-∧                                   → refl
    .tr-nr                                  → refl
    .nr-in-first-iff-in-second              → (λ _ → has-nr₂)
                                            , (λ _ → has-nr₁)
    .𝟘ᵐ-in-second-if-in-first               → ⊥-elim ∘→ not-ok₁
    .𝟘ᵐ-in-first-if-in-second               → ⊥-elim
                                                (not-nr-and-no-nr _)
    .𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ E.erasure-has-well-behaved-zero
  where
  open Is-morphism

-- The function erasure→unit is not a morphism from an erasure
-- modality to a unit modality if a certain assumption holds.

¬erasure⇨unit :
  let 𝕄₁ = ErasureModality v₁
      𝕄₂ = UnitModality v₂ v₂-ok
  in
  No-dedicated-nr 𝕄₁ ⊎ No-dedicated-nr 𝕄₂ →
  ¬ Is-morphism 𝕄₁ 𝕄₂ erasure→unit
¬erasure⇨unit {v₂-ok = v₂-ok} no-nr′ m =
  case
    Is-morphism.𝟘ᵐ-in-first-if-in-second m ⦃ no-nr = no-nr ⦄ (inj₂ refl)
  of λ {
    (inj₁ ok) →
  v₂-ok (Is-morphism.𝟘ᵐ-in-second-if-in-first m ok) }
  where
  no-nr = case no-nr′ of λ where
    (inj₁ no-nr) → no-nr
    (inj₂ no-nr) →
      Is-morphism.no-nr-in-first-if-in-second m ⦃ no-nr = no-nr ⦄

-- The function erasure→unit is not an order embedding from an erasure
-- modality to a unit modality.

¬erasure⇨unit′ :
  ¬ Is-order-embedding (ErasureModality v₁) (UnitModality v₂ v₂-ok)
      erasure→unit
¬erasure⇨unit′ m =
  case Is-order-embedding.tr-injective m {p = 𝟘} {q = ω} refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a zero-one-many-modality modality if certain
-- assumptions hold. The zero-one-many-modality modality can be
-- defined with either 𝟙 ≤ 𝟘 or 𝟙 ≰ 𝟘.

erasure⇨zero-one-many :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = ErasureModality v₁
      𝕄₂ = zero-one-many-modality 𝟙≤𝟘 v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ erasure→zero-one-many
erasure⇨zero-one-many {v₁ = v₁} {v₂ = v₂} {𝟙≤𝟘 = 𝟙≤𝟘} refl s⇔s = λ where
    .Is-order-embedding.trivial not-ok ok   → ⊥-elim (not-ok ok)
    .Is-order-embedding.trivial-⊎-tr-𝟘      → inj₂ refl
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-≤-nr {r = r}     → tr-≤-nr _ _ r _ _ _
    .Is-order-embedding.tr-≤-no-nr {s = s}  → tr-≤-no-nr s
    .Is-order-embedding.tr-order-reflecting →
      tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism → λ where
      .Is-morphism.tr-𝟘-≤                    → refl
      .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                             , λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                      → refl
      .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-· {p = p}              → tr-· p _
      .Is-morphism.tr-∧ {p = p}              → ≤-reflexive (tr-∧ p _)
      .Is-morphism.tr-nr {r = r} {z = z}     → ≤-reflexive
                                                 (tr-nr _ r z _ _)
      .Is-morphism.nr-in-first-iff-in-second → s⇔s
      .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
      .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
        (inj₁ ok) → inj₁ ok
      .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ E.erasure-has-well-behaved-zero
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘
  module P₁ = Graded.Modality.Properties (ErasureModality v₁)
  open Graded.Modality.Properties (zero-one-many-modality 𝟙≤𝟘 v₂)
  open Tools.Reasoning.PartialOrder ≤-poset

  tr′  = erasure→zero-one-many
  tr⁻¹ = zero-one-many→erasure

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

  tr-nr :
    ∀ p r z s n →
    tr′ (E.nr p r z s n) ≡
    𝟘𝟙ω.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = tr-nr′ _
    where
    tr-nr′ :
      ∀ 𝟙≤𝟘 →
      let module 𝟘𝟙ω′ = ZOM 𝟙≤𝟘 in
      ∀ p r z s n →
      tr′ (E.nr p r z s n) ≡
      𝟘𝟙ω′.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
    tr-nr′ = λ where
      false 𝟘 𝟘 𝟘 𝟘 𝟘 → refl
      false 𝟘 𝟘 𝟘 𝟘 ω → refl
      false 𝟘 𝟘 𝟘 ω 𝟘 → refl
      false 𝟘 𝟘 𝟘 ω ω → refl
      false 𝟘 𝟘 ω 𝟘 𝟘 → refl
      false 𝟘 𝟘 ω 𝟘 ω → refl
      false 𝟘 𝟘 ω ω 𝟘 → refl
      false 𝟘 𝟘 ω ω ω → refl
      false 𝟘 ω 𝟘 𝟘 𝟘 → refl
      false 𝟘 ω 𝟘 𝟘 ω → refl
      false 𝟘 ω 𝟘 ω 𝟘 → refl
      false 𝟘 ω 𝟘 ω ω → refl
      false 𝟘 ω ω 𝟘 𝟘 → refl
      false 𝟘 ω ω 𝟘 ω → refl
      false 𝟘 ω ω ω 𝟘 → refl
      false 𝟘 ω ω ω ω → refl
      false ω 𝟘 𝟘 𝟘 𝟘 → refl
      false ω 𝟘 𝟘 𝟘 ω → refl
      false ω 𝟘 𝟘 ω 𝟘 → refl
      false ω 𝟘 𝟘 ω ω → refl
      false ω 𝟘 ω 𝟘 𝟘 → refl
      false ω 𝟘 ω 𝟘 ω → refl
      false ω 𝟘 ω ω 𝟘 → refl
      false ω 𝟘 ω ω ω → refl
      false ω ω 𝟘 𝟘 𝟘 → refl
      false ω ω 𝟘 𝟘 ω → refl
      false ω ω 𝟘 ω 𝟘 → refl
      false ω ω 𝟘 ω ω → refl
      false ω ω ω 𝟘 𝟘 → refl
      false ω ω ω 𝟘 ω → refl
      false ω ω ω ω 𝟘 → refl
      false ω ω ω ω ω → refl
      true  𝟘 𝟘 𝟘 𝟘 𝟘 → refl
      true  𝟘 𝟘 𝟘 𝟘 ω → refl
      true  𝟘 𝟘 𝟘 ω 𝟘 → refl
      true  𝟘 𝟘 𝟘 ω ω → refl
      true  𝟘 𝟘 ω 𝟘 𝟘 → refl
      true  𝟘 𝟘 ω 𝟘 ω → refl
      true  𝟘 𝟘 ω ω 𝟘 → refl
      true  𝟘 𝟘 ω ω ω → refl
      true  𝟘 ω 𝟘 𝟘 𝟘 → refl
      true  𝟘 ω 𝟘 𝟘 ω → refl
      true  𝟘 ω 𝟘 ω 𝟘 → refl
      true  𝟘 ω 𝟘 ω ω → refl
      true  𝟘 ω ω 𝟘 𝟘 → refl
      true  𝟘 ω ω 𝟘 ω → refl
      true  𝟘 ω ω ω 𝟘 → refl
      true  𝟘 ω ω ω ω → refl
      true  ω 𝟘 𝟘 𝟘 𝟘 → refl
      true  ω 𝟘 𝟘 𝟘 ω → refl
      true  ω 𝟘 𝟘 ω 𝟘 → refl
      true  ω 𝟘 𝟘 ω ω → refl
      true  ω 𝟘 ω 𝟘 𝟘 → refl
      true  ω 𝟘 ω 𝟘 ω → refl
      true  ω 𝟘 ω ω 𝟘 → refl
      true  ω 𝟘 ω ω ω → refl
      true  ω ω 𝟘 𝟘 𝟘 → refl
      true  ω ω 𝟘 𝟘 ω → refl
      true  ω ω 𝟘 ω 𝟘 → refl
      true  ω ω 𝟘 ω ω → refl
      true  ω ω ω 𝟘 𝟘 → refl
      true  ω ω ω 𝟘 ω → refl
      true  ω ω ω ω 𝟘 → refl
      true  ω ω ω ω ω → refl

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

  tr-≤-nr :
    ∀ q p r z₁ s₁ n₁ →
    tr′ q 𝟘𝟙ω.≤ 𝟘𝟙ω.nr (tr′ p) (tr′ r) z₁ s₁ n₁ →
    ∃₃ λ z₂ s₂ n₂ →
       tr′ z₂ 𝟘𝟙ω.≤ z₁ × tr′ s₂ 𝟘𝟙ω.≤ s₁ × tr′ n₂ 𝟘𝟙ω.≤ n₁ ×
       q E.≤ E.nr p r z₂ s₂ n₂
  tr-≤-nr = tr-≤-nr′ _
    where
    tr-≤-nr′ :
      ∀ 𝟙≤𝟘 →
      let module 𝟘𝟙ω′ = ZOM 𝟙≤𝟘 in
      ∀ q p r z₁ s₁ n₁ →
      tr′ q 𝟘𝟙ω′.≤ 𝟘𝟙ω′.nr (tr′ p) (tr′ r) z₁ s₁ n₁ →
      ∃₃ λ z₂ s₂ n₂ →
         tr′ z₂ 𝟘𝟙ω′.≤ z₁ × tr′ s₂ 𝟘𝟙ω′.≤ s₁ × tr′ n₂ 𝟘𝟙ω′.≤ n₁ ×
         q E.≤ E.nr p r z₂ s₂ n₂
    tr-≤-nr′ = λ where
      _     𝟘 𝟘 𝟘 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     𝟘 𝟘 ω 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     𝟘 ω 𝟘 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     𝟘 ω ω 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     ω _ _ _ _ _ _  → ω , ω , ω , refl , refl , refl , refl
      false 𝟘 𝟘 𝟘 𝟘 𝟘 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟘 𝟘 ω ()
      false 𝟘 𝟘 𝟘 𝟘 𝟙 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟘 𝟙 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟘 𝟙 ω ()
      false 𝟘 𝟘 𝟘 𝟘 ω 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟘 ω 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟘 ω ω ()
      false 𝟘 𝟘 𝟘 𝟙 𝟘 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟘 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟘 ω ()
      false 𝟘 𝟘 𝟘 𝟙 𝟙 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟙 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟙 ω ()
      false 𝟘 𝟘 𝟘 𝟙 ω 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟙 ω 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟙 ω ω ()
      false 𝟘 𝟘 𝟘 ω 𝟘 𝟘 ()
      false 𝟘 𝟘 𝟘 ω 𝟘 𝟙 ()
      false 𝟘 𝟘 𝟘 ω 𝟘 ω ()
      false 𝟘 𝟘 𝟘 ω 𝟙 𝟘 ()
      false 𝟘 𝟘 𝟘 ω 𝟙 𝟙 ()
      false 𝟘 𝟘 𝟘 ω 𝟙 ω ()
      false 𝟘 𝟘 𝟘 ω ω 𝟘 ()
      false 𝟘 𝟘 𝟘 ω ω 𝟙 ()
      false 𝟘 𝟘 𝟘 ω ω ω ()
      false 𝟘 𝟘 ω 𝟘 𝟘 𝟙 ()
      false 𝟘 𝟘 ω 𝟘 𝟘 ω ()
      false 𝟘 𝟘 ω 𝟘 𝟙 𝟘 ()
      false 𝟘 𝟘 ω 𝟘 𝟙 𝟙 ()
      false 𝟘 𝟘 ω 𝟘 𝟙 ω ()
      false 𝟘 𝟘 ω 𝟘 ω 𝟘 ()
      false 𝟘 𝟘 ω 𝟘 ω 𝟙 ()
      false 𝟘 𝟘 ω 𝟘 ω ω ()
      false 𝟘 𝟘 ω 𝟙 𝟘 𝟘 ()
      false 𝟘 𝟘 ω 𝟙 𝟘 𝟙 ()
      false 𝟘 𝟘 ω 𝟙 𝟘 ω ()
      false 𝟘 𝟘 ω 𝟙 𝟙 𝟘 ()
      false 𝟘 𝟘 ω 𝟙 𝟙 𝟙 ()
      false 𝟘 𝟘 ω 𝟙 𝟙 ω ()
      false 𝟘 𝟘 ω 𝟙 ω 𝟘 ()
      false 𝟘 𝟘 ω 𝟙 ω 𝟙 ()
      false 𝟘 𝟘 ω 𝟙 ω ω ()
      false 𝟘 𝟘 ω ω 𝟘 𝟘 ()
      false 𝟘 𝟘 ω ω 𝟘 𝟙 ()
      false 𝟘 𝟘 ω ω 𝟘 ω ()
      false 𝟘 𝟘 ω ω 𝟙 𝟘 ()
      false 𝟘 𝟘 ω ω 𝟙 𝟙 ()
      false 𝟘 𝟘 ω ω 𝟙 ω ()
      false 𝟘 𝟘 ω ω ω 𝟘 ()
      false 𝟘 𝟘 ω ω ω 𝟙 ()
      false 𝟘 𝟘 ω ω ω ω ()
      false 𝟘 ω 𝟘 𝟘 𝟘 𝟙 ()
      false 𝟘 ω 𝟘 𝟘 𝟘 ω ()
      false 𝟘 ω 𝟘 𝟘 𝟙 𝟘 ()
      false 𝟘 ω 𝟘 𝟘 𝟙 𝟙 ()
      false 𝟘 ω 𝟘 𝟘 𝟙 ω ()
      false 𝟘 ω 𝟘 𝟘 ω 𝟘 ()
      false 𝟘 ω 𝟘 𝟘 ω 𝟙 ()
      false 𝟘 ω 𝟘 𝟘 ω ω ()
      false 𝟘 ω 𝟘 𝟙 𝟘 𝟘 ()
      false 𝟘 ω 𝟘 𝟙 𝟘 𝟙 ()
      false 𝟘 ω 𝟘 𝟙 𝟘 ω ()
      false 𝟘 ω 𝟘 𝟙 𝟙 𝟘 ()
      false 𝟘 ω 𝟘 𝟙 𝟙 𝟙 ()
      false 𝟘 ω 𝟘 𝟙 𝟙 ω ()
      false 𝟘 ω 𝟘 𝟙 ω 𝟘 ()
      false 𝟘 ω 𝟘 𝟙 ω 𝟙 ()
      false 𝟘 ω 𝟘 𝟙 ω ω ()
      false 𝟘 ω 𝟘 ω 𝟘 𝟘 ()
      false 𝟘 ω 𝟘 ω 𝟘 𝟙 ()
      false 𝟘 ω 𝟘 ω 𝟘 ω ()
      false 𝟘 ω 𝟘 ω 𝟙 𝟘 ()
      false 𝟘 ω 𝟘 ω 𝟙 𝟙 ()
      false 𝟘 ω 𝟘 ω 𝟙 ω ()
      false 𝟘 ω 𝟘 ω ω 𝟘 ()
      false 𝟘 ω 𝟘 ω ω 𝟙 ()
      false 𝟘 ω 𝟘 ω ω ω ()
      false 𝟘 ω ω 𝟘 𝟘 𝟙 ()
      false 𝟘 ω ω 𝟘 𝟘 ω ()
      false 𝟘 ω ω 𝟘 𝟙 𝟘 ()
      false 𝟘 ω ω 𝟘 𝟙 𝟙 ()
      false 𝟘 ω ω 𝟘 𝟙 ω ()
      false 𝟘 ω ω 𝟘 ω 𝟘 ()
      false 𝟘 ω ω 𝟘 ω 𝟙 ()
      false 𝟘 ω ω 𝟘 ω ω ()
      false 𝟘 ω ω 𝟙 𝟘 𝟘 ()
      false 𝟘 ω ω 𝟙 𝟘 𝟙 ()
      false 𝟘 ω ω 𝟙 𝟘 ω ()
      false 𝟘 ω ω 𝟙 𝟙 𝟘 ()
      false 𝟘 ω ω 𝟙 𝟙 𝟙 ()
      false 𝟘 ω ω 𝟙 𝟙 ω ()
      false 𝟘 ω ω 𝟙 ω 𝟘 ()
      false 𝟘 ω ω 𝟙 ω 𝟙 ()
      false 𝟘 ω ω 𝟙 ω ω ()
      false 𝟘 ω ω ω 𝟘 𝟘 ()
      false 𝟘 ω ω ω 𝟘 𝟙 ()
      false 𝟘 ω ω ω 𝟘 ω ()
      false 𝟘 ω ω ω 𝟙 𝟘 ()
      false 𝟘 ω ω ω 𝟙 𝟙 ()
      false 𝟘 ω ω ω 𝟙 ω ()
      false 𝟘 ω ω ω ω 𝟘 ()
      false 𝟘 ω ω ω ω 𝟙 ()
      false 𝟘 ω ω ω ω ω ()

  tr⁻¹-monotone : ∀ p q → p 𝟘𝟙ω.≤ q → tr⁻¹ p E.≤ tr⁻¹ q
  tr⁻¹-monotone = λ where
    𝟘 𝟘 _     → refl
    𝟘 𝟙 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
    𝟙 𝟘 _     → refl
    𝟙 𝟙 _     → refl
    ω 𝟘 _     → refl
    ω 𝟙 _     → refl
    ω ω _     → refl

  tr-tr⁻¹≤ : ∀ p → tr′ (tr⁻¹ p) 𝟘𝟙ω.≤ p
  tr-tr⁻¹≤ = λ where
    𝟘 → refl
    𝟙 → refl
    ω → refl

  tr≤→≤tr⁻¹ : ∀ p q → tr′ p 𝟘𝟙ω.≤ q → p E.≤ tr⁻¹ q
  tr≤→≤tr⁻¹ = λ where
    𝟘 𝟘 _     → refl
    𝟘 𝟙 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
    ω 𝟘 _     → refl
    ω 𝟙 _     → refl
    ω ω _     → refl

  tr⁻¹-𝟘∧𝟙 : tr⁻¹ 𝟘𝟙ω.𝟘∧𝟙 ≡ ω
  tr⁻¹-𝟘∧𝟙 = 𝟘𝟙ω.𝟘∧𝟙-elim
    (λ p → tr⁻¹ p ≡ ω)
    (λ _ → refl)
    (λ _ → refl)

  tr⁻¹-∧ : ∀ p q → tr⁻¹ (p 𝟘𝟙ω.∧ q) ≡ tr⁻¹ p E.∧ tr⁻¹ q
  tr⁻¹-∧ = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → tr⁻¹-𝟘∧𝟙
    𝟘 ω → refl
    𝟙 𝟘 → tr⁻¹-𝟘∧𝟙
    𝟙 𝟙 → refl
    𝟙 ω → refl
    ω 𝟘 → refl
    ω 𝟙 → refl
    ω ω → refl

  tr⁻¹-+ : ∀ p q → tr⁻¹ (p 𝟘𝟙ω.+ q) ≡ tr⁻¹ p E.+ tr⁻¹ q
  tr⁻¹-+ = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → refl
    𝟘 ω → refl
    𝟙 𝟘 → refl
    𝟙 𝟙 → refl
    𝟙 ω → refl
    ω 𝟘 → refl
    ω 𝟙 → refl
    ω ω → refl

  tr⁻¹-· : ∀ p q → tr⁻¹ (tr′ p 𝟘𝟙ω.· q) ≡ p E.· tr⁻¹ q
  tr⁻¹-· = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → refl
    𝟘 ω → refl
    ω 𝟘 → refl
    ω 𝟙 → refl
    ω ω → refl

  tr-≤-no-nr :
    ∀ s →
    tr′ p 𝟘𝟙ω.≤ q₁ →
    q₁ 𝟘𝟙ω.≤ q₂ →
    (T (Modality-variant.𝟘ᵐ-allowed v₁) →
     q₁ 𝟘𝟙ω.≤ q₃) →
    (Has-well-behaved-zero 𝟘𝟙ω.Zero-one-many
       𝟘𝟙ω.zero-one-many-semiring-with-meet →
     q₁ 𝟘𝟙ω.≤ q₄) →
    q₁ 𝟘𝟙ω.≤ q₃ 𝟘𝟙ω.+ tr′ r 𝟘𝟙ω.· q₄ 𝟘𝟙ω.+ tr′ s 𝟘𝟙ω.· q₁ →
    ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
       tr′ q₂′ 𝟘𝟙ω.≤ q₂ ×
       tr′ q₃′ 𝟘𝟙ω.≤ q₃ ×
       tr′ q₄′ 𝟘𝟙ω.≤ q₄ ×
       p E.≤ q₁′ ×
       q₁′ E.≤ q₂′ ×
       (T (Modality-variant.𝟘ᵐ-allowed v₂) →
        q₁′ E.≤ q₃′) ×
       (Has-well-behaved-zero Erasure E.erasure-semiring-with-meet →
        q₁′ E.≤ q₄′) ×
       q₁′ E.≤ q₃′ E.+ (r E.· q₄′ E.+ s E.· q₁′)
  tr-≤-no-nr s = →tr-≤-no-nr {s = s}
    (ErasureModality v₁)
    (zero-one-many-modality 𝟙≤𝟘 v₂)
    idᶠ
    (λ _ → 𝟘𝟙ω.zero-one-many-has-well-behaved-zero)
    tr′
    tr⁻¹
    tr⁻¹-monotone
    tr≤→≤tr⁻¹
    tr-tr⁻¹≤
    (λ p q → P₁.≤-reflexive (tr⁻¹-+ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-∧ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-· p q))

-- The function zero-one-many→erasure is a morphism from a
-- zero-one-many-modality modality to an erasure modality if certain
-- assumptions hold. The zero-one-many-modality modality can be
-- defined with either 𝟙 ≤ 𝟘 or 𝟙 ≰ 𝟘.

zero-one-many⇨erasure :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = zero-one-many-modality 𝟙≤𝟘 v₁
      𝕄₂ = ErasureModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ zero-one-many→erasure
zero-one-many⇨erasure {v₂ = v₂} {𝟙≤𝟘 = 𝟙≤𝟘} refl s⇔s = λ where
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                           , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-· {p = p}              → tr-· p _
    .Is-morphism.tr-∧ {p = p}              → ≤-reflexive (tr-∧ p _)
    .Is-morphism.tr-nr {r = r}             → ≤-reflexive
                                               (tr-nr _ r _ _ _)
    .Is-morphism.nr-in-first-iff-in-second → s⇔s
    .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
    .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
      (inj₁ ok) → inj₁ ok
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ 𝟘𝟙ω.zero-one-many-has-well-behaved-zero
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘
  open Graded.Modality.Properties (ErasureModality v₂)

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

  tr-nr :
    ∀ p r z s n →
    tr′ (𝟘𝟙ω.nr p r z s n) ≡
    E.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = tr-nr′ _
    where
    tr-nr′ :
      ∀ 𝟙≤𝟘 →
      let module 𝟘𝟙ω′ = ZOM 𝟙≤𝟘 in
      ∀ p r z s n →
      tr′ (𝟘𝟙ω′.nr p r z s n) ≡
      E.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
    tr-nr′ = λ where
      false 𝟘 𝟘 𝟘 𝟘 𝟘 → refl
      false 𝟘 𝟘 𝟘 𝟘 𝟙 → refl
      false 𝟘 𝟘 𝟘 𝟘 ω → refl
      false 𝟘 𝟘 𝟘 𝟙 𝟘 → refl
      false 𝟘 𝟘 𝟘 𝟙 𝟙 → refl
      false 𝟘 𝟘 𝟘 𝟙 ω → refl
      false 𝟘 𝟘 𝟘 ω 𝟘 → refl
      false 𝟘 𝟘 𝟘 ω 𝟙 → refl
      false 𝟘 𝟘 𝟘 ω ω → refl
      false 𝟘 𝟘 𝟙 𝟘 𝟘 → refl
      false 𝟘 𝟘 𝟙 𝟘 𝟙 → refl
      false 𝟘 𝟘 𝟙 𝟘 ω → refl
      false 𝟘 𝟘 𝟙 𝟙 𝟘 → refl
      false 𝟘 𝟘 𝟙 𝟙 𝟙 → refl
      false 𝟘 𝟘 𝟙 𝟙 ω → refl
      false 𝟘 𝟘 𝟙 ω 𝟘 → refl
      false 𝟘 𝟘 𝟙 ω 𝟙 → refl
      false 𝟘 𝟘 𝟙 ω ω → refl
      false 𝟘 𝟘 ω 𝟘 𝟘 → refl
      false 𝟘 𝟘 ω 𝟘 𝟙 → refl
      false 𝟘 𝟘 ω 𝟘 ω → refl
      false 𝟘 𝟘 ω 𝟙 𝟘 → refl
      false 𝟘 𝟘 ω 𝟙 𝟙 → refl
      false 𝟘 𝟘 ω 𝟙 ω → refl
      false 𝟘 𝟘 ω ω 𝟘 → refl
      false 𝟘 𝟘 ω ω 𝟙 → refl
      false 𝟘 𝟘 ω ω ω → refl
      false 𝟘 𝟙 𝟘 𝟘 𝟘 → refl
      false 𝟘 𝟙 𝟘 𝟘 𝟙 → refl
      false 𝟘 𝟙 𝟘 𝟘 ω → refl
      false 𝟘 𝟙 𝟘 𝟙 𝟘 → refl
      false 𝟘 𝟙 𝟘 𝟙 𝟙 → refl
      false 𝟘 𝟙 𝟘 𝟙 ω → refl
      false 𝟘 𝟙 𝟘 ω 𝟘 → refl
      false 𝟘 𝟙 𝟘 ω 𝟙 → refl
      false 𝟘 𝟙 𝟘 ω ω → refl
      false 𝟘 𝟙 𝟙 𝟘 𝟘 → refl
      false 𝟘 𝟙 𝟙 𝟘 𝟙 → refl
      false 𝟘 𝟙 𝟙 𝟘 ω → refl
      false 𝟘 𝟙 𝟙 𝟙 𝟘 → refl
      false 𝟘 𝟙 𝟙 𝟙 𝟙 → refl
      false 𝟘 𝟙 𝟙 𝟙 ω → refl
      false 𝟘 𝟙 𝟙 ω 𝟘 → refl
      false 𝟘 𝟙 𝟙 ω 𝟙 → refl
      false 𝟘 𝟙 𝟙 ω ω → refl
      false 𝟘 𝟙 ω 𝟘 𝟘 → refl
      false 𝟘 𝟙 ω 𝟘 𝟙 → refl
      false 𝟘 𝟙 ω 𝟘 ω → refl
      false 𝟘 𝟙 ω 𝟙 𝟘 → refl
      false 𝟘 𝟙 ω 𝟙 𝟙 → refl
      false 𝟘 𝟙 ω 𝟙 ω → refl
      false 𝟘 𝟙 ω ω 𝟘 → refl
      false 𝟘 𝟙 ω ω 𝟙 → refl
      false 𝟘 𝟙 ω ω ω → refl
      false 𝟘 ω 𝟘 𝟘 𝟘 → refl
      false 𝟘 ω 𝟘 𝟘 𝟙 → refl
      false 𝟘 ω 𝟘 𝟘 ω → refl
      false 𝟘 ω 𝟘 𝟙 𝟘 → refl
      false 𝟘 ω 𝟘 𝟙 𝟙 → refl
      false 𝟘 ω 𝟘 𝟙 ω → refl
      false 𝟘 ω 𝟘 ω 𝟘 → refl
      false 𝟘 ω 𝟘 ω 𝟙 → refl
      false 𝟘 ω 𝟘 ω ω → refl
      false 𝟘 ω 𝟙 𝟘 𝟘 → refl
      false 𝟘 ω 𝟙 𝟘 𝟙 → refl
      false 𝟘 ω 𝟙 𝟘 ω → refl
      false 𝟘 ω 𝟙 𝟙 𝟘 → refl
      false 𝟘 ω 𝟙 𝟙 𝟙 → refl
      false 𝟘 ω 𝟙 𝟙 ω → refl
      false 𝟘 ω 𝟙 ω 𝟘 → refl
      false 𝟘 ω 𝟙 ω 𝟙 → refl
      false 𝟘 ω 𝟙 ω ω → refl
      false 𝟘 ω ω 𝟘 𝟘 → refl
      false 𝟘 ω ω 𝟘 𝟙 → refl
      false 𝟘 ω ω 𝟘 ω → refl
      false 𝟘 ω ω 𝟙 𝟘 → refl
      false 𝟘 ω ω 𝟙 𝟙 → refl
      false 𝟘 ω ω 𝟙 ω → refl
      false 𝟘 ω ω ω 𝟘 → refl
      false 𝟘 ω ω ω 𝟙 → refl
      false 𝟘 ω ω ω ω → refl
      false 𝟙 𝟘 𝟘 𝟘 𝟘 → refl
      false 𝟙 𝟘 𝟘 𝟘 𝟙 → refl
      false 𝟙 𝟘 𝟘 𝟘 ω → refl
      false 𝟙 𝟘 𝟘 𝟙 𝟘 → refl
      false 𝟙 𝟘 𝟘 𝟙 𝟙 → refl
      false 𝟙 𝟘 𝟘 𝟙 ω → refl
      false 𝟙 𝟘 𝟘 ω 𝟘 → refl
      false 𝟙 𝟘 𝟘 ω 𝟙 → refl
      false 𝟙 𝟘 𝟘 ω ω → refl
      false 𝟙 𝟘 𝟙 𝟘 𝟘 → refl
      false 𝟙 𝟘 𝟙 𝟘 𝟙 → refl
      false 𝟙 𝟘 𝟙 𝟘 ω → refl
      false 𝟙 𝟘 𝟙 𝟙 𝟘 → refl
      false 𝟙 𝟘 𝟙 𝟙 𝟙 → refl
      false 𝟙 𝟘 𝟙 𝟙 ω → refl
      false 𝟙 𝟘 𝟙 ω 𝟘 → refl
      false 𝟙 𝟘 𝟙 ω 𝟙 → refl
      false 𝟙 𝟘 𝟙 ω ω → refl
      false 𝟙 𝟘 ω 𝟘 𝟘 → refl
      false 𝟙 𝟘 ω 𝟘 𝟙 → refl
      false 𝟙 𝟘 ω 𝟘 ω → refl
      false 𝟙 𝟘 ω 𝟙 𝟘 → refl
      false 𝟙 𝟘 ω 𝟙 𝟙 → refl
      false 𝟙 𝟘 ω 𝟙 ω → refl
      false 𝟙 𝟘 ω ω 𝟘 → refl
      false 𝟙 𝟘 ω ω 𝟙 → refl
      false 𝟙 𝟘 ω ω ω → refl
      false 𝟙 𝟙 𝟘 𝟘 𝟘 → refl
      false 𝟙 𝟙 𝟘 𝟘 𝟙 → refl
      false 𝟙 𝟙 𝟘 𝟘 ω → refl
      false 𝟙 𝟙 𝟘 𝟙 𝟘 → refl
      false 𝟙 𝟙 𝟘 𝟙 𝟙 → refl
      false 𝟙 𝟙 𝟘 𝟙 ω → refl
      false 𝟙 𝟙 𝟘 ω 𝟘 → refl
      false 𝟙 𝟙 𝟘 ω 𝟙 → refl
      false 𝟙 𝟙 𝟘 ω ω → refl
      false 𝟙 𝟙 𝟙 𝟘 𝟘 → refl
      false 𝟙 𝟙 𝟙 𝟘 𝟙 → refl
      false 𝟙 𝟙 𝟙 𝟘 ω → refl
      false 𝟙 𝟙 𝟙 𝟙 𝟘 → refl
      false 𝟙 𝟙 𝟙 𝟙 𝟙 → refl
      false 𝟙 𝟙 𝟙 𝟙 ω → refl
      false 𝟙 𝟙 𝟙 ω 𝟘 → refl
      false 𝟙 𝟙 𝟙 ω 𝟙 → refl
      false 𝟙 𝟙 𝟙 ω ω → refl
      false 𝟙 𝟙 ω 𝟘 𝟘 → refl
      false 𝟙 𝟙 ω 𝟘 𝟙 → refl
      false 𝟙 𝟙 ω 𝟘 ω → refl
      false 𝟙 𝟙 ω 𝟙 𝟘 → refl
      false 𝟙 𝟙 ω 𝟙 𝟙 → refl
      false 𝟙 𝟙 ω 𝟙 ω → refl
      false 𝟙 𝟙 ω ω 𝟘 → refl
      false 𝟙 𝟙 ω ω 𝟙 → refl
      false 𝟙 𝟙 ω ω ω → refl
      false 𝟙 ω 𝟘 𝟘 𝟘 → refl
      false 𝟙 ω 𝟘 𝟘 𝟙 → refl
      false 𝟙 ω 𝟘 𝟘 ω → refl
      false 𝟙 ω 𝟘 𝟙 𝟘 → refl
      false 𝟙 ω 𝟘 𝟙 𝟙 → refl
      false 𝟙 ω 𝟘 𝟙 ω → refl
      false 𝟙 ω 𝟘 ω 𝟘 → refl
      false 𝟙 ω 𝟘 ω 𝟙 → refl
      false 𝟙 ω 𝟘 ω ω → refl
      false 𝟙 ω 𝟙 𝟘 𝟘 → refl
      false 𝟙 ω 𝟙 𝟘 𝟙 → refl
      false 𝟙 ω 𝟙 𝟘 ω → refl
      false 𝟙 ω 𝟙 𝟙 𝟘 → refl
      false 𝟙 ω 𝟙 𝟙 𝟙 → refl
      false 𝟙 ω 𝟙 𝟙 ω → refl
      false 𝟙 ω 𝟙 ω 𝟘 → refl
      false 𝟙 ω 𝟙 ω 𝟙 → refl
      false 𝟙 ω 𝟙 ω ω → refl
      false 𝟙 ω ω 𝟘 𝟘 → refl
      false 𝟙 ω ω 𝟘 𝟙 → refl
      false 𝟙 ω ω 𝟘 ω → refl
      false 𝟙 ω ω 𝟙 𝟘 → refl
      false 𝟙 ω ω 𝟙 𝟙 → refl
      false 𝟙 ω ω 𝟙 ω → refl
      false 𝟙 ω ω ω 𝟘 → refl
      false 𝟙 ω ω ω 𝟙 → refl
      false 𝟙 ω ω ω ω → refl
      false ω 𝟘 𝟘 𝟘 𝟘 → refl
      false ω 𝟘 𝟘 𝟘 𝟙 → refl
      false ω 𝟘 𝟘 𝟘 ω → refl
      false ω 𝟘 𝟘 𝟙 𝟘 → refl
      false ω 𝟘 𝟘 𝟙 𝟙 → refl
      false ω 𝟘 𝟘 𝟙 ω → refl
      false ω 𝟘 𝟘 ω 𝟘 → refl
      false ω 𝟘 𝟘 ω 𝟙 → refl
      false ω 𝟘 𝟘 ω ω → refl
      false ω 𝟘 𝟙 𝟘 𝟘 → refl
      false ω 𝟘 𝟙 𝟘 𝟙 → refl
      false ω 𝟘 𝟙 𝟘 ω → refl
      false ω 𝟘 𝟙 𝟙 𝟘 → refl
      false ω 𝟘 𝟙 𝟙 𝟙 → refl
      false ω 𝟘 𝟙 𝟙 ω → refl
      false ω 𝟘 𝟙 ω 𝟘 → refl
      false ω 𝟘 𝟙 ω 𝟙 → refl
      false ω 𝟘 𝟙 ω ω → refl
      false ω 𝟘 ω 𝟘 𝟘 → refl
      false ω 𝟘 ω 𝟘 𝟙 → refl
      false ω 𝟘 ω 𝟘 ω → refl
      false ω 𝟘 ω 𝟙 𝟘 → refl
      false ω 𝟘 ω 𝟙 𝟙 → refl
      false ω 𝟘 ω 𝟙 ω → refl
      false ω 𝟘 ω ω 𝟘 → refl
      false ω 𝟘 ω ω 𝟙 → refl
      false ω 𝟘 ω ω ω → refl
      false ω 𝟙 𝟘 𝟘 𝟘 → refl
      false ω 𝟙 𝟘 𝟘 𝟙 → refl
      false ω 𝟙 𝟘 𝟘 ω → refl
      false ω 𝟙 𝟘 𝟙 𝟘 → refl
      false ω 𝟙 𝟘 𝟙 𝟙 → refl
      false ω 𝟙 𝟘 𝟙 ω → refl
      false ω 𝟙 𝟘 ω 𝟘 → refl
      false ω 𝟙 𝟘 ω 𝟙 → refl
      false ω 𝟙 𝟘 ω ω → refl
      false ω 𝟙 𝟙 𝟘 𝟘 → refl
      false ω 𝟙 𝟙 𝟘 𝟙 → refl
      false ω 𝟙 𝟙 𝟘 ω → refl
      false ω 𝟙 𝟙 𝟙 𝟘 → refl
      false ω 𝟙 𝟙 𝟙 𝟙 → refl
      false ω 𝟙 𝟙 𝟙 ω → refl
      false ω 𝟙 𝟙 ω 𝟘 → refl
      false ω 𝟙 𝟙 ω 𝟙 → refl
      false ω 𝟙 𝟙 ω ω → refl
      false ω 𝟙 ω 𝟘 𝟘 → refl
      false ω 𝟙 ω 𝟘 𝟙 → refl
      false ω 𝟙 ω 𝟘 ω → refl
      false ω 𝟙 ω 𝟙 𝟘 → refl
      false ω 𝟙 ω 𝟙 𝟙 → refl
      false ω 𝟙 ω 𝟙 ω → refl
      false ω 𝟙 ω ω 𝟘 → refl
      false ω 𝟙 ω ω 𝟙 → refl
      false ω 𝟙 ω ω ω → refl
      false ω ω 𝟘 𝟘 𝟘 → refl
      false ω ω 𝟘 𝟘 𝟙 → refl
      false ω ω 𝟘 𝟘 ω → refl
      false ω ω 𝟘 𝟙 𝟘 → refl
      false ω ω 𝟘 𝟙 𝟙 → refl
      false ω ω 𝟘 𝟙 ω → refl
      false ω ω 𝟘 ω 𝟘 → refl
      false ω ω 𝟘 ω 𝟙 → refl
      false ω ω 𝟘 ω ω → refl
      false ω ω 𝟙 𝟘 𝟘 → refl
      false ω ω 𝟙 𝟘 𝟙 → refl
      false ω ω 𝟙 𝟘 ω → refl
      false ω ω 𝟙 𝟙 𝟘 → refl
      false ω ω 𝟙 𝟙 𝟙 → refl
      false ω ω 𝟙 𝟙 ω → refl
      false ω ω 𝟙 ω 𝟘 → refl
      false ω ω 𝟙 ω 𝟙 → refl
      false ω ω 𝟙 ω ω → refl
      false ω ω ω 𝟘 𝟘 → refl
      false ω ω ω 𝟘 𝟙 → refl
      false ω ω ω 𝟘 ω → refl
      false ω ω ω 𝟙 𝟘 → refl
      false ω ω ω 𝟙 𝟙 → refl
      false ω ω ω 𝟙 ω → refl
      false ω ω ω ω 𝟘 → refl
      false ω ω ω ω 𝟙 → refl
      false ω ω ω ω ω → refl
      true  𝟘 𝟘 𝟘 𝟘 𝟘 → refl
      true  𝟘 𝟘 𝟘 𝟘 𝟙 → refl
      true  𝟘 𝟘 𝟘 𝟘 ω → refl
      true  𝟘 𝟘 𝟘 𝟙 𝟘 → refl
      true  𝟘 𝟘 𝟘 𝟙 𝟙 → refl
      true  𝟘 𝟘 𝟘 𝟙 ω → refl
      true  𝟘 𝟘 𝟘 ω 𝟘 → refl
      true  𝟘 𝟘 𝟘 ω 𝟙 → refl
      true  𝟘 𝟘 𝟘 ω ω → refl
      true  𝟘 𝟘 𝟙 𝟘 𝟘 → refl
      true  𝟘 𝟘 𝟙 𝟘 𝟙 → refl
      true  𝟘 𝟘 𝟙 𝟘 ω → refl
      true  𝟘 𝟘 𝟙 𝟙 𝟘 → refl
      true  𝟘 𝟘 𝟙 𝟙 𝟙 → refl
      true  𝟘 𝟘 𝟙 𝟙 ω → refl
      true  𝟘 𝟘 𝟙 ω 𝟘 → refl
      true  𝟘 𝟘 𝟙 ω 𝟙 → refl
      true  𝟘 𝟘 𝟙 ω ω → refl
      true  𝟘 𝟘 ω 𝟘 𝟘 → refl
      true  𝟘 𝟘 ω 𝟘 𝟙 → refl
      true  𝟘 𝟘 ω 𝟘 ω → refl
      true  𝟘 𝟘 ω 𝟙 𝟘 → refl
      true  𝟘 𝟘 ω 𝟙 𝟙 → refl
      true  𝟘 𝟘 ω 𝟙 ω → refl
      true  𝟘 𝟘 ω ω 𝟘 → refl
      true  𝟘 𝟘 ω ω 𝟙 → refl
      true  𝟘 𝟘 ω ω ω → refl
      true  𝟘 𝟙 𝟘 𝟘 𝟘 → refl
      true  𝟘 𝟙 𝟘 𝟘 𝟙 → refl
      true  𝟘 𝟙 𝟘 𝟘 ω → refl
      true  𝟘 𝟙 𝟘 𝟙 𝟘 → refl
      true  𝟘 𝟙 𝟘 𝟙 𝟙 → refl
      true  𝟘 𝟙 𝟘 𝟙 ω → refl
      true  𝟘 𝟙 𝟘 ω 𝟘 → refl
      true  𝟘 𝟙 𝟘 ω 𝟙 → refl
      true  𝟘 𝟙 𝟘 ω ω → refl
      true  𝟘 𝟙 𝟙 𝟘 𝟘 → refl
      true  𝟘 𝟙 𝟙 𝟘 𝟙 → refl
      true  𝟘 𝟙 𝟙 𝟘 ω → refl
      true  𝟘 𝟙 𝟙 𝟙 𝟘 → refl
      true  𝟘 𝟙 𝟙 𝟙 𝟙 → refl
      true  𝟘 𝟙 𝟙 𝟙 ω → refl
      true  𝟘 𝟙 𝟙 ω 𝟘 → refl
      true  𝟘 𝟙 𝟙 ω 𝟙 → refl
      true  𝟘 𝟙 𝟙 ω ω → refl
      true  𝟘 𝟙 ω 𝟘 𝟘 → refl
      true  𝟘 𝟙 ω 𝟘 𝟙 → refl
      true  𝟘 𝟙 ω 𝟘 ω → refl
      true  𝟘 𝟙 ω 𝟙 𝟘 → refl
      true  𝟘 𝟙 ω 𝟙 𝟙 → refl
      true  𝟘 𝟙 ω 𝟙 ω → refl
      true  𝟘 𝟙 ω ω 𝟘 → refl
      true  𝟘 𝟙 ω ω 𝟙 → refl
      true  𝟘 𝟙 ω ω ω → refl
      true  𝟘 ω 𝟘 𝟘 𝟘 → refl
      true  𝟘 ω 𝟘 𝟘 𝟙 → refl
      true  𝟘 ω 𝟘 𝟘 ω → refl
      true  𝟘 ω 𝟘 𝟙 𝟘 → refl
      true  𝟘 ω 𝟘 𝟙 𝟙 → refl
      true  𝟘 ω 𝟘 𝟙 ω → refl
      true  𝟘 ω 𝟘 ω 𝟘 → refl
      true  𝟘 ω 𝟘 ω 𝟙 → refl
      true  𝟘 ω 𝟘 ω ω → refl
      true  𝟘 ω 𝟙 𝟘 𝟘 → refl
      true  𝟘 ω 𝟙 𝟘 𝟙 → refl
      true  𝟘 ω 𝟙 𝟘 ω → refl
      true  𝟘 ω 𝟙 𝟙 𝟘 → refl
      true  𝟘 ω 𝟙 𝟙 𝟙 → refl
      true  𝟘 ω 𝟙 𝟙 ω → refl
      true  𝟘 ω 𝟙 ω 𝟘 → refl
      true  𝟘 ω 𝟙 ω 𝟙 → refl
      true  𝟘 ω 𝟙 ω ω → refl
      true  𝟘 ω ω 𝟘 𝟘 → refl
      true  𝟘 ω ω 𝟘 𝟙 → refl
      true  𝟘 ω ω 𝟘 ω → refl
      true  𝟘 ω ω 𝟙 𝟘 → refl
      true  𝟘 ω ω 𝟙 𝟙 → refl
      true  𝟘 ω ω 𝟙 ω → refl
      true  𝟘 ω ω ω 𝟘 → refl
      true  𝟘 ω ω ω 𝟙 → refl
      true  𝟘 ω ω ω ω → refl
      true  𝟙 𝟘 𝟘 𝟘 𝟘 → refl
      true  𝟙 𝟘 𝟘 𝟘 𝟙 → refl
      true  𝟙 𝟘 𝟘 𝟘 ω → refl
      true  𝟙 𝟘 𝟘 𝟙 𝟘 → refl
      true  𝟙 𝟘 𝟘 𝟙 𝟙 → refl
      true  𝟙 𝟘 𝟘 𝟙 ω → refl
      true  𝟙 𝟘 𝟘 ω 𝟘 → refl
      true  𝟙 𝟘 𝟘 ω 𝟙 → refl
      true  𝟙 𝟘 𝟘 ω ω → refl
      true  𝟙 𝟘 𝟙 𝟘 𝟘 → refl
      true  𝟙 𝟘 𝟙 𝟘 𝟙 → refl
      true  𝟙 𝟘 𝟙 𝟘 ω → refl
      true  𝟙 𝟘 𝟙 𝟙 𝟘 → refl
      true  𝟙 𝟘 𝟙 𝟙 𝟙 → refl
      true  𝟙 𝟘 𝟙 𝟙 ω → refl
      true  𝟙 𝟘 𝟙 ω 𝟘 → refl
      true  𝟙 𝟘 𝟙 ω 𝟙 → refl
      true  𝟙 𝟘 𝟙 ω ω → refl
      true  𝟙 𝟘 ω 𝟘 𝟘 → refl
      true  𝟙 𝟘 ω 𝟘 𝟙 → refl
      true  𝟙 𝟘 ω 𝟘 ω → refl
      true  𝟙 𝟘 ω 𝟙 𝟘 → refl
      true  𝟙 𝟘 ω 𝟙 𝟙 → refl
      true  𝟙 𝟘 ω 𝟙 ω → refl
      true  𝟙 𝟘 ω ω 𝟘 → refl
      true  𝟙 𝟘 ω ω 𝟙 → refl
      true  𝟙 𝟘 ω ω ω → refl
      true  𝟙 𝟙 𝟘 𝟘 𝟘 → refl
      true  𝟙 𝟙 𝟘 𝟘 𝟙 → refl
      true  𝟙 𝟙 𝟘 𝟘 ω → refl
      true  𝟙 𝟙 𝟘 𝟙 𝟘 → refl
      true  𝟙 𝟙 𝟘 𝟙 𝟙 → refl
      true  𝟙 𝟙 𝟘 𝟙 ω → refl
      true  𝟙 𝟙 𝟘 ω 𝟘 → refl
      true  𝟙 𝟙 𝟘 ω 𝟙 → refl
      true  𝟙 𝟙 𝟘 ω ω → refl
      true  𝟙 𝟙 𝟙 𝟘 𝟘 → refl
      true  𝟙 𝟙 𝟙 𝟘 𝟙 → refl
      true  𝟙 𝟙 𝟙 𝟘 ω → refl
      true  𝟙 𝟙 𝟙 𝟙 𝟘 → refl
      true  𝟙 𝟙 𝟙 𝟙 𝟙 → refl
      true  𝟙 𝟙 𝟙 𝟙 ω → refl
      true  𝟙 𝟙 𝟙 ω 𝟘 → refl
      true  𝟙 𝟙 𝟙 ω 𝟙 → refl
      true  𝟙 𝟙 𝟙 ω ω → refl
      true  𝟙 𝟙 ω 𝟘 𝟘 → refl
      true  𝟙 𝟙 ω 𝟘 𝟙 → refl
      true  𝟙 𝟙 ω 𝟘 ω → refl
      true  𝟙 𝟙 ω 𝟙 𝟘 → refl
      true  𝟙 𝟙 ω 𝟙 𝟙 → refl
      true  𝟙 𝟙 ω 𝟙 ω → refl
      true  𝟙 𝟙 ω ω 𝟘 → refl
      true  𝟙 𝟙 ω ω 𝟙 → refl
      true  𝟙 𝟙 ω ω ω → refl
      true  𝟙 ω 𝟘 𝟘 𝟘 → refl
      true  𝟙 ω 𝟘 𝟘 𝟙 → refl
      true  𝟙 ω 𝟘 𝟘 ω → refl
      true  𝟙 ω 𝟘 𝟙 𝟘 → refl
      true  𝟙 ω 𝟘 𝟙 𝟙 → refl
      true  𝟙 ω 𝟘 𝟙 ω → refl
      true  𝟙 ω 𝟘 ω 𝟘 → refl
      true  𝟙 ω 𝟘 ω 𝟙 → refl
      true  𝟙 ω 𝟘 ω ω → refl
      true  𝟙 ω 𝟙 𝟘 𝟘 → refl
      true  𝟙 ω 𝟙 𝟘 𝟙 → refl
      true  𝟙 ω 𝟙 𝟘 ω → refl
      true  𝟙 ω 𝟙 𝟙 𝟘 → refl
      true  𝟙 ω 𝟙 𝟙 𝟙 → refl
      true  𝟙 ω 𝟙 𝟙 ω → refl
      true  𝟙 ω 𝟙 ω 𝟘 → refl
      true  𝟙 ω 𝟙 ω 𝟙 → refl
      true  𝟙 ω 𝟙 ω ω → refl
      true  𝟙 ω ω 𝟘 𝟘 → refl
      true  𝟙 ω ω 𝟘 𝟙 → refl
      true  𝟙 ω ω 𝟘 ω → refl
      true  𝟙 ω ω 𝟙 𝟘 → refl
      true  𝟙 ω ω 𝟙 𝟙 → refl
      true  𝟙 ω ω 𝟙 ω → refl
      true  𝟙 ω ω ω 𝟘 → refl
      true  𝟙 ω ω ω 𝟙 → refl
      true  𝟙 ω ω ω ω → refl
      true  ω 𝟘 𝟘 𝟘 𝟘 → refl
      true  ω 𝟘 𝟘 𝟘 𝟙 → refl
      true  ω 𝟘 𝟘 𝟘 ω → refl
      true  ω 𝟘 𝟘 𝟙 𝟘 → refl
      true  ω 𝟘 𝟘 𝟙 𝟙 → refl
      true  ω 𝟘 𝟘 𝟙 ω → refl
      true  ω 𝟘 𝟘 ω 𝟘 → refl
      true  ω 𝟘 𝟘 ω 𝟙 → refl
      true  ω 𝟘 𝟘 ω ω → refl
      true  ω 𝟘 𝟙 𝟘 𝟘 → refl
      true  ω 𝟘 𝟙 𝟘 𝟙 → refl
      true  ω 𝟘 𝟙 𝟘 ω → refl
      true  ω 𝟘 𝟙 𝟙 𝟘 → refl
      true  ω 𝟘 𝟙 𝟙 𝟙 → refl
      true  ω 𝟘 𝟙 𝟙 ω → refl
      true  ω 𝟘 𝟙 ω 𝟘 → refl
      true  ω 𝟘 𝟙 ω 𝟙 → refl
      true  ω 𝟘 𝟙 ω ω → refl
      true  ω 𝟘 ω 𝟘 𝟘 → refl
      true  ω 𝟘 ω 𝟘 𝟙 → refl
      true  ω 𝟘 ω 𝟘 ω → refl
      true  ω 𝟘 ω 𝟙 𝟘 → refl
      true  ω 𝟘 ω 𝟙 𝟙 → refl
      true  ω 𝟘 ω 𝟙 ω → refl
      true  ω 𝟘 ω ω 𝟘 → refl
      true  ω 𝟘 ω ω 𝟙 → refl
      true  ω 𝟘 ω ω ω → refl
      true  ω 𝟙 𝟘 𝟘 𝟘 → refl
      true  ω 𝟙 𝟘 𝟘 𝟙 → refl
      true  ω 𝟙 𝟘 𝟘 ω → refl
      true  ω 𝟙 𝟘 𝟙 𝟘 → refl
      true  ω 𝟙 𝟘 𝟙 𝟙 → refl
      true  ω 𝟙 𝟘 𝟙 ω → refl
      true  ω 𝟙 𝟘 ω 𝟘 → refl
      true  ω 𝟙 𝟘 ω 𝟙 → refl
      true  ω 𝟙 𝟘 ω ω → refl
      true  ω 𝟙 𝟙 𝟘 𝟘 → refl
      true  ω 𝟙 𝟙 𝟘 𝟙 → refl
      true  ω 𝟙 𝟙 𝟘 ω → refl
      true  ω 𝟙 𝟙 𝟙 𝟘 → refl
      true  ω 𝟙 𝟙 𝟙 𝟙 → refl
      true  ω 𝟙 𝟙 𝟙 ω → refl
      true  ω 𝟙 𝟙 ω 𝟘 → refl
      true  ω 𝟙 𝟙 ω 𝟙 → refl
      true  ω 𝟙 𝟙 ω ω → refl
      true  ω 𝟙 ω 𝟘 𝟘 → refl
      true  ω 𝟙 ω 𝟘 𝟙 → refl
      true  ω 𝟙 ω 𝟘 ω → refl
      true  ω 𝟙 ω 𝟙 𝟘 → refl
      true  ω 𝟙 ω 𝟙 𝟙 → refl
      true  ω 𝟙 ω 𝟙 ω → refl
      true  ω 𝟙 ω ω 𝟘 → refl
      true  ω 𝟙 ω ω 𝟙 → refl
      true  ω 𝟙 ω ω ω → refl
      true  ω ω 𝟘 𝟘 𝟘 → refl
      true  ω ω 𝟘 𝟘 𝟙 → refl
      true  ω ω 𝟘 𝟘 ω → refl
      true  ω ω 𝟘 𝟙 𝟘 → refl
      true  ω ω 𝟘 𝟙 𝟙 → refl
      true  ω ω 𝟘 𝟙 ω → refl
      true  ω ω 𝟘 ω 𝟘 → refl
      true  ω ω 𝟘 ω 𝟙 → refl
      true  ω ω 𝟘 ω ω → refl
      true  ω ω 𝟙 𝟘 𝟘 → refl
      true  ω ω 𝟙 𝟘 𝟙 → refl
      true  ω ω 𝟙 𝟘 ω → refl
      true  ω ω 𝟙 𝟙 𝟘 → refl
      true  ω ω 𝟙 𝟙 𝟙 → refl
      true  ω ω 𝟙 𝟙 ω → refl
      true  ω ω 𝟙 ω 𝟘 → refl
      true  ω ω 𝟙 ω 𝟙 → refl
      true  ω ω 𝟙 ω ω → refl
      true  ω ω ω 𝟘 𝟘 → refl
      true  ω ω ω 𝟘 𝟙 → refl
      true  ω ω ω 𝟘 ω → refl
      true  ω ω ω 𝟙 𝟘 → refl
      true  ω ω ω 𝟙 𝟙 → refl
      true  ω ω ω 𝟙 ω → refl
      true  ω ω ω ω 𝟘 → refl
      true  ω ω ω ω 𝟙 → refl
      true  ω ω ω ω ω → refl

-- The function zero-one-many→erasure is not an order embedding from a
-- zero-one-many-modality modality to an erasure modality.

¬zero-one-many⇨erasure :
  ¬ Is-order-embedding
      (zero-one-many-modality 𝟙≤𝟘 v₁)
      (ErasureModality v₂)
      zero-one-many→erasure
¬zero-one-many⇨erasure m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ω} refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a linear types modality if certain assumptions
-- hold.

erasure⇨linearity :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = ErasureModality v₁
      𝕄₂ = linearityModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ erasure→zero-one-many
erasure⇨linearity = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from a linear
-- types modality to an erasure modality if certain assumptions hold.

linearity⇨erasure :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = linearityModality v₁
      𝕄₂ = ErasureModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ zero-one-many→erasure
linearity⇨erasure = zero-one-many⇨erasure

-- The function zero-one-many→erasure is not an order embedding from a
-- linear types modality to an erasure modality.

¬linearity⇨erasure :
  ¬ Is-order-embedding (linearityModality v₁) (ErasureModality v₂)
      zero-one-many→erasure
¬linearity⇨erasure = ¬zero-one-many⇨erasure

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to an affine types modality if certain assumptions
-- hold.

erasure⇨affine :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = ErasureModality v₁
      𝕄₂ = affineModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ erasure→zero-one-many
erasure⇨affine = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from an affine
-- types modality to an erasure modality if certain assumptions hold.

affine⇨erasure :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = affineModality v₁
      𝕄₂ = ErasureModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ zero-one-many→erasure
affine⇨erasure = zero-one-many⇨erasure

-- The function zero-one-many→erasure is not an order embedding from
-- an affine types modality to an erasure modality.

¬affine⇨erasure :
  ¬ Is-order-embedding (affineModality v₁) (ErasureModality v₂)
      zero-one-many→erasure
¬affine⇨erasure = ¬zero-one-many⇨erasure

-- The function linearity→linear-or-affine is an order embedding from
-- a linear types modality to a linear or affine types modality if
-- certain assumptions hold.

linearity⇨linear-or-affine :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = linearityModality v₁
      𝕄₂ = linear-or-affine v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ linearity→linear-or-affine
linearity⇨linear-or-affine {v₁ = v₁} {v₂ = v₂} refl s⇔s = λ where
    .Is-order-embedding.trivial not-ok ok   → ⊥-elim (not-ok ok)
    .Is-order-embedding.trivial-⊎-tr-𝟘      → inj₂ refl
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-≤-nr {r = r}     → tr-≤-nr _ _ r _ _ _
    .Is-order-embedding.tr-≤-no-nr {s = s}  → tr-≤-no-nr s
    .Is-order-embedding.tr-order-reflecting → tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism         → λ where
      .Is-morphism.tr-𝟘-≤                    → refl
      .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                             , λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                      → refl
      .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-·                      → tr-· _ _
      .Is-morphism.tr-∧                      → tr-∧ _ _
      .Is-morphism.tr-nr {r = r}             → tr-nr _ r _ _ _
      .Is-morphism.nr-in-first-iff-in-second → s⇔s
      .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
      .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
        (inj₁ ok) → inj₁ ok
      .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ (L.linearity-has-well-behaved-zero v₂)
  where
  module P₁ = Graded.Modality.Properties (linearityModality v₁)
  open Graded.Modality.Properties (linear-or-affine v₂)

  tr′  = linearity→linear-or-affine
  tr⁻¹ = linear-or-affine→linearity

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

  tr-nr :
    ∀ p r z s n →
    tr′ (L.nr p r z s n) LA.≤
    LA.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘 𝟘 𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟘 𝟘 𝟙 → refl
    𝟘 𝟘 𝟘 𝟘 ω → refl
    𝟘 𝟘 𝟘 𝟙 𝟘 → refl
    𝟘 𝟘 𝟘 𝟙 𝟙 → refl
    𝟘 𝟘 𝟘 𝟙 ω → refl
    𝟘 𝟘 𝟘 ω 𝟘 → refl
    𝟘 𝟘 𝟘 ω 𝟙 → refl
    𝟘 𝟘 𝟘 ω ω → refl
    𝟘 𝟘 𝟙 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 𝟘 𝟙 → refl
    𝟘 𝟘 𝟙 𝟘 ω → refl
    𝟘 𝟘 𝟙 𝟙 𝟘 → refl
    𝟘 𝟘 𝟙 𝟙 𝟙 → refl
    𝟘 𝟘 𝟙 𝟙 ω → refl
    𝟘 𝟘 𝟙 ω 𝟘 → refl
    𝟘 𝟘 𝟙 ω 𝟙 → refl
    𝟘 𝟘 𝟙 ω ω → refl
    𝟘 𝟘 ω 𝟘 𝟘 → refl
    𝟘 𝟘 ω 𝟘 𝟙 → refl
    𝟘 𝟘 ω 𝟘 ω → refl
    𝟘 𝟘 ω 𝟙 𝟘 → refl
    𝟘 𝟘 ω 𝟙 𝟙 → refl
    𝟘 𝟘 ω 𝟙 ω → refl
    𝟘 𝟘 ω ω 𝟘 → refl
    𝟘 𝟘 ω ω 𝟙 → refl
    𝟘 𝟘 ω ω ω → refl
    𝟘 𝟙 𝟘 𝟘 𝟘 → refl
    𝟘 𝟙 𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 𝟘 ω → refl
    𝟘 𝟙 𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟘 𝟙 𝟙 → refl
    𝟘 𝟙 𝟘 𝟙 ω → refl
    𝟘 𝟙 𝟘 ω 𝟘 → refl
    𝟘 𝟙 𝟘 ω 𝟙 → refl
    𝟘 𝟙 𝟘 ω ω → refl
    𝟘 𝟙 𝟙 𝟘 𝟘 → refl
    𝟘 𝟙 𝟙 𝟘 𝟙 → refl
    𝟘 𝟙 𝟙 𝟘 ω → refl
    𝟘 𝟙 𝟙 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 𝟙 ω → refl
    𝟘 𝟙 𝟙 ω 𝟘 → refl
    𝟘 𝟙 𝟙 ω 𝟙 → refl
    𝟘 𝟙 𝟙 ω ω → refl
    𝟘 𝟙 ω 𝟘 𝟘 → refl
    𝟘 𝟙 ω 𝟘 𝟙 → refl
    𝟘 𝟙 ω 𝟘 ω → refl
    𝟘 𝟙 ω 𝟙 𝟘 → refl
    𝟘 𝟙 ω 𝟙 𝟙 → refl
    𝟘 𝟙 ω 𝟙 ω → refl
    𝟘 𝟙 ω ω 𝟘 → refl
    𝟘 𝟙 ω ω 𝟙 → refl
    𝟘 𝟙 ω ω ω → refl
    𝟘 ω 𝟘 𝟘 𝟘 → refl
    𝟘 ω 𝟘 𝟘 𝟙 → refl
    𝟘 ω 𝟘 𝟘 ω → refl
    𝟘 ω 𝟘 𝟙 𝟘 → refl
    𝟘 ω 𝟘 𝟙 𝟙 → refl
    𝟘 ω 𝟘 𝟙 ω → refl
    𝟘 ω 𝟘 ω 𝟘 → refl
    𝟘 ω 𝟘 ω 𝟙 → refl
    𝟘 ω 𝟘 ω ω → refl
    𝟘 ω 𝟙 𝟘 𝟘 → refl
    𝟘 ω 𝟙 𝟘 𝟙 → refl
    𝟘 ω 𝟙 𝟘 ω → refl
    𝟘 ω 𝟙 𝟙 𝟘 → refl
    𝟘 ω 𝟙 𝟙 𝟙 → refl
    𝟘 ω 𝟙 𝟙 ω → refl
    𝟘 ω 𝟙 ω 𝟘 → refl
    𝟘 ω 𝟙 ω 𝟙 → refl
    𝟘 ω 𝟙 ω ω → refl
    𝟘 ω ω 𝟘 𝟘 → refl
    𝟘 ω ω 𝟘 𝟙 → refl
    𝟘 ω ω 𝟘 ω → refl
    𝟘 ω ω 𝟙 𝟘 → refl
    𝟘 ω ω 𝟙 𝟙 → refl
    𝟘 ω ω 𝟙 ω → refl
    𝟘 ω ω ω 𝟘 → refl
    𝟘 ω ω ω 𝟙 → refl
    𝟘 ω ω ω ω → refl
    𝟙 𝟘 𝟘 𝟘 𝟘 → refl
    𝟙 𝟘 𝟘 𝟘 𝟙 → refl
    𝟙 𝟘 𝟘 𝟘 ω → refl
    𝟙 𝟘 𝟘 𝟙 𝟘 → refl
    𝟙 𝟘 𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 𝟙 ω → refl
    𝟙 𝟘 𝟘 ω 𝟘 → refl
    𝟙 𝟘 𝟘 ω 𝟙 → refl
    𝟙 𝟘 𝟘 ω ω → refl
    𝟙 𝟘 𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 𝟘 𝟙 → refl
    𝟙 𝟘 𝟙 𝟘 ω → refl
    𝟙 𝟘 𝟙 𝟙 𝟘 → refl
    𝟙 𝟘 𝟙 𝟙 𝟙 → refl
    𝟙 𝟘 𝟙 𝟙 ω → refl
    𝟙 𝟘 𝟙 ω 𝟘 → refl
    𝟙 𝟘 𝟙 ω 𝟙 → refl
    𝟙 𝟘 𝟙 ω ω → refl
    𝟙 𝟘 ω 𝟘 𝟘 → refl
    𝟙 𝟘 ω 𝟘 𝟙 → refl
    𝟙 𝟘 ω 𝟘 ω → refl
    𝟙 𝟘 ω 𝟙 𝟘 → refl
    𝟙 𝟘 ω 𝟙 𝟙 → refl
    𝟙 𝟘 ω 𝟙 ω → refl
    𝟙 𝟘 ω ω 𝟘 → refl
    𝟙 𝟘 ω ω 𝟙 → refl
    𝟙 𝟘 ω ω ω → refl
    𝟙 𝟙 𝟘 𝟘 𝟘 → refl
    𝟙 𝟙 𝟘 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 𝟘 ω → refl
    𝟙 𝟙 𝟘 𝟙 𝟘 → refl
    𝟙 𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟙 𝟘 𝟙 ω → refl
    𝟙 𝟙 𝟘 ω 𝟘 → refl
    𝟙 𝟙 𝟘 ω 𝟙 → refl
    𝟙 𝟙 𝟘 ω ω → refl
    𝟙 𝟙 𝟙 𝟘 𝟘 → refl
    𝟙 𝟙 𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 𝟙 𝟙 ω → refl
    𝟙 𝟙 𝟙 ω 𝟘 → refl
    𝟙 𝟙 𝟙 ω 𝟙 → refl
    𝟙 𝟙 𝟙 ω ω → refl
    𝟙 𝟙 ω 𝟘 𝟘 → refl
    𝟙 𝟙 ω 𝟘 𝟙 → refl
    𝟙 𝟙 ω 𝟘 ω → refl
    𝟙 𝟙 ω 𝟙 𝟘 → refl
    𝟙 𝟙 ω 𝟙 𝟙 → refl
    𝟙 𝟙 ω 𝟙 ω → refl
    𝟙 𝟙 ω ω 𝟘 → refl
    𝟙 𝟙 ω ω 𝟙 → refl
    𝟙 𝟙 ω ω ω → refl
    𝟙 ω 𝟘 𝟘 𝟘 → refl
    𝟙 ω 𝟘 𝟘 𝟙 → refl
    𝟙 ω 𝟘 𝟘 ω → refl
    𝟙 ω 𝟘 𝟙 𝟘 → refl
    𝟙 ω 𝟘 𝟙 𝟙 → refl
    𝟙 ω 𝟘 𝟙 ω → refl
    𝟙 ω 𝟘 ω 𝟘 → refl
    𝟙 ω 𝟘 ω 𝟙 → refl
    𝟙 ω 𝟘 ω ω → refl
    𝟙 ω 𝟙 𝟘 𝟘 → refl
    𝟙 ω 𝟙 𝟘 𝟙 → refl
    𝟙 ω 𝟙 𝟘 ω → refl
    𝟙 ω 𝟙 𝟙 𝟘 → refl
    𝟙 ω 𝟙 𝟙 𝟙 → refl
    𝟙 ω 𝟙 𝟙 ω → refl
    𝟙 ω 𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 ω 𝟙 → refl
    𝟙 ω 𝟙 ω ω → refl
    𝟙 ω ω 𝟘 𝟘 → refl
    𝟙 ω ω 𝟘 𝟙 → refl
    𝟙 ω ω 𝟘 ω → refl
    𝟙 ω ω 𝟙 𝟘 → refl
    𝟙 ω ω 𝟙 𝟙 → refl
    𝟙 ω ω 𝟙 ω → refl
    𝟙 ω ω ω 𝟘 → refl
    𝟙 ω ω ω 𝟙 → refl
    𝟙 ω ω ω ω → refl
    ω 𝟘 𝟘 𝟘 𝟘 → refl
    ω 𝟘 𝟘 𝟘 𝟙 → refl
    ω 𝟘 𝟘 𝟘 ω → refl
    ω 𝟘 𝟘 𝟙 𝟘 → refl
    ω 𝟘 𝟘 𝟙 𝟙 → refl
    ω 𝟘 𝟘 𝟙 ω → refl
    ω 𝟘 𝟘 ω 𝟘 → refl
    ω 𝟘 𝟘 ω 𝟙 → refl
    ω 𝟘 𝟘 ω ω → refl
    ω 𝟘 𝟙 𝟘 𝟘 → refl
    ω 𝟘 𝟙 𝟘 𝟙 → refl
    ω 𝟘 𝟙 𝟘 ω → refl
    ω 𝟘 𝟙 𝟙 𝟘 → refl
    ω 𝟘 𝟙 𝟙 𝟙 → refl
    ω 𝟘 𝟙 𝟙 ω → refl
    ω 𝟘 𝟙 ω 𝟘 → refl
    ω 𝟘 𝟙 ω 𝟙 → refl
    ω 𝟘 𝟙 ω ω → refl
    ω 𝟘 ω 𝟘 𝟘 → refl
    ω 𝟘 ω 𝟘 𝟙 → refl
    ω 𝟘 ω 𝟘 ω → refl
    ω 𝟘 ω 𝟙 𝟘 → refl
    ω 𝟘 ω 𝟙 𝟙 → refl
    ω 𝟘 ω 𝟙 ω → refl
    ω 𝟘 ω ω 𝟘 → refl
    ω 𝟘 ω ω 𝟙 → refl
    ω 𝟘 ω ω ω → refl
    ω 𝟙 𝟘 𝟘 𝟘 → refl
    ω 𝟙 𝟘 𝟘 𝟙 → refl
    ω 𝟙 𝟘 𝟘 ω → refl
    ω 𝟙 𝟘 𝟙 𝟘 → refl
    ω 𝟙 𝟘 𝟙 𝟙 → refl
    ω 𝟙 𝟘 𝟙 ω → refl
    ω 𝟙 𝟘 ω 𝟘 → refl
    ω 𝟙 𝟘 ω 𝟙 → refl
    ω 𝟙 𝟘 ω ω → refl
    ω 𝟙 𝟙 𝟘 𝟘 → refl
    ω 𝟙 𝟙 𝟘 𝟙 → refl
    ω 𝟙 𝟙 𝟘 ω → refl
    ω 𝟙 𝟙 𝟙 𝟘 → refl
    ω 𝟙 𝟙 𝟙 𝟙 → refl
    ω 𝟙 𝟙 𝟙 ω → refl
    ω 𝟙 𝟙 ω 𝟘 → refl
    ω 𝟙 𝟙 ω 𝟙 → refl
    ω 𝟙 𝟙 ω ω → refl
    ω 𝟙 ω 𝟘 𝟘 → refl
    ω 𝟙 ω 𝟘 𝟙 → refl
    ω 𝟙 ω 𝟘 ω → refl
    ω 𝟙 ω 𝟙 𝟘 → refl
    ω 𝟙 ω 𝟙 𝟙 → refl
    ω 𝟙 ω 𝟙 ω → refl
    ω 𝟙 ω ω 𝟘 → refl
    ω 𝟙 ω ω 𝟙 → refl
    ω 𝟙 ω ω ω → refl
    ω ω 𝟘 𝟘 𝟘 → refl
    ω ω 𝟘 𝟘 𝟙 → refl
    ω ω 𝟘 𝟘 ω → refl
    ω ω 𝟘 𝟙 𝟘 → refl
    ω ω 𝟘 𝟙 𝟙 → refl
    ω ω 𝟘 𝟙 ω → refl
    ω ω 𝟘 ω 𝟘 → refl
    ω ω 𝟘 ω 𝟙 → refl
    ω ω 𝟘 ω ω → refl
    ω ω 𝟙 𝟘 𝟘 → refl
    ω ω 𝟙 𝟘 𝟙 → refl
    ω ω 𝟙 𝟘 ω → refl
    ω ω 𝟙 𝟙 𝟘 → refl
    ω ω 𝟙 𝟙 𝟙 → refl
    ω ω 𝟙 𝟙 ω → refl
    ω ω 𝟙 ω 𝟘 → refl
    ω ω 𝟙 ω 𝟙 → refl
    ω ω 𝟙 ω ω → refl
    ω ω ω 𝟘 𝟘 → refl
    ω ω ω 𝟘 𝟙 → refl
    ω ω ω 𝟘 ω → refl
    ω ω ω 𝟙 𝟘 → refl
    ω ω ω 𝟙 𝟙 → refl
    ω ω ω 𝟙 ω → refl
    ω ω ω ω 𝟘 → refl
    ω ω ω ω 𝟙 → refl
    ω ω ω ω ω → refl

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

  tr-≤-nr :
    ∀ q p r z₁ s₁ n₁ →
    tr′ q LA.≤ LA.nr (tr′ p) (tr′ r) z₁ s₁ n₁ →
    ∃₃ λ z₂ s₂ n₂ →
       tr′ z₂ LA.≤ z₁ × tr′ s₂ LA.≤ s₁ × tr′ n₂ LA.≤ n₁ ×
       q L.≤ L.nr p r z₂ s₂ n₂
  tr-≤-nr = λ where
    ω _ _ _  _  _  _  → ω , ω , ω , refl , refl , refl , refl
    𝟘 𝟘 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟘  𝟘  𝟙  _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  𝟘  𝟙  _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 𝟘 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 𝟘 ω 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 ω 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 ω 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 ω 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 ω 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 ω 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 ω 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 ω 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 ω 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 ω 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 ω 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 ω ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 ω ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 ω ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 ω ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 ω ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 ω ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 ω ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 ω ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 ω ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 ω ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 ω ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 ω ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 ω ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 ω ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 ω ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 ω ≤ω ≤ω ≤ω ()
    𝟘 𝟙 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 𝟙 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 𝟙 ω 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 ω 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 ω 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 ω 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 ω 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 ω 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 ω 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 ω 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 ω 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 ω 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 ω 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 ω ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 ω ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 ω ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 ω ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 ω ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 ω ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 ω ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 ω ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 ω ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 ω ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 ω ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 ω ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 ω ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 ω ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 ω ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 ω ≤ω ≤ω ≤ω ()
    𝟘 ω 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 ω 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 ω 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 ω 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 ω 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 ω 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 ω 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 ω 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 ω 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 ω 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 ω 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 ω 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 ω 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 ω 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 ω 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 ω 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 ω 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 ω 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 ω 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 ω 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 ω 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 ω 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 ω 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 ω 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 ω 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 ω 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 ω 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 ω 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 ω 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 ω 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 ω 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 ω 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 ω 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 ω 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 ω 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 ω 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 ω 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 ω 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 ω 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 ω 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 ω 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 ω 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 ω 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 ω 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 ω 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 ω 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 ω ω 𝟘  𝟘  𝟙  ()
    𝟘 ω ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω ω 𝟘  𝟘  ≤ω ()
    𝟘 ω ω 𝟘  𝟙  𝟘  ()
    𝟘 ω ω 𝟘  𝟙  𝟙  ()
    𝟘 ω ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω ω 𝟘  𝟙  ≤ω ()
    𝟘 ω ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω ω 𝟘  ≤ω 𝟘  ()
    𝟘 ω ω 𝟘  ≤ω 𝟙  ()
    𝟘 ω ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω ω 𝟘  ≤ω ≤ω ()
    𝟘 ω ω 𝟙  𝟘  𝟘  ()
    𝟘 ω ω 𝟙  𝟘  𝟙  ()
    𝟘 ω ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω ω 𝟙  𝟘  ≤ω ()
    𝟘 ω ω 𝟙  𝟙  𝟘  ()
    𝟘 ω ω 𝟙  𝟙  𝟙  ()
    𝟘 ω ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω ω 𝟙  𝟙  ≤ω ()
    𝟘 ω ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω ω 𝟙  ≤ω 𝟘  ()
    𝟘 ω ω 𝟙  ≤ω 𝟙  ()
    𝟘 ω ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω ω 𝟙  ≤ω ≤ω ()
    𝟘 ω ω ≤𝟙 𝟘  𝟘  ()
    𝟘 ω ω ≤𝟙 𝟘  𝟙  ()
    𝟘 ω ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω ω ≤𝟙 𝟘  ≤ω ()
    𝟘 ω ω ≤𝟙 𝟙  𝟘  ()
    𝟘 ω ω ≤𝟙 𝟙  𝟙  ()
    𝟘 ω ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω ω ≤𝟙 𝟙  ≤ω ()
    𝟘 ω ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω ω ≤𝟙 ≤ω ≤ω ()
    𝟘 ω ω ≤ω 𝟘  𝟘  ()
    𝟘 ω ω ≤ω 𝟘  𝟙  ()
    𝟘 ω ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω ω ≤ω 𝟘  ≤ω ()
    𝟘 ω ω ≤ω 𝟙  𝟘  ()
    𝟘 ω ω ≤ω 𝟙  𝟙  ()
    𝟘 ω ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω ω ≤ω 𝟙  ≤ω ()
    𝟘 ω ω ≤ω ≤𝟙 𝟘  ()
    𝟘 ω ω ≤ω ≤𝟙 𝟙  ()
    𝟘 ω ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω ω ≤ω ≤𝟙 ≤ω ()
    𝟘 ω ω ≤ω ≤ω 𝟘  ()
    𝟘 ω ω ≤ω ≤ω 𝟙  ()
    𝟘 ω ω ≤ω ≤ω ≤𝟙 ()
    𝟘 ω ω ≤ω ≤ω ≤ω ()
    𝟙 𝟘 𝟘 𝟘  𝟘  𝟘  ()
    𝟙 𝟘 𝟘 𝟘  𝟘  𝟙  ()
    𝟙 𝟘 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 𝟘 𝟘  𝟙  𝟘  ()
    𝟙 𝟘 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 𝟘 𝟙  𝟘  𝟘  ()
    𝟙 𝟘 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 𝟘 𝟙 𝟘  𝟘  𝟘  ()
    𝟙 𝟘 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 𝟘 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 𝟘 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 𝟘 ω 𝟘  𝟘  𝟘  ()
    𝟙 𝟘 ω 𝟘  𝟘  𝟙  ()
    𝟙 𝟘 ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 ω 𝟘  𝟙  𝟘  ()
    𝟙 𝟘 ω 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 ω 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 ω 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 ω 𝟙  𝟘  𝟘  ()
    𝟙 𝟘 ω 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 ω 𝟙  𝟙  𝟘  ()
    𝟙 𝟘 ω 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 ω 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 ω 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 ω ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟘 ω ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 ω ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟘 ω ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 ω ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 ω ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 ω ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 ω ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 ω ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 ω ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 ω ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 ω ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 ω ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 ω ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 ω ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 ω ≤ω ≤ω ≤ω ()
    𝟙 𝟙 𝟘 𝟘  𝟘  𝟘  ()
    𝟙 𝟙 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 𝟘 𝟘  𝟙  𝟘  ()
    𝟙 𝟙 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 𝟘 𝟙  𝟘  𝟘  ()
    𝟙 𝟙 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 𝟙 𝟙 𝟘  𝟘  𝟘  ()
    𝟙 𝟙 𝟙 𝟘  𝟘  𝟙  ()
    𝟙 𝟙 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 𝟙 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 𝟙 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 𝟙 ω 𝟘  𝟘  𝟘  ()
    𝟙 𝟙 ω 𝟘  𝟘  𝟙  ()
    𝟙 𝟙 ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 ω 𝟘  𝟙  𝟘  ()
    𝟙 𝟙 ω 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 ω 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 ω 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 ω 𝟙  𝟘  𝟘  ()
    𝟙 𝟙 ω 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 ω 𝟙  𝟙  𝟘  ()
    𝟙 𝟙 ω 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 ω 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 ω 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 ω ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟙 ω ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 ω ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟙 ω ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 ω ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 ω ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 ω ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 ω ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 ω ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 ω ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 ω ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 ω ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 ω ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 ω ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 ω ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 ω ≤ω ≤ω ≤ω ()
    𝟙 ω 𝟘 𝟘  𝟘  𝟘  ()
    𝟙 ω 𝟘 𝟘  𝟘  𝟙  ()
    𝟙 ω 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 ω 𝟘 𝟘  𝟙  𝟘  ()
    𝟙 ω 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 ω 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 ω 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 ω 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 ω 𝟘 𝟙  𝟘  𝟘  ()
    𝟙 ω 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 ω 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 ω 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 ω 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 ω 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 ω 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 ω 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 ω 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 ω 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 ω 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 ω 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 ω 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 ω 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 ω 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 ω 𝟙 𝟘  𝟘  𝟘  ()
    𝟙 ω 𝟙 𝟘  𝟘  𝟙  ()
    𝟙 ω 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 ω 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 ω 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 ω 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 ω 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 ω 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 ω 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 ω 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 ω 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 ω 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 ω 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 ω 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 ω 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 ω 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 ω 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 ω 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 ω 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 ω 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 ω 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 ω 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 ω 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 ω ω 𝟘  𝟘  𝟘  ()
    𝟙 ω ω 𝟘  𝟘  𝟙  ()
    𝟙 ω ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω ω 𝟘  𝟘  ≤ω ()
    𝟙 ω ω 𝟘  𝟙  𝟘  ()
    𝟙 ω ω 𝟘  𝟙  𝟙  ()
    𝟙 ω ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω ω 𝟘  𝟙  ≤ω ()
    𝟙 ω ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 ω ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω ω 𝟘  ≤ω 𝟘  ()
    𝟙 ω ω 𝟘  ≤ω 𝟙  ()
    𝟙 ω ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω ω 𝟘  ≤ω ≤ω ()
    𝟙 ω ω 𝟙  𝟘  𝟘  ()
    𝟙 ω ω 𝟙  𝟘  𝟙  ()
    𝟙 ω ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω ω 𝟙  𝟘  ≤ω ()
    𝟙 ω ω 𝟙  𝟙  𝟘  ()
    𝟙 ω ω 𝟙  𝟙  𝟙  ()
    𝟙 ω ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω ω 𝟙  𝟙  ≤ω ()
    𝟙 ω ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 ω ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω ω 𝟙  ≤ω 𝟘  ()
    𝟙 ω ω 𝟙  ≤ω 𝟙  ()
    𝟙 ω ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω ω 𝟙  ≤ω ≤ω ()
    𝟙 ω ω ≤𝟙 𝟘  𝟘  ()
    𝟙 ω ω ≤𝟙 𝟘  𝟙  ()
    𝟙 ω ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω ω ≤𝟙 𝟘  ≤ω ()
    𝟙 ω ω ≤𝟙 𝟙  𝟘  ()
    𝟙 ω ω ≤𝟙 𝟙  𝟙  ()
    𝟙 ω ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω ω ≤𝟙 𝟙  ≤ω ()
    𝟙 ω ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 ω ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω ω ≤𝟙 ≤ω ≤ω ()
    𝟙 ω ω ≤ω 𝟘  𝟘  ()
    𝟙 ω ω ≤ω 𝟘  𝟙  ()
    𝟙 ω ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω ω ≤ω 𝟘  ≤ω ()
    𝟙 ω ω ≤ω 𝟙  𝟘  ()
    𝟙 ω ω ≤ω 𝟙  𝟙  ()
    𝟙 ω ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω ω ≤ω 𝟙  ≤ω ()
    𝟙 ω ω ≤ω ≤𝟙 𝟘  ()
    𝟙 ω ω ≤ω ≤𝟙 𝟙  ()
    𝟙 ω ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω ω ≤ω ≤𝟙 ≤ω ()
    𝟙 ω ω ≤ω ≤ω 𝟘  ()
    𝟙 ω ω ≤ω ≤ω 𝟙  ()
    𝟙 ω ω ≤ω ≤ω ≤𝟙 ()
    𝟙 ω ω ≤ω ≤ω ≤ω ()

  tr⁻¹-monotone : ∀ p q → p LA.≤ q → tr⁻¹ p L.≤ tr⁻¹ q
  tr⁻¹-monotone = λ where
    𝟘  𝟘  refl → refl
    𝟙  𝟙  refl → refl
    ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟙  refl → refl
    ≤𝟙 ≤𝟙 refl → refl
    ≤ω _  _    → refl

  tr-tr⁻¹≤ : ∀ p → tr′ (tr⁻¹ p) LA.≤ p
  tr-tr⁻¹≤ = λ where
    𝟘  → refl
    𝟙  → refl
    ≤𝟙 → refl
    ≤ω → refl

  tr≤→≤tr⁻¹ : ∀ p q → tr′ p LA.≤ q → p L.≤ tr⁻¹ q
  tr≤→≤tr⁻¹ = λ where
    𝟘 𝟘 refl → refl
    𝟙 𝟙 refl → refl
    ω _ _    → refl

  tr⁻¹-∧ : ∀ p q → tr⁻¹ (p LA.∧ q) ≡ tr⁻¹ p L.∧ tr⁻¹ q
  tr⁻¹-∧ = λ where
    𝟘  𝟘  → refl
    𝟘  𝟙  → refl
    𝟘  ≤𝟙 → refl
    𝟘  ≤ω → refl
    𝟙  𝟘  → refl
    𝟙  𝟙  → refl
    𝟙  ≤𝟙 → refl
    𝟙  ≤ω → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω _  → refl

  tr⁻¹-+ : ∀ p q → tr⁻¹ (p LA.+ q) ≡ tr⁻¹ p L.+ tr⁻¹ q
  tr⁻¹-+ = λ where
    𝟘  𝟘  → refl
    𝟘  𝟙  → refl
    𝟘  ≤𝟙 → refl
    𝟘  ≤ω → refl
    𝟙  𝟘  → refl
    𝟙  𝟙  → refl
    𝟙  ≤𝟙 → refl
    𝟙  ≤ω → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω 𝟘  → refl
    ≤ω 𝟙  → refl
    ≤ω ≤𝟙 → refl
    ≤ω ≤ω → refl

  tr⁻¹-· : ∀ p q → tr⁻¹ (tr′ p LA.· q) ≡ p L.· tr⁻¹ q
  tr⁻¹-· = λ where
    𝟘 𝟘  → refl
    𝟘 𝟙  → refl
    𝟘 ≤𝟙 → refl
    𝟘 ≤ω → refl
    𝟙 𝟘  → refl
    𝟙 𝟙  → refl
    𝟙 ≤𝟙 → refl
    𝟙 ≤ω → refl
    ω 𝟘  → refl
    ω 𝟙  → refl
    ω ≤𝟙 → refl
    ω ≤ω → refl

  tr-≤-no-nr :
    ∀ s →
    tr′ p LA.≤ q₁ →
    q₁ LA.≤ q₂ →
    (T (Modality-variant.𝟘ᵐ-allowed v₁) →
     q₁ LA.≤ q₃) →
    (Has-well-behaved-zero Linear-or-affine
       LA.linear-or-affine-semiring-with-meet →
     q₁ LA.≤ q₄) →
    q₁ LA.≤ q₃ LA.+ tr′ r LA.· q₄ LA.+ tr′ s LA.· q₁ →
    ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
       tr′ q₂′ LA.≤ q₂ ×
       tr′ q₃′ LA.≤ q₃ ×
       tr′ q₄′ LA.≤ q₄ ×
       p L.≤ q₁′ ×
       q₁′ L.≤ q₂′ ×
       (T (Modality-variant.𝟘ᵐ-allowed v₂) →
        q₁′ L.≤ q₃′) ×
       (Has-well-behaved-zero Linearity
          (Modality.semiring-with-meet (linearityModality v₂)) →
        q₁′ L.≤ q₄′) ×
       q₁′ L.≤ q₃′ L.+ r L.· q₄′ L.+ s L.· q₁′
  tr-≤-no-nr s = →tr-≤-no-nr {s = s}
    (linearityModality v₁)
    (linear-or-affine v₂)
    idᶠ
    (λ _ → LA.linear-or-affine-has-well-behaved-zero)
    tr′
    tr⁻¹
    tr⁻¹-monotone
    tr≤→≤tr⁻¹
    tr-tr⁻¹≤
    (λ p q → P₁.≤-reflexive (tr⁻¹-+ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-∧ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-· p q))

-- The function linear-or-affine→linearity is a morphism from a linear
-- or affine types modality to a linear types modality if certain
-- assumptions hold.

linear-or-affine⇨linearity :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = linear-or-affine v₁
      𝕄₂ = linearityModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ linear-or-affine→linearity
linear-or-affine⇨linearity {v₂ = v₂} refl s⇔s = λ where
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧                      → ≤-reflexive (tr-∧ _ _)
    .Is-morphism.tr-nr {r = r}             → ≤-reflexive
                                               (tr-nr _ r _ _ _)
    .Is-morphism.nr-in-first-iff-in-second → s⇔s
    .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
    .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
      (inj₁ ok) → inj₁ ok
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ LA.linear-or-affine-has-well-behaved-zero
  where
  open Graded.Modality.Properties (linearityModality v₂)

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

  tr-nr :
    ∀ p r z s n →
    tr′ (LA.nr p r z s n) ≡
    L.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘  𝟘  𝟘  𝟘  𝟘  → refl
    𝟘  𝟘  𝟘  𝟘  𝟙  → refl
    𝟘  𝟘  𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟘  𝟘  𝟘  ≤ω → refl
    𝟘  𝟘  𝟘  𝟙  𝟘  → refl
    𝟘  𝟘  𝟘  𝟙  𝟙  → refl
    𝟘  𝟘  𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟘  𝟘  𝟙  ≤ω → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟘  → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟙  → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤ω → refl
    𝟘  𝟘  𝟘  ≤ω 𝟘  → refl
    𝟘  𝟘  𝟘  ≤ω 𝟙  → refl
    𝟘  𝟘  𝟘  ≤ω ≤𝟙 → refl
    𝟘  𝟘  𝟘  ≤ω ≤ω → refl
    𝟘  𝟘  𝟙  𝟘  𝟘  → refl
    𝟘  𝟘  𝟙  𝟘  𝟙  → refl
    𝟘  𝟘  𝟙  𝟘  ≤𝟙 → refl
    𝟘  𝟘  𝟙  𝟘  ≤ω → refl
    𝟘  𝟘  𝟙  𝟙  𝟘  → refl
    𝟘  𝟘  𝟙  𝟙  𝟙  → refl
    𝟘  𝟘  𝟙  𝟙  ≤𝟙 → refl
    𝟘  𝟘  𝟙  𝟙  ≤ω → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟘  → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟙  → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤ω → refl
    𝟘  𝟘  𝟙  ≤ω 𝟘  → refl
    𝟘  𝟘  𝟙  ≤ω 𝟙  → refl
    𝟘  𝟘  𝟙  ≤ω ≤𝟙 → refl
    𝟘  𝟘  𝟙  ≤ω ≤ω → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟘  → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟙  → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤ω → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟘  → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟙  → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤ω → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟘  → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟙  → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤ω → refl
    𝟘  𝟘  ≤ω 𝟘  𝟘  → refl
    𝟘  𝟘  ≤ω 𝟘  𝟙  → refl
    𝟘  𝟘  ≤ω 𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤ω 𝟘  ≤ω → refl
    𝟘  𝟘  ≤ω 𝟙  𝟘  → refl
    𝟘  𝟘  ≤ω 𝟙  𝟙  → refl
    𝟘  𝟘  ≤ω 𝟙  ≤𝟙 → refl
    𝟘  𝟘  ≤ω 𝟙  ≤ω → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟘  → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟙  → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤ω → refl
    𝟘  𝟘  ≤ω ≤ω 𝟘  → refl
    𝟘  𝟘  ≤ω ≤ω 𝟙  → refl
    𝟘  𝟘  ≤ω ≤ω ≤𝟙 → refl
    𝟘  𝟘  ≤ω ≤ω ≤ω → refl
    𝟘  𝟙  𝟘  𝟘  𝟘  → refl
    𝟘  𝟙  𝟘  𝟘  𝟙  → refl
    𝟘  𝟙  𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟙  𝟘  𝟘  ≤ω → refl
    𝟘  𝟙  𝟘  𝟙  𝟘  → refl
    𝟘  𝟙  𝟘  𝟙  𝟙  → refl
    𝟘  𝟙  𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟙  𝟘  𝟙  ≤ω → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟘  → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟙  → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤ω → refl
    𝟘  𝟙  𝟘  ≤ω 𝟘  → refl
    𝟘  𝟙  𝟘  ≤ω 𝟙  → refl
    𝟘  𝟙  𝟘  ≤ω ≤𝟙 → refl
    𝟘  𝟙  𝟘  ≤ω ≤ω → refl
    𝟘  𝟙  𝟙  𝟘  𝟘  → refl
    𝟘  𝟙  𝟙  𝟘  𝟙  → refl
    𝟘  𝟙  𝟙  𝟘  ≤𝟙 → refl
    𝟘  𝟙  𝟙  𝟘  ≤ω → refl
    𝟘  𝟙  𝟙  𝟙  𝟘  → refl
    𝟘  𝟙  𝟙  𝟙  𝟙  → refl
    𝟘  𝟙  𝟙  𝟙  ≤𝟙 → refl
    𝟘  𝟙  𝟙  𝟙  ≤ω → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟘  → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟙  → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤ω → refl
    𝟘  𝟙  𝟙  ≤ω 𝟘  → refl
    𝟘  𝟙  𝟙  ≤ω 𝟙  → refl
    𝟘  𝟙  𝟙  ≤ω ≤𝟙 → refl
    𝟘  𝟙  𝟙  ≤ω ≤ω → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟘  → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟙  → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤ω → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟘  → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟙  → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤ω → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟘  → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟙  → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤ω → refl
    𝟘  𝟙  ≤ω 𝟘  𝟘  → refl
    𝟘  𝟙  ≤ω 𝟘  𝟙  → refl
    𝟘  𝟙  ≤ω 𝟘  ≤𝟙 → refl
    𝟘  𝟙  ≤ω 𝟘  ≤ω → refl
    𝟘  𝟙  ≤ω 𝟙  𝟘  → refl
    𝟘  𝟙  ≤ω 𝟙  𝟙  → refl
    𝟘  𝟙  ≤ω 𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤ω 𝟙  ≤ω → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟘  → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟙  → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤ω → refl
    𝟘  𝟙  ≤ω ≤ω 𝟘  → refl
    𝟘  𝟙  ≤ω ≤ω 𝟙  → refl
    𝟘  𝟙  ≤ω ≤ω ≤𝟙 → refl
    𝟘  𝟙  ≤ω ≤ω ≤ω → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟘  → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟙  → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤ω → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟘  → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟙  → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟘  → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟙  → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤ω → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟘  → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟙  → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤ω → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟘  → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟙  → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟘  → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟙  → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟘  → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟙  → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤ω → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟘  → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟙  → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤ω → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟘  → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟙  → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤ω → refl
    𝟘  ≤ω 𝟘  𝟘  𝟘  → refl
    𝟘  ≤ω 𝟘  𝟘  𝟙  → refl
    𝟘  ≤ω 𝟘  𝟘  ≤𝟙 → refl
    𝟘  ≤ω 𝟘  𝟘  ≤ω → refl
    𝟘  ≤ω 𝟘  𝟙  𝟘  → refl
    𝟘  ≤ω 𝟘  𝟙  𝟙  → refl
    𝟘  ≤ω 𝟘  𝟙  ≤𝟙 → refl
    𝟘  ≤ω 𝟘  𝟙  ≤ω → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟙  → refl
    𝟘  ≤ω 𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤ω 𝟘  ≤ω ≤ω → refl
    𝟘  ≤ω 𝟙  𝟘  𝟘  → refl
    𝟘  ≤ω 𝟙  𝟘  𝟙  → refl
    𝟘  ≤ω 𝟙  𝟘  ≤𝟙 → refl
    𝟘  ≤ω 𝟙  𝟘  ≤ω → refl
    𝟘  ≤ω 𝟙  𝟙  𝟘  → refl
    𝟘  ≤ω 𝟙  𝟙  𝟙  → refl
    𝟘  ≤ω 𝟙  𝟙  ≤𝟙 → refl
    𝟘  ≤ω 𝟙  𝟙  ≤ω → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟘  → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟙  → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟙  → refl
    𝟘  ≤ω 𝟙  ≤ω ≤𝟙 → refl
    𝟘  ≤ω 𝟙  ≤ω ≤ω → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟘  → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟙  → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤ω → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟘  → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟙  → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤ω → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟘  → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟙  → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤ω → refl
    𝟘  ≤ω ≤ω 𝟘  𝟘  → refl
    𝟘  ≤ω ≤ω 𝟘  𝟙  → refl
    𝟘  ≤ω ≤ω 𝟘  ≤𝟙 → refl
    𝟘  ≤ω ≤ω 𝟘  ≤ω → refl
    𝟘  ≤ω ≤ω 𝟙  𝟘  → refl
    𝟘  ≤ω ≤ω 𝟙  𝟙  → refl
    𝟘  ≤ω ≤ω 𝟙  ≤𝟙 → refl
    𝟘  ≤ω ≤ω 𝟙  ≤ω → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟘  → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟙  → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤ω → refl
    𝟘  ≤ω ≤ω ≤ω 𝟘  → refl
    𝟘  ≤ω ≤ω ≤ω 𝟙  → refl
    𝟘  ≤ω ≤ω ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤ω ≤ω ≤ω → refl
    𝟙  𝟘  𝟘  𝟘  𝟘  → refl
    𝟙  𝟘  𝟘  𝟘  𝟙  → refl
    𝟙  𝟘  𝟘  𝟘  ≤𝟙 → refl
    𝟙  𝟘  𝟘  𝟘  ≤ω → refl
    𝟙  𝟘  𝟘  𝟙  𝟘  → refl
    𝟙  𝟘  𝟘  𝟙  𝟙  → refl
    𝟙  𝟘  𝟘  𝟙  ≤𝟙 → refl
    𝟙  𝟘  𝟘  𝟙  ≤ω → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟘  → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟙  → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤ω → refl
    𝟙  𝟘  𝟘  ≤ω 𝟘  → refl
    𝟙  𝟘  𝟘  ≤ω 𝟙  → refl
    𝟙  𝟘  𝟘  ≤ω ≤𝟙 → refl
    𝟙  𝟘  𝟘  ≤ω ≤ω → refl
    𝟙  𝟘  𝟙  𝟘  𝟘  → refl
    𝟙  𝟘  𝟙  𝟘  𝟙  → refl
    𝟙  𝟘  𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟘  𝟙  𝟘  ≤ω → refl
    𝟙  𝟘  𝟙  𝟙  𝟘  → refl
    𝟙  𝟘  𝟙  𝟙  𝟙  → refl
    𝟙  𝟘  𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟘  𝟙  𝟙  ≤ω → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟘  → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟙  → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤ω → refl
    𝟙  𝟘  𝟙  ≤ω 𝟘  → refl
    𝟙  𝟘  𝟙  ≤ω 𝟙  → refl
    𝟙  𝟘  𝟙  ≤ω ≤𝟙 → refl
    𝟙  𝟘  𝟙  ≤ω ≤ω → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟘  → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟙  → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤ω → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟘  → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟙  → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤ω → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟘  → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟙  → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤ω → refl
    𝟙  𝟘  ≤ω 𝟘  𝟘  → refl
    𝟙  𝟘  ≤ω 𝟘  𝟙  → refl
    𝟙  𝟘  ≤ω 𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤ω 𝟘  ≤ω → refl
    𝟙  𝟘  ≤ω 𝟙  𝟘  → refl
    𝟙  𝟘  ≤ω 𝟙  𝟙  → refl
    𝟙  𝟘  ≤ω 𝟙  ≤𝟙 → refl
    𝟙  𝟘  ≤ω 𝟙  ≤ω → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟘  → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟙  → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤ω → refl
    𝟙  𝟘  ≤ω ≤ω 𝟘  → refl
    𝟙  𝟘  ≤ω ≤ω 𝟙  → refl
    𝟙  𝟘  ≤ω ≤ω ≤𝟙 → refl
    𝟙  𝟘  ≤ω ≤ω ≤ω → refl
    𝟙  𝟙  𝟘  𝟘  𝟘  → refl
    𝟙  𝟙  𝟘  𝟘  𝟙  → refl
    𝟙  𝟙  𝟘  𝟘  ≤𝟙 → refl
    𝟙  𝟙  𝟘  𝟘  ≤ω → refl
    𝟙  𝟙  𝟘  𝟙  𝟘  → refl
    𝟙  𝟙  𝟘  𝟙  𝟙  → refl
    𝟙  𝟙  𝟘  𝟙  ≤𝟙 → refl
    𝟙  𝟙  𝟘  𝟙  ≤ω → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟘  → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟙  → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤ω → refl
    𝟙  𝟙  𝟘  ≤ω 𝟘  → refl
    𝟙  𝟙  𝟘  ≤ω 𝟙  → refl
    𝟙  𝟙  𝟘  ≤ω ≤𝟙 → refl
    𝟙  𝟙  𝟘  ≤ω ≤ω → refl
    𝟙  𝟙  𝟙  𝟘  𝟘  → refl
    𝟙  𝟙  𝟙  𝟘  𝟙  → refl
    𝟙  𝟙  𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟙  𝟙  𝟘  ≤ω → refl
    𝟙  𝟙  𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  𝟙  𝟙  ≤ω → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟘  → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟙  → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤ω → refl
    𝟙  𝟙  𝟙  ≤ω 𝟘  → refl
    𝟙  𝟙  𝟙  ≤ω 𝟙  → refl
    𝟙  𝟙  𝟙  ≤ω ≤𝟙 → refl
    𝟙  𝟙  𝟙  ≤ω ≤ω → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟘  → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟙  → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤ω → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟘  → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤ω → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟘  → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟙  → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤ω → refl
    𝟙  𝟙  ≤ω 𝟘  𝟘  → refl
    𝟙  𝟙  ≤ω 𝟘  𝟙  → refl
    𝟙  𝟙  ≤ω 𝟘  ≤𝟙 → refl
    𝟙  𝟙  ≤ω 𝟘  ≤ω → refl
    𝟙  𝟙  ≤ω 𝟙  𝟘  → refl
    𝟙  𝟙  ≤ω 𝟙  𝟙  → refl
    𝟙  𝟙  ≤ω 𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω 𝟙  ≤ω → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟘  → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟙  → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤ω → refl
    𝟙  𝟙  ≤ω ≤ω 𝟘  → refl
    𝟙  𝟙  ≤ω ≤ω 𝟙  → refl
    𝟙  𝟙  ≤ω ≤ω ≤𝟙 → refl
    𝟙  𝟙  ≤ω ≤ω ≤ω → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟘  → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟙  → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤ω → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟘  → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟙  → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟘  → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟙  → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤ω → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟘  → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟙  → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤ω → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟘  → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟙  → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟘  → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟙  → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟘  → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟙  → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤ω → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟘  → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟙  → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤ω → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟘  → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟙  → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤ω → refl
    𝟙  ≤ω 𝟘  𝟘  𝟘  → refl
    𝟙  ≤ω 𝟘  𝟘  𝟙  → refl
    𝟙  ≤ω 𝟘  𝟘  ≤𝟙 → refl
    𝟙  ≤ω 𝟘  𝟘  ≤ω → refl
    𝟙  ≤ω 𝟘  𝟙  𝟘  → refl
    𝟙  ≤ω 𝟘  𝟙  𝟙  → refl
    𝟙  ≤ω 𝟘  𝟙  ≤𝟙 → refl
    𝟙  ≤ω 𝟘  𝟙  ≤ω → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟘  → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟙  → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟙  → refl
    𝟙  ≤ω 𝟘  ≤ω ≤𝟙 → refl
    𝟙  ≤ω 𝟘  ≤ω ≤ω → refl
    𝟙  ≤ω 𝟙  𝟘  𝟘  → refl
    𝟙  ≤ω 𝟙  𝟘  𝟙  → refl
    𝟙  ≤ω 𝟙  𝟘  ≤𝟙 → refl
    𝟙  ≤ω 𝟙  𝟘  ≤ω → refl
    𝟙  ≤ω 𝟙  𝟙  𝟘  → refl
    𝟙  ≤ω 𝟙  𝟙  𝟙  → refl
    𝟙  ≤ω 𝟙  𝟙  ≤𝟙 → refl
    𝟙  ≤ω 𝟙  𝟙  ≤ω → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω 𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω 𝟙  ≤ω ≤ω → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟘  → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟙  → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤ω → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟘  → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟙  → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤ω → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟘  → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤ω → refl
    𝟙  ≤ω ≤ω 𝟘  𝟘  → refl
    𝟙  ≤ω ≤ω 𝟘  𝟙  → refl
    𝟙  ≤ω ≤ω 𝟘  ≤𝟙 → refl
    𝟙  ≤ω ≤ω 𝟘  ≤ω → refl
    𝟙  ≤ω ≤ω 𝟙  𝟘  → refl
    𝟙  ≤ω ≤ω 𝟙  𝟙  → refl
    𝟙  ≤ω ≤ω 𝟙  ≤𝟙 → refl
    𝟙  ≤ω ≤ω 𝟙  ≤ω → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟘  → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟙  → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤ω → refl
    𝟙  ≤ω ≤ω ≤ω 𝟘  → refl
    𝟙  ≤ω ≤ω ≤ω 𝟙  → refl
    𝟙  ≤ω ≤ω ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟙  → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤ω → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟘  → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟙  → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤ω → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟘  → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟙  → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟙  → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤ω → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟘  → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟙  → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤ω → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟘  → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟙  → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟘  → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤ω → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟘  → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟙  → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤ω → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟘  → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟙  → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤ω → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟘  → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟙  → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟙  → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤ω → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟘  → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟙  → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤ω → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟘  → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟙  → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟙  → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤ω → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟘  → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟙  → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟘  → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟙  → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤ω → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟘  → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤ω → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟘  → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟙  → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤ω → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟘  → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟙  → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤ω → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟘  → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟙  → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤ω → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟙  → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤ω → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟘  → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟙  → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤ω → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟘  → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟙  → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤ω → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟙  → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟘  → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟙  → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤ω → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟘  → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟙  → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤ω → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟘  → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤ω → refl
    ≤ω 𝟘  𝟘  𝟘  𝟘  → refl
    ≤ω 𝟘  𝟘  𝟘  𝟙  → refl
    ≤ω 𝟘  𝟘  𝟘  ≤𝟙 → refl
    ≤ω 𝟘  𝟘  𝟘  ≤ω → refl
    ≤ω 𝟘  𝟘  𝟙  𝟘  → refl
    ≤ω 𝟘  𝟘  𝟙  𝟙  → refl
    ≤ω 𝟘  𝟘  𝟙  ≤𝟙 → refl
    ≤ω 𝟘  𝟘  𝟙  ≤ω → refl
    ≤ω 𝟘  𝟘  ≤𝟙 𝟘  → refl
    ≤ω 𝟘  𝟘  ≤𝟙 𝟙  → refl
    ≤ω 𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  𝟘  ≤𝟙 ≤ω → refl
    ≤ω 𝟘  𝟘  ≤ω 𝟘  → refl
    ≤ω 𝟘  𝟘  ≤ω 𝟙  → refl
    ≤ω 𝟘  𝟘  ≤ω ≤𝟙 → refl
    ≤ω 𝟘  𝟘  ≤ω ≤ω → refl
    ≤ω 𝟘  𝟙  𝟘  𝟘  → refl
    ≤ω 𝟘  𝟙  𝟘  𝟙  → refl
    ≤ω 𝟘  𝟙  𝟘  ≤𝟙 → refl
    ≤ω 𝟘  𝟙  𝟘  ≤ω → refl
    ≤ω 𝟘  𝟙  𝟙  𝟘  → refl
    ≤ω 𝟘  𝟙  𝟙  𝟙  → refl
    ≤ω 𝟘  𝟙  𝟙  ≤𝟙 → refl
    ≤ω 𝟘  𝟙  𝟙  ≤ω → refl
    ≤ω 𝟘  𝟙  ≤𝟙 𝟘  → refl
    ≤ω 𝟘  𝟙  ≤𝟙 𝟙  → refl
    ≤ω 𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  𝟙  ≤𝟙 ≤ω → refl
    ≤ω 𝟘  𝟙  ≤ω 𝟘  → refl
    ≤ω 𝟘  𝟙  ≤ω 𝟙  → refl
    ≤ω 𝟘  𝟙  ≤ω ≤𝟙 → refl
    ≤ω 𝟘  𝟙  ≤ω ≤ω → refl
    ≤ω 𝟘  ≤𝟙 𝟘  𝟘  → refl
    ≤ω 𝟘  ≤𝟙 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 𝟘  ≤ω → refl
    ≤ω 𝟘  ≤𝟙 𝟙  𝟘  → refl
    ≤ω 𝟘  ≤𝟙 𝟙  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 𝟙  ≤ω → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω 𝟘  ≤𝟙 ≤ω 𝟘  → refl
    ≤ω 𝟘  ≤𝟙 ≤ω 𝟙  → refl
    ≤ω 𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟘  ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟘  ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟘  ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟘  ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω 𝟙  ≤ω → refl
    ≤ω 𝟘  ≤ω ≤𝟙 𝟘  → refl
    ≤ω 𝟘  ≤ω ≤𝟙 𝟙  → refl
    ≤ω 𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  ≤ω ≤𝟙 ≤ω → refl
    ≤ω 𝟘  ≤ω ≤ω 𝟘  → refl
    ≤ω 𝟘  ≤ω ≤ω 𝟙  → refl
    ≤ω 𝟘  ≤ω ≤ω ≤𝟙 → refl
    ≤ω 𝟘  ≤ω ≤ω ≤ω → refl
    ≤ω 𝟙  𝟘  𝟘  𝟘  → refl
    ≤ω 𝟙  𝟘  𝟘  𝟙  → refl
    ≤ω 𝟙  𝟘  𝟘  ≤𝟙 → refl
    ≤ω 𝟙  𝟘  𝟘  ≤ω → refl
    ≤ω 𝟙  𝟘  𝟙  𝟘  → refl
    ≤ω 𝟙  𝟘  𝟙  𝟙  → refl
    ≤ω 𝟙  𝟘  𝟙  ≤𝟙 → refl
    ≤ω 𝟙  𝟘  𝟙  ≤ω → refl
    ≤ω 𝟙  𝟘  ≤𝟙 𝟘  → refl
    ≤ω 𝟙  𝟘  ≤𝟙 𝟙  → refl
    ≤ω 𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  𝟘  ≤𝟙 ≤ω → refl
    ≤ω 𝟙  𝟘  ≤ω 𝟘  → refl
    ≤ω 𝟙  𝟘  ≤ω 𝟙  → refl
    ≤ω 𝟙  𝟘  ≤ω ≤𝟙 → refl
    ≤ω 𝟙  𝟘  ≤ω ≤ω → refl
    ≤ω 𝟙  𝟙  𝟘  𝟘  → refl
    ≤ω 𝟙  𝟙  𝟘  𝟙  → refl
    ≤ω 𝟙  𝟙  𝟘  ≤𝟙 → refl
    ≤ω 𝟙  𝟙  𝟘  ≤ω → refl
    ≤ω 𝟙  𝟙  𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  𝟙  𝟙  → refl
    ≤ω 𝟙  𝟙  𝟙  ≤𝟙 → refl
    ≤ω 𝟙  𝟙  𝟙  ≤ω → refl
    ≤ω 𝟙  𝟙  ≤𝟙 𝟘  → refl
    ≤ω 𝟙  𝟙  ≤𝟙 𝟙  → refl
    ≤ω 𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  𝟙  ≤𝟙 ≤ω → refl
    ≤ω 𝟙  𝟙  ≤ω 𝟘  → refl
    ≤ω 𝟙  𝟙  ≤ω 𝟙  → refl
    ≤ω 𝟙  𝟙  ≤ω ≤𝟙 → refl
    ≤ω 𝟙  𝟙  ≤ω ≤ω → refl
    ≤ω 𝟙  ≤𝟙 𝟘  𝟘  → refl
    ≤ω 𝟙  ≤𝟙 𝟘  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 𝟘  ≤ω → refl
    ≤ω 𝟙  ≤𝟙 𝟙  𝟘  → refl
    ≤ω 𝟙  ≤𝟙 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 𝟙  ≤ω → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω 𝟙  ≤𝟙 ≤ω 𝟘  → refl
    ≤ω 𝟙  ≤𝟙 ≤ω 𝟙  → refl
    ≤ω 𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟙  ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟙  ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟙  ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟙  ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω 𝟙  ≤ω → refl
    ≤ω 𝟙  ≤ω ≤𝟙 𝟘  → refl
    ≤ω 𝟙  ≤ω ≤𝟙 𝟙  → refl
    ≤ω 𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  ≤ω ≤𝟙 ≤ω → refl
    ≤ω 𝟙  ≤ω ≤ω 𝟘  → refl
    ≤ω 𝟙  ≤ω ≤ω 𝟙  → refl
    ≤ω 𝟙  ≤ω ≤ω ≤𝟙 → refl
    ≤ω 𝟙  ≤ω ≤ω ≤ω → refl
    ≤ω ≤𝟙 𝟘  𝟘  𝟘  → refl
    ≤ω ≤𝟙 𝟘  𝟘  𝟙  → refl
    ≤ω ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  𝟘  ≤ω → refl
    ≤ω ≤𝟙 𝟘  𝟙  𝟘  → refl
    ≤ω ≤𝟙 𝟘  𝟙  𝟙  → refl
    ≤ω ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 𝟘  ≤ω 𝟘  → refl
    ≤ω ≤𝟙 𝟘  ≤ω 𝟙  → refl
    ≤ω ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  ≤ω ≤ω → refl
    ≤ω ≤𝟙 𝟙  𝟘  𝟘  → refl
    ≤ω ≤𝟙 𝟙  𝟘  𝟙  → refl
    ≤ω ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  𝟘  ≤ω → refl
    ≤ω ≤𝟙 𝟙  𝟙  𝟘  → refl
    ≤ω ≤𝟙 𝟙  𝟙  𝟙  → refl
    ≤ω ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 𝟙  ≤ω 𝟘  → refl
    ≤ω ≤𝟙 𝟙  ≤ω 𝟙  → refl
    ≤ω ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  ≤ω ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    ≤ω ≤𝟙 ≤ω 𝟘  𝟘  → refl
    ≤ω ≤𝟙 ≤ω 𝟘  𝟙  → refl
    ≤ω ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω 𝟘  ≤ω → refl
    ≤ω ≤𝟙 ≤ω 𝟙  𝟘  → refl
    ≤ω ≤𝟙 ≤ω 𝟙  𝟙  → refl
    ≤ω ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 ≤ω ≤ω 𝟘  → refl
    ≤ω ≤𝟙 ≤ω ≤ω 𝟙  → refl
    ≤ω ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω ≤ω ≤ω → refl
    ≤ω ≤ω 𝟘  𝟘  𝟘  → refl
    ≤ω ≤ω 𝟘  𝟘  𝟙  → refl
    ≤ω ≤ω 𝟘  𝟘  ≤𝟙 → refl
    ≤ω ≤ω 𝟘  𝟘  ≤ω → refl
    ≤ω ≤ω 𝟘  𝟙  𝟘  → refl
    ≤ω ≤ω 𝟘  𝟙  𝟙  → refl
    ≤ω ≤ω 𝟘  𝟙  ≤𝟙 → refl
    ≤ω ≤ω 𝟘  𝟙  ≤ω → refl
    ≤ω ≤ω 𝟘  ≤𝟙 𝟘  → refl
    ≤ω ≤ω 𝟘  ≤𝟙 𝟙  → refl
    ≤ω ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω 𝟘  ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟘  ≤ω 𝟙  → refl
    ≤ω ≤ω 𝟘  ≤ω ≤𝟙 → refl
    ≤ω ≤ω 𝟘  ≤ω ≤ω → refl
    ≤ω ≤ω 𝟙  𝟘  𝟘  → refl
    ≤ω ≤ω 𝟙  𝟘  𝟙  → refl
    ≤ω ≤ω 𝟙  𝟘  ≤𝟙 → refl
    ≤ω ≤ω 𝟙  𝟘  ≤ω → refl
    ≤ω ≤ω 𝟙  𝟙  𝟘  → refl
    ≤ω ≤ω 𝟙  𝟙  𝟙  → refl
    ≤ω ≤ω 𝟙  𝟙  ≤𝟙 → refl
    ≤ω ≤ω 𝟙  𝟙  ≤ω → refl
    ≤ω ≤ω 𝟙  ≤𝟙 𝟘  → refl
    ≤ω ≤ω 𝟙  ≤𝟙 𝟙  → refl
    ≤ω ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω 𝟙  ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟙  ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  ≤ω 𝟙  → refl
    ≤ω ≤ω 𝟙  ≤ω ≤𝟙 → refl
    ≤ω ≤ω 𝟙  ≤ω ≤ω → refl
    ≤ω ≤ω ≤𝟙 𝟘  𝟘  → refl
    ≤ω ≤ω ≤𝟙 𝟘  𝟙  → refl
    ≤ω ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 𝟘  ≤ω → refl
    ≤ω ≤ω ≤𝟙 𝟙  𝟘  → refl
    ≤ω ≤ω ≤𝟙 𝟙  𝟙  → refl
    ≤ω ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 𝟙  ≤ω → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω ≤ω ≤𝟙 ≤ω 𝟘  → refl
    ≤ω ≤ω ≤𝟙 ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 ≤ω ≤ω → refl
    ≤ω ≤ω ≤ω 𝟘  𝟘  → refl
    ≤ω ≤ω ≤ω 𝟘  𝟙  → refl
    ≤ω ≤ω ≤ω 𝟘  ≤𝟙 → refl
    ≤ω ≤ω ≤ω 𝟘  ≤ω → refl
    ≤ω ≤ω ≤ω 𝟙  𝟘  → refl
    ≤ω ≤ω ≤ω 𝟙  𝟙  → refl
    ≤ω ≤ω ≤ω 𝟙  ≤𝟙 → refl
    ≤ω ≤ω ≤ω 𝟙  ≤ω → refl
    ≤ω ≤ω ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤ω ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω ≤ω ≤ω → refl

-- The function linear-or-affine→linearity is not an order embedding
-- from a linear or affine types modality to a linear types modality.

¬linear-or-affine⇨linearity :
  ¬ Is-order-embedding (linear-or-affine v₁) (linearityModality v₂)
      linear-or-affine→linearity
¬linear-or-affine⇨linearity m =
  case Is-order-embedding.tr-injective m {p = ≤𝟙} {q = ≤ω} refl of λ ()

-- The function affine→linear-or-affine is an order embedding from an
-- affine types modality to a linear or affine types modality if
-- certain assumptions hold.

affine⇨linear-or-affine :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = affineModality v₁
      𝕄₂ = linear-or-affine v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ affine→linear-or-affine
affine⇨linear-or-affine {v₁ = v₁} {v₂ = v₂} refl s⇔s = λ where
    .Is-order-embedding.trivial not-ok ok   → ⊥-elim (not-ok ok)
    .Is-order-embedding.trivial-⊎-tr-𝟘      → inj₂ refl
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-≤-nr {r = r}     → tr-≤-nr _ _ r _ _ _
    .Is-order-embedding.tr-≤-no-nr {s = s}  → tr-≤-no-nr s
    .Is-order-embedding.tr-order-reflecting → tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism         → λ where
      .Is-morphism.tr-𝟘-≤                    → refl
      .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                             , λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                      → refl
      .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-·                      → tr-· _ _
      .Is-morphism.tr-∧                      → ≤-reflexive (tr-∧ _ _)
      .Is-morphism.tr-nr {r = r}             → ≤-reflexive
                                                 (tr-nr _ r _ _ _)
      .Is-morphism.nr-in-first-iff-in-second → s⇔s
      .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
      .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
        (inj₁ ok) → inj₁ ok
      .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ (A.affine-has-well-behaved-zero v₁)
  where
  module P₁ = Graded.Modality.Properties (affineModality v₁)
  open Graded.Modality.Properties (linear-or-affine v₂)

  tr′  = affine→linear-or-affine
  tr⁻¹ = linear-or-affine→affine

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

  tr-nr :
    ∀ p r z s n →
    tr′ (A.nr p r z s n) ≡
    LA.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘 𝟘 𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟘 𝟘 𝟙 → refl
    𝟘 𝟘 𝟘 𝟘 ω → refl
    𝟘 𝟘 𝟘 𝟙 𝟘 → refl
    𝟘 𝟘 𝟘 𝟙 𝟙 → refl
    𝟘 𝟘 𝟘 𝟙 ω → refl
    𝟘 𝟘 𝟘 ω 𝟘 → refl
    𝟘 𝟘 𝟘 ω 𝟙 → refl
    𝟘 𝟘 𝟘 ω ω → refl
    𝟘 𝟘 𝟙 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 𝟘 𝟙 → refl
    𝟘 𝟘 𝟙 𝟘 ω → refl
    𝟘 𝟘 𝟙 𝟙 𝟘 → refl
    𝟘 𝟘 𝟙 𝟙 𝟙 → refl
    𝟘 𝟘 𝟙 𝟙 ω → refl
    𝟘 𝟘 𝟙 ω 𝟘 → refl
    𝟘 𝟘 𝟙 ω 𝟙 → refl
    𝟘 𝟘 𝟙 ω ω → refl
    𝟘 𝟘 ω 𝟘 𝟘 → refl
    𝟘 𝟘 ω 𝟘 𝟙 → refl
    𝟘 𝟘 ω 𝟘 ω → refl
    𝟘 𝟘 ω 𝟙 𝟘 → refl
    𝟘 𝟘 ω 𝟙 𝟙 → refl
    𝟘 𝟘 ω 𝟙 ω → refl
    𝟘 𝟘 ω ω 𝟘 → refl
    𝟘 𝟘 ω ω 𝟙 → refl
    𝟘 𝟘 ω ω ω → refl
    𝟘 𝟙 𝟘 𝟘 𝟘 → refl
    𝟘 𝟙 𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 𝟘 ω → refl
    𝟘 𝟙 𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟘 𝟙 𝟙 → refl
    𝟘 𝟙 𝟘 𝟙 ω → refl
    𝟘 𝟙 𝟘 ω 𝟘 → refl
    𝟘 𝟙 𝟘 ω 𝟙 → refl
    𝟘 𝟙 𝟘 ω ω → refl
    𝟘 𝟙 𝟙 𝟘 𝟘 → refl
    𝟘 𝟙 𝟙 𝟘 𝟙 → refl
    𝟘 𝟙 𝟙 𝟘 ω → refl
    𝟘 𝟙 𝟙 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 𝟙 ω → refl
    𝟘 𝟙 𝟙 ω 𝟘 → refl
    𝟘 𝟙 𝟙 ω 𝟙 → refl
    𝟘 𝟙 𝟙 ω ω → refl
    𝟘 𝟙 ω 𝟘 𝟘 → refl
    𝟘 𝟙 ω 𝟘 𝟙 → refl
    𝟘 𝟙 ω 𝟘 ω → refl
    𝟘 𝟙 ω 𝟙 𝟘 → refl
    𝟘 𝟙 ω 𝟙 𝟙 → refl
    𝟘 𝟙 ω 𝟙 ω → refl
    𝟘 𝟙 ω ω 𝟘 → refl
    𝟘 𝟙 ω ω 𝟙 → refl
    𝟘 𝟙 ω ω ω → refl
    𝟘 ω 𝟘 𝟘 𝟘 → refl
    𝟘 ω 𝟘 𝟘 𝟙 → refl
    𝟘 ω 𝟘 𝟘 ω → refl
    𝟘 ω 𝟘 𝟙 𝟘 → refl
    𝟘 ω 𝟘 𝟙 𝟙 → refl
    𝟘 ω 𝟘 𝟙 ω → refl
    𝟘 ω 𝟘 ω 𝟘 → refl
    𝟘 ω 𝟘 ω 𝟙 → refl
    𝟘 ω 𝟘 ω ω → refl
    𝟘 ω 𝟙 𝟘 𝟘 → refl
    𝟘 ω 𝟙 𝟘 𝟙 → refl
    𝟘 ω 𝟙 𝟘 ω → refl
    𝟘 ω 𝟙 𝟙 𝟘 → refl
    𝟘 ω 𝟙 𝟙 𝟙 → refl
    𝟘 ω 𝟙 𝟙 ω → refl
    𝟘 ω 𝟙 ω 𝟘 → refl
    𝟘 ω 𝟙 ω 𝟙 → refl
    𝟘 ω 𝟙 ω ω → refl
    𝟘 ω ω 𝟘 𝟘 → refl
    𝟘 ω ω 𝟘 𝟙 → refl
    𝟘 ω ω 𝟘 ω → refl
    𝟘 ω ω 𝟙 𝟘 → refl
    𝟘 ω ω 𝟙 𝟙 → refl
    𝟘 ω ω 𝟙 ω → refl
    𝟘 ω ω ω 𝟘 → refl
    𝟘 ω ω ω 𝟙 → refl
    𝟘 ω ω ω ω → refl
    𝟙 𝟘 𝟘 𝟘 𝟘 → refl
    𝟙 𝟘 𝟘 𝟘 𝟙 → refl
    𝟙 𝟘 𝟘 𝟘 ω → refl
    𝟙 𝟘 𝟘 𝟙 𝟘 → refl
    𝟙 𝟘 𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 𝟙 ω → refl
    𝟙 𝟘 𝟘 ω 𝟘 → refl
    𝟙 𝟘 𝟘 ω 𝟙 → refl
    𝟙 𝟘 𝟘 ω ω → refl
    𝟙 𝟘 𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 𝟘 𝟙 → refl
    𝟙 𝟘 𝟙 𝟘 ω → refl
    𝟙 𝟘 𝟙 𝟙 𝟘 → refl
    𝟙 𝟘 𝟙 𝟙 𝟙 → refl
    𝟙 𝟘 𝟙 𝟙 ω → refl
    𝟙 𝟘 𝟙 ω 𝟘 → refl
    𝟙 𝟘 𝟙 ω 𝟙 → refl
    𝟙 𝟘 𝟙 ω ω → refl
    𝟙 𝟘 ω 𝟘 𝟘 → refl
    𝟙 𝟘 ω 𝟘 𝟙 → refl
    𝟙 𝟘 ω 𝟘 ω → refl
    𝟙 𝟘 ω 𝟙 𝟘 → refl
    𝟙 𝟘 ω 𝟙 𝟙 → refl
    𝟙 𝟘 ω 𝟙 ω → refl
    𝟙 𝟘 ω ω 𝟘 → refl
    𝟙 𝟘 ω ω 𝟙 → refl
    𝟙 𝟘 ω ω ω → refl
    𝟙 𝟙 𝟘 𝟘 𝟘 → refl
    𝟙 𝟙 𝟘 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 𝟘 ω → refl
    𝟙 𝟙 𝟘 𝟙 𝟘 → refl
    𝟙 𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟙 𝟘 𝟙 ω → refl
    𝟙 𝟙 𝟘 ω 𝟘 → refl
    𝟙 𝟙 𝟘 ω 𝟙 → refl
    𝟙 𝟙 𝟘 ω ω → refl
    𝟙 𝟙 𝟙 𝟘 𝟘 → refl
    𝟙 𝟙 𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 𝟙 𝟙 ω → refl
    𝟙 𝟙 𝟙 ω 𝟘 → refl
    𝟙 𝟙 𝟙 ω 𝟙 → refl
    𝟙 𝟙 𝟙 ω ω → refl
    𝟙 𝟙 ω 𝟘 𝟘 → refl
    𝟙 𝟙 ω 𝟘 𝟙 → refl
    𝟙 𝟙 ω 𝟘 ω → refl
    𝟙 𝟙 ω 𝟙 𝟘 → refl
    𝟙 𝟙 ω 𝟙 𝟙 → refl
    𝟙 𝟙 ω 𝟙 ω → refl
    𝟙 𝟙 ω ω 𝟘 → refl
    𝟙 𝟙 ω ω 𝟙 → refl
    𝟙 𝟙 ω ω ω → refl
    𝟙 ω 𝟘 𝟘 𝟘 → refl
    𝟙 ω 𝟘 𝟘 𝟙 → refl
    𝟙 ω 𝟘 𝟘 ω → refl
    𝟙 ω 𝟘 𝟙 𝟘 → refl
    𝟙 ω 𝟘 𝟙 𝟙 → refl
    𝟙 ω 𝟘 𝟙 ω → refl
    𝟙 ω 𝟘 ω 𝟘 → refl
    𝟙 ω 𝟘 ω 𝟙 → refl
    𝟙 ω 𝟘 ω ω → refl
    𝟙 ω 𝟙 𝟘 𝟘 → refl
    𝟙 ω 𝟙 𝟘 𝟙 → refl
    𝟙 ω 𝟙 𝟘 ω → refl
    𝟙 ω 𝟙 𝟙 𝟘 → refl
    𝟙 ω 𝟙 𝟙 𝟙 → refl
    𝟙 ω 𝟙 𝟙 ω → refl
    𝟙 ω 𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 ω 𝟙 → refl
    𝟙 ω 𝟙 ω ω → refl
    𝟙 ω ω 𝟘 𝟘 → refl
    𝟙 ω ω 𝟘 𝟙 → refl
    𝟙 ω ω 𝟘 ω → refl
    𝟙 ω ω 𝟙 𝟘 → refl
    𝟙 ω ω 𝟙 𝟙 → refl
    𝟙 ω ω 𝟙 ω → refl
    𝟙 ω ω ω 𝟘 → refl
    𝟙 ω ω ω 𝟙 → refl
    𝟙 ω ω ω ω → refl
    ω 𝟘 𝟘 𝟘 𝟘 → refl
    ω 𝟘 𝟘 𝟘 𝟙 → refl
    ω 𝟘 𝟘 𝟘 ω → refl
    ω 𝟘 𝟘 𝟙 𝟘 → refl
    ω 𝟘 𝟘 𝟙 𝟙 → refl
    ω 𝟘 𝟘 𝟙 ω → refl
    ω 𝟘 𝟘 ω 𝟘 → refl
    ω 𝟘 𝟘 ω 𝟙 → refl
    ω 𝟘 𝟘 ω ω → refl
    ω 𝟘 𝟙 𝟘 𝟘 → refl
    ω 𝟘 𝟙 𝟘 𝟙 → refl
    ω 𝟘 𝟙 𝟘 ω → refl
    ω 𝟘 𝟙 𝟙 𝟘 → refl
    ω 𝟘 𝟙 𝟙 𝟙 → refl
    ω 𝟘 𝟙 𝟙 ω → refl
    ω 𝟘 𝟙 ω 𝟘 → refl
    ω 𝟘 𝟙 ω 𝟙 → refl
    ω 𝟘 𝟙 ω ω → refl
    ω 𝟘 ω 𝟘 𝟘 → refl
    ω 𝟘 ω 𝟘 𝟙 → refl
    ω 𝟘 ω 𝟘 ω → refl
    ω 𝟘 ω 𝟙 𝟘 → refl
    ω 𝟘 ω 𝟙 𝟙 → refl
    ω 𝟘 ω 𝟙 ω → refl
    ω 𝟘 ω ω 𝟘 → refl
    ω 𝟘 ω ω 𝟙 → refl
    ω 𝟘 ω ω ω → refl
    ω 𝟙 𝟘 𝟘 𝟘 → refl
    ω 𝟙 𝟘 𝟘 𝟙 → refl
    ω 𝟙 𝟘 𝟘 ω → refl
    ω 𝟙 𝟘 𝟙 𝟘 → refl
    ω 𝟙 𝟘 𝟙 𝟙 → refl
    ω 𝟙 𝟘 𝟙 ω → refl
    ω 𝟙 𝟘 ω 𝟘 → refl
    ω 𝟙 𝟘 ω 𝟙 → refl
    ω 𝟙 𝟘 ω ω → refl
    ω 𝟙 𝟙 𝟘 𝟘 → refl
    ω 𝟙 𝟙 𝟘 𝟙 → refl
    ω 𝟙 𝟙 𝟘 ω → refl
    ω 𝟙 𝟙 𝟙 𝟘 → refl
    ω 𝟙 𝟙 𝟙 𝟙 → refl
    ω 𝟙 𝟙 𝟙 ω → refl
    ω 𝟙 𝟙 ω 𝟘 → refl
    ω 𝟙 𝟙 ω 𝟙 → refl
    ω 𝟙 𝟙 ω ω → refl
    ω 𝟙 ω 𝟘 𝟘 → refl
    ω 𝟙 ω 𝟘 𝟙 → refl
    ω 𝟙 ω 𝟘 ω → refl
    ω 𝟙 ω 𝟙 𝟘 → refl
    ω 𝟙 ω 𝟙 𝟙 → refl
    ω 𝟙 ω 𝟙 ω → refl
    ω 𝟙 ω ω 𝟘 → refl
    ω 𝟙 ω ω 𝟙 → refl
    ω 𝟙 ω ω ω → refl
    ω ω 𝟘 𝟘 𝟘 → refl
    ω ω 𝟘 𝟘 𝟙 → refl
    ω ω 𝟘 𝟘 ω → refl
    ω ω 𝟘 𝟙 𝟘 → refl
    ω ω 𝟘 𝟙 𝟙 → refl
    ω ω 𝟘 𝟙 ω → refl
    ω ω 𝟘 ω 𝟘 → refl
    ω ω 𝟘 ω 𝟙 → refl
    ω ω 𝟘 ω ω → refl
    ω ω 𝟙 𝟘 𝟘 → refl
    ω ω 𝟙 𝟘 𝟙 → refl
    ω ω 𝟙 𝟘 ω → refl
    ω ω 𝟙 𝟙 𝟘 → refl
    ω ω 𝟙 𝟙 𝟙 → refl
    ω ω 𝟙 𝟙 ω → refl
    ω ω 𝟙 ω 𝟘 → refl
    ω ω 𝟙 ω 𝟙 → refl
    ω ω 𝟙 ω ω → refl
    ω ω ω 𝟘 𝟘 → refl
    ω ω ω 𝟘 𝟙 → refl
    ω ω ω 𝟘 ω → refl
    ω ω ω 𝟙 𝟘 → refl
    ω ω ω 𝟙 𝟙 → refl
    ω ω ω 𝟙 ω → refl
    ω ω ω ω 𝟘 → refl
    ω ω ω ω 𝟙 → refl
    ω ω ω ω ω → refl

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

  tr-≤-nr :
    ∀ q p r z₁ s₁ n₁ →
    tr′ q LA.≤ LA.nr (tr′ p) (tr′ r) z₁ s₁ n₁ →
    ∃₃ λ z₂ s₂ n₂ →
       tr′ z₂ LA.≤ z₁ × tr′ s₂ LA.≤ s₁ × tr′ n₂ LA.≤ n₁ ×
       q A.≤ A.nr p r z₂ s₂ n₂
  tr-≤-nr = λ where
    ω _ _ _  _  _  _  → ω , ω , ω , refl , refl , refl , refl
    𝟘 𝟘 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟘  𝟘  𝟙  _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟘  𝟘  ≤𝟙 _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟘  𝟙  𝟘  _  → 𝟘 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 𝟘  _  → 𝟘 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟘  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟘  𝟘  𝟙  _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟘  𝟘  ≤𝟙 _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  𝟘  𝟙  _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  𝟘  ≤𝟙 _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟙 𝟘  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟘  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟘  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟘  ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟙  ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 ≤𝟙 𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟙 𝟘  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟙 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 𝟘 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 𝟘 ω 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 ω 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 ω 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 ω 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 ω 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 ω 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 ω 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 ω 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 ω 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 ω 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 ω 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 ω ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 ω ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 ω ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 ω ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 ω ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 ω ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 ω ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 ω ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 ω ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 ω ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 ω ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 ω ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 ω ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 ω ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 ω ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 ω ≤ω ≤ω ≤ω ()
    𝟘 𝟙 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 𝟙 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 𝟙 ω 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 ω 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 ω 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 ω 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 ω 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 ω 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 ω 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 ω 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 ω 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 ω 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 ω 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 ω ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 ω ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 ω ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 ω ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 ω ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 ω ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 ω ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 ω ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 ω ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 ω ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 ω ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 ω ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 ω ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 ω ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 ω ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 ω ≤ω ≤ω ≤ω ()
    𝟘 ω 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 ω 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 ω 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 ω 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 ω 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 ω 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 ω 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 ω 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 ω 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 ω 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 ω 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 ω 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 ω 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 ω 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 ω 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 ω 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 ω 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 ω 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 ω 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 ω 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 ω 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 ω 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 ω 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 ω 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 ω 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 ω 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 ω 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 ω 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 ω 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 ω 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 ω 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 ω 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 ω 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 ω 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 ω 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 ω 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 ω 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 ω 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 ω 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 ω 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 ω 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 ω 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 ω 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 ω 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 ω 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 ω 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 ω ω 𝟘  𝟘  𝟙  ()
    𝟘 ω ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω ω 𝟘  𝟘  ≤ω ()
    𝟘 ω ω 𝟘  𝟙  𝟘  ()
    𝟘 ω ω 𝟘  𝟙  𝟙  ()
    𝟘 ω ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω ω 𝟘  𝟙  ≤ω ()
    𝟘 ω ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω ω 𝟘  ≤ω 𝟘  ()
    𝟘 ω ω 𝟘  ≤ω 𝟙  ()
    𝟘 ω ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω ω 𝟘  ≤ω ≤ω ()
    𝟘 ω ω 𝟙  𝟘  𝟘  ()
    𝟘 ω ω 𝟙  𝟘  𝟙  ()
    𝟘 ω ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω ω 𝟙  𝟘  ≤ω ()
    𝟘 ω ω 𝟙  𝟙  𝟘  ()
    𝟘 ω ω 𝟙  𝟙  𝟙  ()
    𝟘 ω ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω ω 𝟙  𝟙  ≤ω ()
    𝟘 ω ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω ω 𝟙  ≤ω 𝟘  ()
    𝟘 ω ω 𝟙  ≤ω 𝟙  ()
    𝟘 ω ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω ω 𝟙  ≤ω ≤ω ()
    𝟘 ω ω ≤𝟙 𝟘  𝟘  ()
    𝟘 ω ω ≤𝟙 𝟘  𝟙  ()
    𝟘 ω ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω ω ≤𝟙 𝟘  ≤ω ()
    𝟘 ω ω ≤𝟙 𝟙  𝟘  ()
    𝟘 ω ω ≤𝟙 𝟙  𝟙  ()
    𝟘 ω ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω ω ≤𝟙 𝟙  ≤ω ()
    𝟘 ω ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω ω ≤𝟙 ≤ω ≤ω ()
    𝟘 ω ω ≤ω 𝟘  𝟘  ()
    𝟘 ω ω ≤ω 𝟘  𝟙  ()
    𝟘 ω ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω ω ≤ω 𝟘  ≤ω ()
    𝟘 ω ω ≤ω 𝟙  𝟘  ()
    𝟘 ω ω ≤ω 𝟙  𝟙  ()
    𝟘 ω ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω ω ≤ω 𝟙  ≤ω ()
    𝟘 ω ω ≤ω ≤𝟙 𝟘  ()
    𝟘 ω ω ≤ω ≤𝟙 𝟙  ()
    𝟘 ω ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω ω ≤ω ≤𝟙 ≤ω ()
    𝟘 ω ω ≤ω ≤ω 𝟘  ()
    𝟘 ω ω ≤ω ≤ω 𝟙  ()
    𝟘 ω ω ≤ω ≤ω ≤𝟙 ()
    𝟘 ω ω ≤ω ≤ω ≤ω ()
    𝟙 𝟘 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 𝟘 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 𝟘 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 𝟘 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 𝟘 ω 𝟘  𝟘  𝟙  ()
    𝟙 𝟘 ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 ω 𝟘  𝟙  𝟘  ()
    𝟙 𝟘 ω 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 ω 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 ω 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 ω 𝟙  𝟘  𝟘  ()
    𝟙 𝟘 ω 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 ω 𝟙  𝟙  𝟘  ()
    𝟙 𝟘 ω 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 ω 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 ω 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 ω ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟘 ω ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 ω ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟘 ω ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 ω ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 ω ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 ω ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 ω ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 ω ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 ω ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 ω ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 ω ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 ω ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 ω ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 ω ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 ω ≤ω ≤ω ≤ω ()
    𝟙 𝟙 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 𝟙 𝟙 𝟘  𝟘  𝟙  ()
    𝟙 𝟙 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 𝟙 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 𝟙 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 𝟙 ω 𝟘  𝟘  𝟙  ()
    𝟙 𝟙 ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 ω 𝟘  𝟙  𝟘  ()
    𝟙 𝟙 ω 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 ω 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 ω 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 ω 𝟙  𝟘  𝟘  ()
    𝟙 𝟙 ω 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 ω 𝟙  𝟙  𝟘  ()
    𝟙 𝟙 ω 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 ω 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 ω 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 ω ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟙 ω ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 ω ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟙 ω ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 ω ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 ω ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 ω ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 ω ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 ω ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 ω ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 ω ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 ω ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 ω ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 ω ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 ω ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 ω ≤ω ≤ω ≤ω ()
    𝟙 ω 𝟘 𝟘  𝟘  𝟙  ()
    𝟙 ω 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 ω 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 ω 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 ω 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 ω 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 ω 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 ω 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 ω 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 ω 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 ω 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 ω 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 ω 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 ω 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 ω 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 ω 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 ω 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 ω 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 ω 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 ω 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 ω 𝟙 𝟘  𝟘  𝟙  ()
    𝟙 ω 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 ω 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 ω 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 ω 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 ω 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 ω 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 ω 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 ω 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 ω 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 ω 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 ω 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 ω 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 ω 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 ω 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 ω 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 ω 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 ω 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 ω 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 ω 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 ω 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 ω 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 ω ω 𝟘  𝟘  𝟙  ()
    𝟙 ω ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω ω 𝟘  𝟘  ≤ω ()
    𝟙 ω ω 𝟘  𝟙  𝟘  ()
    𝟙 ω ω 𝟘  𝟙  𝟙  ()
    𝟙 ω ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω ω 𝟘  𝟙  ≤ω ()
    𝟙 ω ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 ω ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω ω 𝟘  ≤ω 𝟘  ()
    𝟙 ω ω 𝟘  ≤ω 𝟙  ()
    𝟙 ω ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω ω 𝟘  ≤ω ≤ω ()
    𝟙 ω ω 𝟙  𝟘  𝟘  ()
    𝟙 ω ω 𝟙  𝟘  𝟙  ()
    𝟙 ω ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω ω 𝟙  𝟘  ≤ω ()
    𝟙 ω ω 𝟙  𝟙  𝟘  ()
    𝟙 ω ω 𝟙  𝟙  𝟙  ()
    𝟙 ω ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω ω 𝟙  𝟙  ≤ω ()
    𝟙 ω ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 ω ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω ω 𝟙  ≤ω 𝟘  ()
    𝟙 ω ω 𝟙  ≤ω 𝟙  ()
    𝟙 ω ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω ω 𝟙  ≤ω ≤ω ()
    𝟙 ω ω ≤𝟙 𝟘  𝟘  ()
    𝟙 ω ω ≤𝟙 𝟘  𝟙  ()
    𝟙 ω ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω ω ≤𝟙 𝟘  ≤ω ()
    𝟙 ω ω ≤𝟙 𝟙  𝟘  ()
    𝟙 ω ω ≤𝟙 𝟙  𝟙  ()
    𝟙 ω ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω ω ≤𝟙 𝟙  ≤ω ()
    𝟙 ω ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 ω ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω ω ≤𝟙 ≤ω ≤ω ()
    𝟙 ω ω ≤ω 𝟘  𝟘  ()
    𝟙 ω ω ≤ω 𝟘  𝟙  ()
    𝟙 ω ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω ω ≤ω 𝟘  ≤ω ()
    𝟙 ω ω ≤ω 𝟙  𝟘  ()
    𝟙 ω ω ≤ω 𝟙  𝟙  ()
    𝟙 ω ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω ω ≤ω 𝟙  ≤ω ()
    𝟙 ω ω ≤ω ≤𝟙 𝟘  ()
    𝟙 ω ω ≤ω ≤𝟙 𝟙  ()
    𝟙 ω ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω ω ≤ω ≤𝟙 ≤ω ()
    𝟙 ω ω ≤ω ≤ω 𝟘  ()
    𝟙 ω ω ≤ω ≤ω 𝟙  ()
    𝟙 ω ω ≤ω ≤ω ≤𝟙 ()
    𝟙 ω ω ≤ω ≤ω ≤ω ()

  tr⁻¹-monotone : ∀ p q → p LA.≤ q → tr⁻¹ p A.≤ tr⁻¹ q
  tr⁻¹-monotone = λ where
    𝟘  𝟘  refl → refl
    𝟙  𝟙  refl → refl
    ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟙  refl → refl
    ≤𝟙 ≤𝟙 refl → refl
    ≤ω _  _    → refl

  tr-tr⁻¹≤ : ∀ p → tr′ (tr⁻¹ p) LA.≤ p
  tr-tr⁻¹≤ = λ where
    𝟘  → refl
    𝟙  → refl
    ≤𝟙 → refl
    ≤ω → refl

  tr≤→≤tr⁻¹ : ∀ p q → tr′ p LA.≤ q → p A.≤ tr⁻¹ q
  tr≤→≤tr⁻¹ = λ where
    𝟘 𝟘  refl → refl
    𝟙 𝟘  refl → refl
    𝟙 𝟙  refl → refl
    𝟙 ≤𝟙 refl → refl
    ω _  _    → refl

  tr⁻¹-∧ : ∀ p q → tr⁻¹ (p LA.∧ q) ≡ tr⁻¹ p A.∧ tr⁻¹ q
  tr⁻¹-∧ = λ where
    𝟘  𝟘  → refl
    𝟘  𝟙  → refl
    𝟘  ≤𝟙 → refl
    𝟘  ≤ω → refl
    𝟙  𝟘  → refl
    𝟙  𝟙  → refl
    𝟙  ≤𝟙 → refl
    𝟙  ≤ω → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω _  → refl

  tr⁻¹-+ : ∀ p q → tr⁻¹ (p LA.+ q) ≡ tr⁻¹ p A.+ tr⁻¹ q
  tr⁻¹-+ = λ where
    𝟘  𝟘  → refl
    𝟘  𝟙  → refl
    𝟘  ≤𝟙 → refl
    𝟘  ≤ω → refl
    𝟙  𝟘  → refl
    𝟙  𝟙  → refl
    𝟙  ≤𝟙 → refl
    𝟙  ≤ω → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω 𝟘  → refl
    ≤ω 𝟙  → refl
    ≤ω ≤𝟙 → refl
    ≤ω ≤ω → refl

  tr⁻¹-· : ∀ p q → tr⁻¹ (tr′ p LA.· q) ≡ p A.· tr⁻¹ q
  tr⁻¹-· = λ where
    𝟘 𝟘  → refl
    𝟘 𝟙  → refl
    𝟘 ≤𝟙 → refl
    𝟘 ≤ω → refl
    𝟙 𝟘  → refl
    𝟙 𝟙  → refl
    𝟙 ≤𝟙 → refl
    𝟙 ≤ω → refl
    ω 𝟘  → refl
    ω 𝟙  → refl
    ω ≤𝟙 → refl
    ω ≤ω → refl

  tr-≤-no-nr :
    ∀ s →
    tr′ p LA.≤ q₁ →
    q₁ LA.≤ q₂ →
    (T (Modality-variant.𝟘ᵐ-allowed v₁) →
     q₁ LA.≤ q₃) →
    (Has-well-behaved-zero Linear-or-affine
       LA.linear-or-affine-semiring-with-meet →
     q₁ LA.≤ q₄) →
    q₁ LA.≤ q₃ LA.+ tr′ r LA.· q₄ LA.+ tr′ s LA.· q₁ →
    ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
       tr′ q₂′ LA.≤ q₂ ×
       tr′ q₃′ LA.≤ q₃ ×
       tr′ q₄′ LA.≤ q₄ ×
       p A.≤ q₁′ ×
       q₁′ A.≤ q₂′ ×
       (T (Modality-variant.𝟘ᵐ-allowed v₂) →
        q₁′ A.≤ q₃′) ×
       (Has-well-behaved-zero Affine
          (Modality.semiring-with-meet (affineModality v₂)) →
        q₁′ A.≤ q₄′) ×
       q₁′ A.≤ q₃′ A.+ r A.· q₄′ A.+ s A.· q₁′
  tr-≤-no-nr s = →tr-≤-no-nr {s = s}
    (affineModality v₁)
    (linear-or-affine v₂)
    idᶠ
    (λ _ → LA.linear-or-affine-has-well-behaved-zero)
    tr′
    tr⁻¹
    tr⁻¹-monotone
    tr≤→≤tr⁻¹
    tr-tr⁻¹≤
    (λ p q → P₁.≤-reflexive (tr⁻¹-+ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-∧ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-· p q))

-- The function linear-or-affine→affine is a morphism from a linear or
-- affine types modality to an affine types modality if certain
-- assumptions hold.

linear-or-affine⇨affine :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = linear-or-affine v₁
      𝕄₂ = affineModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ linear-or-affine→affine
linear-or-affine⇨affine {v₂ = v₂} refl s⇔s = λ where
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                           , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧                      → ≤-reflexive (tr-∧ _ _)
    .Is-morphism.tr-nr {r = r}             → ≤-reflexive
                                               (tr-nr _ r _ _ _)
    .Is-morphism.nr-in-first-iff-in-second → s⇔s
    .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
    .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
      (inj₁ ok) → inj₁ ok
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ LA.linear-or-affine-has-well-behaved-zero
  where
  open Graded.Modality.Properties (affineModality v₂)

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

  tr-nr :
    ∀ p r z s n →
    tr′ (LA.nr p r z s n) ≡
    A.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘  𝟘  𝟘  𝟘  𝟘  → refl
    𝟘  𝟘  𝟘  𝟘  𝟙  → refl
    𝟘  𝟘  𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟘  𝟘  𝟘  ≤ω → refl
    𝟘  𝟘  𝟘  𝟙  𝟘  → refl
    𝟘  𝟘  𝟘  𝟙  𝟙  → refl
    𝟘  𝟘  𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟘  𝟘  𝟙  ≤ω → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟘  → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟙  → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤ω → refl
    𝟘  𝟘  𝟘  ≤ω 𝟘  → refl
    𝟘  𝟘  𝟘  ≤ω 𝟙  → refl
    𝟘  𝟘  𝟘  ≤ω ≤𝟙 → refl
    𝟘  𝟘  𝟘  ≤ω ≤ω → refl
    𝟘  𝟘  𝟙  𝟘  𝟘  → refl
    𝟘  𝟘  𝟙  𝟘  𝟙  → refl
    𝟘  𝟘  𝟙  𝟘  ≤𝟙 → refl
    𝟘  𝟘  𝟙  𝟘  ≤ω → refl
    𝟘  𝟘  𝟙  𝟙  𝟘  → refl
    𝟘  𝟘  𝟙  𝟙  𝟙  → refl
    𝟘  𝟘  𝟙  𝟙  ≤𝟙 → refl
    𝟘  𝟘  𝟙  𝟙  ≤ω → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟘  → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟙  → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤ω → refl
    𝟘  𝟘  𝟙  ≤ω 𝟘  → refl
    𝟘  𝟘  𝟙  ≤ω 𝟙  → refl
    𝟘  𝟘  𝟙  ≤ω ≤𝟙 → refl
    𝟘  𝟘  𝟙  ≤ω ≤ω → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟘  → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟙  → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤ω → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟘  → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟙  → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤ω → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟘  → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟙  → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤ω → refl
    𝟘  𝟘  ≤ω 𝟘  𝟘  → refl
    𝟘  𝟘  ≤ω 𝟘  𝟙  → refl
    𝟘  𝟘  ≤ω 𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤ω 𝟘  ≤ω → refl
    𝟘  𝟘  ≤ω 𝟙  𝟘  → refl
    𝟘  𝟘  ≤ω 𝟙  𝟙  → refl
    𝟘  𝟘  ≤ω 𝟙  ≤𝟙 → refl
    𝟘  𝟘  ≤ω 𝟙  ≤ω → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟘  → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟙  → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤ω → refl
    𝟘  𝟘  ≤ω ≤ω 𝟘  → refl
    𝟘  𝟘  ≤ω ≤ω 𝟙  → refl
    𝟘  𝟘  ≤ω ≤ω ≤𝟙 → refl
    𝟘  𝟘  ≤ω ≤ω ≤ω → refl
    𝟘  𝟙  𝟘  𝟘  𝟘  → refl
    𝟘  𝟙  𝟘  𝟘  𝟙  → refl
    𝟘  𝟙  𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟙  𝟘  𝟘  ≤ω → refl
    𝟘  𝟙  𝟘  𝟙  𝟘  → refl
    𝟘  𝟙  𝟘  𝟙  𝟙  → refl
    𝟘  𝟙  𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟙  𝟘  𝟙  ≤ω → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟘  → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟙  → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤ω → refl
    𝟘  𝟙  𝟘  ≤ω 𝟘  → refl
    𝟘  𝟙  𝟘  ≤ω 𝟙  → refl
    𝟘  𝟙  𝟘  ≤ω ≤𝟙 → refl
    𝟘  𝟙  𝟘  ≤ω ≤ω → refl
    𝟘  𝟙  𝟙  𝟘  𝟘  → refl
    𝟘  𝟙  𝟙  𝟘  𝟙  → refl
    𝟘  𝟙  𝟙  𝟘  ≤𝟙 → refl
    𝟘  𝟙  𝟙  𝟘  ≤ω → refl
    𝟘  𝟙  𝟙  𝟙  𝟘  → refl
    𝟘  𝟙  𝟙  𝟙  𝟙  → refl
    𝟘  𝟙  𝟙  𝟙  ≤𝟙 → refl
    𝟘  𝟙  𝟙  𝟙  ≤ω → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟘  → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟙  → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤ω → refl
    𝟘  𝟙  𝟙  ≤ω 𝟘  → refl
    𝟘  𝟙  𝟙  ≤ω 𝟙  → refl
    𝟘  𝟙  𝟙  ≤ω ≤𝟙 → refl
    𝟘  𝟙  𝟙  ≤ω ≤ω → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟘  → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟙  → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤ω → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟘  → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟙  → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤ω → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟘  → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟙  → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤ω → refl
    𝟘  𝟙  ≤ω 𝟘  𝟘  → refl
    𝟘  𝟙  ≤ω 𝟘  𝟙  → refl
    𝟘  𝟙  ≤ω 𝟘  ≤𝟙 → refl
    𝟘  𝟙  ≤ω 𝟘  ≤ω → refl
    𝟘  𝟙  ≤ω 𝟙  𝟘  → refl
    𝟘  𝟙  ≤ω 𝟙  𝟙  → refl
    𝟘  𝟙  ≤ω 𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤ω 𝟙  ≤ω → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟘  → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟙  → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤ω → refl
    𝟘  𝟙  ≤ω ≤ω 𝟘  → refl
    𝟘  𝟙  ≤ω ≤ω 𝟙  → refl
    𝟘  𝟙  ≤ω ≤ω ≤𝟙 → refl
    𝟘  𝟙  ≤ω ≤ω ≤ω → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟘  → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟙  → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤ω → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟘  → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟙  → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟘  → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟙  → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤ω → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟘  → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟙  → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤ω → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟘  → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟙  → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟘  → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟙  → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟘  → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟙  → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤ω → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟘  → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟙  → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤ω → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟘  → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟙  → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤ω → refl
    𝟘  ≤ω 𝟘  𝟘  𝟘  → refl
    𝟘  ≤ω 𝟘  𝟘  𝟙  → refl
    𝟘  ≤ω 𝟘  𝟘  ≤𝟙 → refl
    𝟘  ≤ω 𝟘  𝟘  ≤ω → refl
    𝟘  ≤ω 𝟘  𝟙  𝟘  → refl
    𝟘  ≤ω 𝟘  𝟙  𝟙  → refl
    𝟘  ≤ω 𝟘  𝟙  ≤𝟙 → refl
    𝟘  ≤ω 𝟘  𝟙  ≤ω → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟙  → refl
    𝟘  ≤ω 𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤ω 𝟘  ≤ω ≤ω → refl
    𝟘  ≤ω 𝟙  𝟘  𝟘  → refl
    𝟘  ≤ω 𝟙  𝟘  𝟙  → refl
    𝟘  ≤ω 𝟙  𝟘  ≤𝟙 → refl
    𝟘  ≤ω 𝟙  𝟘  ≤ω → refl
    𝟘  ≤ω 𝟙  𝟙  𝟘  → refl
    𝟘  ≤ω 𝟙  𝟙  𝟙  → refl
    𝟘  ≤ω 𝟙  𝟙  ≤𝟙 → refl
    𝟘  ≤ω 𝟙  𝟙  ≤ω → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟘  → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟙  → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟙  → refl
    𝟘  ≤ω 𝟙  ≤ω ≤𝟙 → refl
    𝟘  ≤ω 𝟙  ≤ω ≤ω → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟘  → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟙  → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤ω → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟘  → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟙  → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤ω → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟘  → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟙  → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤ω → refl
    𝟘  ≤ω ≤ω 𝟘  𝟘  → refl
    𝟘  ≤ω ≤ω 𝟘  𝟙  → refl
    𝟘  ≤ω ≤ω 𝟘  ≤𝟙 → refl
    𝟘  ≤ω ≤ω 𝟘  ≤ω → refl
    𝟘  ≤ω ≤ω 𝟙  𝟘  → refl
    𝟘  ≤ω ≤ω 𝟙  𝟙  → refl
    𝟘  ≤ω ≤ω 𝟙  ≤𝟙 → refl
    𝟘  ≤ω ≤ω 𝟙  ≤ω → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟘  → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟙  → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤ω → refl
    𝟘  ≤ω ≤ω ≤ω 𝟘  → refl
    𝟘  ≤ω ≤ω ≤ω 𝟙  → refl
    𝟘  ≤ω ≤ω ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤ω ≤ω ≤ω → refl
    𝟙  𝟘  𝟘  𝟘  𝟘  → refl
    𝟙  𝟘  𝟘  𝟘  𝟙  → refl
    𝟙  𝟘  𝟘  𝟘  ≤𝟙 → refl
    𝟙  𝟘  𝟘  𝟘  ≤ω → refl
    𝟙  𝟘  𝟘  𝟙  𝟘  → refl
    𝟙  𝟘  𝟘  𝟙  𝟙  → refl
    𝟙  𝟘  𝟘  𝟙  ≤𝟙 → refl
    𝟙  𝟘  𝟘  𝟙  ≤ω → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟘  → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟙  → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤ω → refl
    𝟙  𝟘  𝟘  ≤ω 𝟘  → refl
    𝟙  𝟘  𝟘  ≤ω 𝟙  → refl
    𝟙  𝟘  𝟘  ≤ω ≤𝟙 → refl
    𝟙  𝟘  𝟘  ≤ω ≤ω → refl
    𝟙  𝟘  𝟙  𝟘  𝟘  → refl
    𝟙  𝟘  𝟙  𝟘  𝟙  → refl
    𝟙  𝟘  𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟘  𝟙  𝟘  ≤ω → refl
    𝟙  𝟘  𝟙  𝟙  𝟘  → refl
    𝟙  𝟘  𝟙  𝟙  𝟙  → refl
    𝟙  𝟘  𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟘  𝟙  𝟙  ≤ω → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟘  → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟙  → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤ω → refl
    𝟙  𝟘  𝟙  ≤ω 𝟘  → refl
    𝟙  𝟘  𝟙  ≤ω 𝟙  → refl
    𝟙  𝟘  𝟙  ≤ω ≤𝟙 → refl
    𝟙  𝟘  𝟙  ≤ω ≤ω → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟘  → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟙  → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤ω → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟘  → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟙  → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤ω → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟘  → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟙  → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤ω → refl
    𝟙  𝟘  ≤ω 𝟘  𝟘  → refl
    𝟙  𝟘  ≤ω 𝟘  𝟙  → refl
    𝟙  𝟘  ≤ω 𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤ω 𝟘  ≤ω → refl
    𝟙  𝟘  ≤ω 𝟙  𝟘  → refl
    𝟙  𝟘  ≤ω 𝟙  𝟙  → refl
    𝟙  𝟘  ≤ω 𝟙  ≤𝟙 → refl
    𝟙  𝟘  ≤ω 𝟙  ≤ω → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟘  → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟙  → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤ω → refl
    𝟙  𝟘  ≤ω ≤ω 𝟘  → refl
    𝟙  𝟘  ≤ω ≤ω 𝟙  → refl
    𝟙  𝟘  ≤ω ≤ω ≤𝟙 → refl
    𝟙  𝟘  ≤ω ≤ω ≤ω → refl
    𝟙  𝟙  𝟘  𝟘  𝟘  → refl
    𝟙  𝟙  𝟘  𝟘  𝟙  → refl
    𝟙  𝟙  𝟘  𝟘  ≤𝟙 → refl
    𝟙  𝟙  𝟘  𝟘  ≤ω → refl
    𝟙  𝟙  𝟘  𝟙  𝟘  → refl
    𝟙  𝟙  𝟘  𝟙  𝟙  → refl
    𝟙  𝟙  𝟘  𝟙  ≤𝟙 → refl
    𝟙  𝟙  𝟘  𝟙  ≤ω → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟘  → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟙  → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤ω → refl
    𝟙  𝟙  𝟘  ≤ω 𝟘  → refl
    𝟙  𝟙  𝟘  ≤ω 𝟙  → refl
    𝟙  𝟙  𝟘  ≤ω ≤𝟙 → refl
    𝟙  𝟙  𝟘  ≤ω ≤ω → refl
    𝟙  𝟙  𝟙  𝟘  𝟘  → refl
    𝟙  𝟙  𝟙  𝟘  𝟙  → refl
    𝟙  𝟙  𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟙  𝟙  𝟘  ≤ω → refl
    𝟙  𝟙  𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  𝟙  𝟙  ≤ω → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟘  → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟙  → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤ω → refl
    𝟙  𝟙  𝟙  ≤ω 𝟘  → refl
    𝟙  𝟙  𝟙  ≤ω 𝟙  → refl
    𝟙  𝟙  𝟙  ≤ω ≤𝟙 → refl
    𝟙  𝟙  𝟙  ≤ω ≤ω → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟘  → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟙  → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤ω → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟘  → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤ω → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟘  → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟙  → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤ω → refl
    𝟙  𝟙  ≤ω 𝟘  𝟘  → refl
    𝟙  𝟙  ≤ω 𝟘  𝟙  → refl
    𝟙  𝟙  ≤ω 𝟘  ≤𝟙 → refl
    𝟙  𝟙  ≤ω 𝟘  ≤ω → refl
    𝟙  𝟙  ≤ω 𝟙  𝟘  → refl
    𝟙  𝟙  ≤ω 𝟙  𝟙  → refl
    𝟙  𝟙  ≤ω 𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω 𝟙  ≤ω → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟘  → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟙  → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤ω → refl
    𝟙  𝟙  ≤ω ≤ω 𝟘  → refl
    𝟙  𝟙  ≤ω ≤ω 𝟙  → refl
    𝟙  𝟙  ≤ω ≤ω ≤𝟙 → refl
    𝟙  𝟙  ≤ω ≤ω ≤ω → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟘  → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟙  → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤ω → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟘  → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟙  → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟘  → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟙  → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤ω → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟘  → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟙  → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤ω → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟘  → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟙  → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟘  → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟙  → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟘  → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟙  → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤ω → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟘  → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟙  → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤ω → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟘  → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟙  → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤ω → refl
    𝟙  ≤ω 𝟘  𝟘  𝟘  → refl
    𝟙  ≤ω 𝟘  𝟘  𝟙  → refl
    𝟙  ≤ω 𝟘  𝟘  ≤𝟙 → refl
    𝟙  ≤ω 𝟘  𝟘  ≤ω → refl
    𝟙  ≤ω 𝟘  𝟙  𝟘  → refl
    𝟙  ≤ω 𝟘  𝟙  𝟙  → refl
    𝟙  ≤ω 𝟘  𝟙  ≤𝟙 → refl
    𝟙  ≤ω 𝟘  𝟙  ≤ω → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟘  → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟙  → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟙  → refl
    𝟙  ≤ω 𝟘  ≤ω ≤𝟙 → refl
    𝟙  ≤ω 𝟘  ≤ω ≤ω → refl
    𝟙  ≤ω 𝟙  𝟘  𝟘  → refl
    𝟙  ≤ω 𝟙  𝟘  𝟙  → refl
    𝟙  ≤ω 𝟙  𝟘  ≤𝟙 → refl
    𝟙  ≤ω 𝟙  𝟘  ≤ω → refl
    𝟙  ≤ω 𝟙  𝟙  𝟘  → refl
    𝟙  ≤ω 𝟙  𝟙  𝟙  → refl
    𝟙  ≤ω 𝟙  𝟙  ≤𝟙 → refl
    𝟙  ≤ω 𝟙  𝟙  ≤ω → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω 𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω 𝟙  ≤ω ≤ω → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟘  → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟙  → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤ω → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟘  → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟙  → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤ω → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟘  → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤ω → refl
    𝟙  ≤ω ≤ω 𝟘  𝟘  → refl
    𝟙  ≤ω ≤ω 𝟘  𝟙  → refl
    𝟙  ≤ω ≤ω 𝟘  ≤𝟙 → refl
    𝟙  ≤ω ≤ω 𝟘  ≤ω → refl
    𝟙  ≤ω ≤ω 𝟙  𝟘  → refl
    𝟙  ≤ω ≤ω 𝟙  𝟙  → refl
    𝟙  ≤ω ≤ω 𝟙  ≤𝟙 → refl
    𝟙  ≤ω ≤ω 𝟙  ≤ω → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟘  → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟙  → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤ω → refl
    𝟙  ≤ω ≤ω ≤ω 𝟘  → refl
    𝟙  ≤ω ≤ω ≤ω 𝟙  → refl
    𝟙  ≤ω ≤ω ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟙  → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤ω → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟘  → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟙  → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤ω → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟘  → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟙  → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟙  → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤ω → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟘  → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟙  → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤ω → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟘  → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟙  → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟘  → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤ω → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟘  → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟙  → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤ω → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟘  → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟙  → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤ω → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟘  → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟙  → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟙  → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤ω → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟘  → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟙  → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤ω → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟘  → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟙  → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟙  → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤ω → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟘  → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟙  → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟘  → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟙  → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤ω → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟘  → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤ω → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟘  → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟙  → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤ω → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟘  → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟙  → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤ω → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟘  → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟙  → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤ω → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟙  → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤ω → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟘  → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟙  → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤ω → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟘  → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟙  → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤ω → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟙  → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟘  → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟙  → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤ω → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟘  → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟙  → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤ω → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟘  → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤ω → refl
    ≤ω 𝟘  𝟘  𝟘  𝟘  → refl
    ≤ω 𝟘  𝟘  𝟘  𝟙  → refl
    ≤ω 𝟘  𝟘  𝟘  ≤𝟙 → refl
    ≤ω 𝟘  𝟘  𝟘  ≤ω → refl
    ≤ω 𝟘  𝟘  𝟙  𝟘  → refl
    ≤ω 𝟘  𝟘  𝟙  𝟙  → refl
    ≤ω 𝟘  𝟘  𝟙  ≤𝟙 → refl
    ≤ω 𝟘  𝟘  𝟙  ≤ω → refl
    ≤ω 𝟘  𝟘  ≤𝟙 𝟘  → refl
    ≤ω 𝟘  𝟘  ≤𝟙 𝟙  → refl
    ≤ω 𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  𝟘  ≤𝟙 ≤ω → refl
    ≤ω 𝟘  𝟘  ≤ω 𝟘  → refl
    ≤ω 𝟘  𝟘  ≤ω 𝟙  → refl
    ≤ω 𝟘  𝟘  ≤ω ≤𝟙 → refl
    ≤ω 𝟘  𝟘  ≤ω ≤ω → refl
    ≤ω 𝟘  𝟙  𝟘  𝟘  → refl
    ≤ω 𝟘  𝟙  𝟘  𝟙  → refl
    ≤ω 𝟘  𝟙  𝟘  ≤𝟙 → refl
    ≤ω 𝟘  𝟙  𝟘  ≤ω → refl
    ≤ω 𝟘  𝟙  𝟙  𝟘  → refl
    ≤ω 𝟘  𝟙  𝟙  𝟙  → refl
    ≤ω 𝟘  𝟙  𝟙  ≤𝟙 → refl
    ≤ω 𝟘  𝟙  𝟙  ≤ω → refl
    ≤ω 𝟘  𝟙  ≤𝟙 𝟘  → refl
    ≤ω 𝟘  𝟙  ≤𝟙 𝟙  → refl
    ≤ω 𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  𝟙  ≤𝟙 ≤ω → refl
    ≤ω 𝟘  𝟙  ≤ω 𝟘  → refl
    ≤ω 𝟘  𝟙  ≤ω 𝟙  → refl
    ≤ω 𝟘  𝟙  ≤ω ≤𝟙 → refl
    ≤ω 𝟘  𝟙  ≤ω ≤ω → refl
    ≤ω 𝟘  ≤𝟙 𝟘  𝟘  → refl
    ≤ω 𝟘  ≤𝟙 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 𝟘  ≤ω → refl
    ≤ω 𝟘  ≤𝟙 𝟙  𝟘  → refl
    ≤ω 𝟘  ≤𝟙 𝟙  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 𝟙  ≤ω → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω 𝟘  ≤𝟙 ≤ω 𝟘  → refl
    ≤ω 𝟘  ≤𝟙 ≤ω 𝟙  → refl
    ≤ω 𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟘  ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟘  ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟘  ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟘  ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω 𝟙  ≤ω → refl
    ≤ω 𝟘  ≤ω ≤𝟙 𝟘  → refl
    ≤ω 𝟘  ≤ω ≤𝟙 𝟙  → refl
    ≤ω 𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  ≤ω ≤𝟙 ≤ω → refl
    ≤ω 𝟘  ≤ω ≤ω 𝟘  → refl
    ≤ω 𝟘  ≤ω ≤ω 𝟙  → refl
    ≤ω 𝟘  ≤ω ≤ω ≤𝟙 → refl
    ≤ω 𝟘  ≤ω ≤ω ≤ω → refl
    ≤ω 𝟙  𝟘  𝟘  𝟘  → refl
    ≤ω 𝟙  𝟘  𝟘  𝟙  → refl
    ≤ω 𝟙  𝟘  𝟘  ≤𝟙 → refl
    ≤ω 𝟙  𝟘  𝟘  ≤ω → refl
    ≤ω 𝟙  𝟘  𝟙  𝟘  → refl
    ≤ω 𝟙  𝟘  𝟙  𝟙  → refl
    ≤ω 𝟙  𝟘  𝟙  ≤𝟙 → refl
    ≤ω 𝟙  𝟘  𝟙  ≤ω → refl
    ≤ω 𝟙  𝟘  ≤𝟙 𝟘  → refl
    ≤ω 𝟙  𝟘  ≤𝟙 𝟙  → refl
    ≤ω 𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  𝟘  ≤𝟙 ≤ω → refl
    ≤ω 𝟙  𝟘  ≤ω 𝟘  → refl
    ≤ω 𝟙  𝟘  ≤ω 𝟙  → refl
    ≤ω 𝟙  𝟘  ≤ω ≤𝟙 → refl
    ≤ω 𝟙  𝟘  ≤ω ≤ω → refl
    ≤ω 𝟙  𝟙  𝟘  𝟘  → refl
    ≤ω 𝟙  𝟙  𝟘  𝟙  → refl
    ≤ω 𝟙  𝟙  𝟘  ≤𝟙 → refl
    ≤ω 𝟙  𝟙  𝟘  ≤ω → refl
    ≤ω 𝟙  𝟙  𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  𝟙  𝟙  → refl
    ≤ω 𝟙  𝟙  𝟙  ≤𝟙 → refl
    ≤ω 𝟙  𝟙  𝟙  ≤ω → refl
    ≤ω 𝟙  𝟙  ≤𝟙 𝟘  → refl
    ≤ω 𝟙  𝟙  ≤𝟙 𝟙  → refl
    ≤ω 𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  𝟙  ≤𝟙 ≤ω → refl
    ≤ω 𝟙  𝟙  ≤ω 𝟘  → refl
    ≤ω 𝟙  𝟙  ≤ω 𝟙  → refl
    ≤ω 𝟙  𝟙  ≤ω ≤𝟙 → refl
    ≤ω 𝟙  𝟙  ≤ω ≤ω → refl
    ≤ω 𝟙  ≤𝟙 𝟘  𝟘  → refl
    ≤ω 𝟙  ≤𝟙 𝟘  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 𝟘  ≤ω → refl
    ≤ω 𝟙  ≤𝟙 𝟙  𝟘  → refl
    ≤ω 𝟙  ≤𝟙 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 𝟙  ≤ω → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω 𝟙  ≤𝟙 ≤ω 𝟘  → refl
    ≤ω 𝟙  ≤𝟙 ≤ω 𝟙  → refl
    ≤ω 𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟙  ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟙  ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟙  ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟙  ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω 𝟙  ≤ω → refl
    ≤ω 𝟙  ≤ω ≤𝟙 𝟘  → refl
    ≤ω 𝟙  ≤ω ≤𝟙 𝟙  → refl
    ≤ω 𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  ≤ω ≤𝟙 ≤ω → refl
    ≤ω 𝟙  ≤ω ≤ω 𝟘  → refl
    ≤ω 𝟙  ≤ω ≤ω 𝟙  → refl
    ≤ω 𝟙  ≤ω ≤ω ≤𝟙 → refl
    ≤ω 𝟙  ≤ω ≤ω ≤ω → refl
    ≤ω ≤𝟙 𝟘  𝟘  𝟘  → refl
    ≤ω ≤𝟙 𝟘  𝟘  𝟙  → refl
    ≤ω ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  𝟘  ≤ω → refl
    ≤ω ≤𝟙 𝟘  𝟙  𝟘  → refl
    ≤ω ≤𝟙 𝟘  𝟙  𝟙  → refl
    ≤ω ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 𝟘  ≤ω 𝟘  → refl
    ≤ω ≤𝟙 𝟘  ≤ω 𝟙  → refl
    ≤ω ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  ≤ω ≤ω → refl
    ≤ω ≤𝟙 𝟙  𝟘  𝟘  → refl
    ≤ω ≤𝟙 𝟙  𝟘  𝟙  → refl
    ≤ω ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  𝟘  ≤ω → refl
    ≤ω ≤𝟙 𝟙  𝟙  𝟘  → refl
    ≤ω ≤𝟙 𝟙  𝟙  𝟙  → refl
    ≤ω ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 𝟙  ≤ω 𝟘  → refl
    ≤ω ≤𝟙 𝟙  ≤ω 𝟙  → refl
    ≤ω ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  ≤ω ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    ≤ω ≤𝟙 ≤ω 𝟘  𝟘  → refl
    ≤ω ≤𝟙 ≤ω 𝟘  𝟙  → refl
    ≤ω ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω 𝟘  ≤ω → refl
    ≤ω ≤𝟙 ≤ω 𝟙  𝟘  → refl
    ≤ω ≤𝟙 ≤ω 𝟙  𝟙  → refl
    ≤ω ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 ≤ω ≤ω 𝟘  → refl
    ≤ω ≤𝟙 ≤ω ≤ω 𝟙  → refl
    ≤ω ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω ≤ω ≤ω → refl
    ≤ω ≤ω 𝟘  𝟘  𝟘  → refl
    ≤ω ≤ω 𝟘  𝟘  𝟙  → refl
    ≤ω ≤ω 𝟘  𝟘  ≤𝟙 → refl
    ≤ω ≤ω 𝟘  𝟘  ≤ω → refl
    ≤ω ≤ω 𝟘  𝟙  𝟘  → refl
    ≤ω ≤ω 𝟘  𝟙  𝟙  → refl
    ≤ω ≤ω 𝟘  𝟙  ≤𝟙 → refl
    ≤ω ≤ω 𝟘  𝟙  ≤ω → refl
    ≤ω ≤ω 𝟘  ≤𝟙 𝟘  → refl
    ≤ω ≤ω 𝟘  ≤𝟙 𝟙  → refl
    ≤ω ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω 𝟘  ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟘  ≤ω 𝟙  → refl
    ≤ω ≤ω 𝟘  ≤ω ≤𝟙 → refl
    ≤ω ≤ω 𝟘  ≤ω ≤ω → refl
    ≤ω ≤ω 𝟙  𝟘  𝟘  → refl
    ≤ω ≤ω 𝟙  𝟘  𝟙  → refl
    ≤ω ≤ω 𝟙  𝟘  ≤𝟙 → refl
    ≤ω ≤ω 𝟙  𝟘  ≤ω → refl
    ≤ω ≤ω 𝟙  𝟙  𝟘  → refl
    ≤ω ≤ω 𝟙  𝟙  𝟙  → refl
    ≤ω ≤ω 𝟙  𝟙  ≤𝟙 → refl
    ≤ω ≤ω 𝟙  𝟙  ≤ω → refl
    ≤ω ≤ω 𝟙  ≤𝟙 𝟘  → refl
    ≤ω ≤ω 𝟙  ≤𝟙 𝟙  → refl
    ≤ω ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω 𝟙  ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟙  ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  ≤ω 𝟙  → refl
    ≤ω ≤ω 𝟙  ≤ω ≤𝟙 → refl
    ≤ω ≤ω 𝟙  ≤ω ≤ω → refl
    ≤ω ≤ω ≤𝟙 𝟘  𝟘  → refl
    ≤ω ≤ω ≤𝟙 𝟘  𝟙  → refl
    ≤ω ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 𝟘  ≤ω → refl
    ≤ω ≤ω ≤𝟙 𝟙  𝟘  → refl
    ≤ω ≤ω ≤𝟙 𝟙  𝟙  → refl
    ≤ω ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 𝟙  ≤ω → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω ≤ω ≤𝟙 ≤ω 𝟘  → refl
    ≤ω ≤ω ≤𝟙 ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 ≤ω ≤ω → refl
    ≤ω ≤ω ≤ω 𝟘  𝟘  → refl
    ≤ω ≤ω ≤ω 𝟘  𝟙  → refl
    ≤ω ≤ω ≤ω 𝟘  ≤𝟙 → refl
    ≤ω ≤ω ≤ω 𝟘  ≤ω → refl
    ≤ω ≤ω ≤ω 𝟙  𝟘  → refl
    ≤ω ≤ω ≤ω 𝟙  𝟙  → refl
    ≤ω ≤ω ≤ω 𝟙  ≤𝟙 → refl
    ≤ω ≤ω ≤ω 𝟙  ≤ω → refl
    ≤ω ≤ω ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤ω ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω ≤ω ≤ω → refl

-- The function linear-or-affine→affine is not an order embedding from
-- a linear or affine types modality to an affine types modality.

¬linear-or-affine⇨affine :
  ¬ Is-order-embedding (linear-or-affine v₁) (affineModality v₂)
      linear-or-affine→affine
¬linear-or-affine⇨affine m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ≤𝟙} refl of λ ()

-- The function affine→linearity is a morphism from an affine types
-- modality to a linear types modality if certain assumptions hold.

affine⇨linearity :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = affineModality v₁
      𝕄₂ = linearityModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ affine→linearity
affine⇨linearity {v₁ = v₁} {v₂ = v₂} refl s⇔s = λ where
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                           , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧ {p = p}              → ≤-reflexive (tr-∧ p _)
    .Is-morphism.tr-nr {r = r}             → ≤-reflexive
                                               (tr-nr _ r _ _ _)
    .Is-morphism.nr-in-first-iff-in-second → s⇔s
    .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
    .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
      (inj₁ ok) → inj₁ ok
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ (A.affine-has-well-behaved-zero v₁)
  where
  open Graded.Modality.Properties (linearityModality v₂)

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

  tr-nr :
    ∀ p r z s n →
    tr′ (A.nr p r z s n) ≡
    L.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘 𝟘 𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟘 𝟘 𝟙 → refl
    𝟘 𝟘 𝟘 𝟘 ω → refl
    𝟘 𝟘 𝟘 𝟙 𝟘 → refl
    𝟘 𝟘 𝟘 𝟙 𝟙 → refl
    𝟘 𝟘 𝟘 𝟙 ω → refl
    𝟘 𝟘 𝟘 ω 𝟘 → refl
    𝟘 𝟘 𝟘 ω 𝟙 → refl
    𝟘 𝟘 𝟘 ω ω → refl
    𝟘 𝟘 𝟙 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 𝟘 𝟙 → refl
    𝟘 𝟘 𝟙 𝟘 ω → refl
    𝟘 𝟘 𝟙 𝟙 𝟘 → refl
    𝟘 𝟘 𝟙 𝟙 𝟙 → refl
    𝟘 𝟘 𝟙 𝟙 ω → refl
    𝟘 𝟘 𝟙 ω 𝟘 → refl
    𝟘 𝟘 𝟙 ω 𝟙 → refl
    𝟘 𝟘 𝟙 ω ω → refl
    𝟘 𝟘 ω 𝟘 𝟘 → refl
    𝟘 𝟘 ω 𝟘 𝟙 → refl
    𝟘 𝟘 ω 𝟘 ω → refl
    𝟘 𝟘 ω 𝟙 𝟘 → refl
    𝟘 𝟘 ω 𝟙 𝟙 → refl
    𝟘 𝟘 ω 𝟙 ω → refl
    𝟘 𝟘 ω ω 𝟘 → refl
    𝟘 𝟘 ω ω 𝟙 → refl
    𝟘 𝟘 ω ω ω → refl
    𝟘 𝟙 𝟘 𝟘 𝟘 → refl
    𝟘 𝟙 𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 𝟘 ω → refl
    𝟘 𝟙 𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟘 𝟙 𝟙 → refl
    𝟘 𝟙 𝟘 𝟙 ω → refl
    𝟘 𝟙 𝟘 ω 𝟘 → refl
    𝟘 𝟙 𝟘 ω 𝟙 → refl
    𝟘 𝟙 𝟘 ω ω → refl
    𝟘 𝟙 𝟙 𝟘 𝟘 → refl
    𝟘 𝟙 𝟙 𝟘 𝟙 → refl
    𝟘 𝟙 𝟙 𝟘 ω → refl
    𝟘 𝟙 𝟙 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 𝟙 ω → refl
    𝟘 𝟙 𝟙 ω 𝟘 → refl
    𝟘 𝟙 𝟙 ω 𝟙 → refl
    𝟘 𝟙 𝟙 ω ω → refl
    𝟘 𝟙 ω 𝟘 𝟘 → refl
    𝟘 𝟙 ω 𝟘 𝟙 → refl
    𝟘 𝟙 ω 𝟘 ω → refl
    𝟘 𝟙 ω 𝟙 𝟘 → refl
    𝟘 𝟙 ω 𝟙 𝟙 → refl
    𝟘 𝟙 ω 𝟙 ω → refl
    𝟘 𝟙 ω ω 𝟘 → refl
    𝟘 𝟙 ω ω 𝟙 → refl
    𝟘 𝟙 ω ω ω → refl
    𝟘 ω 𝟘 𝟘 𝟘 → refl
    𝟘 ω 𝟘 𝟘 𝟙 → refl
    𝟘 ω 𝟘 𝟘 ω → refl
    𝟘 ω 𝟘 𝟙 𝟘 → refl
    𝟘 ω 𝟘 𝟙 𝟙 → refl
    𝟘 ω 𝟘 𝟙 ω → refl
    𝟘 ω 𝟘 ω 𝟘 → refl
    𝟘 ω 𝟘 ω 𝟙 → refl
    𝟘 ω 𝟘 ω ω → refl
    𝟘 ω 𝟙 𝟘 𝟘 → refl
    𝟘 ω 𝟙 𝟘 𝟙 → refl
    𝟘 ω 𝟙 𝟘 ω → refl
    𝟘 ω 𝟙 𝟙 𝟘 → refl
    𝟘 ω 𝟙 𝟙 𝟙 → refl
    𝟘 ω 𝟙 𝟙 ω → refl
    𝟘 ω 𝟙 ω 𝟘 → refl
    𝟘 ω 𝟙 ω 𝟙 → refl
    𝟘 ω 𝟙 ω ω → refl
    𝟘 ω ω 𝟘 𝟘 → refl
    𝟘 ω ω 𝟘 𝟙 → refl
    𝟘 ω ω 𝟘 ω → refl
    𝟘 ω ω 𝟙 𝟘 → refl
    𝟘 ω ω 𝟙 𝟙 → refl
    𝟘 ω ω 𝟙 ω → refl
    𝟘 ω ω ω 𝟘 → refl
    𝟘 ω ω ω 𝟙 → refl
    𝟘 ω ω ω ω → refl
    𝟙 𝟘 𝟘 𝟘 𝟘 → refl
    𝟙 𝟘 𝟘 𝟘 𝟙 → refl
    𝟙 𝟘 𝟘 𝟘 ω → refl
    𝟙 𝟘 𝟘 𝟙 𝟘 → refl
    𝟙 𝟘 𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 𝟙 ω → refl
    𝟙 𝟘 𝟘 ω 𝟘 → refl
    𝟙 𝟘 𝟘 ω 𝟙 → refl
    𝟙 𝟘 𝟘 ω ω → refl
    𝟙 𝟘 𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 𝟘 𝟙 → refl
    𝟙 𝟘 𝟙 𝟘 ω → refl
    𝟙 𝟘 𝟙 𝟙 𝟘 → refl
    𝟙 𝟘 𝟙 𝟙 𝟙 → refl
    𝟙 𝟘 𝟙 𝟙 ω → refl
    𝟙 𝟘 𝟙 ω 𝟘 → refl
    𝟙 𝟘 𝟙 ω 𝟙 → refl
    𝟙 𝟘 𝟙 ω ω → refl
    𝟙 𝟘 ω 𝟘 𝟘 → refl
    𝟙 𝟘 ω 𝟘 𝟙 → refl
    𝟙 𝟘 ω 𝟘 ω → refl
    𝟙 𝟘 ω 𝟙 𝟘 → refl
    𝟙 𝟘 ω 𝟙 𝟙 → refl
    𝟙 𝟘 ω 𝟙 ω → refl
    𝟙 𝟘 ω ω 𝟘 → refl
    𝟙 𝟘 ω ω 𝟙 → refl
    𝟙 𝟘 ω ω ω → refl
    𝟙 𝟙 𝟘 𝟘 𝟘 → refl
    𝟙 𝟙 𝟘 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 𝟘 ω → refl
    𝟙 𝟙 𝟘 𝟙 𝟘 → refl
    𝟙 𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟙 𝟘 𝟙 ω → refl
    𝟙 𝟙 𝟘 ω 𝟘 → refl
    𝟙 𝟙 𝟘 ω 𝟙 → refl
    𝟙 𝟙 𝟘 ω ω → refl
    𝟙 𝟙 𝟙 𝟘 𝟘 → refl
    𝟙 𝟙 𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 𝟙 𝟙 ω → refl
    𝟙 𝟙 𝟙 ω 𝟘 → refl
    𝟙 𝟙 𝟙 ω 𝟙 → refl
    𝟙 𝟙 𝟙 ω ω → refl
    𝟙 𝟙 ω 𝟘 𝟘 → refl
    𝟙 𝟙 ω 𝟘 𝟙 → refl
    𝟙 𝟙 ω 𝟘 ω → refl
    𝟙 𝟙 ω 𝟙 𝟘 → refl
    𝟙 𝟙 ω 𝟙 𝟙 → refl
    𝟙 𝟙 ω 𝟙 ω → refl
    𝟙 𝟙 ω ω 𝟘 → refl
    𝟙 𝟙 ω ω 𝟙 → refl
    𝟙 𝟙 ω ω ω → refl
    𝟙 ω 𝟘 𝟘 𝟘 → refl
    𝟙 ω 𝟘 𝟘 𝟙 → refl
    𝟙 ω 𝟘 𝟘 ω → refl
    𝟙 ω 𝟘 𝟙 𝟘 → refl
    𝟙 ω 𝟘 𝟙 𝟙 → refl
    𝟙 ω 𝟘 𝟙 ω → refl
    𝟙 ω 𝟘 ω 𝟘 → refl
    𝟙 ω 𝟘 ω 𝟙 → refl
    𝟙 ω 𝟘 ω ω → refl
    𝟙 ω 𝟙 𝟘 𝟘 → refl
    𝟙 ω 𝟙 𝟘 𝟙 → refl
    𝟙 ω 𝟙 𝟘 ω → refl
    𝟙 ω 𝟙 𝟙 𝟘 → refl
    𝟙 ω 𝟙 𝟙 𝟙 → refl
    𝟙 ω 𝟙 𝟙 ω → refl
    𝟙 ω 𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 ω 𝟙 → refl
    𝟙 ω 𝟙 ω ω → refl
    𝟙 ω ω 𝟘 𝟘 → refl
    𝟙 ω ω 𝟘 𝟙 → refl
    𝟙 ω ω 𝟘 ω → refl
    𝟙 ω ω 𝟙 𝟘 → refl
    𝟙 ω ω 𝟙 𝟙 → refl
    𝟙 ω ω 𝟙 ω → refl
    𝟙 ω ω ω 𝟘 → refl
    𝟙 ω ω ω 𝟙 → refl
    𝟙 ω ω ω ω → refl
    ω 𝟘 𝟘 𝟘 𝟘 → refl
    ω 𝟘 𝟘 𝟘 𝟙 → refl
    ω 𝟘 𝟘 𝟘 ω → refl
    ω 𝟘 𝟘 𝟙 𝟘 → refl
    ω 𝟘 𝟘 𝟙 𝟙 → refl
    ω 𝟘 𝟘 𝟙 ω → refl
    ω 𝟘 𝟘 ω 𝟘 → refl
    ω 𝟘 𝟘 ω 𝟙 → refl
    ω 𝟘 𝟘 ω ω → refl
    ω 𝟘 𝟙 𝟘 𝟘 → refl
    ω 𝟘 𝟙 𝟘 𝟙 → refl
    ω 𝟘 𝟙 𝟘 ω → refl
    ω 𝟘 𝟙 𝟙 𝟘 → refl
    ω 𝟘 𝟙 𝟙 𝟙 → refl
    ω 𝟘 𝟙 𝟙 ω → refl
    ω 𝟘 𝟙 ω 𝟘 → refl
    ω 𝟘 𝟙 ω 𝟙 → refl
    ω 𝟘 𝟙 ω ω → refl
    ω 𝟘 ω 𝟘 𝟘 → refl
    ω 𝟘 ω 𝟘 𝟙 → refl
    ω 𝟘 ω 𝟘 ω → refl
    ω 𝟘 ω 𝟙 𝟘 → refl
    ω 𝟘 ω 𝟙 𝟙 → refl
    ω 𝟘 ω 𝟙 ω → refl
    ω 𝟘 ω ω 𝟘 → refl
    ω 𝟘 ω ω 𝟙 → refl
    ω 𝟘 ω ω ω → refl
    ω 𝟙 𝟘 𝟘 𝟘 → refl
    ω 𝟙 𝟘 𝟘 𝟙 → refl
    ω 𝟙 𝟘 𝟘 ω → refl
    ω 𝟙 𝟘 𝟙 𝟘 → refl
    ω 𝟙 𝟘 𝟙 𝟙 → refl
    ω 𝟙 𝟘 𝟙 ω → refl
    ω 𝟙 𝟘 ω 𝟘 → refl
    ω 𝟙 𝟘 ω 𝟙 → refl
    ω 𝟙 𝟘 ω ω → refl
    ω 𝟙 𝟙 𝟘 𝟘 → refl
    ω 𝟙 𝟙 𝟘 𝟙 → refl
    ω 𝟙 𝟙 𝟘 ω → refl
    ω 𝟙 𝟙 𝟙 𝟘 → refl
    ω 𝟙 𝟙 𝟙 𝟙 → refl
    ω 𝟙 𝟙 𝟙 ω → refl
    ω 𝟙 𝟙 ω 𝟘 → refl
    ω 𝟙 𝟙 ω 𝟙 → refl
    ω 𝟙 𝟙 ω ω → refl
    ω 𝟙 ω 𝟘 𝟘 → refl
    ω 𝟙 ω 𝟘 𝟙 → refl
    ω 𝟙 ω 𝟘 ω → refl
    ω 𝟙 ω 𝟙 𝟘 → refl
    ω 𝟙 ω 𝟙 𝟙 → refl
    ω 𝟙 ω 𝟙 ω → refl
    ω 𝟙 ω ω 𝟘 → refl
    ω 𝟙 ω ω 𝟙 → refl
    ω 𝟙 ω ω ω → refl
    ω ω 𝟘 𝟘 𝟘 → refl
    ω ω 𝟘 𝟘 𝟙 → refl
    ω ω 𝟘 𝟘 ω → refl
    ω ω 𝟘 𝟙 𝟘 → refl
    ω ω 𝟘 𝟙 𝟙 → refl
    ω ω 𝟘 𝟙 ω → refl
    ω ω 𝟘 ω 𝟘 → refl
    ω ω 𝟘 ω 𝟙 → refl
    ω ω 𝟘 ω ω → refl
    ω ω 𝟙 𝟘 𝟘 → refl
    ω ω 𝟙 𝟘 𝟙 → refl
    ω ω 𝟙 𝟘 ω → refl
    ω ω 𝟙 𝟙 𝟘 → refl
    ω ω 𝟙 𝟙 𝟙 → refl
    ω ω 𝟙 𝟙 ω → refl
    ω ω 𝟙 ω 𝟘 → refl
    ω ω 𝟙 ω 𝟙 → refl
    ω ω 𝟙 ω ω → refl
    ω ω ω 𝟘 𝟘 → refl
    ω ω ω 𝟘 𝟙 → refl
    ω ω ω 𝟘 ω → refl
    ω ω ω 𝟙 𝟘 → refl
    ω ω ω 𝟙 𝟙 → refl
    ω ω ω 𝟙 ω → refl
    ω ω ω ω 𝟘 → refl
    ω ω ω ω 𝟙 → refl
    ω ω ω ω ω → refl

-- The function affine→linearity is not an order embedding from an
-- affine types modality to a linear types modality.

¬affine⇨linearity :
  ¬ Is-order-embedding (affineModality v₁) (linearityModality v₂)
      affine→linearity
¬affine⇨linearity m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ω} refl of λ ()

-- The function linearity→affine is a morphism from a linear types
-- modality to an affine types modality if certain assumptions hold.

linearity⇨affine :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = linearityModality v₁
      𝕄₂ = affineModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ linearity→affine
linearity⇨affine {v₁ = v₁} {v₂ = v₂} refl s⇔s = λ where
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                           , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧ {p = p}              → tr-∧ p _
    .Is-morphism.tr-nr {r = r}             → tr-nr _ r _ _ _
    .Is-morphism.nr-in-first-iff-in-second → s⇔s
    .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
    .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
      (inj₁ ok) → inj₁ ok
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ (L.linearity-has-well-behaved-zero v₁)
  where
  open Graded.Modality.Properties (affineModality v₂)

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

  tr-nr :
    ∀ p r z s n →
    tr′ (L.nr p r z s n) A.≤
    A.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘 𝟘 𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟘 𝟘 𝟙 → refl
    𝟘 𝟘 𝟘 𝟘 ω → refl
    𝟘 𝟘 𝟘 𝟙 𝟘 → refl
    𝟘 𝟘 𝟘 𝟙 𝟙 → refl
    𝟘 𝟘 𝟘 𝟙 ω → refl
    𝟘 𝟘 𝟘 ω 𝟘 → refl
    𝟘 𝟘 𝟘 ω 𝟙 → refl
    𝟘 𝟘 𝟘 ω ω → refl
    𝟘 𝟘 𝟙 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 𝟘 𝟙 → refl
    𝟘 𝟘 𝟙 𝟘 ω → refl
    𝟘 𝟘 𝟙 𝟙 𝟘 → refl
    𝟘 𝟘 𝟙 𝟙 𝟙 → refl
    𝟘 𝟘 𝟙 𝟙 ω → refl
    𝟘 𝟘 𝟙 ω 𝟘 → refl
    𝟘 𝟘 𝟙 ω 𝟙 → refl
    𝟘 𝟘 𝟙 ω ω → refl
    𝟘 𝟘 ω 𝟘 𝟘 → refl
    𝟘 𝟘 ω 𝟘 𝟙 → refl
    𝟘 𝟘 ω 𝟘 ω → refl
    𝟘 𝟘 ω 𝟙 𝟘 → refl
    𝟘 𝟘 ω 𝟙 𝟙 → refl
    𝟘 𝟘 ω 𝟙 ω → refl
    𝟘 𝟘 ω ω 𝟘 → refl
    𝟘 𝟘 ω ω 𝟙 → refl
    𝟘 𝟘 ω ω ω → refl
    𝟘 𝟙 𝟘 𝟘 𝟘 → refl
    𝟘 𝟙 𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 𝟘 ω → refl
    𝟘 𝟙 𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟘 𝟙 𝟙 → refl
    𝟘 𝟙 𝟘 𝟙 ω → refl
    𝟘 𝟙 𝟘 ω 𝟘 → refl
    𝟘 𝟙 𝟘 ω 𝟙 → refl
    𝟘 𝟙 𝟘 ω ω → refl
    𝟘 𝟙 𝟙 𝟘 𝟘 → refl
    𝟘 𝟙 𝟙 𝟘 𝟙 → refl
    𝟘 𝟙 𝟙 𝟘 ω → refl
    𝟘 𝟙 𝟙 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 𝟙 ω → refl
    𝟘 𝟙 𝟙 ω 𝟘 → refl
    𝟘 𝟙 𝟙 ω 𝟙 → refl
    𝟘 𝟙 𝟙 ω ω → refl
    𝟘 𝟙 ω 𝟘 𝟘 → refl
    𝟘 𝟙 ω 𝟘 𝟙 → refl
    𝟘 𝟙 ω 𝟘 ω → refl
    𝟘 𝟙 ω 𝟙 𝟘 → refl
    𝟘 𝟙 ω 𝟙 𝟙 → refl
    𝟘 𝟙 ω 𝟙 ω → refl
    𝟘 𝟙 ω ω 𝟘 → refl
    𝟘 𝟙 ω ω 𝟙 → refl
    𝟘 𝟙 ω ω ω → refl
    𝟘 ω 𝟘 𝟘 𝟘 → refl
    𝟘 ω 𝟘 𝟘 𝟙 → refl
    𝟘 ω 𝟘 𝟘 ω → refl
    𝟘 ω 𝟘 𝟙 𝟘 → refl
    𝟘 ω 𝟘 𝟙 𝟙 → refl
    𝟘 ω 𝟘 𝟙 ω → refl
    𝟘 ω 𝟘 ω 𝟘 → refl
    𝟘 ω 𝟘 ω 𝟙 → refl
    𝟘 ω 𝟘 ω ω → refl
    𝟘 ω 𝟙 𝟘 𝟘 → refl
    𝟘 ω 𝟙 𝟘 𝟙 → refl
    𝟘 ω 𝟙 𝟘 ω → refl
    𝟘 ω 𝟙 𝟙 𝟘 → refl
    𝟘 ω 𝟙 𝟙 𝟙 → refl
    𝟘 ω 𝟙 𝟙 ω → refl
    𝟘 ω 𝟙 ω 𝟘 → refl
    𝟘 ω 𝟙 ω 𝟙 → refl
    𝟘 ω 𝟙 ω ω → refl
    𝟘 ω ω 𝟘 𝟘 → refl
    𝟘 ω ω 𝟘 𝟙 → refl
    𝟘 ω ω 𝟘 ω → refl
    𝟘 ω ω 𝟙 𝟘 → refl
    𝟘 ω ω 𝟙 𝟙 → refl
    𝟘 ω ω 𝟙 ω → refl
    𝟘 ω ω ω 𝟘 → refl
    𝟘 ω ω ω 𝟙 → refl
    𝟘 ω ω ω ω → refl
    𝟙 𝟘 𝟘 𝟘 𝟘 → refl
    𝟙 𝟘 𝟘 𝟘 𝟙 → refl
    𝟙 𝟘 𝟘 𝟘 ω → refl
    𝟙 𝟘 𝟘 𝟙 𝟘 → refl
    𝟙 𝟘 𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 𝟙 ω → refl
    𝟙 𝟘 𝟘 ω 𝟘 → refl
    𝟙 𝟘 𝟘 ω 𝟙 → refl
    𝟙 𝟘 𝟘 ω ω → refl
    𝟙 𝟘 𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 𝟘 𝟙 → refl
    𝟙 𝟘 𝟙 𝟘 ω → refl
    𝟙 𝟘 𝟙 𝟙 𝟘 → refl
    𝟙 𝟘 𝟙 𝟙 𝟙 → refl
    𝟙 𝟘 𝟙 𝟙 ω → refl
    𝟙 𝟘 𝟙 ω 𝟘 → refl
    𝟙 𝟘 𝟙 ω 𝟙 → refl
    𝟙 𝟘 𝟙 ω ω → refl
    𝟙 𝟘 ω 𝟘 𝟘 → refl
    𝟙 𝟘 ω 𝟘 𝟙 → refl
    𝟙 𝟘 ω 𝟘 ω → refl
    𝟙 𝟘 ω 𝟙 𝟘 → refl
    𝟙 𝟘 ω 𝟙 𝟙 → refl
    𝟙 𝟘 ω 𝟙 ω → refl
    𝟙 𝟘 ω ω 𝟘 → refl
    𝟙 𝟘 ω ω 𝟙 → refl
    𝟙 𝟘 ω ω ω → refl
    𝟙 𝟙 𝟘 𝟘 𝟘 → refl
    𝟙 𝟙 𝟘 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 𝟘 ω → refl
    𝟙 𝟙 𝟘 𝟙 𝟘 → refl
    𝟙 𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟙 𝟘 𝟙 ω → refl
    𝟙 𝟙 𝟘 ω 𝟘 → refl
    𝟙 𝟙 𝟘 ω 𝟙 → refl
    𝟙 𝟙 𝟘 ω ω → refl
    𝟙 𝟙 𝟙 𝟘 𝟘 → refl
    𝟙 𝟙 𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 𝟙 𝟙 ω → refl
    𝟙 𝟙 𝟙 ω 𝟘 → refl
    𝟙 𝟙 𝟙 ω 𝟙 → refl
    𝟙 𝟙 𝟙 ω ω → refl
    𝟙 𝟙 ω 𝟘 𝟘 → refl
    𝟙 𝟙 ω 𝟘 𝟙 → refl
    𝟙 𝟙 ω 𝟘 ω → refl
    𝟙 𝟙 ω 𝟙 𝟘 → refl
    𝟙 𝟙 ω 𝟙 𝟙 → refl
    𝟙 𝟙 ω 𝟙 ω → refl
    𝟙 𝟙 ω ω 𝟘 → refl
    𝟙 𝟙 ω ω 𝟙 → refl
    𝟙 𝟙 ω ω ω → refl
    𝟙 ω 𝟘 𝟘 𝟘 → refl
    𝟙 ω 𝟘 𝟘 𝟙 → refl
    𝟙 ω 𝟘 𝟘 ω → refl
    𝟙 ω 𝟘 𝟙 𝟘 → refl
    𝟙 ω 𝟘 𝟙 𝟙 → refl
    𝟙 ω 𝟘 𝟙 ω → refl
    𝟙 ω 𝟘 ω 𝟘 → refl
    𝟙 ω 𝟘 ω 𝟙 → refl
    𝟙 ω 𝟘 ω ω → refl
    𝟙 ω 𝟙 𝟘 𝟘 → refl
    𝟙 ω 𝟙 𝟘 𝟙 → refl
    𝟙 ω 𝟙 𝟘 ω → refl
    𝟙 ω 𝟙 𝟙 𝟘 → refl
    𝟙 ω 𝟙 𝟙 𝟙 → refl
    𝟙 ω 𝟙 𝟙 ω → refl
    𝟙 ω 𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 ω 𝟙 → refl
    𝟙 ω 𝟙 ω ω → refl
    𝟙 ω ω 𝟘 𝟘 → refl
    𝟙 ω ω 𝟘 𝟙 → refl
    𝟙 ω ω 𝟘 ω → refl
    𝟙 ω ω 𝟙 𝟘 → refl
    𝟙 ω ω 𝟙 𝟙 → refl
    𝟙 ω ω 𝟙 ω → refl
    𝟙 ω ω ω 𝟘 → refl
    𝟙 ω ω ω 𝟙 → refl
    𝟙 ω ω ω ω → refl
    ω 𝟘 𝟘 𝟘 𝟘 → refl
    ω 𝟘 𝟘 𝟘 𝟙 → refl
    ω 𝟘 𝟘 𝟘 ω → refl
    ω 𝟘 𝟘 𝟙 𝟘 → refl
    ω 𝟘 𝟘 𝟙 𝟙 → refl
    ω 𝟘 𝟘 𝟙 ω → refl
    ω 𝟘 𝟘 ω 𝟘 → refl
    ω 𝟘 𝟘 ω 𝟙 → refl
    ω 𝟘 𝟘 ω ω → refl
    ω 𝟘 𝟙 𝟘 𝟘 → refl
    ω 𝟘 𝟙 𝟘 𝟙 → refl
    ω 𝟘 𝟙 𝟘 ω → refl
    ω 𝟘 𝟙 𝟙 𝟘 → refl
    ω 𝟘 𝟙 𝟙 𝟙 → refl
    ω 𝟘 𝟙 𝟙 ω → refl
    ω 𝟘 𝟙 ω 𝟘 → refl
    ω 𝟘 𝟙 ω 𝟙 → refl
    ω 𝟘 𝟙 ω ω → refl
    ω 𝟘 ω 𝟘 𝟘 → refl
    ω 𝟘 ω 𝟘 𝟙 → refl
    ω 𝟘 ω 𝟘 ω → refl
    ω 𝟘 ω 𝟙 𝟘 → refl
    ω 𝟘 ω 𝟙 𝟙 → refl
    ω 𝟘 ω 𝟙 ω → refl
    ω 𝟘 ω ω 𝟘 → refl
    ω 𝟘 ω ω 𝟙 → refl
    ω 𝟘 ω ω ω → refl
    ω 𝟙 𝟘 𝟘 𝟘 → refl
    ω 𝟙 𝟘 𝟘 𝟙 → refl
    ω 𝟙 𝟘 𝟘 ω → refl
    ω 𝟙 𝟘 𝟙 𝟘 → refl
    ω 𝟙 𝟘 𝟙 𝟙 → refl
    ω 𝟙 𝟘 𝟙 ω → refl
    ω 𝟙 𝟘 ω 𝟘 → refl
    ω 𝟙 𝟘 ω 𝟙 → refl
    ω 𝟙 𝟘 ω ω → refl
    ω 𝟙 𝟙 𝟘 𝟘 → refl
    ω 𝟙 𝟙 𝟘 𝟙 → refl
    ω 𝟙 𝟙 𝟘 ω → refl
    ω 𝟙 𝟙 𝟙 𝟘 → refl
    ω 𝟙 𝟙 𝟙 𝟙 → refl
    ω 𝟙 𝟙 𝟙 ω → refl
    ω 𝟙 𝟙 ω 𝟘 → refl
    ω 𝟙 𝟙 ω 𝟙 → refl
    ω 𝟙 𝟙 ω ω → refl
    ω 𝟙 ω 𝟘 𝟘 → refl
    ω 𝟙 ω 𝟘 𝟙 → refl
    ω 𝟙 ω 𝟘 ω → refl
    ω 𝟙 ω 𝟙 𝟘 → refl
    ω 𝟙 ω 𝟙 𝟙 → refl
    ω 𝟙 ω 𝟙 ω → refl
    ω 𝟙 ω ω 𝟘 → refl
    ω 𝟙 ω ω 𝟙 → refl
    ω 𝟙 ω ω ω → refl
    ω ω 𝟘 𝟘 𝟘 → refl
    ω ω 𝟘 𝟘 𝟙 → refl
    ω ω 𝟘 𝟘 ω → refl
    ω ω 𝟘 𝟙 𝟘 → refl
    ω ω 𝟘 𝟙 𝟙 → refl
    ω ω 𝟘 𝟙 ω → refl
    ω ω 𝟘 ω 𝟘 → refl
    ω ω 𝟘 ω 𝟙 → refl
    ω ω 𝟘 ω ω → refl
    ω ω 𝟙 𝟘 𝟘 → refl
    ω ω 𝟙 𝟘 𝟙 → refl
    ω ω 𝟙 𝟘 ω → refl
    ω ω 𝟙 𝟙 𝟘 → refl
    ω ω 𝟙 𝟙 𝟙 → refl
    ω ω 𝟙 𝟙 ω → refl
    ω ω 𝟙 ω 𝟘 → refl
    ω ω 𝟙 ω 𝟙 → refl
    ω ω 𝟙 ω ω → refl
    ω ω ω 𝟘 𝟘 → refl
    ω ω ω 𝟘 𝟙 → refl
    ω ω ω 𝟘 ω → refl
    ω ω ω 𝟙 𝟘 → refl
    ω ω ω 𝟙 𝟙 → refl
    ω ω ω 𝟙 ω → refl
    ω ω ω ω 𝟘 → refl
    ω ω ω ω 𝟙 → refl
    ω ω ω ω ω → refl

-- The function linearity→affine is not an order embedding from a
-- linear types modality to an affine types modality.

¬linearity⇨affine :
  ¬ Is-order-embedding (linearityModality v₁) (affineModality v₂)
      linearity→affine
¬linearity⇨affine m =
  case Is-order-embedding.tr-order-reflecting m {p = 𝟙} {q = 𝟘} refl of
    λ ()

------------------------------------------------------------------------
-- Σ-morphisms and order embeddings for Σ

-- The function erasure→zero-one-many-Σ is an order embedding for Σ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- a zero-one-many-modality modality, given that if the second
-- modality allows 𝟘ᵐ, then the first also does this. The
-- zero-one-many-modality modality can be defined with either 𝟙 ≤ 𝟘 or
-- 𝟙 ≰ 𝟘.

erasure⇨zero-one-many-Σ :
  (T (𝟘ᵐ-allowed v₂) → T (𝟘ᵐ-allowed v₁)) →
  Is-Σ-order-embedding
    (ErasureModality v₁)
    (zero-one-many-modality 𝟙≤𝟘 v₂)
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
  (T (𝟘ᵐ-allowed v₂) → T (𝟘ᵐ-allowed v₁)) →
  Is-Σ-order-embedding (ErasureModality v₁) (linearityModality v₂)
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
  (T (𝟘ᵐ-allowed v₂) → T (𝟘ᵐ-allowed v₁)) →
  Is-Σ-order-embedding (ErasureModality v₁) (affineModality v₂)
    erasure→zero-one-many erasure→zero-one-many-Σ
erasure⇨affine-Σ = erasure⇨zero-one-many-Σ

-- The function affine→linear-or-affine-Σ is an order embedding for Σ
-- (with respect to affine→linear-or-affine) from an affine types
-- modality to a linear or affine types modality, given that if the
-- second modality allows 𝟘ᵐ, then the first also does this.

affine⇨linear-or-affine-Σ :
  (T (𝟘ᵐ-allowed v₂) → T (𝟘ᵐ-allowed v₁)) →
  Is-Σ-order-embedding (affineModality v₁) (linear-or-affine v₂)
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
  , affineModality variant
  , linear-or-affine variant
  , affine→linear-or-affine , affine→linear-or-affine-Σ
  , affine⇨linear-or-affine refl _
  , Is-Σ-order-embedding.tr-Σ-morphism (affine⇨linear-or-affine-Σ _)
  , affine⇨linear-or-affine-Σ _
  , affine→linear-or-affine-Σ-not-monotone ∘→ Is-morphism.tr-monotone
  , affine→linear-or-affine-Σ-not-monotone ∘→
    Is-order-embedding.tr-monotone
  where
  variant = nr-available-and-𝟘ᵐ-allowed-if _ true

-- The function affine→linearity-Σ is a Σ-morphism (with respect to
-- affine→linearity) from an affine types modality to a linear types
-- modality, given that if the second modality allows 𝟘ᵐ, then the
-- first also does this.

affine⇨linearity-Σ :
  (T (𝟘ᵐ-allowed v₂) → T (𝟘ᵐ-allowed v₁)) →
  Is-Σ-morphism (affineModality v₁) (linearityModality v₂)
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
  ¬ Is-Σ-order-embedding
      (affineModality v₁)
      (linearityModality v₂)
      affine→linearity affine→linearity-Σ
¬affine⇨linearity-Σ m =
  case
    Is-Σ-order-embedding.tr-≤-tr-Σ-→ m {p = 𝟙} {q = ω} {r = ω} refl
  of λ where
    (𝟘 , () , _)
    (𝟙 , _  , ())
    (ω , _  , ())
