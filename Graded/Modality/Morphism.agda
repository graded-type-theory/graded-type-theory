------------------------------------------------------------------------
-- Modality morphisms
------------------------------------------------------------------------

module Graded.Modality.Morphism where

open import Tools.Bool hiding (∧-decreasingˡ)
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

open import Graded.Modality
open import Graded.Modality.Nr-instances
import Graded.Modality.Properties

private variable
  a₁ a₂                  : Level
  M M₁ M₂                : Set _
  𝕄 𝕄₁ 𝕄₂ 𝕄₃             : Modality _
  tr tr₁ tr₂ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q q₁ q₂ q₃ q₄ r s    : M

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
  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    open module M₂ = Modality 𝕄₂ using (_≤_; _<_)
    module MP₁ = Graded.Modality.Properties 𝕄₁

  field
    -- If the target modality is trivial, then the source modality is
    -- trivial.
    first-trivial-if-second-trivial : M₂.Trivial → M₁.Trivial

    -- The translation of 𝟘 is bounded by 𝟘.
    tr-𝟘-≤ : tr M₁.𝟘 ≤ M₂.𝟘

    -- Either the source modality is trivial, or a quantity p is
    -- mapped to 𝟘 exactly when p itself is 𝟘.
    trivial-⊎-tr-≡-𝟘-⇔ : M₁.Trivial ⊎ (∀ {p} → tr p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘)

    -- The translation of 𝟙 is bounded by 𝟙.
    tr-𝟙 : tr M₁.𝟙 ≤ M₂.𝟙

    -- The translation of ω is bounded by ω.
    tr-ω : tr M₁.ω ≤ M₂.ω

    -- The translation commutes with addition.
    tr-+ : ∀ {p q} → tr (p M₁.+ q) ≡ tr p M₂.+ tr q

    -- The translation commutes with multiplication.
    tr-· : ∀ {p q} → tr (p M₁.· q) ≡ tr p M₂.· tr q

    -- The translation commutes with meet up to _≤_.
    tr-∧ : ∀ {p q} → tr (p M₁.∧ q) ≤ tr p M₂.∧ tr q

  -- If the source modality is not trivial, then the target modality
  -- is not trivial.

  second-not-trivial-if-first-not : ¬ M₁.Trivial → ¬ M₂.Trivial
  second-not-trivial-if-first-not = _∘→ first-trivial-if-second-trivial

  opaque

    -- If the source modality is not trivial, then a quantity p is
    -- mapped to 𝟘 exactly when p itself is 𝟘.

    tr-≡-𝟘-⇔ : ¬ M₁.Trivial → tr p ≡ M₂.𝟘 ⇔ p ≡ M₁.𝟘
    tr-≡-𝟘-⇔ non-trivial = case trivial-⊎-tr-≡-𝟘-⇔ of λ where
      (inj₁ trivial)  → ⊥-elim $ non-trivial trivial
      (inj₂ tr-≡-𝟘-⇔) → tr-≡-𝟘-⇔

  -- If the source modality is not trivial, then 𝟘 is translated to 𝟘.

  tr-𝟘-≡ : ¬ M₁.Trivial → tr M₁.𝟘 ≡ M₂.𝟘
  tr-𝟘-≡ ok = tr-≡-𝟘-⇔ ok .proj₂ refl

  opaque

    -- Either the source modality is trivial, or the translation of 𝟘
    -- is equal to 𝟘.

    trivial-⊎-tr-𝟘 : M₁.Trivial ⊎ (tr M₁.𝟘 ≡ M₂.𝟘)
    trivial-⊎-tr-𝟘 = case trivial-⊎-tr-≡-𝟘-⇔ of λ where
      (inj₁ trivial₁) → inj₁ trivial₁
      (inj₂ tr-≡-𝟘-⇔) → inj₂ (tr-≡-𝟘-⇔ .proj₂ refl)

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

  opaque

    -- The translation commutes with nrᵢ.

    tr-nrᵢ : ∀ {r z s} i → tr (M₁.nrᵢ r z s i) ≡ M₂.nrᵢ (tr r) (tr z) (tr s) i
    tr-nrᵢ 0 = refl
    tr-nrᵢ {r} {z} {s} (1+ i) = begin
      tr (s M₁.+ r M₁.· M₁.nrᵢ r z s i)                 ≡⟨ tr-+ ⟩
      tr s M₂.+ tr (r M₁.· M₁.nrᵢ r z s i)              ≡⟨ M₂.+-congˡ tr-· ⟩
      tr s M₂.+ tr r M₂.· tr (M₁.nrᵢ r z s i)           ≡⟨ M₂.+-congˡ (M₂.·-congˡ (tr-nrᵢ i)) ⟩
      tr s M₂.+ tr r M₂.· M₂.nrᵢ (tr r) (tr z) (tr s) i ∎
      where
      open Tools.Reasoning.PropositionalEquality

-- The property of being an order embedding.

record Is-order-embedding
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module P₁ = Graded.Modality.Properties 𝕄₁
    module P₂ = Graded.Modality.Properties 𝕄₂

  field
    -- The translation tr is a morphism.
    tr-morphism : Is-morphism 𝕄₁ 𝕄₂ tr

    -- The translation is order-reflecting.
    tr-order-reflecting : ∀ {p q} → tr p M₂.≤ tr q → p M₁.≤ q


    -- For every target quantity p there is a source quantity p′ such
    -- that the translation of p′ is bounded by p.
    tr-≤ : ∀ {p} → ∃ λ p′ → tr p′ M₂.≤ p

    -- If the translation of p is bounded by 𝟙, then p is bounded by
    -- 𝟙.
    tr-≤-𝟙 : ∀ {p} → tr p M₂.≤ M₂.𝟙 → p M₁.≤ M₁.𝟙

    -- The translation of ω is equal to ω.
    tr-ω : tr M₁.ω ≡ M₂.ω

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

  open Is-morphism tr-morphism public hiding (tr-ω)

  -- The translation is injective.

  tr-injective : ∀ {p q} → tr p ≡ tr q → p ≡ q
  tr-injective tr-p≡tr-q = P₁.≤-antisym
    (tr-order-reflecting (P₂.≤-reflexive tr-p≡tr-q))
    (tr-order-reflecting (P₂.≤-reflexive (sym tr-p≡tr-q)))

  opaque

    -- If the translation of p is bounded by M₂.ω · q, then there is a
    -- q′ such that the translation of q′ is bounded by q, and p is
    -- bounded by M₁.ω · q′.

    tr-≤-ω· :
      tr p M₂.≤ M₂.ω M₂.· q →
      ∃ λ q′ → tr q′ M₂.≤ q × p M₁.≤ M₁.ω M₁.· q′
    tr-≤-ω· {p} {q} tr-p≤ωq =
      tr-≤-· $ begin
        tr p            ≤⟨ tr-p≤ωq ⟩
        M₂.ω M₂.· q     ≡˘⟨ M₂.·-congʳ tr-ω ⟩
        tr M₁.ω M₂.· q  ∎
      where
      open Tools.Reasoning.PartialOrder P₂.≤-poset

  opaque

    -- A combination of tr-≤-ω· and tr-≤-+.

    tr-≤-ω·+ :
      tr p M₂.≤ M₂.ω M₂.· (q M₂.+ r) →
      ∃₂ λ q′ r′ →
        tr q′ M₂.≤ q × tr r′ M₂.≤ r × p M₁.≤ M₁.ω M₁.· (q′ M₁.+ r′)
    tr-≤-ω·+ {p} {q} {r} tr-p≤ω[q+r] =
      case tr-≤-ω· tr-p≤ω[q+r] of λ
        (s , tr-s≤q+r , p≤ωs) →
      case tr-≤-+ tr-s≤q+r of λ
        (q′ , r′ , tr-q′≤q , tr-r′≤r , s≤q′+r′) →
      q′ , r′ , tr-q′≤q , tr-r′≤r , (begin
        p                       ≤⟨ p≤ωs ⟩
        M₁.ω M₁.· s             ≤⟨ P₁.·-monotoneʳ s≤q′+r′ ⟩
        M₁.ω M₁.· (q′ M₁.+ r′)  ∎)
      where
      open Tools.Reasoning.PartialOrder P₁.≤-poset

-- The property of being a Σ-morphism (with respect to a given
-- function).
--
-- Note that Σ-morphisms do not have to be morphisms (see
-- Graded.Modality.Morphism.Examples.Σ-order-embedding-but-not-order-embedding).

record Is-Σ-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module M₁  = Modality 𝕄₁
    module M₂  = Modality 𝕄₂
    module MP₁ = Graded.Modality.Properties 𝕄₁

  field
    -- The regular translation function tr is bounded by the
    -- Σ-translation tr-Σ.
    tr-≤-tr-Σ : ∀ {p} → tr p M₂.≤ tr-Σ p

    -- If the source modality is not trivial, then tr-Σ translates 𝟘
    -- to 𝟘.
    tr-Σ-𝟘-≡ : ¬ M₁.Trivial → tr-Σ M₁.𝟘 ≡ M₂.𝟘

    -- If p is bounded by 𝟙, then tr-Σ p is bounded by 𝟙.
    tr-Σ-≤-𝟙 : ∀ {p} → p M₁.≤ M₁.𝟙 → tr-Σ p M₂.≤ M₂.𝟙

    -- The quantity tr p · tr-Σ q is bounded by the translation of
    -- p · q.
    tr-·-tr-Σ-≤ : ∀ {p q} → tr p M₂.· tr-Σ q M₂.≤ tr (p M₁.· q)

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
-- embeddings (see
-- Graded.Modality.Morphism.Examples.Σ-order-embedding-but-not-order-embedding).

record Is-Σ-order-embedding
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

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

-- The property of being an "nr-preserving" morphism (related to
-- the usage rule for natrec with an nr function).

record Is-nr-preserving-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  ⦃ has-nr₁ : Has-nr M₁ (Modality.semiring-with-meet 𝕄₁) ⦄
  ⦃ has-nr₂ : Has-nr M₂ (Modality.semiring-with-meet 𝕄₂) ⦄
  (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where

  no-eta-equality
  open Modality 𝕄₂

  -- The translation commutes with nr up to _≤_.

  field
    tr-nr :
      ∀ {p r z s n} →
      tr (nr p r z s n) ≤ nr (tr p) (tr r) (tr z) (tr s) (tr n)

-- The property of being a "no-nr-glb-preserving" morphism (related to
-- the usage rule for natrec with greatest lower bounds.

record Is-no-nr-glb-preserving-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where

  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂

  field

    -- If a greatest lower bound of nrᵢ exists in the source modality
    -- then the translated sequence has a greatest lower bound in the
    -- target modality.

    tr-nrᵢ-GLB :
      ∀ {p r z s} →
      M₁.Greatest-lower-bound p (M₁.nrᵢ r z s) →
      ∃ λ q → M₂.Greatest-lower-bound q (M₂.nrᵢ (tr r) (tr z) (tr s))

    -- A similar property to the one above where the second argument of
    -- nrᵢ in the target modality is 𝟙 instead of tr 𝟙.

    tr-nrᵢ-𝟙-GLB :
      ∀ {q p r} →
      M₁.Greatest-lower-bound q (M₁.nrᵢ r M₁.𝟙 p) →
      ∃ λ q′ → M₂.Greatest-lower-bound q′ (M₂.nrᵢ (tr r) M₂.𝟙 (tr p))

-- The property of being an "nr-reflecting" morphism (related to
-- the usage rule for natrec with an nr function).

record Is-nr-reflecting-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  ⦃ has-nr₁ : Has-nr M₁ (Modality.semiring-with-meet 𝕄₁) ⦄
  ⦃ has-nr₂ : Has-nr M₂ (Modality.semiring-with-meet 𝕄₂) ⦄
  (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where

  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂

  field

    -- A variant of the properties of order embeddings for nr

    tr-≤-nr :
      ∀ {q p r z₁ s₁ n₁} →
      tr q M₂.≤ nr (tr p) (tr r) z₁ s₁ n₁ →
      ∃₃ λ z₂ s₂ n₂ →
         tr z₂ M₂.≤ z₁ × tr s₂ M₂.≤ s₁ × tr n₂ M₂.≤ n₁ ×
         q M₁.≤ nr p r z₂ s₂ n₂

-- The property of being a "no-nr-glb-reflecting" morphism (related to
-- the usage rule for natrec with greatest lower bounds.

record Is-no-nr-glb-reflecting-morphism
  {M₁ : Set a₁} {M₂ : Set a₂}
  (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂)
  (tr : M₁ → M₂) : Set (a₁ ⊔ a₂) where

  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂

  field

    -- Variants of the properties of order embeddings for the
    -- alternative usage rule for natrec using greatest lower bounds.

     tr-≤-no-nr :
       ∀ {x y p p′ q r z s} →
       tr p′ M₂.≤ x M₂.· q M₂.+ y →
       M₂.Greatest-lower-bound x (M₂.nrᵢ (tr r) M₂.𝟙 (tr p)) →
       M₂.Greatest-lower-bound y (M₂.nrᵢ (tr r) z s) →
       ∃₅ λ z′ s′ q′ x′ y′ → tr z′ M₂.≤ z × tr s′ M₂.≤ s × tr q′ M₂.≤ q ×
          M₁.Greatest-lower-bound x′ (M₁.nrᵢ r M₁.𝟙 p) ×
          M₁.Greatest-lower-bound y′ (M₁.nrᵢ r z′ s′) ×
          p′ M₁.≤ x′ M₁.· q′ M₁.+ y′

     tr-nrᵢ-glb :
       M₂.Greatest-lower-bound q (M₂.nrᵢ (tr r) M₂.𝟙 (tr p)) →
       ∃ λ q′ → M₁.Greatest-lower-bound q′ (M₁.nrᵢ r M₁.𝟙 p)

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
    .Is-Σ-morphism.tr-Σ-𝟘-≡ →
      tr-𝟘-≡
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
  module MP₁ = Graded.Modality.Properties 𝕄₁
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
    .tr-≤                → _ , ≤-refl
    .tr-≤-𝟙              → idᶠ
    .tr-ω                → refl
    .tr-≤-+ hyp          → _ , _ , ≤-refl , ≤-refl , hyp
    .tr-≤-· hyp          → _ , ≤-refl , hyp
    .tr-≤-∧ hyp          → _ , _ , ≤-refl , ≤-refl , hyp
    .tr-morphism         → λ where
      .tr-𝟙                                    → ≤-refl
      .tr-ω                                    → ≤-refl
      .tr-𝟘-≤                                  → ≤-refl
      .trivial-⊎-tr-≡-𝟘-⇔                      → inj₂ (idᶠ , idᶠ)
      .tr-+                                    → refl
      .tr-·                                    → refl
      .tr-∧                                    → ≤-refl
      .first-trivial-if-second-trivial         → idᶠ
  where
  open Graded.Modality.Properties 𝕄
  open Is-morphism
  open Is-order-embedding

Is-nr-preserving-morphism-id :
  ⦃ has-nr : Has-nr _ (Modality.semiring-with-meet 𝕄) ⦄ →
  Is-nr-preserving-morphism 𝕄 𝕄 idᶠ
Is-nr-preserving-morphism-id {𝕄} = λ where
    .tr-nr → ≤-refl
  where
  open Is-nr-preserving-morphism
  open Graded.Modality.Properties 𝕄

Is-no-nr-glb-preserving-morphism-id :
  Is-no-nr-glb-preserving-morphism 𝕄 𝕄 idᶠ
Is-no-nr-glb-preserving-morphism-id = λ where
    .tr-nrᵢ-GLB → _ ,_
    .tr-nrᵢ-𝟙-GLB → _ ,_
  where
  open Is-no-nr-glb-preserving-morphism

Is-nr-reflecting-morphism-id :
  ⦃ has-nr : Has-nr _ (Modality.semiring-with-meet 𝕄) ⦄ →
  Is-nr-reflecting-morphism 𝕄 𝕄 idᶠ
Is-nr-reflecting-morphism-id {𝕄} = λ where
    .tr-≤-nr hyp →
      _ , _ , _ , ≤-refl , ≤-refl , ≤-refl , hyp
  where
  open Is-nr-reflecting-morphism
  open Graded.Modality.Properties 𝕄

Is-no-nr-glb-reflecting-morphism-id :
  Is-no-nr-glb-reflecting-morphism 𝕄 𝕄 idᶠ
Is-no-nr-glb-reflecting-morphism-id {𝕄} = λ where
    .tr-≤-no-nr p′≤ x-glb y-glb →
      _ , _ , _ , _ , _ , ≤-refl , ≤-refl , ≤-refl
        , x-glb , y-glb , p′≤
    .tr-nrᵢ-glb → _ ,_
  where
  open Is-no-nr-glb-reflecting-morphism
  open Graded.Modality.Properties 𝕄

------------------------------------------------------------------------
-- Composition

-- Composition preserves Is-morphism.

Is-morphism-∘ :
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-morphism 𝕄₁ 𝕄₂ tr₂ →
  Is-morphism 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂)
Is-morphism-∘
  {𝕄₂ = 𝕄₂} {𝕄₃ = 𝕄₃} {tr₁ = tr₁} {𝕄₁ = 𝕄₁} {tr₂ = tr₂} f g = λ where
    .Is-morphism.first-trivial-if-second-trivial →
      G.first-trivial-if-second-trivial ∘→
      F.first-trivial-if-second-trivial
    .Is-morphism.tr-𝟘-≤ → let open R in begin
       tr₁ (tr₂ M₁.𝟘)  ≤⟨ F.tr-monotone G.tr-𝟘-≤ ⟩
       tr₁ M₂.𝟘        ≤⟨ F.tr-𝟘-≤ ⟩
       M₃.𝟘            ∎
    .Is-morphism.trivial-⊎-tr-≡-𝟘-⇔ →
      case F.trivial-⊎-tr-≡-𝟘-⇔ of λ where
        (inj₁ trivial₂) →
          inj₁ (G.first-trivial-if-second-trivial trivial₂)
        (inj₂ tr-≡-𝟘-⇔₂) → case G.trivial-⊎-tr-≡-𝟘-⇔ of λ where
          (inj₁ trivial₁)  → inj₁ trivial₁
          (inj₂ tr-≡-𝟘-⇔₁) → inj₂ (λ {_} → tr-≡-𝟘-⇔₁ ∘⇔ tr-≡-𝟘-⇔₂)
    .Is-morphism.tr-𝟙 → let open R in begin
       tr₁ (tr₂ M₁.𝟙)  ≤⟨ F.tr-monotone G.tr-𝟙 ⟩
       tr₁ M₂.𝟙        ≤⟨ F.tr-𝟙 ⟩
       M₃.𝟙            ∎
    .Is-morphism.tr-ω → let open R in begin
       tr₁ (tr₂ M₁.ω)  ≤⟨ F.tr-monotone G.tr-ω ⟩
       tr₁ M₂.ω        ≤⟨ F.tr-ω ⟩
       M₃.ω            ∎
    .Is-morphism.tr-+ {p = p} {q = q} →
      let open Tools.Reasoning.PropositionalEquality in
      tr₁ (tr₂ (p M₁.+ q))          ≡⟨ cong tr₁ G.tr-+ ⟩
      tr₁ (tr₂ p M₂.+ tr₂ q)        ≡⟨ F.tr-+ ⟩
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
  where
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module M₃  = Modality 𝕄₃
  module F   = Is-morphism f
  module G   = Is-morphism g
  module MP₂ = Graded.Modality.Properties 𝕄₂
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
    .Is-order-embedding.tr-ω →
      let open Tools.Reasoning.PropositionalEquality in
      tr₁ (tr₂ M₁.ω)  ≡⟨ cong tr₁ G.tr-ω ⟩
      tr₁ M₂.ω        ≡⟨ F.tr-ω ⟩
      M₃.ω            ∎
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
  where
  module MP₂ = Graded.Modality.Properties 𝕄₂
  module MP₃ = Graded.Modality.Properties 𝕄₃
  module M₁  = Modality 𝕄₁
  module M₂  = Modality 𝕄₂
  module M₃  = Modality 𝕄₃
  module F   = Is-order-embedding f
  module G   = Is-order-embedding g

-- Composition preserves Is-Σ-morphism given certain assumptions.

Is-Σ-morphism-∘ :
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-morphism 𝕄₁ 𝕄₂ tr₂ →
  Is-Σ-morphism 𝕄₂ 𝕄₃ tr₁ tr-Σ₁ →
  Is-Σ-morphism 𝕄₁ 𝕄₂ tr₂ tr-Σ₂ →
  Is-Σ-morphism 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Is-Σ-morphism-∘
  {𝕄₂} {𝕄₃} {tr₁} {𝕄₁} {tr₂} {tr-Σ₁} {tr-Σ₂} m₁ m₂ f g = record
  { tr-≤-tr-Σ = λ {p = p} →
      let open Tools.Reasoning.PartialOrder ≤-poset in begin
      tr₁ (tr₂ p)      ≤⟨ Is-morphism.tr-monotone m₁ G.tr-≤-tr-Σ ⟩
      tr₁ (tr-Σ₂ p)    ≤⟨ F.tr-≤-tr-Σ ⟩
      tr-Σ₁ (tr-Σ₂ p)  ∎
  ; tr-Σ-𝟘-≡ = λ not-trivial →
      let open Tools.Reasoning.PropositionalEquality in
      tr-Σ₁ (tr-Σ₂ M₁.𝟘)  ≡⟨ cong tr-Σ₁ (G.tr-Σ-𝟘-≡ not-trivial) ⟩
      tr-Σ₁ M₂.𝟘          ≡⟨ F.tr-Σ-𝟘-≡ (Is-morphism.second-not-trivial-if-first-not m₂ not-trivial) ⟩
      M₃.𝟘                ∎
  ; tr-Σ-≤-𝟙 =
      F.tr-Σ-≤-𝟙 ∘→ G.tr-Σ-≤-𝟙
  ; tr-·-tr-Σ-≤ = λ {p = p} {q = q} →
      let open Tools.Reasoning.PartialOrder ≤-poset in begin
      tr₁ (tr₂ p) M₃.· tr-Σ₁ (tr-Σ₂ q)  ≤⟨ F.tr-·-tr-Σ-≤ ⟩
      tr₁ (tr₂ p M₂.· tr-Σ₂ q)          ≤⟨ Is-morphism.tr-monotone m₁ G.tr-·-tr-Σ-≤ ⟩
      tr₁ (tr₂ (p M₁.· q))              ∎
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  module M₃ = Modality 𝕄₃
  module F  = Is-Σ-morphism f
  module G  = Is-Σ-morphism g
  open Graded.Modality.Properties 𝕄₃

-- Composition preserves Is-Σ-order-embedding given certain
-- assumptions.

Is-Σ-order-embedding-∘ :
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-morphism 𝕄₁ 𝕄₂ tr₂ →
  Is-Σ-order-embedding 𝕄₂ 𝕄₃ tr₁ tr-Σ₁ →
  Is-Σ-order-embedding 𝕄₁ 𝕄₂ tr₂ tr-Σ₂ →
  Is-Σ-order-embedding 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
Is-Σ-order-embedding-∘
  {𝕄₃} {tr₁} {tr₂} {tr-Σ₁} {tr-Σ₂} m₁ m₂ f g = record
  { tr-Σ-morphism =
      Is-Σ-morphism-∘ m₁ m₂ F.tr-Σ-morphism G.tr-Σ-morphism
  ; tr-≤-tr-Σ-→ = λ {p = _} {q = _} {r = r} tr-p≤tr-q·r →
      case F.tr-≤-tr-Σ-→ tr-p≤tr-q·r of
        λ (r′ , tr-r′≤r , tr-p≤tr-q·r′) →
      case G.tr-≤-tr-Σ-→ tr-p≤tr-q·r′ of
        λ (r″ , tr-r″≤r′ , p≤q·r″) →
        r″
      , (begin
           tr₁ (tr₂ r″)  ≤⟨ Is-morphism.tr-monotone m₁ tr-r″≤r′ ⟩
           tr₁ r′        ≤⟨ tr-r′≤r ⟩
           r             ∎)
      , p≤q·r″
  }
  where
  module F = Is-Σ-order-embedding f
  module G = Is-Σ-order-embedding g
  open Graded.Modality.Properties 𝕄₃
  open Tools.Reasoning.PartialOrder ≤-poset

Is-nr-preserving-morphism-∘ :
  ⦃ has-nr₁ : Has-nr _ (Modality.semiring-with-meet 𝕄₁) ⦄ →
  ⦃ has-nr₂ : Has-nr _ (Modality.semiring-with-meet 𝕄₂) ⦄ →
  ⦃ has-nr₃ : Has-nr _ (Modality.semiring-with-meet 𝕄₃) ⦄ →
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-nr-preserving-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-nr-preserving-morphism 𝕄₁ 𝕄₂ tr₂ →
  Is-nr-preserving-morphism 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂)
Is-nr-preserving-morphism-∘ {𝕄₃} {tr₁} {tr₂} m f g = λ where
    .tr-nr {p} {r} {z} {s} {n} → begin
      tr₁ (tr₂ (nr p r z s n))                         ≤⟨ Is-morphism.tr-monotone m (Is-nr-preserving-morphism.tr-nr g) ⟩
      tr₁ (nr (tr₂ p) (tr₂ r) (tr₂ z) (tr₂ s) (tr₂ n)) ≤⟨ Is-nr-preserving-morphism.tr-nr f ⟩
      nr (tr₁ (tr₂ p)) (tr₁ (tr₂ r)) (tr₁ (tr₂ z))
        (tr₁ (tr₂ s)) (tr₁ (tr₂ n))                    ∎
  where
  open Is-nr-preserving-morphism
  open Graded.Modality.Properties 𝕄₃
  open Tools.Reasoning.PartialOrder ≤-poset

Is-no-nr-glb-preserving-morphism-∘ :
  Is-no-nr-glb-preserving-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-no-nr-glb-preserving-morphism 𝕄₁ 𝕄₂ tr₂ →
  Is-no-nr-glb-preserving-morphism 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂)
Is-no-nr-glb-preserving-morphism-∘ f g = λ where
    .tr-nrᵢ-GLB →
      F.tr-nrᵢ-GLB ∘→ proj₂ ∘→ G.tr-nrᵢ-GLB
    .tr-nrᵢ-𝟙-GLB →
      F.tr-nrᵢ-𝟙-GLB ∘→ proj₂ ∘→ G.tr-nrᵢ-𝟙-GLB
  where
  module F = Is-no-nr-glb-preserving-morphism f
  module G = Is-no-nr-glb-preserving-morphism g
  open Is-no-nr-glb-preserving-morphism

Is-nr-reflecting-morphism-∘ :
  ⦃ has-nr₁ : Has-nr _ (Modality.semiring-with-meet 𝕄₁) ⦄ →
  ⦃ has-nr₂ : Has-nr _ (Modality.semiring-with-meet 𝕄₂) ⦄ →
  ⦃ has-nr₃ : Has-nr _ (Modality.semiring-with-meet 𝕄₃) ⦄ →
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-nr-reflecting-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-nr-reflecting-morphism 𝕄₁ 𝕄₂ tr₂ →
  Is-nr-reflecting-morphism 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂)
Is-nr-reflecting-morphism-∘ {𝕄₃} m f g = λ where
    .tr-≤-nr q≤ →
      let _ , _ , _ , ≤z , ≤s , ≤n , q≤′ = F.tr-≤-nr q≤
          _ , _ , _ , ≤z′ , ≤s′ , ≤n′ , q≤″ = G.tr-≤-nr q≤′
      in  _ , _ , _
            , ≤-trans (tr-monotone ≤z′) ≤z
            , ≤-trans (tr-monotone ≤s′) ≤s
            , ≤-trans (tr-monotone ≤n′) ≤n
            , q≤″
  where
  module F = Is-nr-reflecting-morphism f
  module G = Is-nr-reflecting-morphism g
  open Is-morphism m
  open Graded.Modality.Properties 𝕄₃
  open Is-nr-reflecting-morphism

Is-no-nr-glb-reflecting-morphism-∘ :
  Is-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-no-nr-glb-reflecting-morphism 𝕄₂ 𝕄₃ tr₁ →
  Is-no-nr-glb-reflecting-morphism 𝕄₁ 𝕄₂ tr₂ →
  Is-no-nr-glb-reflecting-morphism 𝕄₁ 𝕄₃ (tr₁ ∘→ tr₂)
Is-no-nr-glb-reflecting-morphism-∘ {𝕄₃} m f g = λ where
    .tr-≤-no-nr p≤ x-glb y-glb →
      let _ , _ , _ , _ , _ , ≤z , ≤s , ≤q
            , x-glb′ , y-glb′ , p≤′ = F.tr-≤-no-nr p≤ x-glb y-glb
          _ , _ , _ , _ , _ , ≤z′ , ≤s′ , ≤q′
            , x-glb″ , y-glb″ , p≤″ = G.tr-≤-no-nr p≤′ x-glb′ y-glb′
      in  _ , _ , _ , _ , _
            , ≤-trans (tr-monotone ≤z′) ≤z
            , ≤-trans (tr-monotone ≤s′) ≤s
            , ≤-trans (tr-monotone ≤q′) ≤q
            , x-glb″ , y-glb″ , p≤″
    .tr-nrᵢ-glb →
      G.tr-nrᵢ-glb ∘→ proj₂ ∘→ F.tr-nrᵢ-glb
  where
  module F = Is-no-nr-glb-reflecting-morphism f
  module G = Is-no-nr-glb-reflecting-morphism g
  open Is-no-nr-glb-reflecting-morphism
  open Graded.Modality.Properties 𝕄₃
  open Is-morphism m
