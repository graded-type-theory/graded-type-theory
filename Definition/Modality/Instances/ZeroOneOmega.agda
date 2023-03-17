module Definition.Modality.Instances.ZeroOneOmega where

open import Definition.Modality.Restrictions

open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

-- The three element set, forming the basis for several modalities

data 𝟘𝟙ω : Set where
  𝟘 𝟙 ω : 𝟘𝟙ω

open import Tools.Algebra 𝟘𝟙ω
open import Definition.Modality 𝟘𝟙ω

infixl 40 _+_
infixl 45 _·_

-- Addition

_+_ : Op₂ 𝟘𝟙ω
𝟘 + q = q
𝟙 + 𝟘 = 𝟙
𝟙 + 𝟙 = ω
𝟙 + ω = ω
ω + q = ω

-- Multiplication

_·_ : Op₂ 𝟘𝟙ω
𝟘 · q = 𝟘
𝟙 · q = q
ω · 𝟘 = 𝟘
ω · 𝟙 = ω
ω · ω = ω

-----------------------------
-- Properties of addition  --
-----------------------------

-- Addition is commutative
-- p + q ≡ q + p

+-Commutative : Commutative _+_
+-Commutative 𝟘 𝟘 = refl
+-Commutative 𝟘 𝟙 = refl
+-Commutative 𝟘 ω = refl
+-Commutative 𝟙 𝟘 = refl
+-Commutative 𝟙 𝟙 = refl
+-Commutative 𝟙 ω = refl
+-Commutative ω 𝟘 = refl
+-Commutative ω 𝟙 = refl
+-Commutative ω ω = refl

-- Addition is associative
-- p + (q + r) ≡ (p + q) + r

+-Associative : Associative _+_
+-Associative 𝟘 q r = refl
+-Associative 𝟙 𝟘 r = refl
+-Associative 𝟙 𝟙 𝟘 = refl
+-Associative 𝟙 𝟙 𝟙 = refl
+-Associative 𝟙 𝟙 ω = refl
+-Associative 𝟙 ω r = refl
+-Associative ω q r = refl

-- 𝟘 is a left identity of addition
-- 𝟘 + p ≡ p

+-LeftIdentity : LeftIdentity 𝟘 _+_
+-LeftIdentity p = refl

-- 𝟘 is a right identity of addition
-- p + 𝟘 ≡ p

+-RightIdentity : RightIdentity 𝟘 _+_
+-RightIdentity 𝟘 = refl
+-RightIdentity 𝟙 = refl
+-RightIdentity ω = refl

-- 𝟘 is an identity of addition
-- 𝟘 + p ≡ p ≡ p + 𝟘

+-Identity : Identity 𝟘 _+_
+-Identity = +-LeftIdentity , +-RightIdentity

-- ω is zero for addition
-- ω + p = p + ω = ω

+-LeftZero : LeftZero ω _+_
+-LeftZero p = refl

+-RightZero : RightZero ω _+_
+-RightZero p rewrite +-Commutative p ω = refl

+-Zero : Zero ω _+_
+-Zero = +-LeftZero , +-RightZero

----------------------------------
-- Properties of multiplication --
----------------------------------

-- Multiplication is commutative
-- p + q ≡ q + p

·-Commutative : Commutative _·_
·-Commutative 𝟘 𝟘 = refl
·-Commutative 𝟘 𝟙 = refl
·-Commutative 𝟘 ω = refl
·-Commutative 𝟙 𝟘 = refl
·-Commutative 𝟙 𝟙 = refl
·-Commutative 𝟙 ω = refl
·-Commutative ω 𝟘 = refl
·-Commutative ω 𝟙 = refl
·-Commutative ω ω = refl

-- Multiplication is associative
-- p · (q · r) ≡ (p · q) · r

·-Associative : Associative _·_
·-Associative 𝟘 q r = refl
·-Associative 𝟙 q r = refl
·-Associative ω 𝟘 r = refl
·-Associative ω 𝟙 r = refl
·-Associative ω ω 𝟘 = refl
·-Associative ω ω 𝟙 = refl
·-Associative ω ω ω = refl

-- 𝟘 is a left zero for multiplication
-- 𝟘 · p ≡ 𝟘

·-LeftZero : LeftZero 𝟘 _·_
·-LeftZero p = refl

-- 𝟘 is a right zero for multiplication
-- p · 𝟘 ≡ 𝟘

·-RightZero : RightZero 𝟘 _·_
·-RightZero 𝟘 = refl
·-RightZero 𝟙 = refl
·-RightZero ω = refl

-- 𝟘 is a zero for multiplication
-- 𝟘 · p ≡ 𝟘 ≡ p · 𝟘

·-zero : Zero 𝟘 _·_
·-zero = ·-LeftZero , ·-RightZero

-- 𝟙 is a left identity for multiplication
-- 𝟙 · p ≡ p

·-LeftIdentity : LeftIdentity 𝟙 _·_
·-LeftIdentity p = refl

-- 𝟙 is a right identity for multiplication
-- p · 𝟙 ≡ p

·-RightIdentity : RightIdentity 𝟙 _·_
·-RightIdentity 𝟘 = refl
·-RightIdentity 𝟙 = refl
·-RightIdentity ω = refl

-- 𝟙 is an identity for multiplication
-- 𝟙 · p ≡ p ≡ p · 𝟙

·-Identity : Identity 𝟙 _·_
·-Identity = ·-LeftIdentity , ·-RightIdentity

-- Multiplication is idempotent
-- p · p = p

·-Idempotent : Idempotent _·_
·-Idempotent 𝟘 = refl
·-Idempotent 𝟙 = refl
·-Idempotent ω = refl

----------------------------------------------------------
-- Distributive properties of addition, multiplication  --
----------------------------------------------------------

-- Multiplication is left distributive over addition
-- p · (q + r) ≡ (p · q) + (p · r)

·-distribˡ-+ : _·_ DistributesOverˡ _+_
·-distribˡ-+ 𝟘 q r = refl
·-distribˡ-+ 𝟙 q r = refl
·-distribˡ-+ ω 𝟘 r = refl
·-distribˡ-+ ω 𝟙 𝟘 = refl
·-distribˡ-+ ω 𝟙 𝟙 = refl
·-distribˡ-+ ω 𝟙 ω = refl
·-distribˡ-+ ω ω r = refl

-- Multiplication is right distributive over addition
-- (q + r) · p ≡ (q · p) + (r · p)

·-distribʳ-+ : _·_ DistributesOverʳ _+_
·-distribʳ-+ p q r = begin
  (q + r) · p
    ≡⟨ ·-Commutative (q + r) p ⟩
  p · (q + r)
    ≡⟨ ·-distribˡ-+ p q r ⟩
  p · q + p · r
    ≡⟨ cong₂ _+_ (·-Commutative p q) (·-Commutative p r) ⟩
  q · p + r · p ∎
  where open import Tools.Reasoning.PropositionalEquality

-- Multiplication is distributive over addition
-- p · (q + r) ≡ (p · q) + (p · r) and (q + r) · p ≡ (q · p) + (r · p)

·-distrib-+ : _·_ DistributesOver _+_
·-distrib-+ = ·-distribˡ-+ , ·-distribʳ-+

-------------------------------------------
-- Addition forms the following algebras --
-------------------------------------------

-- Addition forms a magma

+-Magma : IsMagma _+_
+-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _+_
  }

-- Addition forms a semigroup

+-Semigroup : IsSemigroup _+_
+-Semigroup = record
  { isMagma = +-Magma
  ; assoc   = +-Associative
  }

-- Addition forms a monoid for 𝟘 as identity

+-Monoid : IsMonoid _+_ 𝟘
+-Monoid = record
  { isSemigroup = +-Semigroup
  ; identity    = +-Identity
  }

-- Addition forms a commutative monoid with 𝟘 as identity

+-CommutativeMonoid : IsCommutativeMonoid _+_ 𝟘
+-CommutativeMonoid = record
  { isMonoid = +-Monoid
  ; comm     = +-Commutative
  }

-------------------------------------------------
-- Multiplication forms the following algebras --
-------------------------------------------------

-- Multiplication forms a magma

·-Magma : IsMagma _·_
·-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _·_
  }

-- Multiplication forms a semigroup

·-Semigroup : IsSemigroup _·_
·-Semigroup = record
  { isMagma = ·-Magma
  ; assoc   = ·-Associative
  }

-- Multiplication forms a monoid with ω as identity

·-Monoid : IsMonoid _·_ 𝟙
·-Monoid = record
  { isSemigroup = ·-Semigroup
  ; identity    = ·-Identity
  }

-------------------------------------------------
-- Addition and Multiplication form a semiring --
-------------------------------------------------

+-·-SemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _+_ _·_ 𝟘 𝟙
+-·-SemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = +-CommutativeMonoid
  ; *-isMonoid = ·-Monoid
  ; distrib = ·-distrib-+
  }

+-·-Semiring : IsSemiring _+_ _·_ 𝟘 𝟙
+-·-Semiring = record
  { isSemiringWithoutAnnihilatingZero = +-·-SemiringWithoutAnnihilatingZero
  ; zero = ·-zero
  }

-- 𝟘𝟙ω is a modality given a lawful semilattice satisfying some extra
-- properties.

𝟘𝟙ωModalityWithout⊛ :
  {_∧_ : Op₂ 𝟘𝟙ω} →
  IsSemilattice _∧_ →
  _·_ DistributesOver _∧_ →
  _+_ DistributesOver _∧_ →
  ω ≡ (ω ∧ 𝟙) →
  𝟘 ≢ (𝟘 ∧ 𝟙) →
  Restrictions 𝟘𝟙ω →
  ModalityWithout⊛
𝟘𝟙ωModalityWithout⊛
  {_∧_ = _∧_}
  ∧-Semilattice ·-distrib-∧ +-distrib-∧ ω≤𝟙 𝟘≰𝟙 restrictions = record
  { _+_ = _+_
  ; _·_ = _·_
  ; _∧_ = _∧_
  ; 𝟘 = 𝟘
  ; 𝟙 = 𝟙
  ; +-·-Semiring = +-·-Semiring
  ; ∧-Semilattice = ∧-Semilattice
  ; ·-distrib-∧ = ·-distrib-∧
  ; +-distrib-∧ = +-distrib-∧
  ; restrictions = restrictions
  ; 𝟘ᵐ→𝟙≉𝟘 = λ _ ()
  ; is-𝟘? = λ where
      𝟘 → yes refl
      𝟙 → no (λ ())
      ω → no (λ ())
  ; zero-product = λ where
      {p = 𝟘} _ → inj₁ refl
      {q = 𝟘} _ → inj₂ refl
  ; positiveˡ = λ where
      {p = 𝟘}         _  → refl
      {p = 𝟙} {q = 𝟘} ()
      {p = 𝟙} {q = 𝟙} ()
      {p = 𝟙} {q = ω} ()
  ; 𝟘≮ = λ where
      {p = 𝟘} _     → refl
      {p = 𝟙} 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘≰𝟙 𝟘≡𝟘∧𝟙)
      {p = ω} 𝟘≡𝟘∧ω →
        case
          ω      ≡⟨ ω≤𝟘 ⟩
          ω ∧ 𝟘  ≡⟨ S.comm _ _ ⟩
          𝟘 ∧ ω  ≡˘⟨ 𝟘≡𝟘∧ω ⟩
          𝟘      ∎
        of λ ()
  ; ∧≤𝟘ˡ = λ where
      {p = 𝟘} _ →
        𝟘      ≡˘⟨ S.idem _ ⟩
        𝟘 ∧ 𝟘  ∎
      {p = 𝟙} {q = 𝟘} 𝟙∧𝟘≡𝟘 → ⊥-elim (𝟘≰𝟙 (
        𝟘      ≡˘⟨ 𝟙∧𝟘≡𝟘 ⟩
        𝟙 ∧ 𝟘  ≡⟨ S.comm _ _ ⟩
        𝟘 ∧ 𝟙  ∎))
      {p = 𝟙} {q = 𝟙} 𝟙∧𝟙≡𝟘 →
        case
          𝟙      ≡˘⟨ S.idem _ ⟩
          𝟙 ∧ 𝟙  ≡⟨ 𝟙∧𝟙≡𝟘 ⟩
          𝟘      ∎
        of λ ()
      {p = 𝟙} {q = ω} 𝟙∧ω≡𝟘 →
        case
          ω      ≡⟨ ω≤𝟙 ⟩
          ω ∧ 𝟙  ≡⟨ S.comm _ _ ⟩
          𝟙 ∧ ω  ≡⟨ 𝟙∧ω≡𝟘 ⟩
          𝟘      ∎
        of λ ()
      {p = ω} _ →
        ω      ≡⟨ ω≤𝟘 ⟩
        ω ∧ 𝟘  ∎
  ; ≉𝟘→≤𝟙 = λ where
      {p = 𝟘} 𝟘≢𝟘 → ⊥-elim (𝟘≢𝟘 refl)
      {p = 𝟙} _   →
        𝟙      ≡˘⟨ S.idem _ ⟩
        𝟙 ∧ 𝟙  ∎
      {p = ω} _ →
        ω      ≡⟨ ω≤𝟙 ⟩
        ω ∧ 𝟙  ∎
  }
  where
  module S = IsSemilattice ∧-Semilattice
  open Tools.Reasoning.PropositionalEquality

  ω∧𝟙∧𝟘≡ω : ω ∧ (𝟙 ∧ 𝟘) ≡ ω
  ω∧𝟙∧𝟘≡ω = helper (𝟙 ∧ 𝟘) refl
    where
    helper : ∀ p → 𝟙 ∧ 𝟘 ≡ p → ω ∧ p ≡ ω
    helper 𝟘 𝟙∧𝟘≡𝟘 =
      ⊥-elim (𝟘≰𝟙 (
        𝟘      ≡˘⟨ 𝟙∧𝟘≡𝟘 ⟩
        𝟙 ∧ 𝟘  ≡⟨ S.comm _ _ ⟩
        𝟘 ∧ 𝟙  ∎))
    helper 𝟙 _ =
      ω ∧ 𝟙  ≡˘⟨ ω≤𝟙 ⟩
      ω      ∎
    helper ω _ =
      ω ∧ ω  ≡⟨ S.idem _ ⟩
      ω      ∎

  ω≤𝟘 : ω ≡ ω ∧ 𝟘
  ω≤𝟘 =
    ω            ≡˘⟨ ω∧𝟙∧𝟘≡ω ⟩
    ω ∧ (𝟙 ∧ 𝟘)  ≡˘⟨ S.assoc _ _ _ ⟩
    (ω ∧ 𝟙) ∧ 𝟘  ≡˘⟨ cong (_∧ _) ω≤𝟙 ⟩
    ω ∧ 𝟘        ∎

-- Meet-dependent implementation of ⊛

module ⊛ (_∧_ : Op₂ 𝟘𝟙ω) (∧-Semilattice : IsSemilattice _∧_)
         (·-distrib-∧ : _·_ DistributesOver _∧_)
         (+-distrib-∧ : _+_ DistributesOver _∧_)
         (ω∧ : (p : 𝟘𝟙ω) → ω ∧ p ≡ ω)
         (𝟘≰𝟙 : 𝟘 ≢ (𝟘 ∧ 𝟙))
         (restrictions : Restrictions 𝟘𝟙ω) where

  open IsSemilattice ∧-Semilattice

  𝟘𝟙ωMod : ModalityWithout⊛
  𝟘𝟙ωMod = 𝟘𝟙ωModalityWithout⊛
    ∧-Semilattice ·-distrib-∧ +-distrib-∧
    (ω      ≡˘⟨ ω∧ _ ⟩
     ω ∧ 𝟙  ∎)
    𝟘≰𝟙 restrictions
    where
    open Tools.Reasoning.PropositionalEquality

  open ModalityWithout⊛ 𝟘𝟙ωMod hiding (𝟘; 𝟙; _+_; _·_; _∧_; ·-distribˡ-+; ·-distribʳ-+)

  open import Definition.Modality.Properties.Addition 𝟘𝟙ωMod
  open import Definition.Modality.Properties.Meet 𝟘𝟙ωMod
  open import Definition.Modality.Properties.Multiplication 𝟘𝟙ωMod
  open import Definition.Modality.Properties.PartialOrder 𝟘𝟙ωMod

  ω≤ : (p : 𝟘𝟙ω) → ω ≤ p
  ω≤ p = PE.sym (ω∧ p)

  _⊛_▷_ : Op₃ 𝟘𝟙ω
  p ⊛ q ▷ 𝟘 = p ∧ q
  p ⊛ q ▷ 𝟙 = p + ω · q
  p ⊛ q ▷ ω = ω · (p ∧ q)

  -- p ⊛ᵣ q ≤ q + r (p ⊛ᵣ q)

  ⊛-ineq₁ : (p q r : 𝟘𝟙ω) → p ⊛ q ▷ r ≤ q + r · (p ⊛ q ▷ r)
  ⊛-ineq₁ p q 𝟘 rewrite +-identityʳ q = ∧-decreasingʳ p q
  ⊛-ineq₁ p 𝟘 𝟙 = ≤-refl
  ⊛-ineq₁ p 𝟙 𝟙 rewrite +-RightZero p = ≤-refl
  ⊛-ineq₁ p ω 𝟙 rewrite +-RightZero p = ≤-refl
  ⊛-ineq₁ p 𝟘 ω rewrite PE.sym (·-assoc ω ω (p ∧ 𝟘)) = ≤-refl
  ⊛-ineq₁ p 𝟙 ω rewrite ·-distribˡ-∧ ω p 𝟙
                rewrite ∧-comm (ω · p) ω
                rewrite ω∧ (ω · p) = ≤-refl
  ⊛-ineq₁ p ω ω rewrite ·-distribˡ-∧ ω p ω = ∧-decreasingʳ (ω · p) ω

  -- p ⊛ᵣ q ≤ p

  ⊛-ineq₂ : (p q r : 𝟘𝟙ω) → p ⊛ q ▷ r ≤ p
  ⊛-ineq₂ p q 𝟘 = ∧-decreasingˡ p q
  ⊛-ineq₂ p 𝟘 𝟙 rewrite +-identityʳ p = ≤-refl
  ⊛-ineq₂ p 𝟙 𝟙 rewrite +-RightZero p = ω≤ p
  ⊛-ineq₂ p ω 𝟙 rewrite +-RightZero p = ω≤ p
  ⊛-ineq₂ p q ω rewrite ·-distribˡ-∧ ω p q =
    ≤-trans (∧-decreasingˡ (ω · p) (ω · q)) (·-monotoneˡ (ω≤ 𝟙))

  -- Addition is sub-interchangable with ⊛
  -- (p ⊛ᵣ q) + (p′ ⊛ᵣ q′) ≤ (p + p′) ⊛ᵣ (q + q′)

  +-sub-interchangable-⊛ : (r : 𝟘𝟙ω) → _+_ SubInterchangable (_⊛_▷ r) by _≤_
  +-sub-interchangable-⊛ 𝟘 p q p′ q′ = +-sub-interchangeable-∧ p q p′ q′
  +-sub-interchangable-⊛ 𝟙 p q p′ q′ = begin
    p + ω · q + (p′ + ω · q′)
      ≈⟨ +-assoc p (ω · q) (p′ + ω · q′) ⟩
    p + (ω · q + (p′ + ω · q′))
      ≈˘⟨ cong (p +_) (+-assoc (ω · q) p′ (ω · q′)) ⟩
    p + (ω · q + p′ + ω · q′)
      ≈⟨ cong (λ x → p + (x + ω · q′)) (+-comm (ω · q) p′) ⟩
    p + (p′ + ω · q + ω · q′)
      ≈⟨ cong (p +_) (+-assoc p′ (ω · q) (ω · q′)) ⟩
    p + (p′ + (ω · q + ω · q′))
      ≈˘⟨ +-assoc p p′ (ω · q + ω · q′) ⟩
    p + p′ + (ω · q + ω · q′)
      ≈˘⟨ cong (p + p′ +_) (·-distribˡ-+ ω q q′) ⟩
    p + p′ + ω · (q + q′) ∎
    where open import Tools.Reasoning.PartialOrder ≤-poset
  +-sub-interchangable-⊛ ω p q p′ q′ = begin
    ω · (p ∧ q) + ω · (p′ ∧ q′)
      ≈˘⟨ ·-distribˡ-+ ω (p ∧ q) (p′ ∧ q′) ⟩
    ω · ((p ∧ q) + (p′ ∧ q′))
      ≤⟨ ·-monotoneʳ (+-sub-interchangeable-∧ p q p′ q′) ⟩
    ω · ((p + p′) ∧ (q + q′)) ∎
    where open import Tools.Reasoning.PartialOrder ≤-poset

  ·-distribʳ-⊛ : (r : 𝟘𝟙ω) →  _·_ DistributesOverʳ (_⊛_▷ r)
  ·-distribʳ-⊛ 𝟘 q p p′ = ·-distribʳ-∧ q p p′
  ·-distribʳ-⊛ 𝟙 q p p′ rewrite ·-distribʳ-+ q p (ω · p′) =
    cong (p · q +_) (·-assoc ω p′ q)
  ·-distribʳ-⊛ ω q p p′ rewrite ·-assoc ω (p ∧ p′) q =
    cong (ω ·_) (·-distribʳ-∧ q p p′)

  -- ⊛ left distributes over meet
  -- p ⊛ᵣ (q ∧ q′) ≡ (p ⊛ᵣ q) ∧ (p ⊛ᵣ q′)

  ⊛-distribˡ-∧ : (r : 𝟘𝟙ω) → (_⊛_▷ r) DistributesOverˡ _∧_
  ⊛-distribˡ-∧ 𝟘 p q q′ = begin
    p ∧ (q ∧ q′)
      ≈˘⟨ cong (_∧ (q ∧ q′)) (∧-idem p) ⟩
    (p ∧ p) ∧ (q ∧ q′)
      ≈⟨ ∧-assoc p p (q ∧ q′) ⟩
    p ∧ (p ∧ (q ∧ q′))
      ≈˘⟨ cong (p ∧_) (∧-assoc p q q′) ⟩
    p ∧ ((p ∧ q) ∧ q′)
      ≈⟨ cong (λ x → p ∧ (x ∧ q′)) (∧-comm p q) ⟩
    p ∧ ((q ∧ p) ∧ q′)
      ≈⟨ cong (p ∧_) (∧-assoc q p q′) ⟩
    p ∧ (q ∧ (p ∧ q′))
      ≈˘⟨ ∧-assoc p q (p ∧ q′) ⟩
    (p ∧ q) ∧ (p ∧ q′) ∎
    where open import Tools.Reasoning.Equivalence (PE.setoid 𝟘𝟙ω)
  ⊛-distribˡ-∧ 𝟙 p q q′ rewrite ·-distribˡ-∧ ω q q′ =
    +-distribˡ-∧ p (ω · q) (ω · q′)
  ⊛-distribˡ-∧ ω p q q′ rewrite ⊛-distribˡ-∧ 𝟘 p q q′ =
    ·-distribˡ-∧ ω (p ∧ q) (p ∧ q′)

  -- ⊛ right distributes over meet
  -- (p ∧ p′) ⊛ᵣ q ≡ (p ⊛ᵣ q) ∧ (p′ ⊛ᵣ q)

  ⊛-distribʳ-∧ : (r : 𝟘𝟙ω) → (_⊛_▷ r) DistributesOverʳ _∧_
  ⊛-distribʳ-∧ 𝟘 q p p′ = begin
    (p ∧ p′) ∧ q
      ≈⟨ ∧-comm (p ∧ p′) q ⟩
    q ∧ (p ∧ p′)
      ≈⟨ ⊛-distribˡ-∧ 𝟘 q p p′ ⟩
    (q ∧ p) ∧ (q ∧ p′)
      ≈⟨ cong₂ _∧_ (∧-comm q p) (∧-comm q p′) ⟩
    (p ∧ q) ∧ (p′ ∧ q) ∎
    where open import Tools.Reasoning.Equivalence (PE.setoid 𝟘𝟙ω)
  ⊛-distribʳ-∧ 𝟙 q p p′ = +-distribʳ-∧ (ω · q) p p′
  ⊛-distribʳ-∧ ω q p p′ rewrite ⊛-distribʳ-∧ 𝟘 q p p′ =
    ·-distribˡ-∧ ω (p ∧ q) (p′ ∧ q)

  -- If p ⊛ q ▷ r is equal to 𝟘, then p and q are equal to 𝟘.

  ⊛≈𝟘 : ∀ p q r → p ⊛ q ▷ r ≡ 𝟘 → p ≡ 𝟘 × q ≡ 𝟘
  ⊛≈𝟘 = λ where
    p q 𝟘 p∧q≡𝟘  → ∧≈𝟘ˡ p∧q≡𝟘 , ∧≈𝟘ʳ p∧q≡𝟘
    p q 𝟙 p+ωq≡𝟘 →
        positiveˡ p+ωq≡𝟘
      , (case zero-product {p = ω} {q = q} (positiveʳ p+ωq≡𝟘) of λ where
           (inj₂ q≡𝟘) → q≡𝟘)
    p q ω ω[p∧q]≡𝟘 → case zero-product ω[p∧q]≡𝟘 of λ where
      (inj₁ ())
      (inj₂ p∧q≡𝟘) → ∧≈𝟘ˡ p∧q≡𝟘 , ∧≈𝟘ʳ p∧q≡𝟘

  -- 𝟘𝟙ω forms a modality

  𝟘𝟙ωModality : Modality
  𝟘𝟙ωModality = record
    { modalityWithout⊛ = 𝟘𝟙ωMod
    ; _⊛_▷_ = _⊛_▷_
    ; ⊛-ineq = ⊛-ineq₁ , ⊛-ineq₂
    ; ⊛-cong = cong₃ _⊛_▷_
    ; +-sub-interchangable-⊛ = +-sub-interchangable-⊛
    ; ·-sub-distribʳ-⊛ = λ r q p p′ → ≤-reflexive (·-distribʳ-⊛ r q p p′)
    ; ⊛-sub-distrib-∧ = λ r → (λ p q q′ → ≤-reflexive (⊛-distribˡ-∧ r p q q′))
                            , (λ q p p′ → ≤-reflexive (⊛-distribʳ-∧ r q p p′))
    ; ⊛≤𝟘ˡ = λ {r = r} eq → ≤-reflexive (⊛≈𝟘 _ _ r eq .proj₁)
    ; ⊛≤𝟘ʳ = λ {r = r} eq → ≤-reflexive (⊛≈𝟘 _ _ r eq .proj₂)
    }
