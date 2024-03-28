------------------------------------------------------------------------
-- The trivial (unit) modality
------------------------------------------------------------------------

open import Tools.Bool
open import Tools.Unit

module Graded.Modality.Instances.Unit where

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

open import Tools.Algebra ⊤

open import Graded.Modality ⊤ public
import Graded.Modality.Properties.Star as Star
open import Graded.Modality.Variant lzero
open import Graded.FullReduction.Assumptions
open import Graded.Usage.Restrictions

open import Definition.Typed.Restrictions

private variable
  variant : Modality-variant

-- Trivial addition (and multiplication and meet) operation

_+_ : Op₂ ⊤
_ + _ = tt

infixr 20 _+_

_⊛_▷_ : Op₃ ⊤
_ ⊛ _ ▷ _ = tt

-- A decision procedure for equality.

infix 10 _≟_

_≟_ : Decidable (_≡_ {A = ⊤})
_ ≟ _ = yes refl

-- Properties of +

-- Addition is commutative
-- p + q ≡ q + p

+-Commutative : Commutative _+_
+-Commutative x y = refl

-- Addition is associative
-- p + (q + r) ≡ (p + q) + r

+-Associative : Associative _+_
+-Associative x y z = refl

-- Addition is left distributive of itself
-- p + (q + r) ≡ (p + q) + (p + r)

+-Distributiveˡ : _+_ DistributesOverˡ _+_
+-Distributiveˡ x y z = refl

-- Addition is right distributive over itself
-- (q + r) + p ≡ (q + p) + (r + p)

+-Distributiveʳ : _+_ DistributesOverʳ _+_
+-Distributiveʳ x y z = refl

-- tt is the left identity of addition
-- tt + p ≡ p

+-LeftIdentity : LeftIdentity tt _+_
+-LeftIdentity tt = refl

-- tt is the right identity of addition
-- p + tt ≡ p

+-RightIdentity : RightIdentity tt _+_
+-RightIdentity tt = refl

-- tt is the identity of addition
-- tt + p ≡ p ≡ p + tt

+-Identity : Identity tt _+_
+-Identity = +-LeftIdentity , +-RightIdentity

-- Addition is idempotent
-- p + p ≡ p

+-Idempotent : Idempotent _+_
+-Idempotent tt = refl

------------------------------------
-- + forms the following algebras --
------------------------------------

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

-- Addition forms a monoid with tt as identity

+-Monoid : IsMonoid _+_ tt
+-Monoid = record
  { isSemigroup = +-Semigroup
  ; identity    = +-Identity
  }

-- Addition forms a commutative monoid with tt as identity

+-CommutativeMonoid : IsCommutativeMonoid _+_ tt
+-CommutativeMonoid = record
  { isMonoid = +-Monoid
  ; comm     = +-Commutative
  }

-- Addition forms a band

+-Band : IsBand _+_
+-Band = record
  { isSemigroup = +-Semigroup
  ; idem        = +-Idempotent
  }

-- Addition forms a semilattice

+-Semilattice : IsMeetSemilattice _+_
+-Semilattice = record
  { isBand = +-Band
  ; comm   = +-Commutative
  }

+-+-SemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _+_ _+_ tt tt
+-+-SemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = +-CommutativeMonoid
  ; *-cong = cong₂ _+_
  ; *-assoc = +-Associative
  ; *-identity = +-Identity
  ; distrib = +-Distributiveˡ , +-Distributiveʳ
  }

+-+-Semiring : IsSemiring _+_ _+_ tt tt
+-+-Semiring = record
  { isSemiringWithoutAnnihilatingZero = +-+-SemiringWithoutAnnihilatingZero
  ; zero = (λ x → refl) , (λ x → refl)
  }

-- The trivial semiring with meet

unit-semiring-with-meet : Semiring-with-meet
unit-semiring-with-meet = record
  { _+_ = _+_
  ; _·_ = _+_
  ; _∧_ = _+_
  ; 𝟘 = tt
  ; 𝟙 = tt
  ; ω = tt
  ; ω≤𝟙 = refl
  ; ω·+≤ω·ʳ = refl
  ; is-𝟘? = _≟ tt
  ; +-·-Semiring = +-+-Semiring
  ; ∧-Semilattice = +-Semilattice
  ; ·-distrib-∧ = +-Distributiveˡ , +-Distributiveʳ
  ; +-distrib-∧ = +-Distributiveˡ , +-Distributiveʳ
  }

-- A natrec-star operator can be defined for the trivial "semiring
-- with meet".

unit-has-star : Has-star unit-semiring-with-meet
unit-has-star = record
  { _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = (λ p q r → refl) , (λ p q r → refl)
  ; +-sub-interchangeable-⊛ = λ r p q p′ q′ → refl
  ; ·-sub-distribʳ-⊛ = λ r q p p′ → refl
  ; ⊛-sub-distrib-∧ = λ r → (λ p q q′ → refl) , (λ q p p′ → refl)
  }

-- A trivial modality (without 𝟘ᵐ).

UnitModality :
  (variant : Modality-variant) →
  let open Modality-variant variant in
  ¬ T 𝟘ᵐ-allowed →
  Modality
UnitModality variant not-ok = record
  { variant            = variant
  ; semiring-with-meet = unit-semiring-with-meet
  ; 𝟘-well-behaved     = ⊥-elim ∘→ not-ok
  ; has-nr             = λ _ →
                           Star.has-nr _ ⦃ has-star = unit-has-star ⦄
  }

-- The full reduction assumptions hold for any instance of
-- UnitModality and any type restrictions.

full-reduction-assumptions :
  let open Modality-variant variant in
  (ok : ¬ T 𝟘ᵐ-allowed) →
  {rs : Type-restrictions (UnitModality variant ok)} →
  {us : Usage-restrictions (UnitModality variant ok)} →
  Full-reduction-assumptions rs us
full-reduction-assumptions _ = record
  { sink⊎𝟙≤𝟘 = λ _ → inj₂ refl
  ; ≡𝟙⊎𝟙≤𝟘   = λ _ → inj₁ refl
  }
