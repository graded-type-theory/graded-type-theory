------------------------------------------------------------------------
-- The trivial (unit) modality
------------------------------------------------------------------------

open import Tools.Bool
open import Tools.Unit

module Graded.Modality.Instances.Unit where

open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum

open import Tools.Algebra ⊤

open import Graded.Modality ⊤ public
open import Graded.FullReduction.Assumptions

open import Definition.Typed.Restrictions ⊤

private variable
  rs : Type-restrictions

-- Trivial addition (and multiplication and meet) operation

_+_ : Op₂ ⊤
_ + _ = tt

infixr 20 _+_

_⊛_▷_ : Op₃ ⊤
_ ⊛ _ ▷ _ = tt

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

+-Semilattice : IsSemilattice _+_
+-Semilattice = record
  { isBand = +-Band
  ; comm   = +-Commutative
  }

+-+-SemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _+_ _+_ tt tt
+-+-SemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = +-CommutativeMonoid
  ; *-isMonoid = +-Monoid
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
  ; +-·-Semiring = +-+-Semiring
  ; ∧-Semilattice = +-Semilattice
  ; ·-distrib-∧ = +-Distributiveˡ , +-Distributiveʳ
  ; +-distrib-∧ = +-Distributiveˡ , +-Distributiveʳ
  }

-- The trivial semiring with and star

unit-semiring-with-meet-and-star : Semiring-with-meet-and-star
unit-semiring-with-meet-and-star = record
  { semiring-with-meet = unit-semiring-with-meet
  ; _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = (λ p q r → refl) , (λ p q r → refl)
  ; +-sub-interchangeable-⊛ = λ r p q p′ q′ → refl
  ; ·-sub-distribʳ-⊛ = λ r q p p′ → refl
  ; ⊛-sub-distrib-∧ = λ r → (λ p q q′ → refl) , (λ q p p′ → refl)
  }

-- The trivial modality

UnitModality : Modality
UnitModality = record
  { semiring-with-meet-and-star = unit-semiring-with-meet-and-star
  ; mode-restrictions = record
    { 𝟘ᵐ-allowed = false
    }
  ; 𝟘-well-behaved = λ ()
  }

-- The full reduction assumptions hold for UnitModality and any type
-- restrictions.

full-reduction-assumptions :
  Full-reduction-assumptions UnitModality rs
full-reduction-assumptions = record
  { 𝟙≤𝟘    = λ _ → refl
  ; ≡𝟙⊎𝟙≤𝟘 = λ _ → inj₁ refl
  }