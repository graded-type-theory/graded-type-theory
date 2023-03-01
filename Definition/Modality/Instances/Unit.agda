{-# OPTIONS --without-K --safe #-}

module Definition.Modality.Instances.Unit where

open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Unit

Unit′ : Setoid _ _
Unit′ = record { Carrier = ⊤ ; _≈_ = _≡_ ; isEquivalence = isEquivalence }

open import Tools.Algebra Unit′

open import Definition.Modality Unit′ public

-----------------------------------------------
-- A trivial modality formed by the unit set --
-----------------------------------------------

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

-- ⊤ form a modality with + as addition, multiplication and meet

UnitModalityWithout⊛ : ModalityWithout⊛
UnitModalityWithout⊛ = record
  { _+_ = _+_
  ; _·_ = _+_
  ; _∧_ = _+_
  ; 𝟘 = tt
  ; 𝟙 = tt
  ; +-·-Semiring = +-+-Semiring
  ; ∧-Semilattice = +-Semilattice
  ; ·-distrib-∧ = +-Distributiveˡ , +-Distributiveʳ
  ; +-distrib-∧ = +-Distributiveˡ , +-Distributiveʳ
  ; Prodrec = λ _ → ⊤
  }

UnitModality : Modality
UnitModality = record
  { modalityWithout⊛ = UnitModalityWithout⊛
  ; _⊛_▷_ = _⊛_▷_
  ; ⊛-ineq = (λ p q r → refl) , (λ p q r → refl)
  ; ⊛-cong = cong₃ _⊛_▷_
  ; +-sub-interchangable-⊛ = λ r p q p′ q′ → refl
  ; ·-sub-distribʳ-⊛ = λ r q p p′ → refl
  ; ⊛-sub-distrib-∧ = λ r → (λ p q q′ → refl) , (λ q p p′ → refl)
  }
