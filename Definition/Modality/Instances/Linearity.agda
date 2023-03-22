open import Definition.Modality.Instances.ZeroOneOmega
open import Definition.Modality.Restrictions

module Definition.Modality.Instances.Linearity
  (restrictions : Restrictions 𝟘𝟙ω)
  where

open import Tools.Product
open import Tools.PropositionalEquality

open import Definition.Modality.Instances.ZeroOneOmega
  renaming (𝟘𝟙ω to Linearity) public
open import Definition.Modality Linearity
open import Tools.Algebra Linearity


infixl 40 _∧_

_∧_ : Op₂ Linearity
𝟘 ∧ 𝟘 = 𝟘
𝟘 ∧ 𝟙 = ω
𝟘 ∧ ω = ω
𝟙 ∧ 𝟘 = ω
𝟙 ∧ 𝟙 = 𝟙
𝟙 ∧ ω = ω
ω ∧ q = ω

------------------------
-- Properties of meet --
------------------------

-- Meet is commutative
-- p ∧ q ≡ q ∧ p

∧-Commutative : Commutative _∧_
∧-Commutative 𝟘 𝟘 = refl
∧-Commutative 𝟘 𝟙 = refl
∧-Commutative 𝟘 ω = refl
∧-Commutative 𝟙 𝟘 = refl
∧-Commutative 𝟙 𝟙 = refl
∧-Commutative 𝟙 ω = refl
∧-Commutative ω 𝟘 = refl
∧-Commutative ω 𝟙 = refl
∧-Commutative ω ω = refl

-- Meet is associative
-- p ∧ (q ∧ r) ≡ (p ∧ q) ∧ r

∧-Associative : Associative _∧_
∧-Associative 𝟘 𝟘 𝟘 = refl
∧-Associative 𝟘 𝟘 𝟙 = refl
∧-Associative 𝟘 𝟘 ω = refl
∧-Associative 𝟘 𝟙 𝟘 = refl
∧-Associative 𝟘 𝟙 𝟙 = refl
∧-Associative 𝟘 𝟙 ω = refl
∧-Associative 𝟘 ω r = refl
∧-Associative 𝟙 𝟘 𝟘 = refl
∧-Associative 𝟙 𝟘 𝟙 = refl
∧-Associative 𝟙 𝟘 ω = refl
∧-Associative 𝟙 𝟙 𝟘 = refl
∧-Associative 𝟙 𝟙 𝟙 = refl
∧-Associative 𝟙 𝟙 ω = refl
∧-Associative 𝟙 ω r = refl
∧-Associative ω q r = refl

-- Addition is idempotent

∧-Idempotent : Idempotent _∧_
∧-Idempotent 𝟘 = refl
∧-Idempotent 𝟙 = refl
∧-Idempotent ω = refl

-------------------------------------------------------------------
-- Distributive properties of addition, multiplication over meet --
-------------------------------------------------------------------

-- Multiplication is left distributive over meet
-- p · (q ∧ r) ≡ (p · q) ∧ (p · r)

·-distribˡ-∧ : _·_ DistributesOverˡ _∧_
·-distribˡ-∧ 𝟘 q r = refl
·-distribˡ-∧ 𝟙 q r = refl
·-distribˡ-∧ ω 𝟘 𝟘 = refl
·-distribˡ-∧ ω 𝟘 𝟙 = refl
·-distribˡ-∧ ω 𝟘 ω = refl
·-distribˡ-∧ ω 𝟙 𝟘 = refl
·-distribˡ-∧ ω 𝟙 𝟙 = refl
·-distribˡ-∧ ω 𝟙 ω = refl
·-distribˡ-∧ ω ω r = refl

-- Multiplication is right distributive over meet
-- (q ∧ r) · p ≡ (q · p) ∧ (r · p)

·-distribʳ-∧ : _·_ DistributesOverʳ _∧_
·-distribʳ-∧ p q r = begin
  (q ∧ r) · p
    ≈⟨ ·-Commutative (q ∧ r) p ⟩
  p · (q ∧ r)
    ≈⟨ ·-distribˡ-∧ p q r ⟩
  (p · q) ∧ (p · r)
    ≈⟨ cong₂ _∧_ (·-Commutative p q) (·-Commutative p r) ⟩
  (q · p) ∧ (r · p) ∎
  where open import Tools.Reasoning.Equivalence (setoid Linearity)

-- Multiplication is distributive over addition
-- p · (q ∧ r) ≡ (p · q) ∧ (p · r) and (q ∧ r) · p ≡ (q · p) ∧ (r · p)

·-distrib-∧ : _·_ DistributesOver _∧_
·-distrib-∧ = ·-distribˡ-∧ , ·-distribʳ-∧

-- Addition is left distributive over meet
-- p + (q ∧ r) ≡ (p + q) ∧ (p + r)

+-distribˡ-∧ : _+_ DistributesOverˡ _∧_
+-distribˡ-∧ 𝟘 q r = refl
+-distribˡ-∧ 𝟙 𝟘 𝟘 = refl
+-distribˡ-∧ 𝟙 𝟘 𝟙 = refl
+-distribˡ-∧ 𝟙 𝟘 ω = refl
+-distribˡ-∧ 𝟙 𝟙 𝟘 = refl
+-distribˡ-∧ 𝟙 𝟙 𝟙 = refl
+-distribˡ-∧ 𝟙 𝟙 ω = refl
+-distribˡ-∧ 𝟙 ω r = refl
+-distribˡ-∧ ω q r = refl

-- Addition is right distributive over meet
-- (q ∧ r) + p ≡ (q + p) ∧ (r + p)

+-distribʳ-∧ : _+_ DistributesOverʳ _∧_
+-distribʳ-∧ p q r = begin
  (q ∧ r) + p
    ≈⟨ +-Commutative (q ∧ r) p ⟩
  p + (q ∧ r)
    ≈⟨ +-distribˡ-∧ p q r ⟩
  (p + q) ∧ (p + r)
    ≈⟨ cong₂ _∧_ (+-Commutative p q) (+-Commutative p r) ⟩
  (q + p) ∧ (r + p) ∎
  where open import Tools.Reasoning.Equivalence (setoid Linearity)

-- Addition is distributive over meet
-- p + (q ∧ r) ≡ (p + q) ∧ (p + r) and (q ∧ r) + p ≡ (q + p) ∧ (r + p)

+-distrib-∧ : _+_ DistributesOver _∧_
+-distrib-∧ = +-distribˡ-∧ , +-distribʳ-∧

---------------------------------------
-- Meet forms the following algebras --
---------------------------------------

-- Meet forms a magma

∧-Magma : IsMagma _∧_
∧-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _∧_
  }

-- Meet forms a semigroup

∧-Semigroup : IsSemigroup _∧_
∧-Semigroup = record
  { isMagma = ∧-Magma
  ; assoc   = ∧-Associative
  }

-- Meet forms a band

∧-Band : IsBand _∧_
∧-Band = record
  { isSemigroup = ∧-Semigroup
  ; idem        = ∧-Idempotent
  }

-- Meet forms a semilattice

∧-Semilattice : IsSemilattice _∧_
∧-Semilattice = record
  { isBand = ∧-Band
  ; comm   = ∧-Commutative
  }

-- Linearity forms a modality

linearityModality : Modality
linearityModality =
  ⊛.𝟘𝟙ωModality _∧_ ∧-Semilattice ·-distrib-∧ +-distrib-∧ (λ _ → refl)
    (λ ()) restrictions
