------------------------------------------------------------------------
-- Modalities for downward closed sets of natural numbers with
-- decidable membership relations and decidable equality
------------------------------------------------------------------------

module
  Graded.Modality.Instances.Bounded-distributive-lattice.Nat-plus-infinity
  where

open import Graded.Modality.Instances.Nat-plus-infinity as ℕ⊎∞
  using (ℕ⊎∞; ∞; ⌞_⌟; _≤_)

open import Tools.Algebra ℕ⊎∞
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

open import Graded.Modality ℕ⊎∞
import Graded.Modality.Instances.Bounded-distributive-lattice as
  Bounded-distributive-lattice
open import Graded.Modality.Variant lzero

private
  open module BDL = Bounded-distributive-lattice ℕ⊎∞
    using (Bounded-distributive-lattice)
  module R = Semiring-with-meet ℕ⊎∞.ℕ⊎∞-semiring-with-meet

private variable
  xs ys : ℕ⊎∞
  m n   : Nat

------------------------------------------------------------------------
-- Basic types

-- Downward closed sets of natural numbers with decidable membership
-- relations and decidable equality.
--
-- For an alternative implementation (without decidable equality), see
-- Graded.Modality.Instances.Bounded-distributive-lattice.Downward-closed.

Set-ℕ : Set
Set-ℕ = ℕ⊎∞

-- The membership relation.

infix 10 _∈_

_∈_ : Nat → Set-ℕ → Set
_ ∈ ∞     = ⊤
m ∈ ⌞ n ⌟ = m N.< n

------------------------------------------------------------------------
-- Operations

-- The membership relation is decidable.

infix 10 _∈?_

_∈?_ : ∀ n xs → Dec (n ∈ xs)
_ ∈? ∞     = yes _
m ∈? ⌞ n ⌟ = m N.<? n

-- Equality is decidable.

infix 10 _≟_

_≟_ : (xs ys : Set-ℕ) → Dec (xs ≡ ys)
_≟_ = ℕ⊎∞._≟_

-- The empty set.

∅ : Set-ℕ
∅ = ⌞ 0 ⌟

-- The set containing all natural numbers.

ℕ : Set-ℕ
ℕ = ∞

-- Union.

infixr 35 _∪_

_∪_ : Set-ℕ → Set-ℕ → Set-ℕ
_∪_ = ℕ⊎∞._∧_

-- Intersection.

infixr 40 _∩_

_∩_ : Set-ℕ → Set-ℕ → Set-ℕ
∞     ∩ n     = n
m     ∩ ∞     = m
⌞ m ⌟ ∩ ⌞ n ⌟ = ⌞ m N.⊓ n ⌟

------------------------------------------------------------------------
-- Some properties

-- The sets are downward closed.

downward-closed : m N.≤ n → n ∈ xs → m ∈ xs
downward-closed                 {xs = ∞}     = _
downward-closed {m = m} {n = n} {xs = ⌞ o ⌟} = λ m≤n n<o → begin
  1+ m  ≤⟨ N.s≤s m≤n ⟩
  1+ n  ≤⟨ n<o ⟩
  o     ∎
  where
  open N.≤-Reasoning

-- The empty set is empty.

∉∅ : ¬ n ∈ ∅
∉∅ ()

-- ℕ contains every natural number.

∈ℕ : ∀ n → n ∈ ℕ
∈ℕ = _

-- The union of xs and ys contains exactly those numbers that are
-- members of xs or ys.

∈∪⇔ : n ∈ xs ∪ ys ⇔ (n ∈ xs ⊎ n ∈ ys)
∈∪⇔ {xs = ∞} =
  inj₁ , _
∈∪⇔ {xs = ⌞ _ ⌟} {ys = ∞} =
  inj₂ , _
∈∪⇔ {n = n} {xs = ⌞ m ⌟} {ys = ⌞ o ⌟} =
  n N.< m N.⊔ o      ⇔⟨ N.≤⊔⇔≤⊎≤ ⟩
  n N.< m ⊎ n N.< o  □⇔

-- The intersection of xs and ys contains exactly those numbers that
-- are members of both xs and ys.

∈∩⇔ : n ∈ xs ∩ ys ⇔ (n ∈ xs × n ∈ ys)
∈∩⇔ {xs = ∞} =
  (_ ,_) , proj₂
∈∩⇔ {xs = ⌞ _ ⌟} {ys = ∞} =
  (_, _) , proj₁
∈∩⇔ {n = n} {xs = ⌞ m ⌟} {ys = ⌞ o ⌟} =
  n N.< m N.⊓ o      ⇔⟨ (λ hyp → N.m<n⊓o⇒m<n _ _ hyp , N.m<n⊓o⇒m<o _ _ hyp)
                      , uncurry N.⊓-pres-m<
                      ⟩
  n N.< m × n N.< o  □⇔

-- The function _∪ ys is decreasing.

∪-decreasingˡ : xs ∪ ys ≤ xs
∪-decreasingˡ {xs = xs} {ys = ys} =
  xs ∪ ys         ≡˘⟨ cong (_∪ _) (R.∧-idem xs) ⟩
  (xs ∪ xs) ∪ ys  ≡⟨ R.∧-assoc xs _ _ ⟩
  xs ∪ (xs ∪ ys)  ≡⟨ R.∧-comm xs _ ⟩
  (xs ∪ ys) ∪ xs  ∎
  where
  open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- A modality

-- A bounded distributive lattice for Set-ℕ.

bounded-distributive-lattice : Bounded-distributive-lattice
bounded-distributive-lattice = record
  { _∧_                     = _∪_
  ; _∨_                     = _∩_
  ; ⊥                       = ℕ
  ; ⊤                       = ∅
  ; ⊥≤                      = ℕ⊎∞.∞≤
  ; ≤⊤                      = λ _ → ℕ⊎∞.≤0
  ; is-distributive-lattice = record
      { isLattice    = record
        { isEquivalence = PE.isEquivalence
        ; ∨-comm        = ∩-comm
        ; ∨-assoc       = ∩-assoc
        ; ∨-cong        = cong₂ _∩_
        ; ∧-comm        = R.∧-comm
        ; ∧-assoc       = R.∧-assoc
        ; ∧-cong        = cong₂ _∪_
        ; absorptive    = absorptive
        }
      ; ∨-distrib-∧ =
            comm∧distrʳ⇒distrˡ ∩-comm ∩-distribʳ-∪
          , ∩-distribʳ-∪
      ; ∧-distrib-∨ =
            comm∧distrʳ⇒distrˡ R.∧-comm ∪-distribʳ-∩
          , ∪-distribʳ-∩
      }
  }
  where
  open Tools.Reasoning.PropositionalEquality

  ∩-comm : Commutative _∩_
  ∩-comm = λ where
    ⌞ 0 ⌟    ⌞ 0 ⌟    → refl
    ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
    ⌞ 0 ⌟    ⌞ 1+ _ ⌟ → refl
    ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ (N.⊓-comm _ _)
    ⌞ 0 ⌟    ∞        → refl
    ⌞ 1+ _ ⌟ ∞        → refl
    ∞        ⌞ 0 ⌟    → refl
    ∞        ⌞ 1+ _ ⌟ → refl
    ∞        ∞        → refl

  ∩-assoc : Associative _∩_
  ∩-assoc = λ where
    ⌞ _ ⌟ ⌞ _ ⌟ ⌞ _ ⌟ → cong ⌞_⌟ (N.⊓-assoc _ _ _)
    ⌞ _ ⌟ ⌞ _ ⌟ ∞     → refl
    ⌞ _ ⌟ ∞     _     → refl
    ∞     _     _     → refl

  absorptive : Absorptive _∩_ _∪_
  absorptive =
      (λ where
         ⌞ _ ⌟ ⌞ _ ⌟ → cong ⌞_⌟ (N.⊓-absorbs-⊔ _ _)
         ⌞ _ ⌟ ∞     → refl
         ∞     _     → refl)
    , (λ where
         ⌞ _ ⌟ ⌞ _ ⌟ → cong ⌞_⌟ (N.⊔-absorbs-⊓ _ _)
         ⌞ _ ⌟ ∞     → cong ⌞_⌟ (N.⊔-idem _)
         ∞     _     → refl)

  ∩-distribʳ-∪ : _∩_ DistributesOverʳ _∪_
  ∩-distribʳ-∪ = λ where
    ⌞ _ ⌟ ⌞ _ ⌟ ⌞ o ⌟ → cong ⌞_⌟ (N.⊓-distribʳ-⊔ _ _ o)
    ⌞ m ⌟ ⌞ n ⌟ ∞     → cong ⌞_⌟ (
      m                ≡˘⟨ N.⊔-absorbs-⊓ _ _ ⟩
      m N.⊔ (m N.⊓ n)  ≡⟨ N.⊔-comm m _ ⟩
      (m N.⊓ n) N.⊔ m  ≡⟨ cong (N._⊔ _) (N.⊓-comm m _) ⟩
      (n N.⊓ m) N.⊔ m  ∎)
    ⌞ m ⌟ ∞ ⌞ n ⌟ → cong ⌞_⌟ (
      m                ≡˘⟨ N.⊔-absorbs-⊓ _ _ ⟩
      m N.⊔ (m N.⊓ n)  ≡⟨ cong (_ N.⊔_) (N.⊓-comm m _) ⟩
      m N.⊔ (n N.⊓ m)  ∎)
    ⌞ _ ⌟ ∞     ∞     → cong ⌞_⌟ (sym (N.⊔-idem _))
    ∞     ⌞ _ ⌟ ⌞ _ ⌟ → refl
    ∞     ⌞ _ ⌟ ∞     → refl
    ∞     ∞     ⌞ _ ⌟ → refl
    ∞     ∞     ∞     → refl

  ∪-distribʳ-∩ : _∪_ DistributesOverʳ _∩_
  ∪-distribʳ-∩ = λ where
    ⌞ _ ⌟ ⌞ _ ⌟ ⌞ o ⌟ → cong ⌞_⌟ (N.⊔-distribʳ-⊓ _ _ o)
    ⌞ m ⌟ ⌞ n ⌟ ∞     → refl
    ⌞ m ⌟ ∞ ⌞ n ⌟     → refl
    ⌞ _ ⌟ ∞     ∞     → refl
    ∞     ⌞ _ ⌟ ⌞ _ ⌟ → refl
    ∞     ⌞ _ ⌟ ∞     → refl
    ∞     ∞     ⌞ _ ⌟ → refl
    ∞     ∞     ∞     → refl

-- A "semiring with meet" for Set-ℕ, obtained from the distributive
-- lattice.

semiring-with-meet : Semiring-with-meet
semiring-with-meet =
  BDL.semiring-with-meet bounded-distributive-lattice

-- The "semiring with meet" has a well-behaved zero.

has-well-behaved-zero : Has-well-behaved-zero semiring-with-meet
has-well-behaved-zero = record
  { non-trivial  = λ ()
  ; is-𝟘?        = Z.is-𝟘?
  ; +-positiveˡ  = Z.∧-positiveˡ
  ; ∧-positiveˡ  = Z.∧-positiveˡ
  ; zero-product = λ where
      {p = ⌞ 0 ⌟} {q = ⌞ _ ⌟} _ → inj₁ refl
      {p = ⌞ 0 ⌟} {q = ∞}     _ → inj₁ refl
      {p = ⌞ _ ⌟} {q = ⌞ 0 ⌟} _ → inj₂ refl
      {p = ∞}     {q = ⌞ 0 ⌟} _ → inj₂ refl
  }
  where
  module Z = Has-well-behaved-zero ℕ⊎∞.ℕ⊎∞-has-well-behaved-zero

-- A modality (of any kind) for Set-ℕ defined using the construction
-- in Graded.Modality.Instances.BoundedStar.

modality : Modality-variant → Modality
modality variant = BDL.modality
  variant
  bounded-distributive-lattice
  (λ _ → has-well-behaved-zero)
