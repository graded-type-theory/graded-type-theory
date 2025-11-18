------------------------------------------------------------------------
-- Modalities for downward closed sets of natural numbers with
-- decidable membership relations (defined under the assumption of
-- function extensionality)
------------------------------------------------------------------------

module
  Graded.Modality.Instances.Bounded-distributive-lattice.Downward-closed
  where

import Tools.Algebra
open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_)

import Graded.Modality
import Graded.Modality.Instances.Bounded-distributive-lattice as
  Bounded-distributive-lattice
open import Graded.Modality.Variant lzero

private variable
  m n : Nat
  p   : Nat → Bool

------------------------------------------------------------------------
-- Basic types

-- The property of being downward closed (for functions of type
-- Nat → Bool).

Downward-closed : (Nat → Bool) → Set
Downward-closed p = ∀ m n → m ≤ n → T (p n) → T (p m)

-- Downward closed sets of natural numbers with decidable membership
-- relations.
--
-- For an alternative implementation, see
-- Graded.Modality.Instances.Bounded-distributive-lattice.Nat-plus-infinity.

Set-ℕ : Set
Set-ℕ = ∃ λ (p : Nat → Bool) → Downward-closed p

-- The membership relation.

infix 10 _∈_

_∈_ : Nat → Set-ℕ → Set
n ∈ xs = T (xs .proj₁ n)

private
  module BDL = Bounded-distributive-lattice Set-ℕ

open Graded.Modality Set-ℕ
open Tools.Algebra   Set-ℕ

private variable
  xs ys : Set-ℕ

------------------------------------------------------------------------
-- Operations

-- The membership relation is decidable.

infix 10 _∈?_

_∈?_ : ∀ n xs → Dec (n ∈ xs)
n ∈? xs with xs .proj₁ n
… | true  = yes _
… | false = no (λ ())

-- The empty set.

∅ : Set-ℕ
∅ = (λ _ → false) , λ _ _ _ ()

-- The set containing all natural numbers.

ℕ : Set-ℕ
ℕ = (λ _ → true) , _

-- Union.

infixr 35 _∪_

_∪_ : Op₂ Set-ℕ
xs ∪ ys =
    (λ n → xs .proj₁ n ∨ ys .proj₁ n)
  , (λ m n m≤n →
       T (xs .proj₁ n ∨ ys .proj₁ n)      →⟨ T-∨ .proj₁ ⟩
       T (xs .proj₁ n) ⊎ T (ys .proj₁ n)  →⟨ ⊎.map (xs .proj₂ _ _ m≤n) (ys .proj₂ _ _ m≤n) ⟩
       T (xs .proj₁ m) ⊎ T (ys .proj₁ m)  →⟨ T-∨ .proj₂ ⟩
       T (xs .proj₁ m ∨ ys .proj₁ m)      □)

-- Intersection.

infixr 43 _∩_

_∩_ : Op₂ Set-ℕ
xs ∩ ys =
    (λ n → xs .proj₁ n ∧ ys .proj₁ n)
  , (λ m n m≤n →
       T (xs .proj₁ n ∧ ys .proj₁ n)      →⟨ T-∧ .proj₁ ⟩
       T (xs .proj₁ n) × T (ys .proj₁ n)  →⟨ Σ.map (xs .proj₂ _ _ m≤n) (ys .proj₂ _ _ m≤n) ⟩
       T (xs .proj₁ m) × T (ys .proj₁ m)  →⟨ T-∧ .proj₂ ⟩
       T (xs .proj₁ m ∧ ys .proj₁ m)      □)

------------------------------------------------------------------------
-- Some properties

-- The sets are downward closed.

downward-closed : ∀ xs → m ≤ n → n ∈ xs → m ∈ xs
downward-closed xs = xs .proj₂ _ _

-- The empty set is empty.

∉∅ : ∀ n → ¬ n ∈ ∅
∉∅ _ ()

-- ℕ contains every natural number.

∈ℕ : ∀ n → n ∈ ℕ
∈ℕ = _

-- The union of xs and ys contains exactly those numbers that are
-- members of xs or ys.

∈∪⇔ : ∀ xs ys → n ∈ xs ∪ ys ⇔ (n ∈ xs ⊎ n ∈ ys)
∈∪⇔ _ _ = T-∨

-- The intersection of xs and ys contains exactly those numbers that
-- are members of both xs and ys.

∈∩⇔ : ∀ xs ys → n ∈ xs ∩ ys ⇔ (n ∈ xs × n ∈ ys)
∈∩⇔ _ _ = T-∧

-- The following lemmas are proved under the assumption that function
-- extensionality holds.

module _ (fe : Function-extensionality lzero lzero) where

  -- The type Downward-closed p is propositional.

  Downward-closed-propositional :
    {p₁ p₂ : Downward-closed p} → p₁ ≡ p₂
  Downward-closed-propositional =
    ext fe λ _ → ext fe λ _ → ext fe λ _ → ext fe λ _ →
    T-propositional

  -- Two sets are equal if their first components are equal.

  predicates-equal→sets-equal : xs .proj₁ ≡ ys .proj₁ → xs ≡ ys
  predicates-equal→sets-equal {xs = p , _} refl =
    cong (p ,_) Downward-closed-propositional

  -- A "bounded distributive lattice" for Set-ℕ.

  bounded-distributive-lattice : Bounded-distributive-lattice
  bounded-distributive-lattice = record
    { _∧_                     = _∪_
    ; _∨_                     = _∩_
    ; ⊥                       = ℕ
    ; ⊤                       = ∅
    ; is-distributive-lattice = record
      { isLattice = record
        { isEquivalence = PE.isEquivalence
        ; ∨-comm        = λ xs ys →
                            predicates-equal→sets-equal $ ext fe λ n →
                            ∧-comm (xs .proj₁ n) (ys .proj₁ n)
        ; ∨-assoc       = λ xs ys zs →
                            predicates-equal→sets-equal $ ext fe λ n →
                            ∧-assoc (xs .proj₁ n) (ys .proj₁ n)
                              (zs .proj₁ n)
        ; ∨-cong        = cong₂ _∩_
        ; ∧-comm        = λ xs ys →
                            predicates-equal→sets-equal $ ext fe λ n →
                            ∨-comm (xs .proj₁ n) (ys .proj₁ n)
        ; ∧-assoc       = λ xs ys zs →
                            predicates-equal→sets-equal $ ext fe λ n →
                            ∨-assoc (xs .proj₁ n) (ys .proj₁ n)
                              (zs .proj₁ n)
        ; ∧-cong        = cong₂ _∪_
        ; absorptive    = (λ xs ys →
                            predicates-equal→sets-equal $ ext fe λ n →
                             ∨-∧-absorptive .proj₂
                               (xs .proj₁ n) (ys .proj₁ n))
                        , (λ xs ys →
                            predicates-equal→sets-equal $ ext fe λ n →
                             ∨-∧-absorptive .proj₁
                               (xs .proj₁ n) (ys .proj₁ n))
        }
      ; ∨-distrib-∧ = (λ xs ys zs →
                         predicates-equal→sets-equal $ ext fe λ n →
                         ∧-distribˡ-∨ (xs .proj₁ n) (ys .proj₁ n)
                           (zs .proj₁ n))
                    , (λ xs ys zs →
                         predicates-equal→sets-equal $ ext fe λ n →
                         ∧-distribʳ-∨ (xs .proj₁ n) (ys .proj₁ n)
                           (zs .proj₁ n))
      ; ∧-distrib-∨ = (λ xs ys zs →
                        predicates-equal→sets-equal $ ext fe (λ n →
                        ∨-distribˡ-∧ (xs .proj₁ n) (ys .proj₁ n)
                          (zs .proj₁ n)))
                    , (λ xs ys zs →
                        predicates-equal→sets-equal $ ext fe (λ n →
                        ∨-distribʳ-∧ (xs .proj₁ n) (ys .proj₁ n)
                          (zs .proj₁ n)))
      }
    ; ⊥≤ = λ _ →
             predicates-equal→sets-equal $ ext fe λ _ →
             refl
    ; ≤⊤ = λ xs →
             predicates-equal→sets-equal $ ext fe λ n →
             sym (∨-identityʳ (xs .proj₁ n))
    }

  -- A set is equal to ∅ if and only if 0 is not a member of the set.

  ≡∅⇔0∉ : xs ≡ ∅ ⇔ xs .proj₁ 0 ≡ false
  ≡∅⇔0∉ {xs = xs@(p , closed)} =
      (λ { refl → refl })
    , (λ eq →
         predicates-equal→sets-equal $ ext fe λ n →
         ¬-T .proj₁ $ ¬-T .proj₂ eq ∘→ closed 0 n z≤n)

  -- A "semiring with meet" for Set-ℕ.

  semiring-with-meet : Semiring-with-meet
  semiring-with-meet =
    BDL.semiring-with-meet bounded-distributive-lattice is-𝟘?
    where
    is-𝟘? : (xs : Set-ℕ) → Dec (xs ≡ ∅)
    is-𝟘? xs@(p , _) = lemma _ refl
      where
      lemma : (b : Bool) → b ≡ p 0 → Dec (xs ≡ ∅)
      lemma false eq = yes (≡∅⇔0∉ .proj₂ (sym eq))
      lemma true  eq = no
        (xs ≡ ∅        →⟨ ≡∅⇔0∉ .proj₁ ⟩
         p 0 ≡ false   →⟨ trans eq ⟩
         true ≡ false  →⟨ (λ ()) ⟩
         ⊥             □)

  -- The function _∪ ys is decreasing.

  ∪-decreasingˡ :
    (xs : Set-ℕ) →
    Semiring-with-meet._≤_ semiring-with-meet (xs ∪ ys) xs
  ∪-decreasingˡ {ys = ys} xs =
    xs ∪ ys         ≡˘⟨ cong (_∪ _) (R.∧-idem xs) ⟩
    (xs ∪ xs) ∪ ys  ≡⟨ R.+-assoc xs _ _ ⟩
    xs ∪ (xs ∪ ys)  ≡⟨ R.+-comm xs _ ⟩
    (xs ∪ ys) ∪ xs  ∎
    where
    module R = Semiring-with-meet semiring-with-meet

  -- The "semiring with meet" has a well-behaved zero.

  has-well-behaved-zero : Has-well-behaved-zero semiring-with-meet
  has-well-behaved-zero = record
    { non-trivial =
      ℕ ≡ ∅         →⟨ cong (λ xs → xs .proj₁ 0) ⟩
      true ≡ false  →⟨ (λ ()) ⟩
      ⊥             □
    ; zero-product = λ {p = xs} {q = ys} →
        xs ∩ ys ≡ ∅                                →⟨ cong (λ f → f .proj₁ 0) ⟩
        xs .proj₁ 0 ∧ ys .proj₁ 0 ≡ false          →⟨ ∧-zero-product ⟩
        xs .proj₁ 0 ≡ false ⊎ ys .proj₁ 0 ≡ false  →⟨ ⊎.map (≡∅⇔0∉ .proj₂) (≡∅⇔0∉ .proj₂) ⟩
        xs ≡ ∅ ⊎ ys ≡ ∅                            □
    ; +-positiveˡ = ∪-positiveˡ _ _
    ; ∧-positiveˡ = ∪-positiveˡ _ _
    }
    where
    ∪-positiveˡ : ∀ xs ys → xs ∪ ys ≡ ∅ → xs ≡ ∅
    ∪-positiveˡ xs ys =
      xs ∪ ys ≡ ∅                        →⟨ cong (λ f → f .proj₁ 0) ⟩
      xs .proj₁ 0 ∨ ys .proj₁ 0 ≡ false  →⟨ ∨-positiveˡ ⟩
      xs .proj₁ 0 ≡ false                →⟨ ≡∅⇔0∉ .proj₂ ⟩
      xs ≡ ∅                             □

  -- Modalities for Set-ℕ.

  modality : Modality-variant → Modality
  modality variant = BDL.modality
    bounded-distributive-lattice
    (Semiring-with-meet.is-𝟘? semiring-with-meet)
    variant
    (λ _ → has-well-behaved-zero)
