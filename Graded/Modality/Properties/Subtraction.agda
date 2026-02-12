------------------------------------------------------------------------
-- Subtraction
------------------------------------------------------------------------

import Graded.Modality

module Graded.Modality.Properties.Subtraction
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open Modality 𝕄

open import Graded.Modality.Properties.Addition 𝕄
open import Graded.Modality.Properties.Meet 𝕄
open import Graded.Modality.Properties.PartialOrder 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality

private variable
  p p′ q q′ r r′ ∞ : M

------------------------------------------------------------------------
-- The relations _-_≤_ and _-_≡_
-- a kind of subtraction

-- The relation p - q ≤ r is inhabited if "p minus q" is bounded by r.
--
-- For modalities with quantitative interpretetations, p - q ≤ r can be
-- interpreted as "If there are p copies of some resource, it is
-- possible to use q copies and have at least r copies left"

infix 4 _-_≤_

_-_≤_ : (p q r : M) → Set a
p - q ≤ r = p ≤ r + q

-- The relation p - q ≡ r is inhabited if r is the least value for
-- which p - q ≤  is inhabited.
--
-- For modalities with quantitative interpretetations, p - q ≡ r can be
-- interpreted as "If there are p copies of some resource, it is
-- possible to use q copies and have r copies left."
--
-- The reason for chosing the least value is to leave as many copies
-- available as possible to avoid needlessly running out of resources.
-- For instance, for the linearity modality we have ω - 𝟙 ≤ ω and
-- ω - 𝟙 ≤ 𝟙 but using 𝟙 copy of ω can safely leave ω copies remaining.

infix 4 _-_≡_

_-_≡_ : (p q r : M) → Set a
p - q ≡ r = Least-such-that (p - q ≤_) r

opaque

  -- The relation _-_≡_ is functional.

  -≡-functional : p - q ≡ r → p - q ≡ r′ → r ≡ r′
  -≡-functional (p-q≤r , least) (p-q≤r′ , least′) =
    ≤-antisym (least _ p-q≤r′) (least′ _ p-q≤r)

opaque

  -- Subtraction is monotone in its first argument.

  -≡≤-monotoneˡ : p ≤ p′ → p - q ≡ r → p′ - q ≤ r′ → r ≤ r′
  -≡≤-monotoneˡ p≤p′ (p≤q+r , P) p′≤q+r′ =
    P _ (≤-trans p≤p′ p′≤q+r′)

opaque

  -- Subtraction is monotone in its first argument.

  -≡-monotoneˡ : p ≤ p′ → p - q ≡ r → p′ - q ≡ r′ → r ≤ r′
  -≡-monotoneˡ p≤p′ p-q≡r (p′≤q+r′ , P′) =
    -≡≤-monotoneˡ p≤p′ p-q≡r p′≤q+r′

opaque

  -- Subtraction is antitone in its second argument.

  -≡-antitoneʳ : q ≤ q′ → p - q ≡ r → p - q′ ≡ r′ → r′ ≤ r
  -≡-antitoneʳ q≤q′ (p≤q+r , P) (p≤q′+r′ , P′) =
    P′ _ (≤-trans p≤q+r (+-monotoneʳ q≤q′))

opaque

  -- The value of p minus 𝟘 is bounded by p.

  p-𝟘≤p : p - 𝟘 ≤ p
  p-𝟘≤p = ≤-reflexive (sym (+-identityʳ _))

opaque

  -- The value of p minus 𝟘 is p.

  p-𝟘≡p : p - 𝟘 ≡ p
  p-𝟘≡p = p-𝟘≤p , (λ q p≤q+𝟘 → ≤-trans p≤q+𝟘 (≤-reflexive (+-identityʳ q)))

opaque

  -- If p - 𝟘 ≤ q then p ≤ q

  p-𝟘≤  : p - 𝟘 ≤ q → p ≤ q
  p-𝟘≤ p≤q+𝟘 = ≤-trans p≤q+𝟘 (≤-reflexive (+-identityʳ _))

opaque

  -- If p - 𝟘 ≡ q then p ≡ q

  p-𝟘≡ : p - 𝟘 ≡ q → p ≡ q
  p-𝟘≡ p-𝟘≡q = -≡-functional p-𝟘≡p p-𝟘≡q

opaque

  -- The value of p minus p is at most 𝟘.

  p-p≤𝟘 : p - p ≤ 𝟘
  p-p≤𝟘 = ≤-reflexive (sym (+-identityˡ _))

opaque

  -- For a least element, subtraction by p is identity

  ∞-p≤∞ : (∀ {q} → ∞ ≤ q) → ∞ - p ≤ ∞
  ∞-p≤∞ ∞≤ = ∞≤

opaque

  -- For a least element, subtraction by p is identity

  ∞-p≡∞ : (∀ {q} → ∞ ≤ q) → (p : M) → ∞ - p ≡ ∞
  ∞-p≡∞ ∞≤ _ = ∞-p≤∞ ∞≤ , λ _ _ → ∞≤

opaque

  -- If substraction by q is bounded by r and r′ then it is also
  -- bounded by r ∧ r′.

  -≤∧ : p - q ≤ r → p - q ≤ r′ → p - q ≤ (r ∧ r′)
  -≤∧ {p} {q} {r} {r′} ≤r ≤r′ = begin
    p                        ≡⟨ ≤r′ ⟩
    p ∧ (r′ + q)             ≡⟨ ∧-congʳ ≤r ⟩
    (p ∧ (r + q)) ∧ (r′ + q) ≡⟨ ∧-assoc p (r + q) (r′ + q) ⟩
    p ∧ ((r + q) ∧ (r′ + q)) ≡˘⟨ ∧-congˡ (+-distribʳ-∧ q r r′) ⟩
    p ∧ (r ∧ r′ + q)         ∎
    where
    open import Tools.Reasoning.PropositionalEquality

opaque

  -- A distributivity law for substraction over addition

  p+q-r≤p-r+q : p - q ≤ r → (p′ : M)
      → (p + p′ - q ≤ p′ + r)
  p+q-r≤p-r+q {p} {q} {r} p≤r+q p′ = begin
    p + p′        ≤⟨ +-monotoneˡ p≤r+q ⟩
    (r + q) + p′  ≈⟨ +-comm _ _ ⟩
    p′ + (r + q)  ≈˘⟨ +-assoc p′ r q ⟩
    (p′ + r) + q  ∎
    where
    open import Tools.Reasoning.PartialOrder ≤-poset

------------------------------------------------------------------------
-- The predicate Supports-subtraction

-- A modality supports subtraction if whenever p - q ≤ r there is an r′
-- such that p - q ≡ r′.
--
-- In other words, a modality supports subtraction if whenever there is
-- at least one candidate for the value of p - q (i.e. whenever it is
-- meaningful to talk about p - q) there is a least candidate.

Supports-subtraction : Set a
Supports-subtraction =
  ∀ {p q r} → p - q ≤ r → ∃ λ r′ → p - q ≡ r′

-- Subtraction for modalities where _+_ and _∧_ coincide.
-- This is true for instance in some lattices, see e.g.
-- Graded.Modality.Instances.Bounded-distributive-lattice or
-- Graded.Modality.Instances.Information-flow

module Addition≡Meet (+≡∧ : ∀ p q → p + q ≡ p ∧ q) where

  opaque

    -- If p ≤ q then p - q ≤ p

    p-q≤p : p ≤ q → p - q ≤ p
    p-q≤p {p} {q} p≤q = begin
      p     ≡˘⟨ ∧-idem p ⟩
      p ∧ p ≡˘⟨ +≡∧ p p ⟩
      p + p ≤⟨ +-monotoneʳ p≤q ⟩
      p + q ∎
      where
      open import Tools.Reasoning.PartialOrder ≤-poset

  opaque

    -- If p ≤ q then p - q ≡ p

    p-q≡p : p ≤ q → p - q ≡ p
    p-q≡p {p} {q} p≤q = p-q≤p p≤q , (λ r p≤r+q → begin
      p     ≤⟨ p≤r+q ⟩
      r + q ≡⟨ +≡∧ r q ⟩
      r ∧ q ≤⟨ ∧-decreasingˡ r q ⟩
      r     ∎)
      where
      open import Tools.Reasoning.PartialOrder ≤-poset

  opaque

    -- If p - q ≤ r then p ≤ q

    p-q≤r→p≤q : p - q ≤ r → p ≤ q
    p-q≤r→p≤q {p} {q} {r} p≤r+q = begin
      p     ≤⟨ p≤r+q ⟩
      r + q ≡⟨ +≡∧ r q ⟩
      r ∧ q ≤⟨ ∧-decreasingʳ r q ⟩
      q     ∎
      where
      open import Tools.Reasoning.PartialOrder ≤-poset

  opaque

    -- If p - q ≡ r then p ≤ q and r ≡ p

    p-q≡r→p≤q∧r≡p : p - q ≡ r → p ≤ q × r ≡ p
    p-q≡r→p≤q∧r≡p p-q≡r =
      case p-q≤r→p≤q (proj₁ p-q≡r) of λ
        p≤q →
      case -≡-functional p-q≡r (p-q≡p p≤q) of λ
        p≡r →
      p≤q , p≡r

  opaque

    -- Modalities where addition and meet coincide support subtraction

    supports-subtraction : Supports-subtraction
    supports-subtraction {p} p-q≤r = p , p-q≡p (p-q≤r→p≤q p-q≤r)

  opaque

    -- An alternative representation of subtraction

    p-q≡r⇔ : (p - q ≡ r) ⇔ (p ≤ q × r ≡ p)
    p-q≡r⇔ = p-q≡r→p≤q∧r≡p , (λ {(p≤q , refl) → p-q≡p p≤q})

------------------------------------------------------------------------
-- Properties of _-_≤_ and _-_≡_ that hold for well-behaved zeros.

module _ ⦃ _ : Has-well-behaved-zero 𝕄 ⦄ where
  open import Graded.Modality.Properties.Has-well-behaved-zero 𝕄


  opaque

    -- It is only possible to subtract 𝟘 by 𝟘, and the value is 𝟘.

    𝟘-p≤q : 𝟘 - p ≤ q → q ≡ 𝟘 × p ≡ 𝟘
    𝟘-p≤q 𝟘≤p+q = +-positive (𝟘≮ 𝟘≤p+q)

  opaque

    -- It is only possible to subtract 𝟘 by 𝟘, and the value is 𝟘.

    𝟘-p≡q : 𝟘 - p ≡ q → q ≡ 𝟘 × p ≡ 𝟘
    𝟘-p≡q (x , _) = 𝟘-p≤q x

  opaque

    -- It is not possible to subtract non-zero grades from 𝟘

    𝟘-q≰p : q ≢ 𝟘 → 𝟘 - q ≤ p → ⊥
    𝟘-q≰p q≢𝟘 𝟘≤p+q =
      case 𝟘≮ 𝟘≤p+q of λ
        p+q≡𝟘 →
      case +-positiveʳ p+q≡𝟘 of λ
        q≡𝟘 →
      q≢𝟘 q≡𝟘

  opaque

    -- It is not possible to subtract non-zero grades from 𝟘

    𝟘-q≢p : q ≢ 𝟘 → 𝟘 - q ≡ p → ⊥
    𝟘-q≢p q≢𝟘 𝟘-q≡p = 𝟘-q≰p q≢𝟘 (proj₁ 𝟘-q≡p)
