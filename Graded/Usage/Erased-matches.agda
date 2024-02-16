------------------------------------------------------------------------
-- The type Erased-matches
------------------------------------------------------------------------

module Graded.Usage.Erased-matches where

open import Tools.Empty
open import Tools.PropositionalEquality
open import Tools.Unit

-- Two usage rules, with or without support for erased matches, are
-- available for J and K.

data Erased-matches : Set where
  all none : Erased-matches

private variable
  em em₁ em₂ em₃ : Erased-matches

opaque

  -- If em is not equal to none, then em is equal to all.

  ≢none→≡all : em ≢ none → em ≡ all
  ≢none→≡all {em = all}  _   = refl
  ≢none→≡all {em = none} hyp = ⊥-elim (hyp refl)

-- An ordering relation for Erased-matches.

infix 4 _≤ᵉᵐ_

_≤ᵉᵐ_ : Erased-matches → Erased-matches → Set
none ≤ᵉᵐ _   = ⊤
_    ≤ᵉᵐ all = ⊤
_    ≤ᵉᵐ _   = ⊥

opaque

  -- The relation _≤ᵉᵐ_ is reflexive.

  ≤ᵉᵐ-reflexive : em ≤ᵉᵐ em
  ≤ᵉᵐ-reflexive {em = all}  = _
  ≤ᵉᵐ-reflexive {em = none} = _

opaque

  -- The relation _≤ᵉᵐ_ is transitive.

  ≤ᵉᵐ-transitive : em₁ ≤ᵉᵐ em₂ → em₂ ≤ᵉᵐ em₃ → em₁ ≤ᵉᵐ em₃
  ≤ᵉᵐ-transitive {em₁ = none}                         = _
  ≤ᵉᵐ-transitive {em₁ = all}  {em₂ = all} {em₃ = all} = _

opaque

  -- The relation _≤ᵉᵐ_ has a least element.

  none-≤ᵉᵐ : none ≤ᵉᵐ em
  none-≤ᵉᵐ {em = all}  = _
  none-≤ᵉᵐ {em = none} = _

opaque

  -- The relation _≤ᵉᵐ_ has a largest element.

  ≤ᵉᵐ-all : em ≤ᵉᵐ all
  ≤ᵉᵐ-all {em = all}  = _
  ≤ᵉᵐ-all {em = none} = _

opaque

  -- If em₁ ≤ᵉᵐ em₂ and em₂ is the least element (none), then em₁ is
  -- also the least element.

  ≤ᵉᵐ→≡none→≡none : em₁ ≤ᵉᵐ em₂ → em₂ ≡ none → em₁ ≡ none
  ≤ᵉᵐ→≡none→≡none {em₁ = none} {em₂ = none} _ _ = refl

opaque

  -- If em₁ ≤ᵉᵐ em₂ and em₁ is the largest element (all), then em₂
  -- is also the largest element.

  ≤ᵉᵐ→≡all→≡all : em₁ ≤ᵉᵐ em₂ → em₁ ≡ all → em₂ ≡ all
  ≤ᵉᵐ→≡all→≡all {em₁ = all} {em₂ = all} _ _ = refl
