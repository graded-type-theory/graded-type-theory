------------------------------------------------------------------------
-- The type Erased-matches
------------------------------------------------------------------------

module Graded.Usage.Erased-matches where

open import Tools.Empty
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Unit

-- The three values of the type Erased-matches correspond to the three
-- usage rules available for J and K:
--
-- * none: Rules without support for erased matches.
-- * some: Rules with limited support for erased matches.
-- * all:  Rules with full support for erased matches.
--
-- The two values of the type Some-erased-matches correspond to the
-- usage rules with at least some support for erased matches.

data Some-erased-matches : Set where
  all′ some′ : Some-erased-matches

data Erased-matches : Set where
  none     : Erased-matches
  not-none : Some-erased-matches → Erased-matches

pattern all  = not-none all′
pattern some = not-none some′

private variable
  em em₁ em₂ em₃ : Erased-matches

-- An ordering relation for Erased-matches.

infix 4 _≤ᵉᵐ_

_≤ᵉᵐ_ : Erased-matches → Erased-matches → Set
none ≤ᵉᵐ _    = ⊤
some ≤ᵉᵐ some = ⊤
_    ≤ᵉᵐ all  = ⊤
_    ≤ᵉᵐ _    = ⊥

opaque

  -- The relation _≤ᵉᵐ_ is reflexive.

  ≤ᵉᵐ-reflexive : em ≤ᵉᵐ em
  ≤ᵉᵐ-reflexive {em = all}  = _
  ≤ᵉᵐ-reflexive {em = some} = _
  ≤ᵉᵐ-reflexive {em = none} = _

opaque

  -- The relation _≤ᵉᵐ_ is transitive.

  ≤ᵉᵐ-transitive : em₁ ≤ᵉᵐ em₂ → em₂ ≤ᵉᵐ em₃ → em₁ ≤ᵉᵐ em₃
  ≤ᵉᵐ-transitive {em₁ = none}                           = _
  ≤ᵉᵐ-transitive {em₁ = some} {em₂ = some} {em₃ = some} = _
  ≤ᵉᵐ-transitive {em₁ = some}              {em₃ = all}  = _
  ≤ᵉᵐ-transitive {em₁ = all}  {em₂ = all}  {em₃ = all}  = _

opaque

  -- The relation _≤ᵉᵐ_ has a least element.

  none-≤ᵉᵐ : none ≤ᵉᵐ em
  none-≤ᵉᵐ {em = all}  = _
  none-≤ᵉᵐ {em = some} = _
  none-≤ᵉᵐ {em = none} = _

opaque

  -- The relation _≤ᵉᵐ_ has a largest element.

  ≤ᵉᵐ-all : em ≤ᵉᵐ all
  ≤ᵉᵐ-all {em = all}  = _
  ≤ᵉᵐ-all {em = some} = _
  ≤ᵉᵐ-all {em = none} = _

opaque

  -- If em₁ ≤ᵉᵐ em₂ and em₂ is the least element (none), then em₁ is
  -- also the least element.

  ≤ᵉᵐ→≡none→≡none : em₁ ≤ᵉᵐ em₂ → em₂ ≡ none → em₁ ≡ none
  ≤ᵉᵐ→≡none→≡none {em₁ = none} {em₂ = none} _ _ = refl
  ≤ᵉᵐ→≡none→≡none {em₁ = all}  {em₂ = none} ()

opaque

  -- If em₁ ≤ᵉᵐ em₂ and em₁ is some, then em₂ not-none something.

  ≤ᵉᵐ→≡some→≡not-none :
    em₁ ≤ᵉᵐ em₂ → em₁ ≡ some → ∃ λ sem → em₂ ≡ not-none sem
  ≤ᵉᵐ→≡some→≡not-none {em₁ = some} {em₂ = not-none _} _ _ = _ , refl

opaque

  -- If em₁ ≤ᵉᵐ em₂ and em₁ is the largest element (all), then em₂
  -- is also the largest element.

  ≤ᵉᵐ→≡all→≡all : em₁ ≤ᵉᵐ em₂ → em₁ ≡ all → em₂ ≡ all
  ≤ᵉᵐ→≡all→≡all {em₁ = all} {em₂ = all} _ _ = refl
