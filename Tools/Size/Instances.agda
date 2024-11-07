------------------------------------------------------------------------
-- Instances related to _≤ˢ_ and _<ˢ_, and a related lemma
------------------------------------------------------------------------

{-# OPTIONS --backtracking-instance-search #-}

module Tools.Size.Instances where

open import Tools.Size

private variable
  l l₁ l₂ r r₁ r₂ s : Size

instance

  -- Instances for _≤ˢ_.

  ◻ⁱ : s ≤ˢ s
  ◻ⁱ = ◻

  ↙-≤ⁱ  : ⦃ p : s ≤ˢ l ⦄ → s ≤ˢ l ⊕ r
  ↙-≤ⁱ ⦃ p ⦄ = ↙ p

  ↘-≤ⁱ : ⦃ p : s ≤ˢ r ⦄ → s ≤ˢ l ⊕ r
  ↘-≤ⁱ ⦃ p ⦄ = ↘ p

  -- Instances for _<ˢ_.

  ↙-<ⁱ  : ⦃ p : s ≤ˢ l ⦄ → s <ˢ l ⊕ r
  ↙-<ⁱ ⦃ p ⦄ = ↙ p

  ↘-<ⁱ : ⦃ p : s ≤ˢ r ⦄ → s <ˢ l ⊕ r
  ↘-<ⁱ ⦃ p ⦄ = ↘ p

-- A function that can be used to ask Agda to use instance resolution
-- to infer values of type l <ˢ r.

! : ⦃ p : l <ˢ r ⦄ → l <ˢ r
! ⦃ p ⦄ = p

private

  -- Some tests.
  --
  -- Note that --backtracking-instance-search is (at the time of
  -- writing) turned on in this module.

  _ : s <ˢ (leaf ⊕ leaf) ⊕ s
  _ = !

  _ : s <ˢ (leaf ⊕ s) ⊕ leaf
  _ = !

  _ : s <ˢ leaf ⊕ (s ⊕ leaf) ⊕ leaf
  _ = !
