------------------------------------------------------------------------
-- The booleans
------------------------------------------------------------------------

module Tools.Bool where

open import Data.Bool.Base
  using (Bool; true; false; not; _∧_; _∨_; if_then_else_; T; f≤t; b≤b)
  renaming (_≤_ to _≤ᵇ_)
  public
open import Data.Bool.Properties
  using (∨-comm; ∨-assoc; ∨-identityʳ;
         ∧-comm; ∧-assoc; ∧-identityʳ; ∧-idem; ∧-zeroʳ; ∧-zeroˡ;
         ∨-∧-absorptive;
         ∧-distribʳ-∨; ∧-distribˡ-∨; ∨-distribʳ-∧; ∨-distribˡ-∧;
         T?)
  public
open import Data.Bool.Properties using (≤-isPartialOrder)
import Function.Bundles as Fun

open import Tools.Empty
open import Tools.Function
open import Tools.Relation
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Sum

private variable
  b x y : Bool

module ≤ᵇ-Reasoning = Tools.Reasoning.PartialOrder
  (record { Carrier = Bool ; _≈_ = _≡_ ; _≤_ = _≤ᵇ_
          ; isPartialOrder = ≤-isPartialOrder })


-- The function T is pointwise propositional.

T-propositional : Is-proposition (T b)
T-propositional {b = true} = refl

-- T (not b) is logically equivalent to ¬ T b.

T-not⇔¬-T : T (not b) ⇔ (¬ T b)
T-not⇔¬-T {b = false} = (λ { _ → idᶠ }) , _
T-not⇔¬-T {b = true}  = (λ ()) , (_$ _)

-- T x ⇔ T y is logically equivalent to x ≡ y.

T⇔T : (T x ⇔ T y) ⇔ x ≡ y
T⇔T {x = false} {y = false} = (λ _ → refl) , (λ _ → id⇔)
T⇔T {x = false} {y = true}  = ⊥-elim ∘→ (_$ _) ∘→ proj₂ , (λ ())
T⇔T {x = true}  {y = false} = ⊥-elim ∘→ (_$ _) ∘→ proj₁ , (λ ())
T⇔T {x = true}  {y = true}  = (λ _ → refl) , (λ _ → id⇔)

-- T (x ∧ y) is logically equivalent to T x × T y.

T-∧ : T (x ∧ y) ⇔ (T x × T y)
T-∧ =
    Data.Bool.Properties.T-∧ .Fun.Equivalence.to
  , Data.Bool.Properties.T-∧ .Fun.Equivalence.from

-- T (x ∨ y) is logically equivalent to T x ⊎ T y.

T-∨ : T (x ∨ y) ⇔ (T x ⊎ T y)
T-∨ =
    Data.Bool.Properties.T-∨ .Fun.Equivalence.to
  , Data.Bool.Properties.T-∨ .Fun.Equivalence.from

-- The statement ¬ T b is logically equivalent to b ≡ false.

¬-T : (¬ T b) ⇔ b ≡ false
¬-T {b = false} = (λ _ → refl) , (λ _ ())
¬-T {b = true}  = ⊥-elim ∘→ (_$ _) , (λ ())

opaque

  -- The statement T b is logically equivalent to b ≡ true.

  T-true : T b ⇔ b ≡ true
  T-true {b = false} = ⊥-elim , λ ()
  T-true {b = true}  = (λ _ → refl) , λ _ → _

-- If x ∨ y is false, then x is false.

∨-positiveˡ : x ∨ y ≡ false → x ≡ false
∨-positiveˡ {x = false} _ = refl

-- If x ∧ y is false, then x is false or y is false.

∧-zero-product : x ∧ y ≡ false → x ≡ false ⊎ y ≡ false
∧-zero-product {x = false} _ = inj₁ refl
∧-zero-product {y = false} _ = inj₂ refl

-- One cannot have T b and T (not b)

not-T-and-¬T : (b : Bool) → T b → T (not b) → ⊥
not-T-and-¬T false t ¬t = t
not-T-and-¬T true t ¬t = ¬t

not-T-and-¬T′ : (b : Bool) → ⦃ T b ⦄ → ⦃ T (not b) ⦄ → ⊥
not-T-and-¬T′ b ⦃ (x) ⦄ ⦃ (y) ⦄ = not-T-and-¬T b x y


opaque

  -- _∧_ is a decreasing function

  ∧-decreasingˡ : x ∧ y ≤ᵇ x
  ∧-decreasingˡ {(false)} = b≤b
  ∧-decreasingˡ {(true)} {(false)} = f≤t
  ∧-decreasingˡ {(true)} {(true)} = b≤b

opaque

  -- _∧_ is a decreasing function

  ∧-decreasingʳ : x ∧ y ≤ᵇ y
  ∧-decreasingʳ {(false)} {(false)} = b≤b
  ∧-decreasingʳ {(false)} {(true)} = f≤t
  ∧-decreasingʳ {(true)} {(false)} = b≤b
  ∧-decreasingʳ {(true)} {(true)} = b≤b

opaque

  -- Relating _≤ᵇ_ and _∧_

  ≤ᵇ-∧ : x ≤ᵇ y → x ∧ y ≡ x
  ≤ᵇ-∧ f≤t = refl
  ≤ᵇ-∧ b≤b = ∧-idem _
