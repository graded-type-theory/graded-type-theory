------------------------------------------------------------------------
-- Sizes
------------------------------------------------------------------------

module Tools.Size where

open import Data.Nat.Induction
open import Data.Nat.Properties
open import Induction.WellFounded
import Relation.Binary.Construct.On as On

open import Tools.Nat

-- Sizes are simple trees.

infixr 6 _⊕_

data Size : Set where
  leaf : Size
  _⊕_  : Size → Size → Size

-- A unary size "constructor".

pattern node s = s ⊕ leaf

private variable
  l l₁ l₂ r r₁ r₂ s s₁ s₂ s₃ : Size

-- The type s₁ ≤ˢ s₂ is inhabited when s₁ can be transformed into s₂
-- through the addition of zero or more nodes (where one child is an
-- arbitrary tree) anywhere in the tree.

infix 10 ↙_ ↘_
infix  4 _≤ˢ_

data _≤ˢ_ : Size → Size → Set where
  leaf : leaf ≤ˢ leaf
  _⊕_  : l₁ ≤ˢ l₂ → r₁ ≤ˢ r₂ → l₁ ⊕ r₁ ≤ˢ l₂ ⊕ r₂
  ↙_   : s ≤ˢ l → s ≤ˢ l ⊕ r
  ↘_   : s ≤ˢ r → s ≤ˢ l ⊕ r

-- The type s₁ <ˢ s₂ is inhabited when s₁ can be transformed into s₂
-- through the addition of one or more nodes (where one child is an
-- arbitrary tree) anywhere in the tree.

infixr 6 _↙⊕_ _⊕↘_
infix  4 _<ˢ_

data _<ˢ_ : Size → Size → Set where
  _↙⊕_ : l₁ <ˢ l₂ → r₁ ≤ˢ r₂ → l₁ ⊕ r₁ <ˢ l₂ ⊕ r₂
  _⊕↘_ : l₁ ≤ˢ l₂ → r₁ <ˢ r₂ → l₁ ⊕ r₁ <ˢ l₂ ⊕ r₂
  ↙_   : s ≤ˢ l → s <ˢ l ⊕ r
  ↘_   : s ≤ˢ r → s <ˢ l ⊕ r

------------------------------------------------------------------------
-- Conversion

opaque

  -- The relation _<ˢ_ is contained in _≤ˢ_.

  <ˢ→≤ˢ : s₁ <ˢ s₂ → s₁ ≤ˢ s₂
  <ˢ→≤ˢ (↙ p)    = ↙ p
  <ˢ→≤ˢ (↘ p)    = ↘ p
  <ˢ→≤ˢ (p ↙⊕ q) = <ˢ→≤ˢ p ⊕ q
  <ˢ→≤ˢ (p ⊕↘ q) = p ⊕ <ˢ→≤ˢ q


------------------------------------------------------------------------
-- Reflexivity

opaque

  -- Reflexivity for _≤ˢ_.

  ◻ : s ≤ˢ s
  ◻ {s = leaf}  = leaf
  ◻ {s = _ ⊕ _} = ◻ ⊕ ◻

------------------------------------------------------------------------
-- Transitivity

opaque

  -- Transitivity for _≤ˢ_.

  ≤ˢ-trans : s₁ ≤ˢ s₂ → s₂ ≤ˢ s₃ → s₁ ≤ˢ s₃
  ≤ˢ-trans p         leaf      = p
  ≤ˢ-trans p         (↙ q)     = ↙ ≤ˢ-trans p q
  ≤ˢ-trans p         (↘ q)     = ↘ ≤ˢ-trans p q
  ≤ˢ-trans (↙ p)     (q₁ ⊕ q₂) = ≤ˢ-trans p (↙ q₁)
  ≤ˢ-trans (↘ p)     (q₁ ⊕ q₂) = ≤ˢ-trans p (↘ q₂)
  ≤ˢ-trans (p₁ ⊕ p₂) (q₁ ⊕ q₂) = ≤ˢ-trans p₁ q₁ ⊕ ≤ˢ-trans p₂ q₂

opaque

  -- A variant of transitivity for _<ˢ_ and _≤ˢ_.

  <ˢ-trans-≤ˢʳ : s₁ <ˢ s₂ → s₂ ≤ˢ s₃ → s₁ <ˢ s₃
  <ˢ-trans-≤ˢʳ p          leaf      = p
  <ˢ-trans-≤ˢʳ p          (↙ q)     = ↙ ≤ˢ-trans (<ˢ→≤ˢ p) q
  <ˢ-trans-≤ˢʳ p          (↘ q)     = ↘ ≤ˢ-trans (<ˢ→≤ˢ p) q
  <ˢ-trans-≤ˢʳ (↙ p)      (q ⊕ _)   = ↙ ≤ˢ-trans p q
  <ˢ-trans-≤ˢʳ (↘ p)      (_ ⊕ q)   = ↘ ≤ˢ-trans p q
  <ˢ-trans-≤ˢʳ (p₁ ↙⊕ p₂) (q₁ ⊕ q₂) = <ˢ-trans-≤ˢʳ p₁ q₁ ↙⊕
                                      ≤ˢ-trans p₂ q₂
  <ˢ-trans-≤ˢʳ (p₁ ⊕↘ p₂) (q₁ ⊕ q₂) = ≤ˢ-trans p₁ q₁ ⊕↘
                                      <ˢ-trans-≤ˢʳ p₂ q₂

opaque

  -- Transitivity for _<ˢ_.

  <ˢ-trans : s₁ <ˢ s₂ → s₂ <ˢ s₃ → s₁ <ˢ s₃
  <ˢ-trans p q = <ˢ-trans-≤ˢʳ p (<ˢ→≤ˢ q)

opaque

  -- A variant of transitivity for _<ˢ_ and _≤ˢ_.

  <ˢ-trans-≤ˢˡ : s₁ ≤ˢ s₂ → s₂ <ˢ s₃ → s₁ <ˢ s₃
  <ˢ-trans-≤ˢˡ leaf      q          = q
  <ˢ-trans-≤ˢˡ (↙ p)     q          = <ˢ-trans (↙ p) q
  <ˢ-trans-≤ˢˡ (↘ p)     q          = <ˢ-trans (↘ p) q
  <ˢ-trans-≤ˢˡ p@(_ ⊕ _) (↙ q)      = ↙ ≤ˢ-trans p q
  <ˢ-trans-≤ˢˡ p@(_ ⊕ _) (↘ q)      = ↘ ≤ˢ-trans p q
  <ˢ-trans-≤ˢˡ (p₁ ⊕ p₂) (q₁ ↙⊕ q₂) = <ˢ-trans-≤ˢˡ p₁ q₁ ↙⊕
                                      ≤ˢ-trans p₂ q₂
  <ˢ-trans-≤ˢˡ (p₁ ⊕ p₂) (q₁ ⊕↘ q₂) = ≤ˢ-trans p₁ q₁ ⊕↘
                                      <ˢ-trans-≤ˢˡ p₂ q₂

------------------------------------------------------------------------
-- More lemmas

opaque

  -- If s₁ ⊕ s₂ ≤ˢ s₃, then s₁ <ˢ s₃.

  ⊕≤ˢ→<ˢˡ : s₁ ⊕ s₂ ≤ˢ s₃ → s₁ <ˢ s₃
  ⊕≤ˢ→<ˢˡ (↙ p)   = ↙ <ˢ→≤ˢ (⊕≤ˢ→<ˢˡ p)
  ⊕≤ˢ→<ˢˡ (↘ p)   = ↘ <ˢ→≤ˢ (⊕≤ˢ→<ˢˡ p)
  ⊕≤ˢ→<ˢˡ (p ⊕ _) = ↙ p

opaque

  -- If s₁ ⊕ s₂ ≤ˢ s₃, then s₂ <ˢ s₃.

  ⊕≤ˢ→<ˢʳ : s₁ ⊕ s₂ ≤ˢ s₃ → s₂ <ˢ s₃
  ⊕≤ˢ→<ˢʳ (↙ p)   = ↙ <ˢ→≤ˢ (⊕≤ˢ→<ˢʳ p)
  ⊕≤ˢ→<ˢʳ (↘ p)   = ↘ <ˢ→≤ˢ (⊕≤ˢ→<ˢʳ p)
  ⊕≤ˢ→<ˢʳ (_ ⊕ p) = ↘ p

------------------------------------------------------------------------
-- Converting sizes to natural numbers

opaque

  -- Sizes can be turned into natural numbers.

  size-of-size : Size → Nat
  size-of-size leaf    = 0
  size-of-size (l ⊕ r) = 1 + size-of-size l + size-of-size r

opaque
  unfolding size-of-size

  -- The function size-of-size is monotone with respect to _≤ˢ_ and
  -- _≤_.

  size-of-size-mono-≤ :
    s₁ ≤ˢ s₂ → size-of-size s₁ ≤ size-of-size s₂
  size-of-size-mono-≤ leaf =
    ≤-refl
  size-of-size-mono-≤ (↙ p) =
    ≤-trans (size-of-size-mono-≤ p) (≤-trans (m≤m+n _ _) (n≤1+n _))
  size-of-size-mono-≤ (↘ p) =
    ≤-trans (size-of-size-mono-≤ p) (≤-trans (m≤n+m _ _) (n≤1+n _))
  size-of-size-mono-≤ (p ⊕ q) =
    s≤s (+-mono-≤ (size-of-size-mono-≤ p) (size-of-size-mono-≤ q))

opaque
  unfolding size-of-size

  -- The function size-of-size is monotone with respect to _<ˢ_ and
  -- _<_.

  size-of-size-mono-< :
    s₁ <ˢ s₂ → size-of-size s₁ < size-of-size s₂
  size-of-size-mono-< (↙ p) =
    s≤s (≤-trans (size-of-size-mono-≤ p) (m≤m+n _ _))
  size-of-size-mono-< (↘ p) =
    s≤s (≤-trans (size-of-size-mono-≤ p) (m≤n+m _ _))
  size-of-size-mono-< (p ↙⊕ q) =
    s≤s (+-mono-<-≤ (size-of-size-mono-< p) (size-of-size-mono-≤ q))
  size-of-size-mono-< (p ⊕↘ q) =
    s≤s (+-mono-≤-< (size-of-size-mono-≤ p) (size-of-size-mono-< q))

------------------------------------------------------------------------
-- Well-founded induction

opaque

  -- The relation _<ˢ_ is well-founded.

  <ˢ-well-founded : WellFounded _<ˢ_
  <ˢ-well-founded =
    Subrelation.wellFounded
      size-of-size-mono-<
      (On.wellFounded size-of-size <-wellFounded)

opaque

  -- Well-founded induction for sizes.

  well-founded-induction :
    ∀ {p} (P : Size → Set p) →
    (∀ s₁ → (∀ {s₂} → s₂ <ˢ s₁ → P s₂) → P s₁) →
    ∀ s → P s
  well-founded-induction =
    All.wfRec <ˢ-well-founded _
