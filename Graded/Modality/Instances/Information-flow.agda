------------------------------------------------------------------------
-- A three-point information flow modality
------------------------------------------------------------------------

module Graded.Modality.Instances.Information-flow where

import Tools.Algebra
open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Function
open import Tools.Level using (lzero)
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

open import Graded.FullReduction.Assumptions
import Graded.Modality
import Graded.Modality.Properties.Division
import Graded.Modality.Properties.Star as Star
open import Graded.Modality.Variant lzero

import Definition.Typed.Restrictions
open import Definition.Untyped

-- Three information levels: low (public), medium (private), and high
-- (more private).

data Level : Set where
  L M H : Level

open Definition.Typed.Restrictions Level
open Graded.Modality               Level
open Tools.Algebra                 Level

private variable
  p q r   : Level
  variant : Modality-variant
  trs     : Type-restrictions

------------------------------------------------------------------------
-- Operators

-- Meet.
--
-- The meet operation is defined in such a way that L ≤ M ≤ H.

infixr 40 _∧_

_∧_ : Level → Level → Level
L ∧ _ = L
_ ∧ L = L
M ∧ _ = M
_ ∧ M = M
H ∧ H = H

-- Addition.
--
-- Addition returns the smallest argument: if a piece of information
-- is used at two levels, then it must be accessible at the smallest
-- one.

infixr 40 _+_

_+_ : Level → Level → Level
_+_ = _∧_

-- Multiplication.
--
-- * If a function that takes a high argument is applied to an
--   expression, then the expression is treated as contributing
--   no variable occurrences (because 𝟘 ≡ H).
-- * If a function that takes a low argument is applied to an
--   expression, then the expression's usage context is not modified.
-- * If a function that takes a medium-level argument is applied to an
--   expression, then the expression's usage context is modified in
--   the following way: H and M are kept, but L is replaced by M.

infixr 45 _·_

_·_ : Level → Level → Level
H · _ = H
M · H = H
M · M = M
M · L = M
L · q = q

-- Division.

infixr 45 _/_

_/_ : Level → Level → Level
L / _ = L
M / L = M
M / M = L
M / H = L
H / H = L
H / _ = H

-- A star operator.

_⊛_▷_ : Level → Level → Level → Level
p ⊛ q ▷ _ = p ∧ q

-- The inferred ordering relation.

infix 10 _≤_

_≤_ : Level → Level → Set
p ≤ q = p ≡ p ∧ q

------------------------------------------------------------------------
-- Some properties

-- L is the least level.

L≤ : ∀ p → L ≤ p
L≤ _ = refl

-- H is the greatest level.

≤H : p ≤ H
≤H {p = L} = refl
≤H {p = M} = refl
≤H {p = H} = refl

-- Multiplication is commutative.

·-comm : Commutative _·_
·-comm = λ where
  L L → refl
  L M → refl
  L H → refl
  M L → refl
  M M → refl
  M H → refl
  H L → refl
  H M → refl
  H H → refl

-- Equality is decidable.

_≟_ : Decidable (_≡_ {A = Level})
_≟_ = λ where
  L L → yes refl
  L M → no (λ ())
  L H → no (λ ())
  M L → no (λ ())
  M M → yes refl
  M H → no (λ ())
  H L → no (λ ())
  H M → no (λ ())
  H H → yes refl

-- All non-empty "decidable subsets" have a least value.

limit :
  (P : Level → Set) → (∀ p → Dec (P p)) → P p →
  ∃ λ p → P p × (∀ q → P q → p ≤ q)
limit {p = p} P dec P-p =
  case dec L of λ where
    (yes P-L)  → L , P-L , λ q _ → L≤ q
    (no ¬-P-L) → case dec M of λ where
      (yes P-M) → M , P-M , λ where
        L P-L → ⊥-elim (¬-P-L P-L)
        M _   → refl
        H _   → refl
      (no ¬-P-M) → case dec H of λ where
        (yes P-H) → H , P-H , λ where
          L P-L → ⊥-elim (¬-P-L P-L)
          M P-M → ⊥-elim (¬-P-M P-M)
          H _   → refl
        (no ¬-P-H) → case _,_ {B = P} p P-p of λ where
          (L , P-L) → ⊥-elim (¬-P-L P-L)
          (M , P-M) → ⊥-elim (¬-P-M P-M)
          (H , P-H) → ⊥-elim (¬-P-H P-H)

------------------------------------------------------------------------
-- The modality

-- A "semiring with meet" for Level.

L≤M≤H-semiring-with-meet : Semiring-with-meet
L≤M≤H-semiring-with-meet = record
  { _+_          = _+_
  ; _·_          = _·_
  ; _∧_          = _∧_
  ; 𝟘            = H
  ; 𝟙            = L
  ; ω            = L
  ; ω≤𝟙          = refl
  ; +-·-Semiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = PE.isEquivalence
              ; ∙-cong        = cong₂ _+_
              }
            ; assoc = +-assoc
            }
          ; identity =
                (λ where
                   L → refl
                   M → refl
                   H → refl)
              , (λ where
                   L → refl
                   M → refl
                   H → refl)
          }
        ; comm = +-comm
        }
      ; *-isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = PE.isEquivalence
            ; ∙-cong        = cong₂ _·_
            }
          ; assoc = ·-assoc
          }
        ; identity =
              (λ where
                 L → refl
                 M → refl
                 H → refl)
            , (λ where
                 L → refl
                 M → refl
                 H → refl)
        }
      ; distrib = ·-distrib-+
      }
    ; zero =
          (λ where
             L → refl
             M → refl
             H → refl)
        , (λ where
             L → refl
             M → refl
             H → refl)
    }
  ; ∧-Semilattice = record
    { isBand = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = PE.isEquivalence
          ; ∙-cong        = cong₂ _∧_
          }
        ; assoc = +-assoc
        }
      ; idem = λ where
          L → refl
          M → refl
          H → refl
      }
    ; comm = +-comm
    }
  ; ·-distrib-∧ = ·-distrib-+
  ; +-distrib-∧ = +-distrib-∧
  }
  where
  +-assoc : Associative _+_
  +-assoc = λ where
    L L L → refl
    L L M → refl
    L L H → refl
    L M L → refl
    L M M → refl
    L M H → refl
    L H L → refl
    L H M → refl
    L H H → refl
    M L L → refl
    M L M → refl
    M L H → refl
    M M L → refl
    M M M → refl
    M M H → refl
    M H L → refl
    M H M → refl
    M H H → refl
    H L L → refl
    H L M → refl
    H L H → refl
    H M L → refl
    H M M → refl
    H M H → refl
    H H L → refl
    H H M → refl
    H H H → refl

  +-comm : Commutative _+_
  +-comm = λ where
    L L → refl
    L M → refl
    L H → refl
    M L → refl
    M M → refl
    M H → refl
    H L → refl
    H M → refl
    H H → refl

  ·-assoc : Associative _·_
  ·-assoc = λ where
    L L L → refl
    L L M → refl
    L L H → refl
    L M L → refl
    L M M → refl
    L M H → refl
    L H L → refl
    L H M → refl
    L H H → refl
    M L L → refl
    M L M → refl
    M L H → refl
    M M L → refl
    M M M → refl
    M M H → refl
    M H L → refl
    M H M → refl
    M H H → refl
    H L L → refl
    H L M → refl
    H L H → refl
    H M L → refl
    H M M → refl
    H M H → refl
    H H L → refl
    H H M → refl
    H H H → refl

  ·-distribˡ-+ : _·_ DistributesOverˡ _+_
  ·-distribˡ-+ = λ where
    L L L → refl
    L L M → refl
    L L H → refl
    L M L → refl
    L M M → refl
    L M H → refl
    L H L → refl
    L H M → refl
    L H H → refl
    M L L → refl
    M L M → refl
    M L H → refl
    M M L → refl
    M M M → refl
    M M H → refl
    M H L → refl
    M H M → refl
    M H H → refl
    H L L → refl
    H L M → refl
    H L H → refl
    H M L → refl
    H M M → refl
    H M H → refl
    H H L → refl
    H H M → refl
    H H H → refl

  ·-distrib-+ : _·_ DistributesOver _+_
  ·-distrib-+ =
    ·-distribˡ-+ , comm+distrˡ⇒distrʳ ·-comm ·-distribˡ-+

  +-distribˡ-∧ : _+_ DistributesOverˡ _∧_
  +-distribˡ-∧ = λ where
    L L L → refl
    L L M → refl
    L L H → refl
    L M L → refl
    L M M → refl
    L M H → refl
    L H L → refl
    L H M → refl
    L H H → refl
    M L L → refl
    M L M → refl
    M L H → refl
    M M L → refl
    M M M → refl
    M M H → refl
    M H L → refl
    M H M → refl
    M H H → refl
    H L L → refl
    H L M → refl
    H L H → refl
    H M L → refl
    H M M → refl
    H M H → refl
    H H L → refl
    H H M → refl
    H H H → refl

  +-distrib-∧ : _+_ DistributesOver _∧_
  +-distrib-∧ =
    +-distribˡ-∧ , comm+distrˡ⇒distrʳ +-comm +-distribˡ-∧

-- This semiring has a well-behaved zero.

L≤M≤H-has-well-behaved-zero :
  Has-well-behaved-zero L≤M≤H-semiring-with-meet
L≤M≤H-has-well-behaved-zero = record
  { 𝟙≢𝟘   = λ ()
  ; is-𝟘? = λ where
      L → no (λ ())
      M → no (λ ())
      H → yes refl
  ; zero-product = λ where
      {p = L} {q = L} ()
      {p = L} {q = M} ()
      {p = L} {q = H} refl → inj₂ refl
      {p = M} {q = L} ()
      {p = M} {q = M} ()
      {p = M} {q = H} refl → inj₂ refl
      {p = H}         _    → inj₁ refl
  ; +-positiveˡ = λ where
      {p = L} {q = L} ()
      {p = L} {q = M} ()
      {p = L} {q = H} ()
      {p = M} {q = L} ()
      {p = M} {q = M} ()
      {p = M} {q = H} ()
      {p = H}         _  → refl
  ; ∧-positiveˡ = λ where
      {p = L} {q = L} ()
      {p = L} {q = M} ()
      {p = L} {q = H} ()
      {p = M} {q = L} ()
      {p = M} {q = M} ()
      {p = M} {q = H} ()
      {p = H}         _  → refl
  }

-- A natrec-star operator can be defined for L≤M≤H-semiring-with-meet.

L≤M≤H-has-star : Has-star L≤M≤H-semiring-with-meet
L≤M≤H-has-star = record
  { _⊛_▷_              = _⊛_▷_
  ; ⊛-ineq             =
        (λ where
           L L L → refl
           L L M → refl
           L L H → refl
           L M L → refl
           L M M → refl
           L M H → refl
           L H L → refl
           L H M → refl
           L H H → refl
           M L L → refl
           M L M → refl
           M L H → refl
           M M L → refl
           M M M → refl
           M M H → refl
           M H L → refl
           M H M → refl
           M H H → refl
           H L L → refl
           H L M → refl
           H L H → refl
           H M L → refl
           H M M → refl
           H M H → refl
           H H L → refl
           H H M → refl
           H H H → refl)
      , (λ where
           L L _ → refl
           L M _ → refl
           L H _ → refl
           M L _ → refl
           M M _ → refl
           M H _ → refl
           H L _ → refl
           H M _ → refl
           H H _ → refl)
  ; +-sub-interchangeable-⊛ = λ _ → λ where
      L L L L → refl
      L L L M → refl
      L L L H → refl
      L L M L → refl
      L L M M → refl
      L L M H → refl
      L L H L → refl
      L L H M → refl
      L L H H → refl
      L M L L → refl
      L M L M → refl
      L M L H → refl
      L M M L → refl
      L M M M → refl
      L M M H → refl
      L M H L → refl
      L M H M → refl
      L M H H → refl
      L H L L → refl
      L H L M → refl
      L H L H → refl
      L H M L → refl
      L H M M → refl
      L H M H → refl
      L H H L → refl
      L H H M → refl
      L H H H → refl
      M L L L → refl
      M L L M → refl
      M L L H → refl
      M L M L → refl
      M L M M → refl
      M L M H → refl
      M L H L → refl
      M L H M → refl
      M L H H → refl
      M M L L → refl
      M M L M → refl
      M M L H → refl
      M M M L → refl
      M M M M → refl
      M M M H → refl
      M M H L → refl
      M M H M → refl
      M M H H → refl
      M H L L → refl
      M H L M → refl
      M H L H → refl
      M H M L → refl
      M H M M → refl
      M H M H → refl
      M H H L → refl
      M H H M → refl
      M H H H → refl
      H L L L → refl
      H L L M → refl
      H L L H → refl
      H L M L → refl
      H L M M → refl
      H L M H → refl
      H L H L → refl
      H L H M → refl
      H L H H → refl
      H M L L → refl
      H M L M → refl
      H M L H → refl
      H M M L → refl
      H M M M → refl
      H M M H → refl
      H M H L → refl
      H M H M → refl
      H M H H → refl
      H H L L → refl
      H H L M → refl
      H H L H → refl
      H H M L → refl
      H H M M → refl
      H H M H → refl
      H H H L → refl
      H H H M → refl
      H H H H → refl
  ; ·-sub-distribʳ-⊛ = λ _ → λ where
      L L L → refl
      L L M → refl
      L L H → refl
      L M L → refl
      L M M → refl
      L M H → refl
      L H L → refl
      L H M → refl
      L H H → refl
      M L L → refl
      M L M → refl
      M L H → refl
      M M L → refl
      M M M → refl
      M M H → refl
      M H L → refl
      M H M → refl
      M H H → refl
      H L L → refl
      H L M → refl
      H L H → refl
      H M L → refl
      H M M → refl
      H M H → refl
      H H L → refl
      H H M → refl
      H H H → refl
  ; ⊛-sub-distrib-∧ = λ _ →
        (λ where
           L L L → refl
           L L M → refl
           L L H → refl
           L M L → refl
           L M M → refl
           L M H → refl
           L H L → refl
           L H M → refl
           L H H → refl
           M L L → refl
           M L M → refl
           M L H → refl
           M M L → refl
           M M M → refl
           M M H → refl
           M H L → refl
           M H M → refl
           M H H → refl
           H L L → refl
           H L M → refl
           H L H → refl
           H M L → refl
           H M M → refl
           H M H → refl
           H H L → refl
           H H M → refl
           H H H → refl)
      , (λ where
           L L L → refl
           L L M → refl
           L L H → refl
           L M L → refl
           L M M → refl
           L M H → refl
           L H L → refl
           L H M → refl
           L H H → refl
           M L L → refl
           M L M → refl
           M L H → refl
           M M L → refl
           M M M → refl
           M M H → refl
           M H L → refl
           M H M → refl
           M H H → refl
           H L L → refl
           H L M → refl
           H L H → refl
           H M L → refl
           H M M → refl
           H M H → refl
           H H L → refl
           H H M → refl
           H H H → refl)
  }

-- A three-point information flow modality (of any kind).

L≤M≤H : Modality-variant → Modality
L≤M≤H variant = record
  { variant            = variant
  ; semiring-with-meet = L≤M≤H-semiring-with-meet
  ; 𝟘-well-behaved     = λ _ → L≤M≤H-has-well-behaved-zero
  ; has-nr             = λ _ →
                           Star.has-nr _ ⦃ has-star = L≤M≤H-has-star ⦄
  }

------------------------------------------------------------------------
-- Some properties related to division

private
  module D =
    Graded.Modality.Properties.Division L≤M≤H-semiring-with-meet

-- The result of dividing p by q is p / q.

/≡/ : p D./ q ≡ p / q
/≡/ {p = L} {q = q} = refl , λ _ _ → refl
/≡/ {p = M} {q = L} = refl , λ where
                        L ()
                        M refl → refl
                        H refl → refl
/≡/ {p = M} {q = M} = refl , λ _ _ → refl
/≡/ {p = M} {q = H} = refl , λ _ _ → refl
/≡/ {p = H} {q = L} = refl , λ where
                        L ()
                        M ()
                        H refl → refl
/≡/ {p = H} {q = M} = refl , λ where
                        L ()
                        M ()
                        H refl → refl
/≡/ {p = H} {q = H} = refl , λ _ _ → refl

-- Division is supported.

division-supported : D.Supports-division
division-supported _ =
  D.Supports-division-by⇔ .proj₂ (λ _ → _ , /≡/)

private

  -- If the result of dividing p by q is r, then p / q is equal to r.

  /≡→/≡ : p D./ q ≡ r → p / q ≡ r
  /≡→/≡ = D./≡-functional /≡/

-- The value of p divided by L is p.

/L≡ : p / L ≡ p
/L≡ = /≡→/≡ D./𝟙≡

-- The value of p divided by p is L.

/≡L : p / p ≡ L
/≡L = /≡→/≡ $ D./≡𝟙 L≤

-- The value of H divided by p is H if p is not equal to H.

H/≡H : p ≢ H → H / p ≡ H
H/≡H p≢H = /≡→/≡ $ D.𝟘/≡𝟘 zero-product p≢H
  where
  open Has-well-behaved-zero L≤M≤H-has-well-behaved-zero

-- The value of p divided by H is L.

/H≡L : p / H ≡ L
/H≡L = /≡→/≡ $ D./𝟘≡𝟙 L≤ ≤H

-- The value of L divided by p is L.

L/≡L : L / p ≡ L
L/≡L {p = p} = /≡→/≡ {q = p} $ D.𝟙/≡𝟙 {p = p} L≤

------------------------------------------------------------------------
-- Instances of Full-reduction-assumptions

-- An instance of Modality-variant along with an instance of
-- Type-restrictions are suitable for the full reduction theorem if
-- * Σₚ-allowed M p does not hold, and
-- * Σₚ-allowed H p implies that 𝟘ᵐ is allowed.

Suitable-for-full-reduction :
  Modality-variant → Type-restrictions → Set
Suitable-for-full-reduction variant trs =
  (∀ p → ¬ Σₚ-allowed M p) ×
  (∀ p → Σₚ-allowed H p → T 𝟘ᵐ-allowed)
  where
  open Modality-variant variant
  open Type-restrictions trs

-- Given an instance of Modality-variant and an instance of
-- Type-restrictions one can create a "suitable" instance of
-- Type-restrictions.

suitable-for-full-reduction :
  (variant : Modality-variant) → Type-restrictions →
  ∃ (Suitable-for-full-reduction variant)
suitable-for-full-reduction variant trs =
    record trs
      { ΠΣ-allowed = λ b p q →
          ΠΣ-allowed b p q ×
          ¬ (b ≡ BMΣ Σₚ × p ≡ M) ×
          (b ≡ BMΣ Σₚ × p ≡ H → T 𝟘ᵐ-allowed)
      }
  , (λ _ → (_$ (refl , refl)) ∘→ proj₁ ∘→ proj₂)
  , (λ _ → (_$ (refl , refl)) ∘→ proj₂ ∘→ proj₂)
  where
  open Modality-variant variant
  open Type-restrictions trs

-- The full reduction assumptions hold for L≤M≤H variant and any
-- "suitable" Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction variant trs →
  Full-reduction-assumptions (L≤M≤H variant) trs
full-reduction-assumptions (¬M , H→𝟘ᵐ) = record
  { 𝟙≤𝟘    = λ _ → refl
  ; ≡𝟙⊎𝟙≤𝟘 = λ where
      {p = L} _  → inj₁ refl
      {p = M} ok → ⊥-elim (¬M _ ok)
      {p = H} ok → inj₂ (refl , H→𝟘ᵐ _ ok , refl)
  }
