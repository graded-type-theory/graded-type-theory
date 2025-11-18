------------------------------------------------------------------------
-- A bounded, distributive lattice for which division is not total for
-- the associated "semiring with meet"
------------------------------------------------------------------------

module
  Graded.Modality.Instances.Bounded-distributive-lattice.No-division
  where

open import Graded.Modality
import Graded.Modality.Properties.Division
import Graded.Modality.Instances.Bounded-distributive-lattice as BDL

open import Tools.Empty renaming (⊥ to ⊥′)
open import Tools.Function
open import Tools.Nat as N using (Nat; 1+; _⊔_; _⊓_)
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation as Dec
open import Tools.Sum using (_⊎_; inj₁; inj₂)

private variable
  m n : Nat

-- The elements of ⊤⊎ℕ⊎ℕ are of the form ⊥, left n, or right n.

data ⊤⊎ℕ⊎ℕ : Set where
  ⊥          : ⊤⊎ℕ⊎ℕ
  left right : Nat → ⊤⊎ℕ⊎ℕ

open import Tools.Algebra ⊤⊎ℕ⊎ℕ

-- One can turn ⊤⊎ℕ⊎ℕ into a bounded distributive lattice with the
-- following ordering:
--
-- * ⊥ ≤ p.
--
-- * left m ≤ left n iff m ≥ n.
--
-- * right m ≤ right n iff m ≥ n.
--
-- * left n ≤ right n.

bounded-distributive-lattice : Bounded-distributive-lattice
bounded-distributive-lattice = record
  { _∧_                     = _∧_
  ; _∨_                     = _∨_
  ; ⊥                       = ⊥
  ; ⊤                       = right 0
  ; is-distributive-lattice = record
    { isLattice = record
      { isEquivalence = PE.isEquivalence
      ; ∨-comm        = ∨-comm
      ; ∨-assoc = λ where
          ⊥         _         _         → refl
          (left  _) ⊥         _         → refl
          (left  _) (left  _) ⊥         → refl
          (left  _) (left  _) (left  _) → cong left  (N.⊓-assoc _ _ _)
          (left  _) (left  _) (right _) → cong right (N.⊓-assoc _ _ _)
          (left  _) (right _) ⊥         → refl
          (left  _) (right _) (left  _) → cong right (N.⊓-assoc _ _ _)
          (left  _) (right _) (right _) → cong right (N.⊓-assoc _ _ _)
          (right _) ⊥         _         → refl
          (right _) (left  _) ⊥         → refl
          (right _) (left  _) (left  _) → cong right (N.⊓-assoc _ _ _)
          (right _) (left  _) (right _) → cong right (N.⊓-assoc _ _ _)
          (right _) (right _) ⊥         → refl
          (right _) (right _) (left  _) → cong right (N.⊓-assoc _ _ _)
          (right _) (right _) (right _) → cong right (N.⊓-assoc _ _ _)
      ; ∨-cong = PE.cong₂ _∨_
      ; ∧-comm = ∧-comm
      ; ∧-assoc = λ where
          ⊥         _         _         → refl
          (left  _) ⊥         _         → refl
          (left  _) (left  _) ⊥         → refl
          (left  m) (left  _) (left  _) → cong left  (N.⊔-assoc m _ _)
          (left  m) (left  _) (right _) → cong left  (N.⊔-assoc m _ _)
          (left  _) (right _) ⊥         → refl
          (left  m) (right _) (left  _) → cong left  (N.⊔-assoc m _ _)
          (left  m) (right _) (right _) → cong left  (N.⊔-assoc m _ _)
          (right _) ⊥         _         → refl
          (right _) (left  _) ⊥         → refl
          (right m) (left  _) (left  _) → cong left  (N.⊔-assoc m _ _)
          (right m) (left  _) (right _) → cong left  (N.⊔-assoc m _ _)
          (right _) (right _) ⊥         → refl
          (right m) (right _) (left  _) → cong left  (N.⊔-assoc m _ _)
          (right m) (right _) (right _) → cong right (N.⊔-assoc m _ _)
      ; ∧-cong     = PE.cong₂ _∧_
      ; absorptive =
            (λ where
               (left  _) (left  _) → cong left  (N.⊓-absorbs-⊔ _ _)
               (left  _) (right _) → cong left  (N.⊓-absorbs-⊔ _ _)
               (left  _) ⊥         → refl
               (right _) (left  _) → cong right (N.⊓-absorbs-⊔ _ _)
               (right _) (right _) → cong right (N.⊓-absorbs-⊔ _ _)
               (right _) ⊥         → refl
               ⊥         _         → refl)
          , (λ where
               (left  _) (left  _) → cong left  (N.⊔-absorbs-⊓ _ _)
               (left  _) (right _) → cong left  (N.⊔-absorbs-⊓ _ _)
               (left  _) ⊥         → cong left  (N.⊔-idem _)
               (right _) (left  _) → cong right (N.⊔-absorbs-⊓ _ _)
               (right _) (right _) → cong right (N.⊔-absorbs-⊓ _ _)
               (right _) ⊥         → cong right (N.⊔-idem _)
               ⊥         _         → refl)
      }
    ; ∨-distrib-∧ =
          comm∧distrʳ⇒distrˡ ∨-comm ∨-distribʳ-∧
        , ∨-distribʳ-∧
    ; ∧-distrib-∨ =
          comm∧distrʳ⇒distrˡ ∧-comm ∧-distribʳ-∨
        , ∧-distribʳ-∨

    }
  ; ⊥≤ = λ _ → refl
  ; ≤⊤ = λ where
      (left  _) → cong left  (sym (N.⊔-identityʳ _))
      (right _) → cong right (sym (N.⊔-identityʳ _))
      ⊥         → refl
  }
  where
  open Tools.Reasoning.PropositionalEquality

  infix 40 _∧_ _∨_

  _∧_ : ⊤⊎ℕ⊎ℕ → ⊤⊎ℕ⊎ℕ → ⊤⊎ℕ⊎ℕ
  ⊥       ∧ _       = ⊥
  _       ∧ ⊥       = ⊥
  left  m ∧ left  n = left  (m ⊔ n)
  right m ∧ right n = right (m ⊔ n)
  left  m ∧ right n = left  (m ⊔ n)
  right m ∧ left  n = left  (m ⊔ n)

  _∨_ : ⊤⊎ℕ⊎ℕ → ⊤⊎ℕ⊎ℕ → ⊤⊎ℕ⊎ℕ
  ⊥       ∨ q       = q
  p       ∨ ⊥       = p
  left  m ∨ left  n = left  (m ⊓ n)
  right m ∨ right n = right (m ⊓ n)
  left  m ∨ right n = right (m ⊓ n)
  right m ∨ left  n = right (m ⊓ n)

  ∧-comm : Commutative _∧_
  ∧-comm = λ where
    ⊥         ⊥         → refl
    ⊥         (left  _) → refl
    ⊥         (right _) → refl
    (left  _) ⊥         → refl
    (left  m) (left  _) → cong left  (N.⊔-comm m _)
    (left  m) (right _) → cong left  (N.⊔-comm m _)
    (right _) ⊥         → refl
    (right m) (left  _) → cong left  (N.⊔-comm m _)
    (right m) (right _) → cong right (N.⊔-comm m _)

  ∨-comm : Commutative _∨_
  ∨-comm = λ where
    ⊥         ⊥         → refl
    ⊥         (left  _) → refl
    ⊥         (right _) → refl
    (left  _) ⊥         → refl
    (left  _) (left  _) → cong left  (N.⊓-comm _ _)
    (left  _) (right _) → cong right (N.⊓-comm _ _)
    (right _) ⊥         → refl
    (right _) (left  _) → cong right (N.⊓-comm _ _)
    (right _) (right _) → cong right (N.⊓-comm _ _)

  lemma₁ : m ≡ m ⊔ (n ⊓ m)
  lemma₁ {m = m} {n = n} =
    m            ≡˘⟨ N.⊔-absorbs-⊓ m n ⟩
    m ⊔ (m ⊓ n)  ≡⟨ cong (m ⊔_) (N.⊓-comm _ _) ⟩
    m ⊔ (n ⊓ m)  ∎

  lemma₂ : m ≡ (n ⊓ m) ⊔ m
  lemma₂ {m = m} {n = n} =
    m            ≡⟨ lemma₁ ⟩
    m ⊔ (n ⊓ m)  ≡⟨ N.⊔-comm m _ ⟩
    (n ⊓ m) ⊔ m  ∎

  ∨-distribʳ-∧ : _∨_ DistributesOverʳ _∧_
  ∨-distribʳ-∧ = λ where
    (left  _) (left  n) (left  _) → cong left  (N.⊓-distribʳ-⊔ _ n _)
    (right _) (left  n) (left  _) → cong right (N.⊓-distribʳ-⊔ _ n _)
    ⊥         (left  _) (left  _) → refl
    (left  _) (left  n) (right _) → cong left  (N.⊓-distribʳ-⊔ _ n _)
    (right _) (left  n) (right _) → cong right (N.⊓-distribʳ-⊔ _ n _)
    ⊥         (left  _) (right _) → refl
    (left  _) (left  _) ⊥         → cong left  lemma₂
    (right _) (left  _) ⊥         → cong right lemma₂
    ⊥         (left  _) ⊥         → refl
    (left  _) (right n) (left  _) → cong left  (N.⊓-distribʳ-⊔ _ n _)
    (right _) (right n) (left  _) → cong right (N.⊓-distribʳ-⊔ _ n _)
    ⊥         (right _) (left  _) → refl
    (left  _) (right n) (right _) → cong right (N.⊓-distribʳ-⊔ _ n _)
    (right _) (right n) (right _) → cong right (N.⊓-distribʳ-⊔ _ n _)
    ⊥         (right _) (right _) → refl
    (left  _) (right _) ⊥         → cong left  lemma₂
    (right _) (right _) ⊥         → cong right lemma₂
    ⊥         (right _) ⊥         → refl
    (left  _) ⊥         (left  _) → cong left  lemma₁
    (right _) ⊥         (left  _) → cong right lemma₁
    ⊥         ⊥         (left  _) → refl
    (left  _) ⊥         (right _) → cong left  lemma₁
    (right _) ⊥         (right _) → cong right lemma₁
    ⊥         ⊥         (right _) → refl
    (left  _) ⊥         ⊥         → cong left  (sym (N.⊔-idem _))
    (right _) ⊥         ⊥         → cong right (sym (N.⊔-idem _))
    ⊥         ⊥         ⊥         → refl

  ∧-distribʳ-∨ : _∧_ DistributesOverʳ _∨_
  ∧-distribʳ-∨ = λ where
    (left  _) (left  n) (left  _) → cong left (N.⊔-distribʳ-⊓ _ n _)
    (right _) (left  n) (left  _) → cong left (N.⊔-distribʳ-⊓ _ n _)
    ⊥         (left  _) (left  _) → refl
    (left  _) (left  n) (right _) → cong left (N.⊔-distribʳ-⊓ _ n _)
    (right _) (left  n) (right _) → cong right (N.⊔-distribʳ-⊓ _ n _)
    ⊥         (left  _) (right _) → refl
    (left  _) (left  _) ⊥         → refl
    (right _) (left  _) ⊥         → refl
    ⊥         (left  _) ⊥         → refl
    (left  _) (right n) (left  _) → cong left (N.⊔-distribʳ-⊓ _ n _)
    (right _) (right n) (left  _) → cong right (N.⊔-distribʳ-⊓ _ n _)
    ⊥         (right _) (left  _) → refl
    (left  _) (right n) (right _) → cong left (N.⊔-distribʳ-⊓ _ n _)
    (right _) (right n) (right _) → cong right (N.⊔-distribʳ-⊓ _ n _)
    ⊥         (right _) (right _) → refl
    (left  _) (right _) ⊥         → refl
    (right _) (right _) ⊥         → refl
    ⊥         (right _) ⊥         → refl
    (left  _) ⊥         (left  _) → refl
    (right _) ⊥         (left  _) → refl
    ⊥         ⊥         (left  _) → refl
    (left  _) ⊥         (right _) → refl
    (right _) ⊥         (right _) → refl
    ⊥         ⊥         (right _) → refl
    (left  _) ⊥         ⊥         → refl
    (right _) ⊥         ⊥         → refl
    ⊥         ⊥         ⊥         → refl



-- The "semiring with meet" associated to
-- bounded-distributive-lattice.

semiring-with-meet : Semiring-with-meet ⊤⊎ℕ⊎ℕ
semiring-with-meet =
  BDL.semiring-with-meet _ bounded-distributive-lattice λ where
    ⊥         → no (λ ())
    (left _)  → no (λ ())
    (right n) → Dec.map (cong right) (λ { refl → refl }) (n N.≟ 0)

-- The zero-product property fails for this "semiring with meet".

¬-zero-product :
  let open Semiring-with-meet semiring-with-meet in
  ¬ (∀ {p q} → p · q ≡ 𝟘 → p ≡ 𝟘 ⊎ q ≡ 𝟘)
¬-zero-product =
  ({p q : ⊤⊎ℕ⊎ℕ} → p · q ≡ right 0 → p ≡ right 0 ⊎ q ≡ right 0)        →⟨ (λ hyp → hyp) ⟩
  (right 1 · left 0 ≡ right 0 → right 1 ≡ right 0 ⊎ left 0 ≡ right 0)  →⟨ _$ refl ⟩
  right 1 ≡ right 0 ⊎ left 0 ≡ right 0                                 →⟨ (λ { (inj₁ ()); (inj₂ ()) }) ⟩
  ⊥′                                                                   □
  where
  open Semiring-with-meet semiring-with-meet

-- This "semiring with meet" does not have a well-behaved zero.

¬-Has-well-behaved-zero :
  ¬ Has-well-behaved-zero ⊤⊎ℕ⊎ℕ semiring-with-meet
¬-Has-well-behaved-zero =
  Has-well-behaved-zero ⊤⊎ℕ⊎ℕ semiring-with-meet                 →⟨ Has-well-behaved-zero.zero-product ⟩
  ({p q : ⊤⊎ℕ⊎ℕ} → p · q ≡ right 0 → p ≡ right 0 ⊎ q ≡ right 0)  →⟨ ¬-zero-product ⟩
  ⊥′                                                             □
  where
  open Semiring-with-meet semiring-with-meet

open Graded.Modality.Properties.Division semiring-with-meet

-- Division by left n is not supported for semiring-with-meet.

¬-Supports-division-by-left : ¬ Supports-division-by (left n)
¬-Supports-division-by-left {n = n₀} =
  Supports-division-by (left n₀)    →⟨ Supports-division-by⇔ {q = left _} .proj₁ ⟩
  (∀ p → ∃ λ r → p / left n₀ ≡ r)   →⟨ _$ _ ⟩
  (∃ λ r → right n₀ / left n₀ ≡ r)  →⟨ rn₀/ln₀≢ _ ∘→ proj₂ ⟩
  ⊥′                                □
  where
  open Semiring-with-meet semiring-with-meet

  right-injective : right m ≡ right n → m ≡ n
  right-injective refl = refl

  rn₀/ln₀≢ : ∀ p → ¬ right n₀ / left n₀ ≡ p
  rn₀/ln₀≢ ⊥ =
    right n₀ / left n₀ ≡ ⊥  →⟨ proj₁ ⟩
    right n₀ / left n₀ ≤ ⊥  →⟨ (λ ()) ⟩
    ⊥′                    □
  rn₀/ln₀≢ (left n) =
    (right n₀ / left n₀ ≡ left n)  →⟨ proj₁ ⟩
    (right n₀ / left n₀ ≤ left n)  →⟨ idᶠ ⟩
    right n₀ ≤ left (n₀ ⊓ n)       →⟨ (λ ()) ⟩
    ⊥′                             □
  rn₀/ln₀≢ (right n) =
    (right n₀ / left n₀ ≡ right n)  →⟨ (λ hyp → hyp .proj₂ _ (cong right (sym (N.⊔-absorbs-⊓ _ _)))) ⟩
    right n ≤ right (1+ n)          →⟨ right-injective ⟩
    n ≡ n ⊔ 1+ n                    →⟨ trans (sym (N.m≥n⇒m⊔n≡m (N.n≤1+n _))) ∘→ trans (N.⊔-comm (1+ n) n) ∘→ sym ⟩
    1+ n ≡ n                        →⟨ (λ ()) ⟩
    ⊥′                              □

-- Division is not supported for semiring-with-meet.

¬-Supports-division : ¬ Supports-division
¬-Supports-division =
  Supports-division              →⟨ _$ left _ ⟩
  Supports-division-by (left 0)  →⟨ ¬-Supports-division-by-left ⟩
  ⊥′                             □

-- Division is not total for semiring-with-meet.

¬-division-total : ¬ ((p q : ⊤⊎ℕ⊎ℕ) → ∃ (p / q ≡_))
¬-division-total =
  ((p q : ⊤⊎ℕ⊎ℕ) → ∃ (p / q ≡_))  →⟨ (λ hyp p → Supports-division-by⇔ {q = p} .proj₂ (flip hyp p)) ⟩
  Supports-division               →⟨ ¬-Supports-division ⟩
  ⊥′                              □
