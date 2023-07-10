------------------------------------------------------------------------
-- A bounded, distributive lattice for which division is not total for
-- the associated "semiring with meet"
------------------------------------------------------------------------

module
  Graded.Modality.Instances.Bounded-distributive-lattice.No-division
  where

open import Graded.Modality
import Graded.Modality.Properties.Division
open import Graded.Modality.Instances.Bounded-distributive-lattice
  as BDL using (Bounded-distributive-lattice)

open import Tools.Empty renaming (⊥ to ⊥′)
open import Tools.Function
open import Tools.Nat as N using (Nat; 1+; _⊔_; _⊓_)
open import Tools.Nullary
open import Tools.Product
open import Tools.PropositionalEquality as PE hiding (⊥)
import Tools.Reasoning.PropositionalEquality

private variable
  m n : Nat

-- The elements of ⊤⊎ℕ⊎ℕ are of the form ⊥, left n, or right n.

data ⊤⊎ℕ⊎ℕ : Set where
  ⊥          : ⊤⊎ℕ⊎ℕ
  left right : Nat → ⊤⊎ℕ⊎ℕ

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

bounded-distributive-lattice : Bounded-distributive-lattice ⊤⊎ℕ⊎ℕ
bounded-distributive-lattice = record
  { _∧_                     = _∧_
  ; _∨_                     = _∨_
  ; ⊥                       = ⊥
  ; ⊤                       = right 0
  ; is-distributive-lattice = record
    { isLattice = record
      { isEquivalence = PE.isEquivalence
      ; ∨-comm        = λ where
          ⊥         ⊥         → refl
          ⊥         (left  _) → refl
          ⊥         (right _) → refl
          (left  _) ⊥         → refl
          (left  _) (left  _) → cong left  (N.⊓-comm _ _)
          (left  _) (right _) → cong right (N.⊓-comm _ _)
          (right _) ⊥         → refl
          (right _) (left  _) → cong right (N.⊓-comm _ _)
          (right _) (right _) → cong right (N.⊓-comm _ _)
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
      ; ∧-comm = λ where
          ⊥         ⊥         → refl
          ⊥         (left  _) → refl
          ⊥         (right _) → refl
          (left  _) ⊥         → refl
          (left  m) (left  _) → cong left  (N.⊔-comm m _)
          (left  m) (right _) → cong left  (N.⊔-comm m _)
          (right _) ⊥         → refl
          (right m) (left  _) → cong left  (N.⊔-comm m _)
          (right m) (right _) → cong right (N.⊔-comm m _)
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
    ; ∨-distribʳ-∧ = λ where
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

-- The "semiring with meet" associated to
-- bounded-distributive-lattice.

semiring-with-meet : Semiring-with-meet ⊤⊎ℕ⊎ℕ
semiring-with-meet =
  BDL.semiring-with-meet _ bounded-distributive-lattice

open Graded.Modality.Properties.Division semiring-with-meet

-- Division is not total for semiring-with-meet.

¬-division-total : ¬ ((p q : ⊤⊎ℕ⊎ℕ) → ∃ (p / q ≡_))
¬-division-total total = uncurry r0/l0≢ (total (right 0) (left 0))
  where
  open Semiring-with-meet semiring-with-meet

  right-injective : right m ≡ right n → m ≡ n
  right-injective refl = refl

  r0/l0≢ : ∀ p → ¬ right 0 / left 0 ≡ p
  r0/l0≢ ⊥ =
    right 0 / left 0 ≡ ⊥  →⟨ proj₁ ⟩
    right 0 / left 0 ≤ ⊥  →⟨ (λ ()) ⟩
    ⊥′                    □
  r0/l0≢ (left n) =
    (right 0 / left 0 ≡ left n)  →⟨ proj₁ ⟩
    (right 0 / left 0 ≤ left n)  →⟨ idᶠ ⟩
    right 0 ≤ left 0             →⟨ (λ ()) ⟩
    ⊥′                           □
  r0/l0≢ (right n) =
    (right 0 / left 0 ≡ right n)  →⟨ (λ hyp → hyp .proj₂ _ refl) ⟩
    right n ≤ right (1+ n)        →⟨ right-injective ⟩
    n ≡ n ⊔ 1+ n                  →⟨ trans (sym (N.m≥n⇒m⊔n≡m (N.n≤1+n _))) ∘→ trans (N.⊔-comm (1+ n) n) ∘→ sym ⟩
    1+ n ≡ n                      →⟨ (λ ()) ⟩
    ⊥′                            □
