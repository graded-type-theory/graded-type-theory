module Heap.Options where

open import Tools.Bool
open import Tools.Empty
open import Tools.Unit

record Options : Set where
  field
    track-resources : Bool
    ℕ-fullred : Bool

  ℕ-Fullred : Set
  ℕ-Fullred = T ℕ-fullred

  ¬ℕ-Fullred : Set
  ¬ℕ-Fullred = T (not ℕ-fullred)

  not-ℕ-Fullred-and-¬ℕ-Fullred : ⦃ ℕ-Fullred ⦄ → ⦃ ¬ℕ-Fullred ⦄ → ⊥
  not-ℕ-Fullred-and-¬ℕ-Fullred ⦃ (r) ⦄ ⦃ (¬r) ⦄ =
    not-T-and-¬T ℕ-fullred r ¬r

  Track-resources : Set
  Track-resources = T track-resources

  ¬Track-resources : Set
  ¬Track-resources = T (not track-resources)

  not-tracking-and-no-tracking : ⦃ Track-resources ⦄ → ⦃ ¬Track-resources ⦄ → ⊥
  not-tracking-and-no-tracking ⦃ (t) ⦄ ⦃ (nt) ⦄ =
    not-T-and-¬T track-resources t nt

open Options

tracking-and-ℕ-fullred-if : (b : Bool) → Options
tracking-and-ℕ-fullred-if b = record
  { track-resources = true
  ; ℕ-fullred = b
  }

not-tracking-and-ℕ-fullred-if : (b : Bool) → Options
not-tracking-and-ℕ-fullred-if b = record
  { track-resources = false
  ; ℕ-fullred = b
  }

ℕ-Fullred-and-tracking-if : (b : Bool) → Options
ℕ-Fullred-and-tracking-if b = record
  { track-resources = b
  ; ℕ-fullred = true
  }

¬ℕ-Fullred-and-tracking-if : (b : Bool) → Options
¬ℕ-Fullred-and-tracking-if b = record
  { track-resources = b
  ; ℕ-fullred = false
  }

instance
  not-tracking-and-ℕ-fullred-if-true :
    ¬Track-resources (not-tracking-and-ℕ-fullred-if true)
  not-tracking-and-ℕ-fullred-if-true = _

  not-tracking-and-ℕ-fullred-if-false :
    ¬Track-resources (not-tracking-and-ℕ-fullred-if false)
  not-tracking-and-ℕ-fullred-if-false = _

  tracking-and-ℕ-fullred-if-true :
    Track-resources (tracking-and-ℕ-fullred-if true)
  tracking-and-ℕ-fullred-if-true = _

  tracking-and-ℕ-fullred-if-false :
    Track-resources (tracking-and-ℕ-fullred-if false)
  tracking-and-ℕ-fullred-if-false = _

  ℕ-Fullred-and-tracking-if-true :
    ℕ-Fullred (ℕ-Fullred-and-tracking-if true)
  ℕ-Fullred-and-tracking-if-true = _

  ℕ-Fullred-and-tracking-if-false :
    ℕ-Fullred (ℕ-Fullred-and-tracking-if false)
  ℕ-Fullred-and-tracking-if-false = _

  ¬ℕ-Fullred-and-tracking-if-true :
    ¬ℕ-Fullred (¬ℕ-Fullred-and-tracking-if true)
  ¬ℕ-Fullred-and-tracking-if-true = _

  ¬ℕ-Fullred-and-tracking-if-false :
    ¬ℕ-Fullred (¬ℕ-Fullred-and-tracking-if false)
  ¬ℕ-Fullred-and-tracking-if-false = _
