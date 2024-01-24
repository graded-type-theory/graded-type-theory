------------------------------------------------------------------------
-- Restrictions on usage derivations
------------------------------------------------------------------------

import Graded.Modality

module Graded.Usage.Restrictions
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  where

open import Graded.Mode 𝕄

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
open import Tools.Empty

private variable
  p q r  : M
  m m′   : Mode
  ⦃ ok ⦄ : T _

-- Restrictions on/choices for usage derivations.

record Usage-restrictions : Set (lsuc a) where
  no-eta-equality
  field
    -- The prodrec constructor's quantities have to satisfy this
    -- predicate (for the current mode).
    Prodrec-allowed : Mode → (r p q : M) → Set a

    -- Prodrec-allowed is downwards closed in the mode (if 𝟙ᵐ is seen
    -- as a largest element).
    Prodrec-allowed-downwards-closed :
      Prodrec-allowed 𝟙ᵐ r p q → Prodrec-allowed 𝟘ᵐ[ ok ] r p q

    -- The unitrec constructor's quantities have to satisfy this
    -- predicate (for the current mode).
    Unitrec-allowed : Mode → (p q : M) → Set a

    -- Unitrec-allowed is downwards closed in the mode (if 𝟙ᵐ is seen
    -- as a largest element).
    Unitrec-allowed-downwards-closed :
      Unitrec-allowed 𝟙ᵐ p q → Unitrec-allowed 𝟘ᵐ[ ok ] p q

    -- Should the strong unit type act as a "sink"?
    starˢ-sink : Bool

    -- Are most things erased in the usage rule for Id?
    Id-erased : Set a

    -- Id-erased is decided.
    Id-erased? : Dec Id-erased

    -- Are erased matches allowed for the J rule (for the current
    -- mode)? In that case all arguments but one are erased, and the
    -- non-erased argument is treated as "linear".
    Erased-matches-for-J : Mode → Set a

    -- Erased-matches-for-J is pointwise decided.
    Erased-matches-for-J? : ∀ m → Dec (Erased-matches-for-J m)

    -- Erased-matches-for-J is downwards closed (if 𝟙ᵐ is seen as a
    -- largest element).
    Erased-matches-for-J-downwards-closed :
      Erased-matches-for-J 𝟙ᵐ → Erased-matches-for-J 𝟘ᵐ[ ok ]

    -- Are erased matches allowed for the K rule (for the current
    -- mode)? In that case all arguments but one are erased, and the
    -- non-erased argument is treated as "linear".
    Erased-matches-for-K : Mode → Set a

    -- Erased-matches-for-K is pointwise decided.
    Erased-matches-for-K? : ∀ m → Dec (Erased-matches-for-K m)

    -- Erased-matches-for-K is downwards closed (if 𝟙ᵐ is seen as a
    -- largest element).
    Erased-matches-for-K-downwards-closed :
      Erased-matches-for-K 𝟙ᵐ → Erased-matches-for-K 𝟘ᵐ[ ok ]

  private opaque

    -- A lemma used to implement Prodrec-allowed-·ᵐ and some other
    -- lemmas.

    ·ᵐ-lemma :
      (P : Mode → Set a) →
      (∀ ⦃ ok ⦄ → P 𝟙ᵐ → P 𝟘ᵐ[ ok ]) →
      P m → P (m′ ·ᵐ m)
    ·ᵐ-lemma {m′ = 𝟙ᵐ} _ _ =
      idᶠ
    ·ᵐ-lemma {m = 𝟙ᵐ} {m′ = 𝟘ᵐ} _ hyp =
      hyp
    ·ᵐ-lemma {m = 𝟘ᵐ[ ok ]} {m′ = 𝟘ᵐ} P hyp =
      subst (λ m → P 𝟘ᵐ[ ok ] → P m) 𝟘ᵐ-cong idᶠ

  opaque

    -- Prodrec-allowed is closed under application of m′ ·ᵐ_ to the
    -- mode.

    Prodrec-allowed-·ᵐ :
      Prodrec-allowed m r p q → Prodrec-allowed (m′ ·ᵐ m) r p q
    Prodrec-allowed-·ᵐ =
      ·ᵐ-lemma (λ m → Prodrec-allowed m _ _ _)
        Prodrec-allowed-downwards-closed

  opaque

    -- Unitrec-allowed is closed under application of m′ ·ᵐ_ to the
    -- mode.

    Unitrec-allowed-·ᵐ :
      Unitrec-allowed m p q → Unitrec-allowed (m′ ·ᵐ m) p q
    Unitrec-allowed-·ᵐ =
      ·ᵐ-lemma (λ m → Unitrec-allowed m _ _)
        Unitrec-allowed-downwards-closed

  -- Does the strong unit type act as a "sink"?

  Starˢ-sink : Set
  Starˢ-sink = T starˢ-sink

  -- Does the strong unit type not act as a "sink"?
  --
  -- This type is used instead of ¬ Starˢ-sink because "¬ A" does not
  -- work well as the type of an instance argument.

  ¬Starˢ-sink : Set
  ¬Starˢ-sink = T (not starˢ-sink)

  -- The strong unit type is not allowed to both act and not act as a
  -- sink.

  not-sink-and-no-sink : Starˢ-sink → ¬Starˢ-sink → ⊥
  not-sink-and-no-sink sink ¬sink with starˢ-sink
  … | false = sink
  … | true = ¬sink

  -- The strong unit type either acts or does not act as a sink.

  sink-or-no-sink : Starˢ-sink ⊎ ¬Starˢ-sink
  sink-or-no-sink with starˢ-sink
  … | false = inj₂ _
  … | true = inj₁ _

  opaque

    -- Erased-matches-for-J is closed under application of m′ ·ᵐ_ to
    -- the mode.

    Erased-matches-for-J-·ᵐ :
      Erased-matches-for-J m → Erased-matches-for-J (m′ ·ᵐ m)
    Erased-matches-for-J-·ᵐ =
      ·ᵐ-lemma Erased-matches-for-J
        Erased-matches-for-J-downwards-closed

  opaque

    -- Erased-matches-for-K is closed under application of m′ ·ᵐ_ to
    -- the mode.

    Erased-matches-for-K-·ᵐ :
      Erased-matches-for-K m → Erased-matches-for-K (m′ ·ᵐ m)
    Erased-matches-for-K-·ᵐ =
      ·ᵐ-lemma Erased-matches-for-K
        Erased-matches-for-K-downwards-closed
