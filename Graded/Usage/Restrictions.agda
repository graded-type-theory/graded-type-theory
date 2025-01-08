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
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions.Natrec 𝕄
open import Definition.Untyped.NotParametrised

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
open import Tools.Empty

open Modality 𝕄

private variable
  p q r : M
  m m′  : Mode
  s : Strength
  ⦃ ok ⦄ : T _

-- Restrictions on/choices for usage derivations.

record Usage-restrictions : Set (lsuc a) where
  no-eta-equality
  field
    -- Which usage rule for natrec should be used.
    natrec-mode : Natrec-mode

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

    -- The emptyrec constructor's quantity has to satisfy this
    -- predicate (for the current mode).
    Emptyrec-allowed : Mode → M → Set a

    -- Emptyrec-allowed is downwards closed in the mode (if 𝟙ᵐ is seen
    -- as a largest element).
    Emptyrec-allowed-downwards-closed :
      Emptyrec-allowed 𝟙ᵐ p → Emptyrec-allowed 𝟘ᵐ[ ok ] p

    -- Should []-cong be allowed for the current mode?
    []-cong-allowed-mode : Strength → Mode → Set a

    -- []-cong-allowed is downwards closed in the mode (if 𝟙ᵐ is seen
    -- as a largest element).
    []-cong-allowed-mode-downwards-closed :
      []-cong-allowed-mode s 𝟙ᵐ → []-cong-allowed-mode s 𝟘ᵐ[ ok ]

    -- Should strong unit types act as "sinks"?
    starˢ-sink : Bool

    -- Are most things erased in the usage rule for Id?
    Id-erased : Set a

    -- Id-erased is decided.
    Id-erased? : Dec Id-erased

    -- What kinds of erased matches are allowed for the J rule (for
    -- the current mode)?
    erased-matches-for-J : Mode → Erased-matches

    -- The usage rules for J are at least as permissive for 𝟘ᵐ[ ok ]
    -- as for 𝟙ᵐ. (See Graded.Usage.Properties.Jₘ-generalised and
    -- Graded.Usage.Properties.J₀ₘ₁-generalised.)
    erased-matches-for-J-≤ᵉᵐ :
      erased-matches-for-J 𝟙ᵐ ≤ᵉᵐ erased-matches-for-J 𝟘ᵐ[ ok ]

    -- What kinds of erased matches are allowed for the K rule (for
    -- the current mode)?
    erased-matches-for-K : Mode → Erased-matches

    -- The usage rules for K are at least as permissive for 𝟘ᵐ[ ok ]
    -- as for 𝟙ᵐ. (See Graded.Usage.Properties.Kₘ-generalised and
    -- Graded.Usage.Properties.K₀ₘ₁-generalised.)
    erased-matches-for-K-≤ᵉᵐ :
      erased-matches-for-K 𝟙ᵐ ≤ᵉᵐ erased-matches-for-K 𝟘ᵐ[ ok ]

  -- Three mutually exclusive types which corresponding to each of the
  -- three poossibilities for natrec-mode

  Nr-available : Set a
  Nr-available = Natrec-mode-has-nr natrec-mode

  Nr-not-available : Set a
  Nr-not-available = Natrec-mode-no-nr natrec-mode

  Nr-not-available-GLB : Set a
  Nr-not-available-GLB = Natrec-mode-no-nr-glb natrec-mode

  private opaque

    -- Some lemmas used below.

    ·ᵐ-lemma₁ : ∀ {ℓ} →
      (P : Mode → Set ℓ) →
      (∀ ⦃ ok ⦄ → P 𝟙ᵐ → P 𝟘ᵐ[ ok ]) →
      P m → P (m′ ·ᵐ m)
    ·ᵐ-lemma₁ {m′ = 𝟙ᵐ} _ _ =
      idᶠ
    ·ᵐ-lemma₁ {m = 𝟙ᵐ} {m′ = 𝟘ᵐ} _ hyp =
      hyp
    ·ᵐ-lemma₁ {m = 𝟘ᵐ[ ok ]} {m′ = 𝟘ᵐ} P hyp =
      subst (λ m → P 𝟘ᵐ[ ok ] → P m) 𝟘ᵐ-cong idᶠ

    ·ᵐ-lemma₂ :
      (f : Mode → Erased-matches) →
      (∀ ⦃ ok ⦄ → f 𝟙ᵐ ≤ᵉᵐ f 𝟘ᵐ[ ok ]) →
      f m ≤ᵉᵐ f (m′ ·ᵐ m)
    ·ᵐ-lemma₂          {m′ = 𝟙ᵐ} _ _   = ≤ᵉᵐ-reflexive
    ·ᵐ-lemma₂ {m = 𝟙ᵐ} {m′ = 𝟘ᵐ} _ hyp = hyp
    ·ᵐ-lemma₂ {m = 𝟘ᵐ} {m′ = 𝟘ᵐ} f _   =
      subst (_≤ᵉᵐ_ _) (cong f 𝟘ᵐ-cong) ≤ᵉᵐ-reflexive

  opaque

    -- Prodrec-allowed is closed under application of m′ ·ᵐ_ to the
    -- mode.

    Prodrec-allowed-·ᵐ :
      Prodrec-allowed m r p q → Prodrec-allowed (m′ ·ᵐ m) r p q
    Prodrec-allowed-·ᵐ =
      ·ᵐ-lemma₁ (λ m → Prodrec-allowed m _ _ _)
        Prodrec-allowed-downwards-closed

  opaque

    -- Unitrec-allowed is closed under application of m′ ·ᵐ_ to the
    -- mode.

    Unitrec-allowed-·ᵐ :
      Unitrec-allowed m p q → Unitrec-allowed (m′ ·ᵐ m) p q
    Unitrec-allowed-·ᵐ =
      ·ᵐ-lemma₁ (λ m → Unitrec-allowed m _ _)
        Unitrec-allowed-downwards-closed

  opaque

    -- Emptyrec-allowed is closed under application of m′ ·ᵐ_ to the
    -- mode.

    Emptyrec-allowed-·ᵐ :
      Emptyrec-allowed m p → Emptyrec-allowed (m′ ·ᵐ m) p
    Emptyrec-allowed-·ᵐ =
      ·ᵐ-lemma₁ (λ m → Emptyrec-allowed m _)
        Emptyrec-allowed-downwards-closed

  opaque

    -- []-cong-allowed is closed under application of m′ ·ᵐ_ to the
    -- mode.

    []-cong-allowed-·ᵐ :
      []-cong-allowed-mode s m → []-cong-allowed-mode s (m′ ·ᵐ m)
    []-cong-allowed-·ᵐ =
      ·ᵐ-lemma₁ (λ m → []-cong-allowed-mode _ m)
        []-cong-allowed-mode-downwards-closed

  -- Do strong unit types act as "sinks"?

  Starˢ-sink : Set
  Starˢ-sink = T starˢ-sink

  -- Strong unit types are not allowed to both act and not act as
  -- sinks.

  not-sink-and-no-sink : Starˢ-sink → ¬ Starˢ-sink → ⊥
  not-sink-and-no-sink sink ¬sink with starˢ-sink
  … | false = sink
  … | true = ¬sink _

  -- Strong unit types either act or do not act as sinks.

  sink-or-no-sink : Starˢ-sink ⊎ ¬ Starˢ-sink
  sink-or-no-sink with starˢ-sink
  … | false = inj₂ idᶠ
  … | true = inj₁ _

  opaque

    -- The usage rules for J are at least as permissive for m′ ·ᵐ m as
    -- for m. (See Graded.Usage.Properties.Jₘ-generalised and
    -- Graded.Usage.Properties.J₀ₘ₁-generalised.)

    erased-matches-for-J-≤ᵉᵐ·ᵐ :
      erased-matches-for-J m ≤ᵉᵐ erased-matches-for-J (m′ ·ᵐ m)
    erased-matches-for-J-≤ᵉᵐ·ᵐ =
      ·ᵐ-lemma₂ erased-matches-for-J erased-matches-for-J-≤ᵉᵐ

  opaque

    -- The usage rules for K are at least as permissive for m′ ·ᵐ m as
    -- for m. (See Graded.Usage.Properties.Kₘ-generalised and
    -- Graded.Usage.Properties.K₀ₘ₁-generalised.)

    erased-matches-for-K-≤ᵉᵐ·ᵐ :
      erased-matches-for-K m ≤ᵉᵐ erased-matches-for-K (m′ ·ᵐ m)
    erased-matches-for-K-≤ᵉᵐ·ᵐ =
      ·ᵐ-lemma₂ erased-matches-for-K erased-matches-for-K-≤ᵉᵐ
