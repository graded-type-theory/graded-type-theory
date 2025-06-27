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
open import Tools.Unit

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
    -- predicate (when the mode is 𝟙ᵐ).
    Prodrec-allowed-𝟙ᵐ : (r p q : M) → Set a

    -- The unitrec constructor's quantities have to satisfy this
    -- predicate (when the mode is 𝟙ᵐ).
    Unitrec-allowed-𝟙ᵐ : (p q : M) → Set a

    -- The emptyrec constructor's quantity has to satisfy this
    -- predicate (when the mode is 𝟙ᵐ).
    Emptyrec-allowed-𝟙ᵐ : M → Set a

    -- Should []-cong be allowed (when the mode is 𝟙ᵐ)?
    []-cong-allowed-mode-𝟙ᵐ : Strength → Set a

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

  -- Three mutually exclusive types which correspond to each of the
  -- three possibilities for natrec-mode

  Nr-available : Set a
  Nr-available = Natrec-mode-has-nr natrec-mode

  Nr-not-available : Set a
  Nr-not-available = Natrec-mode-no-nr natrec-mode

  Nr-not-available-GLB : Set a
  Nr-not-available-GLB = Natrec-mode-no-nr-glb natrec-mode

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

  private opaque

    -- A lemma used below.

    ·ᵐ-lemma :
      (f : Mode → Erased-matches) →
      (∀ ⦃ ok ⦄ → f 𝟙ᵐ ≤ᵉᵐ f 𝟘ᵐ[ ok ]) →
      f m ≤ᵉᵐ f (m′ ·ᵐ m)
    ·ᵐ-lemma          {m′ = 𝟙ᵐ} _ _   = ≤ᵉᵐ-reflexive
    ·ᵐ-lemma {m = 𝟙ᵐ} {m′ = 𝟘ᵐ} _ hyp = hyp
    ·ᵐ-lemma {m = 𝟘ᵐ} {m′ = 𝟘ᵐ} f _   =
      subst (_≤ᵉᵐ_ _) (cong f 𝟘ᵐ-cong) ≤ᵉᵐ-reflexive

  opaque

    -- The usage rules for J are at least as permissive for m′ ·ᵐ m as
    -- for m. (See Graded.Usage.Properties.Jₘ-generalised and
    -- Graded.Usage.Properties.J₀ₘ₁-generalised.)

    erased-matches-for-J-≤ᵉᵐ·ᵐ :
      erased-matches-for-J m ≤ᵉᵐ erased-matches-for-J (m′ ·ᵐ m)
    erased-matches-for-J-≤ᵉᵐ·ᵐ =
      ·ᵐ-lemma erased-matches-for-J erased-matches-for-J-≤ᵉᵐ

  opaque

    -- The usage rules for K are at least as permissive for m′ ·ᵐ m as
    -- for m. (See Graded.Usage.Properties.Kₘ-generalised and
    -- Graded.Usage.Properties.K₀ₘ₁-generalised.)

    erased-matches-for-K-≤ᵉᵐ·ᵐ :
      erased-matches-for-K m ≤ᵉᵐ erased-matches-for-K (m′ ·ᵐ m)
    erased-matches-for-K-≤ᵉᵐ·ᵐ =
      ·ᵐ-lemma erased-matches-for-K erased-matches-for-K-≤ᵉᵐ

  ----------------------------------------------------------------------
  -- Variants of Prodrec-allowed-𝟙ᵐ, Unitrec-allowed-𝟙ᵐ,
  -- Emptyrec-allowed-𝟙ᵐ and []-cong-allowed-mode-𝟙ᵐ

  -- The prodrec constructor's quantities have to satisfy this
  -- predicate (for the current mode).

  Prodrec-allowed : Mode → (r p q : M) → Set a
  Prodrec-allowed 𝟙ᵐ = Prodrec-allowed-𝟙ᵐ
  Prodrec-allowed 𝟘ᵐ = λ _ _ _ → Lift _ ⊤

  -- The unitrec constructor's quantities have to satisfy this
  -- predicate (for the current mode).

  Unitrec-allowed : Mode → (p q : M) → Set a
  Unitrec-allowed 𝟙ᵐ = Unitrec-allowed-𝟙ᵐ
  Unitrec-allowed 𝟘ᵐ = λ _ _ → Lift _ ⊤

  -- The emptyrec constructor's quantity has to satisfy this
  -- predicate (for the current mode).

  Emptyrec-allowed : Mode → M → Set a
  Emptyrec-allowed 𝟙ᵐ = Emptyrec-allowed-𝟙ᵐ
  Emptyrec-allowed 𝟘ᵐ = λ _ → Lift _ ⊤

  -- Should []-cong be allowed for the current mode?

  []-cong-allowed-mode : Strength → Mode → Set a
  []-cong-allowed-mode s 𝟙ᵐ = []-cong-allowed-mode-𝟙ᵐ s
  []-cong-allowed-mode _ 𝟘ᵐ = Lift _ ⊤
