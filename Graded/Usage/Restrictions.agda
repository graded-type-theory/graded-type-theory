------------------------------------------------------------------------
-- Restrictions on usage derivations
------------------------------------------------------------------------

import Graded.Modality
import Graded.Mode

module Graded.Usage.Restrictions
  {a b} {M : Set a} {Mode : Set b}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Graded.Mode Mode 𝕄)
  (𝐌 : IsMode)
  where

open import Graded.Context 𝕄
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions.Natrec 𝕄
open import Definition.Untyped.NotParametrised

open import Tools.Bool
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
open import Tools.Empty
open import Tools.Unit

open Modality 𝕄
open IsMode 𝐌

private variable
  p q r : M
  m m′  : Mode
  s : Strength
  ⦃ ok ⦄ : T _
  γ δ η : Conₘ _

-- Restrictions on/choices for usage derivations.

record Usage-restrictions : Set (lsuc a ⊔ b) where
  no-eta-equality
  field
    -- Which usage rule for natrec should be used.
    natrec-mode : Natrec-mode

    -- The prodrec constructor's quantities have to satisfy this
    -- predicate (when the mode is 𝟙ᵐ).
    Prodrec-allowed : Mode → (r p q : M) → Set a

    -- Prodrec-allowed is upwards closed in the mode.
    Prodrec-allowed-upwards-closed :
      Prodrec-allowed m r p q → m ≤ᵐ m′ → Prodrec-allowed m′ r p q

    -- The unitrec constructor's quantities have to satisfy this
    -- predicate (when the mode is 𝟙ᵐ).
    Unitrec-allowed : Mode → (p q : M) → Set a

    -- Unitrec-allowed is upwards closed in the mode.
    Unitrec-allowed-upwards-closed :
      Unitrec-allowed m p q → m ≤ᵐ m′ → Unitrec-allowed m′ p q

    -- The emptyrec constructor's quantity has to satisfy this
    -- predicate (when the mode is 𝟙ᵐ).
    Emptyrec-allowed : Mode → M → Set a

    -- Emptyrec-allowed is upwards closed in the mode.
    Emptyrec-allowed-upwards-closed :
      Emptyrec-allowed m p → m ≤ᵐ m′ → Emptyrec-allowed m′ p

    -- Should []-cong be allowed (when the mode is 𝟙ᵐ)?
    []-cong-allowed-mode : Strength → Mode → Set a

    -- []-cong-allowed-mode is upwards closed in the mode.
    []-cong-allowed-mode-upwards-closed :
      []-cong-allowed-mode s m → m ≤ᵐ m′ → []-cong-allowed-mode s m′

    -- Should strong unit types act as "sinks"?
    starˢ-sink : Bool

    -- Is everything erased in the usage rule for Id?
    Id-erased : Set a

    -- Id-erased is decided.
    Id-erased? : Dec Id-erased

    -- What kinds of erased matches are allowed for the J rule (for
    -- the current mode)?
    erased-matches-for-J : Mode → Erased-matches

    -- The usage rules for J are at least as permissive for m′
    -- as for m when m ≤ᵐ m′. (See Graded.Usage.Properties.Jₘ-generalised and
    -- Graded.Usage.Properties.J₀ₘ₁-generalised.)
    erased-matches-for-J-≤ᵉᵐ :
      m ≤ᵐ m′ → erased-matches-for-J m ≤ᵉᵐ erased-matches-for-J m′

    -- What kinds of erased matches are allowed for the K rule (for
    -- the current mode)?
    erased-matches-for-K : Mode → Erased-matches

    -- The usage rules for K are at least as permissive for m′
    -- as for m when m ≤ᵐ m′. (See Graded.Usage.Properties.Kₘ-generalised and
    -- Graded.Usage.Properties.K₀ₘ₁-generalised.)
    erased-matches-for-K-≤ᵉᵐ :
      m ≤ᵐ m′ → erased-matches-for-K m ≤ᵉᵐ erased-matches-for-K m′

  -- Three mutually exclusive types which correspond to each of the
  -- three possibilities for natrec-mode

  Nr-available : Set a
  Nr-available = Natrec-mode-has-nr natrec-mode

  Nr-not-available : Set a
  Nr-not-available = Natrec-mode-no-nr natrec-mode

  Nr-not-available-GLB : Set a
  Nr-not-available-GLB = Natrec-mode-no-nr-glb natrec-mode

  field

    mode-supports-nr :
      ⦃ ok : Nr-available ⦄ →
      Mode-supports-nr ⦃ has-nr = Natrec-mode-Has-nr ok ⦄  𝐌

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

    -- If prodrec is allowed at mode m (for some grade) then it is
    -- also allowed at mode m′ ·ᵐ m.


    Prodrec-allowed-·ᵐ :
      Prodrec-allowed m r p q →
      Prodrec-allowed (m′ ·ᵐ m) r p q
    Prodrec-allowed-·ᵐ ok =
      Prodrec-allowed-upwards-closed ok ·ᵐ-increasingˡ

  opaque

    -- If emptyrec is allowed at mode m (for some grades) then it
    -- is also allowed at mode m′ ·ᵐ m.

    Unitrec-allowed-·ᵐ :
      Unitrec-allowed m p q →
      Unitrec-allowed (m′ ·ᵐ m) p q
    Unitrec-allowed-·ᵐ ok =
      Unitrec-allowed-upwards-closed ok ·ᵐ-increasingˡ

  opaque

    -- If emptyrec is allowed at mode m (for some grade) then it is
    -- also allowed at mode m′ ·ᵐ m.

    Emptyrec-allowed-·ᵐ :
      Emptyrec-allowed m p →
      Emptyrec-allowed (m′ ·ᵐ m) p
    Emptyrec-allowed-·ᵐ ok =
      Emptyrec-allowed-upwards-closed ok ·ᵐ-increasingˡ

  opaque

    []-cong-allowed-mode-·ᵐ :
      []-cong-allowed-mode s m →
      []-cong-allowed-mode s (m′ ·ᵐ m)
    []-cong-allowed-mode-·ᵐ ok =
      []-cong-allowed-mode-upwards-closed ok ·ᵐ-increasingˡ

  opaque

    -- The usage rules for J are at least as permissive for m′ ·ᵐ m as
    -- for m. (See Graded.Usage.Properties.Jₘ-generalised and
    -- Graded.Usage.Properties.J₀ₘ₁-generalised.)

    erased-matches-for-J-≤ᵉᵐ·ᵐ :
      erased-matches-for-J m ≤ᵉᵐ erased-matches-for-J (m′ ·ᵐ m)
    erased-matches-for-J-≤ᵉᵐ·ᵐ =
      erased-matches-for-J-≤ᵉᵐ ·ᵐ-increasingˡ

  opaque

    -- If J has some erased matches for m then it has all
    -- erased matches for m′ ·ᵐ m.

    erased-matches-for-J-all·ᵐ :
      erased-matches-for-J m ≡ all →
      erased-matches-for-J (m′ ·ᵐ m) ≡ all
    erased-matches-for-J-all·ᵐ ≡all =
      ≤ᵉᵐ→≡all→≡all erased-matches-for-J-≤ᵉᵐ·ᵐ ≡all

  opaque

    -- If J has some erased matches for m then it has either all or
    -- some erased matches for m′ ·ᵐ m.

    erased-matches-for-J-some·ᵐ :
      erased-matches-for-J m ≡ some →
      erased-matches-for-J (m′ ·ᵐ m) ≡ all ⊎
      erased-matches-for-J (m′ ·ᵐ m) ≡ some
    erased-matches-for-J-some·ᵐ {m} {m′} ≡some =
      some≤ᵉᵐ→ (subst (_≤ᵉᵐ erased-matches-for-J (m′ ·ᵐ m))
                 ≡some erased-matches-for-J-≤ᵉᵐ·ᵐ)

  private opaque

    -- A lemma used below

    erased-matches-for-JK-not-none·ᵐ :
      ∀ sem em → not-none sem ≤ᵉᵐ em →
      ∃ λ sem′ → em ≡ not-none sem′
    erased-matches-for-JK-not-none·ᵐ all′ none ()
    erased-matches-for-JK-not-none·ᵐ all′ (not-none x) _ = x , refl
    erased-matches-for-JK-not-none·ᵐ some′ none ()
    erased-matches-for-JK-not-none·ᵐ some′ (not-none x) le = x , refl

  opaque

    -- If J has not-none erased matches for m then it has
    -- not-none erased matches for m′ ·ᵐ m.

    erased-matches-for-J-not-none·ᵐ :
      ∀ {sem} →
      erased-matches-for-J m ≡ not-none sem →
      ∃ λ sem′ → erased-matches-for-J (m′ ·ᵐ m) ≡ not-none sem′
    erased-matches-for-J-not-none·ᵐ {m} {m′} ok =
      erased-matches-for-JK-not-none·ᵐ _ _
        (subst (_≤ᵉᵐ erased-matches-for-J (m′ ·ᵐ m)) ok erased-matches-for-J-≤ᵉᵐ·ᵐ)

  opaque

    -- The usage rules for K are at least as permissive for m′ ·ᵐ m as
    -- for m. (See Graded.Usage.Properties.Kₘ-generalised and
    -- Graded.Usage.Properties.K₀ₘ₁-generalised.)

    erased-matches-for-K-≤ᵉᵐ·ᵐ :
      erased-matches-for-K m ≤ᵉᵐ erased-matches-for-K (m′ ·ᵐ m)
    erased-matches-for-K-≤ᵉᵐ·ᵐ =
      erased-matches-for-K-≤ᵉᵐ ·ᵐ-increasingˡ

  opaque


    -- If K has some erased matches for m then it has all
    -- erased matches for m′ ·ᵐ m.

    erased-matches-for-K-all·ᵐ :
      erased-matches-for-K m ≡ all →
      erased-matches-for-K (m′ ·ᵐ m) ≡ all
    erased-matches-for-K-all·ᵐ ≡all =
      ≤ᵉᵐ→≡all→≡all erased-matches-for-K-≤ᵉᵐ·ᵐ ≡all

  opaque

    -- If K has some erased matches for m then it has either all or
    -- some erased matches for m′ ·ᵐ m.

    erased-matches-for-K-some·ᵐ :
      erased-matches-for-K m ≡ some →
      erased-matches-for-K (m′ ·ᵐ m) ≡ all ⊎
      erased-matches-for-K (m′ ·ᵐ m) ≡ some
    erased-matches-for-K-some·ᵐ {m} {m′} ≡some =
      some≤ᵉᵐ→ (subst (_≤ᵉᵐ erased-matches-for-K (m′ ·ᵐ m))
                 ≡some erased-matches-for-K-≤ᵉᵐ·ᵐ)

  opaque

    -- If K has not-none erased matches for m then it has
    -- not-none erased matches for m′ ·ᵐ m.

    erased-matches-for-K-not-none·ᵐ :
      ∀ {sem} →
      erased-matches-for-K m ≡ not-none sem →
      ∃ λ sem′ → erased-matches-for-K (m′ ·ᵐ m) ≡ not-none sem′
    erased-matches-for-K-not-none·ᵐ {m} {m′} ok =
      erased-matches-for-JK-not-none·ᵐ _ _
        (subst (_≤ᵉᵐ erased-matches-for-K (m′ ·ᵐ m)) ok erased-matches-for-K-≤ᵉᵐ·ᵐ)

  opaque

    -- Multiplication by a mode distributes over nrᶜ

    ⌜⌝-·ᶜ-nrᶜ :
      ⦃ ok : Nr-available ⦄ →
      ⌜ m ⌝ ·ᶜ nrᶜ ⦃ Natrec-mode-Has-nr ok ⦄ p r γ δ η ≈ᶜ
      nrᶜ ⦃ Natrec-mode-Has-nr ok ⦄ p r (⌜ m ⌝ ·ᶜ γ) (⌜ m ⌝ ·ᶜ δ) (⌜ m ⌝ ·ᶜ η)
    ⌜⌝-·ᶜ-nrᶜ {γ = ε} {(ε)} {(ε)} = ε
    ⌜⌝-·ᶜ-nrᶜ {γ = _ ∙ _} {_ ∙ _} {_ ∙ _} ⦃ ok ⦄ =
      ⌜⌝-·ᶜ-nrᶜ ∙ Mode-supports-nr.⌜⌝-·-nr ⦃ has-nr = Natrec-mode-Has-nr ok ⦄ mode-supports-nr

  opaque

    -- A variant of ⌞nr⌟-decreasing₁

    ⌞⌟·ᵐ⌞nr⌟₁ :
      ⦃ ok : Nr-available ⦄ {z s n : M} →
      ⌞ z ⌟ ·ᵐ ⌞ Has-nr.nr (Natrec-mode-Has-nr ok) p r z s n ⌟ ≡ ⌞ z ⌟
    ⌞⌟·ᵐ⌞nr⌟₁ ⦃ ok ⦄ =
      sym (Mode-supports-nr.⌞nr⌟-decreasing₁ ⦃ has-nr = Natrec-mode-Has-nr ok ⦄ mode-supports-nr)

  opaque

    -- A variant of ⌞nr⌟-decreasing₃

    ⌞⌟·ᵐ⌞nr⌟₃ :
      ⦃ ok : Nr-available ⦄ {z s n : M} →
      ⌞ n ⌟ ·ᵐ ⌞ Has-nr.nr (Natrec-mode-Has-nr ok) p r z s n ⌟ ≡ ⌞ n ⌟
    ⌞⌟·ᵐ⌞nr⌟₃ ⦃ ok ⦄ =
      sym (Mode-supports-nr.⌞nr⌟-decreasing₃ ⦃ has-nr = Natrec-mode-Has-nr ok ⦄ mode-supports-nr)
