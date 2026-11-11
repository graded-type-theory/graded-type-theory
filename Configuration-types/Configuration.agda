------------------------------------------------------------------------
-- Functions that construct configurations
------------------------------------------------------------------------

import Graded.Modality
import Graded.Mode

module Configuration-types.Configuration
  {a a′} {M : Set a} {Mode : Set a′}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Graded.Mode Mode 𝕄)
  (𝐌 : IsMode)
  where

open Modality 𝕄
open IsMode 𝐌

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Relation as Dec
open import Tools.Sum
open import Tools.Unit

open import Configuration-types
open import Configuration-types.Erased-matches
open import Configuration-types.Natrec 𝕄
open import Configuration-types.Omega 𝕄
import Configuration-types.Type-configuration 𝕄 as TC

import Definition.Typechecking.Decidable.Assumptions as TD
open import Definition.Untyped M using (𝕤)
open import Definition.Untyped.Properties M using (decStrength)

open import Graded.Modality.Properties 𝕄
import Graded.Usage.Decidable.Assumptions as UD

private variable
  b₁ b₂ b₃ b₄ : Bool
  C           : Configuration _
  nm          : Natrec-mode

------------------------------------------------------------------------
-- Functions that construct configurations

-- No type restrictions (see TC.no-type-restrictions, which takes the
-- first two booleans; quotients are allowed if and only if the mode
-- structure is non-trivial), no restrictions for prodrec, unitrec or
-- emptyrec, all erased matches are allowed for J and K, the natrec
-- mode can be anything, Id-erased is inhabited if the third boolean
-- is true, starˢ is treated as a sink if the fourth boolean is true,
-- and Qrec-motive-erased is inhabited if the fifth boolean is true.
-- Usage rules that require the use of ω are not allowed.

no-restrictions :
  (nm : Natrec-mode) →
  (⦃ has-nr : Natrec-mode-has-nr nm ⦄ →
     Mode-supports-nr ⦃ Natrec-mode-Has-nr has-nr ⦄ 𝐌) →
  (_ _ _ _ _ : Bool) → Configuration 𝐌
no-restrictions nm nr-ok k er erased sink qrec = λ where
    .Configuration.TC →
      let TC = TC.no-type-restrictions k er in
      record TC
        { TC⁻ = record (Type-configuration.TC⁻ TC)
            { Quot-allowed = ¬ Trivialᵐ′ }
        ; []-cong→Erased = λ {s = s} →
            Type-configuration.[]-cong→Erased TC {s = s}
        ; []-cong→¬Trivial = λ {s = s} →
            Type-configuration.[]-cong→¬Trivial TC {s = s}
        }
    .usage-rules-with-ω                   → without-ω
    .Emptyrec-allowed                     → λ _ _ → Lift _ ⊤
    .Emptyrec-allowed-upwards-closed      → λ _ _ → _
    .Unitrec-allowed                      → λ _ _ _ → Lift _ ⊤
    .Unitrec-allowed-upwards-closed       → λ _ _ → _
    .starˢ-sink                           → sink
    .Prodrec-allowed                      → λ _ _ _ _ → Lift _ ⊤
    .Prodrec-allowed-upwards-closed       → λ _ _ → _
    .natrec-mode                          → nm
    .mode-supports-nr                     → nr-ok
    .Id-erased                            → Lift _ (T erased)
    .Id-erased?                           → Dec.map lift Lift.lower $
                                            T? erased
    .erased-matches-for-JK                → λ _ _ → all
    .erased-matches-for-JK-≤ᵉᵐ            → _
    .erased-matches-for-JK-supports-ω     → λ ()
    .[]-cong-allowed-mode                 → λ _ _ → ¬ Trivial
    .[]-cong-allowed-mode→[]-cong-allowed → idᶠ
    .[]-cong-allowed-mode-upwards-closed  →
      λ non-trivial _ → non-trivial
    .Quot-allowed→¬Trivialᵐ →
      _∘→ Trivialᵐ′⇔Trivialᵐ .proj₂
    .Qrec-motive-erased →
      Lift _ (T qrec)
    .Qrec-motive-erased? →
      Dec.map lift Lift.lower (T? qrec)
  where
  open Configuration

-- The function enables the usage rule natrecₘ (for the given Has-nr
-- value).

nr-available :
  (has-nr : Has-nr 𝕄) →
  Mode-supports-nr ⦃ has-nr ⦄ 𝐌 →
  Configuration 𝐌 → Configuration 𝐌
nr-available has-nr nr-ok C = record C
  { natrec-mode      = Nr ⦃ has-nr ⦄
  ; mode-supports-nr = λ { ⦃ (Nr) ⦄ → nr-ok}
  }

-- The function enables the usage rule natrec-no-nr-glbₘ.

nr-not-available-glb :
  Has-well-behaved-GLBs 𝕄 →
  Configuration 𝐌 → Configuration 𝐌
nr-not-available-glb ok C =
  record C
    { natrec-mode = No-nr-glb ⦃ ok ⦄
    ; mode-supports-nr = λ { ⦃ () ⦄ }
    }

-- The function adds the restriction that the two quantities on a Π-
-- or Σ-type have to be equal.

equal-binder-quantities : Configuration 𝐌 → Configuration 𝐌
equal-binder-quantities C =
  record C { TC = TC.equal-binder-quantities TC }
  where
  open Configuration C

-- The function adds the restriction that the second quantities
-- associated with Π- and Σ-types are equal to 𝟘.

second-ΠΣ-quantities-𝟘 : Configuration 𝐌 → Configuration 𝐌
second-ΠΣ-quantities-𝟘 C =
  record C { TC = TC.second-ΠΣ-quantities-𝟘 TC }
  where
  open Configuration C

-- The function second-ΠΣ-quantities-𝟘-or-ω 𝕄 adds the restriction
-- that if the first quantity associated with a Π- or Σ-type is the ω
-- grade of 𝕄, then the second quantity is also ω, and if the first
-- quantity is not ω, then the second quantity is the 𝟘 of 𝕄.

second-ΠΣ-quantities-𝟘-or-ω :
  ⦃ ok : Has-omega 𝕄 ⦄ →
  Configuration 𝐌 → Configuration 𝐌
second-ΠΣ-quantities-𝟘-or-ω C =
  record C { TC = TC.second-ΠΣ-quantities-𝟘-or-ω TC }
  where
  open Configuration C

-- The function strong-types-restricted adds the following
-- restrictions:
--
-- * Strong unit types are not allowed.
-- * If strong Σ-types are allowed for p and q, then p is 𝟙.
-- * []-cong is not allowed for 𝕤.

strong-types-restricted :
  Configuration 𝐌 → Configuration 𝐌
strong-types-restricted C = record C
  { TC =
      TC.strong-types-restricted TC
  ; []-cong-allowed-mode = λ s m →
      []-cong-allowed-mode s m × s ≢ 𝕤
  ; []-cong-allowed-mode→[]-cong-allowed =
      Σ.map []-cong-allowed-mode→[]-cong-allowed idᶠ
  ; []-cong-allowed-mode-upwards-closed = flip λ m≤m′ →
      Σ.map (flip []-cong-allowed-mode-upwards-closed m≤m′) idᶠ
  }
  where
  open Configuration C

-- The function no-strong-types adds the following restrictions:
--
-- * Strong unit types are not allowed.
-- * Strong Σ-types are not allowed.
-- * []-cong is not allowed for 𝕤.

no-strong-types :
  Configuration 𝐌 → Configuration 𝐌
no-strong-types C = record C
  { TC =
      TC.no-strong-types TC
  ; []-cong-allowed-mode = λ s m →
      []-cong-allowed-mode s m × s ≢ 𝕤
  ; []-cong-allowed-mode→[]-cong-allowed =
      Σ.map []-cong-allowed-mode→[]-cong-allowed idᶠ
  ; []-cong-allowed-mode-upwards-closed = flip λ m≤m′ →
      Σ.map (flip []-cong-allowed-mode-upwards-closed m≤m′) idᶠ
  }
  where
  open Configuration C

-- The function _with-η-for-Unitʷ enables η-equality for weak unit
-- types.

_with-η-for-Unitʷ : Configuration 𝐌 → Configuration 𝐌
C with-η-for-Unitʷ = record C { TC = TC TC.with-η-for-Unitʷ }
  where
  open Configuration C

-- The function with-equality-reflection enables support for equality
-- reflection, and disables support for opaque definitions.

with-equality-reflection : Configuration 𝐌 → Configuration 𝐌
with-equality-reflection C =
  record C { TC = TC.with-equality-reflection TC }
  where
  open Configuration C

-- The function no-quotients adds the restriction that quotient types
-- are not allowed.

no-quotients : Configuration 𝐌 → Configuration 𝐌
no-quotients C = record C
  { TC =
      TC.no-quotients (C .Configuration.TC)
  ; Quot-allowed→¬Trivialᵐ =
      λ ()
  }
  where
  open Configuration C

------------------------------------------------------------------------
-- Some lemmas related to UD.Assumptions

opaque

  -- If grade equality is decidable and the modality supports usage
  -- inference for a given natrec-mode nm, then UD.Assumptions holds
  -- for certain instances of no-restrictions.

  Assumptions-no-restrictions :
    {nr : ⦃ has-nr : Natrec-mode-has-nr nm ⦄ →
          Mode-supports-nr ⦃ Natrec-mode-Has-nr has-nr ⦄ 𝐌}
    ⦃ ok : Natrec-mode-supports-usage-inference nm ⦄ →
    Decidable (_≡_ {A = M}) →
    UD.Assumptions (no-restrictions nm nr b₁ false b₂ false b₃)
  Assumptions-no-restrictions {b₁} dec = λ where
      .assumptions → λ where
        ._≟_                              → dec
        .Omega-plus-allowed?              → yes _
        .Unit-allowed? _                  → yes _
        .ΠΣ-allowed? _ _ _                → yes _
        .[]-cong-allowed? _               → ¬? trivial?
        .Quot-allowed?                    → ¬? Trivialᵐ′?
        .no-equality-reflection (lift ())
        .K-allowed?                       →
          case singleton b₁ of λ where
            (true  , refl) → yes _
            (false , refl) → no (λ ())
      .Prodrec-allowed? _ _ _ _  → yes _
      .Unitrec-allowed? _ _ _    → yes _
      .Emptyrec-allowed? _ _     → yes _
      .[]-cong-allowed-mode? _ _ → ¬? trivial?
      .no-sink-or-≤𝟘             → inj₁ idᶠ
    where
    open TD.Assumptions
    open UD.Assumptions

opaque

  -- The function second-ΠΣ-quantities-𝟘-or-ω preserves
  -- UD.Assumptions.

  Assumptions-second-ΠΣ-quantities-𝟘-or-ω :
    ⦃ ok : Has-omega 𝕄 ⦄ →
    UD.Assumptions C →
    UD.Assumptions (second-ΠΣ-quantities-𝟘-or-ω C)
  Assumptions-second-ΠΣ-quantities-𝟘-or-ω as = λ where
      .assumptions →
        TC.Assumptions-second-ΠΣ-quantities-𝟘-or-ω A.assumptions
      .Prodrec-allowed?      → A.Prodrec-allowed?
      .Unitrec-allowed?      → A.Unitrec-allowed?
      .Emptyrec-allowed?     → A.Emptyrec-allowed?
      .[]-cong-allowed-mode? → A.[]-cong-allowed-mode?
      .no-sink-or-≤𝟘         → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions as
    open UD.Assumptions

opaque

  -- The function strong-types-restricted preserves
  -- UD.Assumptions.

  Assumptions-strong-types-restricted :
    UD.Assumptions C →
    UD.Assumptions (strong-types-restricted C)
  Assumptions-strong-types-restricted as = λ where
      .assumptions           → TC.Assumptions-strong-types-restricted
                                 A.assumptions
      .Prodrec-allowed?      → A.Prodrec-allowed?
      .Unitrec-allowed?      → A.Unitrec-allowed?
      .Emptyrec-allowed?     → A.Emptyrec-allowed?
      .[]-cong-allowed-mode? → λ s m →
                                 A.[]-cong-allowed-mode? s m
                                   ×-dec
                                 ¬? (decStrength s 𝕤)
      .no-sink-or-≤𝟘         → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions as
    open UD.Assumptions

opaque

  -- The function no-strong-types preserves UD.Assumptions.

  Assumptions-no-strong-types :
    UD.Assumptions C →
    UD.Assumptions (no-strong-types C)
  Assumptions-no-strong-types as = λ where
      .assumptions           → TC.Assumptions-no-strong-types
                                 A.assumptions
      .Prodrec-allowed?      → A.Prodrec-allowed?
      .Unitrec-allowed?      → A.Unitrec-allowed?
      .Emptyrec-allowed?     → A.Emptyrec-allowed?
      .[]-cong-allowed-mode? → λ s m →
                                 A.[]-cong-allowed-mode? s m
                                   ×-dec
                                 ¬? (decStrength s 𝕤)
      .no-sink-or-≤𝟘         → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions as
    open UD.Assumptions

opaque

  -- The function no-quotients preserves UD.Assumptions.

  Assumptions-no-quotients :
    UD.Assumptions C →
    UD.Assumptions (no-quotients C)
  Assumptions-no-quotients as = λ where
      .assumptions           → TC.Assumptions-no-quotients A.assumptions
      .Prodrec-allowed?      → A.Prodrec-allowed?
      .Unitrec-allowed?      → A.Unitrec-allowed?
      .Emptyrec-allowed?     → A.Emptyrec-allowed?
      .[]-cong-allowed-mode? → A.[]-cong-allowed-mode?
      .no-sink-or-≤𝟘         → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions as
    open UD.Assumptions
