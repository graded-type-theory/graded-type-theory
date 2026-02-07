------------------------------------------------------------------------
-- Definitions related to type and usage restrictions for the Zero-one
-- mode instance
------------------------------------------------------------------------

import Graded.Modality
import Graded.Mode.Instances.Zero-one.Variant

module Graded.Restrictions.Zero-one
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (open Graded.Mode.Instances.Zero-one.Variant 𝕄)
  (variant : Mode-variant)
  where

open Modality 𝕄

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Relation as Dec
open import Tools.Sum
open import Tools.Unit

open import Graded.Modality.Properties 𝕄
open import Graded.Mode.Instances.Zero-one variant hiding (_≟_)
import Graded.Usage.Decidable.Assumptions as UD
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions 𝕄 Zero-one-isMode
open import Graded.Usage.Restrictions.Natrec 𝕄

import Definition.Typechecking.Decidable.Assumptions as TD
open import Definition.Typed.Restrictions 𝕄
open import Definition.Typed.Variant
open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

open import Graded.Restrictions 𝕄 Zero-one-isMode public
  hiding (nr-available-UR; no-usage-restrictions;
          No-erased-matches; No-erased-matches′)
import Graded.Restrictions 𝕄 Zero-one-isMode as GR

private variable
  TR : Type-restrictions
  UR : Usage-restrictions
  b  : Bool
  ok : T _
  s  : Strength
  nm : Natrec-mode

------------------------------------------------------------------------
-- A lemma used below

opaque

  -- If a reflexive property holds for modes 𝟙ᵐ and 𝟘ᵐ? then it holds
  -- for all modes m ≤ᵐ m′

  𝟙ᵐ𝟘ᵐ→≤ᵐ :
    (P : (m m′ : Mode) → Set) →
    (∀ {ok} → P 𝟙ᵐ 𝟘ᵐ[ ok ]) →
    (∀ {m} → P m m) →
    ∀ {m m′} → m ≤ᵐ m′ → P m m′
  𝟙ᵐ𝟘ᵐ→≤ᵐ P ok₁₀ okᵣ {(𝟘ᵐ)} {(𝟘ᵐ)} m≤ᵐm′ = subst (P _) 𝟘ᵐ-cong okᵣ
  𝟙ᵐ𝟘ᵐ→≤ᵐ P ok₁₀ okᵣ {(𝟘ᵐ)} {(𝟙ᵐ)} ()
  𝟙ᵐ𝟘ᵐ→≤ᵐ P ok₁₀ okᵣ {(𝟙ᵐ)} {(𝟘ᵐ[ ok ])} m≤ᵐm′ = subst (P _) 𝟘ᵐ-cong (ok₁₀ {ok})
  𝟙ᵐ𝟘ᵐ→≤ᵐ P ok₁₀ okᵣ {(𝟙ᵐ)} {(𝟙ᵐ)} m≤ᵐm′ = okᵣ

------------------------------------------------------------------------
-- Functions that construct Usage-restrictions

-- No restrictions for prodrec, unitrec or emptyrec, all erased
-- matches are allowed for J and K, the natrec mode can be anything,
-- Id-erased is inhabited if the first boolean is true, and starˢ
-- is treated as a sink if the second boolean is true.

no-usage-restrictions :
  (nm : Natrec-mode) →
  Bool → Bool → Usage-restrictions
no-usage-restrictions nm =
  GR.no-usage-restrictions nm
    (λ { ⦃ (Nr) ⦄ → Zero-one-supports-nr ⦃ Natrec-mode-Has-nr Nr ⦄ })

-- A function used to define not-all-erased-matches-JK.

not-all-for-𝟙ᵐ : (Mode → Erased-matches) → Mode → Erased-matches
not-all-for-𝟙ᵐ f 𝟘ᵐ = f 𝟘ᵐ
not-all-for-𝟙ᵐ f 𝟙ᵐ with f 𝟙ᵐ
… | all = some
… | em  = em

-- The function adds the restriction that, for the mode 𝟙ᵐ, "all"
-- erased matches are not allowed for J and K.

not-all-erased-matches-JK : Usage-restrictions → Usage-restrictions
not-all-erased-matches-JK UR = record UR
  { erased-matches-for-J =
      not-all-for-𝟙ᵐ erased-matches-for-J
  ; erased-matches-for-J-≤ᵉᵐ =
     𝟙ᵐ𝟘ᵐ→≤ᵐ (λ m m′ → not-all-for-𝟙ᵐ erased-matches-for-J m ≤ᵉᵐ not-all-for-𝟙ᵐ erased-matches-for-J m′)
       (not-all-for-𝟙ᵐ-≤ᵉᵐ erased-matches-for-J (erased-matches-for-J-≤ᵉᵐ 𝟙ᵐ≤))
       ≤ᵉᵐ-reflexive
  ; erased-matches-for-K =
      not-all-for-𝟙ᵐ erased-matches-for-K
  ; erased-matches-for-K-≤ᵉᵐ =
    𝟙ᵐ𝟘ᵐ→≤ᵐ (λ m m′ → not-all-for-𝟙ᵐ erased-matches-for-K m ≤ᵉᵐ not-all-for-𝟙ᵐ erased-matches-for-K m′)
      (not-all-for-𝟙ᵐ-≤ᵉᵐ erased-matches-for-K (erased-matches-for-K-≤ᵉᵐ 𝟙ᵐ≤))
      ≤ᵉᵐ-reflexive
  }
  where
  open Usage-restrictions UR

  opaque

    not-all-for-𝟙ᵐ-≤ᵉᵐ :
      (f : Mode → Erased-matches) →
      f 𝟙ᵐ ≤ᵉᵐ f 𝟘ᵐ[ ok ] →
      not-all-for-𝟙ᵐ f 𝟙ᵐ ≤ᵉᵐ not-all-for-𝟙ᵐ f 𝟘ᵐ[ ok ]
    not-all-for-𝟙ᵐ-≤ᵉᵐ f f-≤ᵉᵐ with f 𝟙ᵐ
    … | all  = ≤ᵉᵐ-transitive _ f-≤ᵉᵐ
    … | some = f-≤ᵉᵐ
    … | none = f-≤ᵉᵐ

-- The function adds the restriction that certain erased matches are
-- not allowed for the mode 𝟙ᵐ. No restriction is added for emptyrec
-- or unitrec. For prodrec the added restriction only applies to
-- non-trivial modalities.

only-some-erased-matches : Usage-restrictions → Usage-restrictions
only-some-erased-matches UR = record UR
  { Prodrec-allowed = λ m r p q →
      Prodrec-allowed m r p q ×
      (m ≡ 𝟙ᵐ → ¬ Trivial → r ≢ 𝟘)
  ; Prodrec-allowed-upwards-closed = λ (ok , r≢𝟘) m≤m′ →
      Prodrec-allowed-upwards-closed ok m≤m′ , λ { refl → r≢𝟘 (≤ᵐ-𝟙ᵐ→ m≤m′) }
  ; erased-matches-for-J =
      f (erased-matches-for-J 𝟘ᵐ?)
  ; erased-matches-for-J-≤ᵉᵐ =
      𝟙ᵐ𝟘ᵐ→≤ᵐ (λ m m′ → f _ m ≤ᵉᵐ f _ m′) _ ≤ᵉᵐ-reflexive
  ; erased-matches-for-K =
      f (erased-matches-for-K 𝟘ᵐ?)
  ; erased-matches-for-K-≤ᵉᵐ =
      𝟙ᵐ𝟘ᵐ→≤ᵐ (λ m m′ → f _ m ≤ᵉᵐ f _ m′) _ ≤ᵉᵐ-reflexive
  }
  where
  open Usage-restrictions UR
  f : Erased-matches → Mode → Erased-matches
  f _  𝟙ᵐ = none
  f em 𝟘ᵐ = em

-- The function adds the restriction that certain erased matches are
-- not allowed for the mode 𝟙ᵐ. No restriction is added for emptyrec.
-- For prodrec and unitrec the added restriction only applies to
-- non-trivial modalities, and for unitrec the added restriction only
-- applies if η-equality is not allowed for weak unit types.

no-erased-matches-UR :
  Type-restrictions → Usage-restrictions → Usage-restrictions
no-erased-matches-UR TR UR = record (only-some-erased-matches UR)
  { Unitrec-allowed = λ m p q →
      Unitrec-allowed m p q ×
      (m ≡ 𝟙ᵐ → ¬ Trivial → p ≡ 𝟘 → Unitʷ-η)
  ; Unitrec-allowed-upwards-closed = λ (ok , η) m≤m′ →
      Unitrec-allowed-upwards-closed ok m≤m′ , λ { refl → η (≤ᵐ-𝟙ᵐ→ m≤m′) }
  }
  where
  open Type-restrictions TR
  open Usage-restrictions UR

-- The function updates the usage restrictions to use the usage rule
-- natrecₘ for natrec using a given nr function.

nr-available-UR :
  (has-nr : Has-nr 𝕄) →
  Usage-restrictions → Usage-restrictions
nr-available-UR has-nr UR = record UR
  { natrec-mode      = Nr ⦃ has-nr ⦄
  ; mode-supports-nr = λ { ⦃ (Nr) ⦄ → Zero-one-supports-nr}
  }

-- A function used to define no-[]-cong-UR.

at-least-some : (Mode → Erased-matches) → Mode → Erased-matches
at-least-some f m = case f m of λ where
  none → some
  em   → em

-- The function no-[]-cong-UR disables support for []-cong but enables
-- "some" erased matches for J.

no-[]-cong-UR : Usage-restrictions → Usage-restrictions
no-[]-cong-UR UR = record UR
  { []-cong-allowed-mode                = λ _ _ → Lift _ ⊥
  ; []-cong-allowed-mode-upwards-closed = λ ()
  ; erased-matches-for-J     = at-least-some erased-matches-for-J
  ; erased-matches-for-J-≤ᵉᵐ =
      𝟙ᵐ𝟘ᵐ→≤ᵐ (λ m m′ → at-least-some erased-matches-for-J m ≤ᵉᵐ at-least-some erased-matches-for-J m′)
        at-least-some-≤ᵉᵐ ≤ᵉᵐ-reflexive
  }
  where
  open Usage-restrictions UR

  at-least-some-≤ᵉᵐ :
    at-least-some erased-matches-for-J 𝟙ᵐ ≤ᵉᵐ
    at-least-some erased-matches-for-J 𝟘ᵐ[ ok ]
  at-least-some-≤ᵉᵐ {ok}
    with erased-matches-for-J 𝟙ᵐ
       | erased-matches-for-J 𝟘ᵐ[ ok ]
       | erased-matches-for-J-≤ᵉᵐ {m = 𝟙ᵐ} {m′ = 𝟘ᵐ[ ok ]} 𝟙ᵐ≤
  … | none       | none       | _  = _
  … | none       | some       | _  = _
  … | none       | all        | _  = _
  … | all        | none       | ()
  … | some       | none       | ()
  … | not-none _ | not-none _ | r  = r

------------------------------------------------------------------------
-- Only-some-erased-matches

-- The property of not allowing certain erased matches:
-- * Erased matches are allowed for emptyrec and unitrec.
-- * "Erased" matches are allowed for trivial modalities.
-- * Erased matches are allowed when the mode is not 𝟙ᵐ, except for
--   []-cong.

Only-some-erased-matches :
  Type-restrictions → Usage-restrictions → Set a
Only-some-erased-matches TR UR =
  ¬ Trivial →
  (∀ {r p q} → Prodrec-allowed 𝟙ᵐ r p q → r ≢ 𝟘) ×
  (∀ {s} → ¬ ([]-cong-allowed s)) ×
  erased-matches-for-J 𝟙ᵐ ≡ none ×
  erased-matches-for-K 𝟙ᵐ ≡ none
  where
  open Type-restrictions TR
  open Usage-restrictions UR

opaque

  -- Certain restrictions obtained from no-erased-matches-TR and
  -- only-some-erased-matches satisfy Only-some-erased-matches.

  Only-some-erased-matches-only-some-erased-matches :
    ∀ TR UR →
    Only-some-erased-matches
      (no-erased-matches-TR 𝕤 (no-erased-matches-TR 𝕨 TR))
      (only-some-erased-matches UR)
  Only-some-erased-matches-only-some-erased-matches _ _ 𝟙≢𝟘 =
      (λ x → x refl 𝟙≢𝟘) ∘→ proj₂
    , (λ where
         {s = 𝕤} → (_$ refl) ∘→ proj₂
         {s = 𝕨} → (_$ refl) ∘→ proj₂ ∘→ proj₁)
    , refl
    , refl

------------------------------------------------------------------------
-- No-erased-matches

-- The property of not allowing (certain) erased matches:
-- * Erased matches are allowed for emptyrec.
-- * "Erased" matches are allowed for unitrec if η-equality is allowed
--   for weak unit types.
-- * "Erased" matches are allowed for trivial modalities.
-- * Erased matches are allowed when the mode is not 𝟙ᵐ, except for
--   []-cong. (Note that a variant of []-cong that works when the mode
--   is not 𝟙ᵐ can be defined without the use of []-cong, see
--   Graded.Box-cong.▸[]-cong-J-𝟘ᵐ.)

No-erased-matches : Type-restrictions → Usage-restrictions → Set a
No-erased-matches TR UR =
  ¬ Trivial →
  (∀ {r p q} → Prodrec-allowed 𝟙ᵐ r p q → r ≢ 𝟘) ×
  (∀ {p q}   → Unitrec-allowed 𝟙ᵐ p q   → p ≡ 𝟘 → Unitʷ-η) ×
  (∀ {s} → ¬ ([]-cong-allowed s)) ×
  erased-matches-for-J 𝟙ᵐ ≡ none ×
  erased-matches-for-K 𝟙ᵐ ≡ none
  where
  open Type-restrictions TR
  open Usage-restrictions UR

-- Certain restrictions obtained from no-erased-matches-TR and
-- no-erased-matches-UR satisfy No-erased-matches.

No-erased-matches-no-erased-matches :
  ∀ TR UR →
  let TR′ = no-erased-matches-TR 𝕤 (no-erased-matches-TR 𝕨 TR) in
  No-erased-matches TR′ (no-erased-matches-UR TR′ UR)
No-erased-matches-no-erased-matches TR UR 𝟙≢𝟘 =
  case Only-some-erased-matches-only-some-erased-matches TR UR 𝟙≢𝟘 of λ
    (pr , rest) →
    (λ {_ _ _} → pr)
  , (λ {_ _} → (λ x → x refl 𝟙≢𝟘) ∘→ proj₂)
  , rest

opaque

  -- If Unitʷ-η holds for TR, then Only-some-erased-matches TR UR
  -- implies No-erased-matches TR UR.

  Only-some-erased-matches→No-erased-matches :
    ∀ TR UR →
    Type-restrictions.Unitʷ-η TR →
    Only-some-erased-matches TR UR → No-erased-matches TR UR
  Only-some-erased-matches→No-erased-matches _ _ η =
    Σ.map idᶠ ((λ {_ _} _ _ → η) ,_) ∘→_

-- An alternative to No-erased-matches that refers to
-- Type-variant instead of Type-restrictions

No-erased-matches′ : Type-variant → Usage-restrictions → Set a
No-erased-matches′ TV UR =
  ¬ Trivial →
  (∀ {r p q} → Prodrec-allowed 𝟙ᵐ r p q → r ≢ 𝟘) ×
  (∀ {p q}   → Unitrec-allowed 𝟙ᵐ p q   → p ≡ 𝟘 → Unitʷ-η) ×
  (∀ {s} → ¬ ([]-cong-allowed-mode s 𝟙ᵐ)) ×
  erased-matches-for-J 𝟙ᵐ ≡ none ×
  erased-matches-for-K 𝟙ᵐ ≡ none
  where
  open Type-variant TV
  open Usage-restrictions UR

------------------------------------------------------------------------
-- Some lemmas related to UD.Assumptions

opaque

  -- If grade equality is decidable and the modality supports usage
  -- inference for a given natrec-mode nm, UD.Assumptions holds for
  -- no-usage-restrictions nm b false.

  Assumptions-no-usage-restrictions :
    ⦃ ok : Natrec-mode-supports-usage-inference nm ⦄ →
    Decidable (_≡_ {A = M}) →
    UD.Assumptions (no-usage-restrictions nm b false)
  Assumptions-no-usage-restrictions dec = λ where
      ._≟_                       → dec
      .Prodrec-allowed? _ _ _ _  → yes _
      .Unitrec-allowed? _ _ _    → yes _
      .Emptyrec-allowed? _ _     → yes _
      .[]-cong-allowed-mode? _ _ → yes _
      .no-sink-or-≤𝟘             → inj₁ idᶠ
    where
    open UD.Assumptions

opaque

  -- The function not-all-erased-matches-JK preserves UD.Assumptions.

  Assumptions-not-all-erased-matches-JK :
    UD.Assumptions UR → UD.Assumptions (not-all-erased-matches-JK UR)
  Assumptions-not-all-erased-matches-JK as = λ where
      ._≟_                   → A._≟_
      .Prodrec-allowed?      → A.Prodrec-allowed?
      .Unitrec-allowed?      → A.Unitrec-allowed?
      .Emptyrec-allowed?     → A.Emptyrec-allowed?
      .[]-cong-allowed-mode? → A.[]-cong-allowed-mode?
      .no-sink-or-≤𝟘         → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions as
    open UD.Assumptions

opaque

  -- The function only-some-erased-matches preserves UD.Assumptions.

  Assumptions-only-some-erased-matches :
    UD.Assumptions UR → UD.Assumptions (only-some-erased-matches UR)
  Assumptions-only-some-erased-matches as = λ where
      ._≟_                       → A._≟_
      .Prodrec-allowed? m r p q  → A.Prodrec-allowed? m r p q
                                    ×-dec
                                  Dec.map (λ ≡𝟙 → trans (sym (⌞⌜⌝⌟ _)) (trans (⌞⌟-cong ≡𝟙) ⌞𝟙⌟))
                                    (λ { refl → ⌜𝟙ᵐ⌝}) (⌜ m ⌝ A.≟ 𝟙)
                                    →-dec
                                  ¬? trivial?
                                    →-dec
                                  ¬? (r A.≟ 𝟘)
      .Unitrec-allowed?       → A.Unitrec-allowed?
      .Emptyrec-allowed?      → A.Emptyrec-allowed?
      .[]-cong-allowed-mode?  → A.[]-cong-allowed-mode?
      .no-sink-or-≤𝟘          → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions as
    open UD.Assumptions

opaque

  -- The function no-erased-matches-UR TR preserves UD.Assumptions.

  Assumptions-no-erased-matches-UR :
    ∀ TR → UD.Assumptions UR →
    UD.Assumptions (no-erased-matches-UR TR UR)
  Assumptions-no-erased-matches-UR TR as = λ where
      ._≟_                    → A._≟_
      .Prodrec-allowed?        → A.Prodrec-allowed?
      .Unitrec-allowed? m p q  → A.Unitrec-allowed? m p q
                                    ×-dec
                                 (Dec.map (λ ≡𝟙 → trans (sym (⌞⌜⌝⌟ _)) (trans (⌞⌟-cong ≡𝟙) ⌞𝟙⌟))
                                    (λ { refl → ⌜𝟙ᵐ⌝}) (⌜ m ⌝ A.≟ 𝟙)
                                    →-dec
                                   ¬? trivial?
                                    →-dec
                                   p A.≟ 𝟘
                                    →-dec
                                   Unitʷ-η?)
      .Emptyrec-allowed?     → A.Emptyrec-allowed?
      .[]-cong-allowed-mode? → A.[]-cong-allowed-mode?
      .no-sink-or-≤𝟘         → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions (Assumptions-only-some-erased-matches as)
    open UD.Assumptions
    open Type-restrictions TR
