------------------------------------------------------------------------
-- Functions that construct configurations
------------------------------------------------------------------------

import Graded.Modality
import Graded.Mode.Instances.Zero-one.Variant

module Configuration-types.Configuration.Zero-one
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
open import Tools.Sum as ⊎
open import Tools.Unit

import Definition.Typechecking.Decidable.Assumptions as TD
open import Definition.Untyped.NotParametrised
open import Definition.Untyped.Properties.NotParametrised

open import Graded.Modality.Properties 𝕄
open import Graded.Mode.Instances.Zero-one variant as M hiding (_≟_)
import Graded.Usage.Decidable.Assumptions as UD

open import Configuration-types
open import Configuration-types.Configuration Zero-one-isMode public
  hiding (nr-available; no-restrictions)
import Configuration-types.Configuration Zero-one-isMode as C
import Configuration-types.Type-configuration 𝕄 as TC
open import Configuration-types.Erased-matches
open import Configuration-types.Natrec 𝕄
open import Configuration-types.Omega 𝕄

private variable
  TC          : Type-configuration _
  C           : Configuration _
  b₁ b₂ b₃ b₄ : Bool
  ok          : T _
  s           : Strength
  nm          : Natrec-mode

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
-- Functions that construct configurations

-- No type restrictions (see no-type-restrictions, which takes the
-- first two booleans), no restrictions for prodrec, unitrec or
-- emptyrec, all erased matches are allowed for J and K, the natrec
-- mode can be anything, the higher quotient constructors are allowed
-- exactly if the mode structure is non-trivial, Id-erased is
-- inhabited if the first boolean is true, starˢ is treated as a sink
-- if the second boolean is true, and Qrec-motive-erased is inhabited
-- if the third boolean is true. Usage rules that require the use of ω
-- are not allowed.

no-restrictions :
  (nm : Natrec-mode) →
  (_ _ _ _ _ : Bool) → Configuration Zero-one-isMode
no-restrictions nm =
  C.no-restrictions nm
    (λ { ⦃ (Nr) ⦄ → Zero-one-supports-nr ⦃ Natrec-mode-Has-nr Nr ⦄ })

-- A function used to define not-all-erased-matches-JK.

not-all-for-𝟙ᵐ : (Mode → Erased-matches) → Mode → Erased-matches
not-all-for-𝟙ᵐ f 𝟘ᵐ = f 𝟘ᵐ
not-all-for-𝟙ᵐ f 𝟙ᵐ with f 𝟙ᵐ
… | all = some
… | em  = em

-- The function adds the restriction that, for the mode 𝟙ᵐ, "all"
-- erased matches are not allowed for J and K.

not-all-erased-matches-JK :
  ⦃ ok : Has-omega 𝕄 ⦄ →
  Configuration Zero-one-isMode → Configuration Zero-one-isMode
not-all-erased-matches-JK C = record C
  { usage-rules-with-ω = with-ω
  ; erased-matches-for-JK = λ jk m → not-all-for-𝟙ᵐ (erased-matches-for-JK jk) m
  ; erased-matches-for-JK-≤ᵉᵐ =
      𝟙ᵐ𝟘ᵐ→≤ᵐ
        (λ m m′ → not-all-for-𝟙ᵐ (erased-matches-for-JK _) m ≤ᵉᵐ not-all-for-𝟙ᵐ (erased-matches-for-JK _) m′)
        (not-all-for-𝟙ᵐ-≤ᵉᵐ (erased-matches-for-JK _) (erased-matches-for-JK-≤ᵉᵐ 𝟙ᵐ≤))
        ≤ᵉᵐ-reflexive
  ; erased-matches-for-JK-supports-ω = λ _ → with-ω
  }
  where
  open Configuration C

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

only-some-erased-matches :
  ⦃ ok : Has-omega 𝕄 ⦄ →
  Configuration Zero-one-isMode → Configuration Zero-one-isMode
only-some-erased-matches C = record C
  { []-cong-allowed-mode = λ s m →
      []-cong-allowed-mode s m × m ≢ 𝟙ᵐ
  ; []-cong-allowed-mode→[]-cong-allowed =
      []-cong-allowed-mode→[]-cong-allowed ∘→ proj₁
  ; []-cong-allowed-mode-upwards-closed = λ ok m≤m′ →
      Σ.map (flip []-cong-allowed-mode-upwards-closed m≤m′)
        (≢𝟙ᵐ-upwards-closed m≤m′) ok
  ; Prodrec-allowed = λ m r p q →
      Prodrec-allowed m r p q ×
      (m ≡ 𝟙ᵐ → ¬ Trivial → r ≢ 𝟘)
  ; Prodrec-allowed-upwards-closed = λ (ok , r≢𝟘) m≤m′ →
      Prodrec-allowed-upwards-closed ok m≤m′ , λ { refl → r≢𝟘 (≤ᵐ-𝟙ᵐ→ m≤m′) }
  ; usage-rules-with-ω = with-ω
  ; erased-matches-for-JK =
      λ jk → f (erased-matches-for-JK jk 𝟘ᵐ?)
  ; erased-matches-for-JK-≤ᵉᵐ =
      𝟙ᵐ𝟘ᵐ→≤ᵐ (λ m m′ → f _ m ≤ᵉᵐ f _ m′) _ ≤ᵉᵐ-reflexive
  ; erased-matches-for-JK-supports-ω = λ _ → with-ω
  }
  where
  open Configuration C
  f : Erased-matches → Mode → Erased-matches
  f _  𝟙ᵐ = none
  f em 𝟘ᵐ = em

opaque

  -- The configurations obtained from only-some-erased-matches satisfy
  -- Only-some-erased-matches.

  Only-some-erased-matches-only-some-erased-matches :
    ⦃ ok : Has-omega 𝕄 ⦄ →
    ∀ C →
    Configuration.Only-some-erased-matches (only-some-erased-matches C)
  Only-some-erased-matches-only-some-erased-matches _ 𝟙≢𝟘 =
      (λ where
         {m = 𝟘ᵐ} _   _   → refl
         {m = 𝟙ᵐ} hyp r≡𝟘 → ⊥-elim (hyp .proj₂ refl 𝟙≢𝟘 r≡𝟘))
    , (λ where
         {m = 𝟘ᵐ} _   → refl
         {m = 𝟙ᵐ} hyp → ⊥-elim (hyp .proj₂ refl))
    , refl
    , refl

-- The function adds the restriction that certain erased matches are
-- not allowed for the mode 𝟙ᵐ. No restriction is added for emptyrec.
-- For prodrec and unitrec the added restriction only applies to
-- non-trivial modalities, and for unitrec the added restriction only
-- applies if η-equality is not allowed for weak unit types.

no-erased-matches :
  ⦃ ok : Has-omega 𝕄 ⦄ →
  Configuration Zero-one-isMode → Configuration Zero-one-isMode
no-erased-matches C = record (only-some-erased-matches C)
  { Unitrec-allowed = λ m p q →
      Unitrec-allowed m p q ×
      (m ≡ 𝟙ᵐ → ¬ Trivial → p ≡ 𝟘 → Unitʷ-η)
  ; Unitrec-allowed-upwards-closed = λ (ok , η) m≤m′ →
      Unitrec-allowed-upwards-closed ok m≤m′ , λ { refl → η (≤ᵐ-𝟙ᵐ→ m≤m′) }
  }
  where
  open Configuration C

opaque

  -- The configuration no-erased-matches C satisfies No-erased-matches.

  No-erased-matches-no-erased-matches :
    ⦃ ok : Has-omega 𝕄 ⦄ →
    ∀ C → Configuration.No-erased-matches (no-erased-matches C)
  No-erased-matches-no-erased-matches C 𝟙≢𝟘 =
    let pr , []-cong , rest =
          Only-some-erased-matches-only-some-erased-matches C 𝟙≢𝟘
    in
      (λ {_ _ _} → pr)
    , (λ where
         {m = 𝟘ᵐ} _   _   m≢𝟘 → ⊥-elim (m≢𝟘 refl)
         {m = 𝟙ᵐ} hyp p≡𝟘 _   → hyp .proj₂ refl 𝟙≢𝟘 p≡𝟘)
    , (λ {_} → []-cong)
    , rest

-- The function updates the usage restrictions to use the usage rule
-- natrecₘ for natrec using a given nr function.

nr-available :
  (has-nr : Has-nr 𝕄) →
  Configuration Zero-one-isMode → Configuration Zero-one-isMode
nr-available has-nr C = record C
  { natrec-mode      = Nr ⦃ has-nr ⦄
  ; mode-supports-nr = λ { ⦃ (Nr) ⦄ → Zero-one-supports-nr}
  }

-- A function used to define with-[]-cong.

none-for-𝟙ᵐ : (Mode → Erased-matches) → Mode → Erased-matches
none-for-𝟙ᵐ f 𝟙ᵐ = none
none-for-𝟙ᵐ f 𝟘ᵐ = f 𝟘ᵐ

-- The function enables support for []-cong (if the modality is
-- non-trivial), but disables support for erased matches for J (when
-- the mode is 𝟙ᵐ).

with-[]-cong :
  ⦃ ok : Has-omega 𝕄 ⦄ →
  Configuration Zero-one-isMode → Configuration Zero-one-isMode
with-[]-cong ⦃ ok ⦄ C = record C
  { TC =
      TC.with-[]-cong (C .Configuration.TC)
  ; []-cong-allowed-mode =
      λ m s → []-cong-allowed-mode m s ⊎ ¬ Trivial
  ; []-cong-allowed-mode→[]-cong-allowed =
      ⊎.map []-cong-allowed-mode→[]-cong-allowed idᶠ
  ; []-cong-allowed-mode-upwards-closed = λ where
      (inj₁ ok) m≤m′ → inj₁ ([]-cong-allowed-mode-upwards-closed ok m≤m′)
      (inj₂ 𝟙≢𝟘) _   → inj₂ 𝟙≢𝟘
  ; usage-rules-with-ω = with-ω ⦃ ok ⦄
  ; erased-matches-for-JK = λ where
      J m → none-for-𝟙ᵐ erased-matches-for-J m
      K m → erased-matches-for-JK K m
  ; erased-matches-for-JK-≤ᵉᵐ = λ where
      {jk = J} m≤m′ →
        𝟙ᵐ𝟘ᵐ→≤ᵐ
          (λ m₁ m₂ →
             none-for-𝟙ᵐ erased-matches-for-J m₁ ≤ᵉᵐ
             none-for-𝟙ᵐ erased-matches-for-J m₂)
          _ ≤ᵉᵐ-reflexive m≤m′
      {jk = K} m≤m′ → erased-matches-for-JK-≤ᵉᵐ m≤m′
  ; erased-matches-for-JK-supports-ω = λ _ → with-ω
  }
  where
  open Configuration C

-- A function used to define no-[]-cong.

at-least-some : (Mode → Erased-matches) → Mode → Erased-matches
at-least-some f m = case f m of λ where
  none → some
  em   → em

-- The function no-[]-cong disables support for []-cong but enables
-- "some" erased matches for J.

no-[]-cong :
  Configuration Zero-one-isMode → Configuration Zero-one-isMode
no-[]-cong C = record C
  { TC =
      TC.no-[]-cong (C .Configuration.TC)
  ; []-cong-allowed-mode =
      λ _ _ → Lift _ ⊥
  ; []-cong-allowed-mode→[]-cong-allowed =
      λ ()
  ; []-cong-allowed-mode-upwards-closed =
      λ ()
  ; erased-matches-for-JK    = λ where
      J → at-least-some erased-matches-for-J
      K → erased-matches-for-K
  ; erased-matches-for-JK-≤ᵉᵐ = λ where
      {jk = J} → 𝟙ᵐ𝟘ᵐ→≤ᵐ (λ m m′ → at-least-some erased-matches-for-J m ≤ᵉᵐ at-least-some erased-matches-for-J m′)
        at-least-some-≤ᵉᵐ ≤ᵉᵐ-reflexive
      {jk = K} → erased-matches-for-K-≤ᵉᵐ
  ; erased-matches-for-JK-supports-ω = λ where
      {jk = J} ≤some → erased-matches-for-JK-supports-ω
        (≤ᵉᵐ-transitive (some-≤ᵉᵐ-at-least-some (erased-matches-for-JK J) _) ≤some)
      {jk = K} ≤some → erased-matches-for-JK-supports-ω ≤some
  }
  where
  open Configuration C

  some-≤ᵉᵐ-at-least-some :
    (f : Mode → Erased-matches) (m : Mode) →
    f m ≤ᵉᵐ at-least-some f m
  some-≤ᵉᵐ-at-least-some f m with f m
  ... | none       = _
  ... | not-none x = ≤ᵉᵐ-reflexive

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
-- Some lemmas related to UD.Assumptions

opaque

  -- The function not-all-erased-matches-JK preserves UD.Assumptions.

  Assumptions-not-all-erased-matches-JK :
    ⦃ ok : Has-omega 𝕄 ⦄ →
    UD.Assumptions C → UD.Assumptions (not-all-erased-matches-JK C)
  Assumptions-not-all-erased-matches-JK as = λ where
      .assumptions           → A.assumptions
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
    ⦃ ok : Has-omega 𝕄 ⦄ →
    UD.Assumptions C → UD.Assumptions (only-some-erased-matches C)
  Assumptions-only-some-erased-matches as = λ where
      .assumptions              → A.assumptions
      .Prodrec-allowed? m r p q → A.Prodrec-allowed? m r p q
                                    ×-dec
                                  m M.≟ 𝟙ᵐ
                                    →-dec
                                  ¬? trivial?
                                    →-dec
                                  ¬? (r A.≟ 𝟘)
      .Unitrec-allowed?         → A.Unitrec-allowed?
      .Emptyrec-allowed?        → A.Emptyrec-allowed?
      .[]-cong-allowed-mode?    → λ s m →
                                    A.[]-cong-allowed-mode? s m
                                      ×-dec
                                    ¬? (m M.≟ 𝟙ᵐ)
      .no-sink-or-≤𝟘            → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions as
    open UD.Assumptions

opaque

  -- The function no-erased-matches preserves UD.Assumptions.

  Assumptions-no-erased-matches :
    ⦃ ok : Has-omega 𝕄 ⦄ →
    UD.Assumptions C →
    UD.Assumptions (no-erased-matches C)
  Assumptions-no-erased-matches {C} as = λ where
      .assumptions            → A.assumptions
      .Prodrec-allowed?       → A.Prodrec-allowed?
      .Unitrec-allowed? m p q → A.Unitrec-allowed? m p q
                                  ×-dec
                                (m M.≟ 𝟙ᵐ
                                   →-dec
                                 ¬? trivial?
                                   →-dec
                                 p A.≟ 𝟘
                                   →-dec
                                 Unitʷ-η?)
      .Emptyrec-allowed?      → A.Emptyrec-allowed?
      .[]-cong-allowed-mode?  → A.[]-cong-allowed-mode?
      .no-sink-or-≤𝟘          → A.no-sink-or-≤𝟘
    where
    module A = UD.Assumptions (Assumptions-only-some-erased-matches as)
    open UD.Assumptions
    open Configuration C
