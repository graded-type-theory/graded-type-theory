------------------------------------------------------------------------
-- Usage-restrictions-satisfied
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Usage.Restrictions.Satisfied
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions.Natrec 𝕄
open import Graded.Usage.Restrictions.Instance R
open import Graded.Usage.Properties 𝕄 R

open import Definition.Untyped M

open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat hiding (_≤_)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation

private
  module CR {n} = Tools.Reasoning.PartialOrder (≤ᶜ-poset {n = n})

private variable
  l           : Nat
  x           : Fin _
  A B t u v w : Term _
  p q r       : M
  γ           : Conₘ _
  s           : Strength
  b           : BinderMode
  m           : Mode
  sem         : Some-erased-matches
  ok          : T _

------------------------------------------------------------------------
-- Usage-restrictions-satisfied

-- Usage-restrictions-satisfied m t means that the usage restrictions
-- for Prodrec and Unitrec hold, for certain modes, for every subterm
-- in t.

data Usage-restrictions-satisfied {n} (m : Mode) : Term n → Set a where
  varᵤ :
    Usage-restrictions-satisfied m (var x)
  Emptyᵤ :
    Usage-restrictions-satisfied m Empty
  emptyrecᵤ :
    Emptyrec-allowed m p →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m (emptyrec p A t)
  Unitᵤ :
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied m (Unit s t)
  starᵤ :
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied m (star s t)
  unitrecᵤ :
    Unitrec-allowed m p q →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· p) u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (unitrec p q t A u v)
  ΠΣᵤ :
    Usage-restrictions-satisfied (m ᵐ· p) A →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  lamᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m (lam p t)
  ∘ᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied (m ᵐ· p) u →
    Usage-restrictions-satisfied m (t ∘⟨ p ⟩ u)
  prodᵤ :
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (prod s p t u)
  prodrecᵤ :
    Prodrec-allowed m r p q →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· r) t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (prodrec r p q A t u)
  fstᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m (fst p t)
  sndᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m (snd p t)
  ℕᵤ :
    Usage-restrictions-satisfied m ℕ
  zeroᵤ :
    Usage-restrictions-satisfied m zero
  sucᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m (suc t)
  natrecᵤ :
    (⦃ no-nr : Nr-not-available-GLB ⦄ →
       ∃ λ x → Greatest-lower-bound x (nrᵢ r 𝟙 p)) →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (natrec p q r A t u v)
  Levelᵤ :
    Usage-restrictions-satisfied m Level
  zeroᵘᵤ :
    Usage-restrictions-satisfied m zeroᵘ
  sucᵘᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m (sucᵘ t)
  maxᵘᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (t maxᵘ u)
  Uᵤ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m (U t)
  Idᵤ :
    ¬ Id-erased →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (Id A t u)
  Id₀ᵤ :
    Id-erased →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? u →
    Usage-restrictions-satisfied m (Id A t u)
  rflᵤ :
    Usage-restrictions-satisfied m rfl
  Jᵤ :
    erased-matches-for-J m ≤ᵉᵐ some →
    (erased-matches-for-J m ≡ some → ¬ (p ≡ 𝟘 × q ≡ 𝟘)) →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  J₀ᵤ₁ :
    erased-matches-for-J m ≡ some →
    p ≡ 𝟘 →
    q ≡ 𝟘 →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied 𝟘ᵐ? w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  J₀ᵤ₂ :
    erased-matches-for-J m ≡ all →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied 𝟘ᵐ? w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  Kᵤ :
    erased-matches-for-K m ≤ᵉᵐ some →
    (erased-matches-for-K m ≡ some → p ≢ 𝟘) →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (K p A t B u v)
  K₀ᵤ₁ :
    erased-matches-for-K m ≡ some →
    p ≡ 𝟘 →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied m (K p A t B u v)
  K₀ᵤ₂ :
    erased-matches-for-K m ≡ all →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied m (K p A t B u v)
  []-congᵤ :
    []-cong-allowed-mode s m →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied m ([]-cong s A t u v)

------------------------------------------------------------------------
-- Usage-restrictions-satisfied-𝟙ᵐ→ and some related definitions

opaque

  -- If Usage-restrictions-satisfied holds for the mode 𝟙ᵐ and the
  -- term t, then the predicate holds for any mode.

  Usage-restrictions-satisfied-𝟙ᵐ→ :
    Usage-restrictions-satisfied 𝟙ᵐ t →
    Usage-restrictions-satisfied m t

  -- If Usage-restrictions-satisfied holds for any mode and the
  -- term t, then the predicate holds for the mode 𝟘ᵐ?.

  Usage-restrictions-satisfied-→𝟘ᵐ? :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied 𝟘ᵐ? t
  Usage-restrictions-satisfied-→𝟘ᵐ? {m = 𝟙ᵐ} =
    Usage-restrictions-satisfied-𝟙ᵐ→
  Usage-restrictions-satisfied-→𝟘ᵐ? {m = 𝟘ᵐ} =
    subst (flip Usage-restrictions-satisfied _) (sym 𝟘ᵐ?≡𝟘ᵐ)

  -- If Usage-restrictions-satisfied holds for any mode and the
  -- term t, then the predicate holds for the mode 𝟘ᵐ[ ok ].

  Usage-restrictions-satisfied-→𝟘ᵐ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied 𝟘ᵐ[ ok ] t
  Usage-restrictions-satisfied-→𝟘ᵐ =
    subst (flip Usage-restrictions-satisfied _) 𝟘ᵐ?≡𝟘ᵐ ∘→
    Usage-restrictions-satisfied-→𝟘ᵐ?

  -- A generalisation of Jᵤ: erased-matches-for-J m ≡ none has been
  -- removed.

  Jᵤ-generalised :
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  Jᵤ-generalised {m} {p} {q} A t B u v w
    with J-view p q m
  … | is-other ≤some ≢𝟘 =
    Jᵤ ≤some ≢𝟘 A t B u v w
  … | is-some-yes ≡some (refl , refl) =
    J₀ᵤ₁ ≡some refl refl A (Usage-restrictions-satisfied-→𝟘ᵐ? t) B u
      (Usage-restrictions-satisfied-→𝟘ᵐ? v)
      (Usage-restrictions-satisfied-→𝟘ᵐ? w)
  … | is-all ≡all =
    J₀ᵤ₂ ≡all A (Usage-restrictions-satisfied-→𝟘ᵐ? t)
      (Usage-restrictions-satisfied-→𝟘ᵐ? B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ? v)
      (Usage-restrictions-satisfied-→𝟘ᵐ? w)

  -- A generalisation of J₀ᵤ₁.

  J₀ᵤ₁-generalised :
    erased-matches-for-J m ≡ not-none sem →
    p ≡ 𝟘 →
    q ≡ 𝟘 →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied 𝟘ᵐ? w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  J₀ᵤ₁-generalised {m} ≡not-none refl refl A t B u v w
    with erased-matches-for-J m in ok
  … | none =
    case ≡not-none of λ ()
  … | some =
    J₀ᵤ₁ ok refl refl A t B u v w
  … | all =
    J₀ᵤ₂ ok A (Usage-restrictions-satisfied-→𝟘ᵐ? t)
      (Usage-restrictions-satisfied-→𝟘ᵐ? B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ? v)
      (Usage-restrictions-satisfied-→𝟘ᵐ? w)

  -- A generalisation of Kᵤ: erased-matches-for-K m ≡ none has been
  -- removed.

  Kᵤ-generalised :
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (K p A t B u v)
  Kᵤ-generalised {m} {p} A t B u v with K-view p m
  … | is-other ≤some ≢𝟘 =
    Kᵤ ≤some ≢𝟘 A t B u v
  … | is-some-yes ≡some refl =
    K₀ᵤ₁ ≡some refl A (Usage-restrictions-satisfied-→𝟘ᵐ? t) B u
      (Usage-restrictions-satisfied-→𝟘ᵐ? v)
  … | is-all ≡all =
    K₀ᵤ₂ ≡all A (Usage-restrictions-satisfied-→𝟘ᵐ? t)
      (Usage-restrictions-satisfied-→𝟘ᵐ? B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ? v)

  -- A generalisation of K₀ᵤ₁.

  K₀ᵤ₁-generalised :
    erased-matches-for-K m ≡ not-none sem →
    p ≡ 𝟘 →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied m (K p A t B u v)
  K₀ᵤ₁-generalised {m} hyp refl A t B u v
    with erased-matches-for-K m in ok
  … | none =
    case hyp of λ ()
  … | some =
    K₀ᵤ₁ ok refl A t B u v
  … | all =
    K₀ᵤ₂ ok A (Usage-restrictions-satisfied-→𝟘ᵐ? t)
      (Usage-restrictions-satisfied-→𝟘ᵐ? B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ? v)

  Usage-restrictions-satisfied-𝟙ᵐ→ {m = 𝟙ᵐ} = idᶠ
  Usage-restrictions-satisfied-𝟙ᵐ→ {m = 𝟘ᵐ[ ok ]} = λ where
    varᵤ →
      varᵤ
    Emptyᵤ →
      Emptyᵤ
    (emptyrecᵤ ok A t) →
      emptyrecᵤ (Emptyrec-allowed-downwards-closed ok) A
        (Usage-restrictions-satisfied-→𝟘ᵐ t)
    (Unitᵤ t) →
      Unitᵤ t
    (starᵤ t) →
      starᵤ t
    (unitrecᵤ ok t A u v) →
      unitrecᵤ (Unitrec-allowed-downwards-closed ok) t A
        (Usage-restrictions-satisfied-→𝟘ᵐ u)
        (Usage-restrictions-satisfied-→𝟘ᵐ v)
    (ΠΣᵤ A B) →
      ΠΣᵤ (Usage-restrictions-satisfied-→𝟘ᵐ A)
        (Usage-restrictions-satisfied-𝟙ᵐ→ B)
    (lamᵤ t) →
      lamᵤ (Usage-restrictions-satisfied-𝟙ᵐ→ t)
    (∘ᵤ t u) →
      ∘ᵤ (Usage-restrictions-satisfied-𝟙ᵐ→ t)
        (Usage-restrictions-satisfied-→𝟘ᵐ u)
    (prodᵤ t u) →
      prodᵤ (Usage-restrictions-satisfied-→𝟘ᵐ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
    (prodrecᵤ ok A t u) →
      prodrecᵤ (Prodrec-allowed-downwards-closed ok) A
        (Usage-restrictions-satisfied-→𝟘ᵐ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
    (fstᵤ t) →
      fstᵤ (Usage-restrictions-satisfied-𝟙ᵐ→ t)
    (sndᵤ t) →
      sndᵤ (Usage-restrictions-satisfied-𝟙ᵐ→ t)
    ℕᵤ →
      ℕᵤ
    zeroᵤ →
      zeroᵤ
    (sucᵤ t) →
      sucᵤ (Usage-restrictions-satisfied-𝟙ᵐ→ t)
    (natrecᵤ x≤ A t u v) →
      natrecᵤ x≤ A (Usage-restrictions-satisfied-𝟙ᵐ→ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
        (Usage-restrictions-satisfied-𝟙ᵐ→ v)
    Levelᵤ →
      Levelᵤ
    zeroᵘᵤ →
      zeroᵘᵤ
    (sucᵘᵤ t) →
      sucᵘᵤ (Usage-restrictions-satisfied-𝟙ᵐ→ t)
    (maxᵘᵤ t u) →
      maxᵘᵤ (Usage-restrictions-satisfied-𝟙ᵐ→ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
    (Uᵤ t) →
      Uᵤ (Usage-restrictions-satisfied-𝟙ᵐ→ t)
    (Idᵤ ok A t u) →
      Idᵤ ok A (Usage-restrictions-satisfied-𝟙ᵐ→ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
    (Id₀ᵤ ok A t u) →
      Id₀ᵤ ok A t u
    rflᵤ →
      rflᵤ
    (Jᵤ _ _ A t B u v w) →
      Jᵤ-generalised A (Usage-restrictions-satisfied-𝟙ᵐ→ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ B)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
        (Usage-restrictions-satisfied-𝟙ᵐ→ v)
        (Usage-restrictions-satisfied-𝟙ᵐ→ w)
    (J₀ᵤ₁ ≡some p≡𝟘 q≡𝟘 A t B u v w) →
      case singleton $ erased-matches-for-J 𝟘ᵐ of λ where
        (not-none _ , ≡not-none) →
          J₀ᵤ₁-generalised ≡not-none p≡𝟘 q≡𝟘 A
            (Usage-restrictions-satisfied-→𝟘ᵐ? t)
            (Usage-restrictions-satisfied-𝟙ᵐ→ B)
            (Usage-restrictions-satisfied-𝟙ᵐ→ u)
            (Usage-restrictions-satisfied-→𝟘ᵐ? v)
            (Usage-restrictions-satisfied-→𝟘ᵐ? w)
        (none , ≡none) →
          case
            trans (sym ≡some)
              (≤ᵉᵐ→≡none→≡none erased-matches-for-J-≤ᵉᵐ ≡none)
          of λ ()
    (J₀ᵤ₂ ≡all A t B u v w) →
      J₀ᵤ₂ (≤ᵉᵐ→≡all→≡all erased-matches-for-J-≤ᵉᵐ ≡all) A t B
        (Usage-restrictions-satisfied-𝟙ᵐ→ u) v w
    (Kᵤ _ _ A t B u v) →
      Kᵤ-generalised A (Usage-restrictions-satisfied-𝟙ᵐ→ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ B)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
        (Usage-restrictions-satisfied-𝟙ᵐ→ v)
    (K₀ᵤ₁ ≡some p≡𝟘 A t B u v) →
      case singleton $ erased-matches-for-K 𝟘ᵐ of λ where
        (not-none _ , ≡not-none) →
          K₀ᵤ₁-generalised ≡not-none p≡𝟘 A
            (Usage-restrictions-satisfied-→𝟘ᵐ? t)
            (Usage-restrictions-satisfied-𝟙ᵐ→ B)
            (Usage-restrictions-satisfied-𝟙ᵐ→ u)
            (Usage-restrictions-satisfied-→𝟘ᵐ? v)
        (none , ≡none) →
          case
            trans (sym ≡some)
              (≤ᵉᵐ→≡none→≡none erased-matches-for-K-≤ᵉᵐ ≡none)
          of λ ()
    (K₀ᵤ₂ ≡all A t B u v) →
      K₀ᵤ₂ (≤ᵉᵐ→≡all→≡all erased-matches-for-K-≤ᵉᵐ ≡all) A t B
        (Usage-restrictions-satisfied-𝟙ᵐ→ u) v
    ([]-congᵤ ok A t u v) →
      []-congᵤ ([]-cong-allowed-mode-downwards-closed ok) A t u v

opaque

  -- Usage-restrictions-satisfied is closed under _ᵐ· p.

  Usage-restrictions-satisfied-ᵐ· :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied (m ᵐ· p) t
  Usage-restrictions-satisfied-ᵐ· {m = 𝟘ᵐ} = idᶠ
  Usage-restrictions-satisfied-ᵐ· {m = 𝟙ᵐ} =
    Usage-restrictions-satisfied-𝟙ᵐ→

------------------------------------------------------------------------
-- Converting to and from _▸[_]_

opaque

  -- If t is well-resourced (with respect to any context and the
  -- mode m), then Usage-restrictions-satisfied m t holds.

  ▸→Usage-restrictions-satisfied :
    γ ▸[ m ] t → Usage-restrictions-satisfied m t
  ▸→Usage-restrictions-satisfied = λ where
    var →
      varᵤ
    Emptyₘ →
      Emptyᵤ
    (emptyrecₘ ▸t ▸A ok) →
      emptyrecᵤ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
    (Unitₘ ▸t) →
      Unitᵤ (▸→Usage-restrictions-satisfied ▸t)
    (starʷₘ ▸t) →
      starᵤ (▸→Usage-restrictions-satisfied ▸t)
    (starˢₘ _ ▸t) →
      starᵤ (▸→Usage-restrictions-satisfied ▸t)
    (unitrecₘ ▸t ▸A ▸u ▸v ok) →
      unitrecᵤ ok (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    (ΠΣₘ ▸A ▸B) →
      ΠΣᵤ (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸B)
    (lamₘ ▸t) →
      lamᵤ (▸→Usage-restrictions-satisfied ▸t)
    (▸t ∘ₘ ▸u) →
      ∘ᵤ (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
    (prodʷₘ ▸t ▸u) →
      prodᵤ (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
    (prodˢₘ ▸t ▸u) →
      prodᵤ (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
    (prodrecₘ ▸t ▸u ▸A ok) →
      prodrecᵤ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
    (fstₘ _ ▸t refl _) →
      fstᵤ (▸→Usage-restrictions-satisfied ▸t)
    (sndₘ ▸t) →
      sndᵤ (▸→Usage-restrictions-satisfied ▸t)
    ℕₘ →
      ℕᵤ
    zeroₘ →
      zeroᵤ
    (sucₘ ▸t) →
      sucᵤ (▸→Usage-restrictions-satisfied ▸t)
    (natrecₘ ⦃ has-nr ⦄ ▸t ▸u ▸v ▸A) →
      natrecᵤ
        (λ ⦃ no-nr ⦄ → ⊥-elim (¬[Nr∧No-nr-glb] has-nr no-nr))
        (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    (natrec-no-nrₘ ⦃ no-nr ⦄ ▸t ▸u ▸v ▸A _ _ _ _) →
      natrecᵤ
        (λ ⦃ no-nr′ ⦄ → ⊥-elim (¬[No-nr∧No-nr-glb] no-nr no-nr′))
        (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    (natrec-no-nr-glbₘ ▸z ▸s ▸n ▸A x≤ _) →
      natrecᵤ (_ , x≤)
        (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸z)
        (▸→Usage-restrictions-satisfied ▸s)
        (▸→Usage-restrictions-satisfied ▸n)
    Levelₘ →
      Levelᵤ
    zeroᵘₘ →
      zeroᵘᵤ
    (sucᵘₘ ▸t) →
      sucᵘᵤ (▸→Usage-restrictions-satisfied ▸t)
    (maxᵘₘ ▸t ▸u) →
      maxᵘᵤ (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
    (Uₘ ▸t) →
      Uᵤ (▸→Usage-restrictions-satisfied ▸t)
    (Idₘ ok ▸A ▸t ▸u) →
      Idᵤ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
    (Id₀ₘ ok ▸A ▸t ▸u) →
      Id₀ᵤ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
    rflₘ →
      rflᵤ
    (Jₘ ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v ▸w) →
      Jᵤ ok₁ ok₂ (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
        (▸→Usage-restrictions-satisfied ▸w)
    (J₀ₘ₁ ok p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸v ▸w) →
      J₀ᵤ₁ ok p≡𝟘 q≡𝟘 (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
        (▸→Usage-restrictions-satisfied ▸w)
    (J₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v ▸w) →
      J₀ᵤ₂ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
        (▸→Usage-restrictions-satisfied ▸w)
    (Kₘ ok₁ ok₂ ▸A ▸t ▸B ▸u ▸v) →
      Kᵤ ok₁ ok₂ (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    (K₀ₘ₁ ok p≡𝟘 ▸A ▸t ▸B ▸u ▸v) →
      K₀ᵤ₁ ok p≡𝟘 (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    (K₀ₘ₂ ok ▸A ▸t ▸B ▸u ▸v) →
      K₀ᵤ₂ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    ([]-congₘ ▸A ▸t ▸u ▸v ok) →
      []-congᵤ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    (sub ▸t _) →
      ▸→Usage-restrictions-satisfied ▸t

opaque

  -- If Usage-restrictions-satisfied 𝟘ᵐ[ ok ] t holds, then t is
  -- well-resourced with respect to 𝟘ᶜ and 𝟘ᵐ[ ok ].

  Usage-restrictions-satisfied→▸[𝟘ᵐ] :
    Usage-restrictions-satisfied 𝟘ᵐ[ ok ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t
  Usage-restrictions-satisfied→▸[𝟘ᵐ] {ok = 𝟘ᵐ-ok} = lemma
    where
    open CR

    𝟘ᵐ?≡𝟘ᵐ′ : 𝟘ᵐ? ≡ 𝟘ᵐ[ 𝟘ᵐ-ok ]
    𝟘ᵐ?≡𝟘ᵐ′ = 𝟘ᵐ?≡𝟘ᵐ

    lemma :
      Usage-restrictions-satisfied 𝟘ᵐ[ 𝟘ᵐ-ok ] t →
      𝟘ᶜ ▸[ 𝟘ᵐ[ 𝟘ᵐ-ok ] ] t

    lemma-𝟘ᵐ? :
      Usage-restrictions-satisfied 𝟘ᵐ? t →
      𝟘ᶜ ▸[ 𝟘ᵐ? ] t
    lemma-𝟘ᵐ? =
      ▸-cong (sym 𝟘ᵐ?≡𝟘ᵐ) ∘→
      lemma ∘→
      subst (λ m → Usage-restrictions-satisfied m _) 𝟘ᵐ?≡𝟘ᵐ

    lemma = λ where
      (prodrecᵤ {r} {p} {q} ok A-ok t-ok u-ok) →
        sub (prodrecₘ (lemma t-ok)
               (sub (lemma u-ok) $ begin
                  𝟘ᶜ ∙ 𝟘 · r · p ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
                  𝟘ᶜ                      ∎)
               (sub (lemma-𝟘ᵐ? A-ok) $ begin
                  𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
                  𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
                  𝟘ᶜ                ∎)
               ok) $ begin
          𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
          r ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
          r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
      (ΠΣᵤ {q} A-ok B-ok) →
        sub (ΠΣₘ (lemma A-ok) $ sub (lemma B-ok) $ begin
               𝟘ᶜ ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
               𝟘ᶜ          ∎) $ begin
          𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
      (lamᵤ {p} t-ok) →
        lamₘ $ sub (lemma t-ok) $ begin
          𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
          𝟘ᶜ          ∎
      (∘ᵤ {p} t-ok u-ok) →
        sub (lemma t-ok ∘ₘ lemma u-ok) $ begin
          𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
          p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ∎
      (prodᵤ {p} {s = 𝕤} t-ok u-ok) →
        sub (prodˢₘ (lemma t-ok) (lemma u-ok)) $ begin
          𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
          𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
          p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎
      (prodᵤ {p} {s = 𝕨} t-ok u-ok) →
        sub (prodʷₘ (lemma t-ok) (lemma u-ok)) $ begin
          𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
          p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
      (fstᵤ t-ok) →
        fstₘ 𝟘ᵐ[ 𝟘ᵐ-ok ] (lemma t-ok) refl (λ ())
      (sndᵤ t-ok) →
        sndₘ (lemma t-ok)
      (sucᵤ t-ok) →
        sucₘ (lemma t-ok)
      (natrecᵤ {r} {p} {q} x≤ A-ok t-ok u-ok v-ok) →
        let u-lemma =
              sub (lemma u-ok) $ begin
                𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
                𝟘ᶜ                  ∎
            A-lemma =
              sub (lemma-𝟘ᵐ? A-ok) $ begin
                𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
                𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
                𝟘ᶜ                ∎
        in  case natrec-mode? natrec-mode of λ where
              does-have-nr →
                sub (natrecₘ (lemma t-ok) u-lemma (lemma v-ok) A-lemma) $
                begin
                  𝟘ᶜ                ≈˘⟨ nrᶜ-𝟘ᶜ ⟩
                  nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ  ∎
              does-not-have-nr →
                natrec-no-nrₘ (lemma t-ok) u-lemma (lemma v-ok) A-lemma
                  ≤ᶜ-refl (λ _ → ≤ᶜ-refl) ≤ᶜ-refl $ begin
                  𝟘ᶜ                        ≈˘⟨ +ᶜ-identityʳ _ ⟩
                  𝟘ᶜ +ᶜ 𝟘ᶜ                  ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (·ᶜ-zeroʳ _) ⟩
                  p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
                  𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ  ∎
              does-not-have-nr-glb →
                let x , x≤ = x≤
                in  sub (natrec-no-nr-glbₘ (lemma t-ok) u-lemma
                           (lemma v-ok) A-lemma x≤
                           (GLBᶜ-const (λ _ → nrᵢᶜ-𝟘ᶜ))) $ begin
                      𝟘ᶜ            ≈˘⟨ +ᶜ-identityˡ _ ⟩
                      𝟘ᶜ +ᶜ 𝟘ᶜ      ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
                      x ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ ∎
      (emptyrecᵤ {p} ok A-ok t-ok) →
        sub (emptyrecₘ (lemma t-ok) (lemma-𝟘ᵐ? A-ok) ok) $ begin
          𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
          p ·ᶜ 𝟘ᶜ  ∎
      (unitrecᵤ {p} {q} ok t-ok A-ok u-ok v-ok) →
        sub (unitrecₘ (lemma-𝟘ᵐ? t-ok)
               (sub (lemma-𝟘ᵐ? A-ok) $ begin
                  𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) ⟩
                  𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
                  𝟘ᶜ                ∎)
               (lemma u-ok) (lemma v-ok) ok) $ begin
          𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
          p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
      (Idᵤ not-erased A-ok t-ok u-ok) → sub
        (Idₘ not-erased
           (lemma-𝟘ᵐ? A-ok)
           (lemma t-ok)
           (lemma u-ok))
        (begin
           𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
           𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
      (Id₀ᵤ erased A-ok t-ok u-ok) →
        Id₀ₘ erased
          (lemma-𝟘ᵐ? A-ok)
          (lemma-𝟘ᵐ? t-ok)
          (lemma-𝟘ᵐ? u-ok)
      (Jᵤ {p} {q} ok₁ ok₂ A-ok t-ok B-ok u-ok v-ok w-ok) → sub
        (Jₘ ok₁ ok₂
           (lemma-𝟘ᵐ? A-ok)
           (lemma t-ok)
           (sub (lemma B-ok) $ begin
              𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ                  ∎)
           (lemma u-ok)
           (lemma v-ok)
           (lemma w-ok))
        (begin
           𝟘ᶜ                                 ≈˘⟨ ω·ᶜ+ᶜ⁵𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      (J₀ᵤ₁ ok p≡𝟘 q≡𝟘 A-ok t-ok B-ok u-ok v-ok w-ok) → sub
        (J₀ₘ₁ ok p≡𝟘 q≡𝟘 (lemma-𝟘ᵐ? A-ok) (lemma-𝟘ᵐ? t-ok) (lemma B-ok)
           (lemma u-ok) (lemma-𝟘ᵐ? v-ok) (lemma-𝟘ᵐ? w-ok))
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      (J₀ᵤ₂ {p} {q} ok A-ok t-ok B-ok u-ok v-ok w-ok) →
        J₀ₘ₂ ok
          (lemma-𝟘ᵐ? A-ok)
          (lemma-𝟘ᵐ? t-ok)
          (sub (lemma-𝟘ᵐ? B-ok) $ begin
             𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
             𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q              ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ                              ∎)
          (lemma u-ok)
          (lemma-𝟘ᵐ? v-ok)
          (lemma-𝟘ᵐ? w-ok)
      (Kᵤ {p} ok₁ ok₂ A-ok t-ok B-ok u-ok v-ok) → sub
        (Kₘ ok₁ ok₂
           (lemma-𝟘ᵐ? A-ok)
           (lemma t-ok)
           (sub (lemma B-ok) $ begin
              𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ          ∎)
           (lemma u-ok)
           (lemma v-ok))
        (begin
           𝟘ᶜ                           ≈˘⟨ ω·ᶜ+ᶜ⁴𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      (K₀ᵤ₁ ok p≡𝟘 A-ok t-ok B-ok u-ok v-ok) → sub
        (K₀ₘ₁ ok p≡𝟘 (lemma-𝟘ᵐ? A-ok) (lemma-𝟘ᵐ? t-ok) (lemma B-ok)
           (lemma u-ok) (lemma-𝟘ᵐ? v-ok))
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      (K₀ᵤ₂ {p} ok A-ok t-ok B-ok u-ok v-ok) →
        K₀ₘ₂ ok
          (lemma-𝟘ᵐ? A-ok)
          (lemma-𝟘ᵐ? t-ok)
          (sub (lemma-𝟘ᵐ? B-ok) $ begin
             𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
             𝟘ᶜ ∙ 𝟘 · p        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ                ∎)
          (lemma u-ok)
          (lemma-𝟘ᵐ? v-ok)
      ([]-congᵤ ok A-ok t-ok u-ok v-ok) →
        []-congₘ
          (lemma-𝟘ᵐ? A-ok)
          (lemma-𝟘ᵐ? t-ok)
          (lemma-𝟘ᵐ? u-ok)
          (lemma-𝟘ᵐ? v-ok)
          ok
      (varᵤ {x}) →
        sub var $ begin
          𝟘ᶜ          ≡˘⟨ 𝟘ᶜ,≔𝟘 ⟩
          𝟘ᶜ , x ≔ 𝟘  ∎
      Levelᵤ →
        Levelₘ
      zeroᵘᵤ →
        zeroᵘₘ
      (sucᵘᵤ t-ok) →
        sucᵘₘ (lemma t-ok)
      (maxᵘᵤ t-ok u-ok) →
        sub (maxᵘₘ (lemma t-ok) (lemma u-ok)) $ begin
          𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
      (Uᵤ t-ok) →
        Uₘ (lemma t-ok)
      ℕᵤ →
        ℕₘ
      Emptyᵤ →
        Emptyₘ
      (Unitᵤ t-ok) →
        Unitₘ (lemma-𝟘ᵐ? t-ok)
      zeroᵤ →
        zeroₘ
      (starᵤ t-ok) →
        starₘ (lemma-𝟘ᵐ? t-ok)
      rflᵤ →
        rflₘ

opaque

  -- An alternative characterisation of 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t.

  𝟘ᶜ▸[𝟘ᵐ]⇔ : 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t ⇔ Usage-restrictions-satisfied 𝟘ᵐ[ ok ] t
  𝟘ᶜ▸[𝟘ᵐ]⇔ =
      ▸→Usage-restrictions-satisfied
    , Usage-restrictions-satisfied→▸[𝟘ᵐ]

opaque

  -- An alternative characterisation of γ ▸[ 𝟘ᵐ[ ok ] ] t.

  ▸[𝟘ᵐ]⇔ :
    γ ▸[ 𝟘ᵐ[ ok ] ] t ⇔
    (γ ≤ᶜ 𝟘ᶜ × Usage-restrictions-satisfied 𝟘ᵐ[ ok ] t)
  ▸[𝟘ᵐ]⇔ =
      (λ ▸t → ▸-𝟘ᵐ ▸t , ▸→Usage-restrictions-satisfied ▸t)
    , (λ (γ≤𝟘 , ok) → sub (Usage-restrictions-satisfied→▸[𝟘ᵐ] ok) γ≤𝟘)

------------------------------------------------------------------------
-- Lemmas that apply if the modality is trivial

opaque

  -- If the modality is trivial and Usage-restrictions-satisfied m t
  -- holds, then γ ▸[ m ] t holds.

  Trivial→Usage-restrictions-satisfied→▸ :
    Trivial → Usage-restrictions-satisfied m t → γ ▸[ m ] t
  Trivial→Usage-restrictions-satisfied→▸ 𝟙≡𝟘 = lemma
    where mutual
    lemma₀ : Usage-restrictions-satisfied m t → 𝟘ᶜ ▸[ m ] t
    lemma₀ = lemma

    lemma : Usage-restrictions-satisfied m t → γ ▸[ m ] t
    lemma = λ where
      (prodrecᵤ ok A-ok t-ok u-ok) →
        sub
          (prodrecₘ {δ = 𝟘ᶜ} {η = 𝟘ᶜ} (lemma₀ t-ok) (lemma u-ok)
             (lemma A-ok) ok)
          (≈ᶜ-trivial 𝟙≡𝟘)
      (ΠΣᵤ A-ok B-ok) →
        sub (ΠΣₘ {δ = 𝟘ᶜ} (lemma₀ A-ok) (lemma B-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (lamᵤ t-ok) →
        lamₘ (lemma t-ok)
      (∘ᵤ t-ok u-ok) →
        sub (lemma₀ t-ok ∘ₘ lemma₀ u-ok) (≈ᶜ-trivial 𝟙≡𝟘)
      (prodᵤ {s = 𝕤} t-ok u-ok) →
        sub (prodˢₘ (lemma₀ t-ok) (lemma₀ u-ok)) (≈ᶜ-trivial 𝟙≡𝟘)
      (prodᵤ {s = 𝕨} t-ok u-ok) →
        sub (prodʷₘ (lemma₀ t-ok) (lemma₀ u-ok)) (≈ᶜ-trivial 𝟙≡𝟘)
      (fstᵤ t-ok) →
        fstₘ 𝟙ᵐ
          (▸-cong (Mode-propositional-if-trivial 𝟙≡𝟘) (lemma t-ok))
          (Mode-propositional-if-trivial 𝟙≡𝟘)
          (λ _ → ≡-trivial 𝟙≡𝟘)
      (sndᵤ t-ok) →
        sndₘ (lemma t-ok)
      (sucᵤ t-ok) →
        sucₘ (lemma t-ok)
      (natrecᵤ x≤ A-ok t-ok u-ok v-ok) →
        case natrec-mode? natrec-mode of λ where
          does-have-nr →
            sub
              (natrecₘ {δ = 𝟘ᶜ} {θ = 𝟘ᶜ} (lemma₀ t-ok) (lemma u-ok)
                 (lemma₀ v-ok) (lemma A-ok))
              (≈ᶜ-trivial 𝟙≡𝟘)
          does-not-have-nr →
            natrec-no-nrₘ {δ = 𝟘ᶜ} {θ = 𝟘ᶜ} (lemma₀ t-ok) (lemma u-ok)
              (lemma₀ v-ok) (lemma A-ok) (≈ᶜ-trivial 𝟙≡𝟘)
              (λ _ → ≈ᶜ-trivial 𝟙≡𝟘) (≈ᶜ-trivial 𝟙≡𝟘) (≈ᶜ-trivial 𝟙≡𝟘)
          does-not-have-nr-glb →
            sub (natrec-no-nr-glbₘ {δ = 𝟘ᶜ} {θ = 𝟘ᶜ} {χ = 𝟘ᶜ}
                  (lemma₀ t-ok) (lemma u-ok) (lemma₀ v-ok)
                  (lemma A-ok) (x≤ .proj₂) (GLBᶜ-const (λ _ → nrᵢᶜ-𝟘ᶜ)))
                (≈ᶜ-trivial 𝟙≡𝟘)
      (emptyrecᵤ ok A-ok t-ok) →
        sub (emptyrecₘ (lemma₀ t-ok) (lemma₀ A-ok) ok) (≈ᶜ-trivial 𝟙≡𝟘)
      (unitrecᵤ ok t-ok A-ok u-ok v-ok) →
        sub
          (unitrecₘ {γ₂ = 𝟘ᶜ} (lemma₀ t-ok) (lemma A-ok) (lemma₀ u-ok)
             (lemma₀ v-ok) ok)
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Idᵤ not-erased A-ok t-ok u-ok) →
        sub
          (Idₘ not-erased (lemma₀ A-ok) (lemma₀ t-ok) (lemma₀ u-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Id₀ᵤ erased A-ok t-ok u-ok) →
        sub
          (Id₀ₘ erased (lemma₀ A-ok) (lemma₀ t-ok) (lemma₀ u-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Jᵤ ok₁ ok₂ A-ok t-ok B-ok u-ok v-ok w-ok) →
        sub
          (Jₘ {γ₃ = 𝟘ᶜ} ok₁ ok₂ (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok) (lemma₀ w-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (J₀ᵤ₁ ok p≡𝟘 q≡𝟘 A-ok t-ok B-ok u-ok v-ok w-ok) →
        sub
          (J₀ₘ₁ {γ₃ = 𝟘ᶜ} ok p≡𝟘 q≡𝟘 (lemma₀ A-ok) (lemma₀ t-ok)
             (lemma B-ok) (lemma₀ u-ok) (lemma₀ v-ok) (lemma₀ w-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (J₀ᵤ₂ ok A-ok t-ok B-ok u-ok v-ok w-ok) →
        sub
          (J₀ₘ₂ {γ₃ = 𝟘ᶜ} ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok) (lemma₀ w-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Kᵤ ok₁ ok₂ A-ok t-ok B-ok u-ok v-ok) →
        sub
          (Kₘ {γ₃ = 𝟘ᶜ} ok₁ ok₂ (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (K₀ᵤ₁ ok p≡𝟘 A-ok t-ok B-ok u-ok v-ok) →
        sub
          (K₀ₘ₁ {γ₃ = 𝟘ᶜ} ok p≡𝟘 (lemma₀ A-ok) (lemma₀ t-ok)
             (lemma B-ok) (lemma₀ u-ok) (lemma₀ v-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (K₀ᵤ₂ ok A-ok t-ok B-ok u-ok v-ok) →
        sub
          (K₀ₘ₂ {γ₃ = 𝟘ᶜ} ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      ([]-congᵤ ok A-ok t-ok u-ok v-ok) →
        sub
          ([]-congₘ (lemma₀ A-ok) (lemma₀ t-ok) (lemma₀ u-ok)
             (lemma₀ v-ok) ok)
          (≈ᶜ-trivial 𝟙≡𝟘)
      varᵤ →
        sub var (≈ᶜ-trivial 𝟙≡𝟘)
      Levelᵤ →
        sub Levelₘ (≈ᶜ-trivial 𝟙≡𝟘)
      zeroᵘᵤ →
        sub zeroᵘₘ (≈ᶜ-trivial 𝟙≡𝟘)
      (sucᵘᵤ t-ok) →
        sucᵘₘ (lemma t-ok)
      (maxᵘᵤ t-ok u-ok) →
        sub (maxᵘₘ {γ = 𝟘ᶜ} {δ = 𝟘ᶜ} (lemma t-ok) (lemma u-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Uᵤ t-ok) →
        Uₘ (lemma t-ok)
      ℕᵤ →
        sub ℕₘ (≈ᶜ-trivial 𝟙≡𝟘)
      Emptyᵤ →
        sub Emptyₘ (≈ᶜ-trivial 𝟙≡𝟘)
      (Unitᵤ t-ok) →
        sub (Unitₘ {γ = 𝟘ᶜ} (lemma t-ok)) (≈ᶜ-trivial 𝟙≡𝟘)
      zeroᵤ →
        sub zeroₘ (≈ᶜ-trivial 𝟙≡𝟘)
      (starᵤ t-ok) →
        sub (starₘ {γ = 𝟘ᶜ} (lemma t-ok)) (≈ᶜ-trivial 𝟙≡𝟘)
      rflᵤ →
        sub rflₘ (≈ᶜ-trivial 𝟙≡𝟘)

opaque

  -- An alternative characterisation of γ ▸[ m ] t for trivial
  -- modalities.

  Trivial→▸⇔ : Trivial → γ ▸[ m ] t ⇔ Usage-restrictions-satisfied m t
  Trivial→▸⇔ 𝟙≡𝟘 =
      ▸→Usage-restrictions-satisfied
    , Trivial→Usage-restrictions-satisfied→▸ 𝟙≡𝟘
