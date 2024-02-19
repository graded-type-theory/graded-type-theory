------------------------------------------------------------------------
-- Usage-restrictions-satisfied
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

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
open import Graded.Modality.Dedicated-nr 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Erased-matches
open import Graded.Usage.Properties 𝕄 R

open import Definition.Untyped M

open import Tools.Bool using (T)
open import Tools.Fin
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation

private
  module CR {n} = Tools.Reasoning.PartialOrder (≤ᶜ-poset {n = n})

private variable
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
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m (emptyrec p A t)
  Unitᵤ :
    Usage-restrictions-satisfied m (Unit s)
  starᵤ :
    Usage-restrictions-satisfied m (star s)
  unitrecᵤ :
    Unitrec-allowed m p q →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (unitrec p q A t u)
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
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (natrec p q r A t u v)
  Uᵤ :
    Usage-restrictions-satisfied m U
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
    erased-matches-for-J m ≡ none →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  Jᵤ′ :
    erased-matches-for-J m ≡ some →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· (p + q)) t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied (m ᵐ· (p + q)) v →
    Usage-restrictions-satisfied (m ᵐ· (p + q)) w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  J₀ᵤ :
    erased-matches-for-J m ≡ all →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied 𝟘ᵐ? w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  Kᵤ :
    erased-matches-for-K m ≡ none →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (K p A t B u v)
  Kᵤ′ :
    erased-matches-for-K m ≡ some →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied (m ᵐ· p) v →
    Usage-restrictions-satisfied m (K p A t B u v)
  K₀ᵤ :
    erased-matches-for-K m ≡ all →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied 𝟘ᵐ? t →
    Usage-restrictions-satisfied 𝟘ᵐ? B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ? v →
    Usage-restrictions-satisfied m (K p A t B u v)
  []-congᵤ :
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

  -- Usage-restrictions-satisfied is closed under _ᵐ· p.

  Usage-restrictions-satisfied-ᵐ· :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied (m ᵐ· p) t
  Usage-restrictions-satisfied-ᵐ· {m = 𝟘ᵐ} = idᶠ
  Usage-restrictions-satisfied-ᵐ· {m = 𝟙ᵐ} =
    Usage-restrictions-satisfied-𝟙ᵐ→

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
  Jᵤ-generalised {m} A t B u v w
    with erased-matches-for-J m in ok
  … | none =
    Jᵤ ok A t B u v w
  … | some =
    Jᵤ′ ok A (Usage-restrictions-satisfied-ᵐ· t) B u
      (Usage-restrictions-satisfied-ᵐ· v)
      (Usage-restrictions-satisfied-ᵐ· w)
  … | all =
    J₀ᵤ ok A (Usage-restrictions-satisfied-→𝟘ᵐ? t)
      (Usage-restrictions-satisfied-→𝟘ᵐ? B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ? v)
      (Usage-restrictions-satisfied-→𝟘ᵐ? w)

  -- A generalisation of Jᵤ′.

  Jᵤ′-generalised :
    erased-matches-for-J m ≡ not-none sem →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· (p + q)) t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied (m ᵐ· (p + q)) v →
    Usage-restrictions-satisfied (m ᵐ· (p + q)) w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  Jᵤ′-generalised {m} hyp A t B u v w
    with erased-matches-for-J m in ok
  … | none =
    case hyp of λ ()
  … | some =
    Jᵤ′ ok A t B u v w
  … | all =
    J₀ᵤ ok A (Usage-restrictions-satisfied-→𝟘ᵐ? t)
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
  Kᵤ-generalised {m} A t B u v
    with erased-matches-for-K m in ok
  … | none =
    Kᵤ ok A t B u v
  … | some =
    Kᵤ′ ok A (Usage-restrictions-satisfied-ᵐ· t) B u
      (Usage-restrictions-satisfied-ᵐ· v)
  … | all =
    K₀ᵤ ok A (Usage-restrictions-satisfied-→𝟘ᵐ? t)
      (Usage-restrictions-satisfied-→𝟘ᵐ? B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ? v)

  -- A generalisation of Kᵤ′.

  Kᵤ′-generalised :
    erased-matches-for-K m ≡ not-none sem →
    Usage-restrictions-satisfied 𝟘ᵐ? A →
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied (m ᵐ· p) v →
    Usage-restrictions-satisfied m (K p A t B u v)
  Kᵤ′-generalised {m} hyp A t B u v
    with erased-matches-for-K m in ok
  … | none =
    case hyp of λ ()
  … | some =
    Kᵤ′ ok A t B u v
  … | all =
    K₀ᵤ ok A (Usage-restrictions-satisfied-→𝟘ᵐ? t)
      (Usage-restrictions-satisfied-→𝟘ᵐ? B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ? v)

  Usage-restrictions-satisfied-𝟙ᵐ→ {m = 𝟙ᵐ} = idᶠ
  Usage-restrictions-satisfied-𝟙ᵐ→ {m = 𝟘ᵐ[ ok ]} = λ where
    varᵤ →
      varᵤ
    Emptyᵤ →
      Emptyᵤ
    (emptyrecᵤ A t) →
      emptyrecᵤ A (Usage-restrictions-satisfied-→𝟘ᵐ t)
    Unitᵤ →
      Unitᵤ
    starᵤ →
      starᵤ
    (unitrecᵤ ok A t u) →
      unitrecᵤ (Unitrec-allowed-downwards-closed ok) A
        (Usage-restrictions-satisfied-→𝟘ᵐ t)
        (Usage-restrictions-satisfied-→𝟘ᵐ u)
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
    (natrecᵤ A t u v) →
      natrecᵤ A (Usage-restrictions-satisfied-𝟙ᵐ→ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
        (Usage-restrictions-satisfied-𝟙ᵐ→ v)
    Uᵤ →
      Uᵤ
    (Idᵤ ok A t u) →
      Idᵤ ok A (Usage-restrictions-satisfied-𝟙ᵐ→ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
    (Id₀ᵤ ok A t u) →
      Id₀ᵤ ok A t u
    rflᵤ →
      rflᵤ
    (Jᵤ _ A t B u v w) →
      Jᵤ-generalised A (Usage-restrictions-satisfied-𝟙ᵐ→ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ B)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
        (Usage-restrictions-satisfied-𝟙ᵐ→ v)
        (Usage-restrictions-satisfied-𝟙ᵐ→ w)
    (Jᵤ′ ≡some A t B u v w) →
      case singleton $ erased-matches-for-J 𝟘ᵐ of λ where
        (not-none _ , ≡not-none) →
          Jᵤ′-generalised ≡not-none A
            (Usage-restrictions-satisfied-→𝟘ᵐ t)
            (Usage-restrictions-satisfied-𝟙ᵐ→ B)
            (Usage-restrictions-satisfied-𝟙ᵐ→ u)
            (Usage-restrictions-satisfied-→𝟘ᵐ v)
            (Usage-restrictions-satisfied-→𝟘ᵐ w)
        (none , ≡none) →
          case
            trans (sym ≡some)
              (≤ᵉᵐ→≡none→≡none erased-matches-for-J-≤ᵉᵐ ≡none)
          of λ ()
    (J₀ᵤ ≡all A t B u v w) →
      J₀ᵤ (≤ᵉᵐ→≡all→≡all erased-matches-for-J-≤ᵉᵐ ≡all) A t B
        (Usage-restrictions-satisfied-𝟙ᵐ→ u) v w
    (Kᵤ _ A t B u v) →
      Kᵤ-generalised A (Usage-restrictions-satisfied-𝟙ᵐ→ t)
        (Usage-restrictions-satisfied-𝟙ᵐ→ B)
        (Usage-restrictions-satisfied-𝟙ᵐ→ u)
        (Usage-restrictions-satisfied-𝟙ᵐ→ v)
    (Kᵤ′ ≡some A t B u v) →
      case singleton $ erased-matches-for-K 𝟘ᵐ of λ where
        (not-none _ , ≡not-none) →
          Kᵤ′-generalised ≡not-none A
            (Usage-restrictions-satisfied-→𝟘ᵐ t)
            (Usage-restrictions-satisfied-𝟙ᵐ→ B)
            (Usage-restrictions-satisfied-𝟙ᵐ→ u)
            (Usage-restrictions-satisfied-→𝟘ᵐ v)
        (none , ≡none) →
          case
            trans (sym ≡some)
              (≤ᵉᵐ→≡none→≡none erased-matches-for-K-≤ᵉᵐ ≡none)
          of λ ()
    (K₀ᵤ ≡all A t B u v) →
      K₀ᵤ (≤ᵉᵐ→≡all→≡all erased-matches-for-K-≤ᵉᵐ ≡all) A t B
        (Usage-restrictions-satisfied-𝟙ᵐ→ u) v
    ([]-congᵤ A t u v) →
      []-congᵤ A t u v

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
    (emptyrecₘ ▸t ▸A) →
      emptyrecᵤ (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
    Unitₘ →
      Unitᵤ
    starʷₘ →
      starᵤ
    (starˢₘ _) →
      starᵤ
    (unitrecₘ ▸t ▸u ▸A ok) →
      unitrecᵤ ok
        (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
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
    (natrecₘ ▸t ▸u ▸v ▸A) →
      natrecᵤ (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    (natrec-no-nrₘ ▸t ▸u ▸v ▸A _ _ _ _) →
      natrecᵤ (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    Uₘ →
      Uᵤ
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
    (Jₘ ok ▸A ▸t ▸B ▸u ▸v ▸w) →
      Jᵤ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
        (▸→Usage-restrictions-satisfied ▸w)
    (Jₘ′ ok ▸A ▸t ▸B ▸u ▸v ▸w) →
      Jᵤ′ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
        (▸→Usage-restrictions-satisfied ▸w)
    (J₀ₘ ok ▸A ▸t ▸B ▸u ▸v ▸w) →
      J₀ᵤ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
        (▸→Usage-restrictions-satisfied ▸w)
    (Kₘ ok ▸A ▸t ▸B ▸u ▸v) →
      Kᵤ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    (Kₘ′ ok ▸A ▸t ▸B ▸u ▸v) →
      Kᵤ′ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    (K₀ₘ ok ▸A ▸t ▸B ▸u ▸v) →
      K₀ᵤ ok (▸→Usage-restrictions-satisfied ▸A)
        (▸→Usage-restrictions-satisfied ▸t)
        (▸→Usage-restrictions-satisfied ▸B)
        (▸→Usage-restrictions-satisfied ▸u)
        (▸→Usage-restrictions-satisfied ▸v)
    ([]-congₘ ▸A ▸t ▸u ▸v) →
      []-congᵤ (▸→Usage-restrictions-satisfied ▸A)
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
    open import Graded.Modality.Dedicated-nr.Instance

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
      (natrecᵤ {p} {q} {r} A-ok t-ok u-ok v-ok) →
        let u-lemma =
              sub (lemma u-ok) $ begin
                𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
                𝟘ᶜ                  ∎
            A-lemma =
              sub (lemma-𝟘ᵐ? A-ok) $ begin
                𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
                𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
                𝟘ᶜ                ∎
        in case dedicated-nr? of λ where
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
      (emptyrecᵤ {p} A-ok t-ok) →
        sub (emptyrecₘ (lemma t-ok) (lemma-𝟘ᵐ? A-ok)) $ begin
          𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
          p ·ᶜ 𝟘ᶜ  ∎
      (unitrecᵤ {p} {q} ok A-ok t-ok u-ok) →
        sub (unitrecₘ (lemma t-ok) (lemma u-ok)
               (sub (lemma-𝟘ᵐ? A-ok) $ begin
                  𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ (𝟘ᵐ?≡𝟘ᵐ {ok = 𝟘ᵐ-ok})) ⟩
                  𝟘ᶜ ∙ 𝟘 · q        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
                  𝟘ᶜ                ∎)
               ok) $ begin
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
      (Jᵤ {p} {q} not-ok A-ok t-ok B-ok u-ok v-ok w-ok) → sub
        (Jₘ not-ok
           (lemma-𝟘ᵐ? A-ok)
           (lemma t-ok)
           (sub (lemma B-ok) $ begin
              𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ                  ∎)
           (lemma u-ok)
           (lemma v-ok)
           (lemma w-ok))
        (begin
           𝟘ᶜ                                 ≈˘⟨ ω·ᶜ⋀ᶜ⁵𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎)
      (Jᵤ′ {p} {q} ok A-ok t-ok B-ok u-ok v-ok w-ok) → sub
        (Jₘ′ ok
           (lemma-𝟘ᵐ? A-ok)
           (lemma t-ok)
           (sub (lemma B-ok) $ begin
              𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ                  ∎)
           (lemma u-ok)
           (lemma v-ok)
           (lemma w-ok))
        (begin
           𝟘ᶜ                                 ≈˘⟨ ω·ᶜ⋀ᶜ⁵𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎)
      (J₀ᵤ {p} {q} ok A-ok t-ok B-ok u-ok v-ok w-ok) →
        J₀ₘ ok
          (lemma-𝟘ᵐ? A-ok)
          (lemma-𝟘ᵐ? t-ok)
          (sub (lemma-𝟘ᵐ? B-ok) $ begin
             𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p ∙ ⌜ 𝟘ᵐ? ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
             𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q              ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ                              ∎)
          (lemma u-ok)
          (lemma-𝟘ᵐ? v-ok)
          (lemma-𝟘ᵐ? w-ok)
      (Kᵤ {p} not-ok A-ok t-ok B-ok u-ok v-ok) → sub
        (Kₘ not-ok
           (lemma-𝟘ᵐ? A-ok)
           (lemma t-ok)
           (sub (lemma B-ok) $ begin
              𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ          ∎)
           (lemma u-ok)
           (lemma v-ok))
        (begin
           𝟘ᶜ                           ≈˘⟨ ω·ᶜ⋀ᶜ⁴𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎)
      (Kᵤ′ {p} ok A-ok t-ok B-ok u-ok v-ok) → sub
        (Kₘ′ ok
           (lemma-𝟘ᵐ? A-ok)
           (lemma t-ok)
           (sub (lemma B-ok) $ begin
              𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ          ∎)
           (lemma u-ok)
           (lemma v-ok))
        (begin
           𝟘ᶜ                           ≈˘⟨ ω·ᶜ⋀ᶜ⁴𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎)
      (K₀ᵤ {p} ok A-ok t-ok B-ok u-ok v-ok) →
        K₀ₘ ok
          (lemma-𝟘ᵐ? A-ok)
          (lemma-𝟘ᵐ? t-ok)
          (sub (lemma-𝟘ᵐ? B-ok) $ begin
             𝟘ᶜ ∙ ⌜ 𝟘ᵐ? ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ ·-congʳ (cong ⌜_⌝ 𝟘ᵐ?≡𝟘ᵐ′) ⟩
             𝟘ᶜ ∙ 𝟘 · p        ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ                ∎)
          (lemma u-ok)
          (lemma-𝟘ᵐ? v-ok)
      ([]-congᵤ A-ok t-ok u-ok v-ok) →
        []-congₘ
          (lemma-𝟘ᵐ? A-ok)
          (lemma-𝟘ᵐ? t-ok)
          (lemma-𝟘ᵐ? u-ok)
          (lemma-𝟘ᵐ? v-ok)
      (varᵤ {x}) →
        sub var $ begin
          𝟘ᶜ          ≡˘⟨ 𝟘ᶜ,≔𝟘 ⟩
          𝟘ᶜ , x ≔ 𝟘  ∎
      Uᵤ →
        Uₘ
      ℕᵤ →
        ℕₘ
      Emptyᵤ →
        Emptyₘ
      Unitᵤ →
        Unitₘ
      zeroᵤ →
        zeroₘ
      starᵤ →
        starₘ
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
      (natrecᵤ A-ok t-ok u-ok v-ok) →
        case dedicated-nr? of λ where
          does-have-nr →
            sub
              (natrecₘ {δ = 𝟘ᶜ} {θ = 𝟘ᶜ} (lemma₀ t-ok) (lemma u-ok)
                 (lemma₀ v-ok) (lemma A-ok))
              (≈ᶜ-trivial 𝟙≡𝟘)
          does-not-have-nr →
            natrec-no-nrₘ {δ = 𝟘ᶜ} {θ = 𝟘ᶜ} (lemma₀ t-ok) (lemma u-ok)
              (lemma₀ v-ok) (lemma A-ok) (≈ᶜ-trivial 𝟙≡𝟘)
              (λ _ → ≈ᶜ-trivial 𝟙≡𝟘) (≈ᶜ-trivial 𝟙≡𝟘) (≈ᶜ-trivial 𝟙≡𝟘)
      (emptyrecᵤ A-ok t-ok) →
        sub (emptyrecₘ (lemma₀ t-ok) (lemma₀ A-ok)) (≈ᶜ-trivial 𝟙≡𝟘)
      (unitrecᵤ ok A-ok t-ok u-ok) →
        sub
          (unitrecₘ {η = 𝟘ᶜ} (lemma₀ t-ok) (lemma₀ u-ok) (lemma A-ok)
             ok)
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Idᵤ not-erased A-ok t-ok u-ok) →
        sub
          (Idₘ not-erased (lemma₀ A-ok) (lemma₀ t-ok) (lemma₀ u-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Id₀ᵤ erased A-ok t-ok u-ok) →
        sub
          (Id₀ₘ erased (lemma₀ A-ok) (lemma₀ t-ok) (lemma₀ u-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Jᵤ not-ok A-ok t-ok B-ok u-ok v-ok w-ok) →
        sub
          (Jₘ {γ₃ = 𝟘ᶜ} not-ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok) (lemma₀ w-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Jᵤ′ ok A-ok t-ok B-ok u-ok v-ok w-ok) →
        sub
          (Jₘ′ {γ₃ = 𝟘ᶜ} ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok) (lemma₀ w-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (J₀ᵤ ok A-ok t-ok B-ok u-ok v-ok w-ok) →
        sub
          (J₀ₘ {γ₃ = 𝟘ᶜ} ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok) (lemma₀ w-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Kᵤ not-ok A-ok t-ok B-ok u-ok v-ok) →
        sub
          (Kₘ {γ₃ = 𝟘ᶜ} not-ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (Kᵤ′ ok A-ok t-ok B-ok u-ok v-ok) →
        sub
          (Kₘ′ {γ₃ = 𝟘ᶜ} ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      (K₀ᵤ ok A-ok t-ok B-ok u-ok v-ok) →
        sub
          (K₀ₘ {γ₃ = 𝟘ᶜ} ok (lemma₀ A-ok) (lemma₀ t-ok) (lemma B-ok)
             (lemma₀ u-ok) (lemma₀ v-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      ([]-congᵤ A-ok t-ok u-ok v-ok) →
        sub
          ([]-congₘ (lemma₀ A-ok) (lemma₀ t-ok) (lemma₀ u-ok)
             (lemma₀ v-ok))
          (≈ᶜ-trivial 𝟙≡𝟘)
      varᵤ →
        sub var (≈ᶜ-trivial 𝟙≡𝟘)
      Uᵤ →
        sub Uₘ (≈ᶜ-trivial 𝟙≡𝟘)
      ℕᵤ →
        sub ℕₘ (≈ᶜ-trivial 𝟙≡𝟘)
      Emptyᵤ →
        sub Emptyₘ (≈ᶜ-trivial 𝟙≡𝟘)
      Unitᵤ →
        sub Unitₘ (≈ᶜ-trivial 𝟙≡𝟘)
      zeroᵤ →
        sub zeroₘ (≈ᶜ-trivial 𝟙≡𝟘)
      starᵤ →
        sub starₘ (≈ᶜ-trivial 𝟙≡𝟘)
      rflᵤ →
        sub rflₘ (≈ᶜ-trivial 𝟙≡𝟘)

opaque

  -- An alternative characterisation of γ ▸[ m ] t for trivial
  -- modalities.

  Trivial→▸⇔ : Trivial → γ ▸[ m ] t ⇔ Usage-restrictions-satisfied m t
  Trivial→▸⇔ 𝟙≡𝟘 =
      ▸→Usage-restrictions-satisfied
    , Trivial→Usage-restrictions-satisfied→▸ 𝟙≡𝟘
