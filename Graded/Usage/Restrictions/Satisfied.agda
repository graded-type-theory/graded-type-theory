------------------------------------------------------------------------
-- Usage-restrictions-satisfied
------------------------------------------------------------------------

import Graded.Modality
import Graded.Mode
open import Graded.Usage.Restrictions

module Graded.Usage.Restrictions.Satisfied
  {a a′} {M : Set a} {Mode : Set a′}
  (open Graded.Modality M)
  {𝕄 : Modality}
  (open Graded.Mode Mode 𝕄)
  {𝐌 : IsMode}
  (R : Usage-restrictions 𝕄 𝐌)
  where

open Modality 𝕄
open IsMode 𝐌
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties 𝕄
open import Graded.Usage R
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions.Natrec 𝕄
open import Graded.Usage.Restrictions.Instance R
open import Graded.Usage.Properties R

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
  α l n       : Nat
  x           : Fin _
  A B t u v w : Term _
  p q r       : M
  γ           : Conₘ _
  s           : Strength
  b           : BinderMode
  m m′        : Mode
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
  defnᵤ :
    Usage-restrictions-satisfied m (defn α)
  Emptyᵤ :
    Usage-restrictions-satisfied m Empty
  emptyrecᵤ :
    Emptyrec-allowed m p →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m (emptyrec p A t)
  Unitᵤ :
    Usage-restrictions-satisfied m (Unit s l)
  starᵤ :
    Usage-restrictions-satisfied m (star s l)
  unitrecᵤ :
    Unitrec-allowed m p q →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (unitrec l p q A t u)
  ΠΣᵤ :
    Usage-restrictions-satisfied m A →
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
    Usage-restrictions-satisfied 𝟘ᵐ A →
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
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (natrec p q r A t u v)
  Uᵤ :
    Usage-restrictions-satisfied m (U l)
  Idᵤ :
    ¬ Id-erased →
    Usage-restrictions-satisfied m A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m (Id A t u)
  Id₀ᵤ :
    Id-erased →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied 𝟘ᵐ t →
    Usage-restrictions-satisfied 𝟘ᵐ u →
    Usage-restrictions-satisfied m (Id A t u)
  rflᵤ :
    Usage-restrictions-satisfied m rfl
  Jᵤ :
    erased-matches-for-J m ≤ᵉᵐ some →
    (erased-matches-for-J m ≡ some → ¬ (p ≡ 𝟘 × q ≡ 𝟘)) →
    Usage-restrictions-satisfied 𝟘ᵐ A →
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
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied 𝟘ᵐ t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ v →
    Usage-restrictions-satisfied 𝟘ᵐ w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  J₀ᵤ₂ :
    erased-matches-for-J m ≡ all →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied 𝟘ᵐ t →
    Usage-restrictions-satisfied 𝟘ᵐ B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ v →
    Usage-restrictions-satisfied 𝟘ᵐ w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  Kᵤ :
    erased-matches-for-K m ≤ᵉᵐ some →
    (erased-matches-for-K m ≡ some → p ≢ 𝟘) →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (K p A t B u v)
  K₀ᵤ₁ :
    erased-matches-for-K m ≡ some →
    p ≡ 𝟘 →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied 𝟘ᵐ t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ v →
    Usage-restrictions-satisfied m (K p A t B u v)
  K₀ᵤ₂ :
    erased-matches-for-K m ≡ all →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied 𝟘ᵐ t →
    Usage-restrictions-satisfied 𝟘ᵐ B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ v →
    Usage-restrictions-satisfied m (K p A t B u v)
  []-congᵤ :
    []-cong-allowed-mode s m →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied 𝟘ᵐ t →
    Usage-restrictions-satisfied 𝟘ᵐ u →
    Usage-restrictions-satisfied 𝟘ᵐ v →
    Usage-restrictions-satisfied m ([]-cong s A t u v)

------------------------------------------------------------------------
-- Usage-restrictions-satisfied-≤ᵐ and some related definitions

opaque mutual

  -- A special case of Usage-restrictions-satisfied-≤ᵐ for modes
  -- scaled by a grade.

  Usage-restrictions-satisfied-≤ᵐ-ᵐ· :
    m ≤ᵐ m′ →
    Usage-restrictions-satisfied (m ᵐ· p) t →
    Usage-restrictions-satisfied (m′ ᵐ· p) t
  Usage-restrictions-satisfied-≤ᵐ-ᵐ· m≤m′ =
    Usage-restrictions-satisfied-≤ᵐ (ᵐ·-monotoneˡ m≤m′)

  -- If Usage-restrictions-satisfied holds for any mode and the
  -- term t, then the predicate holds for the mode 𝟘ᵐ.

  Usage-restrictions-satisfied-→𝟘ᵐ :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied 𝟘ᵐ t
  Usage-restrictions-satisfied-→𝟘ᵐ =
    Usage-restrictions-satisfied-≤ᵐ ≤𝟘ᵐ

  -- A generalisation of Jᵤ: erased-matches-for-J m ≡ none has been
  -- removed.

  Jᵤ-generalised :
    Usage-restrictions-satisfied 𝟘ᵐ A →
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
    J₀ᵤ₁ ≡some refl refl A (Usage-restrictions-satisfied-→𝟘ᵐ t)
      B u (Usage-restrictions-satisfied-→𝟘ᵐ v)
      (Usage-restrictions-satisfied-→𝟘ᵐ w)
  … | is-all ≡all =
    J₀ᵤ₂ ≡all A (Usage-restrictions-satisfied-→𝟘ᵐ t)
      (Usage-restrictions-satisfied-→𝟘ᵐ B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ v)
      (Usage-restrictions-satisfied-→𝟘ᵐ w)

  -- A generalisation of J₀ᵤ₁.

  J₀ᵤ₁-generalised :
    erased-matches-for-J m ≡ not-none sem →
    p ≡ 𝟘 →
    q ≡ 𝟘 →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied 𝟘ᵐ t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ v →
    Usage-restrictions-satisfied 𝟘ᵐ w →
    Usage-restrictions-satisfied m (J p q A t B u v w)
  J₀ᵤ₁-generalised {m} ≡not-none refl refl A t B u v w
    with erased-matches-for-J m in ok
  … | none = case ≡not-none of λ ()
  … | some =
    J₀ᵤ₁ ok refl refl A t B u v w
  … | all =
    J₀ᵤ₂ ok A (Usage-restrictions-satisfied-→𝟘ᵐ t)
      (Usage-restrictions-satisfied-→𝟘ᵐ B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ v)
      (Usage-restrictions-satisfied-→𝟘ᵐ w)

  -- A generalisation of Kᵤ: erased-matches-for-K m ≡ none has been
  -- removed.

  Kᵤ-generalised :
    -- m ≤ᵐ m′ →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied m v →
    Usage-restrictions-satisfied m (K p A t B u v)
  Kᵤ-generalised {m} {p} A t B u v with K-view p m
  … | is-other ≤some ≢𝟘 =
    Kᵤ ≤some ≢𝟘 A t B u v
  … | is-some-yes ≡some refl =
    K₀ᵤ₁ ≡some refl A (Usage-restrictions-satisfied-→𝟘ᵐ t) B u
      (Usage-restrictions-satisfied-→𝟘ᵐ v)
  … | is-all ≡all =
    K₀ᵤ₂ ≡all A (Usage-restrictions-satisfied-→𝟘ᵐ t)
      (Usage-restrictions-satisfied-→𝟘ᵐ B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ v)

  -- A generalisation of K₀ᵤ₁.

  K₀ᵤ₁-generalised :
    erased-matches-for-K m ≡ not-none sem →
    p ≡ 𝟘 →
    Usage-restrictions-satisfied 𝟘ᵐ A →
    Usage-restrictions-satisfied 𝟘ᵐ t →
    Usage-restrictions-satisfied m B →
    Usage-restrictions-satisfied m u →
    Usage-restrictions-satisfied 𝟘ᵐ v →
    Usage-restrictions-satisfied m (K p A t B u v)
  K₀ᵤ₁-generalised {m} hyp refl A t B u v
    with erased-matches-for-K m in ok
  … | none =
    case hyp of λ ()
  … | some =
    K₀ᵤ₁ ok refl A t B u v
  … | all =
    K₀ᵤ₂ ok A (Usage-restrictions-satisfied-→𝟘ᵐ t)
      (Usage-restrictions-satisfied-→𝟘ᵐ B) u
      (Usage-restrictions-satisfied-→𝟘ᵐ v)

  -- If Usage-restrictions-satisfied holds for mode m and the
  -- term t, then the predicate holds for any larger mode.

  Usage-restrictions-satisfied-≤ᵐ :
    m ≤ᵐ m′ →
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied m′ t
  Usage-restrictions-satisfied-≤ᵐ {m′} m≤m′ = λ where
    varᵤ →
      varᵤ
    defnᵤ →
      defnᵤ
    Emptyᵤ →
      Emptyᵤ
    (emptyrecᵤ ok A t) →
      emptyrecᵤ (Emptyrec-allowed-upwards-closed ok m≤m′) A
        (Usage-restrictions-satisfied-≤ᵐ-ᵐ· m≤m′ t)
    Unitᵤ → Unitᵤ
    starᵤ → starᵤ
    (unitrecᵤ ok A t u) →
      unitrecᵤ (Unitrec-allowed-upwards-closed ok m≤m′) A
        (Usage-restrictions-satisfied-≤ᵐ-ᵐ· m≤m′ t)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ u)
    (ΠΣᵤ A B) →
      ΠΣᵤ (Usage-restrictions-satisfied-≤ᵐ m≤m′ A)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ B)
    (lamᵤ t) →
      lamᵤ (Usage-restrictions-satisfied-≤ᵐ m≤m′ t)
    (∘ᵤ t u) →
      ∘ᵤ (Usage-restrictions-satisfied-≤ᵐ m≤m′ t)
        (Usage-restrictions-satisfied-≤ᵐ-ᵐ· m≤m′ u)
    (prodᵤ t u) →
      prodᵤ (Usage-restrictions-satisfied-≤ᵐ-ᵐ· m≤m′ t)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ u)
    (prodrecᵤ ok A t u) →
      prodrecᵤ
        (Prodrec-allowed-upwards-closed ok m≤m′) A
        (Usage-restrictions-satisfied-≤ᵐ-ᵐ· m≤m′ t)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ u)
    (fstᵤ t) →
      fstᵤ (Usage-restrictions-satisfied-≤ᵐ m≤m′ t)
    (sndᵤ t) →
      sndᵤ (Usage-restrictions-satisfied-≤ᵐ m≤m′ t)
    ℕᵤ → ℕᵤ
    zeroᵤ → zeroᵤ
    (sucᵤ t) →
      sucᵤ (Usage-restrictions-satisfied-≤ᵐ m≤m′ t)
    (natrecᵤ ok A z s n) →
      natrecᵤ ok A (Usage-restrictions-satisfied-≤ᵐ m≤m′ z)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ s)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ n)
    Uᵤ → Uᵤ
    (Idᵤ ok A t u) →
      Idᵤ ok (Usage-restrictions-satisfied-≤ᵐ m≤m′ A)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ t)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ u)
    (Id₀ᵤ ok A t u) →
      Id₀ᵤ ok A t u
    rflᵤ → rflᵤ
    (Jᵤ _ _ A t B u v w) →
      Jᵤ-generalised A (Usage-restrictions-satisfied-≤ᵐ m≤m′ t)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ B)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ u)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ v)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ w)
    (J₀ᵤ₁ ≡some p≡𝟘 q≡𝟘 A t B u v w) →
      case singleton $ erased-matches-for-J m′ of λ where
        (not-none _ , ≡not-none) →
          J₀ᵤ₁-generalised ≡not-none p≡𝟘 q≡𝟘 A t
            (Usage-restrictions-satisfied-≤ᵐ m≤m′ B)
            (Usage-restrictions-satisfied-≤ᵐ m≤m′ u)
            (Usage-restrictions-satisfied-→𝟘ᵐ v)
            (Usage-restrictions-satisfied-→𝟘ᵐ w)
        (none , ≡none) →
          case
            trans (sym ≡some)
              (≤ᵉᵐ→≡none→≡none (erased-matches-for-J-≤ᵉᵐ m≤m′) ≡none)
          of λ ()
    (J₀ᵤ₂ ≡all A t B u v w) →
      J₀ᵤ₂ (subst (λ x → erased-matches-for-J x ≡ all) (sym m≤m′)
             (erased-matches-for-J-all·ᵐ ≡all))
        A t B (Usage-restrictions-satisfied-≤ᵐ m≤m′ u) v w
    (Kᵤ _ _ A t B u v) →
      Kᵤ-generalised A (Usage-restrictions-satisfied-≤ᵐ m≤m′ t)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ B)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ u)
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ v)
    (K₀ᵤ₁ ≡some p≡𝟘 A t B u v) →
      case singleton $ erased-matches-for-K m′ of λ where
        (not-none _ , ≡not-none) →
          K₀ᵤ₁-generalised ≡not-none p≡𝟘 A
            (Usage-restrictions-satisfied-→𝟘ᵐ t)
            (Usage-restrictions-satisfied-≤ᵐ m≤m′ B)
            (Usage-restrictions-satisfied-≤ᵐ m≤m′ u)
            (Usage-restrictions-satisfied-→𝟘ᵐ v)
        (none , ≡none) →
          case
            trans (sym ≡some)
              (≤ᵉᵐ→≡none→≡none (erased-matches-for-K-≤ᵉᵐ m≤m′) ≡none)
          of λ ()
    (K₀ᵤ₂ ≡all A t B u v) →
      K₀ᵤ₂ (≤ᵉᵐ→≡all→≡all (erased-matches-for-K-≤ᵉᵐ m≤m′) ≡all) A t B
        (Usage-restrictions-satisfied-≤ᵐ m≤m′ u) v
    ([]-congᵤ ok A t u v) →
      []-congᵤ ([]-cong-allowed-mode-upwards-closed ok m≤m′) A t u v

opaque

  -- If Usage-restrictions-satisfied holds for the mode 𝟙ᵐ and the
  -- term t, then the predicate holds for any mode.

  Usage-restrictions-satisfied-𝟙ᵐ→ :
    Usage-restrictions-satisfied 𝟙ᵐ t →
    Usage-restrictions-satisfied m t
  Usage-restrictions-satisfied-𝟙ᵐ→ =
    Usage-restrictions-satisfied-≤ᵐ 𝟙ᵐ≤

opaque

  -- Usage-restrictions-satisfied is closed under _ᵐ· p.

  Usage-restrictions-satisfied-ᵐ· :
    Usage-restrictions-satisfied m t →
    Usage-restrictions-satisfied (m ᵐ· p) t
  Usage-restrictions-satisfied-ᵐ· =
    Usage-restrictions-satisfied-≤ᵐ ᵐ·-increasing

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
    defn →
      defnᵤ
    Emptyₘ →
      Emptyᵤ
    (emptyrecₘ ▸t ▸A ok) →
      emptyrecᵤ ok (▸→Usage-restrictions-satisfied ▸A)
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

  -- If the mode structire is not trivial and
  -- Usage-restrictions-satisfied 𝟘ᵐ t holds, then t is
  -- well-resourced with respect to 𝟘ᶜ and 𝟘ᵐ.

  Usage-restrictions-satisfied→▸[𝟘ᵐ] :
    ¬ Trivialᵐ →
    Usage-restrictions-satisfied 𝟘ᵐ t → 𝟘ᶜ ▸[ 𝟘ᵐ ] t
  Usage-restrictions-satisfied→▸[𝟘ᵐ] 𝟙ᵐ≢𝟘ᵐ = lemma
    where
    open CR

    ⌜𝟘ᵐ⌝p≡𝟘 : ⌜ 𝟘ᵐ ⌝ · p ≡ 𝟘
    ⌜𝟘ᵐ⌝p≡𝟘 =
      trans (·-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ)) (·-zeroˡ _)

    lemma :
      Usage-restrictions-satisfied 𝟘ᵐ t →
      𝟘ᶜ ▸[ 𝟘ᵐ ] t

    lemma-ᵐ· :
      Usage-restrictions-satisfied (𝟘ᵐ ᵐ· p) t →
      𝟘ᶜ ▸[ 𝟘ᵐ ᵐ· p ] t
    lemma-ᵐ· =
      ▸-cong (sym ᵐ·-zeroˡ) ∘→
      lemma ∘→
      subst (λ m → Usage-restrictions-satisfied m _) ᵐ·-zeroˡ

    lemma = λ where
      (prodrecᵤ {r} {p} {q} ok A-ok t-ok u-ok) →
        sub (prodrecₘ (lemma-ᵐ· t-ok)
               (sub (lemma u-ok) $ begin
                  𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · r · p ∙ ⌜ 𝟘ᵐ ⌝ · r  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
                  𝟘ᶜ                                ∎)
               (sub (lemma A-ok) $ begin
                  𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
                  𝟘ᶜ                ∎)
               ok) $ begin
          𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
          r ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
          r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
      (ΠΣᵤ {q} A-ok B-ok) →
        sub (ΠΣₘ (lemma A-ok) $ sub (lemma B-ok) $ begin
               𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
               𝟘ᶜ               ∎) $ begin
          𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
      (lamᵤ {p} t-ok) →
        lamₘ $ sub (lemma t-ok) $ begin
          𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
          𝟘ᶜ          ∎
      (∘ᵤ {p} t-ok u-ok) →
        sub (lemma t-ok ∘ₘ lemma-ᵐ· u-ok) $ begin
          𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
          p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ∎
      (prodᵤ {p} {s = 𝕤} t-ok u-ok) →
        sub (prodˢₘ (lemma-ᵐ· t-ok) (lemma u-ok)) $ begin
          𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
          𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
          p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎
      (prodᵤ {p} {s = 𝕨} t-ok u-ok) →
        sub (prodʷₘ (lemma-ᵐ· t-ok) (lemma u-ok)) $ begin
          𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
          p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
      (fstᵤ t-ok) →
        fstₘ 𝟘ᵐ (▸-cong (sym (·ᵐ-zeroˡ _)) (lemma t-ok)) (·ᵐ-zeroˡ _)
          (⊥-elim ∘→ (_$ ⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ))
      (sndᵤ t-ok) →
        sndₘ (lemma t-ok)
      (sucᵤ t-ok) →
        sucₘ (lemma t-ok)
      (natrecᵤ {r} {p} {q} x≤ A-ok t-ok u-ok v-ok) →
        let u-lemma =
              sub (lemma u-ok) $ begin
                𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · p ∙ ⌜ 𝟘ᵐ ⌝ · r  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
                𝟘ᶜ                  ∎
            A-lemma =
              sub (lemma A-ok) $ begin
                𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
                𝟘ᶜ                ∎
        in  case natrec-mode? natrec-mode of λ where
              does-have-nr →
                sub (natrecₘ (lemma t-ok) u-lemma (lemma v-ok) A-lemma) $
                begin
                  𝟘ᶜ                ≈˘⟨ nrᶜ-𝟘ᶜ ⟩
                  nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ  ∎
              does-not-have-nr →
                natrec-no-nrₘ (lemma t-ok) u-lemma (lemma v-ok) A-lemma
                  ≤ᶜ-refl (λ _ → ≤ᶜ-refl) (λ _ → ≤ᶜ-refl) $ begin
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
        sub (emptyrecₘ (lemma-ᵐ· t-ok) (lemma A-ok) ok) $ begin
          𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
          p ·ᶜ 𝟘ᶜ  ∎
      (unitrecᵤ {p} {q} ok A-ok t-ok u-ok) →
        sub (unitrecₘ (lemma-ᵐ· t-ok) (lemma u-ok)
               (sub (lemma A-ok) $ begin
                  𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
                  𝟘ᶜ                ∎)
               ok) $ begin
          𝟘ᶜ             ≈˘⟨ +ᶜ-identityˡ _ ⟩
          𝟘ᶜ +ᶜ 𝟘ᶜ       ≈˘⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
          p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎
      (Idᵤ not-erased A-ok t-ok u-ok) → sub
        (Idₘ not-erased
           (lemma A-ok)
           (lemma t-ok)
           (lemma u-ok))
        (begin
           𝟘ᶜ              ≈˘⟨ ≈ᶜ-trans (+ᶜ-identityˡ _) (+ᶜ-identityˡ _) ⟩
           𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
      (Id₀ᵤ erased A-ok t-ok u-ok) →
        Id₀ₘ erased
          (lemma A-ok)
          (lemma t-ok)
          (lemma u-ok)
      (Jᵤ {p} {q} ok₁ ok₂ A-ok t-ok B-ok u-ok v-ok w-ok) → sub
        (Jₘ ok₁ ok₂
           (lemma A-ok)
           (lemma t-ok)
           (sub (lemma B-ok) $ begin
              𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · p ∙ ⌜ 𝟘ᵐ ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
              𝟘ᶜ                  ∎)
           (lemma u-ok)
           (lemma v-ok)
           (lemma w-ok))
        (begin
           𝟘ᶜ                                 ≈˘⟨ ω·ᶜ+ᶜ⁵𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      (J₀ᵤ₁ ok p≡𝟘 q≡𝟘 A-ok t-ok B-ok u-ok v-ok w-ok) → sub
        (J₀ₘ₁ ok p≡𝟘 q≡𝟘 (lemma A-ok) (lemma t-ok) (lemma B-ok)
           (lemma u-ok) (lemma v-ok) (lemma w-ok))
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      (J₀ᵤ₂ {p} {q} ok A-ok t-ok B-ok u-ok v-ok w-ok) →
        J₀ₘ₂ ok
          (lemma A-ok)
          (lemma t-ok)
          (sub (lemma B-ok) $ begin
             𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · p ∙ ⌜ 𝟘ᵐ ⌝ · q  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
             𝟘ᶜ                            ∎)
          (lemma u-ok)
          (lemma v-ok)
          (lemma w-ok)
      (Kᵤ {p} ok₁ ok₂ A-ok t-ok B-ok u-ok v-ok) → sub
        (Kₘ ok₁ ok₂
           (lemma A-ok)
           (lemma t-ok)
           (sub (lemma B-ok) $ begin
              𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
              𝟘ᶜ          ∎)
           (lemma u-ok)
           (lemma v-ok))
        (begin
           𝟘ᶜ                           ≈˘⟨ ω·ᶜ+ᶜ⁴𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      (K₀ᵤ₁ ok p≡𝟘 A-ok t-ok B-ok u-ok v-ok) → sub
        (K₀ₘ₁ ok p≡𝟘 (lemma A-ok) (lemma t-ok) (lemma B-ok)
           (lemma u-ok) (lemma v-ok))
        (begin
           𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
           ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      (K₀ᵤ₂ {p} ok A-ok t-ok B-ok u-ok v-ok) →
        K₀ₘ₂ ok
          (lemma A-ok)
          (lemma t-ok)
          (sub (lemma B-ok) $ begin
             𝟘ᶜ ∙ ⌜ 𝟘ᵐ ⌝ · p  ≈⟨ ≈ᶜ-refl ∙ ⌜𝟘ᵐ⌝p≡𝟘 ⟩
             𝟘ᶜ                ∎)
          (lemma u-ok)
          (lemma v-ok)
      ([]-congᵤ ok A-ok t-ok u-ok v-ok) →
        []-congₘ
          (lemma A-ok)
          (lemma t-ok)
          (lemma u-ok)
          (lemma v-ok)
          ok
      (varᵤ {x}) →
        sub var $ begin
          𝟘ᶜ               ≡˘⟨ 𝟘ᶜ,≔𝟘 ⟩
          𝟘ᶜ , x ≔ 𝟘       ≈˘⟨ update-congʳ (⌜𝟘ᵐ⌝ 𝟙ᵐ≢𝟘ᵐ) ⟩
          𝟘ᶜ , x ≔ ⌜ 𝟘ᵐ ⌝  ∎
      defnᵤ →
        defn
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

  -- An alternative characterisation of 𝟘ᶜ ▸[ 𝟘ᵐ ] t.

  𝟘ᶜ▸[𝟘ᵐ]⇔ :
    ¬ Trivialᵐ → 𝟘ᶜ ▸[ 𝟘ᵐ ] t ⇔ Usage-restrictions-satisfied 𝟘ᵐ t
  𝟘ᶜ▸[𝟘ᵐ]⇔ 𝟙ᵐ≢𝟘ᵐ =
      ▸→Usage-restrictions-satisfied
    , Usage-restrictions-satisfied→▸[𝟘ᵐ] 𝟙ᵐ≢𝟘ᵐ

opaque

  -- An alternative characterisation of γ ▸[ 𝟘ᵐ ] t.

  ▸[𝟘ᵐ]⇔ :
    ¬ Trivialᵐ →
    γ ▸[ 𝟘ᵐ ] t ⇔
    (γ ≤ᶜ 𝟘ᶜ × Usage-restrictions-satisfied 𝟘ᵐ t)
  ▸[𝟘ᵐ]⇔ 𝟙ᵐ≢𝟘ᵐ =
      (λ ▸t → ▸-𝟘ᵐ 𝟙ᵐ≢𝟘ᵐ ▸t , ▸→Usage-restrictions-satisfied ▸t)
    , (λ (γ≤𝟘 , ok) → sub (Usage-restrictions-satisfied→▸[𝟘ᵐ] 𝟙ᵐ≢𝟘ᵐ ok) γ≤𝟘)

------------------------------------------------------------------------
-- A lemma related to Usage-restrictions-satisfied 𝟘ᵐ

opaque

  -- If certain assumptions holds, then
  -- Usage-restrictions-satisfied 𝟘ᵐ t always holds.

  Usage-restrictions-satisfied-𝟘ᵐ :
    (⦃ no-nr : Nr-not-available-GLB ⦄ →
     ∀ r p → ∃ λ q → Greatest-lower-bound q (nrᵢ r 𝟙 p)) →
    (∀ p → Emptyrec-allowed 𝟘ᵐ p) →
    (∀ p q → Unitrec-allowed 𝟘ᵐ p q) →
    (∀ r p q → Prodrec-allowed 𝟘ᵐ r p q) →
    (∀ p → []-cong-allowed-mode p 𝟘ᵐ) →
    Usage-restrictions-satisfied 𝟘ᵐ t
  Usage-restrictions-satisfied-𝟘ᵐ glb er ur pr bc = lemma _
    where
    mutual

      lemma-ᵐ· : Usage-restrictions-satisfied (𝟘ᵐ ᵐ· p) t
      lemma-ᵐ· =
        subst (λ m → Usage-restrictions-satisfied m _)
          (sym ᵐ·-zeroˡ) (lemma _)

      lemma : (t : Term n) → Usage-restrictions-satisfied 𝟘ᵐ t
      lemma (var _) =
        varᵤ
      lemma (defn _) =
        defnᵤ
      lemma (U _) =
        Uᵤ
      lemma Empty =
        Emptyᵤ
      lemma (emptyrec _ _ _) =
        emptyrecᵤ (er _) (lemma _) lemma-ᵐ·
      lemma (Unit _ _) =
        Unitᵤ
      lemma (star _ _) =
        starᵤ
      lemma (unitrec _ _ _ _ _ _) =
        unitrecᵤ (ur _ _) (lemma _) lemma-ᵐ· (lemma _)
      lemma (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) =
        ΠΣᵤ (lemma _) (lemma _)
      lemma (lam _ _) =
        lamᵤ (lemma _)
      lemma (_ ∘⟨ _ ⟩ _) =
        ∘ᵤ (lemma _) lemma-ᵐ·
      lemma (prod _ _ _ _) =
        prodᵤ lemma-ᵐ· (lemma _)
      lemma (fst _ _) =
        fstᵤ (lemma _)
      lemma (snd _ _) =
        sndᵤ (lemma _)
      lemma (prodrec _ _ _ _ _ _) =
        prodrecᵤ (pr _ _ _) (lemma _) lemma-ᵐ· (lemma _)
      lemma ℕ =
        ℕᵤ
      lemma zero =
        zeroᵤ
      lemma (suc _) =
        sucᵤ (lemma _)
      lemma (natrec _ _ _ _ _ _ _) =
        natrecᵤ (glb _ _) (lemma _) (lemma _) (lemma _) (lemma _)
      lemma (Id _ _ _) with Id-erased?
      … | yes erased =
        Id₀ᵤ erased (lemma _) (lemma _) (lemma _)
      … | no not-erased =
        Idᵤ not-erased (lemma _) (lemma _) (lemma _)
      lemma rfl =
        rflᵤ
      lemma (J _ _ _ _ _ _ _ _) =
        Jᵤ-generalised (lemma _) (lemma _) (lemma _) (lemma _) (lemma _)
          (lemma _)
      lemma (K _ _ _ _ _ _) =
        Kᵤ-generalised (lemma _) (lemma _) (lemma _) (lemma _) (lemma _)
      lemma ([]-cong _ _ _ _ _) =
        []-congᵤ (bc _) (lemma _) (lemma _) (lemma _) (lemma _)

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
        fstₘ 𝟙ᵐ (▸-trivial 𝟙≡𝟘 (lemma t-ok))
          (≡-trivialᵐ (Trivial→Trivialᵐ 𝟙≡𝟘))
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
              (λ _ → ≈ᶜ-trivial 𝟙≡𝟘) (λ _ → ≈ᶜ-trivial 𝟙≡𝟘) (≈ᶜ-trivial 𝟙≡𝟘)
          does-not-have-nr-glb →
            sub (natrec-no-nr-glbₘ {δ = 𝟘ᶜ} {θ = 𝟘ᶜ} {χ = 𝟘ᶜ}
                  (lemma₀ t-ok) (lemma u-ok) (lemma₀ v-ok)
                  (lemma A-ok) (x≤ .proj₂) (GLBᶜ-const (λ _ → nrᵢᶜ-𝟘ᶜ)))
                (≈ᶜ-trivial 𝟙≡𝟘)
      (emptyrecᵤ ok A-ok t-ok) →
        sub (emptyrecₘ (lemma₀ t-ok) (lemma₀ A-ok) ok) (≈ᶜ-trivial 𝟙≡𝟘)
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
      defnᵤ →
        sub defn (≈ᶜ-trivial 𝟙≡𝟘)
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
