------------------------------------------------------------------------
-- Atomic neutral terms
------------------------------------------------------------------------

open import Definition.Typed.Variant

module Definition.Untyped.Neutral.Atomic
  {a}
  (M : Set a)
  (type-variant : Type-variant)
  where

open Type-variant type-variant

open import Definition.Untyped M
open import Definition.Untyped.Inversion M
open import Definition.Untyped.Neutral M type-variant

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Relation

private variable
  P             : Set _
  n             : Nat
  x             : Fin _
  A B l t u v w : Term _
  ρ             : Wk _ _
  s             : Strength
  p q r         : M

------------------------------------------------------------------------
-- The type

-- Non-atomic t holds if t is an application of _supᵘ_.

data Non-atomic {n : Nat} : Term n → Set a where
  is-supᵘ : Non-atomic (t supᵘ u)

-- A term is atomic neutral if it is neutral and not non-atomic.

data Neutralᵃ (t : Term n) : Set a where
  ne : Neutral t → ¬ Non-atomic t → Neutralᵃ t

------------------------------------------------------------------------
-- Some simple properties

opaque

  -- One can derive anything from Neutralᵃ (t supᵘ u).

  Neutralᵃ-supᵘ→ : ∀ {a} {A : Set a} → Neutralᵃ (t supᵘ u) → A
  Neutralᵃ-supᵘ→ (ne _ not-sup) = ⊥-elim (not-sup is-supᵘ)

opaque

  -- Atomic neutrals are neutral.

  ne⁻ : Neutralᵃ t → Neutral t
  ne⁻ (ne n _) = n

opaque

  -- Atomic neutrals are WHNFs.

  ne! : Neutralᵃ t → Whnf t
  ne! = ne ∘→ ne⁻

opaque

  -- A weakening and strengthening lemma for Non-atomic.

  wkNon-atomic : Non-atomic t ⇔ Non-atomic (wk ρ t)
  wkNon-atomic =
    (λ { is-supᵘ → is-supᵘ }) ,
    flip from refl
    where
    from : Non-atomic t → wk ρ u ≡ t → Non-atomic u
    from is-supᵘ eq =
      case wk-supᵘ eq of λ {
        (_ , _ , refl , _ , _) →
      is-supᵘ }

opaque

  -- Weakening for Neutralᵃ.

  wkNeutralᵃ : Neutralᵃ t → Neutralᵃ (wk ρ t)
  wkNeutralᵃ (ne n ok) = ne (wkNeutral _ n) (ok ∘→ wkNon-atomic .proj₂)

------------------------------------------------------------------------
-- Variants of most of the constructors of Neutral

opaque

  -- A variant of var for Neutralᵃ.

  varᵃ : Neutralᵃ (var x)
  varᵃ = ne (var _) (λ ())

opaque

  -- A variant of lowerₙ for Neutralᵃ.

  lowerₙᵃ : Neutralᵃ t → Neutralᵃ (lower t)
  lowerₙᵃ (ne n _) = ne (lowerₙ n) (λ ())

opaque

  -- A variant of emptyrecₙ for Neutralᵃ.

  emptyrecₙᵃ : Neutralᵃ t → Neutralᵃ (emptyrec p A t)
  emptyrecₙᵃ (ne n _) = ne (emptyrecₙ n) (λ ())

opaque

  -- A variant of unitrecₙ for Neutralᵃ.

  unitrecₙᵃ : ¬ Unitʷ-η → Neutralᵃ t → Neutralᵃ (unitrec p q A t u)
  unitrecₙᵃ no-η (ne n _) = ne (unitrecₙ no-η n) (λ ())

opaque

  -- A variant of ∘ₙ for Neutralᵃ.

  ∘ₙᵃ : Neutralᵃ t → Neutralᵃ (t ∘⟨ p ⟩ u)
  ∘ₙᵃ (ne n _) = ne (∘ₙ n) (λ ())

opaque

  -- A variant of fstₙ for Neutralᵃ.

  fstₙᵃ : Neutralᵃ t → Neutralᵃ (fst p t)
  fstₙᵃ (ne n _) = ne (fstₙ n) (λ ())

opaque

  -- A variant of sndₙ for Neutralᵃ.

  sndₙᵃ : Neutralᵃ t → Neutralᵃ (snd p t)
  sndₙᵃ (ne n _) = ne (sndₙ n) (λ ())

opaque

  -- A variant of prodrecₙ for Neutralᵃ.

  prodrecₙᵃ : Neutralᵃ t → Neutralᵃ (prodrec r p q A t u)
  prodrecₙᵃ (ne n _) = ne (prodrecₙ n) (λ ())

opaque

  -- A variant of natrecₙ for Neutralᵃ.

  natrecₙᵃ : Neutralᵃ v → Neutralᵃ (natrec p q r A t u v)
  natrecₙᵃ (ne n _) = ne (natrecₙ n) (λ ())

opaque

  -- A variant of Jₙ for Neutralᵃ.

  Jₙᵃ : Neutralᵃ w → Neutralᵃ (J p q A t B u v w)
  Jₙᵃ (ne n _) = ne (Jₙ n) (λ ())

opaque

  -- A variant of Kₙ for Neutralᵃ.

  Kₙᵃ : Neutralᵃ v → Neutralᵃ (K p A t B u v)
  Kₙᵃ (ne n _) = ne (Kₙ n) (λ ())

opaque

  -- A variant of []-congₙ for Neutralᵃ.

  []-congₙᵃ : Neutralᵃ v → Neutralᵃ ([]-cong s l A t u v)
  []-congₙᵃ (ne n _) = ne ([]-congₙ n) (λ ())

------------------------------------------------------------------------
-- A variant of Function

-- Atomic "functions".

data Functionᵃ {n : Nat} : Term n → Set a where
  lamₙ : Functionᵃ (lam p t)
  ne   : Neutralᵃ t → Functionᵃ t

opaque

  -- A characterisation lemma for Functionᵃ.

  Functionᵃ⇔ : Functionᵃ t ⇔ (Function t × ¬ Non-atomic t)
  Functionᵃ⇔ =
    (λ where
       lamₙ                → lamₙ , λ ()
       (ne (ne t-ne t-nn)) → ne t-ne , t-nn) ,
    (λ where
       (lamₙ    , _)    → lamₙ
       (ne t-ne , t-nn) → ne (ne t-ne t-nn))

opaque

  -- Conversion to Function.

  Functionᵃ→ : Functionᵃ t → Function t
  Functionᵃ→ = proj₁ ∘→ Functionᵃ⇔ .proj₁

opaque

  -- Atomic functions are WHNFs.

  Functionᵃ→Whnf : Functionᵃ t → Whnf t
  Functionᵃ→Whnf = functionWhnf ∘→ Functionᵃ→

opaque

  -- A weakening lemma.

  wkFunctionᵃ : Functionᵃ t → Functionᵃ (wk ρ t)
  wkFunctionᵃ =
    Functionᵃ⇔ .proj₂ ∘→
    Σ.map (wkFunction _) (_∘→ wkNon-atomic .proj₂) ∘→
    Functionᵃ⇔ .proj₁

------------------------------------------------------------------------
-- A variant of Product

-- Atomic products.

data Productᵃ {n : Nat} : Term n → Set a where
  prodₙ : Productᵃ (prod s p t u)
  ne    : Neutralᵃ t → Productᵃ t

opaque

  -- A characterisation lemma for Productᵃ.

  Productᵃ⇔ : Productᵃ t ⇔ (Product t × ¬ Non-atomic t)
  Productᵃ⇔ =
    (λ where
       prodₙ               → prodₙ , λ ()
       (ne (ne t-ne t-nn)) → ne t-ne , t-nn) ,
    (λ where
       (prodₙ    , _)   → prodₙ
       (ne t-ne , t-nn) → ne (ne t-ne t-nn))

opaque

  -- Conversion to Product.

  Productᵃ→ : Productᵃ t → Product t
  Productᵃ→ = proj₁ ∘→ Productᵃ⇔ .proj₁

opaque

  -- Atomic products are WHNFs.

  Productᵃ→Whnf : Productᵃ t → Whnf t
  Productᵃ→Whnf = productWhnf ∘→ Productᵃ→

-- A weakening lemma.

wkProductᵃ : Productᵃ t → Productᵃ (wk ρ t)
wkProductᵃ prodₙ     = prodₙ
wkProductᵃ (ne t-ne) = ne (wkNeutralᵃ t-ne)

------------------------------------------------------------------------
-- A variant of Identity

-- Atomic identities.

data Identityᵃ {n : Nat} : Term n → Set a where
  rflₙ : Identityᵃ rfl
  ne   : Neutralᵃ t → Identityᵃ t

-- A non-dependent eliminator for Identityᵃ. Note that the argument
-- of ne is thrown away.

Identityᵃ-rec : Identityᵃ t → P → P → P
Identityᵃ-rec rflₙ   r n = r
Identityᵃ-rec (ne _) r n = n

opaque

  -- A characterisation lemma for Identityᵃ.

  Identityᵃ⇔ : Identityᵃ t ⇔ (Identity t × ¬ Non-atomic t)
  Identityᵃ⇔ =
    (λ where
       rflₙ                → rflₙ , λ ()
       (ne (ne t-ne t-nn)) → ne t-ne , t-nn) ,
    (λ where
       (rflₙ    , _)    → rflₙ
       (ne t-ne , t-nn) → ne (ne t-ne t-nn))

opaque

  -- Conversion to Identity.

  Identityᵃ→ : Identityᵃ t → Identity t
  Identityᵃ→ = proj₁ ∘→ Identityᵃ⇔ .proj₁

opaque

  -- Atomic identities are WHNFs.

  Identityᵃ→Whnf : Identityᵃ t → Whnf t
  Identityᵃ→Whnf = identityWhnf ∘→ Identityᵃ→

opaque

  -- A weakening lemma.

  wkIdentityᵃ : Identityᵃ t → Identityᵃ (wk ρ t)
  wkIdentityᵃ =
    Identityᵃ⇔ .proj₂ ∘→
    Σ.map wkIdentity (_∘→ wkNon-atomic .proj₂) ∘→
    Identityᵃ⇔ .proj₁
