------------------------------------------------------------------------
-- Some definitions that are re-exported from
-- Definition.Untyped.Properties but do not depend on that module's
-- module parameter
------------------------------------------------------------------------

module Definition.Untyped.Properties.NotParametrised where

open import Definition.Untyped.NotParametrised

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.Relation
open import Tools.PropositionalEquality
open import Tools.Sum as ⊎

open import Induction
open import Induction.WellFounded

private variable
  α ℓ m n o          : Nat
  A A₁ A₂            : Set _
  P Q                : Nat → Set _
  B B₁ B₂ t t₁ t₂    : A
  f g                : A₁ → A₂
  ∇ ∇₁ ∇₂            : DCon _ _
  Γ                  : Con _ _
  ρ ρ′               : Wk _ _
  ω₁ ω₂              : Opacity _
  x y                : Fin _
  l l₁ l₁′ l₂ l₂′ l₃ : Universe-level
  sm sm₁ sm₂ sm₃     : Level-small
  s s₁ s₂ s₃         : Level-support

------------------------------------------------------------------------
-- Properties of weakening

-- Two weakenings ρ and ρ′ are extensionally equal if they agree on
-- all arguments when interpreted as functions mapping variables to
-- variables.  Formally, they are considered equal iff
--
--   (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
--
-- Intensional (propositional) equality would be too fine.  For
-- instance,
--
--   lift id : Γ∙A ≤ Γ∙A
--
-- is extensionally equal to
--
--   id : Γ∙A ≤ Γ∙A
--
-- but syntactically different.

-- "lift" preserves equality of weakenings.  Or:
-- If two weakenings are equal under wkVar, then they are equal when lifted.

wkVar-lift : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
           → (∀ x → wkVar (lift ρ) x ≡ wkVar (lift ρ′) x)

wkVar-lift eq x0     = refl
wkVar-lift eq (x +1) = cong _+1 (eq x)


wkVar-lifts : (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
            → (∀ n x → wkVar (liftn ρ n) x ≡ wkVar (liftn ρ′ n) x)
wkVar-lifts eq 0 x      = eq x
wkVar-lifts eq (1+ n) x = wkVar-lift (wkVar-lifts eq n) x

-- lift id  is extensionally equal to  id.

wkVar-lift-id : (x : Fin (1+ n)) → wkVar (lift id) x ≡ wkVar id x
wkVar-lift-id x0     = refl
wkVar-lift-id (x +1) = refl

wkVar-lifts-id : (n : Nat) (x : Fin (n + m)) → wkVar (liftn id n) x ≡ wkVar id x
wkVar-lifts-id 0 x           = refl
wkVar-lifts-id (1+ n) x0     = refl
wkVar-lifts-id (1+ n) (x +1) = cong _+1 (wkVar-lifts-id n x)

-- id is the identity renaming.

wkVar-id : (x : Fin n) → wkVar id x ≡ x
wkVar-id x = refl

-- The function wkVar commutes with composition.

wkVar-comp : (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (x : Fin n) → wkVar ρ (wkVar ρ′ x) ≡ wkVar (ρ • ρ′) x
wkVar-comp id       ρ′        x      = refl
wkVar-comp (step ρ) ρ′        x      = cong _+1 (wkVar-comp ρ ρ′ x)
wkVar-comp (lift ρ) id        x      = refl
wkVar-comp (lift ρ) (step ρ′) x      = cong _+1 (wkVar-comp ρ ρ′ x)
wkVar-comp (lift ρ) (lift ρ′) x0     = refl
wkVar-comp (lift ρ) (lift ρ′) (x +1) = cong _+1 (wkVar-comp ρ ρ′ x)

wkVar-comps : ∀ k → (ρ : Wk m ℓ) (ρ′ : Wk ℓ n) (x : Fin (k + n))
            → wkVar (liftn ρ k • liftn ρ′ k) x
            ≡ wkVar (liftn (ρ • ρ′) k) x
wkVar-comps 0      ρ ρ′ x      = refl
wkVar-comps (1+ n) ρ ρ′ x0     = refl
wkVar-comps (1+ n) ρ ρ′ (x +1) = cong _+1 (wkVar-comps n ρ ρ′ x)

opaque

  -- The weakening id is a right identity for composition.

  •-id : ρ • id ≡ ρ
  •-id {ρ = id}     = refl
  •-id {ρ = step _} = cong step •-id
  •-id {ρ = lift _} = refl

opaque

  -- A composition lemma for wk₀.

  wk₀-invariant : (ρ : Wk m n) → ρ • wk₀ ≡ wk₀
  wk₀-invariant id       = refl
  wk₀-invariant (step ρ) = cong step (wk₀-invariant ρ)
  wk₀-invariant (lift ρ) = cong step (wk₀-invariant ρ)

opaque

  -- A composition lemma for stepn id.

  stepn-id-• : ∀ n → stepn id n • ρ ≡ stepn ρ n
  stepn-id-• 0      = refl
  stepn-id-• (1+ n) = cong step (stepn-id-• n)

opaque

  -- Another composition lemma for stepn id.

  liftn-stepn-comp : ∀ n → stepn ρ n ≡ liftn ρ n • stepn id n
  liftn-stepn-comp 0      = sym •-id
  liftn-stepn-comp (1+ n) = cong step $ liftn-stepn-comp n

opaque

  -- The weakening step id • ρ is equal to lift ρ • step id.

  lift-step-comp : (ρ : Wk m n) → step id • ρ ≡ lift ρ • step id
  lift-step-comp _ = liftn-stepn-comp 1

opaque

  -- The function wkVar ρ is injective.

  wkVar-injective : wkVar ρ x ≡ wkVar ρ y → x ≡ y
  wkVar-injective = lemma _ _ _
    where
    lemma : ∀ (ρ : Wk m n) x y → wkVar ρ x ≡ wkVar ρ y → x ≡ y
    lemma ρ x0 x0 =
      wkVar ρ x0 ≡ wkVar ρ x0  →⟨ (λ _ → refl) ⟩
      x0 ≡ x0                  □
    lemma id (x +1) (y +1) =
      (x +1) ≡ (y +1)  □
    lemma (lift ρ) (x +1) (y +1) =
      (wkVar ρ x +1) ≡ (wkVar ρ y +1)  →⟨ suc-injective ⟩
      wkVar ρ x ≡ wkVar ρ y            →⟨ wkVar-injective ⟩
      x ≡ y                            →⟨ cong _+1 ⟩
      x +1 ≡ y +1                      □
    lemma (step ρ) x y =
      (wkVar ρ x +1) ≡ (wkVar ρ y +1)  →⟨ suc-injective ⟩
      wkVar ρ x ≡ wkVar ρ y            →⟨ wkVar-injective ⟩
      x ≡ y                            □
    lemma id       x0     (_ +1) ()
    lemma id       (_ +1) x0     ()
    lemma (lift _) x0     (_ +1) ()
    lemma (lift _) (_ +1) x0     ()

opaque

  -- It is not the case that x is equal to wkVar (step-at x) y.

  ≢wkVar-step-at : x ≢ wkVar (step-at x) y
  ≢wkVar-step-at {x = x0}              = λ ()
  ≢wkVar-step-at {x = _ +1} {y = x0}   = λ ()
  ≢wkVar-step-at {x = x +1} {y = y +1} =
    (x +1) ≡ (wkVar (step-at x) y +1)  →⟨ suc-injective ⟩
    x ≡ wkVar (step-at x) y            →⟨ ≢wkVar-step-at ⟩
    ⊥                                  □

------------------------------------------------------------------------
-- A property related to Universe-level

opaque

  -- Equality of universe levels is decidable.

  infix 4 _≟ᵘ_

  _≟ᵘ_ : Decidable (_≡_ {A = Universe-level})
  0ᵘ+ m ≟ᵘ 0ᵘ+ n = Dec-map (cong 0ᵘ+ , λ { refl → refl }) (m ≟ n)
  0ᵘ+ _ ≟ᵘ ωᵘ+ _ = no (λ ())
  0ᵘ+ _ ≟ᵘ ωᵘ·2  = no (λ ())
  ωᵘ+ _ ≟ᵘ 0ᵘ+ _ = no (λ ())
  ωᵘ+ m ≟ᵘ ωᵘ+ n = Dec-map (cong ωᵘ+ , λ { refl → refl }) (m ≟ n)
  ωᵘ+ _ ≟ᵘ ωᵘ·2  = no (λ ())
  ωᵘ·2  ≟ᵘ 0ᵘ+ _ = no (λ ())
  ωᵘ·2  ≟ᵘ ωᵘ+ _ = no (λ ())
  ωᵘ·2  ≟ᵘ ωᵘ·2  = yes refl

------------------------------------------------------------------------
-- Properties related to _≤ᵘ_ and _<ᵘ_

opaque

  -- The level 0 is the lowest level.

  0≤ᵘ : 0ᵘ ≤ᵘ l
  0≤ᵘ {l = 0ᵘ+ _} = 0ᵘ+≤ᵘ0ᵘ+ z≤′n
  0≤ᵘ {l = ωᵘ+ _} = 0ᵘ+≤ᵘωᵘ+
  0≤ᵘ {l = ωᵘ·2}  = ≤ᵘωᵘ·2

opaque

  -- The relation _≤ᵘ_ is transitive.

  ≤ᵘ-trans : l₁ ≤ᵘ l₂ → l₂ ≤ᵘ l₃ → l₁ ≤ᵘ l₃
  ≤ᵘ-trans (0ᵘ+≤ᵘ0ᵘ+ p) (0ᵘ+≤ᵘ0ᵘ+ q) = 0ᵘ+≤ᵘ0ᵘ+ (≤′-trans p q)
  ≤ᵘ-trans (0ᵘ+≤ᵘ0ᵘ+ p) 0ᵘ+≤ᵘωᵘ+     = 0ᵘ+≤ᵘωᵘ+
  ≤ᵘ-trans 0ᵘ+≤ᵘωᵘ+     (ωᵘ+≤ᵘωᵘ+ q) = 0ᵘ+≤ᵘωᵘ+
  ≤ᵘ-trans (ωᵘ+≤ᵘωᵘ+ p) (ωᵘ+≤ᵘωᵘ+ q) = ωᵘ+≤ᵘωᵘ+ (≤′-trans p q)
  ≤ᵘ-trans _            ≤ᵘωᵘ·2       = ≤ᵘωᵘ·2

opaque

  -- The relation _<ᵘ_ is transitive.

  <ᵘ-trans : l₁ <ᵘ l₂ → l₂ <ᵘ l₃ → l₁ <ᵘ l₃
  <ᵘ-trans (0ᵘ+<ᵘ0ᵘ+ p) (0ᵘ+<ᵘ0ᵘ+ q) = 0ᵘ+<ᵘ0ᵘ+ (<′-trans p q)
  <ᵘ-trans (0ᵘ+<ᵘ0ᵘ+ p) 0ᵘ+<ᵘωᵘ+     = 0ᵘ+<ᵘωᵘ+
  <ᵘ-trans (0ᵘ+<ᵘ0ᵘ+ _) 0ᵘ+<ᵘωᵘ·2    = 0ᵘ+<ᵘωᵘ·2
  <ᵘ-trans 0ᵘ+<ᵘωᵘ+     (ωᵘ+<ᵘωᵘ+ q) = 0ᵘ+<ᵘωᵘ+
  <ᵘ-trans 0ᵘ+<ᵘωᵘ+     ωᵘ+<ᵘωᵘ·2    = 0ᵘ+<ᵘωᵘ·2
  <ᵘ-trans 0ᵘ+<ᵘωᵘ·2    ()
  <ᵘ-trans (ωᵘ+<ᵘωᵘ+ p) (ωᵘ+<ᵘωᵘ+ q) = ωᵘ+<ᵘωᵘ+ (<′-trans p q)
  <ᵘ-trans (ωᵘ+<ᵘωᵘ+ _) ωᵘ+<ᵘωᵘ·2    = ωᵘ+<ᵘωᵘ·2
  <ᵘ-trans ωᵘ+<ᵘωᵘ·2    ()

opaque

  <ᵘ-≤ᵘ-trans : l₁ <ᵘ l₂ → l₂ ≤ᵘ l₃ → l₁ <ᵘ l₃
  <ᵘ-≤ᵘ-trans (0ᵘ+<ᵘ0ᵘ+ p) (0ᵘ+≤ᵘ0ᵘ+ q) = 0ᵘ+<ᵘ0ᵘ+ (≤′-trans p q)
  <ᵘ-≤ᵘ-trans (0ᵘ+<ᵘ0ᵘ+ p) 0ᵘ+≤ᵘωᵘ+     = 0ᵘ+<ᵘωᵘ+
  <ᵘ-≤ᵘ-trans (0ᵘ+<ᵘ0ᵘ+ _) ≤ᵘωᵘ·2       = 0ᵘ+<ᵘωᵘ·2
  <ᵘ-≤ᵘ-trans 0ᵘ+<ᵘωᵘ+     (ωᵘ+≤ᵘωᵘ+ q) = 0ᵘ+<ᵘωᵘ+
  <ᵘ-≤ᵘ-trans 0ᵘ+<ᵘωᵘ+     ≤ᵘωᵘ·2       = 0ᵘ+<ᵘωᵘ·2
  <ᵘ-≤ᵘ-trans 0ᵘ+<ᵘωᵘ·2    ≤ᵘωᵘ·2       = 0ᵘ+<ᵘωᵘ·2
  <ᵘ-≤ᵘ-trans (ωᵘ+<ᵘωᵘ+ p) (ωᵘ+≤ᵘωᵘ+ q) = ωᵘ+<ᵘωᵘ+ (≤′-trans p q)
  <ᵘ-≤ᵘ-trans (ωᵘ+<ᵘωᵘ+ _) ≤ᵘωᵘ·2       = ωᵘ+<ᵘωᵘ·2
  <ᵘ-≤ᵘ-trans ωᵘ+<ᵘωᵘ·2    ≤ᵘωᵘ·2       = ωᵘ+<ᵘωᵘ·2

opaque

  -- The relation _<ᵘ_ is contained in _≤ᵘ_.

  <ᵘ→≤ᵘ : l₁ <ᵘ l₂ → l₁ ≤ᵘ l₂
  <ᵘ→≤ᵘ (0ᵘ+<ᵘ0ᵘ+ p) = 0ᵘ+≤ᵘ0ᵘ+ (<′→≤′ p)
  <ᵘ→≤ᵘ 0ᵘ+<ᵘωᵘ+     = 0ᵘ+≤ᵘωᵘ+
  <ᵘ→≤ᵘ 0ᵘ+<ᵘωᵘ·2    = ≤ᵘωᵘ·2
  <ᵘ→≤ᵘ (ωᵘ+<ᵘωᵘ+ p) = ωᵘ+≤ᵘωᵘ+ (<′→≤′ p)
  <ᵘ→≤ᵘ ωᵘ+<ᵘωᵘ·2    = ≤ᵘωᵘ·2

-- The relation _<ᵘ_ is well-founded.

private

  0ᵘ+-accessible : ∀ n → Acc _<ᵘ_ (0ᵘ+ n)
  0ᵘ+-accessible n = acc (helper n)
    where
    helper : ∀ n → WfRec _<ᵘ_ (Acc _<ᵘ_) (0ᵘ+ n)
    helper .(1+ n) (0ᵘ+<ᵘ0ᵘ+ {m = n} ≤′-refl) = 0ᵘ+-accessible n
    helper .(1+ n) (0ᵘ+<ᵘ0ᵘ+ (≤′-step {n} p)) = helper n (0ᵘ+<ᵘ0ᵘ+ p)

  ωᵘ+-accessible : ∀ n → Acc _<ᵘ_ (ωᵘ+ n)
  ωᵘ+-accessible n = acc (helper n)
    where
    helper : ∀ n → WfRec _<ᵘ_ (Acc _<ᵘ_) (ωᵘ+ n)
    helper _       (0ᵘ+<ᵘωᵘ+ {m})             = 0ᵘ+-accessible m
    helper .(1+ n) (ωᵘ+<ᵘωᵘ+ {m = n} ≤′-refl) = ωᵘ+-accessible n
    helper .(1+ n) (ωᵘ+<ᵘωᵘ+ (≤′-step {n} p)) = helper n (ωᵘ+<ᵘωᵘ+ p)

  ωᵘ·2-accessible : Acc _<ᵘ_ ωᵘ·2
  ωᵘ·2-accessible = acc helper
    where
    helper : WfRec _<ᵘ_ (Acc _<ᵘ_) ωᵘ·2
    helper 0ᵘ+<ᵘωᵘ·2 = 0ᵘ+-accessible _
    helper ωᵘ+<ᵘωᵘ·2 = ωᵘ+-accessible _

<ᵘ-wellFounded : WellFounded _<ᵘ_
<ᵘ-wellFounded (0ᵘ+ n) = 0ᵘ+-accessible n
<ᵘ-wellFounded (ωᵘ+ n) = ωᵘ+-accessible n
<ᵘ-wellFounded ωᵘ·2    = ωᵘ·2-accessible

<ᵘ-Rec : ∀ {ℓ} → RecStruct Universe-level ℓ ℓ
<ᵘ-Rec = WfRec _<ᵘ_

module _ {ℓ} where
  open All <ᵘ-wellFounded ℓ public
    renaming ( wfRecBuilder to <ᵘ-recBuilder
             ; wfRec        to <ᵘ-rec
             )
    hiding (wfRec-builder)

------------------------------------------------------------------------
-- Properties related to _⊔ᵘ_

opaque

  -- The level l₁ is bounded by the maximum of l₁ and l₂.

  ≤ᵘ⊔ᵘʳ : l₁ ≤ᵘ l₁ ⊔ᵘ l₂
  ≤ᵘ⊔ᵘʳ {l₁ = 0ᵘ+ _} {l₂ = 0ᵘ+ _} = 0ᵘ+≤ᵘ0ᵘ+ ≤′⊔ʳ
  ≤ᵘ⊔ᵘʳ {l₁ = 0ᵘ+ _} {l₂ = ωᵘ+ _} = 0ᵘ+≤ᵘωᵘ+
  ≤ᵘ⊔ᵘʳ {l₁ = 0ᵘ+ _} {l₂ = ωᵘ·2}  = ≤ᵘωᵘ·2
  ≤ᵘ⊔ᵘʳ {l₁ = ωᵘ+ _} {l₂ = 0ᵘ+ _} = ωᵘ+≤ᵘωᵘ+ ≤′⊔ˡ
  ≤ᵘ⊔ᵘʳ {l₁ = ωᵘ+ _} {l₂ = ωᵘ+ _} = ωᵘ+≤ᵘωᵘ+ ≤′⊔ʳ
  ≤ᵘ⊔ᵘʳ {l₁ = ωᵘ+ _} {l₂ = ωᵘ·2}  = ≤ᵘωᵘ·2
  ≤ᵘ⊔ᵘʳ {l₁ = ωᵘ·2}               = ≤ᵘωᵘ·2

opaque

  -- The level l₂ is bounded by the maximum of l₁ and l₂.

  ≤ᵘ⊔ᵘˡ : l₂ ≤ᵘ l₁ ⊔ᵘ l₂
  ≤ᵘ⊔ᵘˡ {l₂ = 0ᵘ+ _} {l₁ = 0ᵘ+ _} = 0ᵘ+≤ᵘ0ᵘ+ ≤′⊔ˡ
  ≤ᵘ⊔ᵘˡ {l₂ = ωᵘ+ _} {l₁ = 0ᵘ+ _} = ωᵘ+≤ᵘωᵘ+ ≤′⊔ˡ
  ≤ᵘ⊔ᵘˡ {l₂ = ωᵘ·2}  {l₁ = 0ᵘ+ _} = ≤ᵘωᵘ·2
  ≤ᵘ⊔ᵘˡ {l₂ = 0ᵘ+ _} {l₁ = ωᵘ+ _} = 0ᵘ+≤ᵘωᵘ+
  ≤ᵘ⊔ᵘˡ {l₂ = ωᵘ+ _} {l₁ = ωᵘ+ _} = ωᵘ+≤ᵘωᵘ+ ≤′⊔ˡ
  ≤ᵘ⊔ᵘˡ {l₂ = ωᵘ·2}  {l₁ = ωᵘ+ _} = ≤ᵘωᵘ·2
  ≤ᵘ⊔ᵘˡ              {l₁ = ωᵘ·2}  = ≤ᵘωᵘ·2

opaque

  -- The function _⊔ᵘ_ is monotone.

  ⊔ᵘ-mono : l₁ ≤ᵘ l₁′ → l₂ ≤ᵘ l₂′ → l₁ ⊔ᵘ l₂ ≤ᵘ l₁′ ⊔ᵘ l₂′
  ⊔ᵘ-mono (0ᵘ+≤ᵘ0ᵘ+ p) (0ᵘ+≤ᵘ0ᵘ+ q) = 0ᵘ+≤ᵘ0ᵘ+ (⊔-mono p q)
  ⊔ᵘ-mono (0ᵘ+≤ᵘ0ᵘ+ _) 0ᵘ+≤ᵘωᵘ+     = 0ᵘ+≤ᵘωᵘ+
  ⊔ᵘ-mono (0ᵘ+≤ᵘ0ᵘ+ _) (ωᵘ+≤ᵘωᵘ+ q) = ωᵘ+≤ᵘωᵘ+ q
  ⊔ᵘ-mono (0ᵘ+≤ᵘ0ᵘ+ _) ≤ᵘωᵘ·2       = ≤ᵘωᵘ·2
  ⊔ᵘ-mono 0ᵘ+≤ᵘωᵘ+     (0ᵘ+≤ᵘ0ᵘ+ _) = 0ᵘ+≤ᵘωᵘ+
  ⊔ᵘ-mono 0ᵘ+≤ᵘωᵘ+     0ᵘ+≤ᵘωᵘ+     = 0ᵘ+≤ᵘωᵘ+
  ⊔ᵘ-mono 0ᵘ+≤ᵘωᵘ+     (ωᵘ+≤ᵘωᵘ+ q) = ωᵘ+≤ᵘωᵘ+
                                        (≤′-trans q (≤⇒≤′ (m≤n⊔m _ _)))
  ⊔ᵘ-mono 0ᵘ+≤ᵘωᵘ+     ≤ᵘωᵘ·2       = ≤ᵘωᵘ·2
  ⊔ᵘ-mono (ωᵘ+≤ᵘωᵘ+ p) (0ᵘ+≤ᵘ0ᵘ+ _) = ωᵘ+≤ᵘωᵘ+ p
  ⊔ᵘ-mono (ωᵘ+≤ᵘωᵘ+ p) 0ᵘ+≤ᵘωᵘ+     = ωᵘ+≤ᵘωᵘ+
                                        (≤′-trans p (≤⇒≤′ (m≤m⊔n _ _)))
  ⊔ᵘ-mono (ωᵘ+≤ᵘωᵘ+ p) (ωᵘ+≤ᵘωᵘ+ q) = ωᵘ+≤ᵘωᵘ+ (⊔-mono p q)
  ⊔ᵘ-mono (ωᵘ+≤ᵘωᵘ+ _) ≤ᵘωᵘ·2       = ≤ᵘωᵘ·2
  ⊔ᵘ-mono ≤ᵘωᵘ·2       _            = ≤ᵘωᵘ·2

opaque

  -- 0ᵘ is a left identity for _⊔ᵘ_.

  ⊔ᵘ-identityˡ : 0ᵘ ⊔ᵘ l ≡ l
  ⊔ᵘ-identityˡ {l = 0ᵘ+ _} = refl
  ⊔ᵘ-identityˡ {l = ωᵘ+ _} = refl
  ⊔ᵘ-identityˡ {l = ωᵘ·2}  = refl

opaque

  -- The function _⊔ᵘ_ is idempotent.

  ⊔ᵘ-idem : l ⊔ᵘ l ≡ l
  ⊔ᵘ-idem {l = 0ᵘ+ _} = cong 0ᵘ+ (⊔-idem _)
  ⊔ᵘ-idem {l = ωᵘ+ _} = cong ωᵘ+ (⊔-idem _)
  ⊔ᵘ-idem {l = ωᵘ·2}  = refl

------------------------------------------------------------------------
-- Properties related to Level-support

opaque

  -- Equality is decidable for Level-small.

  infix 4 _≟-Level-small_

  _≟-Level-small_ : Decidable-equality Level-small
  small     ≟-Level-small small     = yes refl
  small     ≟-Level-small not-small = no (λ ())
  not-small ≟-Level-small small     = no (λ ())
  not-small ≟-Level-small not-small = yes refl

opaque

  -- Equality is decidable for Level-support.

  infix 4 _≟-Level-support_

  _≟-Level-support_ : Decidable-equality Level-support
  only-literals ≟-Level-support only-literals = yes refl
  only-literals ≟-Level-support level-type _  = no (λ ())
  level-type _  ≟-Level-support only-literals = no (λ ())
  level-type s₁ ≟-Level-support level-type s₂ with s₁ ≟-Level-small s₂
  … | yes eq    = yes (cong level-type eq)
  … | no not-eq = no (not-eq ∘→ λ { refl → refl })

opaque

  -- The relation _≤LSm_ is reflexive.

  refl-≤LSm : sm ≤LSm sm
  refl-≤LSm {sm = small}     = small≤small
  refl-≤LSm {sm = not-small} = not-small≤

opaque

  -- The relation _≤LSm_ is transitive.

  trans-≤LSm : sm₁ ≤LSm sm₂ → sm₂ ≤LSm sm₃ → sm₁ ≤LSm sm₃
  trans-≤LSm not-small≤  _           = not-small≤
  trans-≤LSm small≤small small≤small = small≤small

opaque

  -- The relation _≤LS_ is reflexive.

  refl-≤LS : s ≤LS s
  refl-≤LS {s = only-literals} = only-literals≤
  refl-≤LS {s = level-type _}  = level-type refl-≤LSm

opaque

  -- The relation _≤LS_ is transitive.

  trans-≤LS : s₁ ≤LS s₂ → s₂ ≤LS s₃ → s₁ ≤LS s₃
  trans-≤LS only-literals≤ only-literals≤ = only-literals≤
  trans-≤LS (level-type p) (level-type q) = level-type (trans-≤LSm p q)

opaque

  -- If s₁ ≤LS s₂, then s₁ is distinct from only-literals exactly when
  -- s₂ is distinct from only-literals.

  ≤LS→≢only-literals⇔≢only-literals :
    s₁ ≤LS s₂ →
    s₁ ≢ only-literals ⇔ s₂ ≢ only-literals
  ≤LS→≢only-literals⇔≢only-literals = λ where
    only-literals≤           → id⇔
    (level-type not-small≤)  → (λ _ ()) , (λ _ ())
    (level-type small≤small) → id⇔

opaque

  -- If s₁ ≤LS s₂ and s₁ is equal to level-type small, then s₂ is
  -- equal to level-type small.

  ≤LS→≡small→≡small :
    s₁ ≤LS s₂ →
    s₁ ≡ level-type small → s₂ ≡ level-type small
  ≤LS→≡small→≡small = λ where
    only-literals≤           → λ ()
    (level-type not-small≤)  → λ ()
    (level-type small≤small) → idᶠ

------------------------------------------------------------------------
-- Some properties related to DCon and DExt

opaque

  -- Injectivity for _∙⟨_⟩[_∷_].

  ∙-PE-injectivity :
    ∇₁ ∙⟨ ω₁ ⟩[ t₁ ∷ B₁ ] ≡ ∇₂ ∙⟨ ω₂ ⟩[ t₂ ∷ B₂ ] →
    ∇₁ ≡ ∇₂ × ω₁ ≡ ω₂ × t₁ ≡ t₂ × B₁ ≡ B₂
  ∙-PE-injectivity refl = refl , refl , refl , refl

opaque

  -- The function map-Con idᶠ is pointwise equal to the identity
  -- function.

  map-Con-id : map-Con idᶠ Γ ≡ Γ
  map-Con-id {Γ = ε}     = refl
  map-Con-id {Γ = _ ∙ _} = cong (_∙ _) map-Con-id

opaque

  -- The function map-DCon idᶠ is pointwise equal to the identity
  -- function.

  map-DCon-id : map-DCon idᶠ ∇ ≡ ∇
  map-DCon-id {∇ = ε}    = refl
  map-DCon-id {∇ = _ ∙!} = cong _∙! map-DCon-id

opaque

  -- The function map-Con preserves pointwise equality.

  map-Con-cong :
    {f g : ∀ {n} → P n → Q n} {Γ : Con P n} →
    (∀ {n} (x : P n) → f x ≡ g x) → map-Con f Γ ≡ map-Con g Γ
  map-Con-cong {Γ = ε}     _   = refl
  map-Con-cong {Γ = _ ∙ _} f≡g = cong₂ _∙_ (map-Con-cong f≡g) (f≡g _)

opaque

  -- The function map-DCon preserves pointwise equality.

  map-DCon-cong : (∀ x → f x ≡ g x) → map-DCon f ∇ ≡ map-DCon g ∇
  map-DCon-cong {∇ = ε}    _   = refl
  map-DCon-cong {∇ = _ ∙!} f≡g =
    cong₃ _∙⟨ _ ⟩[_∷_] (map-DCon-cong f≡g) (f≡g _) (f≡g _)

opaque

  -- A lemma related to _↦_∷_∈_ and map-DCon.

  ↦∷∈-map-DCon :
    α ↦ t ∷ B ∈ map-DCon f ∇ →
    ∃₂ λ u C → t ≡ f u × B ≡ f C × α ↦ u ∷ C ∈ ∇
  ↦∷∈-map-DCon {∇ = ε} ()
  ↦∷∈-map-DCon {∇ = _ ∙!} here =
    _ , _ , refl , refl , here
  ↦∷∈-map-DCon {∇ = _ ∙!} (there α↦) =
    Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ there))) $
    ↦∷∈-map-DCon α↦

opaque

  -- If DExt A n m is inhabited, then m ≤ n.

  DExt→≤ : DExt A n m → m ≤ n
  DExt→≤ idᵉ            = ≤-refl
  DExt→≤ (step ξ _ _ _) = m≤n⇒m≤1+n (DExt→≤ ξ)

opaque
  unfolding _ᵈ•_ as-DExt

  -- The definition context ε ᵈ• as-DExt ∇ is equal to ∇.

  εᵈ•as-DExt : ε ᵈ• as-DExt ∇ ≡ ∇
  εᵈ•as-DExt {∇ = ε} =
    refl
  εᵈ•as-DExt {∇ = _ ∙⟨ _ ⟩[ _ ∷ _ ]} =
    cong _∙⟨ _ ⟩[ _ ∷ _ ] εᵈ•as-DExt

opaque
  unfolding glassifyᵉ as-DExt

  -- Glassification commutes with as-DExt.

  glassifyᵉ-as-DExt : glassifyᵉ (as-DExt ∇) ≡ as-DExt (glassify ∇)
  glassifyᵉ-as-DExt {∇ = ε} =
    refl
  glassifyᵉ-as-DExt {∇ = _ ∙!} =
    cong (λ ξ → step ξ _ _ _) glassifyᵉ-as-DExt

opaque

  -- If α points to something in a definition context of length n,
  -- then α is less than n.

  ↦∷∈→< :
    {∇ : DCon A n} →
    α ↦∷ B ∈ ∇ →
    α < n
  ↦∷∈→< here       = ≤-refl
  ↦∷∈→< (there α↦) = m≤n⇒m≤1+n (↦∷∈→< α↦)

opaque
  unfolding _ᵈ•_

  -- If α points to B in ∇ ᵈ• ξ, but not in ξ, then α points to B in
  -- ∇.

  ≰→↦∈→↦∈ :
    {ξ : DExt A o n} →
    ¬ n ≤ α → α ↦∷ B ∈ ∇ ᵈ• ξ → α ↦∷ B ∈ ∇
  ≰→↦∈→↦∈ {ξ = idᵉ} _ α↦ = α↦
  ≰→↦∈→↦∈ {ξ = step ξ _ _ _} l≰α here =
    ⊥-elim $ l≰α (DExt→≤ ξ)
  ≰→↦∈→↦∈ {ξ = step ξ _ _ _} l≰α (there α↦) =
    ≰→↦∈→↦∈ {ξ = ξ} l≰α α↦

opaque
  unfolding _ᵈ•_

  -- If α points to t and B in ∇ ᵈ• ξ, but not in ξ, then α points to
  -- t and B in ∇.

  ≰→↦∷∈→↦∷∈ :
    {ξ : DExt A o n} →
    ¬ n ≤ α → α ↦ t ∷ B ∈ ∇ ᵈ• ξ → α ↦ t ∷ B ∈ ∇
  ≰→↦∷∈→↦∷∈ {ξ = idᵉ} _ α↦ = α↦
  ≰→↦∷∈→↦∷∈ {ξ = step ξ _ _ _} l≰α here =
    ⊥-elim $ l≰α (DExt→≤ ξ)
  ≰→↦∷∈→↦∷∈ {ξ = step ξ _ _ _} l≰α (there α↦) =
    ≰→↦∷∈→↦∷∈ {ξ = ξ} l≰α α↦

------------------------------------------------------------------------
-- Properties related to Empty-con and _or-empty_

opaque

  -- Empty-con is decidable.

  Empty-con? : Dec (Empty-con Γ)
  Empty-con? {Γ = ε}     = yes ε
  Empty-con? {Γ = _ ∙ _} = no (λ ())

opaque

  -- A characterisation lemma for _or-empty_.

  or-empty⇔ : A or-empty Γ ⇔ (A ⊎ Empty-con Γ)
  or-empty⇔ =
      (λ where
         (possibly-nonempty ⦃ ok ⦄) → inj₁ ok
         ε                          → inj₂ ε)
    , (λ where
         (inj₁ x) → possibly-nonempty ⦃ ok = x ⦄
         (inj₂ ε) → ε)

opaque

  -- If A is decided, then A or-empty_ is decidable.

  infix 4 _or-empty?

  _or-empty? : Dec A → Dec (A or-empty Γ)
  A? or-empty? = Dec-map (sym⇔ or-empty⇔) (A? ⊎-dec Empty-con?)

opaque

  -- If the size of Γ is positive, then A or-empty Γ implies A.

  or-empty-1+→ :
    {Γ : Con P (1+ n)}
    ⦃ ok : A or-empty Γ ⦄ →
    A
  or-empty-1+→ ⦃ ok = possibly-nonempty ⦃ ok ⦄ ⦄ = ok

opaque

  -- A or-empty Γ ∙ B implies A or-empty Γ.

  or-empty-∙→ :
    ⦃ ok : A or-empty Γ ∙ B ⦄ →
    A or-empty Γ
  or-empty-∙→ = possibly-nonempty ⦃ ok = or-empty-1+→ ⦄

opaque

  -- A map function for _or-empty_.

  or-empty-map :
    (A → B) → A or-empty Γ → B or-empty Γ
  or-empty-map f =
    or-empty⇔ .proj₂ ∘→ ⊎.map f idᶠ ∘→ or-empty⇔ .proj₁

------------------------------------------------------------------------
-- A property related to Term-kind

opaque

  -- Term-kind is a set.

  Term-kind-set : Is-set Term-kind
  Term-kind-set {x = tm}  {y = tm}  {x = refl} {y = refl} = refl
  Term-kind-set {x = tm}  {y = lvl} {x = ()}
  Term-kind-set {x = lvl} {y = tm}  {x = ()}
  Term-kind-set {x = lvl} {y = lvl} {x = refl} {y = refl} = refl

------------------------------------------------------------------------
-- Other properties

-- Decidability of Strength equality
decStrength : Decidable (_≡_ {A = Strength})
decStrength 𝕤 𝕤 = yes refl
decStrength 𝕤 𝕨 = no λ{()}
decStrength 𝕨 𝕤 = no λ{()}
decStrength 𝕨 𝕨 = yes refl

-- Decidability of equality for BinderMode.
decBinderMode : Decidable (_≡_ {A = BinderMode})
decBinderMode = λ where
  BMΠ      BMΠ      → yes refl
  BMΠ      (BMΣ _)  → no (λ ())
  (BMΣ _)  BMΠ      → no (λ ())
  (BMΣ s₁) (BMΣ s₂) → case decStrength s₁ s₂ of λ where
    (yes refl) → yes refl
    (no s₁≢s₂)    → no λ where
      refl → s₁≢s₂ refl
