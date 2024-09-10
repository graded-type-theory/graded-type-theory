------------------------------------------------------------------------
-- Some definitions that are re-exported from
-- Definition.Untyped.Properties but do not depend on that module's
-- module parameter
------------------------------------------------------------------------

module Definition.Untyped.Properties.NotParametrised where

open import Definition.Untyped.NotParametrised

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Relation
open import Tools.PropositionalEquality

private variable
  ℓ m n              : Nat
  ρ ρ′               : Wk _ _
  x y                : Fin _
  l l₁ l₁′ l₂ l₂′ l₃ : Universe-level

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

  liftn-wk₀-•-wk₀ : ∀ n → liftn {k = m} wk₀ n • wk₀ ≡ wk₀
  liftn-wk₀-•-wk₀ 0      = •-id
  liftn-wk₀-•-wk₀ (1+ n) = cong step $ liftn-wk₀-•-wk₀ n

-- The weakening step id • ρ is equal to lift ρ • step id.

lift-step-comp : (ρ : Wk m n) → step id • ρ ≡ lift ρ • step id
lift-step-comp id       = refl
lift-step-comp (step ρ) = cong step (lift-step-comp ρ)
lift-step-comp (lift ρ) = refl

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

------------------------------------------------------------------------
-- A property related to Universe-level

opaque

  -- Equality of universe levels is decidable.

  infix 4 _≟ᵘ_

  _≟ᵘ_ : Decidable (_≡_ {A = Universe-level})
  _≟ᵘ_ = _≟_

------------------------------------------------------------------------
-- Properties related to _≤ᵘ_ and _<ᵘ_

opaque

  -- The level 0 is the lowest level.

  0≤ᵘ : 0 ≤ᵘ l
  0≤ᵘ = 0≤′

opaque

  -- The successor function is monotone for _≤ᵘ_.

  1+≤ᵘ1+ : l₁ ≤ᵘ l₂ → 1+ l₁ ≤ᵘ 1+ l₂
  1+≤ᵘ1+ = 1+≤′1+

opaque

  -- A level is bounded by its successor.

  ≤ᵘ1+ : l ≤ᵘ 1+ l
  ≤ᵘ1+ = ≤ᵘ-step ≤ᵘ-refl

opaque

  -- The relation _≤ᵘ_ is transitive.

  ≤ᵘ-trans : l₁ ≤ᵘ l₂ → l₂ ≤ᵘ l₃ → l₁ ≤ᵘ l₃
  ≤ᵘ-trans = ≤′-trans

opaque

  -- The relation _<ᵘ_ is transitive.

  <ᵘ-trans : l₁ <ᵘ l₂ → l₂ <ᵘ l₃ → l₁ <ᵘ l₃
  <ᵘ-trans = <′-trans

opaque

  -- The relation _<ᵘ_ is contained in _≤ᵘ_.

  <ᵘ→≤ᵘ : l₁ <ᵘ l₂ → l₁ ≤ᵘ l₂
  <ᵘ→≤ᵘ = <′→≤′

------------------------------------------------------------------------
-- Properties related to _⊔ᵘ_

opaque

  -- The level l₁ is bounded by the maximum of l₁ and l₂.

  ≤ᵘ⊔ᵘʳ : l₁ ≤ᵘ l₁ ⊔ᵘ l₂
  ≤ᵘ⊔ᵘʳ = ≤′⊔ˡ

opaque

  -- The level l₂ is bounded by the maximum of l₁ and l₂.

  ≤ᵘ⊔ᵘˡ : l₂ ≤ᵘ l₁ ⊔ᵘ l₂
  ≤ᵘ⊔ᵘˡ = ≤′⊔ʳ

opaque

  -- The function _⊔ᵘ_ is monotone.

  ⊔ᵘ-mono : l₁ ≤ᵘ l₁′ → l₂ ≤ᵘ l₂′ → l₁ ⊔ᵘ l₂ ≤ᵘ l₁′ ⊔ᵘ l₂′
  ⊔ᵘ-mono = flip ⊔-mono

opaque

  -- The function _⊔ᵘ_ is idempotent.

  ⊔ᵘ-idem : l ⊔ᵘ l ≡ l
  ⊔ᵘ-idem = ⊔-idem _

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
