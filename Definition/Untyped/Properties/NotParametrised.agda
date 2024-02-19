------------------------------------------------------------------------
-- Some definitions that are re-exported from
-- Definition.Untyped.Properties but do not depend on that module's
-- module parameter
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

module Definition.Untyped.Properties.NotParametrised where

open import Definition.Untyped.NotParametrised

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Relation
open import Tools.PropositionalEquality

private variable
  ℓ m n : Nat
  ρ ρ′  : Wk _ _

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

-- The weakening step id • ρ is equal to lift ρ • step id.

lift-step-comp : (ρ : Wk m n) → step id • ρ ≡ lift ρ • step id
lift-step-comp id       = refl
lift-step-comp (step ρ) = cong step (lift-step-comp ρ)
lift-step-comp (lift ρ) = refl

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
