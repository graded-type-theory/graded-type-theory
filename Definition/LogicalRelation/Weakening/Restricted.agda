------------------------------------------------------------------------
-- A restricted variant of _⊢ʷᵏ_∷_, used in the definition of the
-- logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Weakening.Restricted
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.Typed R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Weakening.Combined R as C using (_⊢ʷᵏ_∷_)
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Properties.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  m₁ m₂ n₁ n₂     : Nat
  V               : Set _
  ρ ρ₁ ρ₂         : Wk _ _
  Γ Γ₁ Γ₂ Γ₃      : Cons _ _
  ∇ ∇₁ ∇₂         : DCon (Term 0) _
  Δ Δ₁ Δ₂         : Con Term _
  A A₁ A₂ t t₁ t₂ : Term _
  𝓙               : Judgement _

------------------------------------------------------------------------
-- The type _⊢ʷᵏʳ_∷_

-- A restricted variant of _⊢ʷᵏ_∷_.

infix 4 _⊢ʷᵏʳ_∷_

data _⊢ʷᵏʳ_∷_ {m₁ m₂} : Cons m₂ n₂ → Wk n₂ n₁ → Cons m₁ n₁ → Set a where
  includedʳ : ⦃ inc : Var-included ⦄ →
              (⊢ρ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁) →
              Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁
  id        : (∇₂⊇∇₁ : » ∇₂ ⊇ ∇₁) (⊢Δ : ∇₂ »⊢ Δ) →
              ∇₂ » Δ ⊢ʷᵏʳ id ∷ ∇₁ » Δ

------------------------------------------------------------------------
-- Some lemmas

opaque

  -- Converts from _⊢ʷᵏ_∷_ to _⊢ʷᵏʳ_∷_.

  ⊢ʷᵏ→⊢ʷᵏʳ :
    ⦃ inc : Var-included or-empty Γ₂ .vars ⦄ →
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ → Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁
  ⊢ʷᵏ→⊢ʷᵏʳ ⦃ inc = possibly-nonempty ⦄ ⊢ρ = includedʳ ⊢ρ
  ⊢ʷᵏ→⊢ʷᵏʳ ⦃ inc = ε                 ⦄ ⊢ρ =
    let ∇₂⊇∇₁ , ⊢ρ = C.⊢ʷᵏ⇔ .proj₁ ⊢ρ in
    case W.∷ʷ⊇→∷⊇ ⊢ρ of λ where
      W.id → id ∇₂⊇∇₁ (ε (defn-wf (W.wf-∷ʷ⊇ ⊢ρ)))

opaque

  -- Converts from _⊢ʷᵏʳ_∷_ to _⊢ʷᵏ_∷_.

  ⊢ʷᵏʳ→⊢ʷᵏ : Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ → Γ₂ ⊢ʷᵏ ρ ∷ Γ₁
  ⊢ʷᵏʳ→⊢ʷᵏ (includedʳ ⊢ρ) = ⊢ρ
  ⊢ʷᵏʳ→⊢ʷᵏ (id ∇₂⊇∇₁ ⊢Δ)  = C.⊢ʷᵏ⇔ .proj₂ (∇₂⊇∇₁ , W.idʷ ⊢Δ)

opaque

  -- If Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ holds, then Γ₂ is well-formed.

  wf-⊢ʷᵏʳ : Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ → ⊢ Γ₂
  wf-⊢ʷᵏʳ (includedʳ ⊢ρ) = C.wf-⊢ʷᵏ ⊢ρ
  wf-⊢ʷᵏʳ (id _ ⊢Δ)      = ⊢Δ

opaque

  -- Identity.

  ⊢ʷᵏʳid : ⊢ Γ → Γ ⊢ʷᵏʳ id ∷ Γ
  ⊢ʷᵏʳid = id id⊇

opaque

  -- Composition.

  ⊢ʷᵏʳ• :
    Γ₃ ⊢ʷᵏʳ ρ₂ ∷ Γ₂ →
    Γ₂ ⊢ʷᵏʳ ρ₁ ∷ Γ₁ →
    Γ₃ ⊢ʷᵏʳ ρ₂ • ρ₁ ∷ Γ₁
  ⊢ʷᵏʳ• (id ∇₃⊇∇₂ ⊢Δ₃) (id ∇₂⊇∇₁ _) =
    id (»⊇-trans ∇₃⊇∇₂ ∇₂⊇∇₁) ⊢Δ₃
  ⊢ʷᵏʳ• ⊢ρ₂@(id _ _) (includedʳ ⊢ρ₁) =
    includedʳ (C.⊢ʷᵏ• (⊢ʷᵏʳ→⊢ʷᵏ ⊢ρ₂) ⊢ρ₁)
  ⊢ʷᵏʳ• (includedʳ ⊢ρ₂) ⊢ρ₁ =
    includedʳ (C.⊢ʷᵏ• ⊢ρ₂ (⊢ʷᵏʳ→⊢ʷᵏ ⊢ρ₁))

opaque

  -- If Δ is well-formed, then wk₀ is a well-formed weakening from ε
  -- to Δ (given a certain assumption).

  ⊢ʷᵏʳwk₀ :
    ⦃ inc : Var-included or-empty Δ ⦄ →
    ∇ »⊢ Δ → ∇ » Δ ⊢ʷᵏʳ wk₀ ∷ ∇ » ε
  ⊢ʷᵏʳwk₀ ⊢Δ = ⊢ʷᵏ→⊢ʷᵏʳ (C.⊢ʷᵏwk₀ ⊢Δ)

------------------------------------------------------------------------
-- Weakening lemmas

opaque

  -- Weakening for various judgements.

  wk-⊢ :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Γ₁ ⊢[ 𝓙 ] → Γ₂ ⊢[ mapJ (wk ρ) 𝓙 ]
  wk-⊢ (includedʳ ⊢ρ) = C.wk-⊢ ⊢ρ
  wk-⊢ (id ∇₂⊇∇₁ _)   =
    PE.subst (_⊢[_] _) (PE.sym mapJ-wk-id) ∘→
    defn-wk ∇₂⊇∇₁

opaque

  -- Weakening for single-step reduction for terms.

  wk-⇒∷ :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Γ₁ ⊢ t₁ ⇒ t₂ ∷ A → Γ₂ ⊢ wk ρ t₁ ⇒ wk ρ t₂ ∷ wk ρ A
  wk-⇒∷ (includedʳ ⊢ρ) = C.wk-⇒∷ ⊢ρ
  wk-⇒∷ (id ∇₂⊇∇₁ _)   =
    PE.subst₃ (_⊢_⇒_∷_ _)
      (PE.sym (wk-id _)) (PE.sym (wk-id _)) (PE.sym (wk-id _)) ∘→
    defn-wkRedTerm ∇₂⊇∇₁

opaque

  -- Weakening for multi-step reduction for terms.

  wk-⇒*∷ :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Γ₁ ⊢ t₁ ⇒* t₂ ∷ A → Γ₂ ⊢ wk ρ t₁ ⇒* wk ρ t₂ ∷ wk ρ A
  wk-⇒*∷ (includedʳ ⊢ρ) = C.wk-⇒*∷ ⊢ρ
  wk-⇒*∷ (id ∇₂⊇∇₁ _)   =
    PE.subst₃ (_⊢_⇒*_∷_ _)
      (PE.sym (wk-id _)) (PE.sym (wk-id _)) (PE.sym (wk-id _)) ∘→
    defn-wkRed*Term ∇₂⊇∇₁

opaque

  -- Weakening for reduction to WHNF for terms.

  wk-↘∷ :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Γ₁ ⊢ t₁ ↘ t₂ ∷ A → Γ₂ ⊢ wk ρ t₁ ↘ wk ρ t₂ ∷ wk ρ A
  wk-↘∷ (includedʳ ⊢ρ) = C.wk-↘∷ ⊢ρ
  wk-↘∷ (id ∇₂⊇∇₁ _)   =
    PE.subst₃ (_⊢_↘_∷_ _)
      (PE.sym (wk-id _)) (PE.sym (wk-id _)) (PE.sym (wk-id _)) ∘→
    defn-wkRed↘Term ∇₂⊇∇₁

opaque

  -- Weakening for single-step reduction for types.

  wk-⇒ :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Γ₁ ⊢ A₁ ⇒ A₂ → Γ₂ ⊢ wk ρ A₁ ⇒ wk ρ A₂
  wk-⇒ (includedʳ ⊢ρ) = C.wk-⇒ ⊢ρ
  wk-⇒ (id ∇₂⊇∇₁ _)   =
    PE.subst₂ (_⊢_⇒_ _) (PE.sym (wk-id _)) (PE.sym (wk-id _)) ∘→
    defn-wkRed ∇₂⊇∇₁

opaque

  -- Weakening for multi-step reduction for types.

  wk-⇒* :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Γ₁ ⊢ A₁ ⇒* A₂ → Γ₂ ⊢ wk ρ A₁ ⇒* wk ρ A₂
  wk-⇒* (includedʳ ⊢ρ) = C.wk-⇒* ⊢ρ
  wk-⇒* (id ∇₂⊇∇₁ _)   =
    PE.subst₂ (_⊢_⇒*_ _) (PE.sym (wk-id _)) (PE.sym (wk-id _)) ∘→
    defn-wkRed* ∇₂⊇∇₁

opaque

  -- Weakening for reduction to WHNF for types.

  wk-↘ :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Γ₁ ⊢ A₁ ↘ A₂ → Γ₂ ⊢ wk ρ A₁ ↘ wk ρ A₂
  wk-↘ (includedʳ ⊢ρ) = C.wk-↘ ⊢ρ
  wk-↘ (id ∇₂⊇∇₁ _)   =
    PE.subst₂ (_⊢_↘_ _) (PE.sym (wk-id _)) (PE.sym (wk-id _)) ∘→
    defn-wkRed↘ ∇₂⊇∇₁

opaque

  -- Weakening for Neutral.

  wk-Neutral :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Neutral V (Γ₁ .defs) t → Neutral V (Γ₂ .defs) (wk ρ t)
  wk-Neutral (includedʳ ⊢ρ) = C.wk-Neutral ⊢ρ
  wk-Neutral (id ∇₂⊇∇₁ _)   =
    PE.subst (Neutral _ _) (PE.sym (wk-id _)) ∘→
    defn-wkNeutral ∇₂⊇∇₁

opaque

  -- Weakening for Neutralᵃ.

  wk-Neutralᵃ :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Neutralᵃ V (Γ₁ .defs) t → Neutralᵃ V (Γ₂ .defs) (wk ρ t)
  wk-Neutralᵃ (includedʳ ⊢ρ) = C.wk-Neutralᵃ ⊢ρ
  wk-Neutralᵃ (id ∇₂⊇∇₁ _)   =
    PE.subst (Neutralᵃ _ _) (PE.sym (wk-id _)) ∘→
    defn-wkNeutralᵃ ∇₂⊇∇₁

opaque

  -- Weakening for Whnf.

  wk-Whnf :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Whnf (Γ₁ .defs) t → Whnf (Γ₂ .defs) (wk ρ t)
  wk-Whnf (includedʳ ⊢ρ) = C.wk-Whnf ⊢ρ
  wk-Whnf (id ∇₂⊇∇₁ _)   =
    PE.subst (Whnf _) (PE.sym (wk-id _)) ∘→
    defn-wkWhnf ∇₂⊇∇₁

opaque

  -- Weakening for Type.

  wk-Type :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Type V (Γ₁ .defs) t → Type V (Γ₂ .defs) (wk ρ t)
  wk-Type (includedʳ ⊢ρ) = C.wk-Type ⊢ρ
  wk-Type (id ∇₂⊇∇₁ _)   =
    PE.subst (Type _ _) (PE.sym (wk-id _)) ∘→
    defn-wkType ∇₂⊇∇₁

opaque

  -- Weakening for Natural.

  wk-Natural :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Natural V (Γ₁ .defs) t → Natural V (Γ₂ .defs) (wk ρ t)
  wk-Natural (includedʳ ⊢ρ) = C.wk-Natural ⊢ρ
  wk-Natural (id ∇₂⊇∇₁ _)   =
    PE.subst (Natural _ _) (PE.sym (wk-id _)) ∘→
    defn-wkNatural ∇₂⊇∇₁

opaque

  -- Weakening for Function.

  wk-Function :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Function V (Γ₁ .defs) t → Function V (Γ₂ .defs) (wk ρ t)
  wk-Function (includedʳ ⊢ρ) = C.wk-Function ⊢ρ
  wk-Function (id ∇₂⊇∇₁ _)   =
    PE.subst (Function _ _) (PE.sym (wk-id _)) ∘→
    defn-wkFunction ∇₂⊇∇₁

opaque

  -- Weakening for Functionᵃ.

  wk-Functionᵃ :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Functionᵃ V (Γ₁ .defs) t → Functionᵃ V (Γ₂ .defs) (wk ρ t)
  wk-Functionᵃ (includedʳ ⊢ρ) = C.wk-Functionᵃ ⊢ρ
  wk-Functionᵃ (id ∇₂⊇∇₁ _)   =
    PE.subst (Functionᵃ _ _) (PE.sym (wk-id _)) ∘→
    defn-wkFunctionᵃ ∇₂⊇∇₁

opaque

  -- Weakening for Product.

  wk-Product :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Product V (Γ₁ .defs) t → Product V (Γ₂ .defs) (wk ρ t)
  wk-Product (includedʳ ⊢ρ) = C.wk-Product ⊢ρ
  wk-Product (id ∇₂⊇∇₁ _)   =
    PE.subst (Product _ _) (PE.sym (wk-id _)) ∘→
    defn-wkProduct ∇₂⊇∇₁

opaque

  -- Weakening for Productᵃ.

  wk-Productᵃ :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Productᵃ V (Γ₁ .defs) t → Productᵃ V (Γ₂ .defs) (wk ρ t)
  wk-Productᵃ (includedʳ ⊢ρ) = C.wk-Productᵃ ⊢ρ
  wk-Productᵃ (id ∇₂⊇∇₁ _)   =
    PE.subst (Productᵃ _ _) (PE.sym (wk-id _)) ∘→
    defn-wkProductᵃ ∇₂⊇∇₁

opaque

  -- Weakening for Identity.

  wk-Identity :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Identity V (Γ₁ .defs) t → Identity V (Γ₂ .defs) (wk ρ t)
  wk-Identity (includedʳ ⊢ρ) = C.wk-Identity ⊢ρ
  wk-Identity (id ∇₂⊇∇₁ _)   =
    PE.subst (Identity _ _) (PE.sym (wk-id _)) ∘→
    defn-wkIdentity ∇₂⊇∇₁

opaque

  -- Weakening for Identityᵃ.

  wk-Identityᵃ :
    Γ₂ ⊢ʷᵏʳ ρ ∷ Γ₁ →
    Identityᵃ V (Γ₁ .defs) t → Identityᵃ V (Γ₂ .defs) (wk ρ t)
  wk-Identityᵃ (includedʳ ⊢ρ) = C.wk-Identityᵃ ⊢ρ
  wk-Identityᵃ (id ∇₂⊇∇₁ _)   =
    PE.subst (Identityᵃ _ _) (PE.sym (wk-id _)) ∘→
    defn-wkIdentityᵃ ∇₂⊇∇₁

opaque

  -- If there is a _⊢ʷᵏʳ_∷_-weakening from Δ₁ to Δ₂, then
  -- Var-included or-empty Δ₂ is logically equivalent to
  -- Var-included or-empty Δ₁.

  wk-Var-included-or-empty :
    ∇₂ » Δ₂ ⊢ʷᵏʳ ρ ∷ ∇₁ » Δ₁ →
    Var-included or-empty Δ₂ ⇔
    Var-included or-empty Δ₁
  wk-Var-included-or-empty (id _ _)      = id⇔
  wk-Var-included-or-empty (includedʳ _) =
    (λ _ → included) , (λ _ → included)

opaque

  -- A variant of wk-Var-included-or-empty.

  wk-Var-included-or-empty→ :
    ∇₂ » Δ₂ ⊢ʷᵏʳ ρ ∷ ∇₁ » Δ₁ →
    ⦃ inc : Var-included or-empty Δ₂ ⦄ →
    Var-included or-empty Δ₁
  wk-Var-included-or-empty→ ⊢ρ ⦃ inc ⦄ =
    wk-Var-included-or-empty ⊢ρ .proj₁ inc

opaque

  -- A variant of wk-Var-included-or-empty.

  wk-Var-included-or-empty← :
    ∇₂ » Δ₂ ⊢ʷᵏʳ ρ ∷ ∇₁ » Δ₁ →
    ⦃ inc : Var-included or-empty Δ₁ ⦄ →
    Var-included or-empty Δ₂
  wk-Var-included-or-empty← ρ⊇ ⦃ inc ⦄ =
    wk-Var-included-or-empty ρ⊇ .proj₂ inc
