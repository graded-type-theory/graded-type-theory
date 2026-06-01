------------------------------------------------------------------------
-- Combined weakening for definition and variable contexts
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Weakening.Combined
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Weakening R as W hiding (wk; _•ₜ_)
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Properties.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Whnf M type-variant

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private variable
  k m₁ m₂ n₁ n₂   : Nat
  V               : Set _
  ∇ ∇₁ ∇₂         : DCon _ _
  Δ Δ₁ Δ₂         : Con _ _
  Γ Γ₁ Γ₂ Γ₃      : Cons _ _
  A A₁ A₂ t t₁ t₂ : Term _
  ρ ρ₁ ρ₂         : Wk _ _
  𝓙               : Judgement _

------------------------------------------------------------------------
-- The type _⊢ʷᵏ_∷_

opaque

  infix 4 _⊢ʷᵏ_∷_

  -- Weakening for both definition and variable contexts.

  _⊢ʷᵏ_∷_ : Cons m₂ n₂ → Wk n₂ n₁ → Cons m₁ n₁ → Set a
  ∇₂ » Δ₂ ⊢ʷᵏ ρ ∷ ∇₁ » Δ₁ =
    » ∇₂ ⊇ ∇₁ × ∇₂ » ρ ∷ʷ Δ₂ ⊇ Δ₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- A characterisation lemma for _⊢ʷᵏ_∷_.

  ⊢ʷᵏ⇔ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ ⇔
    (» Γ₂ .defs ⊇ Γ₁ .defs × Γ₂ .defs » ρ ∷ʷ Γ₂ .vars ⊇ Γ₁ .vars)
  ⊢ʷᵏ⇔ = id⇔

------------------------------------------------------------------------
-- Some lemmas

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Conversion from _»_∷ʷ_⊇_ to _⊢ʷᵏ_∷_.

  »∷ʷ⊇→⊢ʷᵏ : ∇ » ρ ∷ʷ Δ₂ ⊇ Δ₁ → ∇ » Δ₂ ⊢ʷᵏ ρ ∷ ∇ » Δ₁
  »∷ʷ⊇→⊢ʷᵏ = id⊇ ,_

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Conversion from _»_⊇_ to _⊢ʷᵏ_∷_.

  »⊇→⊢ʷᵏ : » ∇₂ ⊇ ∇₁ → ∇₂ »⊢ Δ → ∇₂ » Δ ⊢ʷᵏ id ∷ ∇₁ » Δ
  »⊇→⊢ʷᵏ ∇₂⊇∇₁ ⊢Δ = ∇₂⊇∇₁ , idʷ ⊢Δ

opaque
  unfolding _⊢ʷᵏ_∷_

  -- If Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ holds, then Γ₂ is well-formed.

  wf-⊢ʷᵏ : Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ → ⊢ Γ₂
  wf-⊢ʷᵏ (_ , ⊢ρ) = W.wf-∷ʷ⊇ ⊢ρ

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Identity.

  ⊢ʷᵏid : ⊢ Γ → Γ ⊢ʷᵏ id ∷ Γ
  ⊢ʷᵏid ⊢Γ = id⊇ , idʷ ⊢Γ

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Composition.

  ⊢ʷᵏ• :
    Γ₃ ⊢ʷᵏ ρ₂ ∷ Γ₂ →
    Γ₂ ⊢ʷᵏ ρ₁ ∷ Γ₁ →
    Γ₃ ⊢ʷᵏ ρ₂ • ρ₁ ∷ Γ₁
  ⊢ʷᵏ• (∇₂⊆∇₃ , ⊢ρ₂) (∇₁⊆∇₂ , ⊢ρ₁) =
    »⊇-trans ∇₂⊆∇₃ ∇₁⊆∇₂ , (⊢ρ₂ W.•ₜʷ defn-wkWkʷ ∇₂⊆∇₃ ⊢ρ₁)

opaque
  unfolding _⊢ʷᵏ_∷_

  -- If ρ is well-formed, then stepn ρ k is also well-formed, given a
  -- certain assumption.

  ⊢ʷᵏstepn :
    Γ₂ .defs » drop k (Γ₂ .vars) ⊢ʷᵏ ρ ∷ Γ₁ → ⊢ Γ₂ →
    Γ₂ ⊢ʷᵏ stepn ρ k ∷ Γ₁
  ⊢ʷᵏstepn (∇⊇∇ , ρ⊇) ⊢Δ = ∇⊇∇ , stepnʷʷ ρ⊇ ⊢Δ

opaque
  unfolding _⊢ʷᵏ_∷_

  -- If ρ is well-formed, then lift ρ is also well-formed, given a
  -- certain assumption.

  ⊢ʷᵏlift :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ → Γ₂ ⊢ wk ρ A →
    Γ₂ »∙ wk ρ A ⊢ʷᵏ lift ρ ∷ Γ₁ »∙ A
  ⊢ʷᵏlift (∇₂⊇∇₁ , ρ⊇) ⊢A = ∇₂⊇∇₁ , liftʷʷ ρ⊇ ⊢A

opaque

  -- If ρ is well-formed, then liftn ρ k is also well-formed, given a
  -- certain assumption.

  ⊢ʷᵏliftn :
    ∇₂ » Δ₂ ⊢ʷᵏ ρ ∷ ∇₁ » drop k Δ₁ → ∇₂ »⊢ Δ₂ ∙[ k ][ Δ₁ ][ ρ ]ʷ →
    ∇₂ » Δ₂ ∙[ k ][ Δ₁ ][ ρ ]ʷ ⊢ʷᵏ liftn ρ k ∷ ∇₁ » Δ₁
  ⊢ʷᵏliftn {k = 0}                 ⊢ρ _      = ⊢ρ
  ⊢ʷᵏliftn {k = 1+ k} {Δ₁ = _ ∙ _} ⊢ρ (∙ ⊢A) =
    ⊢ʷᵏlift (⊢ʷᵏliftn ⊢ρ (wf ⊢A)) ⊢A

opaque
  unfolding _⊢ʷᵏ_∷_

  -- The weakening stepn id k is well-formed, given a certain
  -- assumption.

  ⊢ʷᵏdrop : ∇ »⊢ Δ → ∇ » Δ ⊢ʷᵏ stepn id k ∷ ∇ » drop k Δ
  ⊢ʷᵏdrop ⊢Δ = id⊇ , ʷ⊇-drop ⊢Δ

opaque
  unfolding _⊢ʷᵏ_∷_

  -- If Δ is well-formed, then wk₀ is a well-formed weakening from ε
  -- to Δ.

  ⊢ʷᵏwk₀ : ∇ »⊢ Δ → ∇ » Δ ⊢ʷᵏ wk₀ ∷ ∇ » ε
  ⊢ʷᵏwk₀ ⊢Δ = id⊇ , W.wk₀∷ʷ⊇ ⊢Δ

------------------------------------------------------------------------
-- Weakening lemmas

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for various judgements.

  wk-⊢ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢[ 𝓙 ] → Γ₂ ⊢[ mapJ (wk ρ) 𝓙 ]
  wk-⊢ (∇₂⊇∇₁ , ρ∷) = W.wk ρ∷ ∘→ defn-wk ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for single-step reduction for terms.

  wk-⇒∷ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ t₁ ⇒ t₂ ∷ A → Γ₂ ⊢ wk ρ t₁ ⇒ wk ρ t₂ ∷ wk ρ A
  wk-⇒∷ (∇₂⊇∇₁ , ρ∷) = W.wkRedTerm ρ∷ ∘→ defn-wkRedTerm ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for multi-step reduction for terms.

  wk-⇒*∷ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ t₁ ⇒* t₂ ∷ A → Γ₂ ⊢ wk ρ t₁ ⇒* wk ρ t₂ ∷ wk ρ A
  wk-⇒*∷ (∇₂⊇∇₁ , ρ∷) = W.wkRed*Term ρ∷ ∘→ defn-wkRed*Term ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for reduction to WHNF for terms.

  wk-↘∷ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ t₁ ↘ t₂ ∷ A → Γ₂ ⊢ wk ρ t₁ ↘ wk ρ t₂ ∷ wk ρ A
  wk-↘∷ (∇₂⊇∇₁ , ρ∷) = W.wkRed↘Term ρ∷ ∘→ defn-wkRed↘Term ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for single-step reduction for types.

  wk-⇒ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ A₁ ⇒ A₂ → Γ₂ ⊢ wk ρ A₁ ⇒ wk ρ A₂
  wk-⇒ (∇₂⊇∇₁ , ρ∷) = W.wkRed ρ∷ ∘→ defn-wkRed ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for multi-step reduction for types.

  wk-⇒* :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ A₁ ⇒* A₂ → Γ₂ ⊢ wk ρ A₁ ⇒* wk ρ A₂
  wk-⇒* (∇₂⊇∇₁ , ρ∷) = W.wkRed* ρ∷ ∘→ defn-wkRed* ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for reduction to WHNF for terms.

  wk-↘ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Γ₁ ⊢ A₁ ↘ A₂ → Γ₂ ⊢ wk ρ A₁ ↘ wk ρ A₂
  wk-↘ (∇₂⊇∇₁ , ρ∷) = W.wkRed↘ ρ∷ ∘→ defn-wkRed↘ ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Neutral.

  wk-Neutral :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Neutral V (Γ₁ .defs) t → Neutral V (Γ₂ .defs) (wk ρ t)
  wk-Neutral (∇₂⊇∇₁ , _) = wkNeutral _ ∘→ defn-wkNeutral ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Neutralᵃ.

  wk-Neutralᵃ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Neutralᵃ V (Γ₁ .defs) t → Neutralᵃ V (Γ₂ .defs) (wk ρ t)
  wk-Neutralᵃ (∇₂⊇∇₁ , _) = wkNeutralᵃ ∘→ defn-wkNeutralᵃ ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Whnf.

  wk-Whnf :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Whnf (Γ₁ .defs) t → Whnf (Γ₂ .defs) (wk ρ t)
  wk-Whnf (∇₂⊇∇₁ , _) = wkWhnf _ ∘→ defn-wkWhnf ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Type.

  wk-Type :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Type V (Γ₁ .defs) t → Type V (Γ₂ .defs) (wk ρ t)
  wk-Type (∇₂⊇∇₁ , _) = wkType _ ∘→ defn-wkType ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Natural.

  wk-Natural :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Natural V (Γ₁ .defs) t → Natural V (Γ₂ .defs) (wk ρ t)
  wk-Natural (∇₂⊇∇₁ , _) = wkNatural _ ∘→ defn-wkNatural ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Function.

  wk-Function :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Function V (Γ₁ .defs) t → Function V (Γ₂ .defs) (wk ρ t)
  wk-Function (∇₂⊇∇₁ , _) = wkFunction _ ∘→ defn-wkFunction ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Functionᵃ.

  wk-Functionᵃ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Functionᵃ V (Γ₁ .defs) t → Functionᵃ V (Γ₂ .defs) (wk ρ t)
  wk-Functionᵃ (∇₂⊇∇₁ , _) = wkFunctionᵃ ∘→ defn-wkFunctionᵃ ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Product.

  wk-Product :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Product V (Γ₁ .defs) t → Product V (Γ₂ .defs) (wk ρ t)
  wk-Product (∇₂⊇∇₁ , _) = wkProduct _ ∘→ defn-wkProduct ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Productᵃ.

  wk-Productᵃ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Productᵃ V (Γ₁ .defs) t → Productᵃ V (Γ₂ .defs) (wk ρ t)
  wk-Productᵃ (∇₂⊇∇₁ , _) = wkProductᵃ ∘→ defn-wkProductᵃ ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Identity.

  wk-Identity :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Identity V (Γ₁ .defs) t → Identity V (Γ₂ .defs) (wk ρ t)
  wk-Identity (∇₂⊇∇₁ , _) = wkIdentity ∘→ defn-wkIdentity ∇₂⊇∇₁

opaque
  unfolding _⊢ʷᵏ_∷_

  -- Weakening for Identityᵃ.

  wk-Identityᵃ :
    Γ₂ ⊢ʷᵏ ρ ∷ Γ₁ →
    Identityᵃ V (Γ₁ .defs) t → Identityᵃ V (Γ₂ .defs) (wk ρ t)
  wk-Identityᵃ (∇₂⊇∇₁ , _) = wkIdentityᵃ ∘→ defn-wkIdentityᵃ ∇₂⊇∇₁
