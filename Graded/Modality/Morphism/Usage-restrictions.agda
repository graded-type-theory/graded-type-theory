------------------------------------------------------------------------
-- Preserving/reflecting usage restrictions
------------------------------------------------------------------------

module Graded.Modality.Morphism.Usage-restrictions where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

open import Graded.Context
import Graded.Context.QuantityTranslation
open import Graded.Modality
import Graded.Modality.Properties
open import Graded.Modality.Morphism
open import Graded.Mode.Instances.Zero-one
import Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Usage.Erased-matches
open import Graded.Usage.Restrictions
open import Graded.Usage.Restrictions.Natrec
open import Graded.Usage.Restrictions.Instance as RI

open import Definition.Untyped.NotParametrised

private variable
  a₁ a₂ p₁ p₂ p₃           : Level
  M M₁ M₂                  : Set _
  P P₃                     : M → Set _
  f f₃ tr₁ tr₂ tr-Σ₁ tr-Σ₂ : M₁ → M₂
  p q r                    : M
  γ δ₁ δ₂ δ₃ δ₄            : Conₘ _ _
  𝕄 𝕄₁ 𝕄₂ 𝕄₃               : Modality _
  R R₁ R₂ R₃               : Usage-restrictions _ _
  m m₁ m₂ m₃               : Mode _
  s                        : Strength
  ⦃ ok₁ ok₂ ⦄              : T _
  nm nm₁ nm₂ nm₃           : Natrec-mode _
  v v₁ v₂ v₃               : Mode-variant _
  𝟘ᵐ-allowed 𝟘ᵐ-allowed₁
    𝟘ᵐ-allowed₂ 𝟘ᵐ-allowed₃ : Bool

------------------------------------------------------------------------
-- The relations _≈ᵐ_ and _≳ᵐ_

-- Two modes from two possibly different modalities are equivalent if
-- they are both 𝟙ᵐ or both 𝟘ᵐ (with arbitrary proofs).

infix 4 _≈ᵐ_

data _≈ᵐ_
       {M₁ : Set a₁} {M₂ : Set a₂}
       {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
       {v₁ : Mode-variant 𝕄₁} {v₂ : Mode-variant 𝕄₂} :
       Mode v₁ → Mode v₂ → Set (a₁ ⊔ a₂) where
  𝟘ᵐ : 𝟘ᵐ[ ok₁ ] ≈ᵐ 𝟘ᵐ[ ok₂ ]
  𝟙ᵐ : 𝟙ᵐ        ≈ᵐ 𝟙ᵐ

-- A variant of _≈ᵐ_. 𝟙ᵐ ≳ᵐ 𝟘ᵐ[ ok₂ ] is allowed if the "first"
-- modality is trivial.

infix 4 _≳ᵐ_

data _≳ᵐ_
       {M₁ : Set a₁} {M₂ : Set a₂}
       {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
       {v₁ : Mode-variant 𝕄₁} {v₂ : Mode-variant 𝕄₂} :
       Mode v₁ → Mode v₂ → Set (a₁ ⊔ a₂) where
  [_]   : m₁ ≈ᵐ m₂ → m₁ ≳ᵐ m₂
  𝟙ᵐ≳𝟘ᵐ : Modality.Trivial 𝕄₁ → 𝟙ᵐ ≳ᵐ 𝟘ᵐ[ ok₂ ]

opaque

  -- The relation _≈ᵐ_ is contained in propositional equality if it is
  -- restricted to modes for a single modality.

  ≈ᵐ→≡ : {m₁ m₂ : Mode v} → m₁ ≈ᵐ m₂ → m₁ ≡ m₂
  ≈ᵐ→≡ 𝟘ᵐ = 𝟘ᵐ-cong _
  ≈ᵐ→≡ 𝟙ᵐ = refl

opaque

  -- The relation _≈ᵐ_ is reflexive.

  ≈ᵐ-reflexive : m ≈ᵐ m
  ≈ᵐ-reflexive {m = 𝟘ᵐ} = 𝟘ᵐ
  ≈ᵐ-reflexive {m = 𝟙ᵐ} = 𝟙ᵐ

opaque

  -- The relation _≈ᵐ_ is symmetric.

  ≈ᵐ-symmetric : m₁ ≈ᵐ m₂ → m₂ ≈ᵐ m₁
  ≈ᵐ-symmetric 𝟘ᵐ = 𝟘ᵐ
  ≈ᵐ-symmetric 𝟙ᵐ = 𝟙ᵐ

opaque

  𝟘ᵐ?≈𝟘ᵐ? :
    T (Mode-variant.𝟘ᵐ-allowed v₁) ⇔ T (Mode-variant.𝟘ᵐ-allowed v₂) →
    𝟘ᵐ? v₁ ≈ᵐ 𝟘ᵐ? v₂
  𝟘ᵐ?≈𝟘ᵐ? {v₁} {v₂} ok = 𝟘ᵐ-allowed-elim v₁
    (λ ok₁ → subst₂ _≈ᵐ_ (sym (𝟘ᵐ?≡𝟘ᵐ v₁)) (sym (𝟘ᵐ?≡𝟘ᵐ v₂)) (𝟘ᵐ ⦃ ok₁ ⦄ ⦃ ok .proj₁ ok₁ ⦄ ))
    (λ not-ok₁ → subst₂ _≈ᵐ_ (sym (𝟘ᵐ?≡𝟙ᵐ⇔ v₁ .proj₂ not-ok₁))
       (sym (𝟘ᵐ?≡𝟙ᵐ⇔ v₂ .proj₂ (λ ok₂ → not-ok₁ (ok .proj₂ ok₂)))) 𝟙ᵐ)

opaque

  𝟘ᵐ?≈𝟘ᵐ?′ :
    ⦃ ok₁ : T (Mode-variant.𝟘ᵐ-allowed v₁) ⦄ →
    ⦃ ok₂ : T (Mode-variant.𝟘ᵐ-allowed v₂) ⦄ →
    𝟘ᵐ? v₁ ≈ᵐ 𝟘ᵐ? v₂
  𝟘ᵐ?≈𝟘ᵐ?′ ⦃ ok₁ ⦄ ⦃ ok₂ ⦄ = 𝟘ᵐ?≈𝟘ᵐ? ((λ _ → ok₂) , (λ _ → ok₁))

opaque

  -- If m₁ ≈ᵐ m₂ holds, then m₂ ≡ 𝟙ᵐ implies m₁ ≡ 𝟙ᵐ.

  ≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ : m₁ ≈ᵐ m₂ → m₂ ≡ 𝟙ᵐ → m₁ ≡ 𝟙ᵐ
  ≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ 𝟙ᵐ refl = refl
  ≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ 𝟘ᵐ ()

opaque

  -- If m₁ ≈ᵐ m₂ holds, then m₁ ≡ 𝟙ᵐ implies m₂ ≡ 𝟙ᵐ.

  ≈ᵐ→≡𝟙ᵐ←≡𝟙ᵐ : m₁ ≈ᵐ m₂ → m₁ ≡ 𝟙ᵐ → m₂ ≡ 𝟙ᵐ
  ≈ᵐ→≡𝟙ᵐ←≡𝟙ᵐ = ≈ᵐ→≡𝟙ᵐ→≡𝟙ᵐ ∘→ ≈ᵐ-symmetric

private opaque

  -- Some lemmas used below.

  ≈ᵐ→≤ᵉᵐ₁ : m₁ ≈ᵐ m₂ → f m₁ ≤ᵉᵐ f m₂
  ≈ᵐ→≤ᵉᵐ₁     𝟙ᵐ = ≤ᵉᵐ-reflexive
  ≈ᵐ→≤ᵉᵐ₁ {f} 𝟘ᵐ = subst (_≤ᵉᵐ_ _) (cong f (𝟘ᵐ-cong _)) ≤ᵉᵐ-reflexive

  ≈ᵐ→→₁ : m₁ ≈ᵐ m₂ → P m₁ → P m₂
  ≈ᵐ→→₁     𝟙ᵐ           = idᶠ
  ≈ᵐ→→₁ {P} (𝟘ᵐ ⦃ ok₁ ⦄) =
    subst (λ ok → P 𝟘ᵐ[ ok₁ ] → P 𝟘ᵐ[ ok ]) T-propositional idᶠ

  ≳ᵐ→←₁ :
    {P : Mode v → Set p} →
    m₁ ≳ᵐ m₂ → P m₂ → P m₁
  ≳ᵐ→←₁ [ m₁≈m₂ ] =
    ≈ᵐ→→₁ $ ≈ᵐ-symmetric m₁≈m₂
  ≳ᵐ→←₁ {v} (𝟙ᵐ≳𝟘ᵐ ⦃ ok₂ = ok ⦄ trivial) =
    ⊥-elim $ 𝟘ᵐ.non-trivial v ok trivial

  ≈ᵐ→≤ᵉᵐ₂ :
    {f₁ : Mode v₁ → Erased-matches}
    {f₂ : Mode v₂ → Erased-matches} →
    let module V₁ = Mode-variant v₁
        module V₂ = Mode-variant v₂
    in
    (T V₁.𝟘ᵐ-allowed → T V₂.𝟘ᵐ-allowed) →
    (∀ {m₁ m₂} → m₁ ≈ᵐ m₂ → f₁ m₁ ≤ᵉᵐ f₂ m₂) →
    (∀ {m₂ m₃} → m₂ ≈ᵐ m₃ → f₂ m₂ ≤ᵉᵐ f₃ m₃) →
    m₁ ≈ᵐ m₃ → f₁ m₁ ≤ᵉᵐ f₃ m₃
  ≈ᵐ→≤ᵉᵐ₂ _ hyp₁ hyp₂ 𝟙ᵐ =
    ≤ᵉᵐ-transitive (hyp₁ 𝟙ᵐ) (hyp₂ 𝟙ᵐ)
  ≈ᵐ→≤ᵉᵐ₂ 𝟘ᵐ→𝟘ᵐ hyp₁ hyp₂ (𝟘ᵐ ⦃ ok₁ ⦄) =
    case 𝟘ᵐ→𝟘ᵐ ok₁ of λ
      ok₂ →
    ≤ᵉᵐ-transitive (hyp₁ (𝟘ᵐ ⦃ ok₂ = ok₂ ⦄)) (hyp₂ (𝟘ᵐ ⦃ ok₁ = ok₂ ⦄))

  ≈ᵐ→→₂ :
    {P₁ : Mode v₁ → Set p₁}
    {P₂ : Mode v₂ → Set p₂} →
    (T (Mode-variant.𝟘ᵐ-allowed v₁) → T (Mode-variant.𝟘ᵐ-allowed v₂)) →
    (∀ {m₁ m₂} → m₁ ≈ᵐ m₂ → P₁ m₁ → P₂ m₂) →
    (∀ {m₂ m₃} → m₂ ≈ᵐ m₃ → P₂ m₂ → P₃ m₃) →
    m₁ ≈ᵐ m₃ → P₁ m₁ → P₃ m₃
  ≈ᵐ→→₂ _ hyp₁ hyp₂ 𝟙ᵐ =
    hyp₂ 𝟙ᵐ ∘→ hyp₁ 𝟙ᵐ
  ≈ᵐ→→₂ 𝟘ᵐ→𝟘ᵐ hyp₁ hyp₂ (𝟘ᵐ ⦃ ok₁ ⦄) =
    case 𝟘ᵐ→𝟘ᵐ ok₁ of λ
      ok₂ →
    hyp₂ (𝟘ᵐ ⦃ ok₁ = ok₂ ⦄) ∘→ hyp₁ (𝟘ᵐ ⦃ ok₂ = ok₂ ⦄)

  ≈ᵐ→≥ᵉᵐ₂ :
    {f₁ : Mode v₁ → Erased-matches}
    {f₂ : Mode v₂ → Erased-matches} →
    let module V₁ = Mode-variant v₁
        module V₂ = Mode-variant v₂
    in
    (T V₁.𝟘ᵐ-allowed → T V₂.𝟘ᵐ-allowed) →
    (∀ {m₂ m₃} → m₂ ≈ᵐ m₃ → f₃ m₃ ≤ᵉᵐ f₂ m₂) →
    (∀ {m₁ m₂} → m₁ ≈ᵐ m₂ → f₂ m₂ ≤ᵉᵐ f₁ m₁) →
    m₁ ≈ᵐ m₃ → f₃ m₃ ≤ᵉᵐ f₁ m₁
  ≈ᵐ→≥ᵉᵐ₂ _ hyp₁ hyp₂ 𝟙ᵐ =
    ≤ᵉᵐ-transitive (hyp₁ 𝟙ᵐ) (hyp₂ 𝟙ᵐ)
  ≈ᵐ→≥ᵉᵐ₂ 𝟘ᵐ→𝟘ᵐ hyp₁ hyp₂ (𝟘ᵐ ⦃ ok₁ ⦄ ⦃ ok₂ = ok₃ ⦄) =
    case 𝟘ᵐ→𝟘ᵐ ok₁ of λ
      ok₂ →
    ≤ᵉᵐ-transitive (hyp₁ (𝟘ᵐ ⦃ ok₁ = ok₂ ⦄)) (hyp₂ (𝟘ᵐ ⦃ ok₂ = ok₂ ⦄))

  ≳ᵐ→←₂ :
    {P₁ : Mode v₁ → Set p₁}
    {P₂ : Mode v₂ → Set p₂}
    {P₃ : Mode v₃ → Set p₃} →
    let module M₂ = Modality 𝕄₂
        module M₃ = Modality 𝕄₃
        module V₁ = Mode-variant v₁
        module V₂ = Mode-variant {𝕄 = 𝕄₂} v₂
        module V₃ = Mode-variant {𝕄 = 𝕄₃} v₃
    in
    (T V₁.𝟘ᵐ-allowed → T V₂.𝟘ᵐ-allowed) →
    (T V₃.𝟘ᵐ-allowed ⊎ M₃.Trivial → T V₂.𝟘ᵐ-allowed ⊎ M₂.Trivial) →
    (∀ {m₂ m₃} → m₂ ≳ᵐ m₃ → P₃ m₃ → P₂ m₂) →
    (∀ {m₁ m₂} → m₁ ≳ᵐ m₂ → P₂ m₂ → P₁ m₁) →
    m₁ ≳ᵐ m₃ → P₃ m₃ → P₁ m₁
  ≳ᵐ→←₂ _ _ hyp₁ hyp₂ [ 𝟙ᵐ ] =
    hyp₂ [ 𝟙ᵐ ] ∘→ hyp₁ [ 𝟙ᵐ ]
  ≳ᵐ→←₂ 𝟘ᵐ→𝟘ᵐ _ hyp₁ hyp₂ [ 𝟘ᵐ ⦃ ok₁ ⦄ ⦃ ok₂ = ok₃ ⦄ ] =
    case 𝟘ᵐ→𝟘ᵐ ok₁ of λ
      ok₂ →
    hyp₂ [ 𝟘ᵐ ⦃ ok₂ = ok₂ ⦄ ] ∘→ hyp₁ [ 𝟘ᵐ ⦃ ok₁ = ok₂ ⦄ ]
  ≳ᵐ→←₂
    {𝕄₂} {m₁ = 𝟙ᵐ} {m₃ = 𝟘ᵐ[ ok₃ ]}
    _ 𝟘ᵐ←𝟘ᵐ hyp₁ hyp₂ (𝟙ᵐ≳𝟘ᵐ ⦃ ok₂ = ok₃ ⦄ trivial₁) =
    case 𝟘ᵐ←𝟘ᵐ (inj₁ ok₃) of λ where
      (inj₁ ok₂) →
        hyp₂ (𝟙ᵐ≳𝟘ᵐ ⦃ ok₂ = ok₂ ⦄ trivial₁) ∘→
        hyp₁ [ 𝟘ᵐ ⦃ ok₁ = ok₂ ⦄ ]
      (inj₂ trivial₂) →
        hyp₂ [ 𝟙ᵐ ] ∘→ hyp₁ (𝟙ᵐ≳𝟘ᵐ trivial₂)

------------------------------------------------------------------------
-- The relation _≈ⁿᵐ_

-- The natrec-modes from two possibly different modalities are
-- equivalent if they are the same (with arbitrary proofs).

infix 4 _≈ⁿᵐ_

data _≈ⁿᵐ_
       {M₁ : Set a₁} {M₂ : Set a₂}
       {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂} :
       Natrec-mode 𝕄₁ → Natrec-mode 𝕄₂ → Set (a₁ ⊔ a₂) where
  Nr :
    ⦃ has-nr₁ : Has-nr M₁ 𝕄₁ ⦄ →
    ⦃ has-nr₂ : Has-nr M₂ 𝕄₂ ⦄ →
    Nr ≈ⁿᵐ Nr
  No-nr :
    No-nr ≈ⁿᵐ No-nr
  No-nr-glb :
    ⦃ ok₁ : Has-well-behaved-GLBs M₁ 𝕄₁ ⦄ →
    ⦃ ok₂ : Has-well-behaved-GLBs M₂ 𝕄₂ ⦄ →
    No-nr-glb ≈ⁿᵐ No-nr-glb

opaque

  -- The relation _≈ⁿᵐ_ is reflexive.

  ≈ⁿᵐ-refl : nm ≈ⁿᵐ nm
  ≈ⁿᵐ-refl {nm = Nr} = Nr
  ≈ⁿᵐ-refl {nm = No-nr} = No-nr
  ≈ⁿᵐ-refl {nm = No-nr-glb} = No-nr-glb

opaque

  -- The relation _≈ⁿᵐ_ is symmetric.

  ≈ⁿᵐ-sym : nm₁ ≈ⁿᵐ nm₂ → nm₂ ≈ⁿᵐ nm₁
  ≈ⁿᵐ-sym Nr = Nr
  ≈ⁿᵐ-sym No-nr = No-nr
  ≈ⁿᵐ-sym No-nr-glb = No-nr-glb

opaque

  -- The relation _≈ⁿᵐ_ is transitive.

  ≈ⁿᵐ-trans : nm₁ ≈ⁿᵐ nm₂ → nm₂ ≈ⁿᵐ nm₃ → nm₁ ≈ⁿᵐ nm₃
  ≈ⁿᵐ-trans Nr Nr = Nr
  ≈ⁿᵐ-trans No-nr No-nr = No-nr
  ≈ⁿᵐ-trans No-nr-glb No-nr-glb = No-nr-glb

opaque

  -- The predicate Natrec-mode-has-nr is preserved by _≈ⁿᵐ_

   Natrec-mode-has-nr-≈ⁿᵐ :
     nm₁ ≈ⁿᵐ nm₂ → Natrec-mode-has-nr _ nm₁ → Natrec-mode-has-nr _ nm₂
   Natrec-mode-has-nr-≈ⁿᵐ Nr _ = Nr
   Natrec-mode-has-nr-≈ⁿᵐ No-nr ()
   Natrec-mode-has-nr-≈ⁿᵐ No-nr-glb ()

opaque

  -- The predicate Natrec-mode-no-nr₁ is preserved by _≈ⁿᵐ_

   Natrec-mode-no-nr-≈ⁿᵐ :
     nm₁ ≈ⁿᵐ nm₂ → Natrec-mode-no-nr _ nm₁ → Natrec-mode-no-nr _ nm₂
   Natrec-mode-no-nr-≈ⁿᵐ No-nr _ = No-nr
   Natrec-mode-no-nr-≈ⁿᵐ Nr ()
   Natrec-mode-no-nr-≈ⁿᵐ No-nr-glb ()

opaque

  -- The predicate Natrec-mode-no-nr₂ is preserved by _≈ⁿᵐ_

   Natrec-mode-no-nr-glb-≈ⁿᵐ :
     nm₁ ≈ⁿᵐ nm₂ → Natrec-mode-no-nr-glb _ nm₁ → Natrec-mode-no-nr-glb _ nm₂
   Natrec-mode-no-nr-glb-≈ⁿᵐ No-nr-glb _ = No-nr-glb
   Natrec-mode-no-nr-glb-≈ⁿᵐ Nr ()
   Natrec-mode-no-nr-glb-≈ⁿᵐ No-nr ()

------------------------------------------------------------------------
-- Common-properties

-- Properties common to Are-preserving-usage-restrictions and
-- Are-reflecting-usage-restrictions.

record Common-properties
  {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  {v₁ : Mode-variant 𝕄₁} {v₂ : Mode-variant 𝕄₂}
  (R₁ : Usage-restrictions 𝕄₁ (Zero-one-isMode v₁))
  (R₂ : Usage-restrictions 𝕄₂ (Zero-one-isMode v₂)) :
  Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module V₁ = Mode-variant v₁
    module V₂ = Mode-variant v₂
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂

  field
    -- If 𝟘ᵐ is allowed for 𝕄₁, then 𝟘ᵐ is allowed for 𝕄₂.
    --
    -- Note that this property is also (at the time of writing) part
    -- of Is-morphism.
    𝟘ᵐ-preserved : T V₁.𝟘ᵐ-allowed → T V₂.𝟘ᵐ-allowed

    -- The natrec-mode is preserved
    natrec-mode-preserved : R₁.natrec-mode ≈ⁿᵐ R₂.natrec-mode

    -- The property that strong unit types act as sinks is preserved.
    starˢ-sink-preserved : R₁.starˢ-sink ≡ R₂.starˢ-sink

    -- R₁.Id-erased holds if and only if R₂.Id-erased holds.
    Id-erased-preserved : R₁.Id-erased ⇔ R₂.Id-erased

    -- If m₁ ≈ᵐ m₂, then R₁.erased-matches-for-J m₁ is bounded by
    -- R₂.erased-matches-for-J m₂.
    erased-matches-for-J-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.erased-matches-for-J m₁ ≤ᵉᵐ R₂.erased-matches-for-J m₂

    -- If m₁ ≈ᵐ m₂, then R₁.erased-matches-for-K m₁ is bounded by
    -- R₂.erased-matches-for-K m₂.
    erased-matches-for-K-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.erased-matches-for-K m₁ ≤ᵉᵐ R₂.erased-matches-for-K m₂

  opaque

    -- If Nr-available holds in the source usage restrictions then it
    -- also holds in the target usage restrictions.

    nr-in-second-if-in-first :
      ⦃ has-nr : R₁.Nr-available ⦄ →
      R₂.Nr-available
    nr-in-second-if-in-first ⦃ has-nr ⦄ =
      Natrec-mode-has-nr-≈ⁿᵐ natrec-mode-preserved has-nr

  opaque

    -- If Nr-not-available holds in the source usage restrictions then it
    -- also holds in the target usage restrictions.

    no-nr-in-second-if-in-first :
      ⦃ no-nr : R₁.Nr-not-available ⦄ →
      R₂.Nr-not-available
    no-nr-in-second-if-in-first ⦃ no-nr ⦄ =
      Natrec-mode-no-nr-≈ⁿᵐ natrec-mode-preserved no-nr

  opaque

    -- If Nr-not-available-GLB holds in the source usage restrictions
    -- then it also holds in the target usage restrictions.

    no-nr-glb-in-second-if-in-first :
      ⦃ no-nr : R₁.Nr-not-available-GLB ⦄ →
      R₂.Nr-not-available-GLB
    no-nr-glb-in-second-if-in-first ⦃ no-nr ⦄ =
      Natrec-mode-no-nr-glb-≈ⁿᵐ natrec-mode-preserved no-nr

  opaque

    -- If Nr-available holds in the target usage restrictions then it
    -- also holds in the source usage restrictions.

    nr-in-first-if-in-second :
      ⦃ has-nr : R₂.Nr-available ⦄ →
      R₁.Nr-available
    nr-in-first-if-in-second ⦃ has-nr ⦄ =
      Natrec-mode-has-nr-≈ⁿᵐ (≈ⁿᵐ-sym natrec-mode-preserved) has-nr

  opaque

    -- If Nr-not-available holds in the target usage restrictions then it
    -- also holds in the source usage restrictions.

    no-nr-in-first-if-in-second :
      ⦃ no-nr : R₂.Nr-not-available ⦄ →
      R₁.Nr-not-available
    no-nr-in-first-if-in-second ⦃ no-nr ⦄ =
      Natrec-mode-no-nr-≈ⁿᵐ (≈ⁿᵐ-sym natrec-mode-preserved) no-nr

  opaque

    -- If Nr-not-available-GLB holds in the target usage restrictions
    -- then it also holds in the source usage restrictions.

    no-nr-glb-in-first-if-in-second :
      ⦃ no-nr : R₂.Nr-not-available-GLB ⦄ →
      R₁.Nr-not-available-GLB
    no-nr-glb-in-first-if-in-second ⦃ no-nr ⦄ =
      Natrec-mode-no-nr-glb-≈ⁿᵐ (≈ⁿᵐ-sym natrec-mode-preserved) no-nr

opaque

  -- The relation Common-properties is reflexive.

  Common-properties-reflexive : Common-properties {v₁ = v} {v₂ = v} R R
  Common-properties-reflexive = λ where
      .𝟘ᵐ-preserved                   → idᶠ
      .natrec-mode-preserved          → ≈ⁿᵐ-refl
      .starˢ-sink-preserved           → refl
      .Id-erased-preserved            → id⇔
      .erased-matches-for-J-preserved → ≈ᵐ→≤ᵉᵐ₁
      .erased-matches-for-K-preserved → ≈ᵐ→≤ᵉᵐ₁
    where
    open Common-properties

opaque

  -- The relation Common-properties is transitive.

  Common-properties-transitive :
    Common-properties {v₁ = v₁} {v₂ = v₂} R₁ R₂ →
    Common-properties {v₁ = v₂} {v₂ = v₃} R₂ R₃ →
    Common-properties {v₁ = v₁} {v₂ = v₃} R₁ R₃
  Common-properties-transitive cp₁ cp₂ = λ where
      .𝟘ᵐ-preserved →
        CP₂.𝟘ᵐ-preserved ∘→ CP₁.𝟘ᵐ-preserved
      .natrec-mode-preserved →
        ≈ⁿᵐ-trans CP₁.natrec-mode-preserved CP₂.natrec-mode-preserved
      .starˢ-sink-preserved →
        trans CP₁.starˢ-sink-preserved CP₂.starˢ-sink-preserved
      .Id-erased-preserved →
        CP₂.Id-erased-preserved ∘⇔ CP₁.Id-erased-preserved
      .erased-matches-for-J-preserved →
        ≈ᵐ→≤ᵉᵐ₂ CP₁.𝟘ᵐ-preserved CP₁.erased-matches-for-J-preserved
          CP₂.erased-matches-for-J-preserved
      .erased-matches-for-K-preserved →
        ≈ᵐ→≤ᵉᵐ₂ CP₁.𝟘ᵐ-preserved CP₁.erased-matches-for-K-preserved
          CP₂.erased-matches-for-K-preserved
    where
    open Common-properties
    module CP₁ = Common-properties cp₁
    module CP₂ = Common-properties cp₂

------------------------------------------------------------------------
-- Are-preserving-usage-restrictions

-- The property of preserving Usage-restrictions.

record Are-preserving-usage-restrictions
         {M₁ : Set a₁} {M₂ : Set a₂}
         {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
         {v₁ : Mode-variant 𝕄₁} {v₂ : Mode-variant 𝕄₂}
         (R₁ : Usage-restrictions 𝕄₁ (Zero-one-isMode v₁))
         (R₂ : Usage-restrictions 𝕄₂ (Zero-one-isMode v₂))
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂
    module Mo = Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive

  open RI R₁
  open RI R₂

  field
    -- Common properties.
    common-properties : Common-properties R₁ R₂

  open Common-properties common-properties

  field

    -- The function tr is assumed to satisfy some properties depending
    -- on the chosen Natrec-mode. Note that by common-properties, both
    -- the source and target usage restrictions have the same
    -- Natrec-mode.

    nr-preserving :
      ⦃ has-nr₁ : R₁.Nr-available ⦄ →
      ⦃ has-nr₂ : R₂.Nr-available ⦄ →
      Is-nr-preserving-morphism 𝕄₁ 𝕄₂ tr

    no-nr-preserving :
      ⦃ no-nr₁ : R₁.Nr-not-available ⦄ →
      ⦃ no-nr₂ : R₂.Nr-not-available ⦄ →
      Mo.Is-no-nr-preserving 𝕄₁ 𝕄₂ v₁ v₂

    no-nr-glb-preserving :
      ⦃ no-nr₁ : R₁.Nr-not-available-GLB ⦄ →
      ⦃ no-nr₂ : R₂.Nr-not-available-GLB ⦄ →
      Is-no-nr-glb-preserving-morphism 𝕄₁ 𝕄₂ tr

    -- The functions tr and tr-Σ preserve the Prodrec-allowed
    -- property in a certain way.
    Prodrec-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.Prodrec-allowed m₁ r p q →
      R₂.Prodrec-allowed m₂ (tr r) (tr-Σ p) (tr q)

    -- The function tr preserves the Unitrec-allowed property in a
    -- certain way.
    Unitrec-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.Unitrec-allowed m₁ p q →
      R₂.Unitrec-allowed m₂ (tr p) (tr q)

    -- The function tr preserves the Emptyrec-allowed property in a
    -- certain way.
    Emptyrec-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.Emptyrec-allowed m₁ p →
      R₂.Emptyrec-allowed m₂ (tr p)

    -- The function tr preserves the []-cong-allowed-mode property in a
    -- certain way.
    []-cong-mode-preserved :
      m₁ ≈ᵐ m₂ →
      R₁.[]-cong-allowed-mode s m₁ →
      R₂.[]-cong-allowed-mode s m₂

  open Common-properties common-properties public

opaque

  -- For every value R the identity function preserves
  -- Usage-restrictions for R and R.

  Are-preserving-usage-restrictions-id :
    Are-preserving-usage-restrictions {v₁ = v} {v₂ = v} R R idᶠ idᶠ
  Are-preserving-usage-restrictions-id {R} = λ where
      .common-properties  → Common-properties-reflexive
      .nr-preserving ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
        case Nr-available-propositional _ has-nr₁ has-nr₂ of λ where
          refl → Is-nr-preserving-morphism-id
      .no-nr-preserving        → Is-no-nr-preserving-reflexive
      .no-nr-glb-preserving    → Is-no-nr-glb-preserving-morphism-id
      .Prodrec-preserved       → ≈ᵐ→→₁
      .Unitrec-preserved       → ≈ᵐ→→₁
      .Emptyrec-preserved      → ≈ᵐ→→₁
      .[]-cong-mode-preserved  → ≈ᵐ→→₁
    where
    open Are-preserving-usage-restrictions
    open Usage-restrictions R
    open RI R
    open Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive

opaque

  -- Composition preserves Are-preserving-usage-restrictions (in a
  -- certain sense).

  Are-preserving-usage-restrictions-∘ :
    {R₁ : Usage-restrictions 𝕄₁ (Zero-one-isMode v₁)} →
    {R₂ : Usage-restrictions 𝕄₂ (Zero-one-isMode v₂)} →
    {R₃ : Usage-restrictions 𝕄₃ (Zero-one-isMode v₃)} →
    Is-morphism 𝕄₂ 𝕄₃ tr₁ →
    Is-morphism 𝕄₁ 𝕄₂ tr₂ →
    Are-preserving-usage-restrictions R₂ R₃ tr₁ tr-Σ₁ →
    Are-preserving-usage-restrictions R₁ R₂ tr₂ tr-Σ₂ →
    Are-preserving-usage-restrictions
      R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
  Are-preserving-usage-restrictions-∘ {R₁} {R₂} {R₃} m₁ m₂ u₁ u₂ = λ where
      .common-properties →
        Common-properties-transitive P₂.common-properties
          P₁.common-properties
      .nr-preserving →
        let has-nr = P₂.nr-in-second-if-in-first
        in  Is-nr-preserving-morphism-∘
              ⦃ has-nr₂ = RI.Nr-available-Has-nr R₂ ⦃ has-nr ⦄ ⦄
              m₁ (P₁.nr-preserving ⦃ has-nr ⦄)
              (P₂.nr-preserving ⦃ has-nr₂ = has-nr ⦄)
      .no-nr-preserving →
        let no-nr = P₂.no-nr-in-second-if-in-first
        in  Is-no-nr-preserving-transitive
              G.first-trivial-if-second-trivial
              (P₁.no-nr-preserving ⦃ no-nr ⦄)
              (P₂.no-nr-preserving ⦃ no-nr₂ = no-nr ⦄)
      .no-nr-glb-preserving →
        let no-nr = P₂.no-nr-glb-in-second-if-in-first
        in  Is-no-nr-glb-preserving-morphism-∘
              (P₁.no-nr-glb-preserving ⦃ no-nr ⦄)
              (P₂.no-nr-glb-preserving ⦃ no-nr₂ = no-nr ⦄)
      .Prodrec-preserved →
        ≈ᵐ→→₂ P₂.𝟘ᵐ-preserved P₂.Prodrec-preserved P₁.Prodrec-preserved
      .Unitrec-preserved →
        ≈ᵐ→→₂ P₂.𝟘ᵐ-preserved P₂.Unitrec-preserved P₁.Unitrec-preserved
      .Emptyrec-preserved →
        ≈ᵐ→→₂ P₂.𝟘ᵐ-preserved P₂.Emptyrec-preserved
          P₁.Emptyrec-preserved
      .[]-cong-mode-preserved →
        ≈ᵐ→→₂ P₂.𝟘ᵐ-preserved P₂.[]-cong-mode-preserved
          P₁.[]-cong-mode-preserved
    where
    open Are-preserving-usage-restrictions
    open RI R₁
    open RI R₂
    open RI R₃
    module P₁ = Are-preserving-usage-restrictions u₁
    module P₂ = Are-preserving-usage-restrictions u₂
    module G = Is-morphism m₂
    open P₁
    open Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive

------------------------------------------------------------------------
-- Are-reflecting-usage-restrictions

-- The property of reflecting Usage-restrictions.

record Are-reflecting-usage-restrictions
         {M₁ : Set a₁} {M₂ : Set a₂}
         {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
         {v₁ : Mode-variant 𝕄₁} {v₂ : Mode-variant 𝕄₂}
         (R₁ : Usage-restrictions 𝕄₁ (Zero-one-isMode v₁))
         (R₂ : Usage-restrictions 𝕄₂ (Zero-one-isMode v₂))
         (tr tr-Σ : M₁ → M₂) : Set (a₁ ⊔ a₂) where
  no-eta-equality

  private
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module V₁ = Mode-variant v₁
    module V₂ = Mode-variant v₂
    module R₁ = Usage-restrictions R₁
    module R₂ = Usage-restrictions R₂
    module Mo = Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive

  open RI R₁
  open RI R₂

  field
    -- Common properties.
    common-properties : Common-properties R₁ R₂

    -- If 𝟘ᵐ is allowed for 𝕄₂ or 𝕄₂ is trivial, then 𝟘ᵐ is allowed
    -- for 𝕄₁ or 𝕄₁ is trivial.
    𝟘ᵐ-reflected :
      T V₂.𝟘ᵐ-allowed ⊎ M₂.Trivial → T V₁.𝟘ᵐ-allowed ⊎ M₁.Trivial

    -- The function tr is assumed to satisfy some properties depending
    -- on the chosen Natrec-mode. Note that by common-properties, both
    -- the source and target usage restrictions have the same
    -- Natrec-mode.

    nr-reflected :
      ⦃ has-nr₁ : R₁.Nr-available ⦄ →
      ⦃ has-nr₂ : R₂.Nr-available ⦄ →
      Is-nr-reflecting-morphism 𝕄₁ 𝕄₂ tr

    no-nr-reflected :
      ⦃ no-nr₁ : R₁.Nr-not-available ⦄ →
      ⦃ no-nr₂ : R₂.Nr-not-available ⦄ →
      Mo.Is-no-nr-reflecting-morphism 𝕄₁ 𝕄₂ v₁ v₂ tr

    no-nr-glb-reflected :
      ⦃ no-nr₁ : R₁.Nr-not-available-GLB ⦄ →
      ⦃ no-nr₂ : R₂.Nr-not-available-GLB ⦄ →
      Is-no-nr-glb-reflecting-morphism 𝕄₁ 𝕄₂ tr

    -- The functions tr and tr-Σ reflect the Prodrec-allowed
    -- property in a certain way.
    Prodrec-reflected :
      m₁ ≳ᵐ m₂ →
      R₂.Prodrec-allowed m₂ (tr r) (tr-Σ p) (tr q) →
      R₁.Prodrec-allowed m₁ r p q

    -- The function tr reflects the Unitrec-allowed property in a
    -- certain way.
    Unitrec-reflected :
      m₁ ≳ᵐ m₂ →
      R₂.Unitrec-allowed m₂ (tr p) (tr q) →
      R₁.Unitrec-allowed m₁ p q

    -- The function tr reflects the Emptyrec-allowed property in a
    -- certain way.
    Emptyrec-reflected :
      m₁ ≳ᵐ m₂ →
      R₂.Emptyrec-allowed m₂ (tr p) →
      R₁.Emptyrec-allowed m₁ p

    -- The []-cong-allowed-mode property is reflected in a certain
    -- way.
    []-cong-mode-reflected :
      m₁ ≳ᵐ m₂ →
      R₂.[]-cong-allowed-mode s m₂ →
      R₁.[]-cong-allowed-mode s m₁

    -- If m₁ ≈ᵐ m₂ holds, then R₂.Erased-matches-for-J m₂ is bounded
    -- by R₁.erased-matches-for-J m₁.
    erased-matches-for-J-reflected :
      m₁ ≈ᵐ m₂ →
      R₂.erased-matches-for-J m₂ ≤ᵉᵐ R₁.erased-matches-for-J m₁

    -- If m₁ ≈ᵐ m₂ holds, then R₂.Erased-matches-for-K m₂ is bounded
    -- by R₁.erased-matches-for-K m₁.
    erased-matches-for-K-reflected :
      m₁ ≈ᵐ m₂ →
      R₂.erased-matches-for-K m₂ ≤ᵉᵐ R₁.erased-matches-for-K m₁

  open Common-properties common-properties public

  opaque

    -- If 𝟘ᵐ is allowed in the target modality but not the source
    -- modality, then the source modality is trivial.
    trivial : ¬ T V₁.𝟘ᵐ-allowed → T V₂.𝟘ᵐ-allowed → M₁.Trivial
    trivial not-ok ok =
      case 𝟘ᵐ-reflected (inj₁ ok) of λ where
        (inj₁ ok) → ⊥-elim (not-ok ok)
        (inj₂ trivial) → trivial

opaque

  -- For every value R the identity function reflects
  -- Usage-restrictions for R and R.

  Are-reflecting-usage-restrictions-id :
    {R : Usage-restrictions 𝕄 (Zero-one-isMode v)} →
    Are-reflecting-usage-restrictions R R idᶠ idᶠ
  Are-reflecting-usage-restrictions-id {𝕄} {v} {R} = λ where
      .common-properties              → Common-properties-reflexive
      .𝟘ᵐ-reflected                   → idᶠ
      .nr-reflected ⦃ has-nr₁ ⦄ ⦃ has-nr₂ ⦄ →
        case Nr-available-propositional _ has-nr₁ has-nr₂ of λ where
          refl → Is-nr-reflecting-morphism-id
      .no-nr-reflected                → Is-no-nr-reflecting-morphism-id
      .no-nr-glb-reflected            → Is-no-nr-glb-reflecting-morphism-id
      .Prodrec-reflected              → ≳ᵐ→←₁
      .Unitrec-reflected              → ≳ᵐ→←₁
      .Emptyrec-reflected             → ≳ᵐ→←₁
      .[]-cong-mode-reflected         → ≳ᵐ→←₁
      .erased-matches-for-J-reflected → ≈ᵐ→≤ᵉᵐ₁ ∘→ ≈ᵐ-symmetric
      .erased-matches-for-K-reflected → ≈ᵐ→≤ᵉᵐ₁ ∘→ ≈ᵐ-symmetric
    where
    open Are-reflecting-usage-restrictions
    open Graded.Modality.Properties 𝕄
    open Modality 𝕄
    open RI R
    open Usage-restrictions R
    open Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive

opaque

  -- Composition preserves Are-reflecting-usage-restrictions (in a
  -- certain sense).

  Are-reflecting-usage-restrictions-∘ :
    {R₁ : Usage-restrictions 𝕄₁ (Zero-one-isMode v₁)} →
    {R₂ : Usage-restrictions 𝕄₂ (Zero-one-isMode v₂)} →
    {R₃ : Usage-restrictions 𝕄₃ (Zero-one-isMode v₃)} →
    Is-morphism 𝕄₂ 𝕄₃ tr₁ →
    Are-reflecting-usage-restrictions R₂ R₃ tr₁ tr-Σ₁ →
    Are-reflecting-usage-restrictions R₁ R₂ tr₂ tr-Σ₂ →
    Are-reflecting-usage-restrictions
      R₁ R₃ (tr₁ ∘→ tr₂) (tr-Σ₁ ∘→ tr-Σ₂)
  Are-reflecting-usage-restrictions-∘
    {𝕄₁} {𝕄₂} {𝕄₃} {R₁} {R₂} {R₃} m m₁ m₂ = λ where
      .common-properties →
        Common-properties-transitive R₂.common-properties
          R₁.common-properties
      .𝟘ᵐ-reflected →
        R₂.𝟘ᵐ-reflected ∘→ R₁.𝟘ᵐ-reflected
      .nr-reflected →
        let has-nr = R₂.nr-in-second-if-in-first
        in  Is-nr-reflecting-morphism-∘
              ⦃ has-nr₂ = RI.Nr-available-Has-nr R₂ ⦃ has-nr ⦄ ⦄
              m (R₁.nr-reflected ⦃ has-nr ⦄)
              (R₂.nr-reflected ⦃ has-nr₂ = has-nr ⦄)
      .no-nr-reflected →
        let no-nr = R₂.no-nr-in-second-if-in-first
        in  Is-no-nr-reflecting-morphism-∘
              m (R₁.no-nr-reflected ⦃ no-nr ⦄)
              (R₂.no-nr-reflected ⦃ no-nr₂ = no-nr ⦄)
      .no-nr-glb-reflected →
        let no-nr = R₂.no-nr-glb-in-second-if-in-first
        in  Is-no-nr-glb-reflecting-morphism-∘
              m (R₁.no-nr-glb-reflected ⦃ no-nr ⦄)
              (R₂.no-nr-glb-reflected ⦃ no-nr₂ = no-nr ⦄)
      .Prodrec-reflected →
        ≳ᵐ→←₂ R₂.𝟘ᵐ-preserved R₁.𝟘ᵐ-reflected R₁.Prodrec-reflected
          R₂.Prodrec-reflected
      .Unitrec-reflected →
        ≳ᵐ→←₂ R₂.𝟘ᵐ-preserved R₁.𝟘ᵐ-reflected R₁.Unitrec-reflected
          R₂.Unitrec-reflected
      .Emptyrec-reflected →
         ≳ᵐ→←₂ R₂.𝟘ᵐ-preserved R₁.𝟘ᵐ-reflected R₁.Emptyrec-reflected
          R₂.Emptyrec-reflected
      .[]-cong-mode-reflected →
        ≳ᵐ→←₂ R₂.𝟘ᵐ-preserved R₁.𝟘ᵐ-reflected R₁.[]-cong-mode-reflected
          R₂.[]-cong-mode-reflected
      .erased-matches-for-J-reflected →
        ≈ᵐ→≥ᵉᵐ₂ R₂.𝟘ᵐ-preserved R₁.erased-matches-for-J-reflected
          R₂.erased-matches-for-J-reflected
      .erased-matches-for-K-reflected →
        ≈ᵐ→≥ᵉᵐ₂ R₂.𝟘ᵐ-preserved R₁.erased-matches-for-K-reflected
          R₂.erased-matches-for-K-reflected
    where
    open Are-reflecting-usage-restrictions
    module M₁ = Modality 𝕄₁
    module M₂ = Modality 𝕄₂
    module M₃ = Modality 𝕄₃
    module R₁ = Are-reflecting-usage-restrictions m₁
    module R₂ = Are-reflecting-usage-restrictions m₂
    open RI R₁
    open RI R₃
    open Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive
