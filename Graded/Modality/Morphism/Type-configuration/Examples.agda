------------------------------------------------------------------------
-- Lemmas related to Is-Σ-morphism-TC/Is-Σ-order-embedding-TC and
-- specific type configuration transformers (and no-type-restrictions)
------------------------------------------------------------------------

module Graded.Modality.Morphism.Type-configuration.Examples where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Product as Σ
open import Tools.PropositionalEquality
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎

open import Configuration-types
open import Configuration-types.Type-configuration

open import Graded.Modality
open import Graded.Modality.Instances.Affine
  using (affineModality)
open import Graded.Modality.Instances.Erasure
  using (𝟘; ω)
open import Graded.Modality.Instances.Erasure.Modality
  using (ErasureModality)
open import Graded.Modality.Instances.Linear-or-affine
  using (𝟘; 𝟙; ≤𝟙; ≤ω; linear-or-affine)
open import Graded.Modality.Instances.Linearity
  using (linearityModality)
open import Graded.Modality.Instances.Unit using (UnitModality)
open import Graded.Modality.Instances.Zero-one-many
  using (𝟘; 𝟙; ω; zero-one-many-modality; zero-one-many-has-omega)
open import Graded.Modality.Morphism.Examples
open import Graded.Modality.Morphism.Type-configuration
import Graded.Modality.Properties

open import Definition.Untyped.NotParametrised
open import Definition.Untyped.QuantityTranslation

private variable
  b₁ b₂ trp 𝟙≤𝟘 : Bool
  TC TC₁ TC₂    : Type-configuration _
  s             : Strength
  M₁ M₂         : Set _
  𝕄₁ 𝕄₂         : Modality _
  tr tr-Σ       : M₁ → M₂

-- An instance used below

private instance
  zero-one-many-has-omega′ : Has-omega _ (zero-one-many-modality 𝟙≤𝟘)
  zero-one-many-has-omega′ = zero-one-many-has-omega _

  {-# OVERLAPPABLE zero-one-many-has-omega′ #-}

------------------------------------------------------------------------
-- Lemmas related to no-type-restrictions

opaque

  -- A lemma related to Is-Σ-morphism-TC and no-type-restrictions.

  M-no-type-restrictions :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (¬ Modality.Trivial 𝕄₁ → ¬ Modality.Trivial 𝕄₂) →
    (¬ Modality.Trivial 𝕄₁ → tr M₁.𝟘 ≡ M₂.𝟘) →
    Is-Σ-morphism-TC trp
      (no-type-restrictions 𝕄₁ b₁ b₂)
      (no-type-restrictions 𝕄₂ b₁ b₂)
      tr tr-Σ
  M-no-type-restrictions hyp₁ hyp₂ =
    λ where
      .unfolding-mode-preserved      → refl
      .level-support-preserved       → level-type small≤small
      .Omega-plus-preserved          → _
      .Unitʷ-η-preserved ()
      .Unit-preserved                → _
      .ΠΣ-preserved                  → _
      .Opacity-preserved _           → lift ∘→ Lift.lower
      .K-preserved                   → lift ∘→ Lift.lower
      .[]-cong-preserved             → hyp₁
      .Equality-reflection-preserved → lift ∘→ Lift.lower
      .Quot-preserved                → hyp₁
      .Quot-allowed→tr-𝟘≡𝟘           → hyp₂
    where
    open Is-Σ-morphism-TC

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- no-type-restrictions.

  OE-no-type-restrictions :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    Is-Σ-order-embedding-TC trp
      (no-type-restrictions 𝕄₁ b₁ b₂)
      (no-type-restrictions 𝕄₂ b₁ b₂)
      tr tr-Σ
  OE-no-type-restrictions {𝕄₁} = λ where
      .unfolding-mode-reflected      → refl
      .level-support-reflected       → level-type small≤small
      .Unitʷ-η-reflected ()
      .Unit-reflected                → _
      .ΠΣ-reflected                  → _
      .Opacity-reflected             → lift ∘→ Lift.lower
      .K-reflected                   → lift ∘→ Lift.lower
      .[]-cong-reflected _           → case MP₁.trivial? of λ where
        (yes triv) → inj₂ triv
        (no not)   → inj₁ not
      .Equality-reflection-reflected → lift ∘→ Lift.lower
      .Quot-reflected _              → case MP₁.trivial? of λ where
        (yes triv) → inj₂ triv
        (no not)   → inj₁ not
    where
    module MP₁ = Graded.Modality.Properties 𝕄₁
    open Is-Σ-order-embedding-TC

------------------------------------------------------------------------
-- Lemmas related to certain type configuration transformers

-- A lemma related to Is-Σ-morphism-TC and equal-binder-quantities.

M-equal-binder-quantities :
  Is-Σ-morphism-TC trp TC₁ TC₂ tr tr →
  Is-Σ-morphism-TC trp
    (equal-binder-quantities 𝕄₁ TC₁)
    (equal-binder-quantities 𝕄₂ TC₂)
    tr tr
M-equal-binder-quantities {trp} {tr} r =
  record
    { unfolding-mode-preserved = TC.unfolding-mode-preserved
    ; level-support-preserved  = TC.level-support-preserved
    ; Omega-plus-preserved     = TC.Omega-plus-preserved
    ; Unitʷ-η-preserved        = TC.Unitʷ-η-preserved
    ; Unit-preserved           = TC.Unit-preserved
    ; ΠΣ-preserved             = λ {b = b} → λ where
        (bn , refl) →
            TC.ΠΣ-preserved bn
          , tr-BinderMode-one-function trp _ _ refl b
    ; Opacity-preserved             = TC.Opacity-preserved
    ; K-preserved                   = TC.K-preserved
    ; []-cong-preserved             = TC.[]-cong-preserved
    ; Equality-reflection-preserved = TC.Equality-reflection-preserved
    ; Quot-preserved                = TC.Quot-preserved
    ; Quot-allowed→tr-𝟘≡𝟘           = TC.Quot-allowed→tr-𝟘≡𝟘
    }
  where
  module TC = Is-Σ-morphism-TC r

-- A lemma related to Is-Σ-order-embedding-TC and
-- equal-binder-quantities.

OE-equal-binder-quantities :
  (∀ {p q} → tr p ≡ tr q → p ≡ q) →
  Is-Σ-order-embedding-TC trp TC₁ TC₂ tr tr →
  Is-Σ-order-embedding-TC trp
    (equal-binder-quantities 𝕄₁ TC₁)
    (equal-binder-quantities 𝕄₂ TC₂)
    tr tr
OE-equal-binder-quantities {tr} {trp} inj r = record
  { unfolding-mode-reflected = unfolding-mode-reflected
  ; level-support-reflected  = level-support-reflected
  ; Unitʷ-η-reflected        = Unitʷ-η-reflected
  ; Unit-reflected           = Unit-reflected
  ; ΠΣ-reflected             =
      λ {b = b} {p = p} {q = q} (bn , eq) →
          ΠΣ-reflected bn
        , inj (
            tr p                         ≡˘⟨ tr-BinderMode-one-function trp _ _ refl b ⟩
            tr-BinderMode trp tr tr b p  ≡⟨ eq ⟩
            tr q                         ∎)
  ; Opacity-reflected             = Opacity-reflected
  ; K-reflected                   = K-reflected
  ; []-cong-reflected             = []-cong-reflected
  ; Equality-reflection-reflected = Equality-reflection-reflected
  ; Quot-reflected                = Quot-reflected
  }
  where
  open Is-Σ-order-embedding-TC r
  open Tools.Reasoning.PropositionalEquality

-- A lemma related to Is-Σ-morphism-TC and second-ΠΣ-quantities-𝟘.

M-second-ΠΣ-quantities-𝟘 :
  tr (Modality.𝟘 𝕄₁) ≡ Modality.𝟘 𝕄₂ →
  Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
  Is-Σ-morphism-TC trp
    (second-ΠΣ-quantities-𝟘 𝕄₁ TC₁)
    (second-ΠΣ-quantities-𝟘 𝕄₂ TC₂)
    tr tr-Σ
M-second-ΠΣ-quantities-𝟘 tr-𝟘 r = record
  { unfolding-mode-preserved = unfolding-mode-preserved
  ; level-support-preserved  = level-support-preserved
  ; Omega-plus-preserved     = Omega-plus-preserved
  ; Unitʷ-η-preserved        = Unitʷ-η-preserved
  ; Unit-preserved           = Unit-preserved
  ; ΠΣ-preserved             = λ where
      (b , refl) → ΠΣ-preserved b , tr-𝟘
  ; Opacity-preserved             = Opacity-preserved
  ; K-preserved                   = K-preserved
  ; []-cong-preserved             = []-cong-preserved
  ; Equality-reflection-preserved = Equality-reflection-preserved
  ; Quot-preserved                = Quot-preserved
  ; Quot-allowed→tr-𝟘≡𝟘           = Quot-allowed→tr-𝟘≡𝟘
  }
  where
  open Is-Σ-morphism-TC r

-- A lemma related to Is-Σ-order-embedding-TC and
-- second-ΠΣ-quantities-𝟘.

OE-second-ΠΣ-quantities-𝟘 :
  (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) →
  Is-Σ-order-embedding-TC trp TC₁ TC₂ tr tr-Σ →
  Is-Σ-order-embedding-TC trp
    (second-ΠΣ-quantities-𝟘 𝕄₁ TC₁)
    (second-ΠΣ-quantities-𝟘 𝕄₂ TC₂)
    tr tr-Σ
OE-second-ΠΣ-quantities-𝟘 tr-𝟘 r = record
  { unfolding-mode-reflected      = unfolding-mode-reflected
  ; level-support-reflected       = level-support-reflected
  ; Unitʷ-η-reflected             = Unitʷ-η-reflected
  ; Unit-reflected                = Unit-reflected
  ; ΠΣ-reflected                  = Σ.map ΠΣ-reflected tr-𝟘
  ; Opacity-reflected             = Opacity-reflected
  ; K-reflected                   = K-reflected
  ; []-cong-reflected             = []-cong-reflected
  ; Equality-reflection-reflected = Equality-reflection-reflected
  ; Quot-reflected                = Quot-reflected
  }
  where
  open Is-Σ-order-embedding-TC r

-- A lemma related to Is-Σ-morphism-TC and
-- second-ΠΣ-quantities-𝟘-or-ω.

M-second-ΠΣ-quantities-𝟘-or-ω :
  ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄ ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
  (Modality.𝟙 𝕄₁ ≢ Modality.𝟘 𝕄₁ →
   tr (Modality.𝟘 𝕄₁) ≡ Modality.𝟘 𝕄₂) →
  (∀ {p} → tr p ≡ Has-omega.ω has-ω₂ ⇔ p ≡ Has-omega.ω has-ω₁) →
  (∀ {p} → tr-Σ p ≡ Has-omega.ω has-ω₂ ⇔ p ≡ Has-omega.ω has-ω₁) →
  Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
  Is-Σ-morphism-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ TC₂)
    tr tr-Σ
M-second-ΠΣ-quantities-𝟘-or-ω
  {𝕄₁} {𝕄₂} {tr} {tr-Σ} {trp} ⦃ has-ω₁ ⦄ ⦃ has-ω₂ ⦄ tr-𝟘 tr-ω tr-Σ-ω r = record
  { unfolding-mode-preserved = unfolding-mode-preserved
  ; level-support-preserved  = level-support-preserved
  ; Omega-plus-preserved     = Omega-plus-preserved
  ; Unitʷ-η-preserved        = Unitʷ-η-preserved
  ; Unit-preserved           = Unit-preserved
  ; ΠΣ-preserved             = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-preserved bn , lemma₁ b is-𝟘 , lemma₃ b not-𝟘
  ; Opacity-preserved             = Opacity-preserved
  ; K-preserved                   = K-preserved
  ; []-cong-preserved             = []-cong-preserved
  ; Equality-reflection-preserved = Equality-reflection-preserved
  ; Quot-preserved                = Quot-preserved
  ; Quot-allowed→tr-𝟘≡𝟘           = Quot-allowed→tr-𝟘≡𝟘
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Is-Σ-morphism-TC r
  open Graded.Modality.Properties 𝕄₁

  lemma₁ :
    ∀ {p q} b →
    (p ≡ Has-omega.ω has-ω₁ → q ≡ Has-omega.ω has-ω₁) →
    tr-BinderMode trp tr tr-Σ b p ≡ Has-omega.ω has-ω₂ → tr q ≡ Has-omega.ω has-ω₂
  lemma₁ {p = p} {q = q} BMΠ hyp =
    tr p ≡ Has-omega.ω has-ω₂  →⟨ tr-ω .proj₁ ⟩
    p ≡ Has-omega.ω has-ω₁    →⟨ hyp ⟩
    q ≡ Has-omega.ω has-ω₁    →⟨ tr-ω .proj₂ ⟩
    tr q ≡ Has-omega.ω has-ω₂ □
  lemma₁ {p = p} {q = q} (BMΣ _) hyp =
    tr-Σ p ≡ Has-omega.ω has-ω₂ →⟨ tr-Σ-ω .proj₁ ⟩
    p ≡ Has-omega.ω has-ω₁      →⟨ hyp ⟩
    q ≡ Has-omega.ω has-ω₁      →⟨ tr-ω .proj₂ ⟩
    tr q ≡ Has-omega.ω has-ω₂   □

  lemma₂ :
    ∀ {p q} →
    (p ≢ Has-omega.ω has-ω₁ → q ≡ M₁.𝟘) →
    p ≢ Has-omega.ω has-ω₁ → tr q ≡ M₂.𝟘
  lemma₂ {p = p} {q = q} hyp p≢ω₁ =
    case hyp p≢ω₁ of λ {
      refl →
    tr-𝟘 (≢→non-trivial p≢ω₁) }

  lemma₃ :
    ∀ {p q} b →
    (p ≢ Has-omega.ω has-ω₁ → q ≡ M₁.𝟘) →
    tr-BinderMode trp tr tr-Σ b p ≢ Has-omega.ω has-ω₂ → tr q ≡ M₂.𝟘
  lemma₃ {p = p} {q = q} BMΠ hyp =
    tr p ≢ Has-omega.ω has-ω₂ →⟨ _∘→ tr-ω .proj₂ ⟩
    p ≢ Has-omega.ω has-ω₁    →⟨ lemma₂ hyp ⟩
    tr q ≡ M₂.𝟘               □
  lemma₃ {p = p} {q = q} (BMΣ _) hyp =
    tr-Σ p ≢ Has-omega.ω has-ω₂ →⟨ _∘→ tr-Σ-ω .proj₂ ⟩
    p ≢ Has-omega.ω has-ω₁      →⟨ lemma₂ hyp ⟩
    tr q ≡ M₂.𝟘                 □

-- A lemma related to Is-Σ-order-embedding-TC and
-- second-ΠΣ-quantities-𝟘-or-ω.

OE-second-ΠΣ-quantities-𝟘-or-ω :
  ⦃ has-ω₁ : Has-omega _ 𝕄₁ ⦄ ⦃ has-ω₂ : Has-omega _ 𝕄₂ ⦄ →
  (∀ {p} → tr p ≡ Modality.𝟘 𝕄₂ → p ≡ Modality.𝟘 𝕄₁) →
  (∀ {p} → tr p ≡ Has-omega.ω has-ω₂ ⇔ p ≡ Has-omega.ω has-ω₁) →
  (∀ {p} → tr-Σ p ≡ Has-omega.ω has-ω₂ ⇔ p ≡ Has-omega.ω has-ω₁) →
  Is-Σ-order-embedding-TC trp TC₁ TC₂ tr tr-Σ →
  Is-Σ-order-embedding-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ TC₂)
    tr tr-Σ
OE-second-ΠΣ-quantities-𝟘-or-ω
  {𝕄₁} {𝕄₂} {tr} {tr-Σ} {trp} ⦃ has-ω₁ ⦄ ⦃ has-ω₂ ⦄ tr-𝟘 tr-ω tr-Σ-ω r = record
  { unfolding-mode-reflected = unfolding-mode-reflected
  ; level-support-reflected  = level-support-reflected
  ; Unitʷ-η-reflected        = Unitʷ-η-reflected
  ; Unit-reflected           = Unit-reflected
  ; ΠΣ-reflected             = λ {b = b} (bn , is-𝟘 , not-𝟘) →
      ΠΣ-reflected bn , lemma₁ b is-𝟘 , lemma₂ b not-𝟘
  ; Opacity-reflected             = Opacity-reflected
  ; K-reflected                   = K-reflected
  ; []-cong-reflected             = []-cong-reflected
  ; Equality-reflection-reflected = Equality-reflection-reflected
  ; Quot-reflected                = Quot-reflected
  }
  where
  module M₁ = Modality 𝕄₁
  module M₂ = Modality 𝕄₂
  open Is-Σ-order-embedding-TC r

  lemma₁ :
    ∀ {p q} b →
    (tr-BinderMode trp tr tr-Σ b p ≡ Has-omega.ω has-ω₂ → tr q ≡ Has-omega.ω has-ω₂) →
    p ≡ Has-omega.ω has-ω₁ → q ≡ Has-omega.ω has-ω₁
  lemma₁ {p = p} {q = q} BMΠ hyp =
    p ≡ Has-omega.ω has-ω₁    →⟨ tr-ω .proj₂ ⟩
    tr p ≡ Has-omega.ω has-ω₂ →⟨ hyp ⟩
    tr q ≡ Has-omega.ω has-ω₂ →⟨ tr-ω .proj₁ ⟩
    q ≡ Has-omega.ω has-ω₁    □
  lemma₁ {p = p} {q = q} (BMΣ _) hyp =
    p ≡ Has-omega.ω has-ω₁      →⟨ tr-Σ-ω .proj₂ ⟩
    tr-Σ p ≡ Has-omega.ω has-ω₂ →⟨ hyp ⟩
    tr q ≡ Has-omega.ω has-ω₂   →⟨ tr-ω .proj₁ ⟩
    q ≡ Has-omega.ω has-ω₁      □

  lemma₂ :
    ∀ {p q} b →
    (tr-BinderMode trp tr tr-Σ b p ≢ Has-omega.ω has-ω₂ → tr q ≡ M₂.𝟘) →
    p ≢ Has-omega.ω has-ω₁ → q ≡ M₁.𝟘
  lemma₂ {p = p} {q = q} BMΠ hyp =
    p ≢ Has-omega.ω has-ω₁    →⟨ _∘→ tr-ω .proj₁ ⟩
    tr p ≢ Has-omega.ω has-ω₂ →⟨ hyp ⟩
    tr q ≡ M₂.𝟘               →⟨ tr-𝟘 ⟩
    q ≡ M₁.𝟘                  □
  lemma₂ {p = p} {q = q} (BMΣ _) hyp =
    p ≢ Has-omega.ω has-ω₁      →⟨ _∘→ tr-Σ-ω .proj₁ ⟩
    tr-Σ p ≢ Has-omega.ω has-ω₂ →⟨ hyp ⟩
    tr q ≡ M₂.𝟘                 →⟨ tr-𝟘 ⟩
    q ≡ M₁.𝟘                    □

opaque

 -- A lemma related to Is-Σ-morphism-TC and strong-types-restricted.

 M-strong-types-restricted :
   tr-Σ (Modality.𝟙 𝕄₁) ≡ Modality.𝟙 𝕄₂ →
   Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
   Is-Σ-morphism-TC trp
     (strong-types-restricted 𝕄₁ TC₁)
     (strong-types-restricted 𝕄₂ TC₂)
     tr tr-Σ
 M-strong-types-restricted hyp r =
   record
     { unfolding-mode-preserved =
         unfolding-mode-preserved
     ; level-support-preserved =
         level-support-preserved
     ; Omega-plus-preserved =
         Omega-plus-preserved
     ; Unitʷ-η-preserved =
         Unitʷ-η-preserved
     ; Unit-preserved =
         Σ.map Unit-preserved idᶠ
     ; ΠΣ-preserved =
         Σ.map ΠΣ-preserved λ where
           hyp′ refl → case hyp′ refl of λ where
             refl → hyp
     ; Opacity-preserved =
         Opacity-preserved
     ; K-preserved =
         K-preserved
     ; []-cong-preserved =
         Σ.map []-cong-preserved idᶠ
     ; Equality-reflection-preserved =
         Equality-reflection-preserved
     ; Quot-preserved =
         Quot-preserved
     ; Quot-allowed→tr-𝟘≡𝟘 =
         Quot-allowed→tr-𝟘≡𝟘
     }
   where
   open Is-Σ-morphism-TC r

opaque

 -- A lemma related to Is-Σ-order-embedding-TC and
 -- strong-types-restricted.

 OE-strong-types-restricted :
   (∀ {p} → tr-Σ p ≡ Modality.𝟙 𝕄₂ → p ≡ Modality.𝟙 𝕄₁) →
   (∀ {s} →
    Modality.Trivial 𝕄₂ →
    ¬ Type-configuration.[]-cong-allowed TC₁ s) →
   Is-Σ-order-embedding-TC trp TC₁ TC₂ tr tr-Σ →
   Is-Σ-order-embedding-TC trp
     (strong-types-restricted 𝕄₁ TC₁)
     (strong-types-restricted 𝕄₂ TC₂)
     tr tr-Σ
 OE-strong-types-restricted hyp₁ hyp₂ r = record
   { unfolding-mode-reflected =
       unfolding-mode-reflected
   ; level-support-reflected =
       level-support-reflected
   ; Unitʷ-η-reflected =
       Unitʷ-η-reflected
   ; Unit-reflected =
       Σ.map Unit-reflected idᶠ
   ; ΠΣ-reflected =
       Σ.map ΠΣ-reflected (λ { hyp refl → hyp₁ (hyp refl) })
   ; Opacity-reflected =
       Opacity-reflected
   ; K-reflected =
       K-reflected
   ; []-cong-reflected = λ {s = s} → λ where
       (inj₁ (ok₂ , s≢𝕤)) →
         case []-cong-reflected (inj₁ ok₂) of λ where
           (inj₁ ok₁)      → inj₁ (ok₁ , s≢𝕤)
           (inj₂ trivial₁) → inj₂ trivial₁
       (inj₂ trivial₂) →
         case []-cong-reflected {s = s} (inj₂ trivial₂) of λ where
           (inj₁ ok₁)      → ⊥-elim $ hyp₂ trivial₂ ok₁
           (inj₂ trivial₁) → inj₂ trivial₁
   ; Equality-reflection-reflected =
       Equality-reflection-reflected
   ; Quot-reflected =
       Quot-reflected
   }
   where
   open Is-Σ-order-embedding-TC r

opaque

 -- A lemma related to Is-Σ-morphism-TC and no-strong-types.

 M-no-strong-types :
   Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
   Is-Σ-morphism-TC trp
     (no-strong-types 𝕄₁ TC₁)
     (no-strong-types 𝕄₂ TC₂)
     tr tr-Σ
 M-no-strong-types r = record
   { unfolding-mode-preserved =
       unfolding-mode-preserved
   ; level-support-preserved =
       level-support-preserved
   ; Omega-plus-preserved =
       Omega-plus-preserved
   ; Unitʷ-η-preserved =
       Unitʷ-η-preserved
   ; Unit-preserved =
       Σ.map Unit-preserved idᶠ
   ; ΠΣ-preserved =
       Σ.map ΠΣ-preserved (lift ∘→ Lift.lower)
   ; Opacity-preserved =
       Opacity-preserved
   ; K-preserved =
       K-preserved
   ; []-cong-preserved =
       Σ.map []-cong-preserved idᶠ
   ; Equality-reflection-preserved =
       Equality-reflection-preserved
   ; Quot-preserved =
       Quot-preserved
   ; Quot-allowed→tr-𝟘≡𝟘 =
       Quot-allowed→tr-𝟘≡𝟘
   }
   where
   open Is-Σ-morphism-TC r

opaque

 -- A lemma related to Is-Σ-order-embedding-TC and no-strong-types.

 OE-no-strong-types :
   (∀ {s} →
    Modality.Trivial 𝕄₂ →
    ¬ Type-configuration.[]-cong-allowed TC₁ s) →
   Is-Σ-order-embedding-TC trp TC₁ TC₂ tr tr-Σ →
   Is-Σ-order-embedding-TC trp
     (no-strong-types 𝕄₁ TC₁)
     (no-strong-types 𝕄₂ TC₂)
     tr tr-Σ
 OE-no-strong-types hyp r = record
   { unfolding-mode-reflected =
       unfolding-mode-reflected
   ; level-support-reflected =
       level-support-reflected
   ; Unitʷ-η-reflected =
       Unitʷ-η-reflected
   ; Unit-reflected =
       Σ.map Unit-reflected idᶠ
   ; ΠΣ-reflected =
       Σ.map ΠΣ-reflected (lift ∘→ Lift.lower)
   ; Opacity-reflected =
       Opacity-reflected
   ; K-reflected =
       K-reflected
   ; []-cong-reflected = λ {s = s} → λ where
       (inj₁ (ok₂ , s≢𝕤)) →
         case []-cong-reflected (inj₁ ok₂) of λ where
           (inj₁ ok₁)      → inj₁ (ok₁ , s≢𝕤)
           (inj₂ trivial₁) → inj₂ trivial₁
       (inj₂ trivial₂) →
         case []-cong-reflected {s = s} (inj₂ trivial₂) of λ where
           (inj₁ ok₁)      → ⊥-elim $ hyp trivial₂ ok₁
           (inj₂ trivial₁) → inj₂ trivial₁
   ; Equality-reflection-reflected =
       Equality-reflection-reflected
   ; Quot-reflected =
       Quot-reflected
   }
   where
   open Is-Σ-order-embedding-TC r

opaque

  -- A lemma related to Is-Σ-morphism-TC and with-[]-cong.

  M-with-[]-cong :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (¬ M₁.Trivial → ¬ M₂.Trivial × tr M₁.𝟘 ≡ M₂.𝟘 × tr-Σ M₁.𝟘 ≡ M₂.𝟘) →
    Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-morphism-TC trp
      (with-[]-cong 𝕄₁ TC₁)
      (with-[]-cong 𝕄₂ TC₂)
      tr tr-Σ
  M-with-[]-cong hyp r = record
    { unfolding-mode-preserved =
        unfolding-mode-preserved
    ; level-support-preserved =
        level-support-preserved
    ; Omega-plus-preserved =
        Omega-plus-preserved
    ; Unitʷ-η-preserved =
        Unitʷ-η-preserved
    ; Unit-preserved =
        ⊎.map Unit-preserved (proj₁ ∘→ hyp)
    ; ΠΣ-preserved = λ {b = b} ok →
        case singleton b of λ where
          (BMΠ , refl) →
            ΠΣ-preserved ok
          (BMΣ s , refl) →
            ⊎.map
              ΠΣ-preserved
              (λ { (non-trivial , refl , refl) →
                   let non-trivial , tr-𝟘≡𝟘 , tr-Σ-𝟘≡𝟘 =
                         hyp non-trivial
                   in
                   non-trivial , tr-Σ-𝟘≡𝟘 , tr-𝟘≡𝟘 })
              ok
    ; Opacity-preserved =
        Opacity-preserved
    ; K-preserved =
        K-preserved
    ; []-cong-preserved =
        ⊎.map []-cong-preserved (proj₁ ∘→ hyp)
    ; Equality-reflection-preserved =
        Equality-reflection-preserved
    ; Quot-preserved =
        Quot-preserved
    ; Quot-allowed→tr-𝟘≡𝟘 =
        Quot-allowed→tr-𝟘≡𝟘
    }
    where
    open Is-Σ-morphism-TC r

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and with-[]-cong.

  OE-with-[]-cong :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (¬ M₂.Trivial →
     ¬ M₁.Trivial ×
     (∀ p → tr p ≡ M₂.𝟘 → p ≡ M₁.𝟘) ×
     (∀ p → tr-Σ p ≡ M₂.𝟘 → p ≡ M₁.𝟘)) →
    Is-Σ-order-embedding-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-order-embedding-TC trp
      (with-[]-cong 𝕄₁ TC₁)
      (with-[]-cong 𝕄₂ TC₂)
      tr tr-Σ
  OE-with-[]-cong {𝕄₁} hyp r = record
    { unfolding-mode-reflected =
        unfolding-mode-reflected
    ; level-support-reflected =
        level-support-reflected
    ; Unitʷ-η-reflected =
        Unitʷ-η-reflected
    ; Unit-reflected =
        ⊎.map Unit-reflected (proj₁ ∘→ hyp)
    ; ΠΣ-reflected =
        λ {b = b} ok →
        case singleton b of λ where
          (BMΠ , refl) →
            ΠΣ-reflected ok
          (BMΣ s , refl) →
            ⊎.map
              ΠΣ-reflected
              (λ (non-trivial , tr-Σ-p≡𝟘 , tr-q≡𝟘) →
                 let non-trivial , tr≡𝟘→≡𝟘 , tr-Σ≡𝟘→≡𝟘 =
                       hyp non-trivial
                 in
                 non-trivial , tr-Σ≡𝟘→≡𝟘 _ tr-Σ-p≡𝟘 , tr≡𝟘→≡𝟘 _ tr-q≡𝟘)
              ok
    ; Opacity-reflected =
        Opacity-reflected
    ; K-reflected =
        K-reflected
    ; []-cong-reflected = λ _ → case trivial? of λ where
        (yes trivial)    → inj₂ trivial
        (no non-trivial) → inj₁ (inj₂ non-trivial)
    ; Equality-reflection-reflected =
        Equality-reflection-reflected
    ; Quot-reflected =
        Quot-reflected
    }
    where
    open Graded.Modality.Properties 𝕄₁
    open Is-Σ-order-embedding-TC r

opaque

  -- A lemma related to Is-Σ-morphism-TC and no-[]-cong.

  M-no-[]-cong :
    Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-morphism-TC trp
      (no-[]-cong 𝕄₁ TC₁)
      (no-[]-cong 𝕄₂ TC₂)
      tr tr-Σ
  M-no-[]-cong r = record
    { unfolding-mode-preserved      = unfolding-mode-preserved
    ; level-support-preserved       = level-support-preserved
    ; Omega-plus-preserved          = Omega-plus-preserved
    ; Unitʷ-η-preserved             = Unitʷ-η-preserved
    ; Unit-preserved                = Unit-preserved
    ; ΠΣ-preserved                  = ΠΣ-preserved
    ; Opacity-preserved             = Opacity-preserved
    ; K-preserved                   = K-preserved
    ; []-cong-preserved             = λ ()
    ; Equality-reflection-preserved = Equality-reflection-preserved
    ; Quot-preserved                = Quot-preserved
    ; Quot-allowed→tr-𝟘≡𝟘           = Quot-allowed→tr-𝟘≡𝟘
    }
    where
    open Is-Σ-morphism-TC r

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and no-[]-cong.

  OE-no-[]-cong :
    (∀ {s} →
     Modality.Trivial 𝕄₂ →
     ¬ Type-configuration.[]-cong-allowed TC₁ s) →
    Is-Σ-order-embedding-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-order-embedding-TC trp
      (no-[]-cong 𝕄₁ TC₁)
      (no-[]-cong 𝕄₂ TC₂)
      tr tr-Σ
  OE-no-[]-cong hyp r = record
    { unfolding-mode-reflected = unfolding-mode-reflected
    ; level-support-reflected  = level-support-reflected
    ; Unitʷ-η-reflected        = Unitʷ-η-reflected
    ; Unit-reflected           = Unit-reflected
    ; ΠΣ-reflected             = ΠΣ-reflected
    ; Opacity-reflected        = Opacity-reflected
    ; K-reflected              = K-reflected
    ; []-cong-reflected        = λ {s = s} → λ where
        (inj₁ ())
        (inj₂ trivial) →
          case []-cong-reflected {s = s} (inj₂ trivial) of λ where
            (inj₁ ok)      → ⊥-elim $ hyp trivial ok
            (inj₂ trivial) → inj₂ trivial
    ; Equality-reflection-reflected = Equality-reflection-reflected
    ; Quot-reflected                = Quot-reflected
    }
    where
    open Is-Σ-order-embedding-TC r

opaque

  -- A lemma related to Is-Σ-morphism-TC and _with-η-for-Unitʷ.

  M-with-η-for-Unitʷʳ :
    Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-morphism-TC trp TC₁ (_with-η-for-Unitʷ 𝕄₂ TC₂) tr tr-Σ
  M-with-η-for-Unitʷʳ m = record
    { unfolding-mode-preserved      = unfolding-mode-preserved
    ; level-support-preserved       = level-support-preserved
    ; Omega-plus-preserved          = Omega-plus-preserved
    ; Unitʷ-η-preserved             = _
    ; Unit-preserved                = Unit-preserved
    ; ΠΣ-preserved                  = ΠΣ-preserved
    ; Opacity-preserved             = Opacity-preserved
    ; K-preserved                   = K-preserved
    ; []-cong-preserved             = []-cong-preserved
    ; Equality-reflection-preserved = Equality-reflection-preserved
    ; Quot-preserved                = Quot-preserved
    ; Quot-allowed→tr-𝟘≡𝟘           = Quot-allowed→tr-𝟘≡𝟘
    }
    where
    open Is-Σ-morphism-TC m

opaque

  -- A lemma related to Is-Σ-morphism-TC and _with-η-for-Unitʷ.

  M-with-η-for-Unitʷ :
    Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-morphism-TC trp
      (_with-η-for-Unitʷ 𝕄₁ TC₁)
      (_with-η-for-Unitʷ 𝕄₂ TC₂)
      tr tr-Σ
  M-with-η-for-Unitʷ m = record
    { unfolding-mode-preserved      = unfolding-mode-preserved
    ; level-support-preserved       = level-support-preserved
    ; Omega-plus-preserved          = Omega-plus-preserved
    ; Unitʷ-η-preserved             = _
    ; Unit-preserved                = Unit-preserved
    ; ΠΣ-preserved                  = ΠΣ-preserved
    ; Opacity-preserved             = Opacity-preserved
    ; K-preserved                   = K-preserved
    ; []-cong-preserved             = []-cong-preserved
    ; Equality-reflection-preserved = Equality-reflection-preserved
    ; Quot-preserved                = Quot-preserved
    ; Quot-allowed→tr-𝟘≡𝟘           = Quot-allowed→tr-𝟘≡𝟘
    }
    where
    open Is-Σ-morphism-TC m

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and _with-η-for-Unitʷ.

  OE-with-η-for-Unitʷ :
    Is-Σ-order-embedding-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-order-embedding-TC trp
      (_with-η-for-Unitʷ 𝕄₁ TC₁)
      (_with-η-for-Unitʷ 𝕄₂ TC₂)
      tr tr-Σ
  OE-with-η-for-Unitʷ oe = record
    { unfolding-mode-reflected      = unfolding-mode-reflected
    ; level-support-reflected       = level-support-reflected
    ; Unitʷ-η-reflected             = _
    ; Unit-reflected                = Unit-reflected
    ; ΠΣ-reflected                  = ΠΣ-reflected
    ; Opacity-reflected             = Opacity-reflected
    ; K-reflected                   = K-reflected
    ; []-cong-reflected             = []-cong-reflected
    ; Equality-reflection-reflected = Equality-reflection-reflected
    ; Quot-reflected                = Quot-reflected
    }
    where
    open Is-Σ-order-embedding-TC oe

opaque

  -- A lemma related to Is-Σ-morphism-TC and with-equality-reflection.

  M-with-equality-reflectionʳ :
    Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-morphism-TC true TC₁
      (with-equality-reflection 𝕄₂ TC₂)
      tr tr-Σ
  M-with-equality-reflectionʳ r = record
    { unfolding-mode-preserved      = unfolding-mode-preserved
    ; level-support-preserved       = level-support-preserved
    ; Omega-plus-preserved          = Omega-plus-preserved
    ; Unitʷ-η-preserved             = Unitʷ-η-preserved
    ; Unit-preserved                = Unit-preserved
    ; ΠΣ-preserved                  = ΠΣ-preserved
    ; Opacity-preserved             = λ ¬-⊤ _ → lift (¬-⊤ _)
    ; K-preserved                   = K-preserved
    ; []-cong-preserved             = []-cong-preserved
    ; Equality-reflection-preserved = _
    ; Quot-preserved                = Quot-preserved
    ; Quot-allowed→tr-𝟘≡𝟘           = Quot-allowed→tr-𝟘≡𝟘
    }
    where
    open Is-Σ-morphism-TC r

opaque

  -- A lemma related to Is-Σ-morphism-TC and with-equality-reflection.

  M-with-equality-reflection :
    Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-morphism-TC trp
      (with-equality-reflection 𝕄₁ TC₁)
      (with-equality-reflection 𝕄₂ TC₂)
      tr tr-Σ
  M-with-equality-reflection r = record
    { unfolding-mode-preserved      = unfolding-mode-preserved
    ; level-support-preserved       = level-support-preserved
    ; Omega-plus-preserved          = Omega-plus-preserved
    ; Unitʷ-η-preserved             = Unitʷ-η-preserved
    ; Unit-preserved                = Unit-preserved
    ; ΠΣ-preserved                  = ΠΣ-preserved
    ; Opacity-preserved             = λ _ ()
    ; K-preserved                   = K-preserved
    ; []-cong-preserved             = []-cong-preserved
    ; Equality-reflection-preserved = _
    ; Quot-preserved                = Quot-preserved
    ; Quot-allowed→tr-𝟘≡𝟘           = Quot-allowed→tr-𝟘≡𝟘
    }
    where
    open Is-Σ-morphism-TC r

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- with-equality-reflection.

  OE-with-equality-reflection :
    (∀ {s} →
     Modality.Trivial 𝕄₂ →
     ¬ Type-configuration.[]-cong-allowed TC₁ s) →
    Is-Σ-order-embedding-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-order-embedding-TC trp
      (with-equality-reflection 𝕄₁ TC₁)
      (with-equality-reflection 𝕄₂ TC₂)
      tr tr-Σ
  OE-with-equality-reflection
    hyp r = record
    { unfolding-mode-reflected      = unfolding-mode-reflected
    ; level-support-reflected       = level-support-reflected
    ; Unitʷ-η-reflected             = Unitʷ-η-reflected
    ; Unit-reflected                = Unit-reflected
    ; ΠΣ-reflected                  = ΠΣ-reflected
    ; Opacity-reflected             = λ ()
    ; K-reflected                   = K-reflected
    ; []-cong-reflected             = []-cong-reflected
    ; Equality-reflection-reflected = _
    ; Quot-reflected                = Quot-reflected
    }
    where
    open Is-Σ-order-embedding-TC r

opaque

  -- A lemma related to Is-Σ-morphism-TC and no-quotients.

  M-no-quotients :
    Is-Σ-morphism-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-morphism-TC trp
      (no-quotients 𝕄₁ TC₁)
      (no-quotients 𝕄₂ TC₂)
      tr tr-Σ
  M-no-quotients r = record
    { unfolding-mode-preserved      = unfolding-mode-preserved
    ; level-support-preserved       = level-support-preserved
    ; Omega-plus-preserved          = Omega-plus-preserved
    ; Unitʷ-η-preserved             = Unitʷ-η-preserved
    ; Unit-preserved                = Unit-preserved
    ; ΠΣ-preserved                  = ΠΣ-preserved
    ; Opacity-preserved             = Opacity-preserved
    ; K-preserved                   = K-preserved
    ; []-cong-preserved             = []-cong-preserved
    ; Equality-reflection-preserved = Equality-reflection-preserved
    ; Quot-preserved                = ⊥-elim ∘→ Lift.lower
    ; Quot-allowed→tr-𝟘≡𝟘           = ⊥-elim ∘→ Lift.lower
    }
    where
    open Is-Σ-morphism-TC r

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and no-quotients.

  OE-no-quotients :
    let module M₁ = Modality 𝕄₁
        module M₂ = Modality 𝕄₂
    in
    (M₂.Trivial → M₁.Trivial) →
    Is-Σ-order-embedding-TC trp TC₁ TC₂ tr tr-Σ →
    Is-Σ-order-embedding-TC trp
      (no-quotients 𝕄₁ TC₁)
      (no-quotients 𝕄₂ TC₂)
      tr tr-Σ
  OE-no-quotients hyp r = record
    { unfolding-mode-reflected      = unfolding-mode-reflected
    ; level-support-reflected       = level-support-reflected
    ; Unitʷ-η-reflected             = Unitʷ-η-reflected
    ; Unit-reflected                = Unit-reflected
    ; ΠΣ-reflected                  = ΠΣ-reflected
    ; Opacity-reflected             = Opacity-reflected
    ; K-reflected                   = K-reflected
    ; []-cong-reflected             = []-cong-reflected
    ; Equality-reflection-reflected = Equality-reflection-reflected
    ; Quot-reflected                = ⊎.map (lift ∘→ Lift.lower) hyp
    }
    where
    open Is-Σ-order-embedding-TC r

------------------------------------------------------------------------
-- Some lemmas related to equal-binder-quantities and concrete
-- translation functions

-- A lemma related to Is-Σ-morphism-TC and erasure→zero-one-many-Σ.

¬-M-equal-binder-quantities-erasure→zero-one-many-Σ :
  (TC : Type-configuration 𝕄₂) →
  ¬ Is-Σ-morphism-TC trp
      (equal-binder-quantities 𝕄₁ (no-type-restrictions 𝕄₁ b₁ b₂))
      (equal-binder-quantities 𝕄₂ TC)
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-M-equal-binder-quantities-erasure→zero-one-many-Σ _ r =
  case ΠΣ-preserved {b = BMΣ 𝕤} {p = ω} (_ , refl) .proj₂ of λ ()
  where
  open Is-Σ-morphism-TC r

-- A lemma related to Is-Σ-morphism-TC and affine→linear-or-affine-Σ.

¬-M-equal-binder-quantities-affine→linear-or-affine-Σ :
  (TC : Type-configuration 𝕄₂) →
  ¬ Is-Σ-morphism-TC trp
      (equal-binder-quantities 𝕄₁ (no-type-restrictions 𝕄₁ b₁ b₂))
      (equal-binder-quantities 𝕄₂ TC)
      affine→linear-or-affine affine→linear-or-affine-Σ
¬-M-equal-binder-quantities-affine→linear-or-affine-Σ
  _ r =
  case ΠΣ-preserved {b = BMΣ 𝕤} {p = 𝟙} (_ , refl) .proj₂ of λ ()
  where
  open Is-Σ-morphism-TC r

------------------------------------------------------------------------
-- Some lemmas related to second-ΠΣ-quantities-𝟘-or-ω and concrete
-- translation functions

-- A lemma related to Is-Σ-morphism-TC and unit→erasure.

M-second-ΠΣ-quantities-𝟘-or-ω-unit→erasure :
  Is-Σ-morphism-TC trp
    TC₁ TC₂ unit→erasure unit→erasure →
  Is-Σ-morphism-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω UnitModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω ErasureModality TC₂)
    unit→erasure unit→erasure
M-second-ΠΣ-quantities-𝟘-or-ω-unit→erasure =
  M-second-ΠΣ-quantities-𝟘-or-ω
    (λ tt≢tt → ⊥-elim (tt≢tt refl))
    ((λ _ → refl) , (λ _ → refl))
    ((λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-order-embedding-TC and unit→erasure.

OE-second-ΠΣ-quantities-𝟘-or-ω-unit→erasure :
  Is-Σ-order-embedding-TC trp
    TC₁ TC₂ unit→erasure unit→erasure →
  Is-Σ-order-embedding-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω UnitModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω ErasureModality TC₂)
    unit→erasure unit→erasure
OE-second-ΠΣ-quantities-𝟘-or-ω-unit→erasure =
  OE-second-ΠΣ-quantities-𝟘-or-ω
    (λ ())
    ((λ _ → refl) , (λ _ → refl))
    ((λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-morphism-TC and erasure→unit.

M-second-ΠΣ-quantities-𝟘-or-ω-erasure→unit :
  Is-Σ-morphism-TC trp
    TC₁ TC₂ erasure→unit erasure→unit →
  Is-Σ-morphism-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω ErasureModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω UnitModality TC₂)
    erasure→unit erasure→unit
M-second-ΠΣ-quantities-𝟘-or-ω-erasure→unit r =
  record
    { unfolding-mode-preserved = unfolding-mode-preserved
    ; level-support-preserved  = level-support-preserved
    ; Omega-plus-preserved     = Omega-plus-preserved
    ; Unitʷ-η-preserved        = Unitʷ-η-preserved
    ; Unit-preserved           = Unit-preserved
    ; ΠΣ-preserved             = λ (b , _) →
        ΠΣ-preserved b , (λ _ → refl) , (λ _ → refl)
    ; Opacity-preserved             = Opacity-preserved
    ; K-preserved                   = K-preserved
    ; []-cong-preserved             = []-cong-preserved
    ; Equality-reflection-preserved = Equality-reflection-preserved
    ; Quot-preserved                = Quot-preserved
    ; Quot-allowed→tr-𝟘≡𝟘           = Quot-allowed→tr-𝟘≡𝟘
  }
  where
  open Is-Σ-morphism-TC r

-- A lemma related to Is-Σ-order-embedding-TC and erasure→unit.

¬-OE-second-ΠΣ-quantities-𝟘-or-ω-erasure→unit :
  let 𝕄₁ = ErasureModality
      𝕄₂ = UnitModality
  in
  (TC₁ : Type-configuration 𝕄₁) →
  ¬ Is-Σ-order-embedding-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ TC₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ (no-type-restrictions 𝕄₂ b₁ b₂))
      erasure→unit erasure→unit
¬-OE-second-ΠΣ-quantities-𝟘-or-ω-erasure→unit _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = 𝟘} {q = ω}
      (_ , (λ _ → refl) , (λ _ → refl))
  of
    λ (_ , _ , eq) →
  case eq (λ ()) of λ ()
  where
  open Is-Σ-order-embedding-TC r

-- A lemma related to Is-Σ-morphism-TC and erasure→zero-one-many.

M-second-ΠΣ-quantities-𝟘-or-ω-erasure→zero-one-many :
  Is-Σ-morphism-TC trp TC₁ TC₂
    erasure→zero-one-many erasure→zero-one-many →
  Is-Σ-morphism-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω ErasureModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω (zero-one-many-modality 𝟙≤𝟘) TC₂)
    erasure→zero-one-many erasure→zero-one-many
M-second-ΠΣ-quantities-𝟘-or-ω-erasure→zero-one-many =
  M-second-ΠΣ-quantities-𝟘-or-ω
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-order-embedding-TC and
-- erasure→zero-one-many.

OE-second-ΠΣ-quantities-𝟘-or-ω-erasure→zero-one-many :
  Is-Σ-order-embedding-TC trp TC₁ TC₂
    erasure→zero-one-many erasure→zero-one-many →
  Is-Σ-order-embedding-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω ErasureModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω (zero-one-many-modality 𝟙≤𝟘) TC₂)
    erasure→zero-one-many erasure→zero-one-many
OE-second-ΠΣ-quantities-𝟘-or-ω-erasure→zero-one-many =
  OE-second-ΠΣ-quantities-𝟘-or-ω
    (λ where
       {p = 𝟘} _  → refl
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-morphism-TC and erasure→zero-one-many-Σ.

¬-M-second-ΠΣ-quantities-𝟘-or-ω-erasure→zero-one-many-Σ :
  let 𝕄₁ = ErasureModality
      𝕄₂ = zero-one-many-modality 𝟙≤𝟘
  in
  (TC₂ : Type-configuration 𝕄₂) →
  ¬ Is-Σ-morphism-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ (no-type-restrictions 𝕄₁ b₁ b₂))
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ TC₂)
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-M-second-ΠΣ-quantities-𝟘-or-ω-erasure→zero-one-many-Σ
  _ r =
  case
    ΠΣ-preserved {b = BMΣ 𝕤} {p = ω} {q = ω}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
      .proj₂ .proj₂ (λ ())
  of λ ()
  where
  open Is-Σ-morphism-TC r

-- A lemma related to Is-Σ-order-embedding-TC and
-- erasure→zero-one-many-Σ.

¬-OE-second-ΠΣ-quantities-𝟘-or-ω-erasure→zero-one-many-Σ :
  let 𝕄₁ = ErasureModality
      𝕄₂ = zero-one-many-modality 𝟙≤𝟘
  in
  (TC₁ : Type-configuration 𝕄₁) →
  ¬ Is-Σ-order-embedding-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ TC₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ (no-type-restrictions 𝕄₂ b₁ b₂))
      erasure→zero-one-many erasure→zero-one-many-Σ
¬-OE-second-ΠΣ-quantities-𝟘-or-ω-erasure→zero-one-many-Σ _ r =
  case
    ΠΣ-reflected {b = BMΣ 𝕤} {p = ω} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Is-Σ-order-embedding-TC r

-- A lemma related to Is-Σ-morphism-TC and zero-one-many→erasure.

¬-M-second-ΠΣ-quantities-𝟘-or-ω-zero-one-many→erasure :
  let 𝕄₁ = zero-one-many-modality 𝟙≤𝟘
      𝕄₂ = ErasureModality
  in
  (TC₂ : Type-configuration 𝕄₂) →
  ¬ Is-Σ-morphism-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ (no-type-restrictions 𝕄₁ b₁ b₂))
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ TC₂)
      zero-one-many→erasure zero-one-many→erasure
¬-M-second-ΠΣ-quantities-𝟘-or-ω-zero-one-many→erasure _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = 𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Is-Σ-morphism-TC r

-- A lemma related to Is-Σ-order-embedding-TC and
-- zero-one-many→erasure.

¬-OE-second-ΠΣ-quantities-𝟘-or-ω-zero-one-many→erasure :
  let 𝕄₁ = zero-one-many-modality 𝟙≤𝟘
      𝕄₂ = ErasureModality
  in
  (TC₁ : Type-configuration 𝕄₁) →
  ¬ Is-Σ-order-embedding-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ TC₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ (no-type-restrictions 𝕄₂ b₁ b₂))
      zero-one-many→erasure zero-one-many→erasure
¬-OE-second-ΠΣ-quantities-𝟘-or-ω-zero-one-many→erasure _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Is-Σ-order-embedding-TC r

-- A lemma related to Is-Σ-morphism-TC and linearity→linear-or-affine.

M-second-ΠΣ-quantities-𝟘-or-ω-linearity→linear-or-affine :
  Is-Σ-morphism-TC trp TC₁ TC₂
    linearity→linear-or-affine linearity→linear-or-affine →
  Is-Σ-morphism-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω linearityModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine TC₂)
    linearity→linear-or-affine linearity→linear-or-affine
M-second-ΠΣ-quantities-𝟘-or-ω-linearity→linear-or-affine =
  M-second-ΠΣ-quantities-𝟘-or-ω
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-order-embedding-TC and
-- linearity→linear-or-affine.

OE-second-ΠΣ-quantities-𝟘-or-ω-linearity→linear-or-affine :
  Is-Σ-order-embedding-TC trp TC₁ TC₂
    linearity→linear-or-affine linearity→linear-or-affine →
  Is-Σ-order-embedding-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω linearityModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine TC₂)
    linearity→linear-or-affine linearity→linear-or-affine
OE-second-ΠΣ-quantities-𝟘-or-ω-linearity→linear-or-affine =
  OE-second-ΠΣ-quantities-𝟘-or-ω
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-morphism-TC and linear-or-affine→linearity.

¬-M-second-ΠΣ-quantities-𝟘-or-ω-linear-or-affine→linearity :
  let 𝕄₁ = linear-or-affine
      𝕄₂ = linearityModality
  in
  (TC₂ : Type-configuration 𝕄₂) →
  ¬ Is-Σ-morphism-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ (no-type-restrictions 𝕄₁ b₁ b₂))
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ TC₂)
      linear-or-affine→linearity linear-or-affine→linearity
¬-M-second-ΠΣ-quantities-𝟘-or-ω-linear-or-affine→linearity
  _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = ≤𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Is-Σ-morphism-TC r

-- A lemma related to Is-Σ-order-embedding-TC and
-- linear-or-affine→linearity.

¬-OE-second-ΠΣ-quantities-𝟘-or-ω-linear-or-affine→linearity :
  let 𝕄₁ = linear-or-affine
      𝕄₂ = linearityModality
  in
  (TC₁ : Type-configuration 𝕄₁) →
  ¬ Is-Σ-order-embedding-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ TC₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ (no-type-restrictions 𝕄₂ b₁ b₂))
      linear-or-affine→linearity linear-or-affine→linearity
¬-OE-second-ΠΣ-quantities-𝟘-or-ω-linear-or-affine→linearity _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ≤ω} {q = ≤𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Is-Σ-order-embedding-TC r

-- A lemma related to Is-Σ-morphism-TC and affine→linear-or-affine.

M-second-ΠΣ-quantities-𝟘-or-ω-affine→linear-or-affine :
  Is-Σ-morphism-TC trp TC₁ TC₂
    affine→linear-or-affine affine→linear-or-affine →
  Is-Σ-morphism-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω affineModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine TC₂)
    affine→linear-or-affine affine→linear-or-affine
M-second-ΠΣ-quantities-𝟘-or-ω-affine→linear-or-affine =
  M-second-ΠΣ-quantities-𝟘-or-ω
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-order-embedding-TC and
-- affine→linear-or-affine.

OE-second-ΠΣ-quantities-𝟘-or-ω-affine→linear-or-affine :
  Is-Σ-order-embedding-TC trp TC₁ TC₂
    affine→linear-or-affine affine→linear-or-affine →
  Is-Σ-order-embedding-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω affineModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine TC₂)
    affine→linear-or-affine affine→linear-or-affine
OE-second-ΠΣ-quantities-𝟘-or-ω-affine→linear-or-affine =
  OE-second-ΠΣ-quantities-𝟘-or-ω
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-morphism-TC and affine→linear-or-affine-Σ.

M-second-ΠΣ-quantities-𝟘-or-ω-affine→linear-or-affine-Σ :
  Is-Σ-morphism-TC trp TC₁ TC₂
    affine→linear-or-affine affine→linear-or-affine-Σ →
  Is-Σ-morphism-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω affineModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine TC₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
M-second-ΠΣ-quantities-𝟘-or-ω-affine→linear-or-affine-Σ =
  M-second-ΠΣ-quantities-𝟘-or-ω
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-order-embedding-TC and
-- affine→linear-or-affine-Σ.

OE-second-ΠΣ-quantities-𝟘-or-ω-affine→linear-or-affine-Σ :
  Is-Σ-order-embedding-TC trp TC₁ TC₂
    affine→linear-or-affine affine→linear-or-affine-Σ →
  Is-Σ-order-embedding-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω affineModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine TC₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
OE-second-ΠΣ-quantities-𝟘-or-ω-affine→linear-or-affine-Σ =
  OE-second-ΠΣ-quantities-𝟘-or-ω
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-morphism-TC and linear-or-affine→affine.

M-second-ΠΣ-quantities-𝟘-or-ω-linear-or-affine→affine :
  Is-Σ-morphism-TC trp TC₁ TC₂
    linear-or-affine→affine linear-or-affine→affine →
  Is-Σ-morphism-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω affineModality TC₂)
    linear-or-affine→affine linear-or-affine→affine
M-second-ΠΣ-quantities-𝟘-or-ω-linear-or-affine→affine =
  M-second-ΠΣ-quantities-𝟘-or-ω
    (λ _ → refl)
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-order-embedding-TC and
-- linear-or-affine→affine.

OE-second-ΠΣ-quantities-𝟘-or-ω-linear-or-affine→affine :
  Is-Σ-order-embedding-TC trp TC₁ TC₂
    linear-or-affine→affine linear-or-affine→affine →
  Is-Σ-order-embedding-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω linear-or-affine TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω affineModality TC₂)
    linear-or-affine→affine linear-or-affine→affine
OE-second-ΠΣ-quantities-𝟘-or-ω-linear-or-affine→affine =
  OE-second-ΠΣ-quantities-𝟘-or-ω
    (λ where
       {p = 𝟘}  _  → refl
       {p = 𝟙}  ()
       {p = ≤𝟙} ()
       {p = ≤ω} ())
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘}  → (λ ()) , (λ ())
       {p = 𝟙}  → (λ ()) , (λ ())
       {p = ≤𝟙} → (λ ()) , (λ ())
       {p = ≤ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-morphism-TC and affine→linearity.

¬-M-second-ΠΣ-quantities-𝟘-or-ω-affine→linearity :
  let 𝕄₁ = affineModality
      𝕄₂ = linearityModality
  in
  (TC₂ : Type-configuration 𝕄₂) →
  ¬ Is-Σ-morphism-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ (no-type-restrictions 𝕄₁ b₁ b₂))
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ TC₂)
      affine→linearity affine→linearity
¬-M-second-ΠΣ-quantities-𝟘-or-ω-affine→linearity _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = 𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Is-Σ-morphism-TC r

-- A lemma related to Is-Σ-order-embedding-TC and affine→linearity.

¬-OE-second-ΠΣ-quantities-𝟘-or-ω-affine→linearity :
  let 𝕄₁ = affineModality
      𝕄₂ = linearityModality
  in
  (TC₁ : Type-configuration 𝕄₁) →
  ¬ Is-Σ-order-embedding-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ TC₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ (no-type-restrictions 𝕄₂ b₁ b₂))
      affine→linearity affine→linearity
¬-OE-second-ΠΣ-quantities-𝟘-or-ω-affine→linearity _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Is-Σ-order-embedding-TC r

-- A lemma related to Is-Σ-morphism-TC and affine→linearity-Σ.

¬-M-second-ΠΣ-quantities-𝟘-or-ω-affine→linearity-Σ :
  let 𝕄₁ = affineModality
      𝕄₂ = linearityModality
  in
  (TC₂ : Type-configuration 𝕄₂) →
  ¬ Is-Σ-morphism-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ (no-type-restrictions 𝕄₁ b₁ b₂))
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ TC₂)
      affine→linearity affine→linearity-Σ
¬-M-second-ΠΣ-quantities-𝟘-or-ω-affine→linearity-Σ _ r =
  case
    ΠΣ-preserved {b = BMΠ} {p = 𝟙} {q = 𝟘}
      (_ , (λ ()) , (λ _ → refl))
      .proj₂ .proj₁ refl
  of λ ()
  where
  open Is-Σ-morphism-TC r

-- A lemma related to Is-Σ-order-embedding-TC and affine→linearity-Σ.

¬-OE-second-ΠΣ-quantities-𝟘-or-ω-affine→linearity-Σ :
  let 𝕄₁ = affineModality
      𝕄₂ = linearityModality
  in
  (TC₁ : Type-configuration 𝕄₁) →
  ¬ Is-Σ-order-embedding-TC trp
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₁ TC₁)
      (second-ΠΣ-quantities-𝟘-or-ω 𝕄₂ (no-type-restrictions 𝕄₂ b₁ b₂))
      affine→linearity affine→linearity-Σ
¬-OE-second-ΠΣ-quantities-𝟘-or-ω-affine→linearity-Σ _ r =
  case
    ΠΣ-reflected {b = BMΠ} {p = ω} {q = 𝟙}
      (_ , (λ _ → refl) , ⊥-elim ∘→ (_$ refl))
  of
    λ (_ , eq , _) →
  case eq refl of λ ()
  where
  open Is-Σ-order-embedding-TC r

-- A lemma related to Is-Σ-morphism-TC and linearity→affine.

M-second-ΠΣ-quantities-𝟘-or-ω-linearity→affine :
  Is-Σ-morphism-TC trp TC₁ TC₂
    linearity→affine linearity→affine →
  Is-Σ-morphism-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω linearityModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω affineModality TC₂)
    linearity→affine linearity→affine
M-second-ΠΣ-quantities-𝟘-or-ω-linearity→affine =
  M-second-ΠΣ-quantities-𝟘-or-ω
    (λ _ → refl)
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

-- A lemma related to Is-Σ-order-embedding-TC and linearity→affine.

OE-second-ΠΣ-quantities-𝟘-or-ω-linearity→affine :
  Is-Σ-order-embedding-TC trp TC₁ TC₂
    linearity→affine linearity→affine →
  Is-Σ-order-embedding-TC trp
    (second-ΠΣ-quantities-𝟘-or-ω linearityModality TC₁)
    (second-ΠΣ-quantities-𝟘-or-ω affineModality TC₂)
    linearity→affine linearity→affine
OE-second-ΠΣ-quantities-𝟘-or-ω-linearity→affine =
  OE-second-ΠΣ-quantities-𝟘-or-ω
    (λ where
       {p = 𝟘} _  → refl
       {p = 𝟙} ()
       {p = ω} ())
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))
    (λ where
       {p = 𝟘} → (λ ()) , (λ ())
       {p = 𝟙} → (λ ()) , (λ ())
       {p = ω} → (λ _ → refl) , (λ _ → refl))

------------------------------------------------------------------------
-- Some lemmas related to strong-types-restricted and concrete
-- translation functions

opaque

  -- A lemma related to Is-Σ-morphism-TC and unit→erasure.

  M-strong-types-restricted-unit→erasure :
    Is-Σ-morphism-TC trp
      TC₁ TC₂ unit→erasure unit→erasure →
    Is-Σ-morphism-TC trp
      (strong-types-restricted UnitModality TC₁)
      (strong-types-restricted ErasureModality TC₂)
      unit→erasure unit→erasure
  M-strong-types-restricted-unit→erasure =
    M-strong-types-restricted refl

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and unit→erasure.

  OE-strong-types-restricted-unit→erasure :
    Is-Σ-order-embedding-TC trp
      TC₁ TC₂ unit→erasure unit→erasure →
    Is-Σ-order-embedding-TC trp
      (strong-types-restricted UnitModality TC₁)
      (strong-types-restricted ErasureModality TC₂)
      unit→erasure unit→erasure
  OE-strong-types-restricted-unit→erasure =
    OE-strong-types-restricted
      (λ _ → refl)
      (λ ())

opaque

  -- A lemma related to Is-Σ-morphism-TC and erasure→unit.

  M-strong-types-restricted-erasure→unit :
    Is-Σ-morphism-TC trp
      TC₁ TC₂ erasure→unit erasure→unit →
    Is-Σ-morphism-TC trp
      (strong-types-restricted ErasureModality TC₁)
      (strong-types-restricted UnitModality TC₂)
      erasure→unit erasure→unit
  M-strong-types-restricted-erasure→unit =
    M-strong-types-restricted refl

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and erasure→unit.

  ¬-OE-strong-types-restricted-erasure→unit :
    let 𝕄₁ = ErasureModality
        𝕄₂ = UnitModality
    in
    (TC₁ : Type-configuration 𝕄₁) →
    ¬ Is-Σ-order-embedding-TC trp
        (strong-types-restricted 𝕄₁ TC₁)
        (strong-types-restricted 𝕄₂ (no-type-restrictions 𝕄₂ b₁ b₂))
        erasure→unit erasure→unit
  ¬-OE-strong-types-restricted-erasure→unit _ r =
    case
      ΠΣ-reflected {b = BMΣ 𝕤} {p = 𝟘} {q = 𝟘} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Is-Σ-order-embedding-TC r

opaque

  -- A lemma related to Is-Σ-morphism-TC and erasure→zero-one-many.

  ¬-M-strong-types-restricted-erasure→zero-one-many :
    let 𝕄₁ = ErasureModality
        𝕄₂ = zero-one-many-modality 𝟙≤𝟘
    in
    (TC₂ : Type-configuration 𝕄₂) →
    ¬ Is-Σ-morphism-TC trp
        (strong-types-restricted 𝕄₁ (no-type-restrictions 𝕄₁ b₁ b₂))
        (strong-types-restricted 𝕄₂ TC₂)
        erasure→zero-one-many erasure→zero-one-many
  ¬-M-strong-types-restricted-erasure→zero-one-many _ r =
    case
      ΠΣ-preserved {b = BMΣ 𝕤} {p = ω} {q = 𝟘} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Is-Σ-morphism-TC r

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- erasure→zero-one-many.

  OE-strong-types-restricted-erasure→zero-one-many :
    Is-Σ-order-embedding-TC trp TC₁ TC₂
      erasure→zero-one-many erasure→zero-one-many →
    Is-Σ-order-embedding-TC trp
      (strong-types-restricted ErasureModality TC₁)
      (strong-types-restricted (zero-one-many-modality 𝟙≤𝟘) TC₂)
      erasure→zero-one-many erasure→zero-one-many
  OE-strong-types-restricted-erasure→zero-one-many =
    OE-strong-types-restricted
      (λ where
         {p = 𝟘} ()
         {p = ω} ())
      (λ ())

opaque

  -- A lemma related to Is-Σ-morphism-TC and erasure→zero-one-many-Σ.

  M-strong-types-restricted-erasure→zero-one-many-Σ :
    Is-Σ-morphism-TC trp TC₁ TC₂
      erasure→zero-one-many erasure→zero-one-many-Σ →
    Is-Σ-morphism-TC trp
      (strong-types-restricted ErasureModality TC₁)
      (strong-types-restricted (zero-one-many-modality 𝟙≤𝟘) TC₂)
      erasure→zero-one-many erasure→zero-one-many-Σ
  M-strong-types-restricted-erasure→zero-one-many-Σ =
    M-strong-types-restricted refl

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- erasure→zero-one-many-Σ.

  OE-strong-types-restricted-erasure→zero-one-many-Σ :
    Is-Σ-order-embedding-TC trp TC₁ TC₂
      erasure→zero-one-many erasure→zero-one-many-Σ →
    Is-Σ-order-embedding-TC trp
      (strong-types-restricted ErasureModality TC₁)
      (strong-types-restricted (zero-one-many-modality 𝟙≤𝟘) TC₂)
      erasure→zero-one-many erasure→zero-one-many-Σ
  OE-strong-types-restricted-erasure→zero-one-many-Σ =
    OE-strong-types-restricted
      (λ where
         {p = ω} refl → refl
         {p = 𝟘} ())
      (λ ())

opaque

  -- A lemma related to Is-Σ-morphism-TC and zero-one-many→erasure.

  M-strong-types-restricted-zero-one-many→erasure :
    Is-Σ-morphism-TC trp
      TC₁ TC₂ zero-one-many→erasure zero-one-many→erasure →
    Is-Σ-morphism-TC trp
      (strong-types-restricted (zero-one-many-modality 𝟙≤𝟘) TC₁)
      (strong-types-restricted ErasureModality TC₂)
      zero-one-many→erasure zero-one-many→erasure
  M-strong-types-restricted-zero-one-many→erasure =
    M-strong-types-restricted refl

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- zero-one-many→erasure.

  ¬-OE-strong-types-restricted-zero-one-many→erasure :
    let 𝕄₁ = zero-one-many-modality 𝟙≤𝟘
        𝕄₂ = ErasureModality
    in
    (TC₁ : Type-configuration 𝕄₁) →
    ¬ Is-Σ-order-embedding-TC trp
        (strong-types-restricted 𝕄₁ TC₁)
        (strong-types-restricted 𝕄₂ (no-type-restrictions 𝕄₂ b₁ b₂))
        zero-one-many→erasure zero-one-many→erasure
  ¬-OE-strong-types-restricted-zero-one-many→erasure _ r =
    case
      ΠΣ-reflected {b = BMΣ 𝕤} {p = ω} {q = ω} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Is-Σ-order-embedding-TC r

opaque

  -- A lemma related to Is-Σ-morphism-TC and
  -- linearity→linear-or-affine.

  M-strong-types-restricted-linearity→linear-or-affine :
    Is-Σ-morphism-TC trp TC₁ TC₂
      linearity→linear-or-affine linearity→linear-or-affine →
    Is-Σ-morphism-TC trp
      (strong-types-restricted linearityModality TC₁)
      (strong-types-restricted linear-or-affine TC₂)
      linearity→linear-or-affine linearity→linear-or-affine
  M-strong-types-restricted-linearity→linear-or-affine =
    M-strong-types-restricted refl

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- linearity→linear-or-affine.

  OE-strong-types-restricted-linearity→linear-or-affine :
    Is-Σ-order-embedding-TC trp TC₁ TC₂
      linearity→linear-or-affine linearity→linear-or-affine →
    Is-Σ-order-embedding-TC trp
      (strong-types-restricted linearityModality TC₁)
      (strong-types-restricted linear-or-affine TC₂)
      linearity→linear-or-affine linearity→linear-or-affine
  OE-strong-types-restricted-linearity→linear-or-affine =
    OE-strong-types-restricted
      (λ where
         {p = 𝟙} refl → refl
         {p = 𝟘} ()
         {p = ω} ())
      (λ ())

opaque

  -- A lemma related to Is-Σ-morphism-TC and
  -- linear-or-affine→linearity.

  M-strong-types-restricted-linear-or-affine→linearity :
    Is-Σ-morphism-TC trp TC₁ TC₂
      linear-or-affine→linearity linear-or-affine→linearity →
    Is-Σ-morphism-TC trp
      (strong-types-restricted linear-or-affine TC₁)
      (strong-types-restricted linearityModality TC₂)
      linear-or-affine→linearity linear-or-affine→linearity
  M-strong-types-restricted-linear-or-affine→linearity =
    M-strong-types-restricted refl

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- linear-or-affine→linearity.

  OE-strong-types-restricted-linear-or-affine→linearity :
    Is-Σ-order-embedding-TC trp TC₁ TC₂
      linear-or-affine→linearity linear-or-affine→linearity →
    Is-Σ-order-embedding-TC trp
      (strong-types-restricted linear-or-affine TC₁)
      (strong-types-restricted linearityModality TC₂)
      linear-or-affine→linearity linear-or-affine→linearity
  OE-strong-types-restricted-linear-or-affine→linearity =
    OE-strong-types-restricted
      (λ where
         {p = 𝟙}  refl → refl
         {p = 𝟘}  ()
         {p = ≤𝟙} ()
         {p = ≤ω} ())
      (λ ())

opaque

  -- A lemma related to Is-Σ-morphism-TC and affine→linear-or-affine.

  ¬-M-strong-types-restricted-affine→linear-or-affine :
    let 𝕄₁ = affineModality
        𝕄₂ = linear-or-affine
    in
    (TC₂ : Type-configuration 𝕄₂) →
    ¬ Is-Σ-morphism-TC trp
        (strong-types-restricted 𝕄₁ (no-type-restrictions 𝕄₁ b₁ b₂))
        (strong-types-restricted 𝕄₂ TC₂)
        affine→linear-or-affine affine→linear-or-affine
  ¬-M-strong-types-restricted-affine→linear-or-affine _ r =
    case
      ΠΣ-preserved {b = BMΣ 𝕤} {p = 𝟙} {q = 𝟙} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Is-Σ-morphism-TC r

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- affine→linear-or-affine.

  OE-strong-types-restricted-affine→linear-or-affine :
    Is-Σ-order-embedding-TC trp TC₁ TC₂
      affine→linear-or-affine affine→linear-or-affine →
    Is-Σ-order-embedding-TC trp
      (strong-types-restricted affineModality TC₁)
      (strong-types-restricted linear-or-affine TC₂)
      affine→linear-or-affine affine→linear-or-affine
  OE-strong-types-restricted-affine→linear-or-affine =
    OE-strong-types-restricted
      (λ where
         {p = 𝟘} ()
         {p = 𝟙} ()
         {p = ω} ())
      (λ ())

opaque

  -- A lemma related to Is-Σ-morphism-TC and
  -- affine→linear-or-affine-Σ.

  M-strong-types-restricted-affine→linear-or-affine-Σ :
    Is-Σ-morphism-TC trp TC₁ TC₂
      affine→linear-or-affine affine→linear-or-affine-Σ →
    Is-Σ-morphism-TC trp
      (strong-types-restricted affineModality TC₁)
      (strong-types-restricted linear-or-affine TC₂)
      affine→linear-or-affine affine→linear-or-affine-Σ
  M-strong-types-restricted-affine→linear-or-affine-Σ =
    M-strong-types-restricted refl

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- affine→linear-or-affine-Σ.

  OE-strong-types-restricted-affine→linear-or-affine-Σ :
    Is-Σ-order-embedding-TC trp TC₁ TC₂
      affine→linear-or-affine affine→linear-or-affine-Σ →
    Is-Σ-order-embedding-TC trp
      (strong-types-restricted affineModality TC₁)
      (strong-types-restricted linear-or-affine TC₂)
      affine→linear-or-affine affine→linear-or-affine-Σ
  OE-strong-types-restricted-affine→linear-or-affine-Σ =
    OE-strong-types-restricted
      (λ where
         {p = 𝟙} refl → refl
         {p = 𝟘} ()
         {p = ω} ())
      (λ ())

opaque

  -- A lemma related to Is-Σ-morphism-TC and linear-or-affine→affine.

  M-strong-types-restricted-linear-or-affine→affine :
    Is-Σ-morphism-TC trp TC₁ TC₂
      linear-or-affine→affine linear-or-affine→affine →
    Is-Σ-morphism-TC trp
      (strong-types-restricted linear-or-affine TC₁)
      (strong-types-restricted affineModality TC₂)
      linear-or-affine→affine linear-or-affine→affine
  M-strong-types-restricted-linear-or-affine→affine =
    M-strong-types-restricted refl

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- linear-or-affine→affine.

  ¬-OE-strong-types-restricted-linear-or-affine→affine :
    let 𝕄₁ = linear-or-affine
        𝕄₂ = affineModality
    in
    (TC₁ : Type-configuration 𝕄₁) →
    ¬ Is-Σ-order-embedding-TC trp
        (strong-types-restricted 𝕄₁ TC₁)
        (strong-types-restricted 𝕄₂ (no-type-restrictions 𝕄₂ b₁ b₂))
        linear-or-affine→affine linear-or-affine→affine
  ¬-OE-strong-types-restricted-linear-or-affine→affine _ r =
    case
      ΠΣ-reflected {b = BMΣ 𝕤} {p = ≤𝟙} {q = ≤𝟙} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Is-Σ-order-embedding-TC r

opaque

  -- A lemma related to Is-Σ-morphism-TC and affine→linearity.

  ¬-M-strong-types-restricted-affine→linearity :
    let 𝕄₁ = affineModality
        𝕄₂ = linearityModality
    in
    (TC₂ : Type-configuration 𝕄₂) →
    ¬ Is-Σ-morphism-TC trp
        (strong-types-restricted 𝕄₁ (no-type-restrictions 𝕄₁ b₁ b₂))
        (strong-types-restricted 𝕄₂ TC₂)
        affine→linearity affine→linearity
  ¬-M-strong-types-restricted-affine→linearity _ r =
    case
      ΠΣ-preserved {b = BMΣ 𝕤} {p = 𝟙} {q = 𝟙} (_ , (λ _ → refl))
        .proj₂ refl
    of λ ()
    where
    open Is-Σ-morphism-TC r

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and affine→linearity.

  OE-strong-types-restricted-affine→linearity :
    Is-Σ-order-embedding-TC trp TC₁ TC₂
      affine→linearity affine→linearity →
    Is-Σ-order-embedding-TC trp
      (strong-types-restricted affineModality TC₁)
      (strong-types-restricted linearityModality TC₂)
      affine→linearity affine→linearity
  OE-strong-types-restricted-affine→linearity =
    OE-strong-types-restricted
      (λ where
         {p = 𝟘} ()
         {p = 𝟙} ()
         {p = ω} ())
      (λ ())

opaque

  -- A lemma related to Is-Σ-morphism-TC and affine→linearity-Σ.

  M-strong-types-restricted-affine→linearity-Σ :
    Is-Σ-morphism-TC trp TC₁ TC₂
      affine→linearity affine→linearity-Σ →
    Is-Σ-morphism-TC trp
      (strong-types-restricted affineModality TC₁)
      (strong-types-restricted linearityModality TC₂)
      affine→linearity affine→linearity-Σ
  M-strong-types-restricted-affine→linearity-Σ =
    M-strong-types-restricted refl

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and
  -- affine→linearity-Σ.

  OE-strong-types-restricted-affine→linearity-Σ :
    Is-Σ-order-embedding-TC trp TC₁ TC₂
      affine→linearity affine→linearity-Σ →
    Is-Σ-order-embedding-TC trp
      (strong-types-restricted affineModality TC₁)
      (strong-types-restricted linearityModality TC₂)
      affine→linearity affine→linearity-Σ
  OE-strong-types-restricted-affine→linearity-Σ =
    OE-strong-types-restricted
      (λ where
         {p = 𝟙} refl → refl
         {p = 𝟘} ()
         {p = ω} ())
      (λ ())

opaque

  -- A lemma related to Is-Σ-morphism-TC and linearity→affine.

  M-strong-types-restricted-linearity→affine :
    Is-Σ-morphism-TC trp TC₁ TC₂
      linearity→affine linearity→affine →
    Is-Σ-morphism-TC trp
      (strong-types-restricted linearityModality TC₁)
      (strong-types-restricted affineModality TC₂)
      linearity→affine linearity→affine
  M-strong-types-restricted-linearity→affine =
    M-strong-types-restricted refl

opaque

  -- A lemma related to Is-Σ-order-embedding-TC and linearity→affine.

  OE-strong-types-restricted-linearity→affine :
    Is-Σ-order-embedding-TC trp TC₁ TC₂
      linearity→affine linearity→affine →
    Is-Σ-order-embedding-TC trp
      (strong-types-restricted linearityModality TC₁)
      (strong-types-restricted affineModality TC₂)
      linearity→affine linearity→affine
  OE-strong-types-restricted-linearity→affine =
    OE-strong-types-restricted
      (λ where
         {p = 𝟙} refl → refl
         {p = 𝟘} ()
         {p = ω} ())
      (λ ())
