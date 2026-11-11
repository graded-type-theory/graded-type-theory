------------------------------------------------------------------------
-- Modality morphisms preserve some things related to usage
------------------------------------------------------------------------

open import Configuration-types
open import Graded.Modality
open import Graded.Modality.Morphism as M
  using (Is-morphism; Is-order-embedding;
         Is-Σ-morphism; Is-Σ-order-embedding;
         Is-no-nr-glb-preserving-morphism)
  hiding (module Is-morphism; module Is-order-embedding)
open import Graded.Mode.Instances.Zero-one.Variant
open import Graded.Mode.Instances.Zero-one
open import Tools.Bool

module Graded.Usage.QuantityTranslation
  {a₁ a₂} {M₁ : Set a₁} {M₂ : Set a₂}
  {𝕄₁ : Modality M₁} {𝕄₂ : Modality M₂}
  {v₁ : Mode-variant 𝕄₁} {v₂ : Mode-variant 𝕄₂}
  (C₁ : Configuration (Zero-one-isMode v₁))
  (C₂ : Configuration (Zero-one-isMode v₂))
  (transparent : Bool)
  (tr tr-Σ : M₁ → M₂)
  where

open import Configuration-types.Erased-matches
import Configuration-types.Instance

open import Definition.Untyped
open import Definition.Untyped.No-box-cong-Quot M₁
open import Definition.Untyped.QuantityTranslation transparent tr tr-Σ

open import Graded.Context
import Graded.Context.Properties
open import Graded.Context.QuantityTranslation 𝕄₁ 𝕄₂ tr
  as CQ using (tr-Conₘ)
open import Graded.Modality.Morphism.Configuration
open import Graded.Modality.Omega-instances
import Graded.Modality.Properties
open import Graded.Usage
import Graded.Usage.Properties
import Graded.Usage.Properties.Zero-one
import Graded.Usage.Restrictions.Satisfied
import Graded.Modality.Morphism.Backward-instances
import Graded.Modality.Morphism.Forward-instances

open import Graded.Mode.Instances.Zero-one.QuantityTranslation.Primitive
  as MQP hiding (module Is-morphism)
open import
  Graded.Mode.Instances.Zero-one.QuantityTranslation
    𝕄₁ 𝕄₂ v₁ v₂ transparent tr tr-Σ
  as MQ hiding (module Is-morphism; module Is-order-embedding)

open Graded.Modality.Properties 𝕄₂
open Graded.Usage.Properties C₂
open Graded.Usage.Properties.Zero-one v₂ C₂
open Graded.Usage.Restrictions.Satisfied C₂

private
  module C₁   = Graded.Context 𝕄₁
  module C₂   = Graded.Context 𝕄₂
  module CP₁  = Graded.Context.Properties 𝕄₁
  module CP₂  = Graded.Context.Properties 𝕄₂
  module MP₁  = Graded.Modality.Properties 𝕄₁
  module U₁   = Graded.Usage C₁
  module U₂   = Graded.Usage C₂
  module UP₁  = Graded.Usage.Properties C₁
  module UP′₁ = Graded.Usage.Properties.Zero-one v₁ C₁
  module RS₁  = Graded.Usage.Restrictions.Satisfied C₁
  module RS₂  = Graded.Usage.Restrictions.Satisfied C₂
  module Mo₁  = Graded.Mode.Instances.Zero-one v₁
  module Mo₂  = Graded.Mode.Instances.Zero-one v₂
  module M₁   = Modality 𝕄₁
  module M₂   = Modality 𝕄₂
  module Co₁  = Configuration C₁
  module Co₂  = Configuration C₂

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (inj₁; inj₂)

private
  module R₁      = Tools.Reasoning.PartialOrder MP₁.≤-poset
  module R₂      = Tools.Reasoning.PartialOrder ≤-poset
  module CR₁ {n} = Tools.Reasoning.PartialOrder (CP₁.≤ᶜ-poset {n = n})
  module CR₂ {n} = Tools.Reasoning.PartialOrder (CP₂.≤ᶜ-poset {n = n})

private variable
  trp        : Bool
  n          : Nat
  x          : Fin _
  p q        : M₁
  p′         : M₂
  ∇          : DCon _ _
  γ γ′ δ     : Conₘ _ _
  m m₁ m₂ m′ : Mode _
  t          : Term[ _ ] _ _
  k          : Term-kind
  ok₂        : T _

------------------------------------------------------------------------
-- If certain properties hold, then they hold also after translation
-- by morphisms that satisfy certain properties

module Is-morphism
  (tr-m   : Is-morphism 𝕄₁ 𝕄₂ tr)
  (tr-Σ-m : Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ)
  (mr     : Are-mode-respecting-morphisms v₁ v₂ tr tr-Σ)
  (mc     : Is-Σ-morphism-C trp C₁ C₂ tr tr-Σ)
  where

  open Is-Σ-morphism-C mc
  open Are-mode-respecting-morphisms mr
  open CQ.Is-morphism tr-m
  open M.Is-morphism tr-m
  open M.Is-Σ-morphism tr-Σ-m
  open MQ.Is-morphism tr-m tr-Σ-m mr
  open MQP.Is-morphism v₁ v₂ tr-m tr-Σ-m

  open CP₂

  -- Preservation of _◂_∈_.

  tr-◂∈ : x U₁.◂ p ∈ γ → x U₂.◂ tr p ∈ tr-Conₘ γ
  tr-◂∈ here      = here
  tr-◂∈ (there x) = there (tr-◂∈ x)

  opaque

    -- tr is bounded by tr-BinderMode

    tr-≤-tr-BinderMode : ∀ {b} → tr p M₂.≤ tr-BinderMode b p
    tr-≤-tr-BinderMode {b = BMΠ} = ≤-refl
    tr-≤-tr-BinderMode {b = BMΣ s} = tr-≤-tr-Σ

  mutual

    -- Preservation of _▸[_]_.

    tr-▸ : γ U₁.▸[ m ] t → tr-Conₘ γ U₂.▸[ tr-Mode m ] tr-Term t
    tr-▸ defn =
      sub defn tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ Levelₘ =
      sub Levelₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ zeroᵘₘ =
      sub zeroᵘₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (sucᵘₘ ▸t) =
      sucᵘₘ (tr-▸ ▸t)
    tr-▸ (supᵘₘ ▸t ▸u) =
      sub (supᵘₘ (tr-▸ ▸t) (tr-▸ ▸u)) (≤ᶜ-reflexive tr-Conₘ-+ᶜ)
    tr-▸ ωᵘ+ =
      sub ωᵘ+ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (level ▸t) =
      level (tr-▸ ▸t)
    tr-▸ (Liftₘ ▸A ▸t) =
      Liftₘ (tr-▸[𝟘ᵐ?] ▸A) (tr-▸ ▸t)
    tr-▸ (liftₘ ▸t) =
      liftₘ (tr-▸ ▸t)
    tr-▸ (lowerₘ ▸t) =
      lowerₘ (tr-▸ ▸t)
    tr-▸ (Uₘ ▸t) =
      sub (Uₘ (tr-▸[𝟘ᵐ?] ▸t)) tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ ℕₘ =
      sub ℕₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ Emptyₘ =
      sub Emptyₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ Unitₘ =
      sub Unitₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (ΠΣₘ {γ = γ} {m = m} {p = p} {δ = δ} {q = q} {b = b} ▸A ▸P) = sub
      (ΠΣₘ (▸-cong (tr-Mode-ᵐ· m b) (tr-▸ ▸A))
        (sub (tr-▸ ▸P) (begin
           tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q  ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ⟩
           tr-Conₘ δ ∙ tr (Mo₁.⌜ m ⌝ M₁.· q)        ∎)))
      (begin
         tr-Conₘ (p C₁.·ᶜ γ C₁.+ᶜ δ)                        ≈⟨ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ (p C₁.·ᶜ γ) C₂.+ᶜ tr-Conₘ δ                ≈⟨ +ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
         tr p C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ               ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ tr-≤-tr-BinderMode) ⟩
         tr-BinderMode b p C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ  ∎)

      where
      open CR₂
    tr-▸ (var {x = x} {m = m}) = sub
      var
      (begin
         tr-Conₘ (C₁.𝟘ᶜ C₁., x ≔ Mo₁.⌜ m ⌝)   ≡⟨ CQ.tr-,≔ ⟩
         tr-Conₘ C₁.𝟘ᶜ C₂., x ≔ tr Mo₁.⌜ m ⌝  ≤⟨ update-monotoneˡ _ tr-Conₘ-𝟘ᶜ-≤ᶜ ⟩
         C₂.𝟘ᶜ C₂., x ≔ tr Mo₁.⌜ m ⌝          ≤⟨ update-monotoneʳ _ (tr-⌜⌝ m) ⟩
         C₂.𝟘ᶜ C₂., x ≔ Mo₂.⌜ tr-Mode m ⌝     ∎)
      where
      open CR₂
    tr-▸ (lamₘ {γ = γ} {m = m} {p = p} {t = t} ▸t) = lamₘ
      (sub (tr-▸ ▸t) (begin
         tr-Conₘ γ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ⟩
         tr-Conₘ γ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p)        ∎))
      where
      open CR₂
    tr-▸ (_∘ₘ_ {γ = γ} {m = m} {δ = δ} {p = p} ▸t ▸u) = sub
      (tr-▸ ▸t ∘ₘ ▸-cong (tr-Mode-ᵐ· m BMΠ) (tr-▸ ▸u))
      (begin
         tr-Conₘ (γ C₁.+ᶜ p C₁.·ᶜ δ)           ≈⟨ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ γ C₂.+ᶜ tr-Conₘ (p C₁.·ᶜ δ)   ≈⟨ +ᶜ-congˡ tr-Conₘ-·ᶜ ⟩
         tr-Conₘ γ C₂.+ᶜ tr p C₂.·ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ (prodʷₘ {γ = γ} {m = m} {p = p} {δ = δ} ▸t ▸u) = sub
      (prodʷₘ (▸-cong (tr-Mode-ᵐ· m (BMΣ 𝕨)) (tr-▸ ▸t)) (tr-▸ ▸u))
      (begin
         tr-Conₘ (p C₁.·ᶜ γ C₁.+ᶜ δ)             ≈⟨ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ (p C₁.·ᶜ γ) C₂.+ᶜ tr-Conₘ δ     ≈⟨ +ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
         tr p C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ    ≤⟨ +ᶜ-monotoneˡ (·ᶜ-monotoneˡ tr-≤-tr-Σ) ⟩
         tr-Σ p C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ (prodˢₘ {γ = γ} {m = m} {p = p} {δ = δ} ▸t ▸u) = sub
      (prodˢₘ (▸-cong (tr-Mode-ᵐ· m (BMΣ 𝕤)) (tr-▸ ▸t)) (tr-▸ ▸u))
      (begin
         tr-Conₘ (p C₁.·ᶜ γ C₁.∧ᶜ δ)             ≤⟨ tr-Conₘ-∧ᶜ ⟩
         tr-Conₘ (p C₁.·ᶜ γ) C₂.∧ᶜ tr-Conₘ δ     ≈⟨ ∧ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
         tr p C₂.·ᶜ tr-Conₘ γ C₂.∧ᶜ tr-Conₘ δ    ≤⟨ ∧ᶜ-monotoneˡ (·ᶜ-monotoneˡ tr-≤-tr-Σ) ⟩
         tr-Σ p C₂.·ᶜ tr-Conₘ γ C₂.∧ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ ▸fst@(fstₘ {p = p} _ _) =
      case UP′₁.inv-usage-fst₀₁ ▸fst of λ where
        (_ , m , refl , ▸t , γ≤ , ok) →
          fstₘ₀₁ (tr-Mode m)
            (sub (▸-cong (tr-Mode-ᵐ· m (BMΣ 𝕤)) (tr-▸ ▸t)) (tr-Conₘ-monotone γ≤))
            (sym (tr-Mode-ᵐ· _ (BMΣ 𝕤)))
            (λ mp≡𝟙 → tr-Σ-≤-𝟙 (ok (tr-Mode-injective mp≡𝟙)))
    tr-▸ (sndₘ ▸t) =
      sndₘ (tr-▸ ▸t)
    tr-▸
      (prodrecₘ {γ = γ} {m = m} {r = r} {δ = δ} {p = p} {η = η} {q = q}
         ▸t ▸u ▸Q ok) = sub
      (prodrecₘ (▸-cong (tr-Mode-ᵐ· m BMΠ) (tr-▸ ▸t))
         (sub (tr-▸ ▸u) (begin
            tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r M₂.· tr-Σ p ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                            ≤⟨ ≤ᶜ-refl ∙ ·-monotoneʳ tr-·-tr-Σ-≤ ∙ ≤-refl ⟩

            tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr (r M₁.· p) ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                            ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩

            tr-Conₘ δ ∙ tr (Mo₁.⌜ m ⌝ M₁.· r M₁.· p) ∙
            tr (Mo₁.⌜ m ⌝ M₁.· r)                                  ∎))
         (tr-∙▸[𝟘ᵐ?] ▸Q) (Prodrec-preserved (≈ᵐ-tr-Mode {m = m}) ok))
      (begin
         tr-Conₘ (r C₁.·ᶜ γ C₁.+ᶜ δ)           ≈⟨ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ (r C₁.·ᶜ γ) C₂.+ᶜ tr-Conₘ δ   ≈⟨ +ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
         tr r C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ zeroₘ =
      sub zeroₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (sucₘ ▸t) =
      sucₘ (tr-▸ ▸t)
    tr-▸
      (natrecₘ {γ = γ} {m = m} {δ = δ} {p = p} {r = r} {η = η} {θ = θ}
         {q = q} ▸z ▸s ▸n ▸P) = sub
      (natrecₘ (tr-▸ ▸z)
         (sub (tr-▸ ▸s) (begin
            tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                                ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩

            tr-Conₘ δ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· r)  ∎))
         (tr-▸ ▸n)
         (tr-∙▸[𝟘ᵐ?] ▸P))
      tr-Conₘ-nrᶜ
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open Graded.Modality.Morphism.Forward-instances common-properties
      open CQ.Is-nr-preserving-morphism nr-preserving
      open CR₂
    tr-▸
      (natrec-no-nrₘ {m = m} {δ = δ} {p = p} {r = r} {η = η} {χ = χ}
         ▸z ▸s ▸n ▸P χ≤γ χ≤δ χ≤η fix) =
      natrec-no-nrₘ₀₁ (tr-▸ ▸z)
        (sub (tr-▸ ▸s) (begin
           tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
           Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                                ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩

           tr-Conₘ δ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· r)  ∎))
        (tr-▸ ▸n)
        (tr-∙▸[𝟘ᵐ?] ▸P)
        (tr-Conₘ-monotone χ≤γ)
        (λ ok →
           case 𝟘ᵐ-in-first-if-in-second ok of λ where
             (inj₁ ok) →
               tr-Conₘ-monotone (χ≤δ (𝟘ᵐ-allowed→¬Trivialᵐ _ ok))
             (inj₂ trivial) → begin
               tr-Conₘ χ  ≡⟨ cong tr-Conₘ (CP₁.≈ᶜ→≡ (CP₁.≈ᶜ-trivial trivial)) ⟩
               tr-Conₘ δ  ∎)
        (λ ⦃ 𝟘-well-behaved = 𝟘-well-behaved ⦄ →
           case 𝟘-well-behaved-in-first-if-in-second
                  𝟘-well-behaved of λ where
             (inj₁ 𝟘-well-behaved) →
               tr-Conₘ-monotone (χ≤η (λ _ → 𝟘-well-behaved))
             (inj₂ trivial) → begin
               tr-Conₘ χ  ≡⟨ cong tr-Conₘ (CP₁.≈ᶜ→≡ (CP₁.≈ᶜ-trivial trivial)) ⟩
               tr-Conₘ η  ∎)
        (begin
           tr-Conₘ χ                                    ≤⟨ tr-Conₘ-monotone fix ⟩

           tr-Conₘ (δ C₁.+ᶜ p C₁.·ᶜ η C₁.+ᶜ r C₁.·ᶜ χ)  ≈⟨ ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ $
                                                           ≈ᶜ-trans tr-Conₘ-+ᶜ $
                                                           +ᶜ-cong tr-Conₘ-·ᶜ tr-Conₘ-·ᶜ ⟩
           tr-Conₘ δ C₂.+ᶜ tr p C₂.·ᶜ tr-Conₘ η C₂.+ᶜ
           tr r C₂.·ᶜ tr-Conₘ χ                         ∎)
      where
      open Graded.Modality.Morphism.Forward-instances common-properties
      open Is-no-nr-preserving no-nr-preserving
      open CR₂
    tr-▸
      (natrec-no-nr-glbₘ {m} {δ} {p} {r} {η} {χ} {x} ▸z ▸s ▸n ▸P x-glb χ-glb) =
      let x′ , x′-glb = tr-nrᵢ-𝟙-GLB x-glb
          χ′ , χ′-glb = tr-Conₘ-nrᵢᶜ-GLBᶜ χ-glb
      in  sub
           (natrec-no-nr-glbₘ (tr-▸ ▸z)
             (sub (tr-▸ ▸s) (begin
               tr-Conₘ δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
                Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                                ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩

                tr-Conₘ δ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· r)  ∎))
             (tr-▸ ▸n)
             (tr-∙▸[𝟘ᵐ?] ▸P)
             x′-glb χ′-glb) (begin
               tr-Conₘ (x C₁.·ᶜ η C₁.+ᶜ χ) ≈⟨ tr-Conₘ-+ᶜ ⟩
               tr-Conₘ (x C₁.·ᶜ η) C₂.+ᶜ tr-Conₘ χ ≈⟨ +ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
               tr x C₂.·ᶜ tr-Conₘ η C₂.+ᶜ tr-Conₘ χ ≤⟨ +ᶜ-monotone (·ᶜ-monotoneˡ
                                                        (x′-glb .proj₂ _ (λ i → ≤-trans (tr-monotone (x-glb .proj₁ i))
                                                                                 (≤-trans (≤-reflexive (tr-nrᵢ i))
                                                                                 (nrᵢ-monotone i tr-𝟙 ≤-refl)))))
                                                        (χ′-glb .proj₂ _ (λ i → ≤ᶜ-trans (tr-Conₘ-monotone (χ-glb .proj₁ i))
                                                                                 (≤ᶜ-reflexive tr-Conₘ-nrᵢᶜ))) ⟩
               x′ C₂.·ᶜ tr-Conₘ η C₂.+ᶜ χ′ ∎)
      where
      open Graded.Modality.Morphism.Forward-instances common-properties
      open Is-no-nr-glb-preserving-morphism no-nr-glb-preserving
      open CQ.Is-no-nr-glb-preserving-morphism no-nr-glb-preserving
      open CR₂
    tr-▸ (emptyrecₘ {m = m} ▸t ▸A ok) = sub
      (emptyrecₘ (▸-cong (tr-Mode-ᵐ· m BMΠ) (tr-▸ ▸t)) (tr-▸[𝟘ᵐ?] ▸A)
         (Emptyrec-preserved (≈ᵐ-tr-Mode {m = m}) ok))
      (≤ᶜ-reflexive tr-Conₘ-·ᶜ)
    tr-▸ starʷₘ = sub starʷₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ {m = m} (starˢₘ {γ = γ} prop) =
      let _ , prop′ , γ≤ = lemma starˢ-sink-preserved prop
      in  sub (starˢₘ prop′) γ≤
      where
      open CR₂
      lemma : {b b′ : Bool} →
        b ≡ b′ →
        (¬ T b → C₁.𝟘ᶜ C₁.≈ᶜ γ) →
          ∃ λ γ′ →
            (¬ T b′ → C₂.𝟘ᶜ C₂.≈ᶜ γ′) ×
            tr-Conₘ (Mo₁.⌜ m ⌝ C₁.·ᶜ γ) C₂.≤ᶜ Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ γ′
      lemma {(false)} refl prop =
        _ , (λ _ → ≈ᶜ-refl) , (begin
          tr-Conₘ (Mo₁.⌜ m ⌝ C₁.·ᶜ γ)       ≈⟨ tr-Conₘ-·ᶜ ⟩
          tr Mo₁.⌜ m ⌝ C₂.·ᶜ tr-Conₘ γ      ≈⟨ ·ᶜ-congˡ (CQ.tr-≈ᶜ (CP₁.≈ᶜ-sym (prop idᶠ))) ⟩
          tr Mo₁.⌜ m ⌝ C₂.·ᶜ tr-Conₘ C₁.𝟘ᶜ  ≤⟨ ·ᶜ-monotone tr-Conₘ-𝟘ᶜ-≤ᶜ (tr-⌜⌝ m) ⟩
          Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ C₂.𝟘ᶜ     ∎)
      lemma {(true)} refl prop =
        _ , ⊥-elim ∘→ (_$ _) , (begin
          tr-Conₘ (Mo₁.⌜ m ⌝ C₁.·ᶜ γ)        ≈⟨ tr-Conₘ-·ᶜ ⟩
          tr Mo₁.⌜ m ⌝ C₂.·ᶜ tr-Conₘ γ       ≤⟨ ·ᶜ-monotoneˡ (tr-⌜⌝ m) ⟩
          Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ tr-Conₘ γ  ∎)

    tr-▸ {m = m} (unitrecₘ {γ} {p = p} {δ} ▸t ▸u ▸A ok) =
      sub (unitrecₘ (▸-cong (tr-Mode-ᵐ· m BMΠ) (tr-▸ ▸t))
             (tr-▸ ▸u) (tr-∙▸[𝟘ᵐ?] ▸A)
             (Unitrec-preserved (≈ᵐ-tr-Mode {m = m}) ok))
          (begin
            tr-Conₘ (p C₁.·ᶜ γ C₁.+ᶜ δ)           ≈⟨ tr-Conₘ-+ᶜ ⟩
            tr-Conₘ (p C₁.·ᶜ γ) C₂.+ᶜ tr-Conₘ δ   ≈⟨ +ᶜ-congʳ tr-Conₘ-·ᶜ ⟩
            tr p C₂.·ᶜ tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ  ∎)
      where
      open CR₂
    tr-▸ (Idₘ {γ} {δ} {η} ok ▸A ▸t ▸u) = sub
      (Idₘ (ok ∘→ Id-erased-preserved .proj₂) (tr-▸ ▸A) (tr-▸ ▸t)
         (tr-▸ ▸u))
      (begin
         tr-Conₘ (γ C₁.+ᶜ δ C₁.+ᶜ η)                ≈⟨ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ γ C₂.+ᶜ tr-Conₘ (δ C₁.+ᶜ η)        ≈⟨ +ᶜ-congˡ tr-Conₘ-+ᶜ ⟩
         tr-Conₘ γ C₂.+ᶜ tr-Conₘ δ C₂.+ᶜ tr-Conₘ η  ∎)
      where
      open CR₂
    tr-▸ (Id₀ₘ ok ▸A ▸t ▸u) = sub
      (Id₀ₘ (Id-erased-preserved .proj₁ ok) (tr-▸[𝟘ᵐ?] ▸A)
         (tr-▸[𝟘ᵐ?] ▸t) (tr-▸[𝟘ᵐ?] ▸u))
      tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ rflₘ =
      sub rflₘ tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸
      (Jₘ {m} {p} {q} {γ₂} {γ₃} {γ₄} {γ₅} {γ₆}
         _ ▸A ▸t ▸B ▸u ▸v ▸w) = sub
      (Jₘ-generalised (tr-▸[𝟘ᵐ?] ▸A) (tr-▸ ▸t)
         (sub (tr-▸ ▸B) $ begin
            tr-Conₘ γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q                                 ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩

            tr-Conₘ γ₃ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· q)  ∎)
         (tr-▸ ▸u) (tr-▸ ▸v) (tr-▸ ▸w))
      (begin
         tr-Conₘ (ω C₁.·ᶜ (γ₂ C₁.+ᶜ γ₃ C₁.+ᶜ γ₄ C₁.+ᶜ γ₅ C₁.+ᶜ γ₆))   ≈⟨ tr-Conₘ-·ᶜ ⟩

         tr ω C₂.·ᶜ tr-Conₘ (γ₂ C₁.+ᶜ γ₃ C₁.+ᶜ γ₄ C₁.+ᶜ γ₅ C₁.+ᶜ γ₆)  ≈⟨ ·ᶜ-cong
                                                                         (M.Is-omega-preserving-morphism.tr-ω omega-preserving) $

                                                                         ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ $
                                                                         ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ $
                                                                         ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ
                                                                         tr-Conₘ-+ᶜ ⟩
         ω C₂.·ᶜ
         (tr-Conₘ γ₂ C₂.+ᶜ tr-Conₘ γ₃ C₂.+ᶜ tr-Conₘ γ₄ C₂.+ᶜ
          tr-Conₘ γ₅ C₂.+ᶜ tr-Conₘ γ₆)                                ∎)
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open CR₂
      open Graded.Modality.Morphism.Forward-instances common-properties

    tr-▸
      (J₀ₘ₁ {m} {γ₂} {γ₃} {γ₄} {γ₅} {γ₆}
         ⦃ (≡some) ⦄ refl refl ▸A ▸t ▸B ▸u ▸v ▸w) =
      case trivial-⊎-tr-𝟘 of λ where
        (inj₁ trivial₁) → sub
          (Jₘ-generalised (tr-▸[𝟘ᵐ?] ▸A) (tr-▸-trivial trivial₁ ▸t)
             (sub (tr-▸ ▸B) $ begin
                tr-Conₘ γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr M₁.𝟘 ∙
                Mo₂.⌜ tr-Mode m ⌝ M₂.· tr M₁.𝟘                      ≡⟨ cong
                                                                         (λ m →
                                                                            tr-Conₘ γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr M₁.𝟘 ∙
                                                                            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr M₁.𝟘) $
                                                                       Mo₁.only-𝟙ᵐ-without-𝟘ᵐ {m = m} ((_$ trivial₁) ∘→ Mo₁.𝟘ᵐ.non-trivial) ⟩

                tr-Conₘ γ₃ ∙ M₂.𝟙 M₂.· tr M₁.𝟘 ∙ M₂.𝟙 M₂.· tr M₁.𝟘  ≈⟨ ≈ᶜ-refl ∙ M₂.·-identityˡ _ ∙ M₂.·-identityˡ _ ⟩

                tr-Conₘ γ₃ ∙ tr M₁.𝟘 ∙ tr M₁.𝟘                      ∎)
             (tr-▸ ▸u) (tr-▸-trivial trivial₁ ▸v)
             (tr-▸-trivial trivial₁ ▸w))
          (begin
             tr-Conₘ (ω C₁.·ᶜ (γ₃ C₁.+ᶜ γ₄))                       ≡⟨ cong tr-Conₘ $ CP₁.≈ᶜ→≡ $ CP₁.≈ᶜ-trivial trivial₁ ⟩

             tr-Conₘ
               (ω C₁.·ᶜ (γ₂ C₁.+ᶜ γ₃ C₁.+ᶜ γ₄ C₁.+ᶜ γ₅ C₁.+ᶜ γ₆))  ≈⟨ tr-Conₘ-·ᶜ ⟩

             tr ω C₂.·ᶜ
             tr-Conₘ (γ₂ C₁.+ᶜ γ₃ C₁.+ᶜ γ₄ C₁.+ᶜ γ₅ C₁.+ᶜ γ₆)      ≈⟨ ·ᶜ-cong
                                                                      (M.Is-omega-preserving-morphism.tr-ω omega-preserving) $
                                                                      ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ $
                                                                      ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ $
                                                                      ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ
                                                                      tr-Conₘ-+ᶜ ⟩
             ω C₂.·ᶜ
             (tr-Conₘ γ₂ C₂.+ᶜ tr-Conₘ γ₃ C₂.+ᶜ tr-Conₘ γ₄ C₂.+ᶜ
              tr-Conₘ γ₅ C₂.+ᶜ tr-Conₘ γ₆)                         ∎)
        (inj₂ tr-𝟘) → sub
          (J₀ₘ₁-generalised
             (≤ᵉᵐ→≡some→≡not-none
                (erased-matches-for-J-preserved ≈ᵐ-tr-Mode) ≡some
                .proj₂)
             tr-𝟘 tr-𝟘 (tr-▸[𝟘ᵐ?] ▸A) (tr-▸[𝟘ᵐ?] ▸t)
             (sub (tr-▸ ▸B) $ begin
                tr-Conₘ γ₃ ∙ M₂.𝟘 ∙ M₂.𝟘        ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘 ∙ tr-𝟘 ⟩
                tr-Conₘ γ₃ ∙ tr M₁.𝟘 ∙ tr M₁.𝟘  ∎)
             (tr-▸ ▸u) (tr-▸[𝟘ᵐ?] ▸v) (tr-▸[𝟘ᵐ?] ▸w))
          (begin
             tr-Conₘ (ω C₁.·ᶜ (γ₃ C₁.+ᶜ γ₄))        ≈⟨ tr-Conₘ-·ᶜ ⟩
             tr ω C₂.·ᶜ tr-Conₘ (γ₃ C₁.+ᶜ γ₄)       ≈⟨ ·ᶜ-cong
                                                       (M.Is-omega-preserving-morphism.tr-ω omega-preserving)
                                                       tr-Conₘ-+ᶜ ⟩
             ω C₂.·ᶜ (tr-Conₘ γ₃ C₂.+ᶜ tr-Conₘ γ₄)  ∎)
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open CR₂
      open Graded.Modality.Morphism.Forward-instances common-properties
    tr-▸ (J₀ₘ₂ ⦃ (≡all) ⦄ ▸A ▸t ▸B ▸u ▸v ▸w) = J₀ₘ₂
      ⦃ ≤ᵉᵐ→≡all→≡all (erased-matches-for-J-preserved ≈ᵐ-tr-Mode) ≡all ⦄
      (tr-▸[𝟘ᵐ?] ▸A) (tr-▸[𝟘ᵐ?] ▸t) (tr-▸[𝟘ᵐ?] ▸B) (tr-▸ ▸u)
      (tr-▸[𝟘ᵐ?] ▸v) (tr-▸[𝟘ᵐ?] ▸w)
    tr-▸ (Kₘ {m} {p} {γ₂} {γ₃} {γ₄} {γ₅} _ ▸A ▸t ▸B ▸u ▸v) = sub
      (Kₘ-generalised (tr-▸[𝟘ᵐ?] ▸A) (tr-▸ ▸t)
         (sub (tr-▸ ▸B) $ begin
            tr-Conₘ γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ⟩
            tr-Conₘ γ₃ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p)        ∎)
         (tr-▸ ▸u) (tr-▸ ▸v))
      (begin
         tr-Conₘ (ω C₁.·ᶜ (γ₂ C₁.+ᶜ γ₃ C₁.+ᶜ γ₄ C₁.+ᶜ γ₅))   ≈⟨ tr-Conₘ-·ᶜ ⟩

         tr ω C₂.·ᶜ tr-Conₘ (γ₂ C₁.+ᶜ γ₃ C₁.+ᶜ γ₄ C₁.+ᶜ γ₅)  ≈⟨ ·ᶜ-cong
                                                                (M.Is-omega-preserving-morphism.tr-ω omega-preserving) $
                                                                ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ $
                                                                ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ
                                                                tr-Conₘ-+ᶜ ⟩
         ω C₂.·ᶜ
         (tr-Conₘ γ₂ C₂.+ᶜ tr-Conₘ γ₃ C₂.+ᶜ tr-Conₘ γ₄ C₂.+ᶜ
          tr-Conₘ γ₅)                                        ∎)
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open CR₂
      open Graded.Modality.Morphism.Forward-instances common-properties
    tr-▸ (K₀ₘ₁ {m} {γ₂} {γ₃} {γ₄} {γ₅} ⦃ (≡some) ⦄ refl ▸A ▸t ▸B ▸u ▸v) =
      case trivial-⊎-tr-𝟘 of λ where
        (inj₁ trivial₁) → sub
          (Kₘ-generalised (tr-▸[𝟘ᵐ?] ▸A) (tr-▸-trivial trivial₁ ▸t)
             (sub (tr-▸ ▸B) $ begin
                tr-Conₘ γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr M₁.𝟘  ≡⟨ cong (λ m → tr-Conₘ γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr M₁.𝟘) $
                                                                Mo₁.only-𝟙ᵐ-without-𝟘ᵐ {m = m} ((_$ trivial₁) ∘→ Mo₁.𝟘ᵐ.non-trivial) ⟩
                tr-Conₘ γ₃ ∙ M₂.𝟙 M₂.· tr M₁.𝟘               ≈⟨ ≈ᶜ-refl ∙ M₂.·-identityˡ _ ⟩
                tr-Conₘ γ₃ ∙ tr M₁.𝟘                         ∎)
             (tr-▸ ▸u) (tr-▸-trivial trivial₁ ▸v))
          (begin
             tr-Conₘ (ω C₁.·ᶜ (γ₃ C₁.+ᶜ γ₄))                     ≡⟨ cong tr-Conₘ $ CP₁.≈ᶜ→≡ $ CP₁.≈ᶜ-trivial trivial₁ ⟩

             tr-Conₘ (ω C₁.·ᶜ (γ₂ C₁.+ᶜ γ₃ C₁.+ᶜ γ₄ C₁.+ᶜ γ₅))   ≈⟨ tr-Conₘ-·ᶜ ⟩

             tr ω C₂.·ᶜ tr-Conₘ (γ₂ C₁.+ᶜ γ₃ C₁.+ᶜ γ₄ C₁.+ᶜ γ₅)  ≈⟨ ·ᶜ-cong (M.Is-omega-preserving-morphism.tr-ω omega-preserving) $
                                                                    ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ $
                                                                    ≈ᶜ-trans tr-Conₘ-+ᶜ $ +ᶜ-congˡ
                                                                    tr-Conₘ-+ᶜ ⟩
             ω C₂.·ᶜ
             (tr-Conₘ γ₂ C₂.+ᶜ tr-Conₘ γ₃ C₂.+ᶜ tr-Conₘ γ₄ C₂.+ᶜ
              tr-Conₘ γ₅)                                           ∎)
        (inj₂ tr-𝟘) → sub
          (K₀ₘ₁-generalised
             (≤ᵉᵐ→≡some→≡not-none
                (erased-matches-for-K-preserved ≈ᵐ-tr-Mode) ≡some
                .proj₂)
             tr-𝟘 (tr-▸[𝟘ᵐ?] ▸A) (tr-▸[𝟘ᵐ?] ▸t)
             (sub (tr-▸ ▸B) $ begin
                tr-Conₘ γ₃ ∙ M₂.𝟘     ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘 ⟩
                tr-Conₘ γ₃ ∙ tr M₁.𝟘  ∎)
             (tr-▸ ▸u) (tr-▸[𝟘ᵐ?] ▸v))
          (begin
             tr-Conₘ (ω C₁.·ᶜ (γ₃ C₁.+ᶜ γ₄))        ≈⟨ tr-Conₘ-·ᶜ ⟩
             tr ω C₂.·ᶜ tr-Conₘ (γ₃ C₁.+ᶜ γ₄)       ≈⟨ ·ᶜ-cong
                                                        (M.Is-omega-preserving-morphism.tr-ω omega-preserving)
                                                        tr-Conₘ-+ᶜ ⟩
             ω C₂.·ᶜ (tr-Conₘ γ₃ C₂.+ᶜ tr-Conₘ γ₄)  ∎)
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open CR₂
      open Graded.Modality.Morphism.Forward-instances common-properties
    tr-▸ (K₀ₘ₂ ⦃ (≡none) ⦄ ▸A ▸t ▸B ▸u ▸v) = K₀ₘ₂
      ⦃ ≤ᵉᵐ→≡all→≡all (erased-matches-for-K-preserved ≈ᵐ-tr-Mode) ≡none ⦄
      (tr-▸[𝟘ᵐ?] ▸A) (tr-▸[𝟘ᵐ?] ▸t) (tr-▸[𝟘ᵐ?] ▸B) (tr-▸ ▸u)
      (tr-▸[𝟘ᵐ?] ▸v)
    tr-▸ ([]-congₘ {m} ▸l ▸A ▸t ▸u ▸v ok) = sub
      ([]-congₘ (tr-▸[𝟘ᵐ?] ▸l) (tr-▸[𝟘ᵐ?] ▸A) (tr-▸[𝟘ᵐ?] ▸t)
         (tr-▸[𝟘ᵐ?] ▸u) (tr-▸[𝟘ᵐ?] ▸v)
         ([]-cong-mode-preserved ≈ᵐ-tr-Mode ok))
      tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (Quot ok ▸A ▸B) =
      Quot (Quot-preserved ok) (tr-▸ ▸A) (tr-▸[𝟘ᵐ?] ▸B)
    tr-▸ (class ok ▸t) =
      class (Quot-preserved ok) (tr-▸ ▸t)
    tr-▸ (resp ok ▸A ▸B ▸t ▸u ▸v refl) =
      sub
        (resp (Quot-preserved ok) (tr-▸[𝟘ᵐ?] ▸A) (tr-▸[𝟘ᵐ?] ▸B)
           (tr-▸[𝟘ᵐ?] ▸t) (tr-▸[𝟘ᵐ?] ▸u) (tr-▸[𝟘ᵐ?] ▸v)
           (tr-Mode-𝟘ᵐ? λ _ →
              Mo₁.¬Trivialᵐ→𝟘ᵐ-allowed (Co₁.Quot-allowed→¬Trivialᵐ ok)))
        tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (set ok ▸A ▸B ▸t ▸u ▸v ▸w refl) =
      sub
        (set (Quot-preserved ok)
           (tr-▸[𝟘ᵐ?] ▸A) (tr-▸[𝟘ᵐ?] ▸B) (tr-▸[𝟘ᵐ?] ▸t) (tr-▸[𝟘ᵐ?] ▸u)
           (tr-▸[𝟘ᵐ?] ▸v) (tr-▸[𝟘ᵐ?] ▸w)
           (tr-Mode-𝟘ᵐ? λ _ →
              Mo₁.¬Trivialᵐ→𝟘ᵐ-allowed (Co₁.Quot-allowed→¬Trivialᵐ ok)))
        tr-Conₘ-𝟘ᶜ-≤ᶜ
    tr-▸ (qrec₀ {γ₂} {m} {γ₅} ok₁ ok₂ ▸C ▸t ▸u ▸v ▸w) =
      sub
        (qrec₀ (Quot-preserved ok₁)
           (Qrec-motive-erased-preserved .proj₁ ok₂) (tr-▸[𝟘ᵐ?] ▸C)
           (sub (tr-▸ ▸t) $ begin
             tr-Conₘ γ₂ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· ω    ≈˘⟨ ≈ᶜ-refl ∙ M₂.·-congˡ tr-ω ⟩
             tr-Conₘ γ₂ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr ω ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ⟩
             tr-Conₘ γ₂ ∙ tr (Mo₁.⌜ m ⌝ M₁.· ω)       ∎)
           (tr-▸[𝟘ᵐ?] ▸u) (tr-▸[𝟘ᵐ?] ▸v) (tr-▸ ▸w))
        (begin
           tr-Conₘ (γ₂ C₁.+ᶜ ω C₁.·ᶜ γ₅)           ≈⟨ ≈ᶜ-trans tr-Conₘ-+ᶜ (+ᶜ-congˡ tr-Conₘ-·ᶜ) ⟩
           tr-Conₘ γ₂ C₂.+ᶜ tr ω C₂.·ᶜ tr-Conₘ γ₅  ≈⟨ +ᶜ-congˡ (·ᶜ-congʳ tr-ω) ⟩
           tr-Conₘ γ₂ C₂.+ᶜ ω C₂.·ᶜ tr-Conₘ γ₅     ∎)

      where
      open ≤ᶜ-reasoning
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open Graded.Modality.Morphism.Forward-instances common-properties
      open M.Is-omega-preserving-morphism omega-preserving
    tr-▸ (qrec₁ {γ₁} {m} {γ₂} {γ₅} ok₁ ok₂ ▸C ▸t ▸u ▸v ▸w) =
      sub
        (qrec₁ (Quot-preserved ok₁)
           (ok₂ ∘→ Qrec-motive-erased-preserved .proj₂)
           (sub (tr-▸ ▸C) $ begin
              tr-Conₘ γ₁ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· ω     ≈˘⟨ ≈ᶜ-refl ∙ M₂.·-congˡ tr-ω ⟩
              tr-Conₘ γ₁ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr ω  ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ⟩
              tr-Conₘ γ₁ ∙ tr (Mo₁.⌜ m ⌝ M₁.· ω)        ∎)
           (sub (tr-▸ ▸t) $ begin
              tr-Conₘ γ₂ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· ω     ≈˘⟨ ≈ᶜ-refl ∙ M₂.·-congˡ tr-ω ⟩
              tr-Conₘ γ₂ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr ω  ≈⟨ ≈ᶜ-refl ∙ tr-⌜⌝-· m ⟩
              tr-Conₘ γ₂ ∙ tr (Mo₁.⌜ m ⌝ M₁.· ω)        ∎)
           (tr-▸[𝟘ᵐ?] ▸u) (tr-▸[𝟘ᵐ?] ▸v) (tr-▸ ▸w))
        (begin
           tr-Conₘ (ω C₁.·ᶜ (γ₁ C₁.+ᶜ γ₂ C₁.+ᶜ γ₅))                ≈⟨ ≈ᶜ-trans tr-Conₘ-·ᶜ $
                                                                      ·ᶜ-cong tr-ω $
                                                                      ≈ᶜ-trans tr-Conₘ-+ᶜ (+ᶜ-congˡ tr-Conₘ-+ᶜ) ⟩
           ω C₂.·ᶜ (tr-Conₘ γ₁ C₂.+ᶜ tr-Conₘ γ₂ C₂.+ᶜ tr-Conₘ γ₅)  ∎)
      where
      open ≤ᶜ-reasoning
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open Graded.Modality.Morphism.Forward-instances common-properties
      open M.Is-omega-preserving-morphism omega-preserving
    tr-▸ (sub ▸t γ≤δ) =
      sub (tr-▸ ▸t) (tr-Conₘ-monotone γ≤δ)

    private

      -- A variant of tr-▸.

      tr-▸[𝟘ᵐ?] :
        γ U₁.▸[ Mo₁.𝟘ᵐ? ] t → tr-Conₘ γ U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-▸[𝟘ᵐ?] {γ = γ} {t = t} = Mo₁.𝟘ᵐ?-elim
        (λ m → γ U₁.▸[ m ] t → tr-Conₘ γ U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t)
        (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) ∘→ tr-▸)
        (λ not-ok ▸t → Mo₂.𝟘ᵐ?-elim
           (λ m → tr-Conₘ γ U₂.▸[ m ] tr-Term t)
           (λ ⦃ ok = ok ⦄ →
              sub (▸-𝟘₀₁ (tr-▸ ▸t)) (tr-Conₘ-≤ᶜ-𝟘ᶜ not-ok ok))
           (λ _ → tr-▸ ▸t))

      -- A variant of tr-▸[𝟘ᵐ?].

      tr-▸[𝟘ᵐ?]′ :
        γ U₁.▸[ m ] t → ∃ λ δ → δ U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-▸[𝟘ᵐ?]′ {t} ▸t = Mo₂.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ U₂.▸[ m ] tr-Term t)
        (_ , ▸-𝟘₀₁ (tr-▸ ▸t))
        (λ not-ok →
             _
           , ▸-cong (Mo₂.Mode-propositional-without-𝟘ᵐ not-ok)
               (tr-▸ ▸t))

      -- A variant of tr-▸.

      tr-▸-trivial :
        M₁.Trivial → γ U₁.▸[ m₁ ] t → tr-Conₘ γ U₂.▸[ tr-Mode m₂ ] tr-Term t
      tr-▸-trivial trivial =
        ▸-cong
          (cong tr-Mode (Mo₁.Mode-propositional-if-trivial trivial)) ∘→
        tr-▸

      -- A variant of tr-▸.

      tr-∙▸[𝟘ᵐ?] :
        γ ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· p U₁.▸[ Mo₁.𝟘ᵐ? ] t →
        tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-∙▸[𝟘ᵐ?] {γ = γ} {p = p} {t = t} = Mo₁.𝟘ᵐ?-elim
        (λ m →
           γ ∙ Mo₁.⌜ m ⌝ M₁.· p U₁.▸[ m ] t →
           tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p U₂.▸[ Mo₂.𝟘ᵐ? ]
             tr-Term t)
        (λ ⦃ ok = ok ⦄ ▸t →
           sub (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) (tr-▸ ▸t)) (begin
             tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙
                                                       Mo₂.𝟘ᵐ?-elim (λ m → Mo₂.⌜ m ⌝ M₂.· tr p ≡ M₂.𝟘)
                                                         (M₂.·-zeroˡ _)
                                                         (λ not-ok → ⊥-elim (not-ok (𝟘ᵐ-in-second-if-in-first ok))) ⟩
             tr-Conₘ γ ∙ M₂.𝟘                       ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘-≡-𝟘ᵐ ok ⟩
             tr-Conₘ γ ∙ tr M₁.𝟘                    ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ⟩
             tr-Conₘ γ ∙ tr (M₁.𝟘 M₁.· p)           ∎))
        (λ not-ok ▸t → Mo₂.𝟘ᵐ?-elim
           (λ m → tr-Conₘ γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p U₂.▸[ m ] tr-Term t)
           (λ ⦃ ok = ok ⦄ →
              sub (▸-𝟘₀₁ (tr-▸ ▸t)) (begin
                tr-Conₘ γ ∙ M₂.𝟘 M₂.· tr p  ≤⟨ tr-Conₘ-≤ᶜ-𝟘ᶜ not-ok ok ∙ ≤-reflexive (M₂.·-zeroˡ _) ⟩
                C₂.𝟘ᶜ                       ∎))
           (λ not-ok →
              sub (tr-▸ ▸t) (begin
                tr-Conₘ γ ∙ M₂.𝟙 M₂.· tr p    ≈⟨ ≈ᶜ-refl ∙ M₂.·-identityˡ _ ⟩
                tr-Conₘ γ ∙ tr p              ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-identityˡ _) ⟩
                tr-Conₘ γ ∙ tr (M₁.𝟙 M₁.· p)  ∎)))
        where
        open CR₂

      -- A variant of tr-∙▸[𝟘ᵐ?].

      tr-∙▸[𝟘ᵐ?]′ :
        γ ∙ Mo₁.⌜ m ⌝ M₁.· p U₁.▸[ m ] t →
        ∃ λ δ → δ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-∙▸[𝟘ᵐ?]′ {γ} {m = 𝟘ᵐ[ ok ]} {p} ▸t =
          tr-Conₘ γ
        , sub (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) (tr-▸ ▸t)) (begin
            tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙
                                                      Mo₂.𝟘ᵐ?-elim (λ m → Mo₂.⌜ m ⌝ M₂.· tr p ≡ M₂.𝟘)
                                                        (M₂.·-zeroˡ _)
                                                        (λ not-ok → ⊥-elim (not-ok (𝟘ᵐ-in-second-if-in-first ok))) ⟩
            tr-Conₘ γ ∙ M₂.𝟘                       ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘-≡-𝟘ᵐ ok ⟩
            tr-Conₘ γ ∙ tr M₁.𝟘                    ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ⟩
            tr-Conₘ γ ∙ tr (M₁.𝟘 M₁.· p)           ∎)
        where
        open CR₂
      tr-∙▸[𝟘ᵐ?]′ {γ} {m = 𝟙ᵐ} {p} {t} ▸t = Mo₂.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ ∙ Mo₂.⌜ m ⌝ M₂.· tr p U₂.▸[ m ] tr-Term t)
        ( C₂.𝟘ᶜ
        , sub (▸-𝟘₀₁ (tr-▸ ▸t)) (begin
            C₂.𝟘ᶜ ∙ M₂.𝟘 M₂.· tr p  ≈⟨ ≈ᶜ-refl ∙ M₂.·-zeroˡ _ ⟩
            C₂.𝟘ᶜ                   ∎)
        )
        (λ not-ok →
             tr-Conₘ γ
           , sub (tr-▸ ▸t) (begin
               tr-Conₘ γ ∙ M₂.𝟙 M₂.· tr p    ≈⟨ ≈ᶜ-refl ∙ M₂.·-identityˡ _ ⟩
               tr-Conₘ γ ∙ tr p              ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-identityˡ _) ⟩
               tr-Conₘ γ ∙ tr (M₁.𝟙 M₁.· p)  ∎))
        where
        open CR₂

      -- A variant of tr-▸.

      tr-∙∙▸[𝟘ᵐ?] :
        γ ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· p ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· q
          U₁.▸[ Mo₁.𝟘ᵐ? ] t →
        tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p ∙
          Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr q
          U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-∙∙▸[𝟘ᵐ?] {γ} {p} {q} {t} = Mo₁.𝟘ᵐ?-elim
        (λ m →
           γ ∙ Mo₁.⌜ m ⌝ M₁.· p ∙ Mo₁.⌜ m ⌝ M₁.· q U₁.▸[ m ] t →
           tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p ∙
             Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr q
             U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t)
        (λ ⦃ ok = ok ⦄ ▸t →
           sub (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) (tr-▸ ▸t)) $ begin
             tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p ∙
             Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr q                        ≈⟨ Mo₂.𝟘ᵐ?-elim
                                                                   (λ m →
                                                                      tr-Conₘ γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p ∙ Mo₂.⌜ m ⌝ M₂.· tr q C₂.≈ᶜ
                                                                      tr-Conₘ γ ∙ M₂.𝟘 ∙ M₂.𝟘)
                                                                   (≈ᶜ-refl ∙ M₂.·-zeroˡ _ ∙ M₂.·-zeroˡ _)
                                                                   (λ not-ok → ⊥-elim (not-ok (𝟘ᵐ-in-second-if-in-first ok))) ⟩
             tr-Conₘ γ ∙ M₂.𝟘 ∙ M₂.𝟘                          ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘-≡-𝟘ᵐ ok ∙ tr-𝟘-≡-𝟘ᵐ ok ⟩
             tr-Conₘ γ ∙ tr M₁.𝟘 ∙ tr M₁.𝟘                    ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ∙ cong tr (M₁.·-zeroˡ _) ⟩
             tr-Conₘ γ ∙ tr (M₁.𝟘 M₁.· p) ∙ tr (M₁.𝟘 M₁.· q)  ∎)
        (λ not-ok ▸t → Mo₂.𝟘ᵐ?-elim
           (λ m →
              tr-Conₘ γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p ∙ Mo₂.⌜ m ⌝ M₂.· tr q
                U₂.▸[ m ] tr-Term t)
           (λ ⦃ ok = ok ⦄ →
              sub (▸-𝟘₀₁ (tr-▸ ▸t)) $ begin
                tr-Conₘ γ ∙ M₂.𝟘 M₂.· tr p ∙ M₂.𝟘 M₂.· tr q  ≤⟨ tr-Conₘ-≤ᶜ-𝟘ᶜ not-ok ok ∙ ≤-reflexive (M₂.·-zeroˡ _) ∙
                                                                ≤-reflexive (M₂.·-zeroˡ _) ⟩
                C₂.𝟘ᶜ                                        ∎)
           (λ not-ok →
              sub (tr-▸ ▸t) $ begin
                tr-Conₘ γ ∙ M₂.𝟙 M₂.· tr p ∙ M₂.𝟙 M₂.· tr q      ≈⟨ ≈ᶜ-refl ∙ M₂.·-identityˡ _ ∙ M₂.·-identityˡ _ ⟩
                tr-Conₘ γ ∙ tr p ∙ tr q                          ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-identityˡ _) ∙ cong tr (M₁.·-identityˡ _) ⟩
                tr-Conₘ γ ∙ tr (M₁.𝟙 M₁.· p) ∙ tr (M₁.𝟙 M₁.· q)  ∎))
        where
        open CR₂

      -- A variant of tr-∙∙▸[𝟘ᵐ?].

      tr-∙∙▸[𝟘ᵐ?]′ :
        γ ∙ Mo₁.⌜ m ⌝ M₁.· p ∙ Mo₁.⌜ m ⌝ M₁.· q U₁.▸[ m ] t →
        ∃ λ δ →
            δ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr q
              U₂.▸[ Mo₂.𝟘ᵐ? ] tr-Term t
      tr-∙∙▸[𝟘ᵐ?]′ {γ} {m = 𝟘ᵐ[ ok ]} {p} {q} ▸t =
          tr-Conₘ γ
        , sub (▸-cong (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) (tr-▸ ▸t)) (begin
            tr-Conₘ γ ∙ Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr p ∙
            Mo₂.⌜ Mo₂.𝟘ᵐ? ⌝ M₂.· tr q                        ≈⟨ Mo₂.𝟘ᵐ?-elim
                                                                  (λ m →
                                                                     tr-Conₘ γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p ∙ Mo₂.⌜ m ⌝ M₂.· tr q C₂.≈ᶜ
                                                                     tr-Conₘ γ ∙ M₂.𝟘 ∙ M₂.𝟘)
                                                                  (≈ᶜ-refl ∙ M₂.·-zeroˡ _ ∙ M₂.·-zeroˡ _)
                                                                  (λ not-ok → ⊥-elim (not-ok (𝟘ᵐ-in-second-if-in-first ok))) ⟩
            tr-Conₘ γ ∙ M₂.𝟘 ∙ M₂.𝟘                          ≈˘⟨ ≈ᶜ-refl ∙ tr-𝟘-≡-𝟘ᵐ ok ∙ tr-𝟘-≡-𝟘ᵐ ok ⟩
            tr-Conₘ γ ∙ tr M₁.𝟘 ∙ tr M₁.𝟘                    ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ∙ cong tr (M₁.·-zeroˡ _) ⟩
            tr-Conₘ γ ∙ tr (M₁.𝟘 M₁.· p) ∙ tr (M₁.𝟘 M₁.· q)  ∎)
        where
        open CR₂
      tr-∙∙▸[𝟘ᵐ?]′ {γ} {m = 𝟙ᵐ} {p} {q} {t} ▸t = Mo₂.𝟘ᵐ?-elim
        (λ m →
           ∃ λ δ →
               δ ∙ Mo₂.⌜ m ⌝ M₂.· tr p ∙ Mo₂.⌜ m ⌝ M₂.· tr q
                 U₂.▸[ m ] tr-Term t)
        ( C₂.𝟘ᶜ
        , sub (▸-𝟘₀₁ (tr-▸ ▸t)) (begin
            C₂.𝟘ᶜ ∙ M₂.𝟘 M₂.· tr p ∙ M₂.𝟘 M₂.· tr q  ≈⟨ ≈ᶜ-refl ∙ M₂.·-zeroˡ _ ∙ M₂.·-zeroˡ _ ⟩
            C₂.𝟘ᶜ                                    ∎)
        )
        (λ _ →
             tr-Conₘ γ
           , sub (tr-▸ ▸t) (begin
               tr-Conₘ γ ∙ M₂.𝟙 M₂.· tr p ∙ M₂.𝟙 M₂.· tr q      ≈⟨ ≈ᶜ-refl ∙ M₂.·-identityˡ _ ∙ M₂.·-identityˡ _ ⟩
               tr-Conₘ γ ∙ tr p ∙ tr q                          ≈˘⟨ ≈ᶜ-refl ∙ cong tr (M₁.·-identityˡ _) ∙ cong tr (M₁.·-identityˡ _) ⟩
               tr-Conₘ γ ∙ tr (M₁.𝟙 M₁.· p) ∙ tr (M₁.𝟙 M₁.· q)  ∎))
        where
        open CR₂

  opaque

    -- Preservation of ▸[_] (if transparent is false).

    tr-▸-DCon :
      ¬ T transparent →
      U₁.▸[ m ] ∇ → U₂.▸[ tr-Mode m ] tr-DCon ∇
    tr-▸-DCon ok ▸∇ α∈ with tr-↦∷⁻¹ ok α∈
    … | _ , _ , eq , _ , α∈∇ =
      PE.subst (U₂._▸[_]_ _ _) (sym eq) (tr-▸ (▸∇ α∈∇))

------------------------------------------------------------------------
-- If certain properties hold after translation by order embeddings
-- that satisfy certain properties, then they hold also before
-- translation

module Is-order-embedding
  (tr-emb   : Is-order-embedding 𝕄₁ 𝕄₂ tr)
  (tr-Σ-emb : Is-Σ-order-embedding 𝕄₁ 𝕄₂ tr tr-Σ)
  (embc     : Is-Σ-order-embedding-C trp C₁ C₂ tr tr-Σ)
  (mr       : Are-mode-respecting-morphisms v₁ v₂ tr tr-Σ)
  where

  open Is-Σ-order-embedding-C embc
  open Are-mode-respecting-morphisms mr
  open CQ.Is-order-embedding tr-emb
  open CQ.Is-Σ-order-embedding tr-Σ-emb
  open M.Is-order-embedding tr-emb
  open M.Is-Σ-order-embedding tr-Σ-emb
  open MQ.Is-order-embedding tr-emb tr-Σ-morphism mr

  opaque

    -- A variant of tr-Conₘ-≤ᶜ-·ᶜ and tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ for tr-BinderMode

    tr-Conₘ-≤ᶜ-tr-BinderMode-·ᶜ :
      ∀ {b} → tr-Conₘ γ C₂.≤ᶜ tr-BinderMode b p C₂.·ᶜ δ →
        ∃ λ δ′ → tr-Conₘ δ′ C₂.≤ᶜ δ × γ C₁.≤ᶜ p C₁.·ᶜ δ′
    tr-Conₘ-≤ᶜ-tr-BinderMode-·ᶜ {b = BMΠ}   = tr-Conₘ-≤ᶜ-·ᶜ
    tr-Conₘ-≤ᶜ-tr-BinderMode-·ᶜ {b = BMΣ s} = tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ

  -- Preservation of _◂_∈_.

  tr-◂∈⁻¹ : x U₂.◂ tr p ∈ tr-Conₘ γ → x U₁.◂ p ∈ γ
  tr-◂∈⁻¹ = λ x → tr-◂∈⁻¹′ x refl
    where
    tr-◂∈⁻¹′ : x U₂.◂ p′ ∈ tr-Conₘ γ → p′ ≡ tr p → x U₁.◂ p ∈ γ
    tr-◂∈⁻¹′ {γ = ε}     ()
    tr-◂∈⁻¹′ {γ = _ ∙ _} (there x) refl = there (tr-◂∈⁻¹ x)
    tr-◂∈⁻¹′ {γ = _ ∙ _} here      eq   =
      PE.subst (_ U₁.◂_∈ _) (tr-injective eq) here

  opaque

    -- Preservation of Usage-restrictions-satisfied for terms which,
    -- if the source modality is trivial, satisfy No-[]-cong-Quot.

    Usage-restrictions-satisfied-tr-Term :
      (M₁.Trivial → No-[]-cong-Quot t) →
      m₁ ≳ᵐ m₂ →
      RS₂.Usage-restrictions-satisfied m₂ (tr-Term t) →
      RS₁.Usage-restrictions-satisfied m₁ t
    Usage-restrictions-satisfied-tr-Term {t} = λ ok m₁≳m₂ →
      lemma m₁≳m₂ _ (No-[]-cong-Quot′⇔ t .proj₂ ok)
      where
      lemma :
        m₁ ≳ᵐ m₂ →
        (t : Term[_] M₁ k n) →
        No-[]-cong-Quot′ M₁.Trivial t →
        RS₂.Usage-restrictions-satisfied m₂ (tr-Term t) →
        RS₁.Usage-restrictions-satisfied m₁ t

      lemma-𝟘ᵐ?-𝟘ᵐ? :
        {t : Term[_] M₁ k n} →
        No-[]-cong-Quot′ M₁.Trivial t →
        RS₂.Usage-restrictions-satisfied Mo₂.𝟘ᵐ? (tr-Term t) →
        RS₁.Usage-restrictions-satisfied Mo₁.𝟘ᵐ? t
      lemma-𝟘ᵐ?-𝟘ᵐ? {t} ok = Mo₁.𝟘ᵐ?-elim
        (λ m →
           RS₂.Usage-restrictions-satisfied Mo₂.𝟘ᵐ? (tr-Term t) →
           RS₁.Usage-restrictions-satisfied m t)
        (λ ⦃ ok = ok₁ ⦄ →
           Mo₂.𝟘ᵐ?-elim
             (λ m →
                RS₂.Usage-restrictions-satisfied m (tr-Term t) →
                RS₁.Usage-restrictions-satisfied 𝟘ᵐ t)
             (lemma [ 𝟘ᵐ ] _ ok)
             (λ not-ok₂ →
                ⊥-elim $ not-ok₂ (𝟘ᵐ-in-second-if-in-first ok₁)))
        (λ not-ok₁ →
           Mo₂.𝟘ᵐ?-elim
             (λ m →
                RS₂.Usage-restrictions-satisfied m (tr-Term t) →
                RS₁.Usage-restrictions-satisfied 𝟙ᵐ t)
             (λ ⦃ ok = ok₂ ⦄ →
                lemma (𝟙ᵐ≳𝟘ᵐ (trivial not-ok₁ ok₂)) _ ok)
             (λ _ → lemma [ 𝟙ᵐ ] _ ok))

      lemma-𝟘ᵐ? :
        {t : Term[_] M₁ k n} →
        _≳ᵐ_ {v₁ = v₁} {v₂ = v₂} 𝟙ᵐ 𝟘ᵐ[ ok₂ ] →
        No-[]-cong-Quot′ M₁.Trivial t →
        RS₂.Usage-restrictions-satisfied Mo₂.𝟘ᵐ? (tr-Term t) →
        RS₁.Usage-restrictions-satisfied m t
      lemma-𝟘ᵐ? 𝟙≳𝟘 ok =
        RS₁.Usage-restrictions-satisfied-𝟙ᵐ→ ∘→
        lemma (subst (_ ≳ᵐ_) (sym Mo₂.𝟘ᵐ?≡𝟘ᵐ) 𝟙≳𝟘) _ ok

      lemma {m₁} m₁≳m₂ = λ where
        (var _) _ varᵤ →
          RS₁.varᵤ
        (defn _) _ defnᵤ →
          RS₁.defnᵤ
        Level _ Levelᵤ →
          RS₁.Levelᵤ
        zeroᵘ _ zeroᵘᵤ →
          RS₁.zeroᵘᵤ
        (sucᵘ _) ok (sucᵘᵤ t) →
          RS₁.sucᵘᵤ (lemma m₁≳m₂ _ ok t)
        (_ supᵘ _) (t-ok , u-ok) (supᵘᵤ t u) →
          RS₁.supᵘᵤ (lemma m₁≳m₂ _ t-ok t) (lemma m₁≳m₂ _ u-ok u)
        (ωᵘ+ _) _ ωᵘ+ →
          RS₁.ωᵘ+
        (level _) ok (level t) →
          RS₁.level (lemma m₁≳m₂ _ ok t)
        (Lift _ _) (t-ok , A-ok) (Liftᵤ t A) →
          RS₁.Liftᵤ (lemma-𝟘ᵐ?-𝟘ᵐ? t-ok t) (lemma m₁≳m₂ _ A-ok A)
        (lift _) ok (liftᵤ t) →
          RS₁.liftᵤ (lemma m₁≳m₂ _ ok t)
        (lower _) ok (lowerᵤ t) →
          RS₁.lowerᵤ (lemma m₁≳m₂ _ ok t)
        Empty _ Emptyᵤ →
          RS₁.Emptyᵤ
        (emptyrec _ _ _) (A-ok , t-ok) (emptyrecᵤ ok A t) →
          RS₁.emptyrecᵤ (Emptyrec-reflected m₁≳m₂ ok)
            (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A) (lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ t-ok t)
        (Unit _) _ Unitᵤ →
          RS₁.Unitᵤ
        (star _) _ starᵤ →
          RS₁.starᵤ
        (unitrec _ _ _ _ _) (A-ok , t-ok , u-ok) (unitrecᵤ ok A t u) →
          RS₁.unitrecᵤ (Unitrec-reflected m₁≳m₂ ok)
            (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A) (lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ t-ok t)
            (lemma m₁≳m₂ _ u-ok u)
        (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) (A-ok , B-ok) (ΠΣᵤ A B) →
          RS₁.ΠΣᵤ (lemma (ᵐ·≳ᵐᵐ·-BinderMode m₁≳m₂) _ A-ok A)
            (lemma m₁≳m₂ _ B-ok B)
        (lam _ _) ok (lamᵤ t) →
          RS₁.lamᵤ (lemma m₁≳m₂ _ ok t)
        (_ ∘⟨ _ ⟩ _) (t-ok , u-ok) (∘ᵤ t u) →
          RS₁.∘ᵤ (lemma m₁≳m₂ _ t-ok t) (lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ u-ok u)
        (prod _ _ _ _) (t-ok , u-ok) (prodᵤ t u) →
          RS₁.prodᵤ (lemma (ᵐ·≳ᵐᵐ·-Σ m₁≳m₂) _ t-ok t)
            (lemma m₁≳m₂ _ u-ok u)
        (prodrec _ _ _ _ _ _) (A-ok , t-ok , u-ok)
          (prodrecᵤ ok₂ A t u) →
          RS₁.prodrecᵤ (Prodrec-reflected m₁≳m₂ ok₂)
            (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A) (lemma (ᵐ·≳ᵐᵐ· m₁≳m₂) _ t-ok t)
            (lemma m₁≳m₂ _ u-ok u)
        (fst _ _) ok (fstᵤ t) →
          RS₁.fstᵤ (lemma m₁≳m₂ _ ok t)
        (snd _ _) ok (sndᵤ t) →
          RS₁.sndᵤ (lemma m₁≳m₂ _ ok t)
        ℕ _ ℕᵤ →
          RS₁.ℕᵤ
        zero _ zeroᵤ →
          RS₁.zeroᵤ
        (suc _) ok (sucᵤ t) →
          RS₁.sucᵤ (lemma m₁≳m₂ _ ok t)
        (natrec _ _ _ _ _ _ _) (A-ok , t-ok , u-ok , v-ok)
          (natrecᵤ x A t u v) →
          let open Graded.Modality.Morphism.Forward-instances common-properties
          in  RS₁.natrecᵤ
                (M.Is-no-nr-glb-reflecting-morphism.tr-nrᵢ-glb no-nr-glb-reflected (x .proj₂))
                (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A) (lemma m₁≳m₂ _ t-ok t)
                (lemma m₁≳m₂ _ u-ok u) (lemma m₁≳m₂ _ v-ok v)
        (U _) ok (Uᵤ t) →
          RS₁.Uᵤ (lemma-𝟘ᵐ?-𝟘ᵐ? ok t)
        (Id _ _ _) (A-ok , t-ok , u-ok) (Idᵤ not-erased A t u) →
          RS₁.Idᵤ (not-erased ∘→ Id-erased-preserved .proj₁)
            (lemma m₁≳m₂ _ A-ok A) (lemma m₁≳m₂ _ t-ok t)
            (lemma m₁≳m₂ _ u-ok u)
        (Id _ _ _) (A-ok , t-ok , u-ok) (Id₀ᵤ erased A t u) →
          RS₁.Id₀ᵤ (Id-erased-preserved .proj₂ erased)
            (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A) (lemma-𝟘ᵐ?-𝟘ᵐ? t-ok t)
            (lemma-𝟘ᵐ?-𝟘ᵐ? u-ok u)
        rfl _ rflᵤ →
          RS₁.rflᵤ
        (J _ _ _ _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok , w-ok)
          (Jᵤ _ A t B u v w) →
          RS₁.Jᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A)
            (lemma m₁≳m₂ _ t-ok t) (lemma m₁≳m₂ _ B-ok B)
            (lemma m₁≳m₂ _ u-ok u) (lemma m₁≳m₂ _ v-ok v)
            (lemma m₁≳m₂ _ w-ok w)
        (J _ _ _ _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok , w-ok)
          (J₀ᵤ₁ ⦃ (≡some) ⦄ tr-p≡𝟘 tr-q≡𝟘 A t B u v w) →
          subst (RS₁.Usage-restrictions-satisfied _)
            (sym $
             case trivial-⊎-tr-≡-𝟘-⇔ of λ where
               (inj₁ trivial₁) →
                 cong₂ (λ p q → J p q _ _ _ _ _ _)
                   (MP₁.≡-trivial trivial₁)
                   (MP₁.≡-trivial trivial₁)
               (inj₂ tr-≡-𝟘-⇔) →
                 cong₂ (λ p q → J p q _ _ _ _ _ _)
                   (tr-≡-𝟘-⇔ .proj₁ tr-p≡𝟘)
                   (tr-≡-𝟘-⇔ .proj₁ tr-q≡𝟘)) $
          case m₁≳m₂ of λ where
            [ m₁≈m₂ ] →
              case singleton $ Co₁.erased-matches-for-J m₁ of λ where
                (none , ≡none) →
                  case
                    PE.trans (PE.sym ≡some)
                      (≤ᵉᵐ→≡none→≡none
                         (erased-matches-for-J-reflected m₁≈m₂) ≡none)
                  of λ ()
                (not-none _ , ≡not-none) →
                  RS₁.J₀ᵤ₁-generalised ≡not-none refl refl
                    (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A) (lemma-𝟘ᵐ?-𝟘ᵐ? t-ok t)
                    (lemma m₁≳m₂ _ B-ok B) (lemma m₁≳m₂ _ u-ok u)
                    (lemma-𝟘ᵐ?-𝟘ᵐ? v-ok v) (lemma-𝟘ᵐ?-𝟘ᵐ? w-ok w)
            (𝟙ᵐ≳𝟘ᵐ _) →
              RS₁.Jᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A)
                (lemma-𝟘ᵐ? m₁≳m₂ t-ok t) (lemma m₁≳m₂ _ B-ok B)
                (lemma m₁≳m₂ _ u-ok u) (lemma-𝟘ᵐ? m₁≳m₂ v-ok v)
                (lemma-𝟘ᵐ? m₁≳m₂ w-ok w)
        (J _ _ _ _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok , w-ok)
          (J₀ᵤ₂ ⦃ (≡all) ⦄ A t B u v w) →
          case m₁≳m₂ of λ where
            [ m₁≈m₂ ] →
              RS₁.J₀ᵤ₂
                ⦃ ≤ᵉᵐ→≡all→≡all (erased-matches-for-J-reflected m₁≈m₂)
                   ≡all ⦄
                (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A) (lemma-𝟘ᵐ?-𝟘ᵐ? t-ok t)
                (lemma-𝟘ᵐ?-𝟘ᵐ? B-ok B) (lemma m₁≳m₂ _ u-ok u)
                (lemma-𝟘ᵐ?-𝟘ᵐ? v-ok v) (lemma-𝟘ᵐ?-𝟘ᵐ? w-ok w)
            (𝟙ᵐ≳𝟘ᵐ _) →
              RS₁.Jᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A)
                (lemma-𝟘ᵐ? m₁≳m₂ t-ok t) (lemma-𝟘ᵐ? m₁≳m₂ B-ok B)
                (lemma m₁≳m₂ _ u-ok u) (lemma-𝟘ᵐ? m₁≳m₂ v-ok v)
                (lemma-𝟘ᵐ? m₁≳m₂ w-ok w)
        (K _ _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok)
          (Kᵤ _ A t B u v) →
          RS₁.Kᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A)
            (lemma m₁≳m₂ _ t-ok t) (lemma m₁≳m₂ _ B-ok B)
            (lemma m₁≳m₂ _ u-ok u) (lemma m₁≳m₂ _ v-ok v)
        (K _ _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok)
          (K₀ᵤ₁ ⦃ (≡some) ⦄ tr-p≡𝟘 A t B u v) →
          case m₁≳m₂ of λ where
            [ m₁≈m₂ ] →
              case singleton $ Co₁.erased-matches-for-K m₁ of λ where
                (none , ≡none) →
                  case
                    PE.trans (PE.sym ≡some)
                      (≤ᵉᵐ→≡none→≡none
                         (erased-matches-for-K-reflected m₁≈m₂) ≡none)
                  of λ ()
                (not-none _ , ≡not-none) →
                  RS₁.K₀ᵤ₁-generalised ≡not-none
                    (case trivial-⊎-tr-≡-𝟘-⇔ of λ where
                       (inj₁ trivial₁) → MP₁.≡-trivial trivial₁
                       (inj₂ tr-≡-𝟘-⇔) → tr-≡-𝟘-⇔ .proj₁ tr-p≡𝟘)
                    (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A) (lemma-𝟘ᵐ?-𝟘ᵐ? t-ok t)
                    (lemma m₁≳m₂ _ B-ok B) (lemma m₁≳m₂ _ u-ok u)
                    (lemma-𝟘ᵐ?-𝟘ᵐ? v-ok v)
            (𝟙ᵐ≳𝟘ᵐ _) →
              RS₁.Kᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A)
                (lemma-𝟘ᵐ? m₁≳m₂ t-ok t) (lemma m₁≳m₂ _ B-ok B)
                (lemma m₁≳m₂ _ u-ok u) (lemma-𝟘ᵐ? m₁≳m₂ v-ok v)
        (K _ _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok)
          (K₀ᵤ₂ ⦃ (≡all) ⦄ A t B u v) →
          case m₁≳m₂ of λ where
            [ m₁≈m₂ ] →
              RS₁.K₀ᵤ₂
                ⦃ ≤ᵉᵐ→≡all→≡all (erased-matches-for-K-reflected m₁≈m₂)
                   ≡all ⦄
                (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A) (lemma-𝟘ᵐ?-𝟘ᵐ? t-ok t)
                (lemma-𝟘ᵐ?-𝟘ᵐ? B-ok B) (lemma m₁≳m₂ _ u-ok u)
                (lemma-𝟘ᵐ?-𝟘ᵐ? v-ok v)
            (𝟙ᵐ≳𝟘ᵐ _) →
              RS₁.Kᵤ-generalised (lemma-𝟘ᵐ?-𝟘ᵐ? A-ok A)
                (lemma-𝟘ᵐ? m₁≳m₂ t-ok t) (lemma-𝟘ᵐ? m₁≳m₂ B-ok B)
                (lemma m₁≳m₂ _ u-ok u) (lemma-𝟘ᵐ? m₁≳m₂ v-ok v)
        ([]-cong _ l A t u v) ok ([]-congᵤ ok′ l′ A′ t′ u′ v′) →
          case []-cong-mode-reflected′ m₁≳m₂ ok′ of λ where
            (inj₂ triv)        → ⊥-elim (ok triv)
            (inj₁ (ok′ , not)) →
              RS₁.[]-congᵤ ok′
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not l) l′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not A) A′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not t) t′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not u) u′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not v) v′)
        (Quot A B) ok (Quot ok′ A′ B′) →
          case Quot-reflected′ ok′ of λ where
            (inj₂ triv)        → ⊥-elim (ok triv)
            (inj₁ (ok′ , not)) →
              RS₁.Quot ok′
                (lemma m₁≳m₂ _ (¬→No-[]-cong-Quot′ not A) A′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not B) B′)
        (class t) ok (class ok′ t′) →
          case Quot-reflected′ ok′ of λ where
            (inj₂ triv)        → ⊥-elim (ok triv)
            (inj₁ (ok′ , not)) →
              RS₁.class ok′
                (lemma m₁≳m₂ _ (¬→No-[]-cong-Quot′ not t) t′)
        (resp A B t u v) ok (resp ok′ A′ B′ t′ u′ v′ eq) →
          case Quot-reflected′ ok′ of λ where
            (inj₂ triv)        → ⊥-elim (ok triv)
            (inj₁ (ok′ , not)) →
              RS₁.resp ok′
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not A) A′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not B) B′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not t) t′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not u) u′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not v) v′)
                (≳ᵐ→≡𝟘ᵐ?→≡𝟘ᵐ? m₁≳m₂ eq)
        (set A B t u v w) ok (set ok′ A′ B′ t′ u′ v′ w′ eq) →
          case Quot-reflected′ ok′ of λ where
            (inj₂ triv)        → ⊥-elim (ok triv)
            (inj₁ (ok′ , not)) →
              RS₁.set ok′
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not A) A′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not B) B′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not t) t′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not u) u′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not v) v′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not w) w′)
                (≳ᵐ→≡𝟘ᵐ?→≡𝟘ᵐ? m₁≳m₂ eq)
        (qrec C t u v w) ok (qrec₀ ok₁ ok₂ C′ t′ u′ v′ w′) →
          let open Graded.Modality.Morphism.Backward-instances common-properties in
          case Quot-reflected′ ok₁ of λ where
            (inj₂ triv)        → ⊥-elim (ok triv)
            (inj₁ (ok₁ , not)) →
              RS₁.qrec₀ ok₁ (Qrec-motive-erased-preserved .proj₂ ok₂)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not C) C′)
                (lemma m₁≳m₂ _ (¬→No-[]-cong-Quot′ not t) t′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not u) u′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not v) v′)
                (lemma m₁≳m₂ _ (¬→No-[]-cong-Quot′ not w) w′)
        (qrec C t u v w) ok (qrec₁ ok₁ ok₂ C′ t′ u′ v′ w′) →
          let open Graded.Modality.Morphism.Backward-instances common-properties in
          case Quot-reflected′ ok₁ of λ where
            (inj₂ triv)        → ⊥-elim (ok triv)
            (inj₁ (ok₁ , not)) →
              RS₁.qrec₁ ok₁ (ok₂ ∘→ Qrec-motive-erased-preserved .proj₁)
                (lemma m₁≳m₂ _ (¬→No-[]-cong-Quot′ not C) C′)
                (lemma m₁≳m₂ _ (¬→No-[]-cong-Quot′ not t) t′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not u) u′)
                (lemma-𝟘ᵐ?-𝟘ᵐ? (¬→No-[]-cong-Quot′ not v) v′)
                (lemma m₁≳m₂ _ (¬→No-[]-cong-Quot′ not w) w′)

  -- Preservation of _▸[_]_ for trivial source modalities and terms
  -- satisfying No-[]-cong-Quot.

  tr-▸⁻¹-trivial :
    No-[]-cong-Quot t →
    M₁.Trivial → γ U₂.▸[ m ] tr-Term t → C₁.𝟘ᶜ U₁.▸[ 𝟙ᵐ ] t
  tr-▸⁻¹-trivial {t} {γ} {m} ok 𝟙≡𝟘 =
    γ U₂.▸[ m ] tr-Term t                       →⟨ ▸→Usage-restrictions-satisfied ⟩
    Usage-restrictions-satisfied m (tr-Term t)  →⟨ Usage-restrictions-satisfied-tr-Term (λ _ → ok) (𝟙ᵐ≳ᵐ m) ⟩
    RS₁.Usage-restrictions-satisfied 𝟙ᵐ t       →⟨ RS₁.Trivial→▸⇔ 𝟙≡𝟘 .proj₂ ⟩
    C₁.𝟘ᶜ U₁.▸[ 𝟙ᵐ ] t                          □
    where
    𝟙ᵐ≳ᵐ : (m : Mo₂.Mode) → Mo₁.𝟙ᵐ ≳ᵐ m
    𝟙ᵐ≳ᵐ 𝟙ᵐ = [ 𝟙ᵐ ]
    𝟙ᵐ≳ᵐ 𝟘ᵐ = 𝟙ᵐ≳𝟘ᵐ 𝟙≡𝟘

  -- Preservation of _▸[_]_ for terms which, if the source modality is
  -- trivial, satisfy No-[]-cong-Quot.

  tr-▸⁻¹ :
    (M₁.Trivial → No-[]-cong-Quot t) →
    tr-Conₘ γ U₂.▸[ tr-Mode m ] tr-Term t → γ U₁.▸[ m ] t
  tr-▸⁻¹ {t} = λ ok ▸t →
    tr-▸⁻¹′ _ (No-[]-cong-Quot′⇔ t .proj₂ ok) ▸t refl CP₂.≤ᶜ-refl
    where mutual
    tr-▸⁻¹′ :
      (t : Term[_] M₁ k n) →
      No-[]-cong-Quot′ M₁.Trivial t →
      γ′ U₂.▸[ m′ ] tr-Term t →
      m′ ≡ tr-Mode m → tr-Conₘ γ C₂.≤ᶜ γ′ → γ U₁.▸[ m ] t
    tr-▸⁻¹′ (defn _) _ defn refl ≤𝟘 =
      sub defn (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ Level _ Levelₘ refl ≤𝟘 =
      sub Levelₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ zeroᵘ _ zeroᵘₘ refl ≤𝟘 =
      sub zeroᵘₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ (sucᵘ _) ok (sucᵘₘ ▸t) refl ≤γ =
      sucᵘₘ (tr-▸⁻¹′ _ ok ▸t refl ≤γ)

    tr-▸⁻¹′ (_ supᵘ _) (t-ok , u-ok) (supᵘₘ ▸t ▸u) refl ≤γ =
      case tr-Conₘ-≤ᶜ-+ᶜ ≤γ of λ (δ′ , η′ , ≤₁ , ≤₂ , γ≤) →
        sub
          (supᵘₘ (tr-▸⁻¹′ _ t-ok ▸t refl ≤₁)
             (tr-▸⁻¹′ _ u-ok ▸u refl ≤₂))
          γ≤

    tr-▸⁻¹′ (ωᵘ+ _) _ ωᵘ+ refl ≤𝟘 =
      sub ωᵘ+ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ (level _) ok (level ▸t) refl ≤γ =
      level (tr-▸⁻¹′ _ ok ▸t refl ≤γ)

    tr-▸⁻¹′ (Lift _ _) (t-ok , A-ok) (Liftₘ ▸t ▸A) refl ≤γ =
      Liftₘ (tr-▸[𝟘ᵐ?]⁻¹ t-ok ▸t .proj₂) (tr-▸⁻¹′ _ A-ok ▸A refl ≤γ)

    tr-▸⁻¹′ (lift _) ok (liftₘ ▸t) refl ≤γ =
      liftₘ (tr-▸⁻¹′ _ ok ▸t refl ≤γ)

    tr-▸⁻¹′ (lower _) ok (lowerₘ ▸t) refl ≤γ =
      lowerₘ (tr-▸⁻¹′ _ ok ▸t refl ≤γ)

    tr-▸⁻¹′ {γ = γ} (U _) ok (Uₘ ▸t) refl ≤𝟘 = sub
      (Uₘ (tr-▸[𝟘ᵐ?]⁻¹ ok ▸t .proj₂))
      (begin
         γ      ≤⟨ tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘 ⟩
         C₁.𝟘ᶜ  ∎)
      where
      open CR₁

    tr-▸⁻¹′ Unit! _ Unitₘ refl ≤𝟘 =
      sub Unitₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ starʷ _ starʷₘ refl ≤𝟘 =
      sub starʷₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ Empty _ Emptyₘ refl ≤𝟘 =
      sub Emptyₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ ℕ _ ℕₘ refl ≤𝟘 =
      sub ℕₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ zero _ zeroₘ refl ≤𝟘 =
      sub zeroₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ (suc _) ok (sucₘ ▸t) refl ≤γ′ =
      sucₘ (tr-▸⁻¹′ _ ok ▸t refl ≤γ′)

    tr-▸⁻¹′ (snd _ _) ok (sndₘ ▸t) refl ≤γ′ =
      sndₘ (tr-▸⁻¹′ _ ok ▸t refl ≤γ′)

    tr-▸⁻¹′ {m} {γ} starˢ _ (starˢₘ {γ = δ} prop) refl ≤mδ =
      case lemma″ starˢ-sink-preserved prop of λ (_ , prop′ , γ≤) →
        sub (starˢₘ prop′) γ≤
      where
      open CR₂
      lemma′ : ∀ m → tr-Conₘ γ C₂.≤ᶜ Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ δ →
               ∃ λ η → γ C₁.≤ᶜ Mo₁.⌜ m ⌝ C₁.·ᶜ η
      lemma′ 𝟘ᵐ ≤𝟘 = C₁.𝟘ᶜ ,
        (case trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ of λ where
          (inj₁ trivial) → trivial
          (inj₂ tr-Conₘ-𝟘ᶜ-≈ᶜ) → tr-Conₘ-order-reflecting (begin
            tr-Conₘ γ ≤⟨ ≤𝟘 ⟩
            Mo₂.⌜ tr-Mode Mo₁.𝟘ᵐ ⌝ C₂.·ᶜ δ    ≈⟨ CP₂.·ᶜ-zeroˡ δ ⟩
            C₂.𝟘ᶜ                             ≈˘⟨ tr-Conₘ-𝟘ᶜ-≈ᶜ ⟩
            tr-Conₘ C₁.𝟘ᶜ                     ≈˘⟨ CQ.tr-≈ᶜ (CP₁.·ᶜ-zeroˡ _) ⟩
            tr-Conₘ (Mo₁.⌜ Mo₁.𝟘ᵐ ⌝ C₁.·ᶜ _)  ∎))
      lemma′ 𝟙ᵐ ≤δ = γ ,
        tr-Conₘ-order-reflecting (begin
          tr-Conₘ γ                         ≈˘⟨ CQ.tr-≈ᶜ (CP₁.·ᶜ-identityˡ γ) ⟩
          tr-Conₘ (Mo₁.⌜ Mo₁.𝟙ᵐ ⌝ C₁.·ᶜ γ)  ∎)

      lemma″ :
        ∀ {b b′} → b′ ≡ b →
        (¬ T b → C₂.𝟘ᶜ C₂.≈ᶜ δ) →
          ∃ λ η → (¬ T b′ → C₁.𝟘ᶜ C₁.≈ᶜ η) × γ C₁.≤ᶜ Mo₁.⌜ m ⌝ C₁.·ᶜ η
      lemma″ {(false)} refl prop =
        _ , (λ _ → CP₁.≈ᶜ-refl) ,
        (case trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ of λ where
          (inj₁ trivial) → trivial
          (inj₂ tr-Conₘ-𝟘ᶜ-≈ᶜ) → tr-Conₘ-order-reflecting (begin
            tr-Conₘ γ                         ≤⟨ ≤mδ ⟩
            Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ δ         ≈˘⟨ CP₂.·ᶜ-congˡ (prop idᶠ) ⟩
            Mo₂.⌜ tr-Mode m ⌝ C₂.·ᶜ C₂.𝟘ᶜ     ≈⟨ CP₂.·ᶜ-zeroʳ _ ⟩
            C₂.𝟘ᶜ                             ≈˘⟨ CP₂.·ᶜ-zeroʳ _ ⟩
            tr Mo₁.⌜ m ⌝ C₂.·ᶜ C₂.𝟘ᶜ          ≈˘⟨ CP₂.·ᶜ-congˡ tr-Conₘ-𝟘ᶜ-≈ᶜ ⟩
            tr Mo₁.⌜ m ⌝ C₂.·ᶜ tr-Conₘ C₁.𝟘ᶜ  ≈˘⟨ tr-Conₘ-·ᶜ ⟩
            tr-Conₘ (Mo₁.⌜ m ⌝ C₁.·ᶜ C₁.𝟘ᶜ)   ∎))
      lemma″ {(true)} refl _ = case lemma′ m ≤mδ of λ (_ , γ≤) →
        _ , ⊥-elim ∘→ (_$ _) , γ≤

    tr-▸⁻¹′ {m} {γ} (var x) _ var refl ≤𝟘,x≔⌜tr-m⌝ = sub
      var
      (case trivial-⊎-tr-Conₘ-𝟘ᶜ-≈ᶜ of λ where
         (inj₁ trivial)   → trivial
         (inj₂ tr-Conₘ-𝟘) → begin
            γ                          ≡˘⟨ CP₁.update-self _ _ ⟩
            γ     C₁., x ≔ γ C₁.⟨ x ⟩  ≤⟨ CP₁.update-monotoneʳ _ (tr-≤-⌜tr-Mode⌝ m lemma₁) ⟩
            γ     C₁., x ≔ Mo₁.⌜ m ⌝   ≤⟨ tr-Conₘ-order-reflecting (lemma₂ tr-Conₘ-𝟘) ⟩
            C₁.𝟘ᶜ C₁., x ≔ Mo₁.⌜ m ⌝   ∎)
      where
      lemma₁ = begin
        tr (γ C₁.⟨ x ⟩)                              ≡⟨ CQ.tr-⟨⟩ γ ⟩
        tr-Conₘ γ C₂.⟨ x ⟩                           ≤⟨ CP₂.lookup-monotone _ ≤𝟘,x≔⌜tr-m⌝ ⟩
        (C₂.𝟘ᶜ C₂., x ≔ Mo₂.⌜ tr-Mode m ⌝) C₂.⟨ x ⟩  ≡⟨ CP₂.update-lookup C₂.𝟘ᶜ x ⟩
        Mo₂.⌜ tr-Mode m ⌝                            ∎
        where
        open R₂

      lemma₂ = λ tr-Conₘ-𝟘 → begin
        tr-Conₘ (γ C₁., x ≔ Mo₁.⌜ m ⌝)                            ≡⟨ CQ.tr-,≔ ⟩
        tr-Conₘ γ C₂., x ≔ tr Mo₁.⌜ m ⌝                           ≤⟨ CP₂.update-monotoneˡ _ ≤𝟘,x≔⌜tr-m⌝ ⟩
        (C₂.𝟘ᶜ C₂., x ≔ Mo₂.⌜ tr-Mode m ⌝) C₂., x ≔ tr Mo₁.⌜ m ⌝  ≡⟨ CP₂.update-twice ⟩
        C₂.𝟘ᶜ C₂., x ≔ tr Mo₁.⌜ m ⌝                               ≈˘⟨ CP₂.update-congˡ tr-Conₘ-𝟘 ⟩
        tr-Conₘ C₁.𝟘ᶜ C₂., x ≔ tr Mo₁.⌜ m ⌝                       ≡˘⟨ CQ.tr-,≔ ⟩
        tr-Conₘ (C₁.𝟘ᶜ C₁., x ≔ Mo₁.⌜ m ⌝)                        ∎
        where
        open CR₂

      open CR₁

    tr-▸⁻¹′ {m} (lam _ _) ok (lamₘ ▸t) refl ≤γ′ = lamₘ
      (tr-▸⁻¹′ _ ok ▸t refl (≤γ′ ∙ ≤-reflexive (sym (tr-⌜⌝-· m))))

    tr-▸⁻¹′
      {m} {γ} (_ ∘⟨ p ⟩ _) (t-ok , u-ok)
      (_∘ₘ_ {γ = δ} {δ = η} ▸t ▸u) refl ≤γ′ =
      case tr-Conₘ-≤ᶜ-+ᶜ ≤γ′ of λ (δ′ , η′ , ≤δ , ≤pη , γ≤) →
      case tr-Conₘ-≤ᶜ-·ᶜ ≤pη of λ (η″ , ≤η , η′≤) →
      sub
        (tr-▸⁻¹′ _ t-ok ▸t refl ≤δ ∘ₘ
         tr-▸⁻¹′ _ u-ok ▸u (sym (tr-Mode-ᵐ· m BMΠ)) ≤η)
        (begin
           γ                    ≤⟨ γ≤ ⟩
           δ′ C₁.+ᶜ η′          ≤⟨ CP₁.+ᶜ-monotoneʳ η′≤ ⟩
           δ′ C₁.+ᶜ p C₁.·ᶜ η″  ∎)
      where
      open CR₁

    tr-▸⁻¹′
      {m} (ΠΣ⟨ b ⟩ _ , q ▷ _ ▹ _) (A-ok , P-ok)
      (ΠΣₘ {δ = η} ▸A ▸P) refl ≤γ′ =
      case tr-Conₘ-≤ᶜ-+ᶜ ≤γ′ of λ (δ′ , η′ , ≤pδ , ≤η , γ≤) →
      case tr-Conₘ-≤ᶜ-tr-BinderMode-·ᶜ ≤pδ of λ (δ″ , ≤δ , δ′≤) →
      sub
        (ΠΣₘ (tr-▸⁻¹′ _ A-ok ▸A (sym (tr-Mode-ᵐ· m b)) ≤δ)
           (tr-▸⁻¹′ _ P-ok ▸P refl (begin
              tr-Conₘ η′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· q)  ≤⟨ ≤η ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
              η C₂.∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q  ∎)))
        (CP₁.≤ᶜ-trans γ≤ (CP₁.+ᶜ-monotoneˡ δ′≤))
      where
      open CR₂

    tr-▸⁻¹′
      {m} {γ} (prodʷ p _ _) (t-ok , u-ok)
      (prodʷₘ {γ = δ} {δ = η} ▸t ▸u) refl ≤γ′ =
      case tr-Conₘ-≤ᶜ-+ᶜ ≤γ′ of λ (δ′ , η′ , ≤pδ , ≤η , γ≤) →
      case tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ ≤pδ of λ (δ″ , ≤δ , δ′≤) →
      sub
        (prodʷₘ (tr-▸⁻¹′ _ t-ok ▸t (sym (tr-Mode-ᵐ· m (BMΣ 𝕨))) ≤δ)
           (tr-▸⁻¹′ _ u-ok ▸u refl ≤η))
        (begin
           γ                    ≤⟨ γ≤ ⟩
           δ′ C₁.+ᶜ η′          ≤⟨ CP₁.+ᶜ-monotoneˡ δ′≤ ⟩
           p C₁.·ᶜ δ″ C₁.+ᶜ η′  ∎)
      where
      open CR₁

    tr-▸⁻¹′
      {m} {γ} (prodˢ p _ _) (t-ok , u-ok)
      (prodˢₘ {γ = δ} {δ = η} ▸t ▸u) refl ≤γ′ =
      case tr-Conₘ-≤ᶜ-∧ᶜ ≤γ′ of λ (δ′ , η′ , ≤pδ , ≤η , γ≤) →
      case tr-Conₘ-≤ᶜ-tr-Σ-·ᶜ ≤pδ of λ (δ″ , ≤δ , δ′≤) →
      sub
        (prodˢₘ (tr-▸⁻¹′ _ t-ok ▸t (sym (tr-Mode-ᵐ· m (BMΣ 𝕤))) ≤δ)
           (tr-▸⁻¹′ _ u-ok ▸u refl ≤η))
        (begin
           γ                    ≤⟨ γ≤ ⟩
           δ′ C₁.∧ᶜ η′          ≤⟨ CP₁.∧ᶜ-monotoneˡ δ′≤ ⟩
           p C₁.·ᶜ δ″ C₁.∧ᶜ η′  ∎)
      where
      open CR₁

    tr-▸⁻¹′ {m} (fst p _) t-ok ▸fst@(fstₘ _ _) refl ≤γ′ =
      let δ , m′ , ≡tr-m′ , ▸t , γ′≤ , ok = inv-usage-fst₀₁ ▸fst
          m″ , ≡m′ , ≡m = tr-Mode-≡-ᵐ· (sym ≡tr-m′)
      in  UP′₁.fstₘ₀₁ m″
            (tr-▸⁻¹′ _ t-ok ▸t
               (let open Tools.Reasoning.PropositionalEquality in
                  tr-Mode m                 ≡⟨ ≡tr-m′ ⟩
                  m′ Mo₂.ᵐ· tr-Σ p          ≡˘⟨ cong (Mo₂._ᵐ· _) ≡m′ ⟩
                  tr-Mode m″ Mo₂.ᵐ· tr-Σ p  ≡˘⟨ tr-Mode-ᵐ· m″ (BMΣ 𝕤) ⟩
                  tr-Mode (m″ Mo₁.ᵐ· p)     ∎)
               (CP₂.≤ᶜ-trans ≤γ′ γ′≤))
            ≡m (λ {refl → tr-Σ-≤-𝟙-→ tr-emb (ok refl)})

    tr-▸⁻¹′
      {m} {γ} (prodrec r p _ _ _ _) (Q-ok , t-ok , u-ok)
      (prodrecₘ {γ = δ} {δ = η} ▸t ▸u ▸Q ok) refl γ≤rδ+η =
      case tr-Conₘ-≤ᶜ-+ᶜ γ≤rδ+η of
        λ (δ′ , η′ , δ′≤rδ , η′≤η , γ≤δ′+η′) →
      case tr-Conₘ-≤ᶜ-·ᶜ δ′≤rδ of
        λ (δ″ , δ″≤δ , δ′≤rδ″) →
      sub
        (prodrecₘ (tr-▸⁻¹′ _ t-ok ▸t (sym (tr-Mode-ᵐ· m BMΠ)) δ″≤δ)
           (tr-▸⁻¹′ _ u-ok ▸u refl let open CR₂ in begin
              tr-Conₘ η′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· r M₁.· p) ∙
              tr (Mo₁.⌜ m ⌝ M₁.· r)                          ≤⟨ η′≤η ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ∙
                                                                ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
              η ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr (r M₁.· p) ∙
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                    ≈˘⟨ CP₂.≈ᶜ-refl ∙ M₂.·-congˡ (tr-·-tr-Σ-≡ tr-morphism) ∙ refl ⟩

              η ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r M₂.· tr-Σ p ∙
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r                    ∎)
           (tr-∙▸[𝟘ᵐ?]⁻¹ Q-ok ▸Q .proj₂)
           (Prodrec-reflected [ ≈ᵐ-tr-Mode {m = m} ] ok))
        (let open CR₁ in begin
           γ                    ≤⟨ γ≤δ′+η′ ⟩
           δ′ C₁.+ᶜ η′          ≤⟨ CP₁.+ᶜ-monotoneˡ δ′≤rδ″ ⟩
           r C₁.·ᶜ δ″ C₁.+ᶜ η′  ∎)

    tr-▸⁻¹′
      {m} (natrec p _ r _ _ _ _) (P-ok , z-ok , s-ok , n-ok)
      (natrecₘ {δ = δ} ▸z ▸s ▸n ▸P) refl γ≤nr-prθδη =
      case tr-Conₘ-≤ᶜ-nrᶜ γ≤nr-prθδη of
        λ (_ , δ′ , _ , θ′≤θ , δ′≤δ , η′≤η , γ≤nr-prθ′δ′η′) →
      sub
        (natrecₘ (tr-▸⁻¹′ _ z-ok ▸z refl θ′≤θ)
           (tr-▸⁻¹′ _ s-ok ▸s refl (let open CR₂ in begin
              tr-Conₘ δ′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙
              tr (Mo₁.⌜ m ⌝ M₁.· r)                 ≤⟨ δ′≤δ ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ∙
                                                       ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
              δ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r           ∎))
           (tr-▸⁻¹′ _ n-ok ▸n refl η′≤η)
           (tr-∙▸[𝟘ᵐ?]⁻¹ P-ok ▸P .proj₂))
        γ≤nr-prθ′δ′η′
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open Graded.Modality.Morphism.Backward-instances common-properties
      open CQ.Is-nr-reflecting-morphism nr-reflected

    tr-▸⁻¹′
      {m} (natrec p _ r _ _ _ _) (P-ok , z-ok , s-ok , n-ok)
      (natrec-no-nrₘ {δ = η} ▸z ▸s ▸n ▸P γ′≤δ γ′≤η γ′≤θ fix) refl γ≤γ′ =
      case tr-≤ᶜ-no-nr γ≤γ′ γ′≤δ (γ′≤η ∘→ 𝟘ᵐ-allowed→¬Trivialᵐ _) (λ ⦃ ok ⦄ → γ′≤θ (λ _ → ok)) fix of λ {
        (_ , _ , η′ , _ ,
         δ′≤δ , η′≤η , θ′≤θ , γ≤γ″ , γ″≤δ′ , γ″≤η′ , γ″≤θ′ , fix′) →
      sub
        (UP′₁.natrec-no-nrₘ₀₁ (tr-▸⁻¹′ _ z-ok ▸z refl δ′≤δ)
           (tr-▸⁻¹′ _ s-ok ▸s refl $ let open CR₂ in begin
              tr-Conₘ η′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙
              tr (Mo₁.⌜ m ⌝ M₁.· r)                 ≤⟨ η′≤η ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ∙
                                                       ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
              η ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
              Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r           ∎)
           (tr-▸⁻¹′ _ n-ok ▸n refl θ′≤θ)
           (tr-∙▸[𝟘ᵐ?]⁻¹ P-ok ▸P .proj₂)
           γ″≤δ′
           γ″≤η′
           γ″≤θ′
           fix′)
        γ≤γ″ }
      where
      open Graded.Modality.Morphism.Backward-instances common-properties
      open MQP.Is-no-nr-reflecting-morphism no-nr-reflected

    tr-▸⁻¹′
      {m} (natrec p _ r _ _ _ _) (P-ok , z-ok , s-ok , n-ok)
      (natrec-no-nr-glbₘ {δ} ▸z ▸s ▸n ▸P x-glb χ-glb) refl γ≤γ′ =
      let _ , δ′ , η′ , _ , _ , ≤γ , ≤δ , ≤η , x′-glb , χ′-glb , θ≤ = tr-Conₘ-≤ᶜ-no-nr γ≤γ′ x-glb χ-glb
      in  sub
            (natrec-no-nr-glbₘ {δ = δ′} {η = η′}
              (tr-▸⁻¹′ _ z-ok ▸z refl ≤γ)
              (tr-▸⁻¹′ _ s-ok ▸s refl $ let open CR₂ in begin
                tr-Conₘ δ′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙
                tr (Mo₁.⌜ m ⌝ M₁.· r)                 ≤⟨ ≤δ ∙ ≤-refl ∙ ≤-refl ⟩
                δ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙
                tr (Mo₁.⌜ m ⌝ M₁.· r)                 ≈˘⟨ CP₂.≈ᶜ-refl ∙ tr-⌜⌝-· m ∙ tr-⌜⌝-· m ⟩
                δ ∙  Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙
                Mo₂.⌜ tr-Mode m ⌝ M₂.· tr r ∎)
              (tr-▸⁻¹′ _ n-ok ▸n refl ≤η)
              (tr-∙▸[𝟘ᵐ?]⁻¹ P-ok ▸P .proj₂) x′-glb χ′-glb) θ≤
      where
      open Graded.Modality.Morphism.Backward-instances common-properties
      open CQ.Is-no-nr-glb-reflecting-morphism no-nr-glb-reflected
    tr-▸⁻¹′
      {m} {γ} (emptyrec p _ _) (A-ok , t-ok)
      (emptyrecₘ ▸t ▸A ok) refl γ≤pδ =
      case tr-Conₘ-≤ᶜ-·ᶜ γ≤pδ of λ (δ′ , δ′≤δ , γ≤pδ′) →
      sub
        (emptyrecₘ (tr-▸⁻¹′ _ t-ok ▸t (sym (tr-Mode-ᵐ· m BMΠ)) δ′≤δ)
           (tr-▸[𝟘ᵐ?]⁻¹ A-ok ▸A .proj₂)
           (Emptyrec-reflected [ ≈ᵐ-tr-Mode {m = m} ] ok))
        (begin
           γ           ≤⟨ γ≤pδ′ ⟩
           p C₁.·ᶜ δ′  ∎)
      where
      open CR₁

    tr-▸⁻¹′
      {m} {γ} (unitrec p _ _ _ _) (A-ok , t-ok , u-ok)
      (unitrecₘ {γ = δ} {δ = η} ▸t ▸u ▸A ok) refl γ≤pδ+η =
      case tr-Conₘ-≤ᶜ-+ᶜ γ≤pδ+η of λ (δ′ , η′ , δ′≤pδ , η′≤η , γ≤δ′+η′) →
      case tr-Conₘ-≤ᶜ-·ᶜ δ′≤pδ of λ (δ″ , δ″≤δ , δ′≤pδ″) →
      sub
        (unitrecₘ (tr-▸⁻¹′ _ t-ok ▸t (sym (tr-Mode-ᵐ· m BMΠ)) δ″≤δ)
           (tr-▸⁻¹′ _ u-ok ▸u refl η′≤η) (tr-∙▸[𝟘ᵐ?]⁻¹ A-ok ▸A .proj₂)
           (Unitrec-reflected [ ≈ᵐ-tr-Mode {m = m} ] ok))
        (begin
          γ                    ≤⟨ γ≤δ′+η′ ⟩
          δ′ C₁.+ᶜ η′          ≤⟨ CP₁.+ᶜ-monotoneˡ δ′≤pδ″ ⟩
          p C₁.·ᶜ δ″ C₁.+ᶜ η′  ∎)
      where
      open CR₁

    tr-▸⁻¹′
      {γ} (Id _ _ _) (A-ok , t-ok , u-ok)
      (Idₘ {γ = δ} {δ = η} {η = θ} ok ▸A ▸t ▸u) refl γ≤δ+η+θ =
      let δ′ , χ  , ≤δ , ≤η+θ , γ≤δ′+χ  = tr-Conₘ-≤ᶜ-+ᶜ γ≤δ+η+θ
          η′ , θ′ , ≤η , ≤θ   , χ≤η′+θ′ = tr-Conₘ-≤ᶜ-+ᶜ ≤η+θ
      in
      sub
        (Idₘ (ok ∘→ Id-erased-preserved .proj₁)
           (tr-▸⁻¹′ _ A-ok ▸A refl ≤δ) (tr-▸⁻¹′ _ t-ok ▸t refl ≤η)
           (tr-▸⁻¹′ _ u-ok ▸u refl ≤θ))
        (begin
           γ                     ≤⟨ γ≤δ′+χ ⟩
           δ′ C₁.+ᶜ χ            ≤⟨ CP₁.+ᶜ-monotoneʳ χ≤η′+θ′ ⟩
           δ′ C₁.+ᶜ η′ C₁.+ᶜ θ′  ∎)
        where
        open CR₁

    tr-▸⁻¹′ (Id _ _ _) (A-ok , t-ok , u-ok) (Id₀ₘ ok ▸A ▸t ▸u) refl ≤𝟘 =
      sub
        (Id₀ₘ (Id-erased-preserved .proj₂ ok)
           (tr-▸[𝟘ᵐ?]⁻¹ A-ok ▸A .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ t-ok ▸t .proj₂)
           (tr-▸[𝟘ᵐ?]⁻¹ u-ok ▸u .proj₂))
        (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ rfl _ rflₘ refl ≤𝟘 =
      sub rflₘ (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′
      {m} (J p q _ _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok , w-ok)
      (Jₘ {γ₃} _ ▸A ▸t ▸B ▸u ▸v ▸w) refl γ≤ω[γ₂+γ₃+γ₄+γ₅+γ₆] =
      case tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ⁴ γ≤ω[γ₂+γ₃+γ₄+γ₅+γ₆] of λ
        (_ , γ₃′ , _ , _ , _ ,
         γ₂′≤γ₂ , γ₃′≤γ₃ , γ₄′≤γ₄ , γ₅′≤γ₅ , γ₆′≤γ₆ ,
         γ≤ω[γ₂′+γ₃′+γ₄′+γ₅′+γ₆′]) → sub
      (UP₁.Jₘ-generalised
         (tr-▸[𝟘ᵐ?]⁻¹ A-ok ▸A .proj₂) (tr-▸⁻¹′ _ t-ok ▸t refl γ₂′≤γ₂)
         (let open CR₂ in
          tr-▸⁻¹′ _ B-ok ▸B refl $ begin
            tr-Conₘ γ₃′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p) ∙ tr (Mo₁.⌜ m ⌝ M₁.· q)  ≤⟨ γ₃′≤γ₃ ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ∙
                                                                            ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
            γ₃ ∙
            Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr q    ∎)
         (tr-▸⁻¹′ _ u-ok ▸u refl γ₄′≤γ₄) (tr-▸⁻¹′ _ v-ok ▸v refl γ₅′≤γ₅)
         (tr-▸⁻¹′ _ w-ok ▸w refl γ₆′≤γ₆))
      γ≤ω[γ₂′+γ₃′+γ₄′+γ₅′+γ₆′]
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open Graded.Modality.Morphism.Backward-instances common-properties
      open CQ.Is-omega-preserving tr-emb omega-preserving

    tr-▸⁻¹′
      {m} {γ} (J p q _ _ _ _ _ _)
      (A-ok , t-ok , B-ok , u-ok , v-ok , w-ok)
      (J₀ₘ₁ {γ₃} {γ₄} ⦃ (≡some) ⦄ tr-p≡𝟘 tr-q≡𝟘 ▸A ▸t ▸B ▸u ▸v ▸w) refl
      γ≤ω[γ₃+γ₄] =
      case
        (case trivial-⊎-tr-≡-𝟘-⇔ of λ where
           (inj₁ trivial₁) →
             MP₁.≡-trivial trivial₁ , MP₁.≡-trivial trivial₁
           (inj₂ tr-≡-𝟘-⇔) →
             tr-≡-𝟘-⇔ .proj₁ tr-p≡𝟘 , tr-≡-𝟘-⇔ .proj₁ tr-q≡𝟘)
      of λ
        (p≡𝟘 , q≡𝟘) →
      case tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ γ≤ω[γ₃+γ₄] of λ
        (γ₃′ , _ , γ₃′≤γ₃ , γ₄′≤γ₄ , γ≤ω[γ₃′+γ₄′]) → sub
      (UP₁.J₀ₘ₁-generalised
         (≤ᵉᵐ→≡some→≡not-none
            (erased-matches-for-J-reflected ≈ᵐ-tr-Mode) ≡some
            .proj₂)
         p≡𝟘 q≡𝟘 (tr-▸[𝟘ᵐ?]⁻¹ A-ok ▸A .proj₂)
         (tr-▸[𝟘ᵐ?]⁻¹ t-ok ▸t .proj₂)
         (let open CR₂ in
          tr-▸⁻¹′ _ B-ok ▸B refl $ begin
            tr-Conₘ γ₃′ ∙ tr M₁.𝟘 ∙ tr M₁.𝟘  ≤⟨ γ₃′≤γ₃ ∙ ≤-reflexive (trans (cong tr $ sym p≡𝟘) tr-p≡𝟘) ∙
                                                ≤-reflexive (trans (cong tr $ sym q≡𝟘) tr-q≡𝟘) ⟩
            γ₃ ∙ M₂.𝟘 ∙ M₂.𝟘                 ∎)
         (tr-▸⁻¹′ _ u-ok ▸u refl γ₄′≤γ₄) (tr-▸[𝟘ᵐ?]⁻¹ v-ok ▸v .proj₂)
         (tr-▸[𝟘ᵐ?]⁻¹ w-ok ▸w .proj₂))
      γ≤ω[γ₃′+γ₄′]
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open Graded.Modality.Morphism.Backward-instances common-properties
      open CQ.Is-omega-preserving tr-emb omega-preserving

    tr-▸⁻¹′
      (J _ _ _ _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok , w-ok)
      (J₀ₘ₂ ⦃ (≡all) ⦄ ▸A ▸t ▸B ▸u ▸v ▸w) refl ≤γ′ = J₀ₘ₂
      ⦃ ≤ᵉᵐ→≡all→≡all (erased-matches-for-J-reflected ≈ᵐ-tr-Mode) ≡all ⦄
      (tr-▸[𝟘ᵐ?]⁻¹ A-ok ▸A .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ t-ok ▸t .proj₂)
      (tr-▸[𝟘ᵐ?]⁻¹ B-ok ▸B .proj₂) (tr-▸⁻¹′ _ u-ok ▸u refl ≤γ′)
      (tr-▸[𝟘ᵐ?]⁻¹ v-ok ▸v .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ w-ok ▸w .proj₂)

    tr-▸⁻¹′
      {m} (K p _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok)
      (Kₘ {γ₃} _ ▸A ▸t ▸B ▸u ▸v) refl γ≤ω[γ₂+γ₃+γ₄+γ₅] =
      case tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ³ γ≤ω[γ₂+γ₃+γ₄+γ₅] of λ
        (_ , γ₃′ , _ , _ , γ₂′≤γ₂ , γ₃′≤γ₃ , γ₄′≤γ₄ , γ₅′≤γ₅ ,
         γ≤ω[γ₂′+γ₃′+γ₄′+γ₅′]) → sub
      (UP₁.Kₘ-generalised
         (tr-▸[𝟘ᵐ?]⁻¹ A-ok ▸A .proj₂) (tr-▸⁻¹′ _ t-ok ▸t refl γ₂′≤γ₂)
         (let open CR₂ in
          tr-▸⁻¹′ _ B-ok ▸B refl $ begin
            tr-Conₘ γ₃′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· p)  ≤⟨ γ₃′≤γ₃ ∙ ≤-reflexive (sym (tr-⌜⌝-· m)) ⟩
            γ₃ ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· tr p     ∎)
         (tr-▸⁻¹′ _ u-ok ▸u refl γ₄′≤γ₄)
         (tr-▸⁻¹′ _ v-ok ▸v refl γ₅′≤γ₅))
      γ≤ω[γ₂′+γ₃′+γ₄′+γ₅′]
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open Graded.Modality.Morphism.Backward-instances common-properties
      open CQ.Is-omega-preserving tr-emb omega-preserving

    tr-▸⁻¹′
      (K _ _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok)
      (K₀ₘ₁ {γ₃} ⦃ (≡some) ⦄ tr-p≡𝟘 ▸A ▸t ▸B ▸u ▸v) refl γ≤ω[γ₃+γ₄] =
      case
        (case trivial-⊎-tr-≡-𝟘-⇔ of λ where
           (inj₁ trivial₁) → MP₁.≡-trivial trivial₁
           (inj₂ tr-≡-𝟘-⇔) → tr-≡-𝟘-⇔ .proj₁ tr-p≡𝟘)
      of λ
        p≡𝟘 →
      case tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ γ≤ω[γ₃+γ₄] of λ
        (γ₃′ , _ , γ₃′≤γ₃ , γ₄′≤γ₄ , γ≤ω[γ₃′+γ₄′]) → sub
      (UP₁.K₀ₘ₁-generalised
         (≤ᵉᵐ→≡some→≡not-none
            (erased-matches-for-K-reflected ≈ᵐ-tr-Mode) ≡some
            .proj₂)
         p≡𝟘 (tr-▸[𝟘ᵐ?]⁻¹ A-ok ▸A .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ t-ok ▸t .proj₂)
         (let open CR₂ in
          tr-▸⁻¹′ _ B-ok ▸B refl $ begin
            tr-Conₘ γ₃′ ∙ tr M₁.𝟘  ≤⟨ γ₃′≤γ₃ ∙ ≤-reflexive (trans (cong tr $ sym p≡𝟘) tr-p≡𝟘) ⟩
            γ₃ ∙ M₂.𝟘              ∎)
         (tr-▸⁻¹′ _ u-ok ▸u refl γ₄′≤γ₄) (tr-▸[𝟘ᵐ?]⁻¹ v-ok ▸v .proj₂))
      γ≤ω[γ₃′+γ₄′]
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open Graded.Modality.Morphism.Backward-instances common-properties
      open CQ.Is-omega-preserving tr-emb omega-preserving

    tr-▸⁻¹′
      (K _ _ _ _ _ _) (A-ok , t-ok , B-ok , u-ok , v-ok)
      (K₀ₘ₂ ⦃ (≡all) ⦄ ▸A ▸t ▸B ▸u ▸v) refl ≤γ′ = K₀ₘ₂
      ⦃ ≤ᵉᵐ→≡all→≡all (erased-matches-for-K-reflected ≈ᵐ-tr-Mode) ≡all ⦄
      (tr-▸[𝟘ᵐ?]⁻¹ A-ok ▸A .proj₂) (tr-▸[𝟘ᵐ?]⁻¹ t-ok ▸t .proj₂)
      (tr-▸[𝟘ᵐ?]⁻¹ B-ok ▸B .proj₂) (tr-▸⁻¹′ _ u-ok ▸u refl ≤γ′)
      (tr-▸[𝟘ᵐ?]⁻¹ v-ok ▸v .proj₂)

    tr-▸⁻¹′
      {m} ([]-cong _ l A t u v) ok ([]-congₘ ▸l ▸A ▸t ▸u ▸v ok′) refl
      ≤𝟘 =
      case []-cong-mode-reflected′ [ ≈ᵐ-tr-Mode {m = m} ] ok′ of λ where
        (inj₂ triv)        → ⊥-elim (ok triv)
        (inj₁ (ok′ , not)) →
          sub
            ([]-congₘ (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not l) ▸l .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not A) ▸A .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not t) ▸t .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not u) ▸u .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not v) ▸v .proj₂)
               ok′)
            (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ (Quot A B) ok (Quot ok′ ▸A ▸B) refl ≤γ′ =
      case Quot-reflected′ ok′ of λ where
        (inj₂ triv)        → ⊥-elim (ok triv)
        (inj₁ (ok′ , not)) →
          Quot ok′ (tr-▸⁻¹′ _ (¬→No-[]-cong-Quot′ not A) ▸A refl ≤γ′)
            (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not B) ▸B .proj₂)

    tr-▸⁻¹′ (class t) ok (class ok′ ▸t) refl ≤γ′ =
      case Quot-reflected′ ok′ of λ where
        (inj₂ triv)        → ⊥-elim (ok triv)
        (inj₁ (ok′ , not)) →
          class ok′ (tr-▸⁻¹′ _ (¬→No-[]-cong-Quot′ not t) ▸t refl ≤γ′)

    tr-▸⁻¹′ (resp A B t u v) ok (resp ok′ ▸A ▸B ▸t ▸u ▸v eq) refl ≤𝟘 =
      case Quot-reflected′ ok′ of λ where
        (inj₂ triv)        → ⊥-elim (ok triv)
        (inj₁ (ok′ , not)) →
          sub
            (resp ok′ (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not A) ▸A .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not B) ▸B .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not t) ▸t .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not u) ▸u .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not v) ▸v .proj₂)
               (tr-Mode-𝟘ᵐ?⁻¹ eq))
            (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′ (set A B t u v w) ok (set ok′ ▸A ▸B ▸t ▸u ▸v ▸w eq) refl
      ≤𝟘 =
      case Quot-reflected′ ok′ of λ where
        (inj₂ triv)        → ⊥-elim (ok triv)
        (inj₁ (ok′ , not)) →
          sub
            (set ok′ (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not A) ▸A .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not B) ▸B .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not t) ▸t .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not u) ▸u .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not v) ▸v .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not w) ▸w .proj₂)
               (tr-Mode-𝟘ᵐ?⁻¹ eq))
            (tr-Conₘ-≤ᶜ-𝟘ᶜ-→-≤ᶜ-𝟘ᶜ ≤𝟘)

    tr-▸⁻¹′
      {m} {γ} (qrec C t u v w) ok
      (qrec₀ {γ₂} {γ₅} ok₁ ok₂ ▸C ▸t ▸u ▸v ▸w) refl ≤γ′ =
      case Quot-reflected′ ok₁ of λ where
        (inj₂ triv)        → ⊥-elim (ok triv)
        (inj₁ (ok₁ , not)) →
          let γ₂′ , δ′ , ≤γ₂ , δ′≤ , γ≤ = tr-Conₘ-≤ᶜ-+ᶜ ≤γ′
              γ₅′ , ≤γ₅ , δ′≤′          = tr-Conₘ-≤ᶜ-ωᶜ·ᶜ δ′≤
          in
          sub
            (qrec₀ ok₁ (Qrec-motive-erased-preserved .proj₂ ok₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not C) ▸C .proj₂)
               (let open CP₂.≤ᶜ-reasoning in
                tr-▸⁻¹′ _ (¬→No-[]-cong-Quot′ not t) ▸t refl $ begin
                  tr-Conₘ γ₂′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· ω)     ≤⟨ ≤γ₂ ∙ ≤-reflexive (trans (sym (tr-⌜⌝-· m))
                                                                    (M₂.·-congˡ (M.Is-omega-preserving-morphism.tr-ω omega-preserving))) ⟩
                  γ₂          ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· ω  ∎)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not u) ▸u .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not v) ▸v .proj₂)
               (tr-▸⁻¹′ _ (¬→No-[]-cong-Quot′ not w) ▸w refl ≤γ₅))
            (let open CP₁.≤ᶜ-reasoning in
             begin
               γ                      ≤⟨ γ≤ ⟩
               γ₂′ C₁.+ᶜ δ′           ≤⟨ CP₁.+ᶜ-monotoneʳ δ′≤′ ⟩
               γ₂′ C₁.+ᶜ ω C₁.·ᶜ γ₅′  ∎)
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open Graded.Modality.Morphism.Backward-instances common-properties
      open CQ.Is-omega-preserving tr-emb omega-preserving

    tr-▸⁻¹′
      {m} {γ} (qrec C t u v w) ok
      (qrec₁ {γ₁} {γ₂} {γ₅} ok₁ ok₂ ▸C ▸t ▸u ▸v ▸w) refl ≤γ′ =
      case Quot-reflected′ ok₁ of λ where
        (inj₂ triv)        → ⊥-elim (ok triv)
        (inj₁ (ok₁ , not)) →
          let γ₁′ , γ₂′ , γ₅′ , ≤γ₁ , ≤γ₂ , ≤γ₅ , γ≤ =
                tr-Conₘ-≤ᶜ-ωᶜ·ᶜ+ᶜ² ≤γ′
          in
          sub
            (qrec₁ ok₁ (ok₂ ∘→ Qrec-motive-erased-preserved .proj₁)
               (tr-▸⁻¹′ _ (¬→No-[]-cong-Quot′ not C) ▸C refl $ begin
                  tr-Conₘ γ₁′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· ω)     ≤⟨ ≤γ₁ ∙ ≤-reflexive (trans (sym (tr-⌜⌝-· m))
                                                                     (M₂.·-congˡ (M.Is-omega-preserving-morphism.tr-ω omega-preserving))) ⟩
                  γ₁          ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· ω  ∎)
               (tr-▸⁻¹′ _ (¬→No-[]-cong-Quot′ not t) ▸t refl $ begin
                  tr-Conₘ γ₂′ ∙ tr (Mo₁.⌜ m ⌝ M₁.· ω)     ≤⟨ ≤γ₂ ∙ ≤-reflexive (trans (sym (tr-⌜⌝-· m))
                                                                     (M₂.·-congˡ (M.Is-omega-preserving-morphism.tr-ω omega-preserving))) ⟩
                  γ₂          ∙ Mo₂.⌜ tr-Mode m ⌝ M₂.· ω  ∎)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not u) ▸u .proj₂)
               (tr-▸[𝟘ᵐ?]⁻¹ (¬→No-[]-cong-Quot′ not v) ▸v .proj₂)
               (tr-▸⁻¹′ _ (¬→No-[]-cong-Quot′ not w) ▸w refl ≤γ₅))
            γ≤
      where
      open Configuration-types.Instance C₁
      open Configuration-types.Instance C₂
      open Graded.Modality.Morphism.Backward-instances common-properties
      open CQ.Is-omega-preserving tr-emb omega-preserving
      open CP₂.≤ᶜ-reasoning
      -- open M.Is-omega-preserving-morphism.tr-ω omega-preserving

    tr-▸⁻¹′ {γ′} {γ} t ok (sub {γ = δ} ▸t γ′≤δ) refl γ≤γ′ =
      tr-▸⁻¹′ t ok ▸t refl (begin
        tr-Conₘ γ  ≤⟨ γ≤γ′ ⟩
        γ′         ≤⟨ γ′≤δ ⟩
        δ          ∎)
      where
      open CR₂

    tr-▸[𝟘ᵐ?]⁻¹ :
      {t : Term[_] M₁ k n} →
      No-[]-cong-Quot′ M₁.Trivial t →
      γ U₂.▸[ m ] tr-Term t → ∃ λ δ → δ U₁.▸[ Mo₁.𝟘ᵐ? ] t
    tr-▸[𝟘ᵐ?]⁻¹ {m = 𝟙ᵐ} {t} ok ▸t =
      case tr-Conₘ-≤ᶜ of λ
        (δ , ≤γ) →
      Mo₁.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ U₁.▸[ m ] t)
        (C₁.𝟘ᶜ , UP′₁.▸-𝟘₀₁ (tr-▸⁻¹′ {γ = δ} _ ok ▸t refl ≤γ))
        (λ _ → δ , tr-▸⁻¹′ _ ok ▸t refl ≤γ)
    tr-▸[𝟘ᵐ?]⁻¹ {m = 𝟘ᵐ[ ok ]} {t} ok′ ▸t =
      Mo₁.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ U₁.▸[ m ] t)
        (case tr-Conₘ-≤ᶜ of λ
           (δ , ≤γ) →
         δ , tr-▸⁻¹′ _ ok′ ▸t Mo₂.𝟘ᵐ-cong ≤γ)
        (λ not-ok →
           let triv = trivial not-ok ok in
           C₁.𝟘ᶜ ,
           tr-▸⁻¹-trivial (No-[]-cong-Quot′⇔ t .proj₁ ok′ triv) triv ▸t)

    tr-∙▸[𝟘ᵐ?]⁻¹ :
      {t : Term[_] M₁ k (1+ n)} →
      No-[]-cong-Quot′ M₁.Trivial t →
      γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p U₂.▸[ m ] tr-Term t →
      ∃ λ δ → δ ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· p U₁.▸[ Mo₁.𝟘ᵐ? ] t
    tr-∙▸[𝟘ᵐ?]⁻¹ {γ} {m = 𝟙ᵐ} {p} {t} ok ▸t =
      Mo₁.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ ∙ Mo₁.⌜ m ⌝ M₁.· p U₁.▸[ m ] t)
        (case tr-Conₘ-≤ᶜ of λ
           (δ , ≤γ) →
           C₁.𝟘ᶜ
         , sub (UP′₁.▸-𝟘₀₁ (tr-▸⁻¹′ {γ = δ} _ ok ▸t refl ≤γ))
             (let open CR₁ in begin
                C₁.𝟘ᶜ ∙ M₁.𝟘 M₁.· p  ≈⟨ CP₁.≈ᶜ-refl ∙ M₁.·-zeroˡ _ ⟩
                C₁.𝟘ᶜ                ∎))
        (λ _ →
           case tr-Conₘ-≤ᶜ of λ
             (δ , ≤γ) →
             δ
           , tr-▸⁻¹′ _ ok ▸t refl
               (let open CR₂ in begin
                  tr-Conₘ δ ∙ tr (M₁.𝟙 M₁.· p)   ≈⟨ CP₂.≈ᶜ-refl ∙ tr-· ⟩
                  tr-Conₘ δ ∙ tr M₁.𝟙 M₂.· tr p  ≤⟨ ≤γ ∙ ·-monotoneˡ tr-𝟙 ⟩
                  γ ∙ M₂.𝟙 M₂.· tr p             ∎))
    tr-∙▸[𝟘ᵐ?]⁻¹ {γ} {m = 𝟘ᵐ[ ok ]} {p} {t} ok′ ▸t =
      Mo₁.𝟘ᵐ?-elim
        (λ m → ∃ λ δ → δ ∙ Mo₁.⌜ m ⌝ M₁.· p U₁.▸[ m ] t)
        (case tr-Conₘ-≤ᶜ of λ
           (δ , ≤γ) →
           δ
         , tr-▸⁻¹′ _ ok′ ▸t Mo₂.𝟘ᵐ-cong (begin
             tr-Conₘ δ ∙ tr (M₁.𝟘 M₁.· p)  ≈⟨ CP₂.≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ⟩
             tr-Conₘ δ ∙ tr M₁.𝟘           ≤⟨ ≤γ ∙ tr-𝟘-≤ ⟩
             γ ∙ M₂.𝟘                      ≈˘⟨ CP₂.≈ᶜ-refl ∙ M₂.·-zeroˡ _ ⟩
             γ ∙ M₂.𝟘 M₂.· tr p            ∎))
        (λ not-ok →
           let triv = trivial not-ok ok in
           C₁.𝟘ᶜ ,
           sub
             (tr-▸⁻¹-trivial (No-[]-cong-Quot′⇔ t .proj₁ ok′ triv) triv
                ▸t)
             (CP₁.≈ᶜ-trivial triv))
      where
      open CR₂

    tr-∙∙▸[𝟘ᵐ?]⁻¹ :
      {t : Term[_] M₁ k (2+ n)} →
      No-[]-cong-Quot′ M₁.Trivial t →
      γ ∙ Mo₂.⌜ m ⌝ M₂.· tr p ∙ Mo₂.⌜ m ⌝ M₂.· tr q
        U₂.▸[ m ] tr-Term t →
      ∃ λ δ →
      δ ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· p ∙ Mo₁.⌜ Mo₁.𝟘ᵐ? ⌝ M₁.· q
        U₁.▸[ Mo₁.𝟘ᵐ? ] t
    tr-∙∙▸[𝟘ᵐ?]⁻¹ {γ} {m = 𝟙ᵐ} {p} {q} {t} ok ▸t =
      Mo₁.𝟘ᵐ?-elim
        (λ m →
           ∃ λ δ → δ ∙ Mo₁.⌜ m ⌝ M₁.· p ∙ Mo₁.⌜ m ⌝ M₁.· q U₁.▸[ m ] t)
        (case tr-Conₘ-≤ᶜ of λ
           (δ , ≤γ) →
           C₁.𝟘ᶜ
         , sub (UP′₁.▸-𝟘₀₁ (tr-▸⁻¹′ {γ = δ} _ ok ▸t refl ≤γ))
             (let open CR₁ in begin
                C₁.𝟘ᶜ ∙ M₁.𝟘 M₁.· p ∙ M₁.𝟘 M₁.· q  ≈⟨ CP₁.≈ᶜ-refl ∙ M₁.·-zeroˡ _ ∙ M₁.·-zeroˡ _ ⟩
                C₁.𝟘ᶜ                              ∎))
        (λ _ →
           case tr-Conₘ-≤ᶜ of λ
             (δ , ≤γ) →
             δ
           , tr-▸⁻¹′ _ ok ▸t refl
               (let open CR₂ in begin
                  tr-Conₘ δ ∙ tr (M₁.𝟙 M₁.· p) ∙ tr (M₁.𝟙 M₁.· q)    ≈⟨ CP₂.≈ᶜ-refl ∙ tr-· ∙ tr-· ⟩
                  tr-Conₘ δ ∙ tr M₁.𝟙 M₂.· tr p ∙ tr M₁.𝟙 M₂.· tr q  ≤⟨ ≤γ ∙ ·-monotoneˡ tr-𝟙 ∙ ·-monotoneˡ tr-𝟙 ⟩
                  γ ∙ M₂.𝟙 M₂.· tr p ∙ M₂.𝟙 M₂.· tr q                ∎))
    tr-∙∙▸[𝟘ᵐ?]⁻¹ {γ} {m = 𝟘ᵐ[ ok ]} {p} {q} {t} ok′ ▸t =
      Mo₁.𝟘ᵐ?-elim
        (λ m →
           ∃ λ δ → δ ∙ Mo₁.⌜ m ⌝ M₁.· p ∙ Mo₁.⌜ m ⌝ M₁.· q U₁.▸[ m ] t)
        (case tr-Conₘ-≤ᶜ of λ
           (δ , ≤γ) →
           δ
         , tr-▸⁻¹′ _ ok′ ▸t Mo₂.𝟘ᵐ-cong (begin
             tr-Conₘ δ ∙ tr (M₁.𝟘 M₁.· p) ∙ tr (M₁.𝟘 M₁.· q)  ≈⟨ CP₂.≈ᶜ-refl ∙ cong tr (M₁.·-zeroˡ _) ∙ cong tr (M₁.·-zeroˡ _) ⟩
             tr-Conₘ δ ∙ tr M₁.𝟘 ∙ tr M₁.𝟘                    ≤⟨ ≤γ ∙ tr-𝟘-≤ ∙ tr-𝟘-≤ ⟩
             γ ∙ M₂.𝟘 ∙ M₂.𝟘                                  ≈˘⟨ CP₂.≈ᶜ-refl ∙ M₂.·-zeroˡ _ ∙ M₂.·-zeroˡ _ ⟩
             γ ∙ M₂.𝟘 M₂.· tr p ∙ M₂.𝟘 M₂.· tr q              ∎))
        (λ not-ok →
           let triv = trivial not-ok ok in
           C₁.𝟘ᶜ ,
           sub
             (tr-▸⁻¹-trivial (No-[]-cong-Quot′⇔ t .proj₁ ok′ triv) triv
                ▸t)
             (CP₁.≈ᶜ-trivial triv))
      where
      open CR₂

  opaque

    -- Preservation of ▸[_].

    tr-▸-DCon⁻¹ :
      (∀ {α t A} → M₁.Trivial → α ↦ t ∷ A ∈ ∇ → No-[]-cong-Quot t) →
      U₂.▸[ tr-Mode m ] tr-DCon ∇ → U₁.▸[ m ] ∇
    tr-▸-DCon⁻¹ ok ▸∇ α∈∇ =
      tr-▸⁻¹ (λ triv → ok triv α∈∇) (▸∇ (tr-↦∷ α∈∇))
