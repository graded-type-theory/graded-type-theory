------------------------------------------------------------------------
-- Some example morphisms and order embeddings
------------------------------------------------------------------------

-- It might make sense to replace some of the proofs below with a lot
-- of cases with automated proofs.

module Graded.Modality.Morphism.Examples where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

open import Graded.Modality
open import Graded.Modality.Dedicated-nr
open import Graded.Modality.Instances.Affine as A
  using (Affine; affineModality)
open import Graded.Modality.Instances.Erasure as E
  using (Erasure; 𝟘; ω)
open import Graded.Modality.Instances.Erasure.Modality as E
  using (ErasureModality)
open import Graded.Modality.Instances.Linear-or-affine as LA
  using (Linear-or-affine; 𝟘; 𝟙; ≤𝟙; ≤ω; linear-or-affine)
open import Graded.Modality.Instances.Linearity as L
  using (Linearity; linearityModality)
open import Graded.Modality.Instances.Unit using (UnitModality)
open import Graded.Modality.Instances.Zero-one-many as ZOM
  using (Zero-one-many; 𝟘; 𝟙; ω; zero-one-many-modality)
open import Graded.Modality.Morphism
import Graded.Modality.Properties
open import Graded.Modality.Variant

open Modality-variant

private variable
  𝟙≤𝟘             : Bool
  v₁ v₂           : Modality-variant _
  A M             : Set _
  v₁-ok v₂-ok     : A
  p q₁ q₂ q₃ q₄ r : M

------------------------------------------------------------------------
-- Some translation functions

-- A translation from ⊤ to Erasure.

unit→erasure : ⊤ → Erasure
unit→erasure _ = ω

-- A translation from Erasure to ⊤.

erasure→unit : Erasure → ⊤
erasure→unit = _

-- A translation from Erasure to Zero-one-many.

erasure→zero-one-many : Erasure → Zero-one-many 𝟙≤𝟘
erasure→zero-one-many = λ where
  𝟘 → 𝟘
  ω → ω

-- A translation from Erasure to Zero-one-many, intended to be used
-- for the first components of Σ-types.

erasure→zero-one-many-Σ : Erasure → Zero-one-many 𝟙≤𝟘
erasure→zero-one-many-Σ = λ where
  𝟘 → 𝟘
  ω → 𝟙

-- A translation from Zero-one-many to Erasure.

zero-one-many→erasure : Zero-one-many 𝟙≤𝟘 → Erasure
zero-one-many→erasure = λ where
  𝟘 → 𝟘
  _ → ω

-- A translation from Linearity to Linear-or-affine.

linearity→linear-or-affine : Linearity → Linear-or-affine
linearity→linear-or-affine = λ where
  𝟘 → 𝟘
  𝟙 → 𝟙
  ω → ≤ω

-- A translation from Linear-or-affine to Linearity.

linear-or-affine→linearity : Linear-or-affine → Linearity
linear-or-affine→linearity = λ where
  𝟘  → 𝟘
  𝟙  → 𝟙
  ≤𝟙 → ω
  ≤ω → ω

-- A translation from Affine to Linear-or-affine.

affine→linear-or-affine : Affine → Linear-or-affine
affine→linear-or-affine = λ where
  𝟘 → 𝟘
  𝟙 → ≤𝟙
  ω → ≤ω

-- A translation from Affine to Linear-or-affine, intended to be used
-- for the first components of Σ-types.

affine→linear-or-affine-Σ : Affine → Linear-or-affine
affine→linear-or-affine-Σ = λ where
  𝟘 → 𝟘
  𝟙 → 𝟙
  ω → ≤ω

-- A translation from Linear-or-affine to Affine.

linear-or-affine→affine : Linear-or-affine → Affine
linear-or-affine→affine = λ where
  𝟘  → 𝟘
  𝟙  → 𝟙
  ≤𝟙 → 𝟙
  ≤ω → ω

-- A translation from Affine to Linearity.

affine→linearity : Affine → Linearity
affine→linearity =
  linear-or-affine→linearity ∘→ affine→linear-or-affine

-- A translation from Affine to Linearity.

affine→linearity-Σ : Affine → Linearity
affine→linearity-Σ =
  linear-or-affine→linearity ∘→ affine→linear-or-affine-Σ

-- A translation from Linearity to Affine.

linearity→affine : Linearity → Affine
linearity→affine =
  linear-or-affine→affine ∘→ linearity→linear-or-affine

------------------------------------------------------------------------
-- Morphisms and order embeddings

-- The function unit→erasure is an order embedding from a unit
-- modality to an erasure modality if a certain assumption holds.

unit⇨erasure :
  let 𝕄₁ = UnitModality v₁ v₁-ok
      𝕄₂ = ErasureModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ unit→erasure
unit⇨erasure {v₁-ok = v₁-ok} s⇔s = λ where
    .tr-order-reflecting _ → refl
    .trivial _ _           → refl
    .trivial-⊎-tr-𝟘        → inj₁ refl
    .tr-≤                  → _ , refl
    .tr-≤-𝟙 _              → refl
    .tr-≤-+ _              → _ , _ , refl , refl , refl
    .tr-≤-· _              → _ , refl , refl
    .tr-≤-∧ _              → _ , _ , refl , refl , refl
    .tr-≤-nr _             → _ , _ , _ , refl , refl , refl , refl
    .tr-≤-no-nr _ _ _ _ _  → _ , _ , _ , _ , refl , refl , refl , refl
                           , refl , (λ _ → refl) , (λ _ → refl) , refl
    .tr-morphism           → λ where
      .𝟘ᵐ-in-second-if-in-first             → ⊥-elim ∘→ v₁-ok
      .𝟘ᵐ-in-first-if-in-second _           → inj₂ refl
      .𝟘-well-behaved-in-first-if-in-second → λ _ → inj₂ refl
      .nr-in-first-iff-in-second            → s⇔s
      .tr-𝟘-≤                               → refl
      .tr-≡-𝟘-⇔                             → ⊥-elim ∘→ v₁-ok
      .tr-<-𝟘 _ _                           → refl , λ ()
      .tr-𝟙                                 → refl
      .tr-+                                 → refl
      .tr-·                                 → refl
      .tr-∧                                 → refl
      .tr-nr                                → refl
  where
  open Is-morphism
  open Is-order-embedding

-- The function erasure→unit is a morphism from an erasure modality to
-- a unit modality if certain assumptions hold.

erasure⇨unit :
  ¬ T (𝟘ᵐ-allowed v₁) →
  let 𝕄₁ = ErasureModality v₁
      𝕄₂ = UnitModality v₂ v₂-ok
  in
  ⦃ has-nr₁ : Dedicated-nr 𝕄₁ ⦄
  ⦃ has-nr₂ : Dedicated-nr 𝕄₂ ⦄ →
  Is-morphism 𝕄₁ 𝕄₂ erasure→unit
erasure⇨unit
  {v₂-ok = v₂-ok} not-ok₁ ⦃ has-nr₁ = has-nr₁ ⦄ ⦃ has-nr₂ = has-nr₂ ⦄ =
  λ where
    .tr-𝟘-≤                                 → refl
    .tr-≡-𝟘-⇔                               → ⊥-elim ∘→ not-ok₁
    .tr-<-𝟘 _                               → ⊥-elim ∘→ v₂-ok
    .tr-𝟙                                   → refl
    .tr-+                                   → refl
    .tr-·                                   → refl
    .tr-∧                                   → refl
    .tr-nr                                  → refl
    .nr-in-first-iff-in-second              → (λ _ → has-nr₂)
                                            , (λ _ → has-nr₁)
    .𝟘ᵐ-in-second-if-in-first               → ⊥-elim ∘→ not-ok₁
    .𝟘ᵐ-in-first-if-in-second               → ⊥-elim
                                                (not-nr-and-no-nr _)
    .𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ E.erasure-has-well-behaved-zero
  where
  open Is-morphism

-- The function erasure→unit is not a morphism from an erasure
-- modality to a unit modality if a certain assumption holds.

¬erasure⇨unit :
  let 𝕄₁ = ErasureModality v₁
      𝕄₂ = UnitModality v₂ v₂-ok
  in
  No-dedicated-nr 𝕄₁ ⊎ No-dedicated-nr 𝕄₂ →
  ¬ Is-morphism 𝕄₁ 𝕄₂ erasure→unit
¬erasure⇨unit {v₂-ok = v₂-ok} no-nr′ m =
  case
    Is-morphism.𝟘ᵐ-in-first-if-in-second m ⦃ no-nr = no-nr ⦄ (inj₂ refl)
  of λ {
    (inj₁ ok) →
  v₂-ok (Is-morphism.𝟘ᵐ-in-second-if-in-first m ok) }
  where
  no-nr = case no-nr′ of λ where
    (inj₁ no-nr) → no-nr
    (inj₂ no-nr) →
      Is-morphism.no-nr-in-first-if-in-second m ⦃ no-nr = no-nr ⦄

-- The function erasure→unit is not an order embedding from an erasure
-- modality to a unit modality.

¬erasure⇨unit′ :
  ¬ Is-order-embedding (ErasureModality v₁) (UnitModality v₂ v₂-ok)
      erasure→unit
¬erasure⇨unit′ m =
  case Is-order-embedding.tr-injective m {p = 𝟘} {q = ω} refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a zero-one-many-modality modality if certain
-- assumptions hold. The zero-one-many-modality modality can be
-- defined with either 𝟙 ≤ 𝟘 or 𝟙 ≰ 𝟘.

erasure⇨zero-one-many :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = ErasureModality v₁
      𝕄₂ = zero-one-many-modality 𝟙≤𝟘 v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ erasure→zero-one-many
erasure⇨zero-one-many {v₁ = v₁} {v₂ = v₂} {𝟙≤𝟘 = 𝟙≤𝟘} refl s⇔s = λ where
    .Is-order-embedding.trivial not-ok ok   → ⊥-elim (not-ok ok)
    .Is-order-embedding.trivial-⊎-tr-𝟘      → inj₂ refl
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-≤-nr {r = r}     → tr-≤-nr _ _ r _ _ _
    .Is-order-embedding.tr-≤-no-nr {s = s}  → tr-≤-no-nr s
    .Is-order-embedding.tr-order-reflecting →
      tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism → λ where
      .Is-morphism.tr-𝟘-≤                    → refl
      .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                             , λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                      → refl
      .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-· {p = p}              → tr-· p _
      .Is-morphism.tr-∧ {p = p}              → ≤-reflexive (tr-∧ p _)
      .Is-morphism.tr-nr {r = r} {z = z}     → ≤-reflexive
                                                 (tr-nr _ r z _ _)
      .Is-morphism.nr-in-first-iff-in-second → s⇔s
      .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
      .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
        (inj₁ ok) → inj₁ ok
      .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ E.erasure-has-well-behaved-zero
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘
  module P₁ = Graded.Modality.Properties (ErasureModality v₁)
  open Graded.Modality.Properties (zero-one-many-modality 𝟙≤𝟘 v₂)
  open Tools.Reasoning.PartialOrder ≤-poset

  tr′  = erasure→zero-one-many
  tr⁻¹ = zero-one-many→erasure

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-≤-𝟙 : ∀ p → tr′ p 𝟘𝟙ω.≤ 𝟙 → p E.≤ ω
  tr-≤-𝟙 𝟘 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-𝟙 ω _     = refl

  tr-+ : ∀ p q → tr′ (p E.+ q) ≡ tr′ p 𝟘𝟙ω.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p E.· q) ≡ tr′ p 𝟘𝟙ω.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p E.∧ q) ≡ tr′ p 𝟘𝟙ω.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω ω = refl

  tr-nr :
    ∀ p r z s n →
    tr′ (E.nr p r z s n) ≡
    𝟘𝟙ω.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = tr-nr′ _
    where
    tr-nr′ :
      ∀ 𝟙≤𝟘 →
      let module 𝟘𝟙ω′ = ZOM 𝟙≤𝟘 in
      ∀ p r z s n →
      tr′ (E.nr p r z s n) ≡
      𝟘𝟙ω′.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
    tr-nr′ = λ where
      false 𝟘 𝟘 𝟘 𝟘 𝟘 → refl
      false 𝟘 𝟘 𝟘 𝟘 ω → refl
      false 𝟘 𝟘 𝟘 ω 𝟘 → refl
      false 𝟘 𝟘 𝟘 ω ω → refl
      false 𝟘 𝟘 ω 𝟘 𝟘 → refl
      false 𝟘 𝟘 ω 𝟘 ω → refl
      false 𝟘 𝟘 ω ω 𝟘 → refl
      false 𝟘 𝟘 ω ω ω → refl
      false 𝟘 ω 𝟘 𝟘 𝟘 → refl
      false 𝟘 ω 𝟘 𝟘 ω → refl
      false 𝟘 ω 𝟘 ω 𝟘 → refl
      false 𝟘 ω 𝟘 ω ω → refl
      false 𝟘 ω ω 𝟘 𝟘 → refl
      false 𝟘 ω ω 𝟘 ω → refl
      false 𝟘 ω ω ω 𝟘 → refl
      false 𝟘 ω ω ω ω → refl
      false ω 𝟘 𝟘 𝟘 𝟘 → refl
      false ω 𝟘 𝟘 𝟘 ω → refl
      false ω 𝟘 𝟘 ω 𝟘 → refl
      false ω 𝟘 𝟘 ω ω → refl
      false ω 𝟘 ω 𝟘 𝟘 → refl
      false ω 𝟘 ω 𝟘 ω → refl
      false ω 𝟘 ω ω 𝟘 → refl
      false ω 𝟘 ω ω ω → refl
      false ω ω 𝟘 𝟘 𝟘 → refl
      false ω ω 𝟘 𝟘 ω → refl
      false ω ω 𝟘 ω 𝟘 → refl
      false ω ω 𝟘 ω ω → refl
      false ω ω ω 𝟘 𝟘 → refl
      false ω ω ω 𝟘 ω → refl
      false ω ω ω ω 𝟘 → refl
      false ω ω ω ω ω → refl
      true  𝟘 𝟘 𝟘 𝟘 𝟘 → refl
      true  𝟘 𝟘 𝟘 𝟘 ω → refl
      true  𝟘 𝟘 𝟘 ω 𝟘 → refl
      true  𝟘 𝟘 𝟘 ω ω → refl
      true  𝟘 𝟘 ω 𝟘 𝟘 → refl
      true  𝟘 𝟘 ω 𝟘 ω → refl
      true  𝟘 𝟘 ω ω 𝟘 → refl
      true  𝟘 𝟘 ω ω ω → refl
      true  𝟘 ω 𝟘 𝟘 𝟘 → refl
      true  𝟘 ω 𝟘 𝟘 ω → refl
      true  𝟘 ω 𝟘 ω 𝟘 → refl
      true  𝟘 ω 𝟘 ω ω → refl
      true  𝟘 ω ω 𝟘 𝟘 → refl
      true  𝟘 ω ω 𝟘 ω → refl
      true  𝟘 ω ω ω 𝟘 → refl
      true  𝟘 ω ω ω ω → refl
      true  ω 𝟘 𝟘 𝟘 𝟘 → refl
      true  ω 𝟘 𝟘 𝟘 ω → refl
      true  ω 𝟘 𝟘 ω 𝟘 → refl
      true  ω 𝟘 𝟘 ω ω → refl
      true  ω 𝟘 ω 𝟘 𝟘 → refl
      true  ω 𝟘 ω 𝟘 ω → refl
      true  ω 𝟘 ω ω 𝟘 → refl
      true  ω 𝟘 ω ω ω → refl
      true  ω ω 𝟘 𝟘 𝟘 → refl
      true  ω ω 𝟘 𝟘 ω → refl
      true  ω ω 𝟘 ω 𝟘 → refl
      true  ω ω 𝟘 ω ω → refl
      true  ω ω ω 𝟘 𝟘 → refl
      true  ω ω ω 𝟘 ω → refl
      true  ω ω ω ω 𝟘 → refl
      true  ω ω ω ω ω → refl

  tr-order-reflecting : ∀ p q → tr′ p 𝟘𝟙ω.≤ tr′ q → p E.≤ q
  tr-order-reflecting 𝟘 𝟘 _ = refl
  tr-order-reflecting ω 𝟘 _ = refl
  tr-order-reflecting ω ω _ = refl

  tr-≤-+ :
    ∀ p q r →
    tr′ p 𝟘𝟙ω.≤ q 𝟘𝟙ω.+ r →
    ∃₂ λ q′ r′ → tr′ q′ 𝟘𝟙ω.≤ q × tr′ r′ 𝟘𝟙ω.≤ r × p E.≤ q′ E.+ r′
  tr-≤-+ 𝟘 𝟘 𝟘 _     = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟘 𝟘 𝟙 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-+ 𝟘 𝟙 𝟘 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-+ ω _ _ _     = ω , ω , refl , refl , refl

  tr-≤-· :
    ∀ p q r →
    tr′ p 𝟘𝟙ω.≤ tr′ q 𝟘𝟙ω.· r →
    ∃ λ r′ → tr′ r′ 𝟘𝟙ω.≤ r × p E.≤ q E.· r′
  tr-≤-· 𝟘 𝟘 _ _ = ω , refl , refl
  tr-≤-· 𝟘 ω 𝟘 _ = 𝟘 , refl , refl
  tr-≤-· ω _ _ _ = ω , refl , refl

  tr-≤-∧ :
    ∀ p q r →
    tr′ p 𝟘𝟙ω.≤ q 𝟘𝟙ω.∧ r →
    ∃₂ λ q′ r′ → tr′ q′ 𝟘𝟙ω.≤ q × tr′ r′ 𝟘𝟙ω.≤ r × p E.≤ q′ E.∧ r′
  tr-≤-∧ 𝟘 𝟘 𝟘 _     = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-∧ 𝟘 𝟘 𝟙 𝟘≤𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘≰𝟘∧𝟙 𝟘≤𝟘∧𝟙)
  tr-≤-∧ 𝟘 𝟙 𝟘 𝟘≤𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘≰𝟘∧𝟙 𝟘≤𝟘∧𝟙)
  tr-≤-∧ 𝟘 𝟙 𝟙 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-∧ ω _ _ _     = ω , ω , refl , refl , refl

  𝟘≰ω·𝟘∧𝟙 : ¬ 𝟘 𝟘𝟙ω.≤ ω 𝟘𝟙ω.· 𝟘𝟙ω.𝟘∧𝟙
  𝟘≰ω·𝟘∧𝟙 𝟘≤ω·𝟘∧𝟙 =
    case begin
      𝟘                ≤⟨ 𝟘≤ω·𝟘∧𝟙 ⟩
      ω 𝟘𝟙ω.· 𝟘𝟙ω.𝟘∧𝟙  ≡⟨ 𝟘𝟙ω.ω·≢𝟘 𝟘𝟙ω.𝟘∧𝟙≢𝟘 ⟩
      ω                ∎
    of λ ()

  tr-≤-nr :
    ∀ q p r z₁ s₁ n₁ →
    tr′ q 𝟘𝟙ω.≤ 𝟘𝟙ω.nr (tr′ p) (tr′ r) z₁ s₁ n₁ →
    ∃₃ λ z₂ s₂ n₂ →
       tr′ z₂ 𝟘𝟙ω.≤ z₁ × tr′ s₂ 𝟘𝟙ω.≤ s₁ × tr′ n₂ 𝟘𝟙ω.≤ n₁ ×
       q E.≤ E.nr p r z₂ s₂ n₂
  tr-≤-nr = tr-≤-nr′ _
    where
    tr-≤-nr′ :
      ∀ 𝟙≤𝟘 →
      let module 𝟘𝟙ω′ = ZOM 𝟙≤𝟘 in
      ∀ q p r z₁ s₁ n₁ →
      tr′ q 𝟘𝟙ω′.≤ 𝟘𝟙ω′.nr (tr′ p) (tr′ r) z₁ s₁ n₁ →
      ∃₃ λ z₂ s₂ n₂ →
         tr′ z₂ 𝟘𝟙ω′.≤ z₁ × tr′ s₂ 𝟘𝟙ω′.≤ s₁ × tr′ n₂ 𝟘𝟙ω′.≤ n₁ ×
         q E.≤ E.nr p r z₂ s₂ n₂
    tr-≤-nr′ = λ where
      _     𝟘 𝟘 𝟘 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     𝟘 𝟘 ω 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     𝟘 ω 𝟘 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     𝟘 ω ω 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     ω _ _ _ _ _ _  → ω , ω , ω , refl , refl , refl , refl
      false 𝟘 𝟘 𝟘 𝟘 𝟘 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟘 𝟘 ω ()
      false 𝟘 𝟘 𝟘 𝟘 𝟙 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟘 𝟙 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟘 𝟙 ω ()
      false 𝟘 𝟘 𝟘 𝟘 ω 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟘 ω 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟘 ω ω ()
      false 𝟘 𝟘 𝟘 𝟙 𝟘 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟘 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟘 ω ()
      false 𝟘 𝟘 𝟘 𝟙 𝟙 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟙 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟙 ω ()
      false 𝟘 𝟘 𝟘 𝟙 ω 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟙 ω 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟙 ω ω ()
      false 𝟘 𝟘 𝟘 ω 𝟘 𝟘 ()
      false 𝟘 𝟘 𝟘 ω 𝟘 𝟙 ()
      false 𝟘 𝟘 𝟘 ω 𝟘 ω ()
      false 𝟘 𝟘 𝟘 ω 𝟙 𝟘 ()
      false 𝟘 𝟘 𝟘 ω 𝟙 𝟙 ()
      false 𝟘 𝟘 𝟘 ω 𝟙 ω ()
      false 𝟘 𝟘 𝟘 ω ω 𝟘 ()
      false 𝟘 𝟘 𝟘 ω ω 𝟙 ()
      false 𝟘 𝟘 𝟘 ω ω ω ()
      false 𝟘 𝟘 ω 𝟘 𝟘 𝟙 ()
      false 𝟘 𝟘 ω 𝟘 𝟘 ω ()
      false 𝟘 𝟘 ω 𝟘 𝟙 𝟘 ()
      false 𝟘 𝟘 ω 𝟘 𝟙 𝟙 ()
      false 𝟘 𝟘 ω 𝟘 𝟙 ω ()
      false 𝟘 𝟘 ω 𝟘 ω 𝟘 ()
      false 𝟘 𝟘 ω 𝟘 ω 𝟙 ()
      false 𝟘 𝟘 ω 𝟘 ω ω ()
      false 𝟘 𝟘 ω 𝟙 𝟘 𝟘 ()
      false 𝟘 𝟘 ω 𝟙 𝟘 𝟙 ()
      false 𝟘 𝟘 ω 𝟙 𝟘 ω ()
      false 𝟘 𝟘 ω 𝟙 𝟙 𝟘 ()
      false 𝟘 𝟘 ω 𝟙 𝟙 𝟙 ()
      false 𝟘 𝟘 ω 𝟙 𝟙 ω ()
      false 𝟘 𝟘 ω 𝟙 ω 𝟘 ()
      false 𝟘 𝟘 ω 𝟙 ω 𝟙 ()
      false 𝟘 𝟘 ω 𝟙 ω ω ()
      false 𝟘 𝟘 ω ω 𝟘 𝟘 ()
      false 𝟘 𝟘 ω ω 𝟘 𝟙 ()
      false 𝟘 𝟘 ω ω 𝟘 ω ()
      false 𝟘 𝟘 ω ω 𝟙 𝟘 ()
      false 𝟘 𝟘 ω ω 𝟙 𝟙 ()
      false 𝟘 𝟘 ω ω 𝟙 ω ()
      false 𝟘 𝟘 ω ω ω 𝟘 ()
      false 𝟘 𝟘 ω ω ω 𝟙 ()
      false 𝟘 𝟘 ω ω ω ω ()
      false 𝟘 ω 𝟘 𝟘 𝟘 𝟙 ()
      false 𝟘 ω 𝟘 𝟘 𝟘 ω ()
      false 𝟘 ω 𝟘 𝟘 𝟙 𝟘 ()
      false 𝟘 ω 𝟘 𝟘 𝟙 𝟙 ()
      false 𝟘 ω 𝟘 𝟘 𝟙 ω ()
      false 𝟘 ω 𝟘 𝟘 ω 𝟘 ()
      false 𝟘 ω 𝟘 𝟘 ω 𝟙 ()
      false 𝟘 ω 𝟘 𝟘 ω ω ()
      false 𝟘 ω 𝟘 𝟙 𝟘 𝟘 ()
      false 𝟘 ω 𝟘 𝟙 𝟘 𝟙 ()
      false 𝟘 ω 𝟘 𝟙 𝟘 ω ()
      false 𝟘 ω 𝟘 𝟙 𝟙 𝟘 ()
      false 𝟘 ω 𝟘 𝟙 𝟙 𝟙 ()
      false 𝟘 ω 𝟘 𝟙 𝟙 ω ()
      false 𝟘 ω 𝟘 𝟙 ω 𝟘 ()
      false 𝟘 ω 𝟘 𝟙 ω 𝟙 ()
      false 𝟘 ω 𝟘 𝟙 ω ω ()
      false 𝟘 ω 𝟘 ω 𝟘 𝟘 ()
      false 𝟘 ω 𝟘 ω 𝟘 𝟙 ()
      false 𝟘 ω 𝟘 ω 𝟘 ω ()
      false 𝟘 ω 𝟘 ω 𝟙 𝟘 ()
      false 𝟘 ω 𝟘 ω 𝟙 𝟙 ()
      false 𝟘 ω 𝟘 ω 𝟙 ω ()
      false 𝟘 ω 𝟘 ω ω 𝟘 ()
      false 𝟘 ω 𝟘 ω ω 𝟙 ()
      false 𝟘 ω 𝟘 ω ω ω ()
      false 𝟘 ω ω 𝟘 𝟘 𝟙 ()
      false 𝟘 ω ω 𝟘 𝟘 ω ()
      false 𝟘 ω ω 𝟘 𝟙 𝟘 ()
      false 𝟘 ω ω 𝟘 𝟙 𝟙 ()
      false 𝟘 ω ω 𝟘 𝟙 ω ()
      false 𝟘 ω ω 𝟘 ω 𝟘 ()
      false 𝟘 ω ω 𝟘 ω 𝟙 ()
      false 𝟘 ω ω 𝟘 ω ω ()
      false 𝟘 ω ω 𝟙 𝟘 𝟘 ()
      false 𝟘 ω ω 𝟙 𝟘 𝟙 ()
      false 𝟘 ω ω 𝟙 𝟘 ω ()
      false 𝟘 ω ω 𝟙 𝟙 𝟘 ()
      false 𝟘 ω ω 𝟙 𝟙 𝟙 ()
      false 𝟘 ω ω 𝟙 𝟙 ω ()
      false 𝟘 ω ω 𝟙 ω 𝟘 ()
      false 𝟘 ω ω 𝟙 ω 𝟙 ()
      false 𝟘 ω ω 𝟙 ω ω ()
      false 𝟘 ω ω ω 𝟘 𝟘 ()
      false 𝟘 ω ω ω 𝟘 𝟙 ()
      false 𝟘 ω ω ω 𝟘 ω ()
      false 𝟘 ω ω ω 𝟙 𝟘 ()
      false 𝟘 ω ω ω 𝟙 𝟙 ()
      false 𝟘 ω ω ω 𝟙 ω ()
      false 𝟘 ω ω ω ω 𝟘 ()
      false 𝟘 ω ω ω ω 𝟙 ()
      false 𝟘 ω ω ω ω ω ()

  tr⁻¹-monotone : ∀ p q → p 𝟘𝟙ω.≤ q → tr⁻¹ p E.≤ tr⁻¹ q
  tr⁻¹-monotone = λ where
    𝟘 𝟘 _     → refl
    𝟘 𝟙 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
    𝟙 𝟘 _     → refl
    𝟙 𝟙 _     → refl
    ω 𝟘 _     → refl
    ω 𝟙 _     → refl
    ω ω _     → refl

  tr-tr⁻¹≤ : ∀ p → tr′ (tr⁻¹ p) 𝟘𝟙ω.≤ p
  tr-tr⁻¹≤ = λ where
    𝟘 → refl
    𝟙 → refl
    ω → refl

  tr≤→≤tr⁻¹ : ∀ p q → tr′ p 𝟘𝟙ω.≤ q → p E.≤ tr⁻¹ q
  tr≤→≤tr⁻¹ = λ where
    𝟘 𝟘 _     → refl
    𝟘 𝟙 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
    ω 𝟘 _     → refl
    ω 𝟙 _     → refl
    ω ω _     → refl

  tr⁻¹-𝟘∧𝟙 : tr⁻¹ 𝟘𝟙ω.𝟘∧𝟙 ≡ ω
  tr⁻¹-𝟘∧𝟙 = 𝟘𝟙ω.𝟘∧𝟙-elim
    (λ p → tr⁻¹ p ≡ ω)
    (λ _ → refl)
    (λ _ → refl)

  tr⁻¹-∧ : ∀ p q → tr⁻¹ (p 𝟘𝟙ω.∧ q) ≡ tr⁻¹ p E.∧ tr⁻¹ q
  tr⁻¹-∧ = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → tr⁻¹-𝟘∧𝟙
    𝟘 ω → refl
    𝟙 𝟘 → tr⁻¹-𝟘∧𝟙
    𝟙 𝟙 → refl
    𝟙 ω → refl
    ω 𝟘 → refl
    ω 𝟙 → refl
    ω ω → refl

  tr⁻¹-+ : ∀ p q → tr⁻¹ (p 𝟘𝟙ω.+ q) ≡ tr⁻¹ p E.+ tr⁻¹ q
  tr⁻¹-+ = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → refl
    𝟘 ω → refl
    𝟙 𝟘 → refl
    𝟙 𝟙 → refl
    𝟙 ω → refl
    ω 𝟘 → refl
    ω 𝟙 → refl
    ω ω → refl

  tr⁻¹-· : ∀ p q → tr⁻¹ (tr′ p 𝟘𝟙ω.· q) ≡ p E.· tr⁻¹ q
  tr⁻¹-· = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → refl
    𝟘 ω → refl
    ω 𝟘 → refl
    ω 𝟙 → refl
    ω ω → refl

  tr-≤-no-nr :
    ∀ s →
    tr′ p 𝟘𝟙ω.≤ q₁ →
    q₁ 𝟘𝟙ω.≤ q₂ →
    (T (Modality-variant.𝟘ᵐ-allowed v₁) →
     q₁ 𝟘𝟙ω.≤ q₃) →
    (Has-well-behaved-zero 𝟘𝟙ω.Zero-one-many
       𝟘𝟙ω.zero-one-many-semiring-with-meet →
     q₁ 𝟘𝟙ω.≤ q₄) →
    q₁ 𝟘𝟙ω.≤ q₃ 𝟘𝟙ω.+ tr′ r 𝟘𝟙ω.· q₄ 𝟘𝟙ω.+ tr′ s 𝟘𝟙ω.· q₁ →
    ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
       tr′ q₂′ 𝟘𝟙ω.≤ q₂ ×
       tr′ q₃′ 𝟘𝟙ω.≤ q₃ ×
       tr′ q₄′ 𝟘𝟙ω.≤ q₄ ×
       p E.≤ q₁′ ×
       q₁′ E.≤ q₂′ ×
       (T (Modality-variant.𝟘ᵐ-allowed v₂) →
        q₁′ E.≤ q₃′) ×
       (Has-well-behaved-zero Erasure E.erasure-semiring-with-meet →
        q₁′ E.≤ q₄′) ×
       q₁′ E.≤ q₃′ E.+ (r E.· q₄′ E.+ s E.· q₁′)
  tr-≤-no-nr s = →tr-≤-no-nr {s = s}
    (ErasureModality v₁)
    (zero-one-many-modality 𝟙≤𝟘 v₂)
    idᶠ
    (λ _ → 𝟘𝟙ω.zero-one-many-has-well-behaved-zero)
    tr′
    tr⁻¹
    tr⁻¹-monotone
    tr≤→≤tr⁻¹
    tr-tr⁻¹≤
    (λ p q → P₁.≤-reflexive (tr⁻¹-+ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-∧ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-· p q))

-- The function zero-one-many→erasure is a morphism from a
-- zero-one-many-modality modality to an erasure modality if certain
-- assumptions hold. The zero-one-many-modality modality can be
-- defined with either 𝟙 ≤ 𝟘 or 𝟙 ≰ 𝟘.

zero-one-many⇨erasure :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = zero-one-many-modality 𝟙≤𝟘 v₁
      𝕄₂ = ErasureModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ zero-one-many→erasure
zero-one-many⇨erasure {v₂ = v₂} {𝟙≤𝟘 = 𝟙≤𝟘} refl s⇔s = λ where
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                           , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-· {p = p}              → tr-· p _
    .Is-morphism.tr-∧ {p = p}              → ≤-reflexive (tr-∧ p _)
    .Is-morphism.tr-nr {r = r}             → ≤-reflexive
                                               (tr-nr _ r _ _ _)
    .Is-morphism.nr-in-first-iff-in-second → s⇔s
    .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
    .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
      (inj₁ ok) → inj₁ ok
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ 𝟘𝟙ω.zero-one-many-has-well-behaved-zero
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘
  open Graded.Modality.Properties (ErasureModality v₂)

  tr′ = zero-one-many→erasure

  tr-𝟘∧𝟙 : tr′ 𝟘𝟙ω.𝟘∧𝟙 ≡ ω
  tr-𝟘∧𝟙 = 𝟘𝟙ω.𝟘∧𝟙-elim
    (λ p → tr′ p ≡ ω)
    (λ _ → refl)
    (λ _ → refl)

  tr-ω[𝟘∧𝟙] : tr′ (ω 𝟘𝟙ω.· 𝟘𝟙ω.𝟘∧𝟙) ≡ ω
  tr-ω[𝟘∧𝟙] = cong tr′ (𝟘𝟙ω.ω·≢𝟘 𝟘𝟙ω.𝟘∧𝟙≢𝟘)

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-+ : ∀ p q → tr′ (p 𝟘𝟙ω.+ q) ≡ tr′ p E.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 𝟙 = refl
  tr-+ 𝟘 ω = refl
  tr-+ 𝟙 𝟘 = refl
  tr-+ 𝟙 𝟙 = refl
  tr-+ 𝟙 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω 𝟙 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p 𝟘𝟙ω.· q) ≡ tr′ p E.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 𝟙 = refl
  tr-· 𝟘 ω = refl
  tr-· 𝟙 𝟘 = refl
  tr-· 𝟙 𝟙 = refl
  tr-· 𝟙 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω 𝟙 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p 𝟘𝟙ω.∧ q) ≡ tr′ p E.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 𝟙 = tr-𝟘∧𝟙
  tr-∧ 𝟘 ω = refl
  tr-∧ 𝟙 𝟘 = tr-𝟘∧𝟙
  tr-∧ 𝟙 𝟙 = refl
  tr-∧ 𝟙 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω 𝟙 = refl
  tr-∧ ω ω = refl

  tr-nr :
    ∀ p r z s n →
    tr′ (𝟘𝟙ω.nr p r z s n) ≡
    E.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = tr-nr′ _
    where
    tr-nr′ :
      ∀ 𝟙≤𝟘 →
      let module 𝟘𝟙ω′ = ZOM 𝟙≤𝟘 in
      ∀ p r z s n →
      tr′ (𝟘𝟙ω′.nr p r z s n) ≡
      E.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
    tr-nr′ = λ where
      false 𝟘 𝟘 𝟘 𝟘 𝟘 → refl
      false 𝟘 𝟘 𝟘 𝟘 𝟙 → refl
      false 𝟘 𝟘 𝟘 𝟘 ω → refl
      false 𝟘 𝟘 𝟘 𝟙 𝟘 → refl
      false 𝟘 𝟘 𝟘 𝟙 𝟙 → refl
      false 𝟘 𝟘 𝟘 𝟙 ω → refl
      false 𝟘 𝟘 𝟘 ω 𝟘 → refl
      false 𝟘 𝟘 𝟘 ω 𝟙 → refl
      false 𝟘 𝟘 𝟘 ω ω → refl
      false 𝟘 𝟘 𝟙 𝟘 𝟘 → refl
      false 𝟘 𝟘 𝟙 𝟘 𝟙 → refl
      false 𝟘 𝟘 𝟙 𝟘 ω → refl
      false 𝟘 𝟘 𝟙 𝟙 𝟘 → refl
      false 𝟘 𝟘 𝟙 𝟙 𝟙 → refl
      false 𝟘 𝟘 𝟙 𝟙 ω → refl
      false 𝟘 𝟘 𝟙 ω 𝟘 → refl
      false 𝟘 𝟘 𝟙 ω 𝟙 → refl
      false 𝟘 𝟘 𝟙 ω ω → refl
      false 𝟘 𝟘 ω 𝟘 𝟘 → refl
      false 𝟘 𝟘 ω 𝟘 𝟙 → refl
      false 𝟘 𝟘 ω 𝟘 ω → refl
      false 𝟘 𝟘 ω 𝟙 𝟘 → refl
      false 𝟘 𝟘 ω 𝟙 𝟙 → refl
      false 𝟘 𝟘 ω 𝟙 ω → refl
      false 𝟘 𝟘 ω ω 𝟘 → refl
      false 𝟘 𝟘 ω ω 𝟙 → refl
      false 𝟘 𝟘 ω ω ω → refl
      false 𝟘 𝟙 𝟘 𝟘 𝟘 → refl
      false 𝟘 𝟙 𝟘 𝟘 𝟙 → refl
      false 𝟘 𝟙 𝟘 𝟘 ω → refl
      false 𝟘 𝟙 𝟘 𝟙 𝟘 → refl
      false 𝟘 𝟙 𝟘 𝟙 𝟙 → refl
      false 𝟘 𝟙 𝟘 𝟙 ω → refl
      false 𝟘 𝟙 𝟘 ω 𝟘 → refl
      false 𝟘 𝟙 𝟘 ω 𝟙 → refl
      false 𝟘 𝟙 𝟘 ω ω → refl
      false 𝟘 𝟙 𝟙 𝟘 𝟘 → refl
      false 𝟘 𝟙 𝟙 𝟘 𝟙 → refl
      false 𝟘 𝟙 𝟙 𝟘 ω → refl
      false 𝟘 𝟙 𝟙 𝟙 𝟘 → refl
      false 𝟘 𝟙 𝟙 𝟙 𝟙 → refl
      false 𝟘 𝟙 𝟙 𝟙 ω → refl
      false 𝟘 𝟙 𝟙 ω 𝟘 → refl
      false 𝟘 𝟙 𝟙 ω 𝟙 → refl
      false 𝟘 𝟙 𝟙 ω ω → refl
      false 𝟘 𝟙 ω 𝟘 𝟘 → refl
      false 𝟘 𝟙 ω 𝟘 𝟙 → refl
      false 𝟘 𝟙 ω 𝟘 ω → refl
      false 𝟘 𝟙 ω 𝟙 𝟘 → refl
      false 𝟘 𝟙 ω 𝟙 𝟙 → refl
      false 𝟘 𝟙 ω 𝟙 ω → refl
      false 𝟘 𝟙 ω ω 𝟘 → refl
      false 𝟘 𝟙 ω ω 𝟙 → refl
      false 𝟘 𝟙 ω ω ω → refl
      false 𝟘 ω 𝟘 𝟘 𝟘 → refl
      false 𝟘 ω 𝟘 𝟘 𝟙 → refl
      false 𝟘 ω 𝟘 𝟘 ω → refl
      false 𝟘 ω 𝟘 𝟙 𝟘 → refl
      false 𝟘 ω 𝟘 𝟙 𝟙 → refl
      false 𝟘 ω 𝟘 𝟙 ω → refl
      false 𝟘 ω 𝟘 ω 𝟘 → refl
      false 𝟘 ω 𝟘 ω 𝟙 → refl
      false 𝟘 ω 𝟘 ω ω → refl
      false 𝟘 ω 𝟙 𝟘 𝟘 → refl
      false 𝟘 ω 𝟙 𝟘 𝟙 → refl
      false 𝟘 ω 𝟙 𝟘 ω → refl
      false 𝟘 ω 𝟙 𝟙 𝟘 → refl
      false 𝟘 ω 𝟙 𝟙 𝟙 → refl
      false 𝟘 ω 𝟙 𝟙 ω → refl
      false 𝟘 ω 𝟙 ω 𝟘 → refl
      false 𝟘 ω 𝟙 ω 𝟙 → refl
      false 𝟘 ω 𝟙 ω ω → refl
      false 𝟘 ω ω 𝟘 𝟘 → refl
      false 𝟘 ω ω 𝟘 𝟙 → refl
      false 𝟘 ω ω 𝟘 ω → refl
      false 𝟘 ω ω 𝟙 𝟘 → refl
      false 𝟘 ω ω 𝟙 𝟙 → refl
      false 𝟘 ω ω 𝟙 ω → refl
      false 𝟘 ω ω ω 𝟘 → refl
      false 𝟘 ω ω ω 𝟙 → refl
      false 𝟘 ω ω ω ω → refl
      false 𝟙 𝟘 𝟘 𝟘 𝟘 → refl
      false 𝟙 𝟘 𝟘 𝟘 𝟙 → refl
      false 𝟙 𝟘 𝟘 𝟘 ω → refl
      false 𝟙 𝟘 𝟘 𝟙 𝟘 → refl
      false 𝟙 𝟘 𝟘 𝟙 𝟙 → refl
      false 𝟙 𝟘 𝟘 𝟙 ω → refl
      false 𝟙 𝟘 𝟘 ω 𝟘 → refl
      false 𝟙 𝟘 𝟘 ω 𝟙 → refl
      false 𝟙 𝟘 𝟘 ω ω → refl
      false 𝟙 𝟘 𝟙 𝟘 𝟘 → refl
      false 𝟙 𝟘 𝟙 𝟘 𝟙 → refl
      false 𝟙 𝟘 𝟙 𝟘 ω → refl
      false 𝟙 𝟘 𝟙 𝟙 𝟘 → refl
      false 𝟙 𝟘 𝟙 𝟙 𝟙 → refl
      false 𝟙 𝟘 𝟙 𝟙 ω → refl
      false 𝟙 𝟘 𝟙 ω 𝟘 → refl
      false 𝟙 𝟘 𝟙 ω 𝟙 → refl
      false 𝟙 𝟘 𝟙 ω ω → refl
      false 𝟙 𝟘 ω 𝟘 𝟘 → refl
      false 𝟙 𝟘 ω 𝟘 𝟙 → refl
      false 𝟙 𝟘 ω 𝟘 ω → refl
      false 𝟙 𝟘 ω 𝟙 𝟘 → refl
      false 𝟙 𝟘 ω 𝟙 𝟙 → refl
      false 𝟙 𝟘 ω 𝟙 ω → refl
      false 𝟙 𝟘 ω ω 𝟘 → refl
      false 𝟙 𝟘 ω ω 𝟙 → refl
      false 𝟙 𝟘 ω ω ω → refl
      false 𝟙 𝟙 𝟘 𝟘 𝟘 → refl
      false 𝟙 𝟙 𝟘 𝟘 𝟙 → refl
      false 𝟙 𝟙 𝟘 𝟘 ω → refl
      false 𝟙 𝟙 𝟘 𝟙 𝟘 → refl
      false 𝟙 𝟙 𝟘 𝟙 𝟙 → refl
      false 𝟙 𝟙 𝟘 𝟙 ω → refl
      false 𝟙 𝟙 𝟘 ω 𝟘 → refl
      false 𝟙 𝟙 𝟘 ω 𝟙 → refl
      false 𝟙 𝟙 𝟘 ω ω → refl
      false 𝟙 𝟙 𝟙 𝟘 𝟘 → refl
      false 𝟙 𝟙 𝟙 𝟘 𝟙 → refl
      false 𝟙 𝟙 𝟙 𝟘 ω → refl
      false 𝟙 𝟙 𝟙 𝟙 𝟘 → refl
      false 𝟙 𝟙 𝟙 𝟙 𝟙 → refl
      false 𝟙 𝟙 𝟙 𝟙 ω → refl
      false 𝟙 𝟙 𝟙 ω 𝟘 → refl
      false 𝟙 𝟙 𝟙 ω 𝟙 → refl
      false 𝟙 𝟙 𝟙 ω ω → refl
      false 𝟙 𝟙 ω 𝟘 𝟘 → refl
      false 𝟙 𝟙 ω 𝟘 𝟙 → refl
      false 𝟙 𝟙 ω 𝟘 ω → refl
      false 𝟙 𝟙 ω 𝟙 𝟘 → refl
      false 𝟙 𝟙 ω 𝟙 𝟙 → refl
      false 𝟙 𝟙 ω 𝟙 ω → refl
      false 𝟙 𝟙 ω ω 𝟘 → refl
      false 𝟙 𝟙 ω ω 𝟙 → refl
      false 𝟙 𝟙 ω ω ω → refl
      false 𝟙 ω 𝟘 𝟘 𝟘 → refl
      false 𝟙 ω 𝟘 𝟘 𝟙 → refl
      false 𝟙 ω 𝟘 𝟘 ω → refl
      false 𝟙 ω 𝟘 𝟙 𝟘 → refl
      false 𝟙 ω 𝟘 𝟙 𝟙 → refl
      false 𝟙 ω 𝟘 𝟙 ω → refl
      false 𝟙 ω 𝟘 ω 𝟘 → refl
      false 𝟙 ω 𝟘 ω 𝟙 → refl
      false 𝟙 ω 𝟘 ω ω → refl
      false 𝟙 ω 𝟙 𝟘 𝟘 → refl
      false 𝟙 ω 𝟙 𝟘 𝟙 → refl
      false 𝟙 ω 𝟙 𝟘 ω → refl
      false 𝟙 ω 𝟙 𝟙 𝟘 → refl
      false 𝟙 ω 𝟙 𝟙 𝟙 → refl
      false 𝟙 ω 𝟙 𝟙 ω → refl
      false 𝟙 ω 𝟙 ω 𝟘 → refl
      false 𝟙 ω 𝟙 ω 𝟙 → refl
      false 𝟙 ω 𝟙 ω ω → refl
      false 𝟙 ω ω 𝟘 𝟘 → refl
      false 𝟙 ω ω 𝟘 𝟙 → refl
      false 𝟙 ω ω 𝟘 ω → refl
      false 𝟙 ω ω 𝟙 𝟘 → refl
      false 𝟙 ω ω 𝟙 𝟙 → refl
      false 𝟙 ω ω 𝟙 ω → refl
      false 𝟙 ω ω ω 𝟘 → refl
      false 𝟙 ω ω ω 𝟙 → refl
      false 𝟙 ω ω ω ω → refl
      false ω 𝟘 𝟘 𝟘 𝟘 → refl
      false ω 𝟘 𝟘 𝟘 𝟙 → refl
      false ω 𝟘 𝟘 𝟘 ω → refl
      false ω 𝟘 𝟘 𝟙 𝟘 → refl
      false ω 𝟘 𝟘 𝟙 𝟙 → refl
      false ω 𝟘 𝟘 𝟙 ω → refl
      false ω 𝟘 𝟘 ω 𝟘 → refl
      false ω 𝟘 𝟘 ω 𝟙 → refl
      false ω 𝟘 𝟘 ω ω → refl
      false ω 𝟘 𝟙 𝟘 𝟘 → refl
      false ω 𝟘 𝟙 𝟘 𝟙 → refl
      false ω 𝟘 𝟙 𝟘 ω → refl
      false ω 𝟘 𝟙 𝟙 𝟘 → refl
      false ω 𝟘 𝟙 𝟙 𝟙 → refl
      false ω 𝟘 𝟙 𝟙 ω → refl
      false ω 𝟘 𝟙 ω 𝟘 → refl
      false ω 𝟘 𝟙 ω 𝟙 → refl
      false ω 𝟘 𝟙 ω ω → refl
      false ω 𝟘 ω 𝟘 𝟘 → refl
      false ω 𝟘 ω 𝟘 𝟙 → refl
      false ω 𝟘 ω 𝟘 ω → refl
      false ω 𝟘 ω 𝟙 𝟘 → refl
      false ω 𝟘 ω 𝟙 𝟙 → refl
      false ω 𝟘 ω 𝟙 ω → refl
      false ω 𝟘 ω ω 𝟘 → refl
      false ω 𝟘 ω ω 𝟙 → refl
      false ω 𝟘 ω ω ω → refl
      false ω 𝟙 𝟘 𝟘 𝟘 → refl
      false ω 𝟙 𝟘 𝟘 𝟙 → refl
      false ω 𝟙 𝟘 𝟘 ω → refl
      false ω 𝟙 𝟘 𝟙 𝟘 → refl
      false ω 𝟙 𝟘 𝟙 𝟙 → refl
      false ω 𝟙 𝟘 𝟙 ω → refl
      false ω 𝟙 𝟘 ω 𝟘 → refl
      false ω 𝟙 𝟘 ω 𝟙 → refl
      false ω 𝟙 𝟘 ω ω → refl
      false ω 𝟙 𝟙 𝟘 𝟘 → refl
      false ω 𝟙 𝟙 𝟘 𝟙 → refl
      false ω 𝟙 𝟙 𝟘 ω → refl
      false ω 𝟙 𝟙 𝟙 𝟘 → refl
      false ω 𝟙 𝟙 𝟙 𝟙 → refl
      false ω 𝟙 𝟙 𝟙 ω → refl
      false ω 𝟙 𝟙 ω 𝟘 → refl
      false ω 𝟙 𝟙 ω 𝟙 → refl
      false ω 𝟙 𝟙 ω ω → refl
      false ω 𝟙 ω 𝟘 𝟘 → refl
      false ω 𝟙 ω 𝟘 𝟙 → refl
      false ω 𝟙 ω 𝟘 ω → refl
      false ω 𝟙 ω 𝟙 𝟘 → refl
      false ω 𝟙 ω 𝟙 𝟙 → refl
      false ω 𝟙 ω 𝟙 ω → refl
      false ω 𝟙 ω ω 𝟘 → refl
      false ω 𝟙 ω ω 𝟙 → refl
      false ω 𝟙 ω ω ω → refl
      false ω ω 𝟘 𝟘 𝟘 → refl
      false ω ω 𝟘 𝟘 𝟙 → refl
      false ω ω 𝟘 𝟘 ω → refl
      false ω ω 𝟘 𝟙 𝟘 → refl
      false ω ω 𝟘 𝟙 𝟙 → refl
      false ω ω 𝟘 𝟙 ω → refl
      false ω ω 𝟘 ω 𝟘 → refl
      false ω ω 𝟘 ω 𝟙 → refl
      false ω ω 𝟘 ω ω → refl
      false ω ω 𝟙 𝟘 𝟘 → refl
      false ω ω 𝟙 𝟘 𝟙 → refl
      false ω ω 𝟙 𝟘 ω → refl
      false ω ω 𝟙 𝟙 𝟘 → refl
      false ω ω 𝟙 𝟙 𝟙 → refl
      false ω ω 𝟙 𝟙 ω → refl
      false ω ω 𝟙 ω 𝟘 → refl
      false ω ω 𝟙 ω 𝟙 → refl
      false ω ω 𝟙 ω ω → refl
      false ω ω ω 𝟘 𝟘 → refl
      false ω ω ω 𝟘 𝟙 → refl
      false ω ω ω 𝟘 ω → refl
      false ω ω ω 𝟙 𝟘 → refl
      false ω ω ω 𝟙 𝟙 → refl
      false ω ω ω 𝟙 ω → refl
      false ω ω ω ω 𝟘 → refl
      false ω ω ω ω 𝟙 → refl
      false ω ω ω ω ω → refl
      true  𝟘 𝟘 𝟘 𝟘 𝟘 → refl
      true  𝟘 𝟘 𝟘 𝟘 𝟙 → refl
      true  𝟘 𝟘 𝟘 𝟘 ω → refl
      true  𝟘 𝟘 𝟘 𝟙 𝟘 → refl
      true  𝟘 𝟘 𝟘 𝟙 𝟙 → refl
      true  𝟘 𝟘 𝟘 𝟙 ω → refl
      true  𝟘 𝟘 𝟘 ω 𝟘 → refl
      true  𝟘 𝟘 𝟘 ω 𝟙 → refl
      true  𝟘 𝟘 𝟘 ω ω → refl
      true  𝟘 𝟘 𝟙 𝟘 𝟘 → refl
      true  𝟘 𝟘 𝟙 𝟘 𝟙 → refl
      true  𝟘 𝟘 𝟙 𝟘 ω → refl
      true  𝟘 𝟘 𝟙 𝟙 𝟘 → refl
      true  𝟘 𝟘 𝟙 𝟙 𝟙 → refl
      true  𝟘 𝟘 𝟙 𝟙 ω → refl
      true  𝟘 𝟘 𝟙 ω 𝟘 → refl
      true  𝟘 𝟘 𝟙 ω 𝟙 → refl
      true  𝟘 𝟘 𝟙 ω ω → refl
      true  𝟘 𝟘 ω 𝟘 𝟘 → refl
      true  𝟘 𝟘 ω 𝟘 𝟙 → refl
      true  𝟘 𝟘 ω 𝟘 ω → refl
      true  𝟘 𝟘 ω 𝟙 𝟘 → refl
      true  𝟘 𝟘 ω 𝟙 𝟙 → refl
      true  𝟘 𝟘 ω 𝟙 ω → refl
      true  𝟘 𝟘 ω ω 𝟘 → refl
      true  𝟘 𝟘 ω ω 𝟙 → refl
      true  𝟘 𝟘 ω ω ω → refl
      true  𝟘 𝟙 𝟘 𝟘 𝟘 → refl
      true  𝟘 𝟙 𝟘 𝟘 𝟙 → refl
      true  𝟘 𝟙 𝟘 𝟘 ω → refl
      true  𝟘 𝟙 𝟘 𝟙 𝟘 → refl
      true  𝟘 𝟙 𝟘 𝟙 𝟙 → refl
      true  𝟘 𝟙 𝟘 𝟙 ω → refl
      true  𝟘 𝟙 𝟘 ω 𝟘 → refl
      true  𝟘 𝟙 𝟘 ω 𝟙 → refl
      true  𝟘 𝟙 𝟘 ω ω → refl
      true  𝟘 𝟙 𝟙 𝟘 𝟘 → refl
      true  𝟘 𝟙 𝟙 𝟘 𝟙 → refl
      true  𝟘 𝟙 𝟙 𝟘 ω → refl
      true  𝟘 𝟙 𝟙 𝟙 𝟘 → refl
      true  𝟘 𝟙 𝟙 𝟙 𝟙 → refl
      true  𝟘 𝟙 𝟙 𝟙 ω → refl
      true  𝟘 𝟙 𝟙 ω 𝟘 → refl
      true  𝟘 𝟙 𝟙 ω 𝟙 → refl
      true  𝟘 𝟙 𝟙 ω ω → refl
      true  𝟘 𝟙 ω 𝟘 𝟘 → refl
      true  𝟘 𝟙 ω 𝟘 𝟙 → refl
      true  𝟘 𝟙 ω 𝟘 ω → refl
      true  𝟘 𝟙 ω 𝟙 𝟘 → refl
      true  𝟘 𝟙 ω 𝟙 𝟙 → refl
      true  𝟘 𝟙 ω 𝟙 ω → refl
      true  𝟘 𝟙 ω ω 𝟘 → refl
      true  𝟘 𝟙 ω ω 𝟙 → refl
      true  𝟘 𝟙 ω ω ω → refl
      true  𝟘 ω 𝟘 𝟘 𝟘 → refl
      true  𝟘 ω 𝟘 𝟘 𝟙 → refl
      true  𝟘 ω 𝟘 𝟘 ω → refl
      true  𝟘 ω 𝟘 𝟙 𝟘 → refl
      true  𝟘 ω 𝟘 𝟙 𝟙 → refl
      true  𝟘 ω 𝟘 𝟙 ω → refl
      true  𝟘 ω 𝟘 ω 𝟘 → refl
      true  𝟘 ω 𝟘 ω 𝟙 → refl
      true  𝟘 ω 𝟘 ω ω → refl
      true  𝟘 ω 𝟙 𝟘 𝟘 → refl
      true  𝟘 ω 𝟙 𝟘 𝟙 → refl
      true  𝟘 ω 𝟙 𝟘 ω → refl
      true  𝟘 ω 𝟙 𝟙 𝟘 → refl
      true  𝟘 ω 𝟙 𝟙 𝟙 → refl
      true  𝟘 ω 𝟙 𝟙 ω → refl
      true  𝟘 ω 𝟙 ω 𝟘 → refl
      true  𝟘 ω 𝟙 ω 𝟙 → refl
      true  𝟘 ω 𝟙 ω ω → refl
      true  𝟘 ω ω 𝟘 𝟘 → refl
      true  𝟘 ω ω 𝟘 𝟙 → refl
      true  𝟘 ω ω 𝟘 ω → refl
      true  𝟘 ω ω 𝟙 𝟘 → refl
      true  𝟘 ω ω 𝟙 𝟙 → refl
      true  𝟘 ω ω 𝟙 ω → refl
      true  𝟘 ω ω ω 𝟘 → refl
      true  𝟘 ω ω ω 𝟙 → refl
      true  𝟘 ω ω ω ω → refl
      true  𝟙 𝟘 𝟘 𝟘 𝟘 → refl
      true  𝟙 𝟘 𝟘 𝟘 𝟙 → refl
      true  𝟙 𝟘 𝟘 𝟘 ω → refl
      true  𝟙 𝟘 𝟘 𝟙 𝟘 → refl
      true  𝟙 𝟘 𝟘 𝟙 𝟙 → refl
      true  𝟙 𝟘 𝟘 𝟙 ω → refl
      true  𝟙 𝟘 𝟘 ω 𝟘 → refl
      true  𝟙 𝟘 𝟘 ω 𝟙 → refl
      true  𝟙 𝟘 𝟘 ω ω → refl
      true  𝟙 𝟘 𝟙 𝟘 𝟘 → refl
      true  𝟙 𝟘 𝟙 𝟘 𝟙 → refl
      true  𝟙 𝟘 𝟙 𝟘 ω → refl
      true  𝟙 𝟘 𝟙 𝟙 𝟘 → refl
      true  𝟙 𝟘 𝟙 𝟙 𝟙 → refl
      true  𝟙 𝟘 𝟙 𝟙 ω → refl
      true  𝟙 𝟘 𝟙 ω 𝟘 → refl
      true  𝟙 𝟘 𝟙 ω 𝟙 → refl
      true  𝟙 𝟘 𝟙 ω ω → refl
      true  𝟙 𝟘 ω 𝟘 𝟘 → refl
      true  𝟙 𝟘 ω 𝟘 𝟙 → refl
      true  𝟙 𝟘 ω 𝟘 ω → refl
      true  𝟙 𝟘 ω 𝟙 𝟘 → refl
      true  𝟙 𝟘 ω 𝟙 𝟙 → refl
      true  𝟙 𝟘 ω 𝟙 ω → refl
      true  𝟙 𝟘 ω ω 𝟘 → refl
      true  𝟙 𝟘 ω ω 𝟙 → refl
      true  𝟙 𝟘 ω ω ω → refl
      true  𝟙 𝟙 𝟘 𝟘 𝟘 → refl
      true  𝟙 𝟙 𝟘 𝟘 𝟙 → refl
      true  𝟙 𝟙 𝟘 𝟘 ω → refl
      true  𝟙 𝟙 𝟘 𝟙 𝟘 → refl
      true  𝟙 𝟙 𝟘 𝟙 𝟙 → refl
      true  𝟙 𝟙 𝟘 𝟙 ω → refl
      true  𝟙 𝟙 𝟘 ω 𝟘 → refl
      true  𝟙 𝟙 𝟘 ω 𝟙 → refl
      true  𝟙 𝟙 𝟘 ω ω → refl
      true  𝟙 𝟙 𝟙 𝟘 𝟘 → refl
      true  𝟙 𝟙 𝟙 𝟘 𝟙 → refl
      true  𝟙 𝟙 𝟙 𝟘 ω → refl
      true  𝟙 𝟙 𝟙 𝟙 𝟘 → refl
      true  𝟙 𝟙 𝟙 𝟙 𝟙 → refl
      true  𝟙 𝟙 𝟙 𝟙 ω → refl
      true  𝟙 𝟙 𝟙 ω 𝟘 → refl
      true  𝟙 𝟙 𝟙 ω 𝟙 → refl
      true  𝟙 𝟙 𝟙 ω ω → refl
      true  𝟙 𝟙 ω 𝟘 𝟘 → refl
      true  𝟙 𝟙 ω 𝟘 𝟙 → refl
      true  𝟙 𝟙 ω 𝟘 ω → refl
      true  𝟙 𝟙 ω 𝟙 𝟘 → refl
      true  𝟙 𝟙 ω 𝟙 𝟙 → refl
      true  𝟙 𝟙 ω 𝟙 ω → refl
      true  𝟙 𝟙 ω ω 𝟘 → refl
      true  𝟙 𝟙 ω ω 𝟙 → refl
      true  𝟙 𝟙 ω ω ω → refl
      true  𝟙 ω 𝟘 𝟘 𝟘 → refl
      true  𝟙 ω 𝟘 𝟘 𝟙 → refl
      true  𝟙 ω 𝟘 𝟘 ω → refl
      true  𝟙 ω 𝟘 𝟙 𝟘 → refl
      true  𝟙 ω 𝟘 𝟙 𝟙 → refl
      true  𝟙 ω 𝟘 𝟙 ω → refl
      true  𝟙 ω 𝟘 ω 𝟘 → refl
      true  𝟙 ω 𝟘 ω 𝟙 → refl
      true  𝟙 ω 𝟘 ω ω → refl
      true  𝟙 ω 𝟙 𝟘 𝟘 → refl
      true  𝟙 ω 𝟙 𝟘 𝟙 → refl
      true  𝟙 ω 𝟙 𝟘 ω → refl
      true  𝟙 ω 𝟙 𝟙 𝟘 → refl
      true  𝟙 ω 𝟙 𝟙 𝟙 → refl
      true  𝟙 ω 𝟙 𝟙 ω → refl
      true  𝟙 ω 𝟙 ω 𝟘 → refl
      true  𝟙 ω 𝟙 ω 𝟙 → refl
      true  𝟙 ω 𝟙 ω ω → refl
      true  𝟙 ω ω 𝟘 𝟘 → refl
      true  𝟙 ω ω 𝟘 𝟙 → refl
      true  𝟙 ω ω 𝟘 ω → refl
      true  𝟙 ω ω 𝟙 𝟘 → refl
      true  𝟙 ω ω 𝟙 𝟙 → refl
      true  𝟙 ω ω 𝟙 ω → refl
      true  𝟙 ω ω ω 𝟘 → refl
      true  𝟙 ω ω ω 𝟙 → refl
      true  𝟙 ω ω ω ω → refl
      true  ω 𝟘 𝟘 𝟘 𝟘 → refl
      true  ω 𝟘 𝟘 𝟘 𝟙 → refl
      true  ω 𝟘 𝟘 𝟘 ω → refl
      true  ω 𝟘 𝟘 𝟙 𝟘 → refl
      true  ω 𝟘 𝟘 𝟙 𝟙 → refl
      true  ω 𝟘 𝟘 𝟙 ω → refl
      true  ω 𝟘 𝟘 ω 𝟘 → refl
      true  ω 𝟘 𝟘 ω 𝟙 → refl
      true  ω 𝟘 𝟘 ω ω → refl
      true  ω 𝟘 𝟙 𝟘 𝟘 → refl
      true  ω 𝟘 𝟙 𝟘 𝟙 → refl
      true  ω 𝟘 𝟙 𝟘 ω → refl
      true  ω 𝟘 𝟙 𝟙 𝟘 → refl
      true  ω 𝟘 𝟙 𝟙 𝟙 → refl
      true  ω 𝟘 𝟙 𝟙 ω → refl
      true  ω 𝟘 𝟙 ω 𝟘 → refl
      true  ω 𝟘 𝟙 ω 𝟙 → refl
      true  ω 𝟘 𝟙 ω ω → refl
      true  ω 𝟘 ω 𝟘 𝟘 → refl
      true  ω 𝟘 ω 𝟘 𝟙 → refl
      true  ω 𝟘 ω 𝟘 ω → refl
      true  ω 𝟘 ω 𝟙 𝟘 → refl
      true  ω 𝟘 ω 𝟙 𝟙 → refl
      true  ω 𝟘 ω 𝟙 ω → refl
      true  ω 𝟘 ω ω 𝟘 → refl
      true  ω 𝟘 ω ω 𝟙 → refl
      true  ω 𝟘 ω ω ω → refl
      true  ω 𝟙 𝟘 𝟘 𝟘 → refl
      true  ω 𝟙 𝟘 𝟘 𝟙 → refl
      true  ω 𝟙 𝟘 𝟘 ω → refl
      true  ω 𝟙 𝟘 𝟙 𝟘 → refl
      true  ω 𝟙 𝟘 𝟙 𝟙 → refl
      true  ω 𝟙 𝟘 𝟙 ω → refl
      true  ω 𝟙 𝟘 ω 𝟘 → refl
      true  ω 𝟙 𝟘 ω 𝟙 → refl
      true  ω 𝟙 𝟘 ω ω → refl
      true  ω 𝟙 𝟙 𝟘 𝟘 → refl
      true  ω 𝟙 𝟙 𝟘 𝟙 → refl
      true  ω 𝟙 𝟙 𝟘 ω → refl
      true  ω 𝟙 𝟙 𝟙 𝟘 → refl
      true  ω 𝟙 𝟙 𝟙 𝟙 → refl
      true  ω 𝟙 𝟙 𝟙 ω → refl
      true  ω 𝟙 𝟙 ω 𝟘 → refl
      true  ω 𝟙 𝟙 ω 𝟙 → refl
      true  ω 𝟙 𝟙 ω ω → refl
      true  ω 𝟙 ω 𝟘 𝟘 → refl
      true  ω 𝟙 ω 𝟘 𝟙 → refl
      true  ω 𝟙 ω 𝟘 ω → refl
      true  ω 𝟙 ω 𝟙 𝟘 → refl
      true  ω 𝟙 ω 𝟙 𝟙 → refl
      true  ω 𝟙 ω 𝟙 ω → refl
      true  ω 𝟙 ω ω 𝟘 → refl
      true  ω 𝟙 ω ω 𝟙 → refl
      true  ω 𝟙 ω ω ω → refl
      true  ω ω 𝟘 𝟘 𝟘 → refl
      true  ω ω 𝟘 𝟘 𝟙 → refl
      true  ω ω 𝟘 𝟘 ω → refl
      true  ω ω 𝟘 𝟙 𝟘 → refl
      true  ω ω 𝟘 𝟙 𝟙 → refl
      true  ω ω 𝟘 𝟙 ω → refl
      true  ω ω 𝟘 ω 𝟘 → refl
      true  ω ω 𝟘 ω 𝟙 → refl
      true  ω ω 𝟘 ω ω → refl
      true  ω ω 𝟙 𝟘 𝟘 → refl
      true  ω ω 𝟙 𝟘 𝟙 → refl
      true  ω ω 𝟙 𝟘 ω → refl
      true  ω ω 𝟙 𝟙 𝟘 → refl
      true  ω ω 𝟙 𝟙 𝟙 → refl
      true  ω ω 𝟙 𝟙 ω → refl
      true  ω ω 𝟙 ω 𝟘 → refl
      true  ω ω 𝟙 ω 𝟙 → refl
      true  ω ω 𝟙 ω ω → refl
      true  ω ω ω 𝟘 𝟘 → refl
      true  ω ω ω 𝟘 𝟙 → refl
      true  ω ω ω 𝟘 ω → refl
      true  ω ω ω 𝟙 𝟘 → refl
      true  ω ω ω 𝟙 𝟙 → refl
      true  ω ω ω 𝟙 ω → refl
      true  ω ω ω ω 𝟘 → refl
      true  ω ω ω ω 𝟙 → refl
      true  ω ω ω ω ω → refl

-- The function zero-one-many→erasure is not an order embedding from a
-- zero-one-many-modality modality to an erasure modality.

¬zero-one-many⇨erasure :
  ¬ Is-order-embedding
      (zero-one-many-modality 𝟙≤𝟘 v₁)
      (ErasureModality v₂)
      zero-one-many→erasure
¬zero-one-many⇨erasure m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ω} refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a linear types modality if certain assumptions
-- hold.

erasure⇨linearity :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = ErasureModality v₁
      𝕄₂ = linearityModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ erasure→zero-one-many
erasure⇨linearity = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from a linear
-- types modality to an erasure modality if certain assumptions hold.

linearity⇨erasure :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = linearityModality v₁
      𝕄₂ = ErasureModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ zero-one-many→erasure
linearity⇨erasure = zero-one-many⇨erasure

-- The function zero-one-many→erasure is not an order embedding from a
-- linear types modality to an erasure modality.

¬linearity⇨erasure :
  ¬ Is-order-embedding (linearityModality v₁) (ErasureModality v₂)
      zero-one-many→erasure
¬linearity⇨erasure = ¬zero-one-many⇨erasure

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to an affine types modality if certain assumptions
-- hold.

erasure⇨affine :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = ErasureModality v₁
      𝕄₂ = affineModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ erasure→zero-one-many
erasure⇨affine = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from an affine
-- types modality to an erasure modality if certain assumptions hold.

affine⇨erasure :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = affineModality v₁
      𝕄₂ = ErasureModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ zero-one-many→erasure
affine⇨erasure = zero-one-many⇨erasure

-- The function zero-one-many→erasure is not an order embedding from
-- an affine types modality to an erasure modality.

¬affine⇨erasure :
  ¬ Is-order-embedding (affineModality v₁) (ErasureModality v₂)
      zero-one-many→erasure
¬affine⇨erasure = ¬zero-one-many⇨erasure

-- The function linearity→linear-or-affine is an order embedding from
-- a linear types modality to a linear or affine types modality if
-- certain assumptions hold.

linearity⇨linear-or-affine :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = linearityModality v₁
      𝕄₂ = linear-or-affine v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ linearity→linear-or-affine
linearity⇨linear-or-affine {v₁ = v₁} {v₂ = v₂} refl s⇔s = λ where
    .Is-order-embedding.trivial not-ok ok   → ⊥-elim (not-ok ok)
    .Is-order-embedding.trivial-⊎-tr-𝟘      → inj₂ refl
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-≤-nr {r = r}     → tr-≤-nr _ _ r _ _ _
    .Is-order-embedding.tr-≤-no-nr {s = s}  → tr-≤-no-nr s
    .Is-order-embedding.tr-order-reflecting → tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism         → λ where
      .Is-morphism.tr-𝟘-≤                    → refl
      .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                             , λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                      → refl
      .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-·                      → tr-· _ _
      .Is-morphism.tr-∧                      → tr-∧ _ _
      .Is-morphism.tr-nr {r = r}             → tr-nr _ r _ _ _
      .Is-morphism.nr-in-first-iff-in-second → s⇔s
      .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
      .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
        (inj₁ ok) → inj₁ ok
      .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ (L.linearity-has-well-behaved-zero v₂)
  where
  module P₁ = Graded.Modality.Properties (linearityModality v₁)
  open Graded.Modality.Properties (linear-or-affine v₂)

  tr′  = linearity→linear-or-affine
  tr⁻¹ = linear-or-affine→linearity

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-≤-𝟙 : ∀ p → tr′ p LA.≤ 𝟙 → p L.≤ 𝟙
  tr-≤-𝟙 𝟙 _ = refl
  tr-≤-𝟙 ω _ = refl

  tr-+ : ∀ p q → tr′ (p L.+ q) ≡ tr′ p LA.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 𝟙 = refl
  tr-+ 𝟘 ω = refl
  tr-+ 𝟙 𝟘 = refl
  tr-+ 𝟙 𝟙 = refl
  tr-+ 𝟙 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω 𝟙 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p L.· q) ≡ tr′ p LA.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 𝟙 = refl
  tr-· 𝟘 ω = refl
  tr-· 𝟙 𝟘 = refl
  tr-· 𝟙 𝟙 = refl
  tr-· 𝟙 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω 𝟙 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p L.∧ q) LA.≤ tr′ p LA.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 𝟙 = ≤-refl
  tr-∧ 𝟘 ω = refl
  tr-∧ 𝟙 𝟘 = ≤-refl
  tr-∧ 𝟙 𝟙 = refl
  tr-∧ 𝟙 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω 𝟙 = refl
  tr-∧ ω ω = refl

  tr-nr :
    ∀ p r z s n →
    tr′ (L.nr p r z s n) LA.≤
    LA.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘 𝟘 𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟘 𝟘 𝟙 → refl
    𝟘 𝟘 𝟘 𝟘 ω → refl
    𝟘 𝟘 𝟘 𝟙 𝟘 → refl
    𝟘 𝟘 𝟘 𝟙 𝟙 → refl
    𝟘 𝟘 𝟘 𝟙 ω → refl
    𝟘 𝟘 𝟘 ω 𝟘 → refl
    𝟘 𝟘 𝟘 ω 𝟙 → refl
    𝟘 𝟘 𝟘 ω ω → refl
    𝟘 𝟘 𝟙 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 𝟘 𝟙 → refl
    𝟘 𝟘 𝟙 𝟘 ω → refl
    𝟘 𝟘 𝟙 𝟙 𝟘 → refl
    𝟘 𝟘 𝟙 𝟙 𝟙 → refl
    𝟘 𝟘 𝟙 𝟙 ω → refl
    𝟘 𝟘 𝟙 ω 𝟘 → refl
    𝟘 𝟘 𝟙 ω 𝟙 → refl
    𝟘 𝟘 𝟙 ω ω → refl
    𝟘 𝟘 ω 𝟘 𝟘 → refl
    𝟘 𝟘 ω 𝟘 𝟙 → refl
    𝟘 𝟘 ω 𝟘 ω → refl
    𝟘 𝟘 ω 𝟙 𝟘 → refl
    𝟘 𝟘 ω 𝟙 𝟙 → refl
    𝟘 𝟘 ω 𝟙 ω → refl
    𝟘 𝟘 ω ω 𝟘 → refl
    𝟘 𝟘 ω ω 𝟙 → refl
    𝟘 𝟘 ω ω ω → refl
    𝟘 𝟙 𝟘 𝟘 𝟘 → refl
    𝟘 𝟙 𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 𝟘 ω → refl
    𝟘 𝟙 𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟘 𝟙 𝟙 → refl
    𝟘 𝟙 𝟘 𝟙 ω → refl
    𝟘 𝟙 𝟘 ω 𝟘 → refl
    𝟘 𝟙 𝟘 ω 𝟙 → refl
    𝟘 𝟙 𝟘 ω ω → refl
    𝟘 𝟙 𝟙 𝟘 𝟘 → refl
    𝟘 𝟙 𝟙 𝟘 𝟙 → refl
    𝟘 𝟙 𝟙 𝟘 ω → refl
    𝟘 𝟙 𝟙 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 𝟙 ω → refl
    𝟘 𝟙 𝟙 ω 𝟘 → refl
    𝟘 𝟙 𝟙 ω 𝟙 → refl
    𝟘 𝟙 𝟙 ω ω → refl
    𝟘 𝟙 ω 𝟘 𝟘 → refl
    𝟘 𝟙 ω 𝟘 𝟙 → refl
    𝟘 𝟙 ω 𝟘 ω → refl
    𝟘 𝟙 ω 𝟙 𝟘 → refl
    𝟘 𝟙 ω 𝟙 𝟙 → refl
    𝟘 𝟙 ω 𝟙 ω → refl
    𝟘 𝟙 ω ω 𝟘 → refl
    𝟘 𝟙 ω ω 𝟙 → refl
    𝟘 𝟙 ω ω ω → refl
    𝟘 ω 𝟘 𝟘 𝟘 → refl
    𝟘 ω 𝟘 𝟘 𝟙 → refl
    𝟘 ω 𝟘 𝟘 ω → refl
    𝟘 ω 𝟘 𝟙 𝟘 → refl
    𝟘 ω 𝟘 𝟙 𝟙 → refl
    𝟘 ω 𝟘 𝟙 ω → refl
    𝟘 ω 𝟘 ω 𝟘 → refl
    𝟘 ω 𝟘 ω 𝟙 → refl
    𝟘 ω 𝟘 ω ω → refl
    𝟘 ω 𝟙 𝟘 𝟘 → refl
    𝟘 ω 𝟙 𝟘 𝟙 → refl
    𝟘 ω 𝟙 𝟘 ω → refl
    𝟘 ω 𝟙 𝟙 𝟘 → refl
    𝟘 ω 𝟙 𝟙 𝟙 → refl
    𝟘 ω 𝟙 𝟙 ω → refl
    𝟘 ω 𝟙 ω 𝟘 → refl
    𝟘 ω 𝟙 ω 𝟙 → refl
    𝟘 ω 𝟙 ω ω → refl
    𝟘 ω ω 𝟘 𝟘 → refl
    𝟘 ω ω 𝟘 𝟙 → refl
    𝟘 ω ω 𝟘 ω → refl
    𝟘 ω ω 𝟙 𝟘 → refl
    𝟘 ω ω 𝟙 𝟙 → refl
    𝟘 ω ω 𝟙 ω → refl
    𝟘 ω ω ω 𝟘 → refl
    𝟘 ω ω ω 𝟙 → refl
    𝟘 ω ω ω ω → refl
    𝟙 𝟘 𝟘 𝟘 𝟘 → refl
    𝟙 𝟘 𝟘 𝟘 𝟙 → refl
    𝟙 𝟘 𝟘 𝟘 ω → refl
    𝟙 𝟘 𝟘 𝟙 𝟘 → refl
    𝟙 𝟘 𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 𝟙 ω → refl
    𝟙 𝟘 𝟘 ω 𝟘 → refl
    𝟙 𝟘 𝟘 ω 𝟙 → refl
    𝟙 𝟘 𝟘 ω ω → refl
    𝟙 𝟘 𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 𝟘 𝟙 → refl
    𝟙 𝟘 𝟙 𝟘 ω → refl
    𝟙 𝟘 𝟙 𝟙 𝟘 → refl
    𝟙 𝟘 𝟙 𝟙 𝟙 → refl
    𝟙 𝟘 𝟙 𝟙 ω → refl
    𝟙 𝟘 𝟙 ω 𝟘 → refl
    𝟙 𝟘 𝟙 ω 𝟙 → refl
    𝟙 𝟘 𝟙 ω ω → refl
    𝟙 𝟘 ω 𝟘 𝟘 → refl
    𝟙 𝟘 ω 𝟘 𝟙 → refl
    𝟙 𝟘 ω 𝟘 ω → refl
    𝟙 𝟘 ω 𝟙 𝟘 → refl
    𝟙 𝟘 ω 𝟙 𝟙 → refl
    𝟙 𝟘 ω 𝟙 ω → refl
    𝟙 𝟘 ω ω 𝟘 → refl
    𝟙 𝟘 ω ω 𝟙 → refl
    𝟙 𝟘 ω ω ω → refl
    𝟙 𝟙 𝟘 𝟘 𝟘 → refl
    𝟙 𝟙 𝟘 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 𝟘 ω → refl
    𝟙 𝟙 𝟘 𝟙 𝟘 → refl
    𝟙 𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟙 𝟘 𝟙 ω → refl
    𝟙 𝟙 𝟘 ω 𝟘 → refl
    𝟙 𝟙 𝟘 ω 𝟙 → refl
    𝟙 𝟙 𝟘 ω ω → refl
    𝟙 𝟙 𝟙 𝟘 𝟘 → refl
    𝟙 𝟙 𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 𝟙 𝟙 ω → refl
    𝟙 𝟙 𝟙 ω 𝟘 → refl
    𝟙 𝟙 𝟙 ω 𝟙 → refl
    𝟙 𝟙 𝟙 ω ω → refl
    𝟙 𝟙 ω 𝟘 𝟘 → refl
    𝟙 𝟙 ω 𝟘 𝟙 → refl
    𝟙 𝟙 ω 𝟘 ω → refl
    𝟙 𝟙 ω 𝟙 𝟘 → refl
    𝟙 𝟙 ω 𝟙 𝟙 → refl
    𝟙 𝟙 ω 𝟙 ω → refl
    𝟙 𝟙 ω ω 𝟘 → refl
    𝟙 𝟙 ω ω 𝟙 → refl
    𝟙 𝟙 ω ω ω → refl
    𝟙 ω 𝟘 𝟘 𝟘 → refl
    𝟙 ω 𝟘 𝟘 𝟙 → refl
    𝟙 ω 𝟘 𝟘 ω → refl
    𝟙 ω 𝟘 𝟙 𝟘 → refl
    𝟙 ω 𝟘 𝟙 𝟙 → refl
    𝟙 ω 𝟘 𝟙 ω → refl
    𝟙 ω 𝟘 ω 𝟘 → refl
    𝟙 ω 𝟘 ω 𝟙 → refl
    𝟙 ω 𝟘 ω ω → refl
    𝟙 ω 𝟙 𝟘 𝟘 → refl
    𝟙 ω 𝟙 𝟘 𝟙 → refl
    𝟙 ω 𝟙 𝟘 ω → refl
    𝟙 ω 𝟙 𝟙 𝟘 → refl
    𝟙 ω 𝟙 𝟙 𝟙 → refl
    𝟙 ω 𝟙 𝟙 ω → refl
    𝟙 ω 𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 ω 𝟙 → refl
    𝟙 ω 𝟙 ω ω → refl
    𝟙 ω ω 𝟘 𝟘 → refl
    𝟙 ω ω 𝟘 𝟙 → refl
    𝟙 ω ω 𝟘 ω → refl
    𝟙 ω ω 𝟙 𝟘 → refl
    𝟙 ω ω 𝟙 𝟙 → refl
    𝟙 ω ω 𝟙 ω → refl
    𝟙 ω ω ω 𝟘 → refl
    𝟙 ω ω ω 𝟙 → refl
    𝟙 ω ω ω ω → refl
    ω 𝟘 𝟘 𝟘 𝟘 → refl
    ω 𝟘 𝟘 𝟘 𝟙 → refl
    ω 𝟘 𝟘 𝟘 ω → refl
    ω 𝟘 𝟘 𝟙 𝟘 → refl
    ω 𝟘 𝟘 𝟙 𝟙 → refl
    ω 𝟘 𝟘 𝟙 ω → refl
    ω 𝟘 𝟘 ω 𝟘 → refl
    ω 𝟘 𝟘 ω 𝟙 → refl
    ω 𝟘 𝟘 ω ω → refl
    ω 𝟘 𝟙 𝟘 𝟘 → refl
    ω 𝟘 𝟙 𝟘 𝟙 → refl
    ω 𝟘 𝟙 𝟘 ω → refl
    ω 𝟘 𝟙 𝟙 𝟘 → refl
    ω 𝟘 𝟙 𝟙 𝟙 → refl
    ω 𝟘 𝟙 𝟙 ω → refl
    ω 𝟘 𝟙 ω 𝟘 → refl
    ω 𝟘 𝟙 ω 𝟙 → refl
    ω 𝟘 𝟙 ω ω → refl
    ω 𝟘 ω 𝟘 𝟘 → refl
    ω 𝟘 ω 𝟘 𝟙 → refl
    ω 𝟘 ω 𝟘 ω → refl
    ω 𝟘 ω 𝟙 𝟘 → refl
    ω 𝟘 ω 𝟙 𝟙 → refl
    ω 𝟘 ω 𝟙 ω → refl
    ω 𝟘 ω ω 𝟘 → refl
    ω 𝟘 ω ω 𝟙 → refl
    ω 𝟘 ω ω ω → refl
    ω 𝟙 𝟘 𝟘 𝟘 → refl
    ω 𝟙 𝟘 𝟘 𝟙 → refl
    ω 𝟙 𝟘 𝟘 ω → refl
    ω 𝟙 𝟘 𝟙 𝟘 → refl
    ω 𝟙 𝟘 𝟙 𝟙 → refl
    ω 𝟙 𝟘 𝟙 ω → refl
    ω 𝟙 𝟘 ω 𝟘 → refl
    ω 𝟙 𝟘 ω 𝟙 → refl
    ω 𝟙 𝟘 ω ω → refl
    ω 𝟙 𝟙 𝟘 𝟘 → refl
    ω 𝟙 𝟙 𝟘 𝟙 → refl
    ω 𝟙 𝟙 𝟘 ω → refl
    ω 𝟙 𝟙 𝟙 𝟘 → refl
    ω 𝟙 𝟙 𝟙 𝟙 → refl
    ω 𝟙 𝟙 𝟙 ω → refl
    ω 𝟙 𝟙 ω 𝟘 → refl
    ω 𝟙 𝟙 ω 𝟙 → refl
    ω 𝟙 𝟙 ω ω → refl
    ω 𝟙 ω 𝟘 𝟘 → refl
    ω 𝟙 ω 𝟘 𝟙 → refl
    ω 𝟙 ω 𝟘 ω → refl
    ω 𝟙 ω 𝟙 𝟘 → refl
    ω 𝟙 ω 𝟙 𝟙 → refl
    ω 𝟙 ω 𝟙 ω → refl
    ω 𝟙 ω ω 𝟘 → refl
    ω 𝟙 ω ω 𝟙 → refl
    ω 𝟙 ω ω ω → refl
    ω ω 𝟘 𝟘 𝟘 → refl
    ω ω 𝟘 𝟘 𝟙 → refl
    ω ω 𝟘 𝟘 ω → refl
    ω ω 𝟘 𝟙 𝟘 → refl
    ω ω 𝟘 𝟙 𝟙 → refl
    ω ω 𝟘 𝟙 ω → refl
    ω ω 𝟘 ω 𝟘 → refl
    ω ω 𝟘 ω 𝟙 → refl
    ω ω 𝟘 ω ω → refl
    ω ω 𝟙 𝟘 𝟘 → refl
    ω ω 𝟙 𝟘 𝟙 → refl
    ω ω 𝟙 𝟘 ω → refl
    ω ω 𝟙 𝟙 𝟘 → refl
    ω ω 𝟙 𝟙 𝟙 → refl
    ω ω 𝟙 𝟙 ω → refl
    ω ω 𝟙 ω 𝟘 → refl
    ω ω 𝟙 ω 𝟙 → refl
    ω ω 𝟙 ω ω → refl
    ω ω ω 𝟘 𝟘 → refl
    ω ω ω 𝟘 𝟙 → refl
    ω ω ω 𝟘 ω → refl
    ω ω ω 𝟙 𝟘 → refl
    ω ω ω 𝟙 𝟙 → refl
    ω ω ω 𝟙 ω → refl
    ω ω ω ω 𝟘 → refl
    ω ω ω ω 𝟙 → refl
    ω ω ω ω ω → refl

  tr-order-reflecting : ∀ p q → tr′ p LA.≤ tr′ q → p L.≤ q
  tr-order-reflecting 𝟘 𝟘 _ = refl
  tr-order-reflecting 𝟙 𝟙 _ = refl
  tr-order-reflecting ω 𝟘 _ = refl
  tr-order-reflecting ω 𝟙 _ = refl
  tr-order-reflecting ω ω _ = refl

  tr-≤-+ :
    ∀ p q r →
    tr′ p LA.≤ q LA.+ r →
    ∃₂ λ q′ r′ → tr′ q′ LA.≤ q × tr′ r′ LA.≤ r × p L.≤ q′ L.+ r′
  tr-≤-+ 𝟘 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟙 𝟘  𝟙  _  = 𝟘 , 𝟙 , refl , refl , refl
  tr-≤-+ 𝟙 𝟙  𝟘  _  = 𝟙 , 𝟘 , refl , refl , refl
  tr-≤-+ ω _  _  _  = ω , ω , refl , refl , refl
  tr-≤-+ 𝟘 𝟙  𝟙  ()
  tr-≤-+ 𝟘 ≤𝟙 𝟙  ()
  tr-≤-+ 𝟘 ≤ω 𝟙  ()
  tr-≤-+ 𝟙 ≤ω ≤𝟙 ()
  tr-≤-+ 𝟙 ≤ω ≤ω ()

  tr-≤-· :
    ∀ p q r →
    tr′ p LA.≤ tr′ q LA.· r →
    ∃ λ r′ → tr′ r′ LA.≤ r × p L.≤ q L.· r′
  tr-≤-· 𝟘 𝟘 𝟘  _   = ω , refl , refl
  tr-≤-· 𝟘 𝟘 𝟙  _   = ω , refl , refl
  tr-≤-· 𝟘 𝟘 ≤𝟙 _   = ω , refl , refl
  tr-≤-· 𝟘 𝟘 ≤ω _   = ω , refl , refl
  tr-≤-· 𝟘 𝟙 𝟘  _   = 𝟘 , refl , refl
  tr-≤-· 𝟘 ω 𝟘  _   = 𝟘 , refl , refl
  tr-≤-· 𝟙 𝟙 𝟙  _   = 𝟙 , refl , refl
  tr-≤-· ω _ _  _   = ω , refl , refl
  tr-≤-· 𝟙 ω  ≤ω ()

  tr-≤-∧ :
    ∀ p q r →
    tr′ p LA.≤ q LA.∧ r →
    ∃₂ λ q′ r′ → tr′ q′ LA.≤ q × tr′ r′ LA.≤ r × p L.≤ q′ L.∧ r′
  tr-≤-∧ 𝟘 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟙  𝟙  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ ω _  _  _  = ω , ω , refl , refl , refl
  tr-≤-∧ 𝟘 𝟙  𝟙  ()
  tr-≤-∧ 𝟘 ≤𝟙 𝟙  ()
  tr-≤-∧ 𝟙 ≤ω ≤𝟙 ()
  tr-≤-∧ 𝟙 ≤ω ≤ω ()
  tr-≤-∧ 𝟙 ≤ω 𝟘  ()

  tr-≤-nr :
    ∀ q p r z₁ s₁ n₁ →
    tr′ q LA.≤ LA.nr (tr′ p) (tr′ r) z₁ s₁ n₁ →
    ∃₃ λ z₂ s₂ n₂ →
       tr′ z₂ LA.≤ z₁ × tr′ s₂ LA.≤ s₁ × tr′ n₂ LA.≤ n₁ ×
       q L.≤ L.nr p r z₂ s₂ n₂
  tr-≤-nr = λ where
    ω _ _ _  _  _  _  → ω , ω , ω , refl , refl , refl , refl
    𝟘 𝟘 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟘  𝟘  𝟙  _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  𝟘  𝟙  _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 𝟘 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 𝟘 ω 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 ω 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 ω 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 ω 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 ω 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 ω 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 ω 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 ω 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 ω 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 ω 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 ω 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 ω ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 ω ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 ω ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 ω ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 ω ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 ω ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 ω ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 ω ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 ω ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 ω ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 ω ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 ω ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 ω ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 ω ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 ω ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 ω ≤ω ≤ω ≤ω ()
    𝟘 𝟙 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 𝟙 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 𝟙 ω 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 ω 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 ω 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 ω 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 ω 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 ω 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 ω 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 ω 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 ω 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 ω 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 ω 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 ω ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 ω ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 ω ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 ω ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 ω ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 ω ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 ω ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 ω ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 ω ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 ω ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 ω ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 ω ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 ω ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 ω ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 ω ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 ω ≤ω ≤ω ≤ω ()
    𝟘 ω 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 ω 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 ω 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 ω 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 ω 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 ω 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 ω 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 ω 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 ω 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 ω 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 ω 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 ω 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 ω 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 ω 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 ω 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 ω 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 ω 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 ω 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 ω 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 ω 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 ω 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 ω 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 ω 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 ω 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 ω 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 ω 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 ω 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 ω 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 ω 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 ω 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 ω 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 ω 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 ω 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 ω 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 ω 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 ω 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 ω 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 ω 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 ω 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 ω 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 ω 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 ω 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 ω 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 ω 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 ω 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 ω 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 ω ω 𝟘  𝟘  𝟙  ()
    𝟘 ω ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω ω 𝟘  𝟘  ≤ω ()
    𝟘 ω ω 𝟘  𝟙  𝟘  ()
    𝟘 ω ω 𝟘  𝟙  𝟙  ()
    𝟘 ω ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω ω 𝟘  𝟙  ≤ω ()
    𝟘 ω ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω ω 𝟘  ≤ω 𝟘  ()
    𝟘 ω ω 𝟘  ≤ω 𝟙  ()
    𝟘 ω ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω ω 𝟘  ≤ω ≤ω ()
    𝟘 ω ω 𝟙  𝟘  𝟘  ()
    𝟘 ω ω 𝟙  𝟘  𝟙  ()
    𝟘 ω ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω ω 𝟙  𝟘  ≤ω ()
    𝟘 ω ω 𝟙  𝟙  𝟘  ()
    𝟘 ω ω 𝟙  𝟙  𝟙  ()
    𝟘 ω ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω ω 𝟙  𝟙  ≤ω ()
    𝟘 ω ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω ω 𝟙  ≤ω 𝟘  ()
    𝟘 ω ω 𝟙  ≤ω 𝟙  ()
    𝟘 ω ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω ω 𝟙  ≤ω ≤ω ()
    𝟘 ω ω ≤𝟙 𝟘  𝟘  ()
    𝟘 ω ω ≤𝟙 𝟘  𝟙  ()
    𝟘 ω ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω ω ≤𝟙 𝟘  ≤ω ()
    𝟘 ω ω ≤𝟙 𝟙  𝟘  ()
    𝟘 ω ω ≤𝟙 𝟙  𝟙  ()
    𝟘 ω ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω ω ≤𝟙 𝟙  ≤ω ()
    𝟘 ω ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω ω ≤𝟙 ≤ω ≤ω ()
    𝟘 ω ω ≤ω 𝟘  𝟘  ()
    𝟘 ω ω ≤ω 𝟘  𝟙  ()
    𝟘 ω ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω ω ≤ω 𝟘  ≤ω ()
    𝟘 ω ω ≤ω 𝟙  𝟘  ()
    𝟘 ω ω ≤ω 𝟙  𝟙  ()
    𝟘 ω ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω ω ≤ω 𝟙  ≤ω ()
    𝟘 ω ω ≤ω ≤𝟙 𝟘  ()
    𝟘 ω ω ≤ω ≤𝟙 𝟙  ()
    𝟘 ω ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω ω ≤ω ≤𝟙 ≤ω ()
    𝟘 ω ω ≤ω ≤ω 𝟘  ()
    𝟘 ω ω ≤ω ≤ω 𝟙  ()
    𝟘 ω ω ≤ω ≤ω ≤𝟙 ()
    𝟘 ω ω ≤ω ≤ω ≤ω ()
    𝟙 𝟘 𝟘 𝟘  𝟘  𝟘  ()
    𝟙 𝟘 𝟘 𝟘  𝟘  𝟙  ()
    𝟙 𝟘 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 𝟘 𝟘  𝟙  𝟘  ()
    𝟙 𝟘 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 𝟘 𝟙  𝟘  𝟘  ()
    𝟙 𝟘 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 𝟘 𝟙 𝟘  𝟘  𝟘  ()
    𝟙 𝟘 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 𝟘 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 𝟘 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 𝟘 ω 𝟘  𝟘  𝟘  ()
    𝟙 𝟘 ω 𝟘  𝟘  𝟙  ()
    𝟙 𝟘 ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 ω 𝟘  𝟙  𝟘  ()
    𝟙 𝟘 ω 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 ω 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 ω 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 ω 𝟙  𝟘  𝟘  ()
    𝟙 𝟘 ω 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 ω 𝟙  𝟙  𝟘  ()
    𝟙 𝟘 ω 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 ω 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 ω 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 ω ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟘 ω ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 ω ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟘 ω ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 ω ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 ω ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 ω ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 ω ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 ω ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 ω ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 ω ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 ω ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 ω ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 ω ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 ω ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 ω ≤ω ≤ω ≤ω ()
    𝟙 𝟙 𝟘 𝟘  𝟘  𝟘  ()
    𝟙 𝟙 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 𝟘 𝟘  𝟙  𝟘  ()
    𝟙 𝟙 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 𝟘 𝟙  𝟘  𝟘  ()
    𝟙 𝟙 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 𝟙 𝟙 𝟘  𝟘  𝟘  ()
    𝟙 𝟙 𝟙 𝟘  𝟘  𝟙  ()
    𝟙 𝟙 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 𝟙 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 𝟙 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 𝟙 ω 𝟘  𝟘  𝟘  ()
    𝟙 𝟙 ω 𝟘  𝟘  𝟙  ()
    𝟙 𝟙 ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 ω 𝟘  𝟙  𝟘  ()
    𝟙 𝟙 ω 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 ω 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 ω 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 ω 𝟙  𝟘  𝟘  ()
    𝟙 𝟙 ω 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 ω 𝟙  𝟙  𝟘  ()
    𝟙 𝟙 ω 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 ω 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 ω 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 ω ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟙 ω ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 ω ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟙 ω ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 ω ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 ω ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 ω ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 ω ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 ω ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 ω ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 ω ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 ω ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 ω ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 ω ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 ω ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 ω ≤ω ≤ω ≤ω ()
    𝟙 ω 𝟘 𝟘  𝟘  𝟘  ()
    𝟙 ω 𝟘 𝟘  𝟘  𝟙  ()
    𝟙 ω 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 ω 𝟘 𝟘  𝟙  𝟘  ()
    𝟙 ω 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 ω 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 ω 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 ω 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 ω 𝟘 𝟙  𝟘  𝟘  ()
    𝟙 ω 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 ω 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 ω 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 ω 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 ω 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 ω 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 ω 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 ω 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 ω 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 ω 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 ω 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 ω 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 ω 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 ω 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 ω 𝟙 𝟘  𝟘  𝟘  ()
    𝟙 ω 𝟙 𝟘  𝟘  𝟙  ()
    𝟙 ω 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 ω 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 ω 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 ω 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 ω 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 ω 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 ω 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 ω 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 ω 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 ω 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 ω 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 ω 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 ω 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 ω 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 ω 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 ω 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 ω 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 ω 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 ω 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 ω 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 ω 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 ω ω 𝟘  𝟘  𝟘  ()
    𝟙 ω ω 𝟘  𝟘  𝟙  ()
    𝟙 ω ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω ω 𝟘  𝟘  ≤ω ()
    𝟙 ω ω 𝟘  𝟙  𝟘  ()
    𝟙 ω ω 𝟘  𝟙  𝟙  ()
    𝟙 ω ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω ω 𝟘  𝟙  ≤ω ()
    𝟙 ω ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 ω ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω ω 𝟘  ≤ω 𝟘  ()
    𝟙 ω ω 𝟘  ≤ω 𝟙  ()
    𝟙 ω ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω ω 𝟘  ≤ω ≤ω ()
    𝟙 ω ω 𝟙  𝟘  𝟘  ()
    𝟙 ω ω 𝟙  𝟘  𝟙  ()
    𝟙 ω ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω ω 𝟙  𝟘  ≤ω ()
    𝟙 ω ω 𝟙  𝟙  𝟘  ()
    𝟙 ω ω 𝟙  𝟙  𝟙  ()
    𝟙 ω ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω ω 𝟙  𝟙  ≤ω ()
    𝟙 ω ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 ω ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω ω 𝟙  ≤ω 𝟘  ()
    𝟙 ω ω 𝟙  ≤ω 𝟙  ()
    𝟙 ω ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω ω 𝟙  ≤ω ≤ω ()
    𝟙 ω ω ≤𝟙 𝟘  𝟘  ()
    𝟙 ω ω ≤𝟙 𝟘  𝟙  ()
    𝟙 ω ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω ω ≤𝟙 𝟘  ≤ω ()
    𝟙 ω ω ≤𝟙 𝟙  𝟘  ()
    𝟙 ω ω ≤𝟙 𝟙  𝟙  ()
    𝟙 ω ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω ω ≤𝟙 𝟙  ≤ω ()
    𝟙 ω ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 ω ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω ω ≤𝟙 ≤ω ≤ω ()
    𝟙 ω ω ≤ω 𝟘  𝟘  ()
    𝟙 ω ω ≤ω 𝟘  𝟙  ()
    𝟙 ω ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω ω ≤ω 𝟘  ≤ω ()
    𝟙 ω ω ≤ω 𝟙  𝟘  ()
    𝟙 ω ω ≤ω 𝟙  𝟙  ()
    𝟙 ω ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω ω ≤ω 𝟙  ≤ω ()
    𝟙 ω ω ≤ω ≤𝟙 𝟘  ()
    𝟙 ω ω ≤ω ≤𝟙 𝟙  ()
    𝟙 ω ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω ω ≤ω ≤𝟙 ≤ω ()
    𝟙 ω ω ≤ω ≤ω 𝟘  ()
    𝟙 ω ω ≤ω ≤ω 𝟙  ()
    𝟙 ω ω ≤ω ≤ω ≤𝟙 ()
    𝟙 ω ω ≤ω ≤ω ≤ω ()

  tr⁻¹-monotone : ∀ p q → p LA.≤ q → tr⁻¹ p L.≤ tr⁻¹ q
  tr⁻¹-monotone = λ where
    𝟘  𝟘  refl → refl
    𝟙  𝟙  refl → refl
    ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟙  refl → refl
    ≤𝟙 ≤𝟙 refl → refl
    ≤ω _  _    → refl

  tr-tr⁻¹≤ : ∀ p → tr′ (tr⁻¹ p) LA.≤ p
  tr-tr⁻¹≤ = λ where
    𝟘  → refl
    𝟙  → refl
    ≤𝟙 → refl
    ≤ω → refl

  tr≤→≤tr⁻¹ : ∀ p q → tr′ p LA.≤ q → p L.≤ tr⁻¹ q
  tr≤→≤tr⁻¹ = λ where
    𝟘 𝟘 refl → refl
    𝟙 𝟙 refl → refl
    ω _ _    → refl

  tr⁻¹-∧ : ∀ p q → tr⁻¹ (p LA.∧ q) ≡ tr⁻¹ p L.∧ tr⁻¹ q
  tr⁻¹-∧ = λ where
    𝟘  𝟘  → refl
    𝟘  𝟙  → refl
    𝟘  ≤𝟙 → refl
    𝟘  ≤ω → refl
    𝟙  𝟘  → refl
    𝟙  𝟙  → refl
    𝟙  ≤𝟙 → refl
    𝟙  ≤ω → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω _  → refl

  tr⁻¹-+ : ∀ p q → tr⁻¹ (p LA.+ q) ≡ tr⁻¹ p L.+ tr⁻¹ q
  tr⁻¹-+ = λ where
    𝟘  𝟘  → refl
    𝟘  𝟙  → refl
    𝟘  ≤𝟙 → refl
    𝟘  ≤ω → refl
    𝟙  𝟘  → refl
    𝟙  𝟙  → refl
    𝟙  ≤𝟙 → refl
    𝟙  ≤ω → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω 𝟘  → refl
    ≤ω 𝟙  → refl
    ≤ω ≤𝟙 → refl
    ≤ω ≤ω → refl

  tr⁻¹-· : ∀ p q → tr⁻¹ (tr′ p LA.· q) ≡ p L.· tr⁻¹ q
  tr⁻¹-· = λ where
    𝟘 𝟘  → refl
    𝟘 𝟙  → refl
    𝟘 ≤𝟙 → refl
    𝟘 ≤ω → refl
    𝟙 𝟘  → refl
    𝟙 𝟙  → refl
    𝟙 ≤𝟙 → refl
    𝟙 ≤ω → refl
    ω 𝟘  → refl
    ω 𝟙  → refl
    ω ≤𝟙 → refl
    ω ≤ω → refl

  tr-≤-no-nr :
    ∀ s →
    tr′ p LA.≤ q₁ →
    q₁ LA.≤ q₂ →
    (T (Modality-variant.𝟘ᵐ-allowed v₁) →
     q₁ LA.≤ q₃) →
    (Has-well-behaved-zero Linear-or-affine
       LA.linear-or-affine-semiring-with-meet →
     q₁ LA.≤ q₄) →
    q₁ LA.≤ q₃ LA.+ tr′ r LA.· q₄ LA.+ tr′ s LA.· q₁ →
    ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
       tr′ q₂′ LA.≤ q₂ ×
       tr′ q₃′ LA.≤ q₃ ×
       tr′ q₄′ LA.≤ q₄ ×
       p L.≤ q₁′ ×
       q₁′ L.≤ q₂′ ×
       (T (Modality-variant.𝟘ᵐ-allowed v₂) →
        q₁′ L.≤ q₃′) ×
       (Has-well-behaved-zero Linearity
          (Modality.semiring-with-meet (linearityModality v₂)) →
        q₁′ L.≤ q₄′) ×
       q₁′ L.≤ q₃′ L.+ r L.· q₄′ L.+ s L.· q₁′
  tr-≤-no-nr s = →tr-≤-no-nr {s = s}
    (linearityModality v₁)
    (linear-or-affine v₂)
    idᶠ
    (λ _ → LA.linear-or-affine-has-well-behaved-zero)
    tr′
    tr⁻¹
    tr⁻¹-monotone
    tr≤→≤tr⁻¹
    tr-tr⁻¹≤
    (λ p q → P₁.≤-reflexive (tr⁻¹-+ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-∧ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-· p q))

-- The function linear-or-affine→linearity is a morphism from a linear
-- or affine types modality to a linear types modality if certain
-- assumptions hold.

linear-or-affine⇨linearity :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = linear-or-affine v₁
      𝕄₂ = linearityModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ linear-or-affine→linearity
linear-or-affine⇨linearity {v₂ = v₂} refl s⇔s = λ where
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _ , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧                      → ≤-reflexive (tr-∧ _ _)
    .Is-morphism.tr-nr {r = r}             → ≤-reflexive
                                               (tr-nr _ r _ _ _)
    .Is-morphism.nr-in-first-iff-in-second → s⇔s
    .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
    .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
      (inj₁ ok) → inj₁ ok
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ LA.linear-or-affine-has-well-behaved-zero
  where
  open Graded.Modality.Properties (linearityModality v₂)

  tr′ = linear-or-affine→linearity

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-+ : ∀ p q → tr′ (p LA.+ q) ≡ tr′ p L.+ tr′ q
  tr-+ 𝟘  𝟘  = refl
  tr-+ 𝟘  𝟙  = refl
  tr-+ 𝟘  ≤𝟙 = refl
  tr-+ 𝟘  ≤ω = refl
  tr-+ 𝟙  𝟘  = refl
  tr-+ 𝟙  𝟙  = refl
  tr-+ 𝟙  ≤𝟙 = refl
  tr-+ 𝟙  ≤ω = refl
  tr-+ ≤𝟙 𝟘  = refl
  tr-+ ≤𝟙 𝟙  = refl
  tr-+ ≤𝟙 ≤𝟙 = refl
  tr-+ ≤𝟙 ≤ω = refl
  tr-+ ≤ω 𝟘  = refl
  tr-+ ≤ω 𝟙  = refl
  tr-+ ≤ω ≤𝟙 = refl
  tr-+ ≤ω ≤ω = refl

  tr-· : ∀ p q → tr′ (p LA.· q) ≡ tr′ p L.· tr′ q
  tr-· 𝟘  𝟘  = refl
  tr-· 𝟘  𝟙  = refl
  tr-· 𝟘  ≤𝟙 = refl
  tr-· 𝟘  ≤ω = refl
  tr-· 𝟙  𝟘  = refl
  tr-· 𝟙  𝟙  = refl
  tr-· 𝟙  ≤𝟙 = refl
  tr-· 𝟙  ≤ω = refl
  tr-· ≤𝟙 𝟘  = refl
  tr-· ≤𝟙 𝟙  = refl
  tr-· ≤𝟙 ≤𝟙 = refl
  tr-· ≤𝟙 ≤ω = refl
  tr-· ≤ω 𝟘  = refl
  tr-· ≤ω 𝟙  = refl
  tr-· ≤ω ≤𝟙 = refl
  tr-· ≤ω ≤ω = refl

  tr-∧ : ∀ p q → tr′ (p LA.∧ q) ≡ tr′ p L.∧ tr′ q
  tr-∧ 𝟘  𝟘  = refl
  tr-∧ 𝟘  𝟙  = refl
  tr-∧ 𝟘  ≤𝟙 = refl
  tr-∧ 𝟘  ≤ω = refl
  tr-∧ 𝟙  𝟘  = refl
  tr-∧ 𝟙  𝟙  = refl
  tr-∧ 𝟙  ≤𝟙 = refl
  tr-∧ 𝟙  ≤ω = refl
  tr-∧ ≤𝟙 𝟘  = refl
  tr-∧ ≤𝟙 𝟙  = refl
  tr-∧ ≤𝟙 ≤𝟙 = refl
  tr-∧ ≤𝟙 ≤ω = refl
  tr-∧ ≤ω 𝟘  = refl
  tr-∧ ≤ω 𝟙  = refl
  tr-∧ ≤ω ≤𝟙 = refl
  tr-∧ ≤ω ≤ω = refl

  tr-nr :
    ∀ p r z s n →
    tr′ (LA.nr p r z s n) ≡
    L.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘  𝟘  𝟘  𝟘  𝟘  → refl
    𝟘  𝟘  𝟘  𝟘  𝟙  → refl
    𝟘  𝟘  𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟘  𝟘  𝟘  ≤ω → refl
    𝟘  𝟘  𝟘  𝟙  𝟘  → refl
    𝟘  𝟘  𝟘  𝟙  𝟙  → refl
    𝟘  𝟘  𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟘  𝟘  𝟙  ≤ω → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟘  → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟙  → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤ω → refl
    𝟘  𝟘  𝟘  ≤ω 𝟘  → refl
    𝟘  𝟘  𝟘  ≤ω 𝟙  → refl
    𝟘  𝟘  𝟘  ≤ω ≤𝟙 → refl
    𝟘  𝟘  𝟘  ≤ω ≤ω → refl
    𝟘  𝟘  𝟙  𝟘  𝟘  → refl
    𝟘  𝟘  𝟙  𝟘  𝟙  → refl
    𝟘  𝟘  𝟙  𝟘  ≤𝟙 → refl
    𝟘  𝟘  𝟙  𝟘  ≤ω → refl
    𝟘  𝟘  𝟙  𝟙  𝟘  → refl
    𝟘  𝟘  𝟙  𝟙  𝟙  → refl
    𝟘  𝟘  𝟙  𝟙  ≤𝟙 → refl
    𝟘  𝟘  𝟙  𝟙  ≤ω → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟘  → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟙  → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤ω → refl
    𝟘  𝟘  𝟙  ≤ω 𝟘  → refl
    𝟘  𝟘  𝟙  ≤ω 𝟙  → refl
    𝟘  𝟘  𝟙  ≤ω ≤𝟙 → refl
    𝟘  𝟘  𝟙  ≤ω ≤ω → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟘  → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟙  → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤ω → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟘  → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟙  → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤ω → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟘  → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟙  → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤ω → refl
    𝟘  𝟘  ≤ω 𝟘  𝟘  → refl
    𝟘  𝟘  ≤ω 𝟘  𝟙  → refl
    𝟘  𝟘  ≤ω 𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤ω 𝟘  ≤ω → refl
    𝟘  𝟘  ≤ω 𝟙  𝟘  → refl
    𝟘  𝟘  ≤ω 𝟙  𝟙  → refl
    𝟘  𝟘  ≤ω 𝟙  ≤𝟙 → refl
    𝟘  𝟘  ≤ω 𝟙  ≤ω → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟘  → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟙  → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤ω → refl
    𝟘  𝟘  ≤ω ≤ω 𝟘  → refl
    𝟘  𝟘  ≤ω ≤ω 𝟙  → refl
    𝟘  𝟘  ≤ω ≤ω ≤𝟙 → refl
    𝟘  𝟘  ≤ω ≤ω ≤ω → refl
    𝟘  𝟙  𝟘  𝟘  𝟘  → refl
    𝟘  𝟙  𝟘  𝟘  𝟙  → refl
    𝟘  𝟙  𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟙  𝟘  𝟘  ≤ω → refl
    𝟘  𝟙  𝟘  𝟙  𝟘  → refl
    𝟘  𝟙  𝟘  𝟙  𝟙  → refl
    𝟘  𝟙  𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟙  𝟘  𝟙  ≤ω → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟘  → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟙  → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤ω → refl
    𝟘  𝟙  𝟘  ≤ω 𝟘  → refl
    𝟘  𝟙  𝟘  ≤ω 𝟙  → refl
    𝟘  𝟙  𝟘  ≤ω ≤𝟙 → refl
    𝟘  𝟙  𝟘  ≤ω ≤ω → refl
    𝟘  𝟙  𝟙  𝟘  𝟘  → refl
    𝟘  𝟙  𝟙  𝟘  𝟙  → refl
    𝟘  𝟙  𝟙  𝟘  ≤𝟙 → refl
    𝟘  𝟙  𝟙  𝟘  ≤ω → refl
    𝟘  𝟙  𝟙  𝟙  𝟘  → refl
    𝟘  𝟙  𝟙  𝟙  𝟙  → refl
    𝟘  𝟙  𝟙  𝟙  ≤𝟙 → refl
    𝟘  𝟙  𝟙  𝟙  ≤ω → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟘  → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟙  → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤ω → refl
    𝟘  𝟙  𝟙  ≤ω 𝟘  → refl
    𝟘  𝟙  𝟙  ≤ω 𝟙  → refl
    𝟘  𝟙  𝟙  ≤ω ≤𝟙 → refl
    𝟘  𝟙  𝟙  ≤ω ≤ω → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟘  → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟙  → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤ω → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟘  → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟙  → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤ω → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟘  → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟙  → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤ω → refl
    𝟘  𝟙  ≤ω 𝟘  𝟘  → refl
    𝟘  𝟙  ≤ω 𝟘  𝟙  → refl
    𝟘  𝟙  ≤ω 𝟘  ≤𝟙 → refl
    𝟘  𝟙  ≤ω 𝟘  ≤ω → refl
    𝟘  𝟙  ≤ω 𝟙  𝟘  → refl
    𝟘  𝟙  ≤ω 𝟙  𝟙  → refl
    𝟘  𝟙  ≤ω 𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤ω 𝟙  ≤ω → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟘  → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟙  → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤ω → refl
    𝟘  𝟙  ≤ω ≤ω 𝟘  → refl
    𝟘  𝟙  ≤ω ≤ω 𝟙  → refl
    𝟘  𝟙  ≤ω ≤ω ≤𝟙 → refl
    𝟘  𝟙  ≤ω ≤ω ≤ω → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟘  → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟙  → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤ω → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟘  → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟙  → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟘  → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟙  → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤ω → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟘  → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟙  → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤ω → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟘  → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟙  → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟘  → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟙  → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟘  → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟙  → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤ω → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟘  → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟙  → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤ω → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟘  → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟙  → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤ω → refl
    𝟘  ≤ω 𝟘  𝟘  𝟘  → refl
    𝟘  ≤ω 𝟘  𝟘  𝟙  → refl
    𝟘  ≤ω 𝟘  𝟘  ≤𝟙 → refl
    𝟘  ≤ω 𝟘  𝟘  ≤ω → refl
    𝟘  ≤ω 𝟘  𝟙  𝟘  → refl
    𝟘  ≤ω 𝟘  𝟙  𝟙  → refl
    𝟘  ≤ω 𝟘  𝟙  ≤𝟙 → refl
    𝟘  ≤ω 𝟘  𝟙  ≤ω → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟙  → refl
    𝟘  ≤ω 𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤ω 𝟘  ≤ω ≤ω → refl
    𝟘  ≤ω 𝟙  𝟘  𝟘  → refl
    𝟘  ≤ω 𝟙  𝟘  𝟙  → refl
    𝟘  ≤ω 𝟙  𝟘  ≤𝟙 → refl
    𝟘  ≤ω 𝟙  𝟘  ≤ω → refl
    𝟘  ≤ω 𝟙  𝟙  𝟘  → refl
    𝟘  ≤ω 𝟙  𝟙  𝟙  → refl
    𝟘  ≤ω 𝟙  𝟙  ≤𝟙 → refl
    𝟘  ≤ω 𝟙  𝟙  ≤ω → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟘  → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟙  → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟙  → refl
    𝟘  ≤ω 𝟙  ≤ω ≤𝟙 → refl
    𝟘  ≤ω 𝟙  ≤ω ≤ω → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟘  → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟙  → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤ω → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟘  → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟙  → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤ω → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟘  → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟙  → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤ω → refl
    𝟘  ≤ω ≤ω 𝟘  𝟘  → refl
    𝟘  ≤ω ≤ω 𝟘  𝟙  → refl
    𝟘  ≤ω ≤ω 𝟘  ≤𝟙 → refl
    𝟘  ≤ω ≤ω 𝟘  ≤ω → refl
    𝟘  ≤ω ≤ω 𝟙  𝟘  → refl
    𝟘  ≤ω ≤ω 𝟙  𝟙  → refl
    𝟘  ≤ω ≤ω 𝟙  ≤𝟙 → refl
    𝟘  ≤ω ≤ω 𝟙  ≤ω → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟘  → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟙  → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤ω → refl
    𝟘  ≤ω ≤ω ≤ω 𝟘  → refl
    𝟘  ≤ω ≤ω ≤ω 𝟙  → refl
    𝟘  ≤ω ≤ω ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤ω ≤ω ≤ω → refl
    𝟙  𝟘  𝟘  𝟘  𝟘  → refl
    𝟙  𝟘  𝟘  𝟘  𝟙  → refl
    𝟙  𝟘  𝟘  𝟘  ≤𝟙 → refl
    𝟙  𝟘  𝟘  𝟘  ≤ω → refl
    𝟙  𝟘  𝟘  𝟙  𝟘  → refl
    𝟙  𝟘  𝟘  𝟙  𝟙  → refl
    𝟙  𝟘  𝟘  𝟙  ≤𝟙 → refl
    𝟙  𝟘  𝟘  𝟙  ≤ω → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟘  → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟙  → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤ω → refl
    𝟙  𝟘  𝟘  ≤ω 𝟘  → refl
    𝟙  𝟘  𝟘  ≤ω 𝟙  → refl
    𝟙  𝟘  𝟘  ≤ω ≤𝟙 → refl
    𝟙  𝟘  𝟘  ≤ω ≤ω → refl
    𝟙  𝟘  𝟙  𝟘  𝟘  → refl
    𝟙  𝟘  𝟙  𝟘  𝟙  → refl
    𝟙  𝟘  𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟘  𝟙  𝟘  ≤ω → refl
    𝟙  𝟘  𝟙  𝟙  𝟘  → refl
    𝟙  𝟘  𝟙  𝟙  𝟙  → refl
    𝟙  𝟘  𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟘  𝟙  𝟙  ≤ω → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟘  → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟙  → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤ω → refl
    𝟙  𝟘  𝟙  ≤ω 𝟘  → refl
    𝟙  𝟘  𝟙  ≤ω 𝟙  → refl
    𝟙  𝟘  𝟙  ≤ω ≤𝟙 → refl
    𝟙  𝟘  𝟙  ≤ω ≤ω → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟘  → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟙  → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤ω → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟘  → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟙  → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤ω → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟘  → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟙  → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤ω → refl
    𝟙  𝟘  ≤ω 𝟘  𝟘  → refl
    𝟙  𝟘  ≤ω 𝟘  𝟙  → refl
    𝟙  𝟘  ≤ω 𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤ω 𝟘  ≤ω → refl
    𝟙  𝟘  ≤ω 𝟙  𝟘  → refl
    𝟙  𝟘  ≤ω 𝟙  𝟙  → refl
    𝟙  𝟘  ≤ω 𝟙  ≤𝟙 → refl
    𝟙  𝟘  ≤ω 𝟙  ≤ω → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟘  → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟙  → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤ω → refl
    𝟙  𝟘  ≤ω ≤ω 𝟘  → refl
    𝟙  𝟘  ≤ω ≤ω 𝟙  → refl
    𝟙  𝟘  ≤ω ≤ω ≤𝟙 → refl
    𝟙  𝟘  ≤ω ≤ω ≤ω → refl
    𝟙  𝟙  𝟘  𝟘  𝟘  → refl
    𝟙  𝟙  𝟘  𝟘  𝟙  → refl
    𝟙  𝟙  𝟘  𝟘  ≤𝟙 → refl
    𝟙  𝟙  𝟘  𝟘  ≤ω → refl
    𝟙  𝟙  𝟘  𝟙  𝟘  → refl
    𝟙  𝟙  𝟘  𝟙  𝟙  → refl
    𝟙  𝟙  𝟘  𝟙  ≤𝟙 → refl
    𝟙  𝟙  𝟘  𝟙  ≤ω → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟘  → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟙  → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤ω → refl
    𝟙  𝟙  𝟘  ≤ω 𝟘  → refl
    𝟙  𝟙  𝟘  ≤ω 𝟙  → refl
    𝟙  𝟙  𝟘  ≤ω ≤𝟙 → refl
    𝟙  𝟙  𝟘  ≤ω ≤ω → refl
    𝟙  𝟙  𝟙  𝟘  𝟘  → refl
    𝟙  𝟙  𝟙  𝟘  𝟙  → refl
    𝟙  𝟙  𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟙  𝟙  𝟘  ≤ω → refl
    𝟙  𝟙  𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  𝟙  𝟙  ≤ω → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟘  → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟙  → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤ω → refl
    𝟙  𝟙  𝟙  ≤ω 𝟘  → refl
    𝟙  𝟙  𝟙  ≤ω 𝟙  → refl
    𝟙  𝟙  𝟙  ≤ω ≤𝟙 → refl
    𝟙  𝟙  𝟙  ≤ω ≤ω → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟘  → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟙  → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤ω → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟘  → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤ω → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟘  → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟙  → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤ω → refl
    𝟙  𝟙  ≤ω 𝟘  𝟘  → refl
    𝟙  𝟙  ≤ω 𝟘  𝟙  → refl
    𝟙  𝟙  ≤ω 𝟘  ≤𝟙 → refl
    𝟙  𝟙  ≤ω 𝟘  ≤ω → refl
    𝟙  𝟙  ≤ω 𝟙  𝟘  → refl
    𝟙  𝟙  ≤ω 𝟙  𝟙  → refl
    𝟙  𝟙  ≤ω 𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω 𝟙  ≤ω → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟘  → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟙  → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤ω → refl
    𝟙  𝟙  ≤ω ≤ω 𝟘  → refl
    𝟙  𝟙  ≤ω ≤ω 𝟙  → refl
    𝟙  𝟙  ≤ω ≤ω ≤𝟙 → refl
    𝟙  𝟙  ≤ω ≤ω ≤ω → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟘  → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟙  → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤ω → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟘  → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟙  → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟘  → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟙  → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤ω → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟘  → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟙  → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤ω → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟘  → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟙  → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟘  → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟙  → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟘  → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟙  → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤ω → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟘  → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟙  → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤ω → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟘  → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟙  → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤ω → refl
    𝟙  ≤ω 𝟘  𝟘  𝟘  → refl
    𝟙  ≤ω 𝟘  𝟘  𝟙  → refl
    𝟙  ≤ω 𝟘  𝟘  ≤𝟙 → refl
    𝟙  ≤ω 𝟘  𝟘  ≤ω → refl
    𝟙  ≤ω 𝟘  𝟙  𝟘  → refl
    𝟙  ≤ω 𝟘  𝟙  𝟙  → refl
    𝟙  ≤ω 𝟘  𝟙  ≤𝟙 → refl
    𝟙  ≤ω 𝟘  𝟙  ≤ω → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟘  → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟙  → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟙  → refl
    𝟙  ≤ω 𝟘  ≤ω ≤𝟙 → refl
    𝟙  ≤ω 𝟘  ≤ω ≤ω → refl
    𝟙  ≤ω 𝟙  𝟘  𝟘  → refl
    𝟙  ≤ω 𝟙  𝟘  𝟙  → refl
    𝟙  ≤ω 𝟙  𝟘  ≤𝟙 → refl
    𝟙  ≤ω 𝟙  𝟘  ≤ω → refl
    𝟙  ≤ω 𝟙  𝟙  𝟘  → refl
    𝟙  ≤ω 𝟙  𝟙  𝟙  → refl
    𝟙  ≤ω 𝟙  𝟙  ≤𝟙 → refl
    𝟙  ≤ω 𝟙  𝟙  ≤ω → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω 𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω 𝟙  ≤ω ≤ω → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟘  → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟙  → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤ω → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟘  → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟙  → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤ω → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟘  → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤ω → refl
    𝟙  ≤ω ≤ω 𝟘  𝟘  → refl
    𝟙  ≤ω ≤ω 𝟘  𝟙  → refl
    𝟙  ≤ω ≤ω 𝟘  ≤𝟙 → refl
    𝟙  ≤ω ≤ω 𝟘  ≤ω → refl
    𝟙  ≤ω ≤ω 𝟙  𝟘  → refl
    𝟙  ≤ω ≤ω 𝟙  𝟙  → refl
    𝟙  ≤ω ≤ω 𝟙  ≤𝟙 → refl
    𝟙  ≤ω ≤ω 𝟙  ≤ω → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟘  → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟙  → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤ω → refl
    𝟙  ≤ω ≤ω ≤ω 𝟘  → refl
    𝟙  ≤ω ≤ω ≤ω 𝟙  → refl
    𝟙  ≤ω ≤ω ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟙  → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤ω → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟘  → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟙  → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤ω → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟘  → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟙  → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟙  → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤ω → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟘  → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟙  → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤ω → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟘  → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟙  → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟘  → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤ω → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟘  → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟙  → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤ω → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟘  → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟙  → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤ω → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟘  → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟙  → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟙  → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤ω → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟘  → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟙  → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤ω → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟘  → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟙  → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟙  → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤ω → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟘  → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟙  → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟘  → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟙  → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤ω → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟘  → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤ω → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟘  → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟙  → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤ω → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟘  → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟙  → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤ω → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟘  → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟙  → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤ω → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟙  → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤ω → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟘  → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟙  → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤ω → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟘  → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟙  → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤ω → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟙  → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟘  → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟙  → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤ω → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟘  → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟙  → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤ω → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟘  → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤ω → refl
    ≤ω 𝟘  𝟘  𝟘  𝟘  → refl
    ≤ω 𝟘  𝟘  𝟘  𝟙  → refl
    ≤ω 𝟘  𝟘  𝟘  ≤𝟙 → refl
    ≤ω 𝟘  𝟘  𝟘  ≤ω → refl
    ≤ω 𝟘  𝟘  𝟙  𝟘  → refl
    ≤ω 𝟘  𝟘  𝟙  𝟙  → refl
    ≤ω 𝟘  𝟘  𝟙  ≤𝟙 → refl
    ≤ω 𝟘  𝟘  𝟙  ≤ω → refl
    ≤ω 𝟘  𝟘  ≤𝟙 𝟘  → refl
    ≤ω 𝟘  𝟘  ≤𝟙 𝟙  → refl
    ≤ω 𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  𝟘  ≤𝟙 ≤ω → refl
    ≤ω 𝟘  𝟘  ≤ω 𝟘  → refl
    ≤ω 𝟘  𝟘  ≤ω 𝟙  → refl
    ≤ω 𝟘  𝟘  ≤ω ≤𝟙 → refl
    ≤ω 𝟘  𝟘  ≤ω ≤ω → refl
    ≤ω 𝟘  𝟙  𝟘  𝟘  → refl
    ≤ω 𝟘  𝟙  𝟘  𝟙  → refl
    ≤ω 𝟘  𝟙  𝟘  ≤𝟙 → refl
    ≤ω 𝟘  𝟙  𝟘  ≤ω → refl
    ≤ω 𝟘  𝟙  𝟙  𝟘  → refl
    ≤ω 𝟘  𝟙  𝟙  𝟙  → refl
    ≤ω 𝟘  𝟙  𝟙  ≤𝟙 → refl
    ≤ω 𝟘  𝟙  𝟙  ≤ω → refl
    ≤ω 𝟘  𝟙  ≤𝟙 𝟘  → refl
    ≤ω 𝟘  𝟙  ≤𝟙 𝟙  → refl
    ≤ω 𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  𝟙  ≤𝟙 ≤ω → refl
    ≤ω 𝟘  𝟙  ≤ω 𝟘  → refl
    ≤ω 𝟘  𝟙  ≤ω 𝟙  → refl
    ≤ω 𝟘  𝟙  ≤ω ≤𝟙 → refl
    ≤ω 𝟘  𝟙  ≤ω ≤ω → refl
    ≤ω 𝟘  ≤𝟙 𝟘  𝟘  → refl
    ≤ω 𝟘  ≤𝟙 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 𝟘  ≤ω → refl
    ≤ω 𝟘  ≤𝟙 𝟙  𝟘  → refl
    ≤ω 𝟘  ≤𝟙 𝟙  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 𝟙  ≤ω → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω 𝟘  ≤𝟙 ≤ω 𝟘  → refl
    ≤ω 𝟘  ≤𝟙 ≤ω 𝟙  → refl
    ≤ω 𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟘  ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟘  ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟘  ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟘  ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω 𝟙  ≤ω → refl
    ≤ω 𝟘  ≤ω ≤𝟙 𝟘  → refl
    ≤ω 𝟘  ≤ω ≤𝟙 𝟙  → refl
    ≤ω 𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  ≤ω ≤𝟙 ≤ω → refl
    ≤ω 𝟘  ≤ω ≤ω 𝟘  → refl
    ≤ω 𝟘  ≤ω ≤ω 𝟙  → refl
    ≤ω 𝟘  ≤ω ≤ω ≤𝟙 → refl
    ≤ω 𝟘  ≤ω ≤ω ≤ω → refl
    ≤ω 𝟙  𝟘  𝟘  𝟘  → refl
    ≤ω 𝟙  𝟘  𝟘  𝟙  → refl
    ≤ω 𝟙  𝟘  𝟘  ≤𝟙 → refl
    ≤ω 𝟙  𝟘  𝟘  ≤ω → refl
    ≤ω 𝟙  𝟘  𝟙  𝟘  → refl
    ≤ω 𝟙  𝟘  𝟙  𝟙  → refl
    ≤ω 𝟙  𝟘  𝟙  ≤𝟙 → refl
    ≤ω 𝟙  𝟘  𝟙  ≤ω → refl
    ≤ω 𝟙  𝟘  ≤𝟙 𝟘  → refl
    ≤ω 𝟙  𝟘  ≤𝟙 𝟙  → refl
    ≤ω 𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  𝟘  ≤𝟙 ≤ω → refl
    ≤ω 𝟙  𝟘  ≤ω 𝟘  → refl
    ≤ω 𝟙  𝟘  ≤ω 𝟙  → refl
    ≤ω 𝟙  𝟘  ≤ω ≤𝟙 → refl
    ≤ω 𝟙  𝟘  ≤ω ≤ω → refl
    ≤ω 𝟙  𝟙  𝟘  𝟘  → refl
    ≤ω 𝟙  𝟙  𝟘  𝟙  → refl
    ≤ω 𝟙  𝟙  𝟘  ≤𝟙 → refl
    ≤ω 𝟙  𝟙  𝟘  ≤ω → refl
    ≤ω 𝟙  𝟙  𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  𝟙  𝟙  → refl
    ≤ω 𝟙  𝟙  𝟙  ≤𝟙 → refl
    ≤ω 𝟙  𝟙  𝟙  ≤ω → refl
    ≤ω 𝟙  𝟙  ≤𝟙 𝟘  → refl
    ≤ω 𝟙  𝟙  ≤𝟙 𝟙  → refl
    ≤ω 𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  𝟙  ≤𝟙 ≤ω → refl
    ≤ω 𝟙  𝟙  ≤ω 𝟘  → refl
    ≤ω 𝟙  𝟙  ≤ω 𝟙  → refl
    ≤ω 𝟙  𝟙  ≤ω ≤𝟙 → refl
    ≤ω 𝟙  𝟙  ≤ω ≤ω → refl
    ≤ω 𝟙  ≤𝟙 𝟘  𝟘  → refl
    ≤ω 𝟙  ≤𝟙 𝟘  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 𝟘  ≤ω → refl
    ≤ω 𝟙  ≤𝟙 𝟙  𝟘  → refl
    ≤ω 𝟙  ≤𝟙 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 𝟙  ≤ω → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω 𝟙  ≤𝟙 ≤ω 𝟘  → refl
    ≤ω 𝟙  ≤𝟙 ≤ω 𝟙  → refl
    ≤ω 𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟙  ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟙  ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟙  ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟙  ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω 𝟙  ≤ω → refl
    ≤ω 𝟙  ≤ω ≤𝟙 𝟘  → refl
    ≤ω 𝟙  ≤ω ≤𝟙 𝟙  → refl
    ≤ω 𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  ≤ω ≤𝟙 ≤ω → refl
    ≤ω 𝟙  ≤ω ≤ω 𝟘  → refl
    ≤ω 𝟙  ≤ω ≤ω 𝟙  → refl
    ≤ω 𝟙  ≤ω ≤ω ≤𝟙 → refl
    ≤ω 𝟙  ≤ω ≤ω ≤ω → refl
    ≤ω ≤𝟙 𝟘  𝟘  𝟘  → refl
    ≤ω ≤𝟙 𝟘  𝟘  𝟙  → refl
    ≤ω ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  𝟘  ≤ω → refl
    ≤ω ≤𝟙 𝟘  𝟙  𝟘  → refl
    ≤ω ≤𝟙 𝟘  𝟙  𝟙  → refl
    ≤ω ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 𝟘  ≤ω 𝟘  → refl
    ≤ω ≤𝟙 𝟘  ≤ω 𝟙  → refl
    ≤ω ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  ≤ω ≤ω → refl
    ≤ω ≤𝟙 𝟙  𝟘  𝟘  → refl
    ≤ω ≤𝟙 𝟙  𝟘  𝟙  → refl
    ≤ω ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  𝟘  ≤ω → refl
    ≤ω ≤𝟙 𝟙  𝟙  𝟘  → refl
    ≤ω ≤𝟙 𝟙  𝟙  𝟙  → refl
    ≤ω ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 𝟙  ≤ω 𝟘  → refl
    ≤ω ≤𝟙 𝟙  ≤ω 𝟙  → refl
    ≤ω ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  ≤ω ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    ≤ω ≤𝟙 ≤ω 𝟘  𝟘  → refl
    ≤ω ≤𝟙 ≤ω 𝟘  𝟙  → refl
    ≤ω ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω 𝟘  ≤ω → refl
    ≤ω ≤𝟙 ≤ω 𝟙  𝟘  → refl
    ≤ω ≤𝟙 ≤ω 𝟙  𝟙  → refl
    ≤ω ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 ≤ω ≤ω 𝟘  → refl
    ≤ω ≤𝟙 ≤ω ≤ω 𝟙  → refl
    ≤ω ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω ≤ω ≤ω → refl
    ≤ω ≤ω 𝟘  𝟘  𝟘  → refl
    ≤ω ≤ω 𝟘  𝟘  𝟙  → refl
    ≤ω ≤ω 𝟘  𝟘  ≤𝟙 → refl
    ≤ω ≤ω 𝟘  𝟘  ≤ω → refl
    ≤ω ≤ω 𝟘  𝟙  𝟘  → refl
    ≤ω ≤ω 𝟘  𝟙  𝟙  → refl
    ≤ω ≤ω 𝟘  𝟙  ≤𝟙 → refl
    ≤ω ≤ω 𝟘  𝟙  ≤ω → refl
    ≤ω ≤ω 𝟘  ≤𝟙 𝟘  → refl
    ≤ω ≤ω 𝟘  ≤𝟙 𝟙  → refl
    ≤ω ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω 𝟘  ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟘  ≤ω 𝟙  → refl
    ≤ω ≤ω 𝟘  ≤ω ≤𝟙 → refl
    ≤ω ≤ω 𝟘  ≤ω ≤ω → refl
    ≤ω ≤ω 𝟙  𝟘  𝟘  → refl
    ≤ω ≤ω 𝟙  𝟘  𝟙  → refl
    ≤ω ≤ω 𝟙  𝟘  ≤𝟙 → refl
    ≤ω ≤ω 𝟙  𝟘  ≤ω → refl
    ≤ω ≤ω 𝟙  𝟙  𝟘  → refl
    ≤ω ≤ω 𝟙  𝟙  𝟙  → refl
    ≤ω ≤ω 𝟙  𝟙  ≤𝟙 → refl
    ≤ω ≤ω 𝟙  𝟙  ≤ω → refl
    ≤ω ≤ω 𝟙  ≤𝟙 𝟘  → refl
    ≤ω ≤ω 𝟙  ≤𝟙 𝟙  → refl
    ≤ω ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω 𝟙  ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟙  ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  ≤ω 𝟙  → refl
    ≤ω ≤ω 𝟙  ≤ω ≤𝟙 → refl
    ≤ω ≤ω 𝟙  ≤ω ≤ω → refl
    ≤ω ≤ω ≤𝟙 𝟘  𝟘  → refl
    ≤ω ≤ω ≤𝟙 𝟘  𝟙  → refl
    ≤ω ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 𝟘  ≤ω → refl
    ≤ω ≤ω ≤𝟙 𝟙  𝟘  → refl
    ≤ω ≤ω ≤𝟙 𝟙  𝟙  → refl
    ≤ω ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 𝟙  ≤ω → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω ≤ω ≤𝟙 ≤ω 𝟘  → refl
    ≤ω ≤ω ≤𝟙 ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 ≤ω ≤ω → refl
    ≤ω ≤ω ≤ω 𝟘  𝟘  → refl
    ≤ω ≤ω ≤ω 𝟘  𝟙  → refl
    ≤ω ≤ω ≤ω 𝟘  ≤𝟙 → refl
    ≤ω ≤ω ≤ω 𝟘  ≤ω → refl
    ≤ω ≤ω ≤ω 𝟙  𝟘  → refl
    ≤ω ≤ω ≤ω 𝟙  𝟙  → refl
    ≤ω ≤ω ≤ω 𝟙  ≤𝟙 → refl
    ≤ω ≤ω ≤ω 𝟙  ≤ω → refl
    ≤ω ≤ω ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤ω ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω ≤ω ≤ω → refl

-- The function linear-or-affine→linearity is not an order embedding
-- from a linear or affine types modality to a linear types modality.

¬linear-or-affine⇨linearity :
  ¬ Is-order-embedding (linear-or-affine v₁) (linearityModality v₂)
      linear-or-affine→linearity
¬linear-or-affine⇨linearity m =
  case Is-order-embedding.tr-injective m {p = ≤𝟙} {q = ≤ω} refl of λ ()

-- The function affine→linear-or-affine is an order embedding from an
-- affine types modality to a linear or affine types modality if
-- certain assumptions hold.

affine⇨linear-or-affine :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = affineModality v₁
      𝕄₂ = linear-or-affine v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-order-embedding 𝕄₁ 𝕄₂ affine→linear-or-affine
affine⇨linear-or-affine {v₁ = v₁} {v₂ = v₂} refl s⇔s = λ where
    .Is-order-embedding.trivial not-ok ok   → ⊥-elim (not-ok ok)
    .Is-order-embedding.trivial-⊎-tr-𝟘      → inj₂ refl
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-≤-nr {r = r}     → tr-≤-nr _ _ r _ _ _
    .Is-order-embedding.tr-≤-no-nr {s = s}  → tr-≤-no-nr s
    .Is-order-embedding.tr-order-reflecting → tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism         → λ where
      .Is-morphism.tr-𝟘-≤                    → refl
      .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                             , λ { refl → refl }
      .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
      .Is-morphism.tr-𝟙                      → refl
      .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
      .Is-morphism.tr-·                      → tr-· _ _
      .Is-morphism.tr-∧                      → ≤-reflexive (tr-∧ _ _)
      .Is-morphism.tr-nr {r = r}             → ≤-reflexive
                                                 (tr-nr _ r _ _ _)
      .Is-morphism.nr-in-first-iff-in-second → s⇔s
      .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
      .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
        (inj₁ ok) → inj₁ ok
      .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
        inj₁ (A.affine-has-well-behaved-zero v₁)
  where
  module P₁ = Graded.Modality.Properties (affineModality v₁)
  open Graded.Modality.Properties (linear-or-affine v₂)

  tr′  = affine→linear-or-affine
  tr⁻¹ = linear-or-affine→affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-≤-𝟙 : ∀ p → tr′ p LA.≤ 𝟙 → p A.≤ 𝟙
  tr-≤-𝟙 𝟙 _ = refl
  tr-≤-𝟙 ω _ = refl

  tr-+ : ∀ p q → tr′ (p A.+ q) ≡ tr′ p LA.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 𝟙 = refl
  tr-+ 𝟘 ω = refl
  tr-+ 𝟙 𝟘 = refl
  tr-+ 𝟙 𝟙 = refl
  tr-+ 𝟙 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω 𝟙 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p A.· q) ≡ tr′ p LA.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 𝟙 = refl
  tr-· 𝟘 ω = refl
  tr-· 𝟙 𝟘 = refl
  tr-· 𝟙 𝟙 = refl
  tr-· 𝟙 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω 𝟙 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p A.∧ q) ≡ tr′ p LA.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 𝟙 = refl
  tr-∧ 𝟘 ω = refl
  tr-∧ 𝟙 𝟘 = refl
  tr-∧ 𝟙 𝟙 = refl
  tr-∧ 𝟙 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω 𝟙 = refl
  tr-∧ ω ω = refl

  tr-nr :
    ∀ p r z s n →
    tr′ (A.nr p r z s n) ≡
    LA.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘 𝟘 𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟘 𝟘 𝟙 → refl
    𝟘 𝟘 𝟘 𝟘 ω → refl
    𝟘 𝟘 𝟘 𝟙 𝟘 → refl
    𝟘 𝟘 𝟘 𝟙 𝟙 → refl
    𝟘 𝟘 𝟘 𝟙 ω → refl
    𝟘 𝟘 𝟘 ω 𝟘 → refl
    𝟘 𝟘 𝟘 ω 𝟙 → refl
    𝟘 𝟘 𝟘 ω ω → refl
    𝟘 𝟘 𝟙 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 𝟘 𝟙 → refl
    𝟘 𝟘 𝟙 𝟘 ω → refl
    𝟘 𝟘 𝟙 𝟙 𝟘 → refl
    𝟘 𝟘 𝟙 𝟙 𝟙 → refl
    𝟘 𝟘 𝟙 𝟙 ω → refl
    𝟘 𝟘 𝟙 ω 𝟘 → refl
    𝟘 𝟘 𝟙 ω 𝟙 → refl
    𝟘 𝟘 𝟙 ω ω → refl
    𝟘 𝟘 ω 𝟘 𝟘 → refl
    𝟘 𝟘 ω 𝟘 𝟙 → refl
    𝟘 𝟘 ω 𝟘 ω → refl
    𝟘 𝟘 ω 𝟙 𝟘 → refl
    𝟘 𝟘 ω 𝟙 𝟙 → refl
    𝟘 𝟘 ω 𝟙 ω → refl
    𝟘 𝟘 ω ω 𝟘 → refl
    𝟘 𝟘 ω ω 𝟙 → refl
    𝟘 𝟘 ω ω ω → refl
    𝟘 𝟙 𝟘 𝟘 𝟘 → refl
    𝟘 𝟙 𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 𝟘 ω → refl
    𝟘 𝟙 𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟘 𝟙 𝟙 → refl
    𝟘 𝟙 𝟘 𝟙 ω → refl
    𝟘 𝟙 𝟘 ω 𝟘 → refl
    𝟘 𝟙 𝟘 ω 𝟙 → refl
    𝟘 𝟙 𝟘 ω ω → refl
    𝟘 𝟙 𝟙 𝟘 𝟘 → refl
    𝟘 𝟙 𝟙 𝟘 𝟙 → refl
    𝟘 𝟙 𝟙 𝟘 ω → refl
    𝟘 𝟙 𝟙 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 𝟙 ω → refl
    𝟘 𝟙 𝟙 ω 𝟘 → refl
    𝟘 𝟙 𝟙 ω 𝟙 → refl
    𝟘 𝟙 𝟙 ω ω → refl
    𝟘 𝟙 ω 𝟘 𝟘 → refl
    𝟘 𝟙 ω 𝟘 𝟙 → refl
    𝟘 𝟙 ω 𝟘 ω → refl
    𝟘 𝟙 ω 𝟙 𝟘 → refl
    𝟘 𝟙 ω 𝟙 𝟙 → refl
    𝟘 𝟙 ω 𝟙 ω → refl
    𝟘 𝟙 ω ω 𝟘 → refl
    𝟘 𝟙 ω ω 𝟙 → refl
    𝟘 𝟙 ω ω ω → refl
    𝟘 ω 𝟘 𝟘 𝟘 → refl
    𝟘 ω 𝟘 𝟘 𝟙 → refl
    𝟘 ω 𝟘 𝟘 ω → refl
    𝟘 ω 𝟘 𝟙 𝟘 → refl
    𝟘 ω 𝟘 𝟙 𝟙 → refl
    𝟘 ω 𝟘 𝟙 ω → refl
    𝟘 ω 𝟘 ω 𝟘 → refl
    𝟘 ω 𝟘 ω 𝟙 → refl
    𝟘 ω 𝟘 ω ω → refl
    𝟘 ω 𝟙 𝟘 𝟘 → refl
    𝟘 ω 𝟙 𝟘 𝟙 → refl
    𝟘 ω 𝟙 𝟘 ω → refl
    𝟘 ω 𝟙 𝟙 𝟘 → refl
    𝟘 ω 𝟙 𝟙 𝟙 → refl
    𝟘 ω 𝟙 𝟙 ω → refl
    𝟘 ω 𝟙 ω 𝟘 → refl
    𝟘 ω 𝟙 ω 𝟙 → refl
    𝟘 ω 𝟙 ω ω → refl
    𝟘 ω ω 𝟘 𝟘 → refl
    𝟘 ω ω 𝟘 𝟙 → refl
    𝟘 ω ω 𝟘 ω → refl
    𝟘 ω ω 𝟙 𝟘 → refl
    𝟘 ω ω 𝟙 𝟙 → refl
    𝟘 ω ω 𝟙 ω → refl
    𝟘 ω ω ω 𝟘 → refl
    𝟘 ω ω ω 𝟙 → refl
    𝟘 ω ω ω ω → refl
    𝟙 𝟘 𝟘 𝟘 𝟘 → refl
    𝟙 𝟘 𝟘 𝟘 𝟙 → refl
    𝟙 𝟘 𝟘 𝟘 ω → refl
    𝟙 𝟘 𝟘 𝟙 𝟘 → refl
    𝟙 𝟘 𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 𝟙 ω → refl
    𝟙 𝟘 𝟘 ω 𝟘 → refl
    𝟙 𝟘 𝟘 ω 𝟙 → refl
    𝟙 𝟘 𝟘 ω ω → refl
    𝟙 𝟘 𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 𝟘 𝟙 → refl
    𝟙 𝟘 𝟙 𝟘 ω → refl
    𝟙 𝟘 𝟙 𝟙 𝟘 → refl
    𝟙 𝟘 𝟙 𝟙 𝟙 → refl
    𝟙 𝟘 𝟙 𝟙 ω → refl
    𝟙 𝟘 𝟙 ω 𝟘 → refl
    𝟙 𝟘 𝟙 ω 𝟙 → refl
    𝟙 𝟘 𝟙 ω ω → refl
    𝟙 𝟘 ω 𝟘 𝟘 → refl
    𝟙 𝟘 ω 𝟘 𝟙 → refl
    𝟙 𝟘 ω 𝟘 ω → refl
    𝟙 𝟘 ω 𝟙 𝟘 → refl
    𝟙 𝟘 ω 𝟙 𝟙 → refl
    𝟙 𝟘 ω 𝟙 ω → refl
    𝟙 𝟘 ω ω 𝟘 → refl
    𝟙 𝟘 ω ω 𝟙 → refl
    𝟙 𝟘 ω ω ω → refl
    𝟙 𝟙 𝟘 𝟘 𝟘 → refl
    𝟙 𝟙 𝟘 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 𝟘 ω → refl
    𝟙 𝟙 𝟘 𝟙 𝟘 → refl
    𝟙 𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟙 𝟘 𝟙 ω → refl
    𝟙 𝟙 𝟘 ω 𝟘 → refl
    𝟙 𝟙 𝟘 ω 𝟙 → refl
    𝟙 𝟙 𝟘 ω ω → refl
    𝟙 𝟙 𝟙 𝟘 𝟘 → refl
    𝟙 𝟙 𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 𝟙 𝟙 ω → refl
    𝟙 𝟙 𝟙 ω 𝟘 → refl
    𝟙 𝟙 𝟙 ω 𝟙 → refl
    𝟙 𝟙 𝟙 ω ω → refl
    𝟙 𝟙 ω 𝟘 𝟘 → refl
    𝟙 𝟙 ω 𝟘 𝟙 → refl
    𝟙 𝟙 ω 𝟘 ω → refl
    𝟙 𝟙 ω 𝟙 𝟘 → refl
    𝟙 𝟙 ω 𝟙 𝟙 → refl
    𝟙 𝟙 ω 𝟙 ω → refl
    𝟙 𝟙 ω ω 𝟘 → refl
    𝟙 𝟙 ω ω 𝟙 → refl
    𝟙 𝟙 ω ω ω → refl
    𝟙 ω 𝟘 𝟘 𝟘 → refl
    𝟙 ω 𝟘 𝟘 𝟙 → refl
    𝟙 ω 𝟘 𝟘 ω → refl
    𝟙 ω 𝟘 𝟙 𝟘 → refl
    𝟙 ω 𝟘 𝟙 𝟙 → refl
    𝟙 ω 𝟘 𝟙 ω → refl
    𝟙 ω 𝟘 ω 𝟘 → refl
    𝟙 ω 𝟘 ω 𝟙 → refl
    𝟙 ω 𝟘 ω ω → refl
    𝟙 ω 𝟙 𝟘 𝟘 → refl
    𝟙 ω 𝟙 𝟘 𝟙 → refl
    𝟙 ω 𝟙 𝟘 ω → refl
    𝟙 ω 𝟙 𝟙 𝟘 → refl
    𝟙 ω 𝟙 𝟙 𝟙 → refl
    𝟙 ω 𝟙 𝟙 ω → refl
    𝟙 ω 𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 ω 𝟙 → refl
    𝟙 ω 𝟙 ω ω → refl
    𝟙 ω ω 𝟘 𝟘 → refl
    𝟙 ω ω 𝟘 𝟙 → refl
    𝟙 ω ω 𝟘 ω → refl
    𝟙 ω ω 𝟙 𝟘 → refl
    𝟙 ω ω 𝟙 𝟙 → refl
    𝟙 ω ω 𝟙 ω → refl
    𝟙 ω ω ω 𝟘 → refl
    𝟙 ω ω ω 𝟙 → refl
    𝟙 ω ω ω ω → refl
    ω 𝟘 𝟘 𝟘 𝟘 → refl
    ω 𝟘 𝟘 𝟘 𝟙 → refl
    ω 𝟘 𝟘 𝟘 ω → refl
    ω 𝟘 𝟘 𝟙 𝟘 → refl
    ω 𝟘 𝟘 𝟙 𝟙 → refl
    ω 𝟘 𝟘 𝟙 ω → refl
    ω 𝟘 𝟘 ω 𝟘 → refl
    ω 𝟘 𝟘 ω 𝟙 → refl
    ω 𝟘 𝟘 ω ω → refl
    ω 𝟘 𝟙 𝟘 𝟘 → refl
    ω 𝟘 𝟙 𝟘 𝟙 → refl
    ω 𝟘 𝟙 𝟘 ω → refl
    ω 𝟘 𝟙 𝟙 𝟘 → refl
    ω 𝟘 𝟙 𝟙 𝟙 → refl
    ω 𝟘 𝟙 𝟙 ω → refl
    ω 𝟘 𝟙 ω 𝟘 → refl
    ω 𝟘 𝟙 ω 𝟙 → refl
    ω 𝟘 𝟙 ω ω → refl
    ω 𝟘 ω 𝟘 𝟘 → refl
    ω 𝟘 ω 𝟘 𝟙 → refl
    ω 𝟘 ω 𝟘 ω → refl
    ω 𝟘 ω 𝟙 𝟘 → refl
    ω 𝟘 ω 𝟙 𝟙 → refl
    ω 𝟘 ω 𝟙 ω → refl
    ω 𝟘 ω ω 𝟘 → refl
    ω 𝟘 ω ω 𝟙 → refl
    ω 𝟘 ω ω ω → refl
    ω 𝟙 𝟘 𝟘 𝟘 → refl
    ω 𝟙 𝟘 𝟘 𝟙 → refl
    ω 𝟙 𝟘 𝟘 ω → refl
    ω 𝟙 𝟘 𝟙 𝟘 → refl
    ω 𝟙 𝟘 𝟙 𝟙 → refl
    ω 𝟙 𝟘 𝟙 ω → refl
    ω 𝟙 𝟘 ω 𝟘 → refl
    ω 𝟙 𝟘 ω 𝟙 → refl
    ω 𝟙 𝟘 ω ω → refl
    ω 𝟙 𝟙 𝟘 𝟘 → refl
    ω 𝟙 𝟙 𝟘 𝟙 → refl
    ω 𝟙 𝟙 𝟘 ω → refl
    ω 𝟙 𝟙 𝟙 𝟘 → refl
    ω 𝟙 𝟙 𝟙 𝟙 → refl
    ω 𝟙 𝟙 𝟙 ω → refl
    ω 𝟙 𝟙 ω 𝟘 → refl
    ω 𝟙 𝟙 ω 𝟙 → refl
    ω 𝟙 𝟙 ω ω → refl
    ω 𝟙 ω 𝟘 𝟘 → refl
    ω 𝟙 ω 𝟘 𝟙 → refl
    ω 𝟙 ω 𝟘 ω → refl
    ω 𝟙 ω 𝟙 𝟘 → refl
    ω 𝟙 ω 𝟙 𝟙 → refl
    ω 𝟙 ω 𝟙 ω → refl
    ω 𝟙 ω ω 𝟘 → refl
    ω 𝟙 ω ω 𝟙 → refl
    ω 𝟙 ω ω ω → refl
    ω ω 𝟘 𝟘 𝟘 → refl
    ω ω 𝟘 𝟘 𝟙 → refl
    ω ω 𝟘 𝟘 ω → refl
    ω ω 𝟘 𝟙 𝟘 → refl
    ω ω 𝟘 𝟙 𝟙 → refl
    ω ω 𝟘 𝟙 ω → refl
    ω ω 𝟘 ω 𝟘 → refl
    ω ω 𝟘 ω 𝟙 → refl
    ω ω 𝟘 ω ω → refl
    ω ω 𝟙 𝟘 𝟘 → refl
    ω ω 𝟙 𝟘 𝟙 → refl
    ω ω 𝟙 𝟘 ω → refl
    ω ω 𝟙 𝟙 𝟘 → refl
    ω ω 𝟙 𝟙 𝟙 → refl
    ω ω 𝟙 𝟙 ω → refl
    ω ω 𝟙 ω 𝟘 → refl
    ω ω 𝟙 ω 𝟙 → refl
    ω ω 𝟙 ω ω → refl
    ω ω ω 𝟘 𝟘 → refl
    ω ω ω 𝟘 𝟙 → refl
    ω ω ω 𝟘 ω → refl
    ω ω ω 𝟙 𝟘 → refl
    ω ω ω 𝟙 𝟙 → refl
    ω ω ω 𝟙 ω → refl
    ω ω ω ω 𝟘 → refl
    ω ω ω ω 𝟙 → refl
    ω ω ω ω ω → refl

  tr-order-reflecting : ∀ p q → tr′ p LA.≤ tr′ q → p A.≤ q
  tr-order-reflecting 𝟘 𝟘 _ = refl
  tr-order-reflecting 𝟙 𝟘 _ = refl
  tr-order-reflecting 𝟙 𝟙 _ = refl
  tr-order-reflecting ω 𝟘 _ = refl
  tr-order-reflecting ω 𝟙 _ = refl
  tr-order-reflecting ω ω _ = refl

  tr-≤-+ :
    ∀ p q r →
    tr′ p LA.≤ q LA.+ r →
    ∃₂ λ q′ r′ → tr′ q′ LA.≤ q × tr′ r′ LA.≤ r × p A.≤ q′ A.+ r′
  tr-≤-+ 𝟘 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟙 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟙 𝟘  𝟙  _  = 𝟘 , 𝟙 , refl , refl , refl
  tr-≤-+ 𝟙 𝟘  ≤𝟙 _  = 𝟘 , 𝟙 , refl , refl , refl
  tr-≤-+ 𝟙 𝟙  𝟘  _  = 𝟙 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟙 ≤𝟙 𝟘  _  = 𝟙 , 𝟘 , refl , refl , refl
  tr-≤-+ ω _  _  _  = ω , ω , refl , refl , refl
  tr-≤-+ 𝟘 𝟙  𝟙  ()
  tr-≤-+ 𝟘 ≤𝟙 𝟙  ()
  tr-≤-+ 𝟘 ≤ω 𝟙  ()
  tr-≤-+ 𝟙 ≤ω ≤ω ()

  tr-≤-· :
    ∀ p q r →
    tr′ p LA.≤ tr′ q LA.· r →
    ∃ λ r′ → tr′ r′ LA.≤ r × p A.≤ q A.· r′
  tr-≤-· 𝟘 𝟘 𝟘  _ = ω , refl , refl
  tr-≤-· 𝟘 𝟘 𝟙  _ = ω , refl , refl
  tr-≤-· 𝟘 𝟘 ≤𝟙 _ = ω , refl , refl
  tr-≤-· 𝟘 𝟘 ≤ω _ = ω , refl , refl
  tr-≤-· 𝟘 𝟙 𝟘  _ = 𝟘 , refl , refl
  tr-≤-· 𝟘 ω 𝟘  _ = 𝟘 , refl , refl
  tr-≤-· 𝟙 𝟘 𝟘  _ = ω , refl , refl
  tr-≤-· 𝟙 𝟘 𝟙  _ = ω , refl , refl
  tr-≤-· 𝟙 𝟘 ≤𝟙 _ = ω , refl , refl
  tr-≤-· 𝟙 𝟘 ≤ω _ = ω , refl , refl
  tr-≤-· 𝟙 𝟙 𝟘  _ = 𝟙 , refl , refl
  tr-≤-· 𝟙 𝟙 𝟙  _ = 𝟙 , refl , refl
  tr-≤-· 𝟙 𝟙 ≤𝟙 _ = 𝟙 , refl , refl
  tr-≤-· 𝟙 ω 𝟘  _ = 𝟘 , refl , refl
  tr-≤-· ω _ _  _ = ω , refl , refl

  tr-≤-∧ :
    ∀ p q r →
    tr′ p LA.≤ q LA.∧ r →
    ∃₂ λ q′ r′ → tr′ q′ LA.≤ q × tr′ r′ LA.≤ r × p A.≤ q′ A.∧ r′
  tr-≤-∧ 𝟘 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟘  𝟘  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟘  𝟙  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟘  ≤𝟙 _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟙  𝟘  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟙  𝟙  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟙  ≤𝟙 _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 ≤𝟙 𝟘  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 ≤𝟙 𝟙  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ 𝟙 ≤𝟙 ≤𝟙 _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ ω _  _  _  = ω , ω , refl , refl , refl
  tr-≤-∧ 𝟘 𝟙  𝟙  ()
  tr-≤-∧ 𝟘 ≤𝟙 𝟙  ()

  tr-≤-nr :
    ∀ q p r z₁ s₁ n₁ →
    tr′ q LA.≤ LA.nr (tr′ p) (tr′ r) z₁ s₁ n₁ →
    ∃₃ λ z₂ s₂ n₂ →
       tr′ z₂ LA.≤ z₁ × tr′ s₂ LA.≤ s₁ × tr′ n₂ LA.≤ n₁ ×
       q A.≤ A.nr p r z₂ s₂ n₂
  tr-≤-nr = λ where
    ω _ _ _  _  _  _  → ω , ω , ω , refl , refl , refl , refl
    𝟘 𝟘 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟙 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω 𝟙 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 ω ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟘  𝟘  𝟙  _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟘  𝟘  ≤𝟙 _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟘  𝟙  𝟘  _  → 𝟘 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 𝟘  _  → 𝟘 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟘  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟘  𝟘  𝟙  _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟘  𝟘  ≤𝟙 _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟘 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  𝟘  𝟙  _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  𝟘  ≤𝟙 _  → 𝟘 , 𝟘 , 𝟙 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟙 𝟘  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 𝟙 ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟘  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟘  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟘  ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟙  𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 𝟙  ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 ≤𝟙 𝟙  𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 𝟘  _  → 𝟙 , 𝟙 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟙 𝟘  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟙 𝟙  𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω 𝟙 ≤𝟙 𝟘  𝟘  _  → 𝟙 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟙 ω ω 𝟘  𝟘  𝟘  _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
    𝟘 𝟘 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 𝟘 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 𝟘 ω 𝟘  𝟘  𝟙  ()
    𝟘 𝟘 ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  𝟘  ≤ω ()
    𝟘 𝟘 ω 𝟘  𝟙  𝟘  ()
    𝟘 𝟘 ω 𝟘  𝟙  𝟙  ()
    𝟘 𝟘 ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  𝟙  ≤ω ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟘 ω 𝟘  ≤ω 𝟘  ()
    𝟘 𝟘 ω 𝟘  ≤ω 𝟙  ()
    𝟘 𝟘 ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟘 ω 𝟘  ≤ω ≤ω ()
    𝟘 𝟘 ω 𝟙  𝟘  𝟘  ()
    𝟘 𝟘 ω 𝟙  𝟘  𝟙  ()
    𝟘 𝟘 ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  𝟘  ≤ω ()
    𝟘 𝟘 ω 𝟙  𝟙  𝟘  ()
    𝟘 𝟘 ω 𝟙  𝟙  𝟙  ()
    𝟘 𝟘 ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  𝟙  ≤ω ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟘 ω 𝟙  ≤ω 𝟘  ()
    𝟘 𝟘 ω 𝟙  ≤ω 𝟙  ()
    𝟘 𝟘 ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟘 ω 𝟙  ≤ω ≤ω ()
    𝟘 𝟘 ω ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟘 ω ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟘 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟘 ω ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟘 ω ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟘 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟘 ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟘 ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟘 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟘 ω ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟘 ω ≤ω 𝟘  𝟘  ()
    𝟘 𝟘 ω ≤ω 𝟘  𝟙  ()
    𝟘 𝟘 ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟘 ω ≤ω 𝟘  ≤ω ()
    𝟘 𝟘 ω ≤ω 𝟙  𝟘  ()
    𝟘 𝟘 ω ≤ω 𝟙  𝟙  ()
    𝟘 𝟘 ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟘 ω ≤ω 𝟙  ≤ω ()
    𝟘 𝟘 ω ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟘 ω ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟘 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟘 ω ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟘 ω ≤ω ≤ω 𝟘  ()
    𝟘 𝟘 ω ≤ω ≤ω 𝟙  ()
    𝟘 𝟘 ω ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟘 ω ≤ω ≤ω ≤ω ()
    𝟘 𝟙 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 𝟙 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 𝟙 ω 𝟘  𝟘  𝟙  ()
    𝟘 𝟙 ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  𝟘  ≤ω ()
    𝟘 𝟙 ω 𝟘  𝟙  𝟘  ()
    𝟘 𝟙 ω 𝟘  𝟙  𝟙  ()
    𝟘 𝟙 ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  𝟙  ≤ω ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 𝟙 ω 𝟘  ≤ω 𝟘  ()
    𝟘 𝟙 ω 𝟘  ≤ω 𝟙  ()
    𝟘 𝟙 ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 𝟙 ω 𝟘  ≤ω ≤ω ()
    𝟘 𝟙 ω 𝟙  𝟘  𝟘  ()
    𝟘 𝟙 ω 𝟙  𝟘  𝟙  ()
    𝟘 𝟙 ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  𝟘  ≤ω ()
    𝟘 𝟙 ω 𝟙  𝟙  𝟘  ()
    𝟘 𝟙 ω 𝟙  𝟙  𝟙  ()
    𝟘 𝟙 ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  𝟙  ≤ω ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 𝟙 ω 𝟙  ≤ω 𝟘  ()
    𝟘 𝟙 ω 𝟙  ≤ω 𝟙  ()
    𝟘 𝟙 ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 𝟙 ω 𝟙  ≤ω ≤ω ()
    𝟘 𝟙 ω ≤𝟙 𝟘  𝟘  ()
    𝟘 𝟙 ω ≤𝟙 𝟘  𝟙  ()
    𝟘 𝟙 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 𝟘  ≤ω ()
    𝟘 𝟙 ω ≤𝟙 𝟙  𝟘  ()
    𝟘 𝟙 ω ≤𝟙 𝟙  𝟙  ()
    𝟘 𝟙 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 𝟙  ≤ω ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 𝟙 ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 𝟙 ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 𝟙 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 𝟙 ω ≤𝟙 ≤ω ≤ω ()
    𝟘 𝟙 ω ≤ω 𝟘  𝟘  ()
    𝟘 𝟙 ω ≤ω 𝟘  𝟙  ()
    𝟘 𝟙 ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 𝟙 ω ≤ω 𝟘  ≤ω ()
    𝟘 𝟙 ω ≤ω 𝟙  𝟘  ()
    𝟘 𝟙 ω ≤ω 𝟙  𝟙  ()
    𝟘 𝟙 ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 𝟙 ω ≤ω 𝟙  ≤ω ()
    𝟘 𝟙 ω ≤ω ≤𝟙 𝟘  ()
    𝟘 𝟙 ω ≤ω ≤𝟙 𝟙  ()
    𝟘 𝟙 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 𝟙 ω ≤ω ≤𝟙 ≤ω ()
    𝟘 𝟙 ω ≤ω ≤ω 𝟘  ()
    𝟘 𝟙 ω ≤ω ≤ω 𝟙  ()
    𝟘 𝟙 ω ≤ω ≤ω ≤𝟙 ()
    𝟘 𝟙 ω ≤ω ≤ω ≤ω ()
    𝟘 ω 𝟘 𝟘  𝟘  𝟙  ()
    𝟘 ω 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  𝟘  ≤ω ()
    𝟘 ω 𝟘 𝟘  𝟙  𝟘  ()
    𝟘 ω 𝟘 𝟘  𝟙  𝟙  ()
    𝟘 ω 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  𝟙  ≤ω ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 𝟘  ≤ω 𝟘  ()
    𝟘 ω 𝟘 𝟘  ≤ω 𝟙  ()
    𝟘 ω 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 𝟘  ≤ω ≤ω ()
    𝟘 ω 𝟘 𝟙  𝟘  𝟘  ()
    𝟘 ω 𝟘 𝟙  𝟘  𝟙  ()
    𝟘 ω 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  𝟘  ≤ω ()
    𝟘 ω 𝟘 𝟙  𝟙  𝟘  ()
    𝟘 ω 𝟘 𝟙  𝟙  𝟙  ()
    𝟘 ω 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  𝟙  ≤ω ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 𝟙  ≤ω 𝟘  ()
    𝟘 ω 𝟘 𝟙  ≤ω 𝟙  ()
    𝟘 ω 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 𝟙  ≤ω ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟘 ω 𝟘 ≤ω 𝟘  𝟘  ()
    𝟘 ω 𝟘 ≤ω 𝟘  𝟙  ()
    𝟘 ω 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω 𝟘  ≤ω ()
    𝟘 ω 𝟘 ≤ω 𝟙  𝟘  ()
    𝟘 ω 𝟘 ≤ω 𝟙  𝟙  ()
    𝟘 ω 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω 𝟙  ≤ω ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟘 ω 𝟘 ≤ω ≤ω 𝟘  ()
    𝟘 ω 𝟘 ≤ω ≤ω 𝟙  ()
    𝟘 ω 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟘 ω 𝟘 ≤ω ≤ω ≤ω ()
    𝟘 ω 𝟙 𝟘  𝟘  𝟙  ()
    𝟘 ω 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  𝟘  ≤ω ()
    𝟘 ω 𝟙 𝟘  𝟙  𝟘  ()
    𝟘 ω 𝟙 𝟘  𝟙  𝟙  ()
    𝟘 ω 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  𝟙  ≤ω ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 𝟘  ≤ω 𝟘  ()
    𝟘 ω 𝟙 𝟘  ≤ω 𝟙  ()
    𝟘 ω 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 𝟘  ≤ω ≤ω ()
    𝟘 ω 𝟙 𝟙  𝟘  𝟘  ()
    𝟘 ω 𝟙 𝟙  𝟘  𝟙  ()
    𝟘 ω 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  𝟘  ≤ω ()
    𝟘 ω 𝟙 𝟙  𝟙  𝟘  ()
    𝟘 ω 𝟙 𝟙  𝟙  𝟙  ()
    𝟘 ω 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  𝟙  ≤ω ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 𝟙  ≤ω 𝟘  ()
    𝟘 ω 𝟙 𝟙  ≤ω 𝟙  ()
    𝟘 ω 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 𝟙  ≤ω ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟘 ω 𝟙 ≤ω 𝟘  𝟘  ()
    𝟘 ω 𝟙 ≤ω 𝟘  𝟙  ()
    𝟘 ω 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω 𝟘  ≤ω ()
    𝟘 ω 𝟙 ≤ω 𝟙  𝟘  ()
    𝟘 ω 𝟙 ≤ω 𝟙  𝟙  ()
    𝟘 ω 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω 𝟙  ≤ω ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟘 ω 𝟙 ≤ω ≤ω 𝟘  ()
    𝟘 ω 𝟙 ≤ω ≤ω 𝟙  ()
    𝟘 ω 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟘 ω 𝟙 ≤ω ≤ω ≤ω ()
    𝟘 ω ω 𝟘  𝟘  𝟙  ()
    𝟘 ω ω 𝟘  𝟘  ≤𝟙 ()
    𝟘 ω ω 𝟘  𝟘  ≤ω ()
    𝟘 ω ω 𝟘  𝟙  𝟘  ()
    𝟘 ω ω 𝟘  𝟙  𝟙  ()
    𝟘 ω ω 𝟘  𝟙  ≤𝟙 ()
    𝟘 ω ω 𝟘  𝟙  ≤ω ()
    𝟘 ω ω 𝟘  ≤𝟙 𝟘  ()
    𝟘 ω ω 𝟘  ≤𝟙 𝟙  ()
    𝟘 ω ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟘 ω ω 𝟘  ≤𝟙 ≤ω ()
    𝟘 ω ω 𝟘  ≤ω 𝟘  ()
    𝟘 ω ω 𝟘  ≤ω 𝟙  ()
    𝟘 ω ω 𝟘  ≤ω ≤𝟙 ()
    𝟘 ω ω 𝟘  ≤ω ≤ω ()
    𝟘 ω ω 𝟙  𝟘  𝟘  ()
    𝟘 ω ω 𝟙  𝟘  𝟙  ()
    𝟘 ω ω 𝟙  𝟘  ≤𝟙 ()
    𝟘 ω ω 𝟙  𝟘  ≤ω ()
    𝟘 ω ω 𝟙  𝟙  𝟘  ()
    𝟘 ω ω 𝟙  𝟙  𝟙  ()
    𝟘 ω ω 𝟙  𝟙  ≤𝟙 ()
    𝟘 ω ω 𝟙  𝟙  ≤ω ()
    𝟘 ω ω 𝟙  ≤𝟙 𝟘  ()
    𝟘 ω ω 𝟙  ≤𝟙 𝟙  ()
    𝟘 ω ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟘 ω ω 𝟙  ≤𝟙 ≤ω ()
    𝟘 ω ω 𝟙  ≤ω 𝟘  ()
    𝟘 ω ω 𝟙  ≤ω 𝟙  ()
    𝟘 ω ω 𝟙  ≤ω ≤𝟙 ()
    𝟘 ω ω 𝟙  ≤ω ≤ω ()
    𝟘 ω ω ≤𝟙 𝟘  𝟘  ()
    𝟘 ω ω ≤𝟙 𝟘  𝟙  ()
    𝟘 ω ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟘 ω ω ≤𝟙 𝟘  ≤ω ()
    𝟘 ω ω ≤𝟙 𝟙  𝟘  ()
    𝟘 ω ω ≤𝟙 𝟙  𝟙  ()
    𝟘 ω ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟘 ω ω ≤𝟙 𝟙  ≤ω ()
    𝟘 ω ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟘 ω ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟘 ω ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟘 ω ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟘 ω ω ≤𝟙 ≤ω 𝟘  ()
    𝟘 ω ω ≤𝟙 ≤ω 𝟙  ()
    𝟘 ω ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟘 ω ω ≤𝟙 ≤ω ≤ω ()
    𝟘 ω ω ≤ω 𝟘  𝟘  ()
    𝟘 ω ω ≤ω 𝟘  𝟙  ()
    𝟘 ω ω ≤ω 𝟘  ≤𝟙 ()
    𝟘 ω ω ≤ω 𝟘  ≤ω ()
    𝟘 ω ω ≤ω 𝟙  𝟘  ()
    𝟘 ω ω ≤ω 𝟙  𝟙  ()
    𝟘 ω ω ≤ω 𝟙  ≤𝟙 ()
    𝟘 ω ω ≤ω 𝟙  ≤ω ()
    𝟘 ω ω ≤ω ≤𝟙 𝟘  ()
    𝟘 ω ω ≤ω ≤𝟙 𝟙  ()
    𝟘 ω ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟘 ω ω ≤ω ≤𝟙 ≤ω ()
    𝟘 ω ω ≤ω ≤ω 𝟘  ()
    𝟘 ω ω ≤ω ≤ω 𝟙  ()
    𝟘 ω ω ≤ω ≤ω ≤𝟙 ()
    𝟘 ω ω ≤ω ≤ω ≤ω ()
    𝟙 𝟘 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 𝟘 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 𝟘 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 𝟘 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 𝟘 ω 𝟘  𝟘  𝟙  ()
    𝟙 𝟘 ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  𝟘  ≤ω ()
    𝟙 𝟘 ω 𝟘  𝟙  𝟘  ()
    𝟙 𝟘 ω 𝟘  𝟙  𝟙  ()
    𝟙 𝟘 ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  𝟙  ≤ω ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟘 ω 𝟘  ≤ω 𝟘  ()
    𝟙 𝟘 ω 𝟘  ≤ω 𝟙  ()
    𝟙 𝟘 ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟘 ω 𝟘  ≤ω ≤ω ()
    𝟙 𝟘 ω 𝟙  𝟘  𝟘  ()
    𝟙 𝟘 ω 𝟙  𝟘  𝟙  ()
    𝟙 𝟘 ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  𝟘  ≤ω ()
    𝟙 𝟘 ω 𝟙  𝟙  𝟘  ()
    𝟙 𝟘 ω 𝟙  𝟙  𝟙  ()
    𝟙 𝟘 ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  𝟙  ≤ω ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟘 ω 𝟙  ≤ω 𝟘  ()
    𝟙 𝟘 ω 𝟙  ≤ω 𝟙  ()
    𝟙 𝟘 ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟘 ω 𝟙  ≤ω ≤ω ()
    𝟙 𝟘 ω ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟘 ω ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟘 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟘 ω ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟘 ω ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟘 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟘 ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟘 ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟘 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟘 ω ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟘 ω ≤ω 𝟘  𝟘  ()
    𝟙 𝟘 ω ≤ω 𝟘  𝟙  ()
    𝟙 𝟘 ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟘 ω ≤ω 𝟘  ≤ω ()
    𝟙 𝟘 ω ≤ω 𝟙  𝟘  ()
    𝟙 𝟘 ω ≤ω 𝟙  𝟙  ()
    𝟙 𝟘 ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟘 ω ≤ω 𝟙  ≤ω ()
    𝟙 𝟘 ω ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟘 ω ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟘 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟘 ω ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟘 ω ≤ω ≤ω 𝟘  ()
    𝟙 𝟘 ω ≤ω ≤ω 𝟙  ()
    𝟙 𝟘 ω ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟘 ω ≤ω ≤ω ≤ω ()
    𝟙 𝟙 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 𝟙 𝟙 𝟘  𝟘  𝟙  ()
    𝟙 𝟙 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 𝟙 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 𝟙 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 𝟙 ω 𝟘  𝟘  𝟙  ()
    𝟙 𝟙 ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  𝟘  ≤ω ()
    𝟙 𝟙 ω 𝟘  𝟙  𝟘  ()
    𝟙 𝟙 ω 𝟘  𝟙  𝟙  ()
    𝟙 𝟙 ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  𝟙  ≤ω ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 𝟙 ω 𝟘  ≤ω 𝟘  ()
    𝟙 𝟙 ω 𝟘  ≤ω 𝟙  ()
    𝟙 𝟙 ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 𝟙 ω 𝟘  ≤ω ≤ω ()
    𝟙 𝟙 ω 𝟙  𝟘  𝟘  ()
    𝟙 𝟙 ω 𝟙  𝟘  𝟙  ()
    𝟙 𝟙 ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  𝟘  ≤ω ()
    𝟙 𝟙 ω 𝟙  𝟙  𝟘  ()
    𝟙 𝟙 ω 𝟙  𝟙  𝟙  ()
    𝟙 𝟙 ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  𝟙  ≤ω ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 𝟙 ω 𝟙  ≤ω 𝟘  ()
    𝟙 𝟙 ω 𝟙  ≤ω 𝟙  ()
    𝟙 𝟙 ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 𝟙 ω 𝟙  ≤ω ≤ω ()
    𝟙 𝟙 ω ≤𝟙 𝟘  𝟘  ()
    𝟙 𝟙 ω ≤𝟙 𝟘  𝟙  ()
    𝟙 𝟙 ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 𝟘  ≤ω ()
    𝟙 𝟙 ω ≤𝟙 𝟙  𝟘  ()
    𝟙 𝟙 ω ≤𝟙 𝟙  𝟙  ()
    𝟙 𝟙 ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 𝟙  ≤ω ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 𝟙 ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 𝟙 ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 𝟙 ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 𝟙 ω ≤𝟙 ≤ω ≤ω ()
    𝟙 𝟙 ω ≤ω 𝟘  𝟘  ()
    𝟙 𝟙 ω ≤ω 𝟘  𝟙  ()
    𝟙 𝟙 ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 𝟙 ω ≤ω 𝟘  ≤ω ()
    𝟙 𝟙 ω ≤ω 𝟙  𝟘  ()
    𝟙 𝟙 ω ≤ω 𝟙  𝟙  ()
    𝟙 𝟙 ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 𝟙 ω ≤ω 𝟙  ≤ω ()
    𝟙 𝟙 ω ≤ω ≤𝟙 𝟘  ()
    𝟙 𝟙 ω ≤ω ≤𝟙 𝟙  ()
    𝟙 𝟙 ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 𝟙 ω ≤ω ≤𝟙 ≤ω ()
    𝟙 𝟙 ω ≤ω ≤ω 𝟘  ()
    𝟙 𝟙 ω ≤ω ≤ω 𝟙  ()
    𝟙 𝟙 ω ≤ω ≤ω ≤𝟙 ()
    𝟙 𝟙 ω ≤ω ≤ω ≤ω ()
    𝟙 ω 𝟘 𝟘  𝟘  𝟙  ()
    𝟙 ω 𝟘 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  𝟘  ≤ω ()
    𝟙 ω 𝟘 𝟘  𝟙  𝟙  ()
    𝟙 ω 𝟘 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  𝟙  ≤ω ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 𝟘  ≤ω 𝟘  ()
    𝟙 ω 𝟘 𝟘  ≤ω 𝟙  ()
    𝟙 ω 𝟘 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 𝟘  ≤ω ≤ω ()
    𝟙 ω 𝟘 𝟙  𝟘  𝟙  ()
    𝟙 ω 𝟘 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  𝟘  ≤ω ()
    𝟙 ω 𝟘 𝟙  𝟙  𝟙  ()
    𝟙 ω 𝟘 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  𝟙  ≤ω ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 𝟙  ≤ω 𝟘  ()
    𝟙 ω 𝟘 𝟙  ≤ω 𝟙  ()
    𝟙 ω 𝟘 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 𝟙  ≤ω ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 𝟘  ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 𝟙  ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 ≤𝟙 ≤ω ≤ω ()
    𝟙 ω 𝟘 ≤ω 𝟘  𝟘  ()
    𝟙 ω 𝟘 ≤ω 𝟘  𝟙  ()
    𝟙 ω 𝟘 ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω 𝟘  ≤ω ()
    𝟙 ω 𝟘 ≤ω 𝟙  𝟘  ()
    𝟙 ω 𝟘 ≤ω 𝟙  𝟙  ()
    𝟙 ω 𝟘 ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω 𝟙  ≤ω ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 𝟘  ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 𝟙  ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω ≤𝟙 ≤ω ()
    𝟙 ω 𝟘 ≤ω ≤ω 𝟘  ()
    𝟙 ω 𝟘 ≤ω ≤ω 𝟙  ()
    𝟙 ω 𝟘 ≤ω ≤ω ≤𝟙 ()
    𝟙 ω 𝟘 ≤ω ≤ω ≤ω ()
    𝟙 ω 𝟙 𝟘  𝟘  𝟙  ()
    𝟙 ω 𝟙 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  𝟘  ≤ω ()
    𝟙 ω 𝟙 𝟘  𝟙  𝟘  ()
    𝟙 ω 𝟙 𝟘  𝟙  𝟙  ()
    𝟙 ω 𝟙 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  𝟙  ≤ω ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 𝟘  ≤ω 𝟘  ()
    𝟙 ω 𝟙 𝟘  ≤ω 𝟙  ()
    𝟙 ω 𝟙 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 𝟘  ≤ω ≤ω ()
    𝟙 ω 𝟙 𝟙  𝟘  𝟙  ()
    𝟙 ω 𝟙 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  𝟘  ≤ω ()
    𝟙 ω 𝟙 𝟙  𝟙  𝟘  ()
    𝟙 ω 𝟙 𝟙  𝟙  𝟙  ()
    𝟙 ω 𝟙 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  𝟙  ≤ω ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 𝟙  ≤ω 𝟘  ()
    𝟙 ω 𝟙 𝟙  ≤ω 𝟙  ()
    𝟙 ω 𝟙 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 𝟙  ≤ω ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 𝟘  ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 𝟙  ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 ≤𝟙 ≤ω ≤ω ()
    𝟙 ω 𝟙 ≤ω 𝟘  𝟘  ()
    𝟙 ω 𝟙 ≤ω 𝟘  𝟙  ()
    𝟙 ω 𝟙 ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω 𝟘  ≤ω ()
    𝟙 ω 𝟙 ≤ω 𝟙  𝟘  ()
    𝟙 ω 𝟙 ≤ω 𝟙  𝟙  ()
    𝟙 ω 𝟙 ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω 𝟙  ≤ω ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 𝟘  ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 𝟙  ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω ≤𝟙 ≤ω ()
    𝟙 ω 𝟙 ≤ω ≤ω 𝟘  ()
    𝟙 ω 𝟙 ≤ω ≤ω 𝟙  ()
    𝟙 ω 𝟙 ≤ω ≤ω ≤𝟙 ()
    𝟙 ω 𝟙 ≤ω ≤ω ≤ω ()
    𝟙 ω ω 𝟘  𝟘  𝟙  ()
    𝟙 ω ω 𝟘  𝟘  ≤𝟙 ()
    𝟙 ω ω 𝟘  𝟘  ≤ω ()
    𝟙 ω ω 𝟘  𝟙  𝟘  ()
    𝟙 ω ω 𝟘  𝟙  𝟙  ()
    𝟙 ω ω 𝟘  𝟙  ≤𝟙 ()
    𝟙 ω ω 𝟘  𝟙  ≤ω ()
    𝟙 ω ω 𝟘  ≤𝟙 𝟘  ()
    𝟙 ω ω 𝟘  ≤𝟙 𝟙  ()
    𝟙 ω ω 𝟘  ≤𝟙 ≤𝟙 ()
    𝟙 ω ω 𝟘  ≤𝟙 ≤ω ()
    𝟙 ω ω 𝟘  ≤ω 𝟘  ()
    𝟙 ω ω 𝟘  ≤ω 𝟙  ()
    𝟙 ω ω 𝟘  ≤ω ≤𝟙 ()
    𝟙 ω ω 𝟘  ≤ω ≤ω ()
    𝟙 ω ω 𝟙  𝟘  𝟘  ()
    𝟙 ω ω 𝟙  𝟘  𝟙  ()
    𝟙 ω ω 𝟙  𝟘  ≤𝟙 ()
    𝟙 ω ω 𝟙  𝟘  ≤ω ()
    𝟙 ω ω 𝟙  𝟙  𝟘  ()
    𝟙 ω ω 𝟙  𝟙  𝟙  ()
    𝟙 ω ω 𝟙  𝟙  ≤𝟙 ()
    𝟙 ω ω 𝟙  𝟙  ≤ω ()
    𝟙 ω ω 𝟙  ≤𝟙 𝟘  ()
    𝟙 ω ω 𝟙  ≤𝟙 𝟙  ()
    𝟙 ω ω 𝟙  ≤𝟙 ≤𝟙 ()
    𝟙 ω ω 𝟙  ≤𝟙 ≤ω ()
    𝟙 ω ω 𝟙  ≤ω 𝟘  ()
    𝟙 ω ω 𝟙  ≤ω 𝟙  ()
    𝟙 ω ω 𝟙  ≤ω ≤𝟙 ()
    𝟙 ω ω 𝟙  ≤ω ≤ω ()
    𝟙 ω ω ≤𝟙 𝟘  𝟘  ()
    𝟙 ω ω ≤𝟙 𝟘  𝟙  ()
    𝟙 ω ω ≤𝟙 𝟘  ≤𝟙 ()
    𝟙 ω ω ≤𝟙 𝟘  ≤ω ()
    𝟙 ω ω ≤𝟙 𝟙  𝟘  ()
    𝟙 ω ω ≤𝟙 𝟙  𝟙  ()
    𝟙 ω ω ≤𝟙 𝟙  ≤𝟙 ()
    𝟙 ω ω ≤𝟙 𝟙  ≤ω ()
    𝟙 ω ω ≤𝟙 ≤𝟙 𝟘  ()
    𝟙 ω ω ≤𝟙 ≤𝟙 𝟙  ()
    𝟙 ω ω ≤𝟙 ≤𝟙 ≤𝟙 ()
    𝟙 ω ω ≤𝟙 ≤𝟙 ≤ω ()
    𝟙 ω ω ≤𝟙 ≤ω 𝟘  ()
    𝟙 ω ω ≤𝟙 ≤ω 𝟙  ()
    𝟙 ω ω ≤𝟙 ≤ω ≤𝟙 ()
    𝟙 ω ω ≤𝟙 ≤ω ≤ω ()
    𝟙 ω ω ≤ω 𝟘  𝟘  ()
    𝟙 ω ω ≤ω 𝟘  𝟙  ()
    𝟙 ω ω ≤ω 𝟘  ≤𝟙 ()
    𝟙 ω ω ≤ω 𝟘  ≤ω ()
    𝟙 ω ω ≤ω 𝟙  𝟘  ()
    𝟙 ω ω ≤ω 𝟙  𝟙  ()
    𝟙 ω ω ≤ω 𝟙  ≤𝟙 ()
    𝟙 ω ω ≤ω 𝟙  ≤ω ()
    𝟙 ω ω ≤ω ≤𝟙 𝟘  ()
    𝟙 ω ω ≤ω ≤𝟙 𝟙  ()
    𝟙 ω ω ≤ω ≤𝟙 ≤𝟙 ()
    𝟙 ω ω ≤ω ≤𝟙 ≤ω ()
    𝟙 ω ω ≤ω ≤ω 𝟘  ()
    𝟙 ω ω ≤ω ≤ω 𝟙  ()
    𝟙 ω ω ≤ω ≤ω ≤𝟙 ()
    𝟙 ω ω ≤ω ≤ω ≤ω ()

  tr⁻¹-monotone : ∀ p q → p LA.≤ q → tr⁻¹ p A.≤ tr⁻¹ q
  tr⁻¹-monotone = λ where
    𝟘  𝟘  refl → refl
    𝟙  𝟙  refl → refl
    ≤𝟙 𝟘  refl → refl
    ≤𝟙 𝟙  refl → refl
    ≤𝟙 ≤𝟙 refl → refl
    ≤ω _  _    → refl

  tr-tr⁻¹≤ : ∀ p → tr′ (tr⁻¹ p) LA.≤ p
  tr-tr⁻¹≤ = λ where
    𝟘  → refl
    𝟙  → refl
    ≤𝟙 → refl
    ≤ω → refl

  tr≤→≤tr⁻¹ : ∀ p q → tr′ p LA.≤ q → p A.≤ tr⁻¹ q
  tr≤→≤tr⁻¹ = λ where
    𝟘 𝟘  refl → refl
    𝟙 𝟘  refl → refl
    𝟙 𝟙  refl → refl
    𝟙 ≤𝟙 refl → refl
    ω _  _    → refl

  tr⁻¹-∧ : ∀ p q → tr⁻¹ (p LA.∧ q) ≡ tr⁻¹ p A.∧ tr⁻¹ q
  tr⁻¹-∧ = λ where
    𝟘  𝟘  → refl
    𝟘  𝟙  → refl
    𝟘  ≤𝟙 → refl
    𝟘  ≤ω → refl
    𝟙  𝟘  → refl
    𝟙  𝟙  → refl
    𝟙  ≤𝟙 → refl
    𝟙  ≤ω → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω _  → refl

  tr⁻¹-+ : ∀ p q → tr⁻¹ (p LA.+ q) ≡ tr⁻¹ p A.+ tr⁻¹ q
  tr⁻¹-+ = λ where
    𝟘  𝟘  → refl
    𝟘  𝟙  → refl
    𝟘  ≤𝟙 → refl
    𝟘  ≤ω → refl
    𝟙  𝟘  → refl
    𝟙  𝟙  → refl
    𝟙  ≤𝟙 → refl
    𝟙  ≤ω → refl
    ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω → refl
    ≤ω 𝟘  → refl
    ≤ω 𝟙  → refl
    ≤ω ≤𝟙 → refl
    ≤ω ≤ω → refl

  tr⁻¹-· : ∀ p q → tr⁻¹ (tr′ p LA.· q) ≡ p A.· tr⁻¹ q
  tr⁻¹-· = λ where
    𝟘 𝟘  → refl
    𝟘 𝟙  → refl
    𝟘 ≤𝟙 → refl
    𝟘 ≤ω → refl
    𝟙 𝟘  → refl
    𝟙 𝟙  → refl
    𝟙 ≤𝟙 → refl
    𝟙 ≤ω → refl
    ω 𝟘  → refl
    ω 𝟙  → refl
    ω ≤𝟙 → refl
    ω ≤ω → refl

  tr-≤-no-nr :
    ∀ s →
    tr′ p LA.≤ q₁ →
    q₁ LA.≤ q₂ →
    (T (Modality-variant.𝟘ᵐ-allowed v₁) →
     q₁ LA.≤ q₃) →
    (Has-well-behaved-zero Linear-or-affine
       LA.linear-or-affine-semiring-with-meet →
     q₁ LA.≤ q₄) →
    q₁ LA.≤ q₃ LA.+ tr′ r LA.· q₄ LA.+ tr′ s LA.· q₁ →
    ∃₄ λ q₁′ q₂′ q₃′ q₄′ →
       tr′ q₂′ LA.≤ q₂ ×
       tr′ q₃′ LA.≤ q₃ ×
       tr′ q₄′ LA.≤ q₄ ×
       p A.≤ q₁′ ×
       q₁′ A.≤ q₂′ ×
       (T (Modality-variant.𝟘ᵐ-allowed v₂) →
        q₁′ A.≤ q₃′) ×
       (Has-well-behaved-zero Affine
          (Modality.semiring-with-meet (affineModality v₂)) →
        q₁′ A.≤ q₄′) ×
       q₁′ A.≤ q₃′ A.+ r A.· q₄′ A.+ s A.· q₁′
  tr-≤-no-nr s = →tr-≤-no-nr {s = s}
    (affineModality v₁)
    (linear-or-affine v₂)
    idᶠ
    (λ _ → LA.linear-or-affine-has-well-behaved-zero)
    tr′
    tr⁻¹
    tr⁻¹-monotone
    tr≤→≤tr⁻¹
    tr-tr⁻¹≤
    (λ p q → P₁.≤-reflexive (tr⁻¹-+ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-∧ p q))
    (λ p q → P₁.≤-reflexive (tr⁻¹-· p q))

-- The function linear-or-affine→affine is a morphism from a linear or
-- affine types modality to an affine types modality if certain
-- assumptions hold.

linear-or-affine⇨affine :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = linear-or-affine v₁
      𝕄₂ = affineModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ linear-or-affine→affine
linear-or-affine⇨affine {v₂ = v₂} refl s⇔s = λ where
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                           , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧                      → ≤-reflexive (tr-∧ _ _)
    .Is-morphism.tr-nr {r = r}             → ≤-reflexive
                                               (tr-nr _ r _ _ _)
    .Is-morphism.nr-in-first-iff-in-second → s⇔s
    .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
    .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
      (inj₁ ok) → inj₁ ok
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ LA.linear-or-affine-has-well-behaved-zero
  where
  open Graded.Modality.Properties (affineModality v₂)

  tr′ = linear-or-affine→affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-+ : ∀ p q → tr′ (p LA.+ q) ≡ tr′ p A.+ tr′ q
  tr-+ 𝟘  𝟘  = refl
  tr-+ 𝟘  𝟙  = refl
  tr-+ 𝟘  ≤𝟙 = refl
  tr-+ 𝟘  ≤ω = refl
  tr-+ 𝟙  𝟘  = refl
  tr-+ 𝟙  𝟙  = refl
  tr-+ 𝟙  ≤𝟙 = refl
  tr-+ 𝟙  ≤ω = refl
  tr-+ ≤𝟙 𝟘  = refl
  tr-+ ≤𝟙 𝟙  = refl
  tr-+ ≤𝟙 ≤𝟙 = refl
  tr-+ ≤𝟙 ≤ω = refl
  tr-+ ≤ω 𝟘  = refl
  tr-+ ≤ω 𝟙  = refl
  tr-+ ≤ω ≤𝟙 = refl
  tr-+ ≤ω ≤ω = refl

  tr-· : ∀ p q → tr′ (p LA.· q) ≡ tr′ p A.· tr′ q
  tr-· 𝟘  𝟘  = refl
  tr-· 𝟘  𝟙  = refl
  tr-· 𝟘  ≤𝟙 = refl
  tr-· 𝟘  ≤ω = refl
  tr-· 𝟙  𝟘  = refl
  tr-· 𝟙  𝟙  = refl
  tr-· 𝟙  ≤𝟙 = refl
  tr-· 𝟙  ≤ω = refl
  tr-· ≤𝟙 𝟘  = refl
  tr-· ≤𝟙 𝟙  = refl
  tr-· ≤𝟙 ≤𝟙 = refl
  tr-· ≤𝟙 ≤ω = refl
  tr-· ≤ω 𝟘  = refl
  tr-· ≤ω 𝟙  = refl
  tr-· ≤ω ≤𝟙 = refl
  tr-· ≤ω ≤ω = refl

  tr-∧ : ∀ p q → tr′ (p LA.∧ q) ≡ tr′ p A.∧ tr′ q
  tr-∧ 𝟘  𝟘  = refl
  tr-∧ 𝟘  𝟙  = refl
  tr-∧ 𝟘  ≤𝟙 = refl
  tr-∧ 𝟘  ≤ω = refl
  tr-∧ 𝟙  𝟘  = refl
  tr-∧ 𝟙  𝟙  = refl
  tr-∧ 𝟙  ≤𝟙 = refl
  tr-∧ 𝟙  ≤ω = refl
  tr-∧ ≤𝟙 𝟘  = refl
  tr-∧ ≤𝟙 𝟙  = refl
  tr-∧ ≤𝟙 ≤𝟙 = refl
  tr-∧ ≤𝟙 ≤ω = refl
  tr-∧ ≤ω 𝟘  = refl
  tr-∧ ≤ω 𝟙  = refl
  tr-∧ ≤ω ≤𝟙 = refl
  tr-∧ ≤ω ≤ω = refl

  tr-nr :
    ∀ p r z s n →
    tr′ (LA.nr p r z s n) ≡
    A.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘  𝟘  𝟘  𝟘  𝟘  → refl
    𝟘  𝟘  𝟘  𝟘  𝟙  → refl
    𝟘  𝟘  𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟘  𝟘  𝟘  ≤ω → refl
    𝟘  𝟘  𝟘  𝟙  𝟘  → refl
    𝟘  𝟘  𝟘  𝟙  𝟙  → refl
    𝟘  𝟘  𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟘  𝟘  𝟙  ≤ω → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟘  → refl
    𝟘  𝟘  𝟘  ≤𝟙 𝟙  → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  𝟘  ≤𝟙 ≤ω → refl
    𝟘  𝟘  𝟘  ≤ω 𝟘  → refl
    𝟘  𝟘  𝟘  ≤ω 𝟙  → refl
    𝟘  𝟘  𝟘  ≤ω ≤𝟙 → refl
    𝟘  𝟘  𝟘  ≤ω ≤ω → refl
    𝟘  𝟘  𝟙  𝟘  𝟘  → refl
    𝟘  𝟘  𝟙  𝟘  𝟙  → refl
    𝟘  𝟘  𝟙  𝟘  ≤𝟙 → refl
    𝟘  𝟘  𝟙  𝟘  ≤ω → refl
    𝟘  𝟘  𝟙  𝟙  𝟘  → refl
    𝟘  𝟘  𝟙  𝟙  𝟙  → refl
    𝟘  𝟘  𝟙  𝟙  ≤𝟙 → refl
    𝟘  𝟘  𝟙  𝟙  ≤ω → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟘  → refl
    𝟘  𝟘  𝟙  ≤𝟙 𝟙  → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  𝟙  ≤𝟙 ≤ω → refl
    𝟘  𝟘  𝟙  ≤ω 𝟘  → refl
    𝟘  𝟘  𝟙  ≤ω 𝟙  → refl
    𝟘  𝟘  𝟙  ≤ω ≤𝟙 → refl
    𝟘  𝟘  𝟙  ≤ω ≤ω → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟘  → refl
    𝟘  𝟘  ≤𝟙 𝟘  𝟙  → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 𝟘  ≤ω → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟘  → refl
    𝟘  𝟘  ≤𝟙 𝟙  𝟙  → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 𝟙  ≤ω → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟘  → refl
    𝟘  𝟘  ≤𝟙 ≤ω 𝟙  → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  𝟘  ≤𝟙 ≤ω ≤ω → refl
    𝟘  𝟘  ≤ω 𝟘  𝟘  → refl
    𝟘  𝟘  ≤ω 𝟘  𝟙  → refl
    𝟘  𝟘  ≤ω 𝟘  ≤𝟙 → refl
    𝟘  𝟘  ≤ω 𝟘  ≤ω → refl
    𝟘  𝟘  ≤ω 𝟙  𝟘  → refl
    𝟘  𝟘  ≤ω 𝟙  𝟙  → refl
    𝟘  𝟘  ≤ω 𝟙  ≤𝟙 → refl
    𝟘  𝟘  ≤ω 𝟙  ≤ω → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟘  → refl
    𝟘  𝟘  ≤ω ≤𝟙 𝟙  → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  𝟘  ≤ω ≤𝟙 ≤ω → refl
    𝟘  𝟘  ≤ω ≤ω 𝟘  → refl
    𝟘  𝟘  ≤ω ≤ω 𝟙  → refl
    𝟘  𝟘  ≤ω ≤ω ≤𝟙 → refl
    𝟘  𝟘  ≤ω ≤ω ≤ω → refl
    𝟘  𝟙  𝟘  𝟘  𝟘  → refl
    𝟘  𝟙  𝟘  𝟘  𝟙  → refl
    𝟘  𝟙  𝟘  𝟘  ≤𝟙 → refl
    𝟘  𝟙  𝟘  𝟘  ≤ω → refl
    𝟘  𝟙  𝟘  𝟙  𝟘  → refl
    𝟘  𝟙  𝟘  𝟙  𝟙  → refl
    𝟘  𝟙  𝟘  𝟙  ≤𝟙 → refl
    𝟘  𝟙  𝟘  𝟙  ≤ω → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟘  → refl
    𝟘  𝟙  𝟘  ≤𝟙 𝟙  → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  𝟘  ≤𝟙 ≤ω → refl
    𝟘  𝟙  𝟘  ≤ω 𝟘  → refl
    𝟘  𝟙  𝟘  ≤ω 𝟙  → refl
    𝟘  𝟙  𝟘  ≤ω ≤𝟙 → refl
    𝟘  𝟙  𝟘  ≤ω ≤ω → refl
    𝟘  𝟙  𝟙  𝟘  𝟘  → refl
    𝟘  𝟙  𝟙  𝟘  𝟙  → refl
    𝟘  𝟙  𝟙  𝟘  ≤𝟙 → refl
    𝟘  𝟙  𝟙  𝟘  ≤ω → refl
    𝟘  𝟙  𝟙  𝟙  𝟘  → refl
    𝟘  𝟙  𝟙  𝟙  𝟙  → refl
    𝟘  𝟙  𝟙  𝟙  ≤𝟙 → refl
    𝟘  𝟙  𝟙  𝟙  ≤ω → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟘  → refl
    𝟘  𝟙  𝟙  ≤𝟙 𝟙  → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  𝟙  ≤𝟙 ≤ω → refl
    𝟘  𝟙  𝟙  ≤ω 𝟘  → refl
    𝟘  𝟙  𝟙  ≤ω 𝟙  → refl
    𝟘  𝟙  𝟙  ≤ω ≤𝟙 → refl
    𝟘  𝟙  𝟙  ≤ω ≤ω → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟘  → refl
    𝟘  𝟙  ≤𝟙 𝟘  𝟙  → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 𝟘  ≤ω → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟘  → refl
    𝟘  𝟙  ≤𝟙 𝟙  𝟙  → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 𝟙  ≤ω → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟘  → refl
    𝟘  𝟙  ≤𝟙 ≤ω 𝟙  → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  𝟙  ≤𝟙 ≤ω ≤ω → refl
    𝟘  𝟙  ≤ω 𝟘  𝟘  → refl
    𝟘  𝟙  ≤ω 𝟘  𝟙  → refl
    𝟘  𝟙  ≤ω 𝟘  ≤𝟙 → refl
    𝟘  𝟙  ≤ω 𝟘  ≤ω → refl
    𝟘  𝟙  ≤ω 𝟙  𝟘  → refl
    𝟘  𝟙  ≤ω 𝟙  𝟙  → refl
    𝟘  𝟙  ≤ω 𝟙  ≤𝟙 → refl
    𝟘  𝟙  ≤ω 𝟙  ≤ω → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟘  → refl
    𝟘  𝟙  ≤ω ≤𝟙 𝟙  → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  𝟙  ≤ω ≤𝟙 ≤ω → refl
    𝟘  𝟙  ≤ω ≤ω 𝟘  → refl
    𝟘  𝟙  ≤ω ≤ω 𝟙  → refl
    𝟘  𝟙  ≤ω ≤ω ≤𝟙 → refl
    𝟘  𝟙  ≤ω ≤ω ≤ω → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟘  → refl
    𝟘  ≤𝟙 𝟘  𝟘  𝟙  → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  𝟘  ≤ω → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟘  → refl
    𝟘  ≤𝟙 𝟘  𝟙  𝟙  → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟘  → refl
    𝟘  ≤𝟙 𝟘  ≤ω 𝟙  → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 𝟘  ≤ω ≤ω → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟘  → refl
    𝟘  ≤𝟙 𝟙  𝟘  𝟙  → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  𝟘  ≤ω → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟘  → refl
    𝟘  ≤𝟙 𝟙  𝟙  𝟙  → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  𝟙  ≤ω → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟘  → refl
    𝟘  ≤𝟙 𝟙  ≤ω 𝟙  → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 𝟙  ≤ω ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟘  → refl
    𝟘  ≤𝟙 ≤ω 𝟘  𝟙  → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω 𝟘  ≤ω → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟘  → refl
    𝟘  ≤𝟙 ≤ω 𝟙  𝟙  → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω 𝟙  ≤ω → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟘  → refl
    𝟘  ≤𝟙 ≤ω ≤ω 𝟙  → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    𝟘  ≤𝟙 ≤ω ≤ω ≤ω → refl
    𝟘  ≤ω 𝟘  𝟘  𝟘  → refl
    𝟘  ≤ω 𝟘  𝟘  𝟙  → refl
    𝟘  ≤ω 𝟘  𝟘  ≤𝟙 → refl
    𝟘  ≤ω 𝟘  𝟘  ≤ω → refl
    𝟘  ≤ω 𝟘  𝟙  𝟘  → refl
    𝟘  ≤ω 𝟘  𝟙  𝟙  → refl
    𝟘  ≤ω 𝟘  𝟙  ≤𝟙 → refl
    𝟘  ≤ω 𝟘  𝟙  ≤ω → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟘  → refl
    𝟘  ≤ω 𝟘  ≤𝟙 𝟙  → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω 𝟘  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟘  ≤ω 𝟙  → refl
    𝟘  ≤ω 𝟘  ≤ω ≤𝟙 → refl
    𝟘  ≤ω 𝟘  ≤ω ≤ω → refl
    𝟘  ≤ω 𝟙  𝟘  𝟘  → refl
    𝟘  ≤ω 𝟙  𝟘  𝟙  → refl
    𝟘  ≤ω 𝟙  𝟘  ≤𝟙 → refl
    𝟘  ≤ω 𝟙  𝟘  ≤ω → refl
    𝟘  ≤ω 𝟙  𝟙  𝟘  → refl
    𝟘  ≤ω 𝟙  𝟙  𝟙  → refl
    𝟘  ≤ω 𝟙  𝟙  ≤𝟙 → refl
    𝟘  ≤ω 𝟙  𝟙  ≤ω → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟘  → refl
    𝟘  ≤ω 𝟙  ≤𝟙 𝟙  → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω 𝟙  ≤𝟙 ≤ω → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟘  → refl
    𝟘  ≤ω 𝟙  ≤ω 𝟙  → refl
    𝟘  ≤ω 𝟙  ≤ω ≤𝟙 → refl
    𝟘  ≤ω 𝟙  ≤ω ≤ω → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟘  → refl
    𝟘  ≤ω ≤𝟙 𝟘  𝟙  → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 𝟘  ≤ω → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟘  → refl
    𝟘  ≤ω ≤𝟙 𝟙  𝟙  → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 𝟙  ≤ω → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟘  → refl
    𝟘  ≤ω ≤𝟙 ≤ω 𝟙  → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤𝟙 ≤ω ≤ω → refl
    𝟘  ≤ω ≤ω 𝟘  𝟘  → refl
    𝟘  ≤ω ≤ω 𝟘  𝟙  → refl
    𝟘  ≤ω ≤ω 𝟘  ≤𝟙 → refl
    𝟘  ≤ω ≤ω 𝟘  ≤ω → refl
    𝟘  ≤ω ≤ω 𝟙  𝟘  → refl
    𝟘  ≤ω ≤ω 𝟙  𝟙  → refl
    𝟘  ≤ω ≤ω 𝟙  ≤𝟙 → refl
    𝟘  ≤ω ≤ω 𝟙  ≤ω → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟘  → refl
    𝟘  ≤ω ≤ω ≤𝟙 𝟙  → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    𝟘  ≤ω ≤ω ≤𝟙 ≤ω → refl
    𝟘  ≤ω ≤ω ≤ω 𝟘  → refl
    𝟘  ≤ω ≤ω ≤ω 𝟙  → refl
    𝟘  ≤ω ≤ω ≤ω ≤𝟙 → refl
    𝟘  ≤ω ≤ω ≤ω ≤ω → refl
    𝟙  𝟘  𝟘  𝟘  𝟘  → refl
    𝟙  𝟘  𝟘  𝟘  𝟙  → refl
    𝟙  𝟘  𝟘  𝟘  ≤𝟙 → refl
    𝟙  𝟘  𝟘  𝟘  ≤ω → refl
    𝟙  𝟘  𝟘  𝟙  𝟘  → refl
    𝟙  𝟘  𝟘  𝟙  𝟙  → refl
    𝟙  𝟘  𝟘  𝟙  ≤𝟙 → refl
    𝟙  𝟘  𝟘  𝟙  ≤ω → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟘  → refl
    𝟙  𝟘  𝟘  ≤𝟙 𝟙  → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  𝟘  ≤𝟙 ≤ω → refl
    𝟙  𝟘  𝟘  ≤ω 𝟘  → refl
    𝟙  𝟘  𝟘  ≤ω 𝟙  → refl
    𝟙  𝟘  𝟘  ≤ω ≤𝟙 → refl
    𝟙  𝟘  𝟘  ≤ω ≤ω → refl
    𝟙  𝟘  𝟙  𝟘  𝟘  → refl
    𝟙  𝟘  𝟙  𝟘  𝟙  → refl
    𝟙  𝟘  𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟘  𝟙  𝟘  ≤ω → refl
    𝟙  𝟘  𝟙  𝟙  𝟘  → refl
    𝟙  𝟘  𝟙  𝟙  𝟙  → refl
    𝟙  𝟘  𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟘  𝟙  𝟙  ≤ω → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟘  → refl
    𝟙  𝟘  𝟙  ≤𝟙 𝟙  → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  𝟙  ≤𝟙 ≤ω → refl
    𝟙  𝟘  𝟙  ≤ω 𝟘  → refl
    𝟙  𝟘  𝟙  ≤ω 𝟙  → refl
    𝟙  𝟘  𝟙  ≤ω ≤𝟙 → refl
    𝟙  𝟘  𝟙  ≤ω ≤ω → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟘  → refl
    𝟙  𝟘  ≤𝟙 𝟘  𝟙  → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 𝟘  ≤ω → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟘  → refl
    𝟙  𝟘  ≤𝟙 𝟙  𝟙  → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 𝟙  ≤ω → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟘  → refl
    𝟙  𝟘  ≤𝟙 ≤ω 𝟙  → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  𝟘  ≤𝟙 ≤ω ≤ω → refl
    𝟙  𝟘  ≤ω 𝟘  𝟘  → refl
    𝟙  𝟘  ≤ω 𝟘  𝟙  → refl
    𝟙  𝟘  ≤ω 𝟘  ≤𝟙 → refl
    𝟙  𝟘  ≤ω 𝟘  ≤ω → refl
    𝟙  𝟘  ≤ω 𝟙  𝟘  → refl
    𝟙  𝟘  ≤ω 𝟙  𝟙  → refl
    𝟙  𝟘  ≤ω 𝟙  ≤𝟙 → refl
    𝟙  𝟘  ≤ω 𝟙  ≤ω → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟘  → refl
    𝟙  𝟘  ≤ω ≤𝟙 𝟙  → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  𝟘  ≤ω ≤𝟙 ≤ω → refl
    𝟙  𝟘  ≤ω ≤ω 𝟘  → refl
    𝟙  𝟘  ≤ω ≤ω 𝟙  → refl
    𝟙  𝟘  ≤ω ≤ω ≤𝟙 → refl
    𝟙  𝟘  ≤ω ≤ω ≤ω → refl
    𝟙  𝟙  𝟘  𝟘  𝟘  → refl
    𝟙  𝟙  𝟘  𝟘  𝟙  → refl
    𝟙  𝟙  𝟘  𝟘  ≤𝟙 → refl
    𝟙  𝟙  𝟘  𝟘  ≤ω → refl
    𝟙  𝟙  𝟘  𝟙  𝟘  → refl
    𝟙  𝟙  𝟘  𝟙  𝟙  → refl
    𝟙  𝟙  𝟘  𝟙  ≤𝟙 → refl
    𝟙  𝟙  𝟘  𝟙  ≤ω → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟘  → refl
    𝟙  𝟙  𝟘  ≤𝟙 𝟙  → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  𝟘  ≤𝟙 ≤ω → refl
    𝟙  𝟙  𝟘  ≤ω 𝟘  → refl
    𝟙  𝟙  𝟘  ≤ω 𝟙  → refl
    𝟙  𝟙  𝟘  ≤ω ≤𝟙 → refl
    𝟙  𝟙  𝟘  ≤ω ≤ω → refl
    𝟙  𝟙  𝟙  𝟘  𝟘  → refl
    𝟙  𝟙  𝟙  𝟘  𝟙  → refl
    𝟙  𝟙  𝟙  𝟘  ≤𝟙 → refl
    𝟙  𝟙  𝟙  𝟘  ≤ω → refl
    𝟙  𝟙  𝟙  𝟙  𝟘  → refl
    𝟙  𝟙  𝟙  𝟙  𝟙  → refl
    𝟙  𝟙  𝟙  𝟙  ≤𝟙 → refl
    𝟙  𝟙  𝟙  𝟙  ≤ω → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟘  → refl
    𝟙  𝟙  𝟙  ≤𝟙 𝟙  → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  𝟙  ≤𝟙 ≤ω → refl
    𝟙  𝟙  𝟙  ≤ω 𝟘  → refl
    𝟙  𝟙  𝟙  ≤ω 𝟙  → refl
    𝟙  𝟙  𝟙  ≤ω ≤𝟙 → refl
    𝟙  𝟙  𝟙  ≤ω ≤ω → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟘  → refl
    𝟙  𝟙  ≤𝟙 𝟘  𝟙  → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 𝟘  ≤ω → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟘  → refl
    𝟙  𝟙  ≤𝟙 𝟙  𝟙  → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 𝟙  ≤ω → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟘  → refl
    𝟙  𝟙  ≤𝟙 ≤ω 𝟙  → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  𝟙  ≤𝟙 ≤ω ≤ω → refl
    𝟙  𝟙  ≤ω 𝟘  𝟘  → refl
    𝟙  𝟙  ≤ω 𝟘  𝟙  → refl
    𝟙  𝟙  ≤ω 𝟘  ≤𝟙 → refl
    𝟙  𝟙  ≤ω 𝟘  ≤ω → refl
    𝟙  𝟙  ≤ω 𝟙  𝟘  → refl
    𝟙  𝟙  ≤ω 𝟙  𝟙  → refl
    𝟙  𝟙  ≤ω 𝟙  ≤𝟙 → refl
    𝟙  𝟙  ≤ω 𝟙  ≤ω → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟘  → refl
    𝟙  𝟙  ≤ω ≤𝟙 𝟙  → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  𝟙  ≤ω ≤𝟙 ≤ω → refl
    𝟙  𝟙  ≤ω ≤ω 𝟘  → refl
    𝟙  𝟙  ≤ω ≤ω 𝟙  → refl
    𝟙  𝟙  ≤ω ≤ω ≤𝟙 → refl
    𝟙  𝟙  ≤ω ≤ω ≤ω → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟘  → refl
    𝟙  ≤𝟙 𝟘  𝟘  𝟙  → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  𝟘  ≤ω → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟘  → refl
    𝟙  ≤𝟙 𝟘  𝟙  𝟙  → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟘  → refl
    𝟙  ≤𝟙 𝟘  ≤ω 𝟙  → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 𝟘  ≤ω ≤ω → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟘  → refl
    𝟙  ≤𝟙 𝟙  𝟘  𝟙  → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  𝟘  ≤ω → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟘  → refl
    𝟙  ≤𝟙 𝟙  𝟙  𝟙  → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  𝟙  ≤ω → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟘  → refl
    𝟙  ≤𝟙 𝟙  ≤ω 𝟙  → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 𝟙  ≤ω ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟘  → refl
    𝟙  ≤𝟙 ≤ω 𝟘  𝟙  → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω 𝟘  ≤ω → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟘  → refl
    𝟙  ≤𝟙 ≤ω 𝟙  𝟙  → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω 𝟙  ≤ω → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟘  → refl
    𝟙  ≤𝟙 ≤ω ≤ω 𝟙  → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    𝟙  ≤𝟙 ≤ω ≤ω ≤ω → refl
    𝟙  ≤ω 𝟘  𝟘  𝟘  → refl
    𝟙  ≤ω 𝟘  𝟘  𝟙  → refl
    𝟙  ≤ω 𝟘  𝟘  ≤𝟙 → refl
    𝟙  ≤ω 𝟘  𝟘  ≤ω → refl
    𝟙  ≤ω 𝟘  𝟙  𝟘  → refl
    𝟙  ≤ω 𝟘  𝟙  𝟙  → refl
    𝟙  ≤ω 𝟘  𝟙  ≤𝟙 → refl
    𝟙  ≤ω 𝟘  𝟙  ≤ω → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟘  → refl
    𝟙  ≤ω 𝟘  ≤𝟙 𝟙  → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω 𝟘  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟘  ≤ω 𝟙  → refl
    𝟙  ≤ω 𝟘  ≤ω ≤𝟙 → refl
    𝟙  ≤ω 𝟘  ≤ω ≤ω → refl
    𝟙  ≤ω 𝟙  𝟘  𝟘  → refl
    𝟙  ≤ω 𝟙  𝟘  𝟙  → refl
    𝟙  ≤ω 𝟙  𝟘  ≤𝟙 → refl
    𝟙  ≤ω 𝟙  𝟘  ≤ω → refl
    𝟙  ≤ω 𝟙  𝟙  𝟘  → refl
    𝟙  ≤ω 𝟙  𝟙  𝟙  → refl
    𝟙  ≤ω 𝟙  𝟙  ≤𝟙 → refl
    𝟙  ≤ω 𝟙  𝟙  ≤ω → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟘  → refl
    𝟙  ≤ω 𝟙  ≤𝟙 𝟙  → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω 𝟙  ≤𝟙 ≤ω → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟘  → refl
    𝟙  ≤ω 𝟙  ≤ω 𝟙  → refl
    𝟙  ≤ω 𝟙  ≤ω ≤𝟙 → refl
    𝟙  ≤ω 𝟙  ≤ω ≤ω → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟘  → refl
    𝟙  ≤ω ≤𝟙 𝟘  𝟙  → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 𝟘  ≤ω → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟘  → refl
    𝟙  ≤ω ≤𝟙 𝟙  𝟙  → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 𝟙  ≤ω → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟘  → refl
    𝟙  ≤ω ≤𝟙 ≤ω 𝟙  → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤𝟙 ≤ω ≤ω → refl
    𝟙  ≤ω ≤ω 𝟘  𝟘  → refl
    𝟙  ≤ω ≤ω 𝟘  𝟙  → refl
    𝟙  ≤ω ≤ω 𝟘  ≤𝟙 → refl
    𝟙  ≤ω ≤ω 𝟘  ≤ω → refl
    𝟙  ≤ω ≤ω 𝟙  𝟘  → refl
    𝟙  ≤ω ≤ω 𝟙  𝟙  → refl
    𝟙  ≤ω ≤ω 𝟙  ≤𝟙 → refl
    𝟙  ≤ω ≤ω 𝟙  ≤ω → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟘  → refl
    𝟙  ≤ω ≤ω ≤𝟙 𝟙  → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    𝟙  ≤ω ≤ω ≤𝟙 ≤ω → refl
    𝟙  ≤ω ≤ω ≤ω 𝟘  → refl
    𝟙  ≤ω ≤ω ≤ω 𝟙  → refl
    𝟙  ≤ω ≤ω ≤ω ≤𝟙 → refl
    𝟙  ≤ω ≤ω ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟘  𝟘  𝟙  → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  𝟘  ≤ω → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟘  → refl
    ≤𝟙 𝟘  𝟘  𝟙  𝟙  → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  𝟙  ≤ω → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟘  → refl
    ≤𝟙 𝟘  𝟘  ≤ω 𝟙  → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  𝟘  ≤ω ≤ω → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟘  → refl
    ≤𝟙 𝟘  𝟙  𝟘  𝟙  → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  𝟘  ≤ω → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟘  → refl
    ≤𝟙 𝟘  𝟙  𝟙  𝟙  → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  𝟙  ≤ω → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟘  → refl
    ≤𝟙 𝟘  𝟙  ≤ω 𝟙  → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟘  → refl
    ≤𝟙 𝟘  ≤ω 𝟘  𝟙  → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω 𝟘  ≤ω → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟘  → refl
    ≤𝟙 𝟘  ≤ω 𝟙  𝟙  → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω 𝟙  ≤ω → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟘  → refl
    ≤𝟙 𝟘  ≤ω ≤ω 𝟙  → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 𝟘  ≤ω ≤ω ≤ω → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟘  → refl
    ≤𝟙 𝟙  𝟘  𝟘  𝟙  → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟘  𝟙  𝟙  → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  𝟙  ≤ω → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟘  → refl
    ≤𝟙 𝟙  𝟘  ≤ω 𝟙  → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  𝟘  ≤ω ≤ω → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟘  → refl
    ≤𝟙 𝟙  𝟙  𝟘  𝟙  → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  𝟘  ≤ω → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟘  → refl
    ≤𝟙 𝟙  𝟙  𝟙  𝟙  → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  𝟙  ≤ω → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟘  → refl
    ≤𝟙 𝟙  𝟙  ≤ω 𝟙  → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  𝟙  ≤ω ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟘  → refl
    ≤𝟙 𝟙  ≤ω 𝟘  𝟙  → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω 𝟘  ≤ω → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟘  → refl
    ≤𝟙 𝟙  ≤ω 𝟙  𝟙  → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω 𝟙  ≤ω → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟘  → refl
    ≤𝟙 𝟙  ≤ω ≤ω 𝟙  → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 𝟙  ≤ω ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟘  ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 𝟙  ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟘  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω 𝟙  ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟘  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω 𝟙  → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 ≤𝟙 ≤ω ≤ω ≤ω → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟘  → refl
    ≤𝟙 ≤ω 𝟘  𝟘  𝟙  → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  𝟘  ≤ω → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟘  → refl
    ≤𝟙 ≤ω 𝟘  𝟙  𝟙  → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  𝟙  ≤ω → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟘  ≤ω 𝟙  → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟘  ≤ω ≤ω → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟘  → refl
    ≤𝟙 ≤ω 𝟙  𝟘  𝟙  → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  𝟘  ≤ω → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟘  → refl
    ≤𝟙 ≤ω 𝟙  𝟙  𝟙  → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  𝟙  ≤ω → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟘  → refl
    ≤𝟙 ≤ω 𝟙  ≤ω 𝟙  → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω 𝟙  ≤ω ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 𝟘  ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 𝟙  ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟘  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤𝟙 ≤ω ≤ω → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟘  → refl
    ≤𝟙 ≤ω ≤ω 𝟘  𝟙  → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω 𝟘  ≤ω → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟘  → refl
    ≤𝟙 ≤ω ≤ω 𝟙  𝟙  → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω 𝟙  ≤ω → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟘  → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 𝟙  → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω ≤𝟙 ≤ω → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟘  → refl
    ≤𝟙 ≤ω ≤ω ≤ω 𝟙  → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤𝟙 → refl
    ≤𝟙 ≤ω ≤ω ≤ω ≤ω → refl
    ≤ω 𝟘  𝟘  𝟘  𝟘  → refl
    ≤ω 𝟘  𝟘  𝟘  𝟙  → refl
    ≤ω 𝟘  𝟘  𝟘  ≤𝟙 → refl
    ≤ω 𝟘  𝟘  𝟘  ≤ω → refl
    ≤ω 𝟘  𝟘  𝟙  𝟘  → refl
    ≤ω 𝟘  𝟘  𝟙  𝟙  → refl
    ≤ω 𝟘  𝟘  𝟙  ≤𝟙 → refl
    ≤ω 𝟘  𝟘  𝟙  ≤ω → refl
    ≤ω 𝟘  𝟘  ≤𝟙 𝟘  → refl
    ≤ω 𝟘  𝟘  ≤𝟙 𝟙  → refl
    ≤ω 𝟘  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  𝟘  ≤𝟙 ≤ω → refl
    ≤ω 𝟘  𝟘  ≤ω 𝟘  → refl
    ≤ω 𝟘  𝟘  ≤ω 𝟙  → refl
    ≤ω 𝟘  𝟘  ≤ω ≤𝟙 → refl
    ≤ω 𝟘  𝟘  ≤ω ≤ω → refl
    ≤ω 𝟘  𝟙  𝟘  𝟘  → refl
    ≤ω 𝟘  𝟙  𝟘  𝟙  → refl
    ≤ω 𝟘  𝟙  𝟘  ≤𝟙 → refl
    ≤ω 𝟘  𝟙  𝟘  ≤ω → refl
    ≤ω 𝟘  𝟙  𝟙  𝟘  → refl
    ≤ω 𝟘  𝟙  𝟙  𝟙  → refl
    ≤ω 𝟘  𝟙  𝟙  ≤𝟙 → refl
    ≤ω 𝟘  𝟙  𝟙  ≤ω → refl
    ≤ω 𝟘  𝟙  ≤𝟙 𝟘  → refl
    ≤ω 𝟘  𝟙  ≤𝟙 𝟙  → refl
    ≤ω 𝟘  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  𝟙  ≤𝟙 ≤ω → refl
    ≤ω 𝟘  𝟙  ≤ω 𝟘  → refl
    ≤ω 𝟘  𝟙  ≤ω 𝟙  → refl
    ≤ω 𝟘  𝟙  ≤ω ≤𝟙 → refl
    ≤ω 𝟘  𝟙  ≤ω ≤ω → refl
    ≤ω 𝟘  ≤𝟙 𝟘  𝟘  → refl
    ≤ω 𝟘  ≤𝟙 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 𝟘  ≤ω → refl
    ≤ω 𝟘  ≤𝟙 𝟙  𝟘  → refl
    ≤ω 𝟘  ≤𝟙 𝟙  𝟙  → refl
    ≤ω 𝟘  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 𝟙  ≤ω → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω 𝟘  ≤𝟙 ≤ω 𝟘  → refl
    ≤ω 𝟘  ≤𝟙 ≤ω 𝟙  → refl
    ≤ω 𝟘  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω 𝟘  ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟘  ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟘  ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟘  ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟘  ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟘  ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟘  ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟘  ≤ω 𝟙  ≤ω → refl
    ≤ω 𝟘  ≤ω ≤𝟙 𝟘  → refl
    ≤ω 𝟘  ≤ω ≤𝟙 𝟙  → refl
    ≤ω 𝟘  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟘  ≤ω ≤𝟙 ≤ω → refl
    ≤ω 𝟘  ≤ω ≤ω 𝟘  → refl
    ≤ω 𝟘  ≤ω ≤ω 𝟙  → refl
    ≤ω 𝟘  ≤ω ≤ω ≤𝟙 → refl
    ≤ω 𝟘  ≤ω ≤ω ≤ω → refl
    ≤ω 𝟙  𝟘  𝟘  𝟘  → refl
    ≤ω 𝟙  𝟘  𝟘  𝟙  → refl
    ≤ω 𝟙  𝟘  𝟘  ≤𝟙 → refl
    ≤ω 𝟙  𝟘  𝟘  ≤ω → refl
    ≤ω 𝟙  𝟘  𝟙  𝟘  → refl
    ≤ω 𝟙  𝟘  𝟙  𝟙  → refl
    ≤ω 𝟙  𝟘  𝟙  ≤𝟙 → refl
    ≤ω 𝟙  𝟘  𝟙  ≤ω → refl
    ≤ω 𝟙  𝟘  ≤𝟙 𝟘  → refl
    ≤ω 𝟙  𝟘  ≤𝟙 𝟙  → refl
    ≤ω 𝟙  𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  𝟘  ≤𝟙 ≤ω → refl
    ≤ω 𝟙  𝟘  ≤ω 𝟘  → refl
    ≤ω 𝟙  𝟘  ≤ω 𝟙  → refl
    ≤ω 𝟙  𝟘  ≤ω ≤𝟙 → refl
    ≤ω 𝟙  𝟘  ≤ω ≤ω → refl
    ≤ω 𝟙  𝟙  𝟘  𝟘  → refl
    ≤ω 𝟙  𝟙  𝟘  𝟙  → refl
    ≤ω 𝟙  𝟙  𝟘  ≤𝟙 → refl
    ≤ω 𝟙  𝟙  𝟘  ≤ω → refl
    ≤ω 𝟙  𝟙  𝟙  𝟘  → refl
    ≤ω 𝟙  𝟙  𝟙  𝟙  → refl
    ≤ω 𝟙  𝟙  𝟙  ≤𝟙 → refl
    ≤ω 𝟙  𝟙  𝟙  ≤ω → refl
    ≤ω 𝟙  𝟙  ≤𝟙 𝟘  → refl
    ≤ω 𝟙  𝟙  ≤𝟙 𝟙  → refl
    ≤ω 𝟙  𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  𝟙  ≤𝟙 ≤ω → refl
    ≤ω 𝟙  𝟙  ≤ω 𝟘  → refl
    ≤ω 𝟙  𝟙  ≤ω 𝟙  → refl
    ≤ω 𝟙  𝟙  ≤ω ≤𝟙 → refl
    ≤ω 𝟙  𝟙  ≤ω ≤ω → refl
    ≤ω 𝟙  ≤𝟙 𝟘  𝟘  → refl
    ≤ω 𝟙  ≤𝟙 𝟘  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 𝟘  ≤ω → refl
    ≤ω 𝟙  ≤𝟙 𝟙  𝟘  → refl
    ≤ω 𝟙  ≤𝟙 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 𝟙  ≤ω → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω 𝟙  ≤𝟙 ≤ω 𝟘  → refl
    ≤ω 𝟙  ≤𝟙 ≤ω 𝟙  → refl
    ≤ω 𝟙  ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω 𝟙  ≤𝟙 ≤ω ≤ω → refl
    ≤ω 𝟙  ≤ω 𝟘  𝟘  → refl
    ≤ω 𝟙  ≤ω 𝟘  𝟙  → refl
    ≤ω 𝟙  ≤ω 𝟘  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω 𝟘  ≤ω → refl
    ≤ω 𝟙  ≤ω 𝟙  𝟘  → refl
    ≤ω 𝟙  ≤ω 𝟙  𝟙  → refl
    ≤ω 𝟙  ≤ω 𝟙  ≤𝟙 → refl
    ≤ω 𝟙  ≤ω 𝟙  ≤ω → refl
    ≤ω 𝟙  ≤ω ≤𝟙 𝟘  → refl
    ≤ω 𝟙  ≤ω ≤𝟙 𝟙  → refl
    ≤ω 𝟙  ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω 𝟙  ≤ω ≤𝟙 ≤ω → refl
    ≤ω 𝟙  ≤ω ≤ω 𝟘  → refl
    ≤ω 𝟙  ≤ω ≤ω 𝟙  → refl
    ≤ω 𝟙  ≤ω ≤ω ≤𝟙 → refl
    ≤ω 𝟙  ≤ω ≤ω ≤ω → refl
    ≤ω ≤𝟙 𝟘  𝟘  𝟘  → refl
    ≤ω ≤𝟙 𝟘  𝟘  𝟙  → refl
    ≤ω ≤𝟙 𝟘  𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  𝟘  ≤ω → refl
    ≤ω ≤𝟙 𝟘  𝟙  𝟘  → refl
    ≤ω ≤𝟙 𝟘  𝟙  𝟙  → refl
    ≤ω ≤𝟙 𝟘  𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 𝟘  ≤ω 𝟘  → refl
    ≤ω ≤𝟙 𝟘  ≤ω 𝟙  → refl
    ≤ω ≤𝟙 𝟘  ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 𝟘  ≤ω ≤ω → refl
    ≤ω ≤𝟙 𝟙  𝟘  𝟘  → refl
    ≤ω ≤𝟙 𝟙  𝟘  𝟙  → refl
    ≤ω ≤𝟙 𝟙  𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  𝟘  ≤ω → refl
    ≤ω ≤𝟙 𝟙  𝟙  𝟘  → refl
    ≤ω ≤𝟙 𝟙  𝟙  𝟙  → refl
    ≤ω ≤𝟙 𝟙  𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  𝟙  ≤ω → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 𝟙  ≤ω 𝟘  → refl
    ≤ω ≤𝟙 𝟙  ≤ω 𝟙  → refl
    ≤ω ≤𝟙 𝟙  ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 𝟙  ≤ω ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 𝟘  ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 𝟙  ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω 𝟘  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω 𝟙  → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 ≤𝟙 ≤ω ≤ω → refl
    ≤ω ≤𝟙 ≤ω 𝟘  𝟘  → refl
    ≤ω ≤𝟙 ≤ω 𝟘  𝟙  → refl
    ≤ω ≤𝟙 ≤ω 𝟘  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω 𝟘  ≤ω → refl
    ≤ω ≤𝟙 ≤ω 𝟙  𝟘  → refl
    ≤ω ≤𝟙 ≤ω 𝟙  𝟙  → refl
    ≤ω ≤𝟙 ≤ω 𝟙  ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω 𝟙  ≤ω → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤𝟙 ≤ω ≤ω 𝟘  → refl
    ≤ω ≤𝟙 ≤ω ≤ω 𝟙  → refl
    ≤ω ≤𝟙 ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤𝟙 ≤ω ≤ω ≤ω → refl
    ≤ω ≤ω 𝟘  𝟘  𝟘  → refl
    ≤ω ≤ω 𝟘  𝟘  𝟙  → refl
    ≤ω ≤ω 𝟘  𝟘  ≤𝟙 → refl
    ≤ω ≤ω 𝟘  𝟘  ≤ω → refl
    ≤ω ≤ω 𝟘  𝟙  𝟘  → refl
    ≤ω ≤ω 𝟘  𝟙  𝟙  → refl
    ≤ω ≤ω 𝟘  𝟙  ≤𝟙 → refl
    ≤ω ≤ω 𝟘  𝟙  ≤ω → refl
    ≤ω ≤ω 𝟘  ≤𝟙 𝟘  → refl
    ≤ω ≤ω 𝟘  ≤𝟙 𝟙  → refl
    ≤ω ≤ω 𝟘  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω 𝟘  ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟘  ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟘  ≤ω 𝟙  → refl
    ≤ω ≤ω 𝟘  ≤ω ≤𝟙 → refl
    ≤ω ≤ω 𝟘  ≤ω ≤ω → refl
    ≤ω ≤ω 𝟙  𝟘  𝟘  → refl
    ≤ω ≤ω 𝟙  𝟘  𝟙  → refl
    ≤ω ≤ω 𝟙  𝟘  ≤𝟙 → refl
    ≤ω ≤ω 𝟙  𝟘  ≤ω → refl
    ≤ω ≤ω 𝟙  𝟙  𝟘  → refl
    ≤ω ≤ω 𝟙  𝟙  𝟙  → refl
    ≤ω ≤ω 𝟙  𝟙  ≤𝟙 → refl
    ≤ω ≤ω 𝟙  𝟙  ≤ω → refl
    ≤ω ≤ω 𝟙  ≤𝟙 𝟘  → refl
    ≤ω ≤ω 𝟙  ≤𝟙 𝟙  → refl
    ≤ω ≤ω 𝟙  ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω 𝟙  ≤𝟙 ≤ω → refl
    ≤ω ≤ω 𝟙  ≤ω 𝟘  → refl
    ≤ω ≤ω 𝟙  ≤ω 𝟙  → refl
    ≤ω ≤ω 𝟙  ≤ω ≤𝟙 → refl
    ≤ω ≤ω 𝟙  ≤ω ≤ω → refl
    ≤ω ≤ω ≤𝟙 𝟘  𝟘  → refl
    ≤ω ≤ω ≤𝟙 𝟘  𝟙  → refl
    ≤ω ≤ω ≤𝟙 𝟘  ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 𝟘  ≤ω → refl
    ≤ω ≤ω ≤𝟙 𝟙  𝟘  → refl
    ≤ω ≤ω ≤𝟙 𝟙  𝟙  → refl
    ≤ω ≤ω ≤𝟙 𝟙  ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 𝟙  ≤ω → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 𝟘  → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 𝟙  → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 ≤𝟙 ≤ω → refl
    ≤ω ≤ω ≤𝟙 ≤ω 𝟘  → refl
    ≤ω ≤ω ≤𝟙 ≤ω 𝟙  → refl
    ≤ω ≤ω ≤𝟙 ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤𝟙 ≤ω ≤ω → refl
    ≤ω ≤ω ≤ω 𝟘  𝟘  → refl
    ≤ω ≤ω ≤ω 𝟘  𝟙  → refl
    ≤ω ≤ω ≤ω 𝟘  ≤𝟙 → refl
    ≤ω ≤ω ≤ω 𝟘  ≤ω → refl
    ≤ω ≤ω ≤ω 𝟙  𝟘  → refl
    ≤ω ≤ω ≤ω 𝟙  𝟙  → refl
    ≤ω ≤ω ≤ω 𝟙  ≤𝟙 → refl
    ≤ω ≤ω ≤ω 𝟙  ≤ω → refl
    ≤ω ≤ω ≤ω ≤𝟙 𝟘  → refl
    ≤ω ≤ω ≤ω ≤𝟙 𝟙  → refl
    ≤ω ≤ω ≤ω ≤𝟙 ≤𝟙 → refl
    ≤ω ≤ω ≤ω ≤𝟙 ≤ω → refl
    ≤ω ≤ω ≤ω ≤ω 𝟘  → refl
    ≤ω ≤ω ≤ω ≤ω 𝟙  → refl
    ≤ω ≤ω ≤ω ≤ω ≤𝟙 → refl
    ≤ω ≤ω ≤ω ≤ω ≤ω → refl

-- The function linear-or-affine→affine is not an order embedding from
-- a linear or affine types modality to an affine types modality.

¬linear-or-affine⇨affine :
  ¬ Is-order-embedding (linear-or-affine v₁) (affineModality v₂)
      linear-or-affine→affine
¬linear-or-affine⇨affine m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ≤𝟙} refl of λ ()

-- The function affine→linearity is a morphism from an affine types
-- modality to a linear types modality if certain assumptions hold.

affine⇨linearity :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = affineModality v₁
      𝕄₂ = linearityModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ affine→linearity
affine⇨linearity {v₁ = v₁} {v₂ = v₂} refl s⇔s = λ where
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                           , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧ {p = p}              → ≤-reflexive (tr-∧ p _)
    .Is-morphism.tr-nr {r = r}             → ≤-reflexive
                                               (tr-nr _ r _ _ _)
    .Is-morphism.nr-in-first-iff-in-second → s⇔s
    .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
    .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
      (inj₁ ok) → inj₁ ok
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ (A.affine-has-well-behaved-zero v₁)
  where
  open Graded.Modality.Properties (linearityModality v₂)

  tr′ = affine→linearity

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-+ : ∀ p q → tr′ (p A.+ q) ≡ tr′ p L.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 𝟙 = refl
  tr-+ 𝟘 ω = refl
  tr-+ 𝟙 𝟘 = refl
  tr-+ 𝟙 𝟙 = refl
  tr-+ 𝟙 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω 𝟙 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p A.· q) ≡ tr′ p L.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 𝟙 = refl
  tr-· 𝟘 ω = refl
  tr-· 𝟙 𝟘 = refl
  tr-· 𝟙 𝟙 = refl
  tr-· 𝟙 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω 𝟙 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p A.∧ q) ≡ tr′ p L.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 𝟙 = refl
  tr-∧ 𝟘 ω = refl
  tr-∧ 𝟙 𝟘 = refl
  tr-∧ 𝟙 𝟙 = refl
  tr-∧ 𝟙 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω 𝟙 = refl
  tr-∧ ω ω = refl

  tr-nr :
    ∀ p r z s n →
    tr′ (A.nr p r z s n) ≡
    L.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘 𝟘 𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟘 𝟘 𝟙 → refl
    𝟘 𝟘 𝟘 𝟘 ω → refl
    𝟘 𝟘 𝟘 𝟙 𝟘 → refl
    𝟘 𝟘 𝟘 𝟙 𝟙 → refl
    𝟘 𝟘 𝟘 𝟙 ω → refl
    𝟘 𝟘 𝟘 ω 𝟘 → refl
    𝟘 𝟘 𝟘 ω 𝟙 → refl
    𝟘 𝟘 𝟘 ω ω → refl
    𝟘 𝟘 𝟙 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 𝟘 𝟙 → refl
    𝟘 𝟘 𝟙 𝟘 ω → refl
    𝟘 𝟘 𝟙 𝟙 𝟘 → refl
    𝟘 𝟘 𝟙 𝟙 𝟙 → refl
    𝟘 𝟘 𝟙 𝟙 ω → refl
    𝟘 𝟘 𝟙 ω 𝟘 → refl
    𝟘 𝟘 𝟙 ω 𝟙 → refl
    𝟘 𝟘 𝟙 ω ω → refl
    𝟘 𝟘 ω 𝟘 𝟘 → refl
    𝟘 𝟘 ω 𝟘 𝟙 → refl
    𝟘 𝟘 ω 𝟘 ω → refl
    𝟘 𝟘 ω 𝟙 𝟘 → refl
    𝟘 𝟘 ω 𝟙 𝟙 → refl
    𝟘 𝟘 ω 𝟙 ω → refl
    𝟘 𝟘 ω ω 𝟘 → refl
    𝟘 𝟘 ω ω 𝟙 → refl
    𝟘 𝟘 ω ω ω → refl
    𝟘 𝟙 𝟘 𝟘 𝟘 → refl
    𝟘 𝟙 𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 𝟘 ω → refl
    𝟘 𝟙 𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟘 𝟙 𝟙 → refl
    𝟘 𝟙 𝟘 𝟙 ω → refl
    𝟘 𝟙 𝟘 ω 𝟘 → refl
    𝟘 𝟙 𝟘 ω 𝟙 → refl
    𝟘 𝟙 𝟘 ω ω → refl
    𝟘 𝟙 𝟙 𝟘 𝟘 → refl
    𝟘 𝟙 𝟙 𝟘 𝟙 → refl
    𝟘 𝟙 𝟙 𝟘 ω → refl
    𝟘 𝟙 𝟙 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 𝟙 ω → refl
    𝟘 𝟙 𝟙 ω 𝟘 → refl
    𝟘 𝟙 𝟙 ω 𝟙 → refl
    𝟘 𝟙 𝟙 ω ω → refl
    𝟘 𝟙 ω 𝟘 𝟘 → refl
    𝟘 𝟙 ω 𝟘 𝟙 → refl
    𝟘 𝟙 ω 𝟘 ω → refl
    𝟘 𝟙 ω 𝟙 𝟘 → refl
    𝟘 𝟙 ω 𝟙 𝟙 → refl
    𝟘 𝟙 ω 𝟙 ω → refl
    𝟘 𝟙 ω ω 𝟘 → refl
    𝟘 𝟙 ω ω 𝟙 → refl
    𝟘 𝟙 ω ω ω → refl
    𝟘 ω 𝟘 𝟘 𝟘 → refl
    𝟘 ω 𝟘 𝟘 𝟙 → refl
    𝟘 ω 𝟘 𝟘 ω → refl
    𝟘 ω 𝟘 𝟙 𝟘 → refl
    𝟘 ω 𝟘 𝟙 𝟙 → refl
    𝟘 ω 𝟘 𝟙 ω → refl
    𝟘 ω 𝟘 ω 𝟘 → refl
    𝟘 ω 𝟘 ω 𝟙 → refl
    𝟘 ω 𝟘 ω ω → refl
    𝟘 ω 𝟙 𝟘 𝟘 → refl
    𝟘 ω 𝟙 𝟘 𝟙 → refl
    𝟘 ω 𝟙 𝟘 ω → refl
    𝟘 ω 𝟙 𝟙 𝟘 → refl
    𝟘 ω 𝟙 𝟙 𝟙 → refl
    𝟘 ω 𝟙 𝟙 ω → refl
    𝟘 ω 𝟙 ω 𝟘 → refl
    𝟘 ω 𝟙 ω 𝟙 → refl
    𝟘 ω 𝟙 ω ω → refl
    𝟘 ω ω 𝟘 𝟘 → refl
    𝟘 ω ω 𝟘 𝟙 → refl
    𝟘 ω ω 𝟘 ω → refl
    𝟘 ω ω 𝟙 𝟘 → refl
    𝟘 ω ω 𝟙 𝟙 → refl
    𝟘 ω ω 𝟙 ω → refl
    𝟘 ω ω ω 𝟘 → refl
    𝟘 ω ω ω 𝟙 → refl
    𝟘 ω ω ω ω → refl
    𝟙 𝟘 𝟘 𝟘 𝟘 → refl
    𝟙 𝟘 𝟘 𝟘 𝟙 → refl
    𝟙 𝟘 𝟘 𝟘 ω → refl
    𝟙 𝟘 𝟘 𝟙 𝟘 → refl
    𝟙 𝟘 𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 𝟙 ω → refl
    𝟙 𝟘 𝟘 ω 𝟘 → refl
    𝟙 𝟘 𝟘 ω 𝟙 → refl
    𝟙 𝟘 𝟘 ω ω → refl
    𝟙 𝟘 𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 𝟘 𝟙 → refl
    𝟙 𝟘 𝟙 𝟘 ω → refl
    𝟙 𝟘 𝟙 𝟙 𝟘 → refl
    𝟙 𝟘 𝟙 𝟙 𝟙 → refl
    𝟙 𝟘 𝟙 𝟙 ω → refl
    𝟙 𝟘 𝟙 ω 𝟘 → refl
    𝟙 𝟘 𝟙 ω 𝟙 → refl
    𝟙 𝟘 𝟙 ω ω → refl
    𝟙 𝟘 ω 𝟘 𝟘 → refl
    𝟙 𝟘 ω 𝟘 𝟙 → refl
    𝟙 𝟘 ω 𝟘 ω → refl
    𝟙 𝟘 ω 𝟙 𝟘 → refl
    𝟙 𝟘 ω 𝟙 𝟙 → refl
    𝟙 𝟘 ω 𝟙 ω → refl
    𝟙 𝟘 ω ω 𝟘 → refl
    𝟙 𝟘 ω ω 𝟙 → refl
    𝟙 𝟘 ω ω ω → refl
    𝟙 𝟙 𝟘 𝟘 𝟘 → refl
    𝟙 𝟙 𝟘 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 𝟘 ω → refl
    𝟙 𝟙 𝟘 𝟙 𝟘 → refl
    𝟙 𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟙 𝟘 𝟙 ω → refl
    𝟙 𝟙 𝟘 ω 𝟘 → refl
    𝟙 𝟙 𝟘 ω 𝟙 → refl
    𝟙 𝟙 𝟘 ω ω → refl
    𝟙 𝟙 𝟙 𝟘 𝟘 → refl
    𝟙 𝟙 𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 𝟙 𝟙 ω → refl
    𝟙 𝟙 𝟙 ω 𝟘 → refl
    𝟙 𝟙 𝟙 ω 𝟙 → refl
    𝟙 𝟙 𝟙 ω ω → refl
    𝟙 𝟙 ω 𝟘 𝟘 → refl
    𝟙 𝟙 ω 𝟘 𝟙 → refl
    𝟙 𝟙 ω 𝟘 ω → refl
    𝟙 𝟙 ω 𝟙 𝟘 → refl
    𝟙 𝟙 ω 𝟙 𝟙 → refl
    𝟙 𝟙 ω 𝟙 ω → refl
    𝟙 𝟙 ω ω 𝟘 → refl
    𝟙 𝟙 ω ω 𝟙 → refl
    𝟙 𝟙 ω ω ω → refl
    𝟙 ω 𝟘 𝟘 𝟘 → refl
    𝟙 ω 𝟘 𝟘 𝟙 → refl
    𝟙 ω 𝟘 𝟘 ω → refl
    𝟙 ω 𝟘 𝟙 𝟘 → refl
    𝟙 ω 𝟘 𝟙 𝟙 → refl
    𝟙 ω 𝟘 𝟙 ω → refl
    𝟙 ω 𝟘 ω 𝟘 → refl
    𝟙 ω 𝟘 ω 𝟙 → refl
    𝟙 ω 𝟘 ω ω → refl
    𝟙 ω 𝟙 𝟘 𝟘 → refl
    𝟙 ω 𝟙 𝟘 𝟙 → refl
    𝟙 ω 𝟙 𝟘 ω → refl
    𝟙 ω 𝟙 𝟙 𝟘 → refl
    𝟙 ω 𝟙 𝟙 𝟙 → refl
    𝟙 ω 𝟙 𝟙 ω → refl
    𝟙 ω 𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 ω 𝟙 → refl
    𝟙 ω 𝟙 ω ω → refl
    𝟙 ω ω 𝟘 𝟘 → refl
    𝟙 ω ω 𝟘 𝟙 → refl
    𝟙 ω ω 𝟘 ω → refl
    𝟙 ω ω 𝟙 𝟘 → refl
    𝟙 ω ω 𝟙 𝟙 → refl
    𝟙 ω ω 𝟙 ω → refl
    𝟙 ω ω ω 𝟘 → refl
    𝟙 ω ω ω 𝟙 → refl
    𝟙 ω ω ω ω → refl
    ω 𝟘 𝟘 𝟘 𝟘 → refl
    ω 𝟘 𝟘 𝟘 𝟙 → refl
    ω 𝟘 𝟘 𝟘 ω → refl
    ω 𝟘 𝟘 𝟙 𝟘 → refl
    ω 𝟘 𝟘 𝟙 𝟙 → refl
    ω 𝟘 𝟘 𝟙 ω → refl
    ω 𝟘 𝟘 ω 𝟘 → refl
    ω 𝟘 𝟘 ω 𝟙 → refl
    ω 𝟘 𝟘 ω ω → refl
    ω 𝟘 𝟙 𝟘 𝟘 → refl
    ω 𝟘 𝟙 𝟘 𝟙 → refl
    ω 𝟘 𝟙 𝟘 ω → refl
    ω 𝟘 𝟙 𝟙 𝟘 → refl
    ω 𝟘 𝟙 𝟙 𝟙 → refl
    ω 𝟘 𝟙 𝟙 ω → refl
    ω 𝟘 𝟙 ω 𝟘 → refl
    ω 𝟘 𝟙 ω 𝟙 → refl
    ω 𝟘 𝟙 ω ω → refl
    ω 𝟘 ω 𝟘 𝟘 → refl
    ω 𝟘 ω 𝟘 𝟙 → refl
    ω 𝟘 ω 𝟘 ω → refl
    ω 𝟘 ω 𝟙 𝟘 → refl
    ω 𝟘 ω 𝟙 𝟙 → refl
    ω 𝟘 ω 𝟙 ω → refl
    ω 𝟘 ω ω 𝟘 → refl
    ω 𝟘 ω ω 𝟙 → refl
    ω 𝟘 ω ω ω → refl
    ω 𝟙 𝟘 𝟘 𝟘 → refl
    ω 𝟙 𝟘 𝟘 𝟙 → refl
    ω 𝟙 𝟘 𝟘 ω → refl
    ω 𝟙 𝟘 𝟙 𝟘 → refl
    ω 𝟙 𝟘 𝟙 𝟙 → refl
    ω 𝟙 𝟘 𝟙 ω → refl
    ω 𝟙 𝟘 ω 𝟘 → refl
    ω 𝟙 𝟘 ω 𝟙 → refl
    ω 𝟙 𝟘 ω ω → refl
    ω 𝟙 𝟙 𝟘 𝟘 → refl
    ω 𝟙 𝟙 𝟘 𝟙 → refl
    ω 𝟙 𝟙 𝟘 ω → refl
    ω 𝟙 𝟙 𝟙 𝟘 → refl
    ω 𝟙 𝟙 𝟙 𝟙 → refl
    ω 𝟙 𝟙 𝟙 ω → refl
    ω 𝟙 𝟙 ω 𝟘 → refl
    ω 𝟙 𝟙 ω 𝟙 → refl
    ω 𝟙 𝟙 ω ω → refl
    ω 𝟙 ω 𝟘 𝟘 → refl
    ω 𝟙 ω 𝟘 𝟙 → refl
    ω 𝟙 ω 𝟘 ω → refl
    ω 𝟙 ω 𝟙 𝟘 → refl
    ω 𝟙 ω 𝟙 𝟙 → refl
    ω 𝟙 ω 𝟙 ω → refl
    ω 𝟙 ω ω 𝟘 → refl
    ω 𝟙 ω ω 𝟙 → refl
    ω 𝟙 ω ω ω → refl
    ω ω 𝟘 𝟘 𝟘 → refl
    ω ω 𝟘 𝟘 𝟙 → refl
    ω ω 𝟘 𝟘 ω → refl
    ω ω 𝟘 𝟙 𝟘 → refl
    ω ω 𝟘 𝟙 𝟙 → refl
    ω ω 𝟘 𝟙 ω → refl
    ω ω 𝟘 ω 𝟘 → refl
    ω ω 𝟘 ω 𝟙 → refl
    ω ω 𝟘 ω ω → refl
    ω ω 𝟙 𝟘 𝟘 → refl
    ω ω 𝟙 𝟘 𝟙 → refl
    ω ω 𝟙 𝟘 ω → refl
    ω ω 𝟙 𝟙 𝟘 → refl
    ω ω 𝟙 𝟙 𝟙 → refl
    ω ω 𝟙 𝟙 ω → refl
    ω ω 𝟙 ω 𝟘 → refl
    ω ω 𝟙 ω 𝟙 → refl
    ω ω 𝟙 ω ω → refl
    ω ω ω 𝟘 𝟘 → refl
    ω ω ω 𝟘 𝟙 → refl
    ω ω ω 𝟘 ω → refl
    ω ω ω 𝟙 𝟘 → refl
    ω ω ω 𝟙 𝟙 → refl
    ω ω ω 𝟙 ω → refl
    ω ω ω ω 𝟘 → refl
    ω ω ω ω 𝟙 → refl
    ω ω ω ω ω → refl

-- The function affine→linearity is not an order embedding from an
-- affine types modality to a linear types modality.

¬affine⇨linearity :
  ¬ Is-order-embedding (affineModality v₁) (linearityModality v₂)
      affine→linearity
¬affine⇨linearity m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ω} refl of λ ()

-- The function linearity→affine is a morphism from a linear types
-- modality to an affine types modality if certain assumptions hold.

linearity⇨affine :
  𝟘ᵐ-allowed v₁ ≡ 𝟘ᵐ-allowed v₂ →
  let 𝕄₁ = linearityModality v₁
      𝕄₂ = affineModality v₂
  in
  Dedicated-nr 𝕄₁ ⇔ Dedicated-nr 𝕄₂ →
  Is-morphism 𝕄₁ 𝕄₂ linearity→affine
linearity⇨affine {v₁ = v₁} {v₂ = v₂} refl s⇔s = λ where
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.tr-≡-𝟘-⇔ _                → tr-≡-𝟘 _
                                           , λ { refl → refl }
    .Is-morphism.tr-<-𝟘 not-ok ok          → ⊥-elim (not-ok ok)
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-+ {p = p}              → ≤-reflexive (tr-+ p _)
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧ {p = p}              → tr-∧ p _
    .Is-morphism.tr-nr {r = r}             → tr-nr _ r _ _ _
    .Is-morphism.nr-in-first-iff-in-second → s⇔s
    .Is-morphism.𝟘ᵐ-in-second-if-in-first  → idᶠ
    .Is-morphism.𝟘ᵐ-in-first-if-in-second  → λ where
      (inj₁ ok) → inj₁ ok
    .Is-morphism.𝟘-well-behaved-in-first-if-in-second _ →
      inj₁ (L.linearity-has-well-behaved-zero v₁)
  where
  open Graded.Modality.Properties (affineModality v₂)

  tr′ = linearity→affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl

  tr-+ : ∀ p q → tr′ (p L.+ q) ≡ tr′ p A.+ tr′ q
  tr-+ 𝟘 𝟘 = refl
  tr-+ 𝟘 𝟙 = refl
  tr-+ 𝟘 ω = refl
  tr-+ 𝟙 𝟘 = refl
  tr-+ 𝟙 𝟙 = refl
  tr-+ 𝟙 ω = refl
  tr-+ ω 𝟘 = refl
  tr-+ ω 𝟙 = refl
  tr-+ ω ω = refl

  tr-· : ∀ p q → tr′ (p L.· q) ≡ tr′ p A.· tr′ q
  tr-· 𝟘 𝟘 = refl
  tr-· 𝟘 𝟙 = refl
  tr-· 𝟘 ω = refl
  tr-· 𝟙 𝟘 = refl
  tr-· 𝟙 𝟙 = refl
  tr-· 𝟙 ω = refl
  tr-· ω 𝟘 = refl
  tr-· ω 𝟙 = refl
  tr-· ω ω = refl

  tr-∧ : ∀ p q → tr′ (p L.∧ q) A.≤ tr′ p A.∧ tr′ q
  tr-∧ 𝟘 𝟘 = refl
  tr-∧ 𝟘 𝟙 = ≤-refl
  tr-∧ 𝟘 ω = refl
  tr-∧ 𝟙 𝟘 = ≤-refl
  tr-∧ 𝟙 𝟙 = refl
  tr-∧ 𝟙 ω = refl
  tr-∧ ω 𝟘 = refl
  tr-∧ ω 𝟙 = refl
  tr-∧ ω ω = refl

  tr-nr :
    ∀ p r z s n →
    tr′ (L.nr p r z s n) A.≤
    A.nr (tr′ p) (tr′ r) (tr′ z) (tr′ s) (tr′ n)
  tr-nr = λ where
    𝟘 𝟘 𝟘 𝟘 𝟘 → refl
    𝟘 𝟘 𝟘 𝟘 𝟙 → refl
    𝟘 𝟘 𝟘 𝟘 ω → refl
    𝟘 𝟘 𝟘 𝟙 𝟘 → refl
    𝟘 𝟘 𝟘 𝟙 𝟙 → refl
    𝟘 𝟘 𝟘 𝟙 ω → refl
    𝟘 𝟘 𝟘 ω 𝟘 → refl
    𝟘 𝟘 𝟘 ω 𝟙 → refl
    𝟘 𝟘 𝟘 ω ω → refl
    𝟘 𝟘 𝟙 𝟘 𝟘 → refl
    𝟘 𝟘 𝟙 𝟘 𝟙 → refl
    𝟘 𝟘 𝟙 𝟘 ω → refl
    𝟘 𝟘 𝟙 𝟙 𝟘 → refl
    𝟘 𝟘 𝟙 𝟙 𝟙 → refl
    𝟘 𝟘 𝟙 𝟙 ω → refl
    𝟘 𝟘 𝟙 ω 𝟘 → refl
    𝟘 𝟘 𝟙 ω 𝟙 → refl
    𝟘 𝟘 𝟙 ω ω → refl
    𝟘 𝟘 ω 𝟘 𝟘 → refl
    𝟘 𝟘 ω 𝟘 𝟙 → refl
    𝟘 𝟘 ω 𝟘 ω → refl
    𝟘 𝟘 ω 𝟙 𝟘 → refl
    𝟘 𝟘 ω 𝟙 𝟙 → refl
    𝟘 𝟘 ω 𝟙 ω → refl
    𝟘 𝟘 ω ω 𝟘 → refl
    𝟘 𝟘 ω ω 𝟙 → refl
    𝟘 𝟘 ω ω ω → refl
    𝟘 𝟙 𝟘 𝟘 𝟘 → refl
    𝟘 𝟙 𝟘 𝟘 𝟙 → refl
    𝟘 𝟙 𝟘 𝟘 ω → refl
    𝟘 𝟙 𝟘 𝟙 𝟘 → refl
    𝟘 𝟙 𝟘 𝟙 𝟙 → refl
    𝟘 𝟙 𝟘 𝟙 ω → refl
    𝟘 𝟙 𝟘 ω 𝟘 → refl
    𝟘 𝟙 𝟘 ω 𝟙 → refl
    𝟘 𝟙 𝟘 ω ω → refl
    𝟘 𝟙 𝟙 𝟘 𝟘 → refl
    𝟘 𝟙 𝟙 𝟘 𝟙 → refl
    𝟘 𝟙 𝟙 𝟘 ω → refl
    𝟘 𝟙 𝟙 𝟙 𝟘 → refl
    𝟘 𝟙 𝟙 𝟙 𝟙 → refl
    𝟘 𝟙 𝟙 𝟙 ω → refl
    𝟘 𝟙 𝟙 ω 𝟘 → refl
    𝟘 𝟙 𝟙 ω 𝟙 → refl
    𝟘 𝟙 𝟙 ω ω → refl
    𝟘 𝟙 ω 𝟘 𝟘 → refl
    𝟘 𝟙 ω 𝟘 𝟙 → refl
    𝟘 𝟙 ω 𝟘 ω → refl
    𝟘 𝟙 ω 𝟙 𝟘 → refl
    𝟘 𝟙 ω 𝟙 𝟙 → refl
    𝟘 𝟙 ω 𝟙 ω → refl
    𝟘 𝟙 ω ω 𝟘 → refl
    𝟘 𝟙 ω ω 𝟙 → refl
    𝟘 𝟙 ω ω ω → refl
    𝟘 ω 𝟘 𝟘 𝟘 → refl
    𝟘 ω 𝟘 𝟘 𝟙 → refl
    𝟘 ω 𝟘 𝟘 ω → refl
    𝟘 ω 𝟘 𝟙 𝟘 → refl
    𝟘 ω 𝟘 𝟙 𝟙 → refl
    𝟘 ω 𝟘 𝟙 ω → refl
    𝟘 ω 𝟘 ω 𝟘 → refl
    𝟘 ω 𝟘 ω 𝟙 → refl
    𝟘 ω 𝟘 ω ω → refl
    𝟘 ω 𝟙 𝟘 𝟘 → refl
    𝟘 ω 𝟙 𝟘 𝟙 → refl
    𝟘 ω 𝟙 𝟘 ω → refl
    𝟘 ω 𝟙 𝟙 𝟘 → refl
    𝟘 ω 𝟙 𝟙 𝟙 → refl
    𝟘 ω 𝟙 𝟙 ω → refl
    𝟘 ω 𝟙 ω 𝟘 → refl
    𝟘 ω 𝟙 ω 𝟙 → refl
    𝟘 ω 𝟙 ω ω → refl
    𝟘 ω ω 𝟘 𝟘 → refl
    𝟘 ω ω 𝟘 𝟙 → refl
    𝟘 ω ω 𝟘 ω → refl
    𝟘 ω ω 𝟙 𝟘 → refl
    𝟘 ω ω 𝟙 𝟙 → refl
    𝟘 ω ω 𝟙 ω → refl
    𝟘 ω ω ω 𝟘 → refl
    𝟘 ω ω ω 𝟙 → refl
    𝟘 ω ω ω ω → refl
    𝟙 𝟘 𝟘 𝟘 𝟘 → refl
    𝟙 𝟘 𝟘 𝟘 𝟙 → refl
    𝟙 𝟘 𝟘 𝟘 ω → refl
    𝟙 𝟘 𝟘 𝟙 𝟘 → refl
    𝟙 𝟘 𝟘 𝟙 𝟙 → refl
    𝟙 𝟘 𝟘 𝟙 ω → refl
    𝟙 𝟘 𝟘 ω 𝟘 → refl
    𝟙 𝟘 𝟘 ω 𝟙 → refl
    𝟙 𝟘 𝟘 ω ω → refl
    𝟙 𝟘 𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 𝟘 𝟙 → refl
    𝟙 𝟘 𝟙 𝟘 ω → refl
    𝟙 𝟘 𝟙 𝟙 𝟘 → refl
    𝟙 𝟘 𝟙 𝟙 𝟙 → refl
    𝟙 𝟘 𝟙 𝟙 ω → refl
    𝟙 𝟘 𝟙 ω 𝟘 → refl
    𝟙 𝟘 𝟙 ω 𝟙 → refl
    𝟙 𝟘 𝟙 ω ω → refl
    𝟙 𝟘 ω 𝟘 𝟘 → refl
    𝟙 𝟘 ω 𝟘 𝟙 → refl
    𝟙 𝟘 ω 𝟘 ω → refl
    𝟙 𝟘 ω 𝟙 𝟘 → refl
    𝟙 𝟘 ω 𝟙 𝟙 → refl
    𝟙 𝟘 ω 𝟙 ω → refl
    𝟙 𝟘 ω ω 𝟘 → refl
    𝟙 𝟘 ω ω 𝟙 → refl
    𝟙 𝟘 ω ω ω → refl
    𝟙 𝟙 𝟘 𝟘 𝟘 → refl
    𝟙 𝟙 𝟘 𝟘 𝟙 → refl
    𝟙 𝟙 𝟘 𝟘 ω → refl
    𝟙 𝟙 𝟘 𝟙 𝟘 → refl
    𝟙 𝟙 𝟘 𝟙 𝟙 → refl
    𝟙 𝟙 𝟘 𝟙 ω → refl
    𝟙 𝟙 𝟘 ω 𝟘 → refl
    𝟙 𝟙 𝟘 ω 𝟙 → refl
    𝟙 𝟙 𝟘 ω ω → refl
    𝟙 𝟙 𝟙 𝟘 𝟘 → refl
    𝟙 𝟙 𝟙 𝟘 𝟙 → refl
    𝟙 𝟙 𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 𝟙 𝟙 ω → refl
    𝟙 𝟙 𝟙 ω 𝟘 → refl
    𝟙 𝟙 𝟙 ω 𝟙 → refl
    𝟙 𝟙 𝟙 ω ω → refl
    𝟙 𝟙 ω 𝟘 𝟘 → refl
    𝟙 𝟙 ω 𝟘 𝟙 → refl
    𝟙 𝟙 ω 𝟘 ω → refl
    𝟙 𝟙 ω 𝟙 𝟘 → refl
    𝟙 𝟙 ω 𝟙 𝟙 → refl
    𝟙 𝟙 ω 𝟙 ω → refl
    𝟙 𝟙 ω ω 𝟘 → refl
    𝟙 𝟙 ω ω 𝟙 → refl
    𝟙 𝟙 ω ω ω → refl
    𝟙 ω 𝟘 𝟘 𝟘 → refl
    𝟙 ω 𝟘 𝟘 𝟙 → refl
    𝟙 ω 𝟘 𝟘 ω → refl
    𝟙 ω 𝟘 𝟙 𝟘 → refl
    𝟙 ω 𝟘 𝟙 𝟙 → refl
    𝟙 ω 𝟘 𝟙 ω → refl
    𝟙 ω 𝟘 ω 𝟘 → refl
    𝟙 ω 𝟘 ω 𝟙 → refl
    𝟙 ω 𝟘 ω ω → refl
    𝟙 ω 𝟙 𝟘 𝟘 → refl
    𝟙 ω 𝟙 𝟘 𝟙 → refl
    𝟙 ω 𝟙 𝟘 ω → refl
    𝟙 ω 𝟙 𝟙 𝟘 → refl
    𝟙 ω 𝟙 𝟙 𝟙 → refl
    𝟙 ω 𝟙 𝟙 ω → refl
    𝟙 ω 𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 ω 𝟙 → refl
    𝟙 ω 𝟙 ω ω → refl
    𝟙 ω ω 𝟘 𝟘 → refl
    𝟙 ω ω 𝟘 𝟙 → refl
    𝟙 ω ω 𝟘 ω → refl
    𝟙 ω ω 𝟙 𝟘 → refl
    𝟙 ω ω 𝟙 𝟙 → refl
    𝟙 ω ω 𝟙 ω → refl
    𝟙 ω ω ω 𝟘 → refl
    𝟙 ω ω ω 𝟙 → refl
    𝟙 ω ω ω ω → refl
    ω 𝟘 𝟘 𝟘 𝟘 → refl
    ω 𝟘 𝟘 𝟘 𝟙 → refl
    ω 𝟘 𝟘 𝟘 ω → refl
    ω 𝟘 𝟘 𝟙 𝟘 → refl
    ω 𝟘 𝟘 𝟙 𝟙 → refl
    ω 𝟘 𝟘 𝟙 ω → refl
    ω 𝟘 𝟘 ω 𝟘 → refl
    ω 𝟘 𝟘 ω 𝟙 → refl
    ω 𝟘 𝟘 ω ω → refl
    ω 𝟘 𝟙 𝟘 𝟘 → refl
    ω 𝟘 𝟙 𝟘 𝟙 → refl
    ω 𝟘 𝟙 𝟘 ω → refl
    ω 𝟘 𝟙 𝟙 𝟘 → refl
    ω 𝟘 𝟙 𝟙 𝟙 → refl
    ω 𝟘 𝟙 𝟙 ω → refl
    ω 𝟘 𝟙 ω 𝟘 → refl
    ω 𝟘 𝟙 ω 𝟙 → refl
    ω 𝟘 𝟙 ω ω → refl
    ω 𝟘 ω 𝟘 𝟘 → refl
    ω 𝟘 ω 𝟘 𝟙 → refl
    ω 𝟘 ω 𝟘 ω → refl
    ω 𝟘 ω 𝟙 𝟘 → refl
    ω 𝟘 ω 𝟙 𝟙 → refl
    ω 𝟘 ω 𝟙 ω → refl
    ω 𝟘 ω ω 𝟘 → refl
    ω 𝟘 ω ω 𝟙 → refl
    ω 𝟘 ω ω ω → refl
    ω 𝟙 𝟘 𝟘 𝟘 → refl
    ω 𝟙 𝟘 𝟘 𝟙 → refl
    ω 𝟙 𝟘 𝟘 ω → refl
    ω 𝟙 𝟘 𝟙 𝟘 → refl
    ω 𝟙 𝟘 𝟙 𝟙 → refl
    ω 𝟙 𝟘 𝟙 ω → refl
    ω 𝟙 𝟘 ω 𝟘 → refl
    ω 𝟙 𝟘 ω 𝟙 → refl
    ω 𝟙 𝟘 ω ω → refl
    ω 𝟙 𝟙 𝟘 𝟘 → refl
    ω 𝟙 𝟙 𝟘 𝟙 → refl
    ω 𝟙 𝟙 𝟘 ω → refl
    ω 𝟙 𝟙 𝟙 𝟘 → refl
    ω 𝟙 𝟙 𝟙 𝟙 → refl
    ω 𝟙 𝟙 𝟙 ω → refl
    ω 𝟙 𝟙 ω 𝟘 → refl
    ω 𝟙 𝟙 ω 𝟙 → refl
    ω 𝟙 𝟙 ω ω → refl
    ω 𝟙 ω 𝟘 𝟘 → refl
    ω 𝟙 ω 𝟘 𝟙 → refl
    ω 𝟙 ω 𝟘 ω → refl
    ω 𝟙 ω 𝟙 𝟘 → refl
    ω 𝟙 ω 𝟙 𝟙 → refl
    ω 𝟙 ω 𝟙 ω → refl
    ω 𝟙 ω ω 𝟘 → refl
    ω 𝟙 ω ω 𝟙 → refl
    ω 𝟙 ω ω ω → refl
    ω ω 𝟘 𝟘 𝟘 → refl
    ω ω 𝟘 𝟘 𝟙 → refl
    ω ω 𝟘 𝟘 ω → refl
    ω ω 𝟘 𝟙 𝟘 → refl
    ω ω 𝟘 𝟙 𝟙 → refl
    ω ω 𝟘 𝟙 ω → refl
    ω ω 𝟘 ω 𝟘 → refl
    ω ω 𝟘 ω 𝟙 → refl
    ω ω 𝟘 ω ω → refl
    ω ω 𝟙 𝟘 𝟘 → refl
    ω ω 𝟙 𝟘 𝟙 → refl
    ω ω 𝟙 𝟘 ω → refl
    ω ω 𝟙 𝟙 𝟘 → refl
    ω ω 𝟙 𝟙 𝟙 → refl
    ω ω 𝟙 𝟙 ω → refl
    ω ω 𝟙 ω 𝟘 → refl
    ω ω 𝟙 ω 𝟙 → refl
    ω ω 𝟙 ω ω → refl
    ω ω ω 𝟘 𝟘 → refl
    ω ω ω 𝟘 𝟙 → refl
    ω ω ω 𝟘 ω → refl
    ω ω ω 𝟙 𝟘 → refl
    ω ω ω 𝟙 𝟙 → refl
    ω ω ω 𝟙 ω → refl
    ω ω ω ω 𝟘 → refl
    ω ω ω ω 𝟙 → refl
    ω ω ω ω ω → refl

-- The function linearity→affine is not an order embedding from a
-- linear types modality to an affine types modality.

¬linearity⇨affine :
  ¬ Is-order-embedding (linearityModality v₁) (affineModality v₂)
      linearity→affine
¬linearity⇨affine m =
  case Is-order-embedding.tr-order-reflecting m {p = 𝟙} {q = 𝟘} refl of
    λ ()

------------------------------------------------------------------------
-- Σ-morphisms and order embeddings for Σ

-- The function erasure→zero-one-many-Σ is an order embedding for Σ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- a zero-one-many-modality modality, given that if the second
-- modality allows 𝟘ᵐ, then the first also does this. The
-- zero-one-many-modality modality can be defined with either 𝟙 ≤ 𝟘 or
-- 𝟙 ≰ 𝟘.

erasure⇨zero-one-many-Σ :
  (T (𝟘ᵐ-allowed v₂) → T (𝟘ᵐ-allowed v₁)) →
  Is-Σ-order-embedding
    (ErasureModality v₁)
    (zero-one-many-modality 𝟙≤𝟘 v₂)
    erasure→zero-one-many
    erasure→zero-one-many-Σ
erasure⇨zero-one-many-Σ {𝟙≤𝟘 = 𝟙≤𝟘} ok₂₁ = record
  { tr-Σ-morphism = record
    { tr-≤-tr-Σ = λ where
        {p = 𝟘} → refl
        {p = ω} → refl
    ; tr-Σ-≡-𝟘-→ = λ where
        {p = 𝟘} ok₂ _ → ok₂₁ ok₂ , refl
    ; tr-Σ-≤-𝟙 = λ where
        {p = ω} _ → refl
    ; tr-·-tr-Σ-≤ = λ where
        {p = 𝟘} {q = _} → refl
        {p = ω} {q = 𝟘} → refl
        {p = ω} {q = ω} → refl
    }
  ; tr-≤-tr-Σ-→ = λ where
      {p = 𝟘} {q = 𝟘}         _     → ω , refl , refl
      {p = 𝟘} {q = ω} {r = 𝟘} _     → 𝟘 , refl , refl
      {p = 𝟘} {q = ω} {r = 𝟙} 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
      {p = ω}                 _     → ω , refl , refl
  }
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘

-- The function erasure→zero-one-many-Σ is an order embedding for Σ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- a linear types modality, given that if the second modality allows
-- 𝟘ᵐ, then the first also does this.

erasure⇨linearity-Σ :
  (T (𝟘ᵐ-allowed v₂) → T (𝟘ᵐ-allowed v₁)) →
  Is-Σ-order-embedding (ErasureModality v₁) (linearityModality v₂)
    erasure→zero-one-many erasure→zero-one-many-Σ
erasure⇨linearity-Σ = erasure⇨zero-one-many-Σ

-- The function erasure→zero-one-many-Σ is not monotone with respect
-- to the erasure and linear types orderings.

erasure⇨linearity-Σ-not-monotone :
  ¬ (∀ {p q} →
     p E.≤ q →
     erasure→zero-one-many-Σ p L.≤ erasure→zero-one-many-Σ q)
erasure⇨linearity-Σ-not-monotone mono =
  case mono {p = ω} {q = 𝟘} refl of λ ()

-- The function erasure→zero-one-many-Σ is an order embedding for Σ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- an affine types modality, given that if the second modality allows
-- 𝟘ᵐ, then the first also does this.

erasure⇨affine-Σ :
  (T (𝟘ᵐ-allowed v₂) → T (𝟘ᵐ-allowed v₁)) →
  Is-Σ-order-embedding (ErasureModality v₁) (affineModality v₂)
    erasure→zero-one-many erasure→zero-one-many-Σ
erasure⇨affine-Σ = erasure⇨zero-one-many-Σ

-- The function affine→linear-or-affine-Σ is an order embedding for Σ
-- (with respect to affine→linear-or-affine) from an affine types
-- modality to a linear or affine types modality, given that if the
-- second modality allows 𝟘ᵐ, then the first also does this.

affine⇨linear-or-affine-Σ :
  (T (𝟘ᵐ-allowed v₂) → T (𝟘ᵐ-allowed v₁)) →
  Is-Σ-order-embedding (affineModality v₁) (linear-or-affine v₂)
    affine→linear-or-affine affine→linear-or-affine-Σ
affine⇨linear-or-affine-Σ ok₂₁ = record
  { tr-Σ-morphism = record
    { tr-≤-tr-Σ = λ where
        {p = 𝟘} → refl
        {p = 𝟙} → refl
        {p = ω} → refl
    ; tr-Σ-≡-𝟘-→ = λ where
        {p = 𝟘} ok₂ _ → ok₂₁ ok₂ , refl
    ; tr-Σ-≤-𝟙 = λ where
        {p = 𝟙} _ → refl
        {p = ω} _ → refl
    ; tr-·-tr-Σ-≤ = λ where
        {p = 𝟘} {q = _} → refl
        {p = 𝟙} {q = 𝟘} → refl
        {p = 𝟙} {q = 𝟙} → refl
        {p = 𝟙} {q = ω} → refl
        {p = ω} {q = 𝟘} → refl
        {p = ω} {q = 𝟙} → refl
        {p = ω} {q = ω} → refl
    }
  ; tr-≤-tr-Σ-→ = λ where
      {p = 𝟘} {q = 𝟘}          _ → ω , refl , refl
      {p = 𝟘} {q = 𝟙} {r = 𝟘}  _ → 𝟘 , refl , refl
      {p = 𝟘} {q = ω} {r = 𝟘}  _ → 𝟘 , refl , refl
      {p = 𝟙} {q = 𝟘}          _ → ω , refl , refl
      {p = 𝟙} {q = 𝟙} {r = 𝟘}  _ → 𝟙 , refl , refl
      {p = 𝟙} {q = 𝟙} {r = 𝟙}  _ → 𝟙 , refl , refl
      {p = 𝟙} {q = 𝟙} {r = ≤𝟙} _ → 𝟙 , refl , refl
      {p = 𝟙} {q = ω} {r = 𝟘}  _ → 𝟘 , refl , refl
      {p = ω}                  _ → ω , refl , refl
  }

-- The function affine→linear-or-affine-Σ is not monotone with respect
-- to the affine types and linear or affine types orderings.

affine→linear-or-affine-Σ-not-monotone :
  ¬ (∀ {p q} →
     p A.≤ q →
     affine→linear-or-affine-Σ p LA.≤ affine→linear-or-affine-Σ q)
affine→linear-or-affine-Σ-not-monotone mono =
  case mono {p = 𝟙} {q = 𝟘} refl of λ ()

-- There is a function tr-Σ that is a Σ-morphism and an order
-- embedding for Σ for two modalities (with respect to a function that
-- is an order embedding for those modalities), but neither a morphism
-- nor an order embedding for those modalities.

Σ-order-embedding-but-not-order-embedding :
  ∃₂ λ (M₁ M₂ : Set) →
  ∃₂ λ (𝕄₁ : Modality M₁) (𝕄₂ : Modality M₂) →
  ∃₂ λ (tr tr-Σ : M₁ → M₂) →
  Is-order-embedding 𝕄₁ 𝕄₂ tr ×
  Is-Σ-morphism 𝕄₁ 𝕄₂ tr tr-Σ ×
  Is-Σ-order-embedding 𝕄₁ 𝕄₂ tr tr-Σ ×
  ¬ Is-morphism 𝕄₁ 𝕄₂ tr-Σ ×
  ¬ Is-order-embedding 𝕄₁ 𝕄₂ tr-Σ
Σ-order-embedding-but-not-order-embedding =
    Affine , Linear-or-affine
  , affineModality variant
  , linear-or-affine variant
  , affine→linear-or-affine , affine→linear-or-affine-Σ
  , affine⇨linear-or-affine refl _
  , Is-Σ-order-embedding.tr-Σ-morphism (affine⇨linear-or-affine-Σ _)
  , affine⇨linear-or-affine-Σ _
  , affine→linear-or-affine-Σ-not-monotone ∘→ Is-morphism.tr-monotone
  , affine→linear-or-affine-Σ-not-monotone ∘→
    Is-order-embedding.tr-monotone
  where
  variant = nr-available-and-𝟘ᵐ-allowed-if _ true

-- The function affine→linearity-Σ is a Σ-morphism (with respect to
-- affine→linearity) from an affine types modality to a linear types
-- modality, given that if the second modality allows 𝟘ᵐ, then the
-- first also does this.

affine⇨linearity-Σ :
  (T (𝟘ᵐ-allowed v₂) → T (𝟘ᵐ-allowed v₁)) →
  Is-Σ-morphism (affineModality v₁) (linearityModality v₂)
    affine→linearity affine→linearity-Σ
affine⇨linearity-Σ ok₂₁ = record
  { tr-≤-tr-Σ = λ where
      {p = 𝟘} → refl
      {p = 𝟙} → refl
      {p = ω} → refl
  ; tr-Σ-≡-𝟘-→ = λ where
      {p = 𝟘} ok₂ _ → ok₂₁ ok₂ , refl
  ; tr-Σ-≤-𝟙 = λ where
      {p = 𝟙} _ → refl
      {p = ω} _ → refl
  ; tr-·-tr-Σ-≤ = λ where
      {p = 𝟘} {q = _} → refl
      {p = 𝟙} {q = 𝟘} → refl
      {p = 𝟙} {q = 𝟙} → refl
      {p = 𝟙} {q = ω} → refl
      {p = ω} {q = 𝟘} → refl
      {p = ω} {q = 𝟙} → refl
      {p = ω} {q = ω} → refl
  }

-- The function affine→linearity-Σ is not monotone with respect to the
-- affine types and linear types orderings.

affine→linearity-Σ-not-monotone :
  ¬ (∀ {p q} →
     p A.≤ q →
     affine→linearity-Σ p L.≤ affine→linearity-Σ q)
affine→linearity-Σ-not-monotone mono =
  case mono {p = 𝟙} {q = 𝟘} refl of λ ()

-- The function affine→linearity-Σ is not an order embedding for Σ
-- (with respect to affine→linearity) from an affine types modality to
-- a linear types modality.

¬affine⇨linearity-Σ :
  ¬ Is-Σ-order-embedding
      (affineModality v₁)
      (linearityModality v₂)
      affine→linearity affine→linearity-Σ
¬affine⇨linearity-Σ m =
  case
    Is-Σ-order-embedding.tr-≤-tr-Σ-→ m {p = 𝟙} {q = ω} {r = ω} refl
  of λ where
    (𝟘 , () , _)
    (𝟙 , _  , ())
    (ω , _  , ())
