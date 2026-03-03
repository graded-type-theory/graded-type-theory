------------------------------------------------------------------------
-- Some example morphisms and order embeddings
------------------------------------------------------------------------

-- It might make sense to replace some of the proofs below with a lot
-- of cases with automated proofs.

module Graded.Modality.Morphism.Examples where

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Nat using (1+)
open import Tools.Product
open import Tools.PropositionalEquality
import Tools.Reasoning.PartialOrder
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

open import Graded.Modality
open import Graded.Modality.Instances.Affine as A
  using (Affine; affineModality)
open import Graded.Modality.Instances.Erasure as E
  using (Erasure; 𝟘; ω)
open import Graded.Modality.Instances.Erasure.Modality as E
  using (ErasureModality)
import Graded.Modality.Instances.Erasure.Properties as EP
open import Graded.Modality.Instances.Linear-or-affine as LA
  using (Linear-or-affine; 𝟘; 𝟙; ≤𝟙; ≤ω; linear-or-affine)
open import Graded.Modality.Instances.Linearity as L
  using (Linearity; linearityModality)
open import Graded.Modality.Instances.Unit
  using (UnitModality; unit-has-nr)
open import Graded.Modality.Instances.Zero-one-many as ZOM
  using (Zero-one-many; 𝟘; 𝟙; ω; zero-one-many-modality)
open import Graded.Modality.Morphism
import Graded.Modality.Properties

private variable
  𝟙≤𝟘             : Bool
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
  let 𝕄₁ = UnitModality
      𝕄₂ = ErasureModality
  in
  Is-order-embedding 𝕄₁ 𝕄₂ unit→erasure
unit⇨erasure = λ where
    .tr-order-reflecting _ → refl
    .tr-≤                  → _ , refl
    .tr-≤-𝟙 _              → refl
    .tr-ω                  → refl
    .tr-≤-+ _              → _ , _ , refl , refl , refl
    .tr-≤-· _              → _ , refl , refl
    .tr-≤-∧ _              → _ , _ , refl , refl , refl
    .tr-morphism           → λ where
      .first-trivial-if-second-trivial
        ()
      .tr-𝟘-≤                               → refl
      .trivial-⊎-tr-≡-𝟘-⇔                   → inj₁ refl
      .tr-𝟙                                 → refl
      .tr-ω                                 → refl
      .tr-+                                 → refl
      .tr-·                                 → refl
      .tr-∧                                 → refl
  where
  open Is-morphism
  open Is-order-embedding

-- The function erasure→unit is not a morphism from an erasure
-- modality to a unit modality.

¬erasure⇨unit :
  ¬ Is-morphism ErasureModality UnitModality
      erasure→unit
¬erasure⇨unit m =
  case Is-morphism.first-trivial-if-second-trivial m refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a zero-one-many-modality modality if certain
-- assumptions hold. The zero-one-many-modality modality can be
-- defined with either 𝟙 ≤ 𝟘 or 𝟙 ≰ 𝟘.

erasure⇨zero-one-many :
  let 𝕄₁ = ErasureModality
      𝕄₂ = zero-one-many-modality 𝟙≤𝟘
  in
  Is-order-embedding 𝕄₁ 𝕄₂ erasure→zero-one-many
erasure⇨zero-one-many {𝟙≤𝟘} =
  λ where
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-ω                → refl
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-order-reflecting →
      tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism → λ where
      .Is-morphism.first-trivial-if-second-trivial
        ()
      .Is-morphism.tr-𝟘-≤                    → refl
      .Is-morphism.trivial-⊎-tr-≡-𝟘-⇔        → inj₂ ( tr-≡-𝟘 _
                                                    , λ { refl → refl }
                                                    )
      .Is-morphism.tr-𝟙                      → refl
      .Is-morphism.tr-ω                      → refl
      .Is-morphism.tr-+ {p = p}              → tr-+ p _
      .Is-morphism.tr-· {p = p}              → tr-· p _
      .Is-morphism.tr-∧ {p = p}              → ≤-reflexive (tr-∧ p _)
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘
  module P₁ = Graded.Modality.Properties ErasureModality
  open Graded.Modality.Properties (zero-one-many-modality 𝟙≤𝟘)
  open Tools.Reasoning.PartialOrder ≤-poset

  tr′  = erasure→zero-one-many

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl
  tr-≡-𝟘 ω ()

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

  tr-order-reflecting : ∀ p q → tr′ p 𝟘𝟙ω.≤ tr′ q → p E.≤ q
  tr-order-reflecting 𝟘 𝟘 _ = refl
  tr-order-reflecting ω 𝟘 _ = refl
  tr-order-reflecting ω ω _ = refl
  tr-order-reflecting 𝟘 ω ()

  tr-≤-+ :
    ∀ p q r →
    tr′ p 𝟘𝟙ω.≤ q 𝟘𝟙ω.+ r →
    ∃₂ λ q′ r′ → tr′ q′ 𝟘𝟙ω.≤ q × tr′ r′ 𝟘𝟙ω.≤ r × p E.≤ q′ E.+ r′
  tr-≤-+ 𝟘 𝟘 𝟘 _     = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟘 𝟘 𝟙 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-+ 𝟘 𝟙 𝟘 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-+ ω _ _ _     = ω , ω , refl , refl , refl
  tr-≤-+ 𝟘 𝟘 ω ()
  tr-≤-+ 𝟘 𝟙 𝟙 ()
  tr-≤-+ 𝟘 𝟙 ω ()
  tr-≤-+ 𝟘 ω 𝟘 ()
  tr-≤-+ 𝟘 ω 𝟙 ()
  tr-≤-+ 𝟘 ω ω ()

  tr-≤-· :
    ∀ p q r →
    tr′ p 𝟘𝟙ω.≤ tr′ q 𝟘𝟙ω.· r →
    ∃ λ r′ → tr′ r′ 𝟘𝟙ω.≤ r × p E.≤ q E.· r′
  tr-≤-· 𝟘 𝟘 _ _ = ω , refl , refl
  tr-≤-· 𝟘 ω 𝟘 _ = 𝟘 , refl , refl
  tr-≤-· ω _ _ _ = ω , refl , refl
  tr-≤-· 𝟘 ω 𝟙 ()
  tr-≤-· 𝟘 ω ω ()

  tr-≤-∧ :
    ∀ p q r →
    tr′ p 𝟘𝟙ω.≤ q 𝟘𝟙ω.∧ r →
    ∃₂ λ q′ r′ → tr′ q′ 𝟘𝟙ω.≤ q × tr′ r′ 𝟘𝟙ω.≤ r × p E.≤ q′ E.∧ r′
  tr-≤-∧ 𝟘 𝟘 𝟘 _     = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-∧ 𝟘 𝟘 𝟙 𝟘≤𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘≰𝟘∧𝟙 𝟘≤𝟘∧𝟙)
  tr-≤-∧ 𝟘 𝟙 𝟘 𝟘≤𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘≰𝟘∧𝟙 𝟘≤𝟘∧𝟙)
  tr-≤-∧ 𝟘 𝟙 𝟙 𝟘≡𝟘∧𝟙 = ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
  tr-≤-∧ ω _ _ _     = ω , ω , refl , refl , refl
  tr-≤-∧ 𝟘 𝟘 ω ()
  tr-≤-∧ 𝟘 𝟙 ω ()
  tr-≤-∧ 𝟘 ω 𝟘 ()
  tr-≤-∧ 𝟘 ω 𝟙 ()
  tr-≤-∧ 𝟘 ω ω ()

-- The function zero-one-many→erasure is a morphism from a
-- zero-one-many-modality modality to an erasure modality if certain
-- assumptions hold. The zero-one-many-modality modality can be
-- defined with either 𝟙 ≤ 𝟘 or 𝟙 ≰ 𝟘.

zero-one-many⇨erasure :
  let 𝕄₁ = zero-one-many-modality 𝟙≤𝟘
      𝕄₂ = ErasureModality
  in
  Is-morphism 𝕄₁ 𝕄₂ zero-one-many→erasure
zero-one-many⇨erasure {𝟙≤𝟘} = λ where
    .Is-morphism.first-trivial-if-second-trivial
      ()
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.trivial-⊎-tr-≡-𝟘-⇔        → inj₂ ( tr-≡-𝟘 _
                                                  , λ { refl → refl }
                                                  )
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-ω                      → refl
    .Is-morphism.tr-+ {p = p}              → tr-+ p _
    .Is-morphism.tr-· {p = p}              → tr-· p _
    .Is-morphism.tr-∧ {p = p}              → ≤-reflexive (tr-∧ p _)
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘
  open Graded.Modality.Properties ErasureModality

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
  tr-≡-𝟘 𝟙 ()
  tr-≡-𝟘 ω ()

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

-- The function zero-one-many→erasure is not an order embedding from a
-- zero-one-many-modality modality to an erasure modality.

¬zero-one-many⇨erasure :
  ¬ Is-order-embedding
      (zero-one-many-modality 𝟙≤𝟘)
      ErasureModality
      zero-one-many→erasure
¬zero-one-many⇨erasure m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ω} refl of λ ()

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to a linear types modality if certain assumptions
-- hold.

erasure⇨linearity :
  let 𝕄₁ = ErasureModality
      𝕄₂ = linearityModality
  in
  Is-order-embedding 𝕄₁ 𝕄₂ erasure→zero-one-many
erasure⇨linearity = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from a linear
-- types modality to an erasure modality if certain assumptions hold.

linearity⇨erasure :
  let 𝕄₁ = linearityModality
      𝕄₂ = ErasureModality
  in
  Is-morphism 𝕄₁ 𝕄₂ zero-one-many→erasure
linearity⇨erasure = zero-one-many⇨erasure

-- The function zero-one-many→erasure is not an order embedding from a
-- linear types modality to an erasure modality.

¬linearity⇨erasure :
  ¬ Is-order-embedding linearityModality ErasureModality
      zero-one-many→erasure
¬linearity⇨erasure = ¬zero-one-many⇨erasure

-- The function erasure→zero-one-many is an order embedding from an
-- erasure modality to an affine types modality if certain assumptions
-- hold.

erasure⇨affine :
  let 𝕄₁ = ErasureModality
      𝕄₂ = affineModality
  in
  Is-order-embedding 𝕄₁ 𝕄₂ erasure→zero-one-many
erasure⇨affine = erasure⇨zero-one-many

-- The function zero-one-many→erasure is a morphism from an affine
-- types modality to an erasure modality if certain assumptions hold.

affine⇨erasure :
  let 𝕄₁ = affineModality
      𝕄₂ = ErasureModality
  in
  Is-morphism 𝕄₁ 𝕄₂ zero-one-many→erasure
affine⇨erasure = zero-one-many⇨erasure

-- The function zero-one-many→erasure is not an order embedding from
-- an affine types modality to an erasure modality.

¬affine⇨erasure :
  ¬ Is-order-embedding affineModality ErasureModality
      zero-one-many→erasure
¬affine⇨erasure = ¬zero-one-many⇨erasure

-- The function linearity→linear-or-affine is an order embedding from
-- a linear types modality to a linear or affine types modality if
-- certain assumptions hold.

linearity⇨linear-or-affine :
  let 𝕄₁ = linearityModality
      𝕄₂ = linear-or-affine
  in
  Is-order-embedding 𝕄₁ 𝕄₂ linearity→linear-or-affine
linearity⇨linear-or-affine = λ where
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-ω                → refl
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-order-reflecting → tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism         → λ where
      .Is-morphism.first-trivial-if-second-trivial
        ()
      .Is-morphism.tr-𝟘-≤                    → refl
      .Is-morphism.trivial-⊎-tr-≡-𝟘-⇔        → inj₂ ( tr-≡-𝟘 _
                                                    , λ { refl → refl }
                                                    )
      .Is-morphism.tr-𝟙                      → refl
      .Is-morphism.tr-ω                      → refl
      .Is-morphism.tr-+ {p = p}              → tr-+ p _
      .Is-morphism.tr-·                      → tr-· _ _
      .Is-morphism.tr-∧                      → tr-∧ _ _
  where
  module P₁ = Graded.Modality.Properties linearityModality
  open Graded.Modality.Properties linear-or-affine

  tr′  = linearity→linear-or-affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl
  tr-≡-𝟘 𝟙 ()
  tr-≡-𝟘 ω ()

  tr-≤-𝟙 : ∀ p → tr′ p LA.≤ 𝟙 → p L.≤ 𝟙
  tr-≤-𝟙 𝟙 _ = refl
  tr-≤-𝟙 ω _ = refl
  tr-≤-𝟙 𝟘 ()

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


  tr-order-reflecting : ∀ p q → tr′ p LA.≤ tr′ q → p L.≤ q
  tr-order-reflecting 𝟘 𝟘 _ = refl
  tr-order-reflecting 𝟙 𝟙 _ = refl
  tr-order-reflecting ω 𝟘 _ = refl
  tr-order-reflecting ω 𝟙 _ = refl
  tr-order-reflecting ω ω _ = refl
  tr-order-reflecting 𝟘 𝟙 ()
  tr-order-reflecting 𝟘 ω ()
  tr-order-reflecting 𝟙 𝟘 ()
  tr-order-reflecting 𝟙 ω ()

  tr-≤-+ :
    ∀ p q r →
    tr′ p LA.≤ q LA.+ r →
    ∃₂ λ q′ r′ → tr′ q′ LA.≤ q × tr′ r′ LA.≤ r × p L.≤ q′ L.+ r′
  tr-≤-+ 𝟘 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-+ 𝟙 𝟘  𝟙  _  = 𝟘 , 𝟙 , refl , refl , refl
  tr-≤-+ 𝟙 𝟙  𝟘  _  = 𝟙 , 𝟘 , refl , refl , refl
  tr-≤-+ ω _  _  _  = ω , ω , refl , refl , refl
  tr-≤-+ 𝟘 𝟘  𝟙  ()
  tr-≤-+ 𝟘 𝟘  ≤𝟙 ()
  tr-≤-+ 𝟘 𝟘  ≤ω ()
  tr-≤-+ 𝟘 𝟙  𝟘  ()
  tr-≤-+ 𝟘 𝟙  𝟙  ()
  tr-≤-+ 𝟘 𝟙  ≤𝟙 ()
  tr-≤-+ 𝟘 𝟙  ≤ω ()
  tr-≤-+ 𝟘 ≤𝟙 𝟘  ()
  tr-≤-+ 𝟘 ≤𝟙 𝟙  ()
  tr-≤-+ 𝟘 ≤𝟙 ≤𝟙 ()
  tr-≤-+ 𝟘 ≤𝟙 ≤ω ()
  tr-≤-+ 𝟘 ≤ω 𝟘  ()
  tr-≤-+ 𝟘 ≤ω 𝟙  ()
  tr-≤-+ 𝟘 ≤ω ≤𝟙 ()
  tr-≤-+ 𝟘 ≤ω ≤ω ()
  tr-≤-+ 𝟙 𝟘  𝟘  ()
  tr-≤-+ 𝟙 𝟘  ≤𝟙 ()
  tr-≤-+ 𝟙 𝟘  ≤ω ()
  tr-≤-+ 𝟙 𝟙  𝟙  ()
  tr-≤-+ 𝟙 𝟙  ≤𝟙 ()
  tr-≤-+ 𝟙 𝟙  ≤ω ()
  tr-≤-+ 𝟙 ≤𝟙 𝟘  ()
  tr-≤-+ 𝟙 ≤𝟙 𝟙  ()
  tr-≤-+ 𝟙 ≤𝟙 ≤𝟙 ()
  tr-≤-+ 𝟙 ≤𝟙 ≤ω ()
  tr-≤-+ 𝟙 ≤ω 𝟘  ()
  tr-≤-+ 𝟙 ≤ω 𝟙  ()
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
  tr-≤-· 𝟘 𝟙 𝟙  ()
  tr-≤-· 𝟘 𝟙 ≤𝟙 ()
  tr-≤-· 𝟘 𝟙 ≤ω ()
  tr-≤-· 𝟘 ω 𝟙  ()
  tr-≤-· 𝟘 ω ≤𝟙 ()
  tr-≤-· 𝟘 ω ≤ω ()
  tr-≤-· 𝟙 𝟘 𝟘  ()
  tr-≤-· 𝟙 𝟘 𝟙  ()
  tr-≤-· 𝟙 𝟘 ≤𝟙 ()
  tr-≤-· 𝟙 𝟘 ≤ω ()
  tr-≤-· 𝟙 𝟙 𝟘  ()
  tr-≤-· 𝟙 𝟙 ≤𝟙 ()
  tr-≤-· 𝟙 𝟙 ≤ω ()
  tr-≤-· 𝟙 ω 𝟘  ()
  tr-≤-· 𝟙 ω 𝟙  ()
  tr-≤-· 𝟙 ω ≤𝟙 ()
  tr-≤-· 𝟙 ω ≤ω ()

  tr-≤-∧ :
    ∀ p q r →
    tr′ p LA.≤ q LA.∧ r →
    ∃₂ λ q′ r′ → tr′ q′ LA.≤ q × tr′ r′ LA.≤ r × p L.≤ q′ L.∧ r′
  tr-≤-∧ 𝟘 𝟘  𝟘  _  = 𝟘 , 𝟘 , refl , refl , refl
  tr-≤-∧ 𝟙 𝟙  𝟙  _  = 𝟙 , 𝟙 , refl , refl , refl
  tr-≤-∧ ω _  _  _  = ω , ω , refl , refl , refl
  tr-≤-∧ 𝟘 𝟘  𝟙  ()
  tr-≤-∧ 𝟘 𝟘  ≤𝟙 ()
  tr-≤-∧ 𝟘 𝟘  ≤ω ()
  tr-≤-∧ 𝟘 𝟙  𝟘  ()
  tr-≤-∧ 𝟘 𝟙  𝟙  ()
  tr-≤-∧ 𝟘 𝟙  ≤𝟙 ()
  tr-≤-∧ 𝟘 𝟙  ≤ω ()
  tr-≤-∧ 𝟘 ≤𝟙 𝟘  ()
  tr-≤-∧ 𝟘 ≤𝟙 𝟙  ()
  tr-≤-∧ 𝟘 ≤𝟙 ≤𝟙 ()
  tr-≤-∧ 𝟘 ≤𝟙 ≤ω ()
  tr-≤-∧ 𝟘 ≤ω 𝟘  ()
  tr-≤-∧ 𝟘 ≤ω 𝟙  ()
  tr-≤-∧ 𝟘 ≤ω ≤𝟙 ()
  tr-≤-∧ 𝟘 ≤ω ≤ω ()
  tr-≤-∧ 𝟙 𝟘  𝟘  ()
  tr-≤-∧ 𝟙 𝟘  𝟙  ()
  tr-≤-∧ 𝟙 𝟘  ≤𝟙 ()
  tr-≤-∧ 𝟙 𝟘  ≤ω ()
  tr-≤-∧ 𝟙 𝟙  𝟘  ()
  tr-≤-∧ 𝟙 𝟙  ≤𝟙 ()
  tr-≤-∧ 𝟙 𝟙  ≤ω ()
  tr-≤-∧ 𝟙 ≤𝟙 𝟘  ()
  tr-≤-∧ 𝟙 ≤𝟙 𝟙  ()
  tr-≤-∧ 𝟙 ≤𝟙 ≤𝟙 ()
  tr-≤-∧ 𝟙 ≤𝟙 ≤ω ()
  tr-≤-∧ 𝟙 ≤ω 𝟘  ()
  tr-≤-∧ 𝟙 ≤ω 𝟙  ()
  tr-≤-∧ 𝟙 ≤ω ≤𝟙 ()
  tr-≤-∧ 𝟙 ≤ω ≤ω ()

-- The function linear-or-affine→linearity is a morphism from a linear
-- or affine types modality to a linear types modality if certain
-- assumptions hold.

linear-or-affine⇨linearity :
  let 𝕄₁ = linear-or-affine
      𝕄₂ = linearityModality
  in
  Is-morphism 𝕄₁ 𝕄₂ linear-or-affine→linearity
linear-or-affine⇨linearity = λ where
    .Is-morphism.first-trivial-if-second-trivial
      ()
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.trivial-⊎-tr-≡-𝟘-⇔        → inj₂ ( tr-≡-𝟘 _
                                                  , λ { refl → refl }
                                                  )
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-ω                      → refl
    .Is-morphism.tr-+ {p = p}              → tr-+ p _
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧                      → ≤-reflexive (tr-∧ _ _)
  where
  open Graded.Modality.Properties linearityModality

  tr′ = linear-or-affine→linearity

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl
  tr-≡-𝟘 𝟙  ()
  tr-≡-𝟘 ≤𝟙 ()
  tr-≡-𝟘 ≤ω ()

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


-- The function linear-or-affine→linearity is not an order embedding
-- from a linear or affine types modality to a linear types modality.

¬linear-or-affine⇨linearity :
  ¬ Is-order-embedding linear-or-affine linearityModality
      linear-or-affine→linearity
¬linear-or-affine⇨linearity m =
  case Is-order-embedding.tr-injective m {p = ≤𝟙} {q = ≤ω} refl of λ ()

-- The function affine→linear-or-affine is an order embedding from an
-- affine types modality to a linear or affine types modality if
-- certain assumptions hold.

affine⇨linear-or-affine :
  let 𝕄₁ = affineModality
      𝕄₂ = linear-or-affine
  in
  Is-order-embedding 𝕄₁ 𝕄₂ affine→linear-or-affine
affine⇨linear-or-affine = λ where
    .Is-order-embedding.tr-≤                → ω , refl
    .Is-order-embedding.tr-≤-𝟙              → tr-≤-𝟙 _
    .Is-order-embedding.tr-ω                → refl
    .Is-order-embedding.tr-≤-+              → tr-≤-+ _ _ _
    .Is-order-embedding.tr-≤-·              → tr-≤-· _ _ _
    .Is-order-embedding.tr-≤-∧              → tr-≤-∧ _ _ _
    .Is-order-embedding.tr-order-reflecting → tr-order-reflecting _ _
    .Is-order-embedding.tr-morphism         → λ where
      .Is-morphism.first-trivial-if-second-trivial
        ()
      .Is-morphism.tr-𝟘-≤                    → refl
      .Is-morphism.trivial-⊎-tr-≡-𝟘-⇔        → inj₂ ( tr-≡-𝟘 _
                                                    , λ { refl → refl }
                                                    )
      .Is-morphism.tr-𝟙                      → refl
      .Is-morphism.tr-ω                      → refl
      .Is-morphism.tr-+ {p = p}              → tr-+ p _
      .Is-morphism.tr-·                      → tr-· _ _
      .Is-morphism.tr-∧                      → ≤-reflexive (tr-∧ _ _)
  where
  module P₁ = Graded.Modality.Properties affineModality
  open Graded.Modality.Properties linear-or-affine

  tr′  = affine→linear-or-affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl
  tr-≡-𝟘 𝟙 ()
  tr-≡-𝟘 ω ()

  tr-≤-𝟙 : ∀ p → tr′ p LA.≤ 𝟙 → p A.≤ 𝟙
  tr-≤-𝟙 𝟙 _ = refl
  tr-≤-𝟙 ω _ = refl
  tr-≤-𝟙 𝟘 ()

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

  tr-order-reflecting : ∀ p q → tr′ p LA.≤ tr′ q → p A.≤ q
  tr-order-reflecting 𝟘 𝟘 _ = refl
  tr-order-reflecting 𝟙 𝟘 _ = refl
  tr-order-reflecting 𝟙 𝟙 _ = refl
  tr-order-reflecting ω 𝟘 _ = refl
  tr-order-reflecting ω 𝟙 _ = refl
  tr-order-reflecting ω ω _ = refl
  tr-order-reflecting 𝟘 𝟙 ()
  tr-order-reflecting 𝟘 ω ()
  tr-order-reflecting 𝟙 ω ()


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
  tr-≤-+ 𝟘 𝟘  𝟙  ()
  tr-≤-+ 𝟘 𝟘  ≤𝟙 ()
  tr-≤-+ 𝟘 𝟘  ≤ω ()
  tr-≤-+ 𝟘 𝟙  𝟘  ()
  tr-≤-+ 𝟘 𝟙  𝟙  ()
  tr-≤-+ 𝟘 𝟙  ≤𝟙 ()
  tr-≤-+ 𝟘 𝟙  ≤ω ()
  tr-≤-+ 𝟘 ≤𝟙 𝟘  ()
  tr-≤-+ 𝟘 ≤𝟙 𝟙  ()
  tr-≤-+ 𝟘 ≤𝟙 ≤𝟙 ()
  tr-≤-+ 𝟘 ≤𝟙 ≤ω ()
  tr-≤-+ 𝟘 ≤ω 𝟘  ()
  tr-≤-+ 𝟘 ≤ω 𝟙  ()
  tr-≤-+ 𝟘 ≤ω ≤𝟙 ()
  tr-≤-+ 𝟘 ≤ω ≤ω ()
  tr-≤-+ 𝟙 𝟘  ≤ω ()
  tr-≤-+ 𝟙 𝟙  𝟙  ()
  tr-≤-+ 𝟙 𝟙  ≤𝟙 ()
  tr-≤-+ 𝟙 𝟙  ≤ω ()
  tr-≤-+ 𝟙 ≤𝟙 𝟙  ()
  tr-≤-+ 𝟙 ≤𝟙 ≤𝟙 ()
  tr-≤-+ 𝟙 ≤𝟙 ≤ω ()
  tr-≤-+ 𝟙 ≤ω 𝟘  ()
  tr-≤-+ 𝟙 ≤ω 𝟙  ()
  tr-≤-+ 𝟙 ≤ω ≤𝟙 ()
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
  tr-≤-· 𝟘 𝟙 𝟙  ()
  tr-≤-· 𝟘 𝟙 ≤𝟙 ()
  tr-≤-· 𝟘 𝟙 ≤ω ()
  tr-≤-· 𝟘 ω 𝟙  ()
  tr-≤-· 𝟘 ω ≤𝟙 ()
  tr-≤-· 𝟘 ω ≤ω ()
  tr-≤-· 𝟙 𝟙 ≤ω ()
  tr-≤-· 𝟙 ω 𝟙  ()
  tr-≤-· 𝟙 ω ≤𝟙 ()
  tr-≤-· 𝟙 ω ≤ω ()

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
  tr-≤-∧ 𝟘 𝟘  𝟙  ()
  tr-≤-∧ 𝟘 𝟘  ≤𝟙 ()
  tr-≤-∧ 𝟘 𝟘  ≤ω ()
  tr-≤-∧ 𝟘 𝟙  𝟘  ()
  tr-≤-∧ 𝟘 𝟙  𝟙  ()
  tr-≤-∧ 𝟘 𝟙  ≤𝟙 ()
  tr-≤-∧ 𝟘 𝟙  ≤ω ()
  tr-≤-∧ 𝟘 ≤𝟙 𝟘  ()
  tr-≤-∧ 𝟘 ≤𝟙 𝟙  ()
  tr-≤-∧ 𝟘 ≤𝟙 ≤𝟙 ()
  tr-≤-∧ 𝟘 ≤𝟙 ≤ω ()
  tr-≤-∧ 𝟘 ≤ω 𝟘  ()
  tr-≤-∧ 𝟘 ≤ω 𝟙  ()
  tr-≤-∧ 𝟘 ≤ω ≤𝟙 ()
  tr-≤-∧ 𝟘 ≤ω ≤ω ()
  tr-≤-∧ 𝟙 𝟘  ≤ω ()
  tr-≤-∧ 𝟙 𝟙  ≤ω ()
  tr-≤-∧ 𝟙 ≤𝟙 ≤ω ()
  tr-≤-∧ 𝟙 ≤ω 𝟘  ()
  tr-≤-∧ 𝟙 ≤ω 𝟙  ()
  tr-≤-∧ 𝟙 ≤ω ≤𝟙 ()
  tr-≤-∧ 𝟙 ≤ω ≤ω ()


-- The function linear-or-affine→affine is a morphism from a linear or
-- affine types modality to an affine types modality if certain
-- assumptions hold.

linear-or-affine⇨affine :
  let 𝕄₁ = linear-or-affine
      𝕄₂ = affineModality
  in
  Is-morphism 𝕄₁ 𝕄₂ linear-or-affine→affine
linear-or-affine⇨affine = λ where
    .Is-morphism.first-trivial-if-second-trivial
      ()
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.trivial-⊎-tr-≡-𝟘-⇔        → inj₂ ( tr-≡-𝟘 _
                                                  , λ { refl → refl }
                                                  )
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-ω                      → refl
    .Is-morphism.tr-+ {p = p}              → tr-+ p _
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧                      → ≤-reflexive (tr-∧ _ _)
  where
  open Graded.Modality.Properties affineModality

  tr′ = linear-or-affine→affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl
  tr-≡-𝟘 𝟙  ()
  tr-≡-𝟘 ≤𝟙 ()
  tr-≡-𝟘 ≤ω ()

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

-- The function linear-or-affine→affine is not an order embedding from
-- a linear or affine types modality to an affine types modality.

¬linear-or-affine⇨affine :
  ¬ Is-order-embedding linear-or-affine affineModality
      linear-or-affine→affine
¬linear-or-affine⇨affine m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ≤𝟙} refl of λ ()

-- The function affine→linearity is a morphism from an affine types
-- modality to a linear types modality if certain assumptions hold.

affine⇨linearity :
  let 𝕄₁ = affineModality
      𝕄₂ = linearityModality
  in
  Is-morphism 𝕄₁ 𝕄₂ affine→linearity
affine⇨linearity = λ where
    .Is-morphism.first-trivial-if-second-trivial
      ()
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.trivial-⊎-tr-≡-𝟘-⇔        → inj₂ ( tr-≡-𝟘 _
                                                  , λ { refl → refl }
                                                  )
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-ω                      → refl
    .Is-morphism.tr-+ {p = p}              → tr-+ p _
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧ {p = p}              → ≤-reflexive (tr-∧ p _)
  where
  open Graded.Modality.Properties linearityModality

  tr′ = affine→linearity

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl
  tr-≡-𝟘 𝟙 ()
  tr-≡-𝟘 ω ()

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

-- The function affine→linearity is not an order embedding from an
-- affine types modality to a linear types modality.

¬affine⇨linearity :
  ¬ Is-order-embedding affineModality linearityModality
      affine→linearity
¬affine⇨linearity m =
  case Is-order-embedding.tr-injective m {p = 𝟙} {q = ω} refl of λ ()

-- The function linearity→affine is a morphism from a linear types
-- modality to an affine types modality if certain assumptions hold.

linearity⇨affine :
  let 𝕄₁ = linearityModality
      𝕄₂ = affineModality
  in
  Is-morphism 𝕄₁ 𝕄₂ linearity→affine
linearity⇨affine = λ where
    .Is-morphism.first-trivial-if-second-trivial
      ()
    .Is-morphism.tr-𝟘-≤                    → refl
    .Is-morphism.trivial-⊎-tr-≡-𝟘-⇔        → inj₂ ( tr-≡-𝟘 _
                                                  , λ { refl → refl }
                                                  )
    .Is-morphism.tr-𝟙                      → refl
    .Is-morphism.tr-ω                      → refl
    .Is-morphism.tr-+ {p = p}              → tr-+ p _
    .Is-morphism.tr-·                      → tr-· _ _
    .Is-morphism.tr-∧ {p = p}              → tr-∧ p _
  where
  open Graded.Modality.Properties affineModality

  tr′ = linearity→affine

  tr-≡-𝟘 : ∀ p → tr′ p ≡ 𝟘 → p ≡ 𝟘
  tr-≡-𝟘 𝟘 _ = refl
  tr-≡-𝟘 𝟙 ()
  tr-≡-𝟘 ω ()

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

-- The function linearity→affine is not an order embedding from a
-- linear types modality to an affine types modality.

¬linearity⇨affine :
  ¬ Is-order-embedding linearityModality affineModality
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
  Is-Σ-order-embedding
    ErasureModality
    (zero-one-many-modality 𝟙≤𝟘)
    erasure→zero-one-many
    erasure→zero-one-many-Σ
erasure⇨zero-one-many-Σ {𝟙≤𝟘} = record
  { tr-Σ-morphism = record
    { tr-≤-tr-Σ = λ where
        {p = 𝟘} → refl
        {p = ω} → refl
    ; tr-Σ-𝟘-≡ =
        λ _ → refl
    ; tr-Σ-≤-𝟙 = λ where
        {p = ω} _ → refl
        {p = 𝟘} ()
    ; tr-·-tr-Σ-≤ = λ where
        {p = 𝟘} {q = _} → refl
        {p = ω} {q = 𝟘} → refl
        {p = ω} {q = ω} → refl
    }
  ; tr-≤-tr-Σ-→ = λ where
      {p = 𝟘} {q = 𝟘}         _     → ω , refl , refl
      {p = 𝟘} {q = ω} {r = 𝟘} _     → 𝟘 , refl , refl
      {p = 𝟘} {q = ω} {r = 𝟙} 𝟘≡𝟘∧𝟙 → ⊥-elim (𝟘𝟙ω.𝟘∧𝟙≢𝟘 (sym 𝟘≡𝟘∧𝟙))
      {p = 𝟘} {q = ω} {r = ω} ()
      {p = ω}                 _     → ω , refl , refl
  }
  where
  module 𝟘𝟙ω = ZOM 𝟙≤𝟘

-- The function erasure→zero-one-many-Σ is an order embedding for Σ
-- (with respect to erasure→zero-one-many) from an erasure modality to
-- a linear types modality, given that if the second modality allows
-- 𝟘ᵐ, then the first also does this.

erasure⇨linearity-Σ :
  Is-Σ-order-embedding ErasureModality linearityModality
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
  Is-Σ-order-embedding ErasureModality affineModality
    erasure→zero-one-many erasure→zero-one-many-Σ
erasure⇨affine-Σ = erasure⇨zero-one-many-Σ

-- The function affine→linear-or-affine-Σ is an order embedding for Σ
-- (with respect to affine→linear-or-affine) from an affine types
-- modality to a linear or affine types modality, given that if the
-- second modality allows 𝟘ᵐ, then the first also does this.

affine⇨linear-or-affine-Σ :
  Is-Σ-order-embedding affineModality linear-or-affine
    affine→linear-or-affine affine→linear-or-affine-Σ
affine⇨linear-or-affine-Σ = record
  { tr-Σ-morphism = record
    { tr-≤-tr-Σ = λ where
        {p = 𝟘} → refl
        {p = 𝟙} → refl
        {p = ω} → refl
    ; tr-Σ-𝟘-≡ =
        λ _ → refl
    ; tr-Σ-≤-𝟙 = λ where
        {p = 𝟙} _ → refl
        {p = ω} _ → refl
        {p = 𝟘} ()
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
      {p = 𝟘} {q = 𝟙} {r = 𝟙}  ()
      {p = 𝟘} {q = 𝟙} {r = ≤𝟙} ()
      {p = 𝟘} {q = 𝟙} {r = ≤ω} ()
      {p = 𝟘} {q = ω} {r = 𝟙}  ()
      {p = 𝟘} {q = ω} {r = ≤𝟙} ()
      {p = 𝟘} {q = ω} {r = ≤ω} ()
      {p = 𝟙} {q = 𝟙} {r = ≤ω} ()
      {p = 𝟙} {q = ω} {r = 𝟙}  ()
      {p = 𝟙} {q = ω} {r = ≤𝟙} ()
      {p = 𝟙} {q = ω} {r = ≤ω} ()
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
  , affineModality
  , linear-or-affine
  , affine→linear-or-affine , affine→linear-or-affine-Σ
  , affine⇨linear-or-affine
  , Is-Σ-order-embedding.tr-Σ-morphism affine⇨linear-or-affine-Σ
  , affine⇨linear-or-affine-Σ
  , affine→linear-or-affine-Σ-not-monotone ∘→ Is-morphism.tr-monotone
  , affine→linear-or-affine-Σ-not-monotone ∘→
    Is-order-embedding.tr-monotone

-- The function affine→linearity-Σ is a Σ-morphism (with respect to
-- affine→linearity) from an affine types modality to a linear types
-- modality, given that if the second modality allows 𝟘ᵐ, then the
-- first also does this.

affine⇨linearity-Σ :
  Is-Σ-morphism affineModality linearityModality
    affine→linearity affine→linearity-Σ
affine⇨linearity-Σ = record
  { tr-≤-tr-Σ = λ where
      {p = 𝟘} → refl
      {p = 𝟙} → refl
      {p = ω} → refl
  ; tr-Σ-𝟘-≡ =
      λ _ → refl
  ; tr-Σ-≤-𝟙 = λ where
      {p = 𝟙} _ → refl
      {p = ω} _ → refl
      {p = 𝟘} ()
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
      affineModality
      linearityModality
      affine→linearity affine→linearity-Σ
¬affine⇨linearity-Σ m =
  case
    Is-Σ-order-embedding.tr-≤-tr-Σ-→ m {p = 𝟙} {q = ω} {r = ω} refl
  of λ where
    (𝟘 , () , _)
    (𝟙 , _  , ())
    (ω , _  , ())

------------------------------------------------------------------------
-- nr-preserving, no-nr-preserving and no-nr-glb-preserving morphisms

opaque

  -- The function unit→erasure is nr preserving

  unit⇒erasure-nr-preserving :
    Is-nr-preserving-morphism
      UnitModality
      ErasureModality
      ⦃ unit-has-nr ⦄
      unit→erasure
  unit⇒erasure-nr-preserving = λ where
      .tr-nr → refl
    where
    open Is-nr-preserving-morphism

opaque

  -- The function unit→erasure is no-nr-glb preserving

  unit⇒erasure-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      UnitModality
      ErasureModality
      unit→erasure
  unit⇒erasure-no-nr-glb-preserving = λ where
      .tr-nrᵢ-GLB _ →
        _ , GLB-const (λ { 0 → refl ; (1+ i) → refl})
      .tr-nrᵢ-𝟙-GLB _ →
        _ , GLB-const (λ { 0 → refl ; (1+ i) → refl})
    where
    open Is-no-nr-glb-preserving-morphism
    open Graded.Modality.Properties ErasureModality

opaque

  -- The function erasure→zero-one-many is nr preserving

  erasure⇨zero-one-many-nr-preserving :
    Is-nr-preserving-morphism
      ErasureModality
      (zero-one-many-modality 𝟙≤𝟘)
      ⦃ has-nr₂ = ZOM.zero-one-many-has-nr 𝟙≤𝟘 ⦄
      erasure→zero-one-many
  erasure⇨zero-one-many-nr-preserving {𝟙≤𝟘} = λ where
      .tr-nr {r} {z} → ≤-reflexive (tr-nr′ 𝟙≤𝟘 _ r z _ _)
    where
    open Is-nr-preserving-morphism
    open Graded.Modality.Properties (zero-one-many-modality 𝟙≤𝟘)
    tr-nr′ :
      ∀ 𝟙≤𝟘 →
      let module 𝟘𝟙ω′ = ZOM 𝟙≤𝟘
          tr = erasure→zero-one-many in
      ∀ p r z s n →
      tr (E.nr p r z s n) ≡
      𝟘𝟙ω′.nr (tr p) (tr r) (tr z) (tr s) (tr n)
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

opaque

  -- The function erasure→zero-one-many is no-nr-glb preserving

  erasure⇨zero-one-many-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      ErasureModality
      (zero-one-many-modality 𝟙≤𝟘)
      erasure→zero-one-many
  erasure⇨zero-one-many-no-nr-glb-preserving {𝟙≤𝟘} = λ where
      .tr-nrᵢ-GLB p-glb → _ , ZOM.nr-nrᵢ-GLB 𝟙≤𝟘 _
      .tr-nrᵢ-𝟙-GLB _ → _ , ZOM.nr-nrᵢ-GLB 𝟙≤𝟘 _
    where
    open Is-no-nr-glb-preserving-morphism

opaque

  -- The function zero-one-many→erasure is nr preserving

  zero-one-many⇒erasure-nr-preserving :
    Is-nr-preserving-morphism
      (zero-one-many-modality 𝟙≤𝟘)
      ErasureModality
      ⦃ ZOM.zero-one-many-has-nr 𝟙≤𝟘 ⦄
      ⦃ E.erasure-has-nr ⦄
      zero-one-many→erasure
  zero-one-many⇒erasure-nr-preserving {𝟙≤𝟘} = λ where
      .tr-nr {r} → ≤-reflexive (tr-nr′ 𝟙≤𝟘 _ r _ _ _)
    where
    open Is-nr-preserving-morphism
    open Graded.Modality.Properties ErasureModality
    tr-nr′ :
      ∀ 𝟙≤𝟘 →
      let module 𝟘𝟙ω′ = ZOM 𝟙≤𝟘
          tr = zero-one-many→erasure
      in
      ∀ p r z s n →
      tr (𝟘𝟙ω′.nr p r z s n) ≡
      E.nr (tr p) (tr r) (tr z) (tr s) (tr n)
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

opaque

  -- The function zero-one-many→erasure is no-nr-glb preserving

  zero-one-many⇒erasure-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      (zero-one-many-modality 𝟙≤𝟘)
      ErasureModality
      zero-one-many→erasure
  zero-one-many⇒erasure-no-nr-glb-preserving = λ where
      .tr-nrᵢ-GLB _ → EP.Erasure-nrᵢ-glb _ _ _
      .tr-nrᵢ-𝟙-GLB _ → EP.Erasure-nrᵢ-glb _ _ _
    where
    open Is-no-nr-glb-preserving-morphism

opaque

  -- The function erasure→zero-one-many is nr preserving from an
  -- erasure modality to a linear types modality

  erasure⇒linearity-nr-preserving :
    Is-nr-preserving-morphism
      ErasureModality
      linearityModality
      ⦃ E.erasure-has-nr ⦄
      ⦃ L.zero-one-many-has-nr ⦄
      erasure→zero-one-many
  erasure⇒linearity-nr-preserving = erasure⇨zero-one-many-nr-preserving

opaque

  -- The function erasure→zero-one-many is nr preserving from an
  -- erasure modality to a affine types modality

  erasure⇒affine-nr-preserving :
    Is-nr-preserving-morphism
      ErasureModality
      affineModality
      ⦃ E.erasure-has-nr ⦄
      ⦃ A.zero-one-many-has-nr ⦄
      erasure→zero-one-many
  erasure⇒affine-nr-preserving = erasure⇨zero-one-many-nr-preserving

opaque

  -- The function erasure→zero-one-many is no-nr-glb preserving from an
  -- erasure modality to a linear types modality

  erasure⇒linearity-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      ErasureModality
      linearityModality
      erasure→zero-one-many
  erasure⇒linearity-no-nr-glb-preserving = erasure⇨zero-one-many-no-nr-glb-preserving

opaque

  -- The function erasure→zero-one-many is no-nr-glb preserving from an
  -- erasure modality to a affine types modality

  erasure⇒affine-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      ErasureModality
      affineModality
      erasure→zero-one-many
  erasure⇒affine-no-nr-glb-preserving = erasure⇨zero-one-many-no-nr-glb-preserving

opaque

 -- The function zero-one-many→erasure is nr preserving from a
 -- linear types modality to an erasure modality

  linearity⇒erasure-nr-preserving :
    Is-nr-preserving-morphism
      linearityModality
      ErasureModality
      ⦃ L.zero-one-many-has-nr ⦄
      ⦃ E.erasure-has-nr ⦄
      zero-one-many→erasure
  linearity⇒erasure-nr-preserving = zero-one-many⇒erasure-nr-preserving

opaque

 -- The function zero-one-many→erasure is nr preserving from a
 -- affine types modality to an erasure modality

  affine⇒erasure-nr-preserving :
    Is-nr-preserving-morphism
      affineModality
      ErasureModality
      ⦃ A.zero-one-many-has-nr ⦄
      ⦃ E.erasure-has-nr ⦄
      zero-one-many→erasure
  affine⇒erasure-nr-preserving = zero-one-many⇒erasure-nr-preserving

opaque

 -- The function zero-one-many→erasure is no-nr preserving from a
 -- affine types modality to an erasure modality

  affine⇒erasure-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      affineModality
      ErasureModality
      zero-one-many→erasure
  affine⇒erasure-no-nr-glb-preserving = zero-one-many⇒erasure-no-nr-glb-preserving

opaque

 -- The function zero-one-many→erasure is no-nr-glb preserving from a
 -- linear types modality to an erasure modality

  linearity⇒erasure-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      linearityModality
      ErasureModality
      zero-one-many→erasure
  linearity⇒erasure-no-nr-glb-preserving = zero-one-many⇒erasure-no-nr-glb-preserving

opaque

  -- The function linearity→linear-or-affine is nr preserving

  linearity⇨linear-or-affine-nr-preserving :
    Is-nr-preserving-morphism
      linearityModality
      linear-or-affine
      ⦃ L.zero-one-many-has-nr ⦄
      ⦃ LA.linear-or-affine-has-nr ⦄
      linearity→linear-or-affine
  linearity⇨linear-or-affine-nr-preserving = λ where
      .tr-nr {r} → tr-nr′ _ r _ _ _
    where
    open Is-nr-preserving-morphism
    tr : Linearity → Linear-or-affine
    tr = linearity→linear-or-affine
    tr-nr′ :
      ∀ p r z s n →
      tr (L.nr p r z s n) LA.≤
      LA.nr (tr p) (tr r) (tr z) (tr s) (tr n)
    tr-nr′ = λ where
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

opaque

  -- The function linearity→linear-or-affine is no-nr-glb preserving

  linearity⇨linear-or-affine-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      linearityModality
      linear-or-affine
      linearity→linear-or-affine
  linearity⇨linear-or-affine-no-nr-glb-preserving = λ where
      .tr-nrᵢ-GLB _ → _ , LA.nr-nrᵢ-GLB _
      .tr-nrᵢ-𝟙-GLB _ → _ , LA.nr-nrᵢ-GLB _
    where
    open Is-no-nr-glb-preserving-morphism

opaque

  -- The function linear-or-affine→linearity is nr preserving

  linear-or-affine⇨linearity-nr-preserving :
    Is-nr-preserving-morphism
      linear-or-affine
      linearityModality
      ⦃ LA.linear-or-affine-has-nr ⦄
      ⦃ L.zero-one-many-has-nr ⦄
      linear-or-affine→linearity
  linear-or-affine⇨linearity-nr-preserving = λ where
      .tr-nr {r} → ≤-reflexive (tr-nr′ _ r _ _ _)
    where
    open Is-nr-preserving-morphism
    open Graded.Modality.Properties linearityModality
    tr : Linear-or-affine → Linearity
    tr = linear-or-affine→linearity
    tr-nr′ :
      ∀ p r z s n →
      tr (LA.nr p r z s n) ≡
      L.nr (tr p) (tr r) (tr z) (tr s) (tr n)
    tr-nr′ = λ where
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

opaque

  -- The function linear-or-affine→linearity is no-nr-glb preserving

  linear-or-affine⇨linearity-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      linear-or-affine
      linearityModality
      linear-or-affine→linearity
  linear-or-affine⇨linearity-no-nr-glb-preserving = λ where
      .tr-nrᵢ-GLB _ → _ , L.nr-nrᵢ-GLB _
      .tr-nrᵢ-𝟙-GLB _ → _ , L.nr-nrᵢ-GLB _
    where
    open Is-no-nr-glb-preserving-morphism

opaque

  -- The function affine→linear-or-affine is nr preserving

  affine⇨linear-or-affine-nr-preserving :
    Is-nr-preserving-morphism
      affineModality
      linear-or-affine
      ⦃ A.zero-one-many-has-nr ⦄
      ⦃ LA.linear-or-affine-has-nr ⦄
      affine→linear-or-affine
  affine⇨linear-or-affine-nr-preserving = λ where
      .tr-nr {r} → ≤-reflexive (tr-nr′ _ r _ _ _)
    where
    open Is-nr-preserving-morphism
    open Graded.Modality.Properties linear-or-affine
    tr : Affine → Linear-or-affine
    tr = affine→linear-or-affine
    tr-nr′ :
      ∀ p r z s n →
      tr (A.nr p r z s n) ≡
      LA.nr (tr p) (tr r) (tr z) (tr s) (tr n)
    tr-nr′ = λ where
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

opaque

  -- The function affine→linear-or-affine is no-nr-glb preserving

  affine⇨linear-or-affine-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      affineModality
      linear-or-affine
      affine→linear-or-affine
  affine⇨linear-or-affine-no-nr-glb-preserving = λ where
      .tr-nrᵢ-GLB _ → _ , LA.nr-nrᵢ-GLB _
      .tr-nrᵢ-𝟙-GLB _ → _ , LA.nr-nrᵢ-GLB _
    where
    open Is-no-nr-glb-preserving-morphism

opaque

  -- The function linear-or-affine→affine is nr preserving

  linear-or-affine⇨affine-nr-preserving :
    Is-nr-preserving-morphism
      linear-or-affine
      affineModality
      ⦃ LA.linear-or-affine-has-nr ⦄
      ⦃ A.zero-one-many-has-nr ⦄
      linear-or-affine→affine
  linear-or-affine⇨affine-nr-preserving = λ where
      .tr-nr {r} → ≤-reflexive (tr-nr′ _ r _ _ _)
    where
    open Is-nr-preserving-morphism
    open Graded.Modality.Properties affineModality
    tr : Linear-or-affine → Affine
    tr = linear-or-affine→affine
    tr-nr′ :
      ∀ p r z s n →
      tr (LA.nr p r z s n) ≡
      A.nr (tr p) (tr r) (tr z) (tr s) (tr n)
    tr-nr′ = λ where
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

opaque

  -- The function linear-or-affine→affine is no-nr-glb preserving

  linear-or-affine⇨affine-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      linear-or-affine
      affineModality
      linear-or-affine→affine
  linear-or-affine⇨affine-no-nr-glb-preserving = λ where
      .tr-nrᵢ-GLB _ → _ , A.nr-nrᵢ-GLB _
      .tr-nrᵢ-𝟙-GLB _ → _ , A.nr-nrᵢ-GLB _
    where
    open Is-no-nr-glb-preserving-morphism

opaque

  -- The function affine→linearity is nr preserving

  affine⇨linearity-nr-preserving :
    Is-nr-preserving-morphism
      affineModality
      linearityModality
      ⦃ A.zero-one-many-has-nr ⦄
      ⦃ L.zero-one-many-has-nr ⦄
      affine→linearity
  affine⇨linearity-nr-preserving = λ where
      .tr-nr {r} → ≤-reflexive (tr-nr′ _ r _ _ _)
    where
    open Is-nr-preserving-morphism
    open Graded.Modality.Properties linearityModality
    tr : Affine → Linearity
    tr = affine→linearity
    tr-nr′ :
      ∀ p r z s n →
      tr (A.nr p r z s n) ≡
      L.nr (tr p) (tr r) (tr z) (tr s) (tr n)
    tr-nr′ = λ where
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

opaque

  -- The function affine→linearity is no-nr-glb preserving

  affine⇨linearity-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      affineModality
      linearityModality
      affine→linearity
  affine⇨linearity-no-nr-glb-preserving = λ where
      .tr-nrᵢ-GLB _ → _ , L.nr-nrᵢ-GLB _
      .tr-nrᵢ-𝟙-GLB _ → _ , L.nr-nrᵢ-GLB _
    where
    open Is-no-nr-glb-preserving-morphism

opaque

  -- The function linearity→affine is nr preserving

  linearity⇨affine-nr-preserving :
    Is-nr-preserving-morphism
      linearityModality
      affineModality
      ⦃ L.zero-one-many-has-nr ⦄
      ⦃ A.zero-one-many-has-nr ⦄
      linearity→affine
  linearity⇨affine-nr-preserving = λ where
      .tr-nr {r} → tr-nr′ _ r _ _ _
    where
    open Is-nr-preserving-morphism
    tr : Linearity → Affine
    tr = linearity→affine
    tr-nr′ :
      ∀ p r z s n →
      tr (L.nr p r z s n) A.≤
      A.nr (tr p) (tr r) (tr z) (tr s) (tr n)
    tr-nr′ = λ where
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

opaque

  -- The function linearity→affine is no-nr-glb preserving

  linearity⇨affine-no-nr-glb-preserving :
    Is-no-nr-glb-preserving-morphism
      linearityModality
      affineModality
      linearity→affine
  linearity⇨affine-no-nr-glb-preserving = λ where
      .tr-nrᵢ-GLB _ → _ , A.nr-nrᵢ-GLB _
      .tr-nrᵢ-𝟙-GLB _ → _ , A.nr-nrᵢ-GLB _
    where
    open Is-no-nr-glb-preserving-morphism

------------------------------------------------------------------------
-- nr-reflecting and no-nr-glb-reflecting morphisms

opaque

  -- The function unit→erasure is nr reflecting

  unit⇒erasure-nr-reflecting :
    Is-nr-reflecting-morphism
      UnitModality
      ErasureModality
      ⦃ unit-has-nr ⦄
      unit→erasure
  unit⇒erasure-nr-reflecting = λ where
      .tr-≤-nr _ →
        _ , _ , _ , refl , refl , refl , refl
    where
    open Is-nr-reflecting-morphism

opaque

  -- The function unit→erasure is no-nr-glb reflecting

  unit⇒erasure-no-nr-glb-reflecting :
    Is-no-nr-glb-reflecting-morphism
      UnitModality
      ErasureModality
      unit→erasure
  unit⇒erasure-no-nr-glb-reflecting = λ where
      .tr-≤-no-nr _ _ _ →
        _ , _ , _ , _ , _ , refl , refl , refl
          , GLB-const′ , GLB-const′ , refl
      .tr-nrᵢ-glb _ →
        _ , GLB-const′
    where
    open Is-no-nr-glb-reflecting-morphism
    open Graded.Modality.Properties UnitModality

opaque

  -- The function erasure→zero-one-many is nr reflecting

  erasure⇨zero-one-many-nr-reflecting :
    Is-nr-reflecting-morphism
      ErasureModality
      (zero-one-many-modality 𝟙≤𝟘)
      ⦃ has-nr₂ = ZOM.zero-one-many-has-nr 𝟙≤𝟘 ⦄
      erasure→zero-one-many
  erasure⇨zero-one-many-nr-reflecting = λ where
      .tr-≤-nr {r} → tr-≤-nr′ _ _ _ r _ _ _
    where
    open Is-nr-reflecting-morphism
    tr-≤-nr′ :
      ∀ 𝟙≤𝟘 →
      let module 𝟘𝟙ω′ = ZOM 𝟙≤𝟘
          tr = erasure→zero-one-many in
      ∀ q p r z₁ s₁ n₁ →
      tr q 𝟘𝟙ω′.≤ 𝟘𝟙ω′.nr (tr p) (tr r) z₁ s₁ n₁ →
      ∃₃ λ z₂ s₂ n₂ →
         tr z₂ 𝟘𝟙ω′.≤ z₁ × tr s₂ 𝟘𝟙ω′.≤ s₁ × tr n₂ 𝟘𝟙ω′.≤ n₁ ×
         q E.≤ E.nr p r z₂ s₂ n₂
    tr-≤-nr′ = λ where
      _     𝟘 𝟘 𝟘 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     𝟘 𝟘 ω 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     𝟘 ω 𝟘 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     𝟘 ω ω 𝟘 𝟘 𝟘 _  → 𝟘 , 𝟘 , 𝟘 , refl , refl , refl , refl
      _     ω _ _ _ _ _ _  → ω , ω , ω , refl , refl , refl , refl
      true  𝟘 𝟘 𝟘 𝟘 𝟘 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟘 𝟘 𝟙 ()
      true  𝟘 𝟘 𝟘 𝟘 𝟘 ω ()
      false 𝟘 𝟘 𝟘 𝟘 𝟘 ω ()
      true  𝟘 𝟘 𝟘 𝟘 𝟙 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟘 𝟙 𝟘 ()
      true  𝟘 𝟘 𝟘 𝟘 𝟙 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟘 𝟙 𝟙 ()
      true  𝟘 𝟘 𝟘 𝟘 𝟙 ω ()
      false 𝟘 𝟘 𝟘 𝟘 𝟙 ω ()
      true  𝟘 𝟘 𝟘 𝟘 ω 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟘 ω 𝟘 ()
      true  𝟘 𝟘 𝟘 𝟘 ω 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟘 ω 𝟙 ()
      true  𝟘 𝟘 𝟘 𝟘 ω ω ()
      false 𝟘 𝟘 𝟘 𝟘 ω ω ()
      true  𝟘 𝟘 𝟘 𝟙 𝟘 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟘 𝟘 ()
      true  𝟘 𝟘 𝟘 𝟙 𝟘 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟘 𝟙 ()
      true  𝟘 𝟘 𝟘 𝟙 𝟘 ω ()
      false 𝟘 𝟘 𝟘 𝟙 𝟘 ω ()
      true  𝟘 𝟘 𝟘 𝟙 𝟙 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟙 𝟘 ()
      true  𝟘 𝟘 𝟘 𝟙 𝟙 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟙 𝟙 𝟙 ()
      true  𝟘 𝟘 𝟘 𝟙 𝟙 ω ()
      false 𝟘 𝟘 𝟘 𝟙 𝟙 ω ()
      true  𝟘 𝟘 𝟘 𝟙 ω 𝟘 ()
      false 𝟘 𝟘 𝟘 𝟙 ω 𝟘 ()
      true  𝟘 𝟘 𝟘 𝟙 ω 𝟙 ()
      false 𝟘 𝟘 𝟘 𝟙 ω 𝟙 ()
      true  𝟘 𝟘 𝟘 𝟙 ω ω ()
      false 𝟘 𝟘 𝟘 𝟙 ω ω ()
      true  𝟘 𝟘 𝟘 ω 𝟘 𝟘 ()
      false 𝟘 𝟘 𝟘 ω 𝟘 𝟘 ()
      true  𝟘 𝟘 𝟘 ω 𝟘 𝟙 ()
      false 𝟘 𝟘 𝟘 ω 𝟘 𝟙 ()
      true  𝟘 𝟘 𝟘 ω 𝟘 ω ()
      false 𝟘 𝟘 𝟘 ω 𝟘 ω ()
      true  𝟘 𝟘 𝟘 ω 𝟙 𝟘 ()
      false 𝟘 𝟘 𝟘 ω 𝟙 𝟘 ()
      true  𝟘 𝟘 𝟘 ω 𝟙 𝟙 ()
      false 𝟘 𝟘 𝟘 ω 𝟙 𝟙 ()
      true  𝟘 𝟘 𝟘 ω 𝟙 ω ()
      false 𝟘 𝟘 𝟘 ω 𝟙 ω ()
      true  𝟘 𝟘 𝟘 ω ω 𝟘 ()
      false 𝟘 𝟘 𝟘 ω ω 𝟘 ()
      true  𝟘 𝟘 𝟘 ω ω 𝟙 ()
      false 𝟘 𝟘 𝟘 ω ω 𝟙 ()
      true  𝟘 𝟘 𝟘 ω ω ω ()
      false 𝟘 𝟘 𝟘 ω ω ω ()
      _     𝟘 𝟘 ω 𝟘 𝟘 𝟙 ()
      _     𝟘 𝟘 ω 𝟘 𝟘 ω ()
      _     𝟘 𝟘 ω 𝟘 𝟙 𝟘 ()
      _     𝟘 𝟘 ω 𝟘 𝟙 𝟙 ()
      _     𝟘 𝟘 ω 𝟘 𝟙 ω ()
      _     𝟘 𝟘 ω 𝟘 ω 𝟘 ()
      _     𝟘 𝟘 ω 𝟘 ω 𝟙 ()
      _     𝟘 𝟘 ω 𝟘 ω ω ()
      _     𝟘 𝟘 ω 𝟙 𝟘 𝟘 ()
      _     𝟘 𝟘 ω 𝟙 𝟘 𝟙 ()
      _     𝟘 𝟘 ω 𝟙 𝟘 ω ()
      _     𝟘 𝟘 ω 𝟙 𝟙 𝟘 ()
      _     𝟘 𝟘 ω 𝟙 𝟙 𝟙 ()
      _     𝟘 𝟘 ω 𝟙 𝟙 ω ()
      _     𝟘 𝟘 ω 𝟙 ω 𝟘 ()
      _     𝟘 𝟘 ω 𝟙 ω 𝟙 ()
      _     𝟘 𝟘 ω 𝟙 ω ω ()
      _     𝟘 𝟘 ω ω 𝟘 𝟘 ()
      _     𝟘 𝟘 ω ω 𝟘 𝟙 ()
      _     𝟘 𝟘 ω ω 𝟘 ω ()
      _     𝟘 𝟘 ω ω 𝟙 𝟘 ()
      _     𝟘 𝟘 ω ω 𝟙 𝟙 ()
      _     𝟘 𝟘 ω ω 𝟙 ω ()
      _     𝟘 𝟘 ω ω ω 𝟘 ()
      _     𝟘 𝟘 ω ω ω 𝟙 ()
      _     𝟘 𝟘 ω ω ω ω ()
      _     𝟘 ω 𝟘 𝟘 𝟘 𝟙 ()
      _     𝟘 ω 𝟘 𝟘 𝟘 ω ()
      true  𝟘 ω 𝟘 𝟘 𝟙 𝟘 ()
      false 𝟘 ω 𝟘 𝟘 𝟙 𝟘 ()
      _     𝟘 ω 𝟘 𝟘 𝟙 𝟙 ()
      _     𝟘 ω 𝟘 𝟘 𝟙 ω ()
      _     𝟘 ω 𝟘 𝟘 ω 𝟘 ()
      _     𝟘 ω 𝟘 𝟘 ω 𝟙 ()
      _     𝟘 ω 𝟘 𝟘 ω ω ()
      true  𝟘 ω 𝟘 𝟙 𝟘 𝟘 ()
      false 𝟘 ω 𝟘 𝟙 𝟘 𝟘 ()
      _     𝟘 ω 𝟘 𝟙 𝟘 𝟙 ()
      _     𝟘 ω 𝟘 𝟙 𝟘 ω ()
      true  𝟘 ω 𝟘 𝟙 𝟙 𝟘 ()
      false 𝟘 ω 𝟘 𝟙 𝟙 𝟘 ()
      _     𝟘 ω 𝟘 𝟙 𝟙 𝟙 ()
      _     𝟘 ω 𝟘 𝟙 𝟙 ω ()
      _     𝟘 ω 𝟘 𝟙 ω 𝟘 ()
      _     𝟘 ω 𝟘 𝟙 ω 𝟙 ()
      _     𝟘 ω 𝟘 𝟙 ω ω ()
      _     𝟘 ω 𝟘 ω 𝟘 𝟘 ()
      _     𝟘 ω 𝟘 ω 𝟘 𝟙 ()
      _     𝟘 ω 𝟘 ω 𝟘 ω ()
      _     𝟘 ω 𝟘 ω 𝟙 𝟘 ()
      _     𝟘 ω 𝟘 ω 𝟙 𝟙 ()
      _     𝟘 ω 𝟘 ω 𝟙 ω ()
      _     𝟘 ω 𝟘 ω ω 𝟘 ()
      _     𝟘 ω 𝟘 ω ω 𝟙 ()
      _     𝟘 ω 𝟘 ω ω ω ()
      _     𝟘 ω ω 𝟘 𝟘 𝟙 ()
      _     𝟘 ω ω 𝟘 𝟘 ω ()
      _     𝟘 ω ω 𝟘 𝟙 𝟘 ()
      _     𝟘 ω ω 𝟘 𝟙 𝟙 ()
      _     𝟘 ω ω 𝟘 𝟙 ω ()
      _     𝟘 ω ω 𝟘 ω 𝟘 ()
      _     𝟘 ω ω 𝟘 ω 𝟙 ()
      _     𝟘 ω ω 𝟘 ω ω ()
      _     𝟘 ω ω 𝟙 𝟘 𝟘 ()
      _     𝟘 ω ω 𝟙 𝟘 𝟙 ()
      _     𝟘 ω ω 𝟙 𝟘 ω ()
      _     𝟘 ω ω 𝟙 𝟙 𝟘 ()
      _     𝟘 ω ω 𝟙 𝟙 𝟙 ()
      _     𝟘 ω ω 𝟙 𝟙 ω ()
      _     𝟘 ω ω 𝟙 ω 𝟘 ()
      _     𝟘 ω ω 𝟙 ω 𝟙 ()
      _     𝟘 ω ω 𝟙 ω ω ()
      _     𝟘 ω ω ω 𝟘 𝟘 ()
      _     𝟘 ω ω ω 𝟘 𝟙 ()
      _     𝟘 ω ω ω 𝟘 ω ()
      _     𝟘 ω ω ω 𝟙 𝟘 ()
      _     𝟘 ω ω ω 𝟙 𝟙 ()
      _     𝟘 ω ω ω 𝟙 ω ()
      _     𝟘 ω ω ω ω 𝟘 ()
      _     𝟘 ω ω ω ω 𝟙 ()
      _     𝟘 ω ω ω ω ω ()

opaque

  -- The function erasure→zero-one-many is nr reflecting from an
  -- erasure modality to a linear types modality

  erasure⇒linearity-nr-reflecting :
    Is-nr-reflecting-morphism
      ErasureModality
      linearityModality
      ⦃ E.erasure-has-nr ⦄
      ⦃ L.zero-one-many-has-nr ⦄
      erasure→zero-one-many
  erasure⇒linearity-nr-reflecting = erasure⇨zero-one-many-nr-reflecting

opaque

  -- The function erasure→zero-one-many is nr reflecting from an
  -- erasure modality to a affinetypes modality

  erasure⇒affine-nr-reflecting :
    Is-nr-reflecting-morphism
      ErasureModality
      affineModality
      ⦃ E.erasure-has-nr ⦄
      ⦃ A.zero-one-many-has-nr ⦄
      erasure→zero-one-many
  erasure⇒affine-nr-reflecting = erasure⇨zero-one-many-nr-reflecting

opaque

  -- The function linearity→linear-or-affine is nr reflecting

  linearity⇨linear-or-affine-nr-reflecting :
    Is-nr-reflecting-morphism
      linearityModality
      linear-or-affine
      ⦃ L.zero-one-many-has-nr ⦄
      ⦃ LA.linear-or-affine-has-nr ⦄
      linearity→linear-or-affine
  linearity⇨linear-or-affine-nr-reflecting = λ where
      .tr-≤-nr {r} → tr-≤-nr′ _ _ r _ _ _
    where
    open Is-nr-reflecting-morphism
    tr : Linearity → Linear-or-affine
    tr = linearity→linear-or-affine
    tr-≤-nr′ :
      ∀ q p r z₁ s₁ n₁ →
      tr q LA.≤ LA.nr (tr p) (tr r) z₁ s₁ n₁ →
      ∃₃ λ z₂ s₂ n₂ →
         tr z₂ LA.≤ z₁ × tr s₂ LA.≤ s₁ × tr n₂ LA.≤ n₁ ×
         q L.≤ L.nr p r z₂ s₂ n₂
    tr-≤-nr′ = λ where
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

opaque

  -- The function affine→linear-or-affine is nr reflecting

  affine⇨linear-or-affine-nr-reflecting :
    Is-nr-reflecting-morphism
      affineModality
      linear-or-affine
      ⦃ A.zero-one-many-has-nr ⦄
      ⦃ LA.linear-or-affine-has-nr ⦄
      affine→linear-or-affine
  affine⇨linear-or-affine-nr-reflecting = λ where
      .tr-≤-nr {r} → tr-≤-nr′ _ _ r _ _ _
    where
    open Is-nr-reflecting-morphism
    tr : Affine → Linear-or-affine
    tr = affine→linear-or-affine
    tr-≤-nr′ :
      ∀ q p r z₁ s₁ n₁ →
      tr q LA.≤ LA.nr (tr p) (tr r) z₁ s₁ n₁ →
      ∃₃ λ z₂ s₂ n₂ →
         tr z₂ LA.≤ z₁ × tr s₂ LA.≤ s₁ × tr n₂ LA.≤ n₁ ×
         q A.≤ A.nr p r z₂ s₂ n₂
    tr-≤-nr′ = λ where
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
