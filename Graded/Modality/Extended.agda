------------------------------------------------------------------------
-- Modalities packaged with other things, and morphisms between these
-- packages
------------------------------------------------------------------------

module Graded.Modality.Extended where

open import Tools.Function
open import Tools.Level

import Definition.Typechecking.Decidable.Assumptions as TD
open import Definition.Typed.Restrictions

open import Graded.FullReduction.Assumptions
open import Graded.Modality
open import Graded.Modality.Morphism
open import Graded.Modality.Morphism.Type-restrictions
open import Graded.Modality.Morphism.Usage-restrictions
import Graded.Usage.Decidable.Assumptions as UD
open import Graded.Usage.Restrictions
open import Graded.Usage.Restrictions.Natrec

private variable
  a₁ a₂ : Level

-- A modality along with type and usage restrictions as well as some
-- proofs.

record Extended-modality a : Set (lsuc a) where
  no-eta-equality
  field
    -- The type of grades.
    M  : Set a

    -- M is a modality.
    𝕄  : Modality M

  open Modality 𝕄 public

  field
    -- Type restrictions for 𝕄.
    TR : Type-restrictions 𝕄

    -- Usage restrictions for 𝕄.
    UR : Usage-restrictions 𝕄

    -- The full reduction assumptions hold for TR and UR.
    FA : Full-reduction-assumptions TR UR

    -- The assumptions used to prove decidability of type-checking
    -- (for certain contexts, types and terms) hold for TR.
    TA : TD.Assumptions TR

    -- The assumptions used to prove that the usage relation is
    -- decidable hold for UR.
    UA : UD.Assumptions UR

    -- The modality supports nr functions.
    NR : Usage-restrictions.Nr-available UR

    -- The modality supports the additional properties required
    -- when the natrec-mode is chosen to be No-nr-glb.
    NO-NR-GLB : Supports-GLB-for-natrec _ semiring-with-meet

  open Has-nr (Natrec-mode-Has-nr 𝕄 NR) public

  field
    -- The dedicated nr function satisfies Linearity-like-nr-for-𝟘.
    NR₀ : Linearity-like-nr-for-𝟘

    -- The dedicated nr function satisfies Linearity-like-nr-for-𝟙.
    NR₁ : Linearity-like-nr-for-𝟙

  open Type-restrictions TR public
  open Usage-restrictions UR public
  open Full-reduction-assumptions FA public

private variable
  𝕄 𝕄₁ 𝕄₂ 𝕄₃ : Extended-modality _

-- A morphism from one extended modality to another.

infix 4 _⇨_

record _⇨_
  (𝕄₁ : Extended-modality a₁) (𝕄₂ : Extended-modality a₂) :
  Set (a₁ ⊔ a₂) where
  no-eta-equality
  module M₁ = Extended-modality 𝕄₁
  module M₂ = Extended-modality 𝕄₂
  field
    tr tr-Σ :
      M₁.M → M₂.M
    is-order-embedding :
      Is-order-embedding M₁.𝕄 M₂.𝕄 tr
    is-Σ-order-embedding :
      Is-Σ-order-embedding M₁.𝕄 M₂.𝕄 tr tr-Σ
    are-preserving-type-restrictions :
      Are-preserving-type-restrictions M₁.TR M₂.TR tr tr-Σ
    are-reflecting-type-restrictions :
      Are-reflecting-type-restrictions M₁.TR M₂.TR tr tr-Σ
    are-preserving-usage-restrictions :
      Are-preserving-usage-restrictions M₁.UR M₂.UR tr tr-Σ
    are-reflecting-usage-restrictions :
      Are-reflecting-usage-restrictions M₁.UR M₂.UR tr tr-Σ

  open Is-order-embedding is-order-embedding public
  open Is-Σ-order-embedding is-Σ-order-embedding public
  open Are-preserving-type-restrictions
         are-preserving-type-restrictions
    public
  open Are-reflecting-type-restrictions
         are-reflecting-type-restrictions
    public
  open Are-preserving-usage-restrictions
         are-preserving-usage-restrictions
    public
  open Are-reflecting-usage-restrictions
         are-reflecting-usage-restrictions
    public
    hiding
      (common-properties; 𝟘ᵐ-preserved; starˢ-sink-preserved;
       Id-erased-preserved; erased-matches-for-J-preserved;
       erased-matches-for-K-preserved;
       nr-in-first-if-in-second; nr-in-second-if-in-first;
       no-nr-in-first-if-in-second; no-nr-in-second-if-in-first;
       no-nr-glb-in-first-if-in-second; no-nr-glb-in-second-if-in-first)

-- An identity morphism.

id : 𝕄 ⇨ 𝕄
id = λ where
  ._⇨_.tr →
    idᶠ
  ._⇨_.tr-Σ →
    idᶠ
  ._⇨_.is-order-embedding →
    Is-order-embedding-id
  ._⇨_.is-Σ-order-embedding →
    Is-order-embedding→Is-Σ-order-embedding Is-order-embedding-id
  ._⇨_.are-preserving-type-restrictions →
    Are-preserving-type-restrictions-id
  ._⇨_.are-reflecting-type-restrictions →
    Are-reflecting-type-restrictions-id
  ._⇨_.are-preserving-usage-restrictions →
    Are-preserving-usage-restrictions-id
  ._⇨_.are-reflecting-usage-restrictions →
    Are-reflecting-usage-restrictions-id

-- Composition of morphisms.

_∘_ : 𝕄₂ ⇨ 𝕄₃ → 𝕄₁ ⇨ 𝕄₂ → 𝕄₁ ⇨ 𝕄₃
m₁ ∘ m₂ = λ where
    ._⇨_.tr →
      M₁.tr ∘→ M₂.tr
    ._⇨_.tr-Σ →
      M₁.tr-Σ ∘→ M₂.tr-Σ
    ._⇨_.is-order-embedding →
      Is-order-embedding-∘ M₁.is-order-embedding M₂.is-order-embedding
    ._⇨_.is-Σ-order-embedding →
      Is-Σ-order-embedding-∘
        (Is-order-embedding.tr-morphism M₁.is-order-embedding)
        (Is-order-embedding.tr-morphism M₂.is-order-embedding)
        M₁.is-Σ-order-embedding M₂.is-Σ-order-embedding
    ._⇨_.are-preserving-type-restrictions →
      Are-preserving-type-restrictions-∘
        M₁.are-preserving-type-restrictions
        M₂.are-preserving-type-restrictions
    ._⇨_.are-reflecting-type-restrictions →
      Are-reflecting-type-restrictions-∘
        M₁.are-reflecting-type-restrictions
        M₂.are-reflecting-type-restrictions
    ._⇨_.are-preserving-usage-restrictions →
      Are-preserving-usage-restrictions-∘
        M₁.tr-morphism
        M₂.tr-morphism
        M₁.are-preserving-usage-restrictions
        M₂.are-preserving-usage-restrictions
    ._⇨_.are-reflecting-usage-restrictions →
      Are-reflecting-usage-restrictions-∘
        M₁.tr-morphism
        M₁.are-reflecting-usage-restrictions
        M₂.are-reflecting-usage-restrictions
  where
  module M₁ = _⇨_ m₁
  module M₂ = _⇨_ m₂
