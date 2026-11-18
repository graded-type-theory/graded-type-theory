------------------------------------------------------------------------
-- Modalities packaged with other things, and morphisms between these
-- packages
------------------------------------------------------------------------

module Graded.Modality.Extended where

open import Tools.Bool
open import Tools.Function
open import Tools.Level

open import Configuration-types
import Configuration-types.Instance.Configuration
open import Configuration-types.Natrec
open import Configuration-types.Omega

import Definition.Typechecking.Decidable.Assumptions as TD

open import Graded.FullReduction.Assumptions
open import Graded.Modality
open import Graded.Modality.Morphism
open import Graded.Modality.Morphism.Configuration
open import Graded.Modality.Morphism.Type-configuration
open import Graded.Modality.Properties.Subtraction
open import Graded.Mode.Instances.Zero-one
open import Graded.Mode.Instances.Zero-one.Variant
import Graded.Usage.Decidable.Assumptions as UD

private variable
  a₁ a₂ : Level

-- A modality along with a configuration as well as some other things.

record Extended-modality a : Set (lsuc a) where
  no-eta-equality
  field
    -- The type of grades.
    M  : Set a

    -- M is a modality.
    𝕄  : Modality M

    -- The mode variant.
    MV : Mode-variant 𝕄

  open Modality 𝕄 public

  field
    -- Configuration for Zero-one-isMode.
    C : Configuration (Zero-one-isMode MV)

  open Configuration C
  open Configuration-types.Instance.Configuration C

  field
    -- The full reduction assumptions hold for C.
    FA : Full-reduction-assumptions MV C

    -- The assumptions used to prove decidability of typing (for
    -- certain contexts, types and terms) and usage hold for C.
    DA : UD.Assumptions C

    -- The modality supports nr functions.
    NR : Configuration.Nr-available C

    -- The modality has well-behaved GLBs.
    NO-NR-GLB : Has-well-behaved-GLBs _ 𝕄

    -- The modality has a dedicated grade ω.
    ⦃ HAS-ω ⦄ : Omega-allowed

  open Has-nr (Natrec-mode-Has-nr 𝕄 NR) public

  field
    -- The dedicated nr function satisfies Linearity-like-nr-for-𝟘.
    NR₀ : Linearity-like-nr-for-𝟘

    -- The dedicated nr function satisfies Linearity-like-nr-for-𝟙.
    NR₁ : Linearity-like-nr-for-𝟙

    -- The modality supports subtraction
    SUB : Supports-subtraction 𝕄

  open Configuration C public
  open Full-reduction-assumptions FA public

  instance
    has-omega : Has-omega _ 𝕄
    has-omega = Omega-allowed→Has-omega

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
    transparent :
      Bool
    tr tr-Σ :
      M₁.M → M₂.M
    is-order-embedding :
      Is-order-embedding M₁.𝕄 M₂.𝕄 tr
    is-Σ-order-embedding :
      Is-Σ-order-embedding M₁.𝕄 M₂.𝕄 tr tr-Σ
    is-Σ-order-embedding-C :
      Is-Σ-order-embedding-C transparent M₁.C M₂.C tr tr-Σ

  open Is-order-embedding is-order-embedding public
  open Is-Σ-order-embedding is-Σ-order-embedding public
  open Is-Σ-order-embedding-C is-Σ-order-embedding-C public

-- An identity morphism.

id : 𝕄 ⇨ 𝕄
id = λ where
  ._⇨_.transparent →
    false
  ._⇨_.tr →
    idᶠ
  ._⇨_.tr-Σ →
    idᶠ
  ._⇨_.is-order-embedding →
    Is-order-embedding-id
  ._⇨_.is-Σ-order-embedding →
    Is-order-embedding→Is-Σ-order-embedding Is-order-embedding-id
  ._⇨_.is-Σ-order-embedding-C →
    Is-Σ-order-embedding-C-id

-- Composition of morphisms.

_∘_ : 𝕄₂ ⇨ 𝕄₃ → 𝕄₁ ⇨ 𝕄₂ → 𝕄₁ ⇨ 𝕄₃
m₁ ∘ m₂ = λ where
    ._⇨_.transparent →
      M₁.transparent ∨ M₂.transparent
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
    ._⇨_.is-Σ-order-embedding-C →
      Is-Σ-order-embedding-C-∘
        M₁.tr-morphism
        M₂.tr-morphism
        M₁.is-Σ-order-embedding-C
        M₂.is-Σ-order-embedding-C
  where
  module M₁ = _⇨_ m₁
  module M₂ = _⇨_ m₂
