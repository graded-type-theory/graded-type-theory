------------------------------------------------------------------------
-- A translation that turns on equality reflection and leaves
-- everything else unchanged, except that opacity is disallowed and
-- definitions are made transparent
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.With-equality-reflection
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Tools.Bool
open import Tools.Function
import Tools.PropositionalEquality as PE

import Definition.Typed
open Definition.Typed R
import Definition.Typed.QuantityTranslation
import Definition.Typed.Substitution
open Definition.Typed.Substitution R

open import Definition.Untyped M
open import Definition.Untyped.QuantityTranslation.Identity M true as Id

open Id.Transparent _

open import Graded.Modality.Morphism
open import Graded.Modality.Morphism.Type-restrictions
open import Graded.Modality.Morphism.Type-restrictions.Examples
import Graded.Mode.Instances.Trivial 𝕄 as Triv
open import Graded.Restrictions 𝕄 Triv.trivial

private variable
  ∇       : DCon _ _
  Γ Δ     : Con _ _
  A B t u : Term _
  l l₁ l₂ : Lvl _
  σ σ₁ σ₂ : Subst _ _

-- The type restrictions used for the target.

With-refl : Type-restrictions 𝕄
With-refl = with-equality-reflection R

-- Some definitions are re-exported.

module With-refl where

  open Definition.Typed              With-refl public
  open Definition.Typed.Substitution With-refl public

private

  module QT = Definition.Typed.QuantityTranslation
    R With-refl true idᶠ idᶠ
    (Is-order-embedding.tr-morphism Is-order-embedding-id)
    (Is-morphism→Is-Σ-morphism
       (Is-order-embedding.tr-morphism Is-order-embedding-id))
    (Are-preserving-type-restrictions-with-equality-reflectionʳ
       {trp = false} {𝐌₂ = Triv.trivial}
       Are-preserving-type-restrictions-id)

opaque

  -- Preservation of »_.

  tr-» : » ∇ → With-refl.» glassify ∇
  tr-» = PE.subst With-refl.»_ tr-DCon-glassify ∘→ QT.tr-»

opaque

  -- Preservation of _»⊢_.

  tr-»⊢ : ∇ »⊢ Γ → glassify ∇ With-refl.»⊢ Γ
  tr-»⊢ = PE.subst With-refl.⊢_ tr-Cons-glassify ∘→ QT.tr-⊢

opaque

  -- Preservation of _⊢_.

  tr-⊢ : ∇ » Γ ⊢ A → glassify ∇ » Γ With-refl.⊢ A
  tr-⊢ = PE.subst₂ With-refl._⊢_ tr-Cons-glassify tr-Term-id ∘→ QT.tr-⊢′

opaque

  -- Preservation of _⊢_∷_.

  tr-⊢∷ : ∇ » Γ ⊢ t ∷ A → glassify ∇ » Γ With-refl.⊢ t ∷ A
  tr-⊢∷ =
    PE.subst₃ With-refl._⊢_∷_ tr-Cons-glassify tr-Term-id tr-Term-id ∘→
    QT.tr-⊢∷

opaque

  -- Preservation of _⊢_∷Level.

  tr-⊢∷L : ∇ » Γ ⊢ l ∷Level → glassify ∇ » Γ With-refl.⊢ l ∷Level
  tr-⊢∷L =
    PE.subst₂ With-refl._⊢_∷Level tr-Cons-glassify tr-Term-id ∘→
    QT.tr-⊢∷L

opaque

  -- Preservation of _⊢_≡_.

  tr-⊢≡ : ∇ » Γ ⊢ A ≡ B → glassify ∇ » Γ With-refl.⊢ A ≡ B
  tr-⊢≡ =
    PE.subst₃ With-refl._⊢_≡_ tr-Cons-glassify tr-Term-id tr-Term-id ∘→
    QT.tr-⊢≡

opaque

  -- Preservation of _⊢_≡_∷_.

  tr-⊢≡∷ : ∇ » Γ ⊢ t ≡ u ∷ A → glassify ∇ » Γ With-refl.⊢ t ≡ u ∷ A
  tr-⊢≡∷ =
    PE.subst₄ With-refl._⊢_≡_∷_ tr-Cons-glassify tr-Term-id tr-Term-id
      tr-Term-id ∘→
    QT.tr-⊢≡∷

opaque

  -- Preservation of _⊢_≡_∷Level.

  tr-⊢≡∷L :
    ∇ » Γ ⊢ l₁ ≡ l₂ ∷Level →
    glassify ∇ » Γ With-refl.⊢ l₁ ≡ l₂ ∷Level
  tr-⊢≡∷L =
    PE.subst₃ With-refl._⊢_≡_∷Level tr-Cons-glassify tr-Term-id
      tr-Term-id ∘→
    QT.tr-⊢≡∷L

opaque

  -- Preservation of _⊢ˢʷ_∷_.

  tr-⊢ˢʷ∷ : ∇ » Γ ⊢ˢʷ σ ∷ Δ → glassify ∇ » Γ With-refl.⊢ˢʷ σ ∷ Δ
  tr-⊢ˢʷ∷ {σ} =
    With-refl.cast-⊢ˢʷ∷ (λ _ → tr-Subst-id σ) ∘→
    PE.subst₃ With-refl._⊢ˢʷ_∷_ tr-Cons-glassify PE.refl tr-Con-id ∘→
    QT.tr-⊢ˢʷ∷

opaque

  -- Preservation of _⊢ˢʷ_≡_∷_.

  tr-⊢ˢʷ≡∷ :
    ∇ » Γ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ → glassify ∇ » Γ With-refl.⊢ˢʷ σ₁ ≡ σ₂ ∷ Δ
  tr-⊢ˢʷ≡∷ {σ₁} {σ₂} =
    With-refl.cast-⊢ˢʷ≡∷ (λ _ → tr-Subst-id σ₁)
      (λ _ → tr-Subst-id σ₂) ∘→
    PE.subst₄ With-refl._⊢ˢʷ_≡_∷_ tr-Cons-glassify PE.refl PE.refl
      tr-Con-id ∘→
    QT.tr-⊢ˢʷ≡∷

opaque

  -- Preservation of _⊢_⇒_∷_.

  tr-⊢⇒∷ : ∇ » Γ ⊢ t ⇒ u ∷ A → glassify ∇ » Γ With-refl.⊢ t ⇒ u ∷ A
  tr-⊢⇒∷ =
    PE.subst₄ With-refl._⊢_⇒_∷_ tr-Cons-glassify tr-Term-id tr-Term-id
      tr-Term-id ∘→
    QT.tr-⊢⇒∷ idᶠ

opaque

  -- Preservation of _⊢_⇒_.

  tr-⊢⇒ : ∇ » Γ ⊢ A ⇒ B → glassify ∇ » Γ With-refl.⊢ A ⇒ B
  tr-⊢⇒ =
    PE.subst₃ With-refl._⊢_⇒_ tr-Cons-glassify tr-Term-id tr-Term-id ∘→
    QT.tr-⊢⇒ idᶠ

opaque

  -- Preservation of _⊢_⇒*_∷_.

  tr-⊢⇒*∷ : ∇ » Γ ⊢ t ⇒* u ∷ A → glassify ∇ » Γ With-refl.⊢ t ⇒* u ∷ A
  tr-⊢⇒*∷ =
    PE.subst₄ With-refl._⊢_⇒*_∷_ tr-Cons-glassify tr-Term-id tr-Term-id
      tr-Term-id ∘→
    QT.tr-⊢⇒*∷ idᶠ

opaque

  -- Preservation of _⊢_⇒*_.

  tr-⊢⇒* : ∇ » Γ ⊢ A ⇒* B → glassify ∇ » Γ With-refl.⊢ A ⇒* B
  tr-⊢⇒* =
    PE.subst₃ With-refl._⊢_⇒*_ tr-Cons-glassify tr-Term-id tr-Term-id ∘→
    QT.tr-⊢⇒* idᶠ
