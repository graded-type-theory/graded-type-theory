------------------------------------------------------------------------
-- Embedding of the logical relation into higher type levels
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.MaybeEmb
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (_∷_)
open import Definition.LogicalRelation R

open import Tools.Nat using (Nat)

private
  variable
    n       : Nat
    Γ       : Con Term n
    A B t u : Term n
    l l′    : TypeLevel

-- Any level can be embedded into the highest level.
maybeEmb : ∀ {l A}
         → Γ ⊩⟨ l ⟩ A
         → Γ ⊩⟨ ¹ ⟩ A
maybeEmb {l = ⁰} [A] = emb 0<1 [A]
maybeEmb {l = ¹} [A] = [A]

-- The lowest level can be embedded in any level.
maybeEmb′ : ∀ {l A}
          → Γ ⊩⟨ ⁰ ⟩ A
          → Γ ⊩⟨ l ⟩ A
maybeEmb′ {l = ⁰} [A] = [A]
maybeEmb′ {l = ¹} [A] = emb 0<1 [A]

opaque

  -- A variant of emb.

  emb-≤-⊩ : l ≤ l′ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l′ ⟩ A
  emb-≤-⊩ refl      ⊩A = ⊩A
  emb-≤-⊩ (emb 0<1) ⊩A = emb 0<1 ⊩A

opaque
  unfolding emb-≤-⊩

  -- A cast lemma related to emb-≤-⊩.

  emb-≤-≡ :
    {l≤l′ : l ≤ l′} {⊩A : Γ ⊩⟨ l ⟩ A} →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A →
    Γ ⊩⟨ l′ ⟩ A ≡ B / emb-≤-⊩ l≤l′ ⊩A
  emb-≤-≡ {l≤l′ = refl}    A≡B = A≡B
  emb-≤-≡ {l≤l′ = emb 0<1} A≡B = A≡B

opaque
  unfolding emb-≤-⊩

  -- A cast lemma related to emb-≤-⊩.

  emb-≤-∷ :
    {l≤l′ : l ≤ l′} {⊩A : Γ ⊩⟨ l ⟩ A} →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l′ ⟩ t ∷ A / emb-≤-⊩ l≤l′ ⊩A
  emb-≤-∷ {l≤l′ = refl}    ⊩t = ⊩t
  emb-≤-∷ {l≤l′ = emb 0<1} ⊩t = ⊩t

opaque
  unfolding emb-≤-⊩

  -- A cast lemma related to emb-≤-⊩.

  emb-≤-≡∷ :
    {l≤l′ : l ≤ l′} {⊩A : Γ ⊩⟨ l ⟩ A} →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / emb-≤-⊩ l≤l′ ⊩A
  emb-≤-≡∷ {l≤l′ = refl}    t≡u = t≡u
  emb-≤-≡∷ {l≤l′ = emb 0<1} t≡u = t≡u
