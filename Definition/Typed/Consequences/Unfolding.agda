------------------------------------------------------------------------
-- Typing is preserved by unfolding only under certain conditions
------------------------------------------------------------------------

open import Definition.Typed.Variant
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Unfolding
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant hiding (ℕ≢ne)
open import Definition.Untyped.Whnf M type-variant

open import Definition.Typed R
open import Definition.Typed.Consequences.Equality R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Definition R
open import Definition.Typed.Well-formed R

open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Unit

private
  variable
    n α : Nat
    ∇ ∇′ ∇″ : DCon (Term 0) _
    Γ : Con Term _
    t u A B : Term _
    V : Set a
    φ φ′ : Unfolding _

opaque

  -- If α has type A in ∇, then α has the same type in every
  -- transparentisation of ∇.

  unfold-↦∈ : φ » ∇′ ↜ ∇ → α ↦∷ A ∈ ∇ → α ↦∷ A ∈ ∇′
  unfold-↦∈ ε       ()
  unfold-↦∈ (φ↜ ⁰)  here         = here
  unfold-↦∈ (φ↜ ¹ᵒ) here         = here
  unfold-↦∈ (φ↜ ¹ᵗ) here         = here
  unfold-↦∈ (φ↜ ⁰)  (there α↦∷A) = there (unfold-↦∈ φ↜ α↦∷A)
  unfold-↦∈ (φ↜ ¹ᵒ) (there α↦∷A) = there (unfold-↦∈ φ↜ α↦∷A)
  unfold-↦∈ (φ↜ ¹ᵗ) (there α↦∷A) = there (unfold-↦∈ φ↜ α↦∷A)

opaque

  -- If α has the body t and the type A in ∇, then α has the same body
  -- and type in every transparentisation of ∇.

  unfold-↦∷∈ : φ » ∇′ ↜ ∇ → α ↦ t ∷ A ∈ ∇ → α ↦ t ∷ A ∈ ∇′
  unfold-↦∷∈ ε       ()
  unfold-↦∷∈ (φ↜ ⁰)  here        = here
  unfold-↦∷∈ (φ↜ ¹ᵗ) here        = here
  unfold-↦∷∈ (φ↜ ⁰)  (there α↦t) = there (unfold-↦∷∈ φ↜ α↦t)
  unfold-↦∷∈ (φ↜ ¹ᵒ) (there α↦t) = there (unfold-↦∷∈ φ↜ α↦t)
  unfold-↦∷∈ (φ↜ ¹ᵗ) (there α↦t) = there (unfold-↦∷∈ φ↜ α↦t)

-- The following module is re-exported from the module Transitive
-- below. It uses the assumption that ∇′ is a transparentisation of ∇
-- that is well-formed whenever ∇ is.

module Unconditional (φ↜ : φ » ∇′ ↜ ∇) (»∇′ : » ∇ → » ∇′) where

  opaque mutual

    -- Varible contexts that are well-formed under ∇ are well-formed
    -- under ∇′.

    unfold-⊢′ : ∇ »⊢ Γ → ∇′ »⊢ Γ
    unfold-⊢′ (ε »∇) = ε (»∇′ »∇)
    unfold-⊢′ (∙ ⊢A) = ∙ unfold-⊢ ⊢A

    -- Types that are well-formed under ∇ are well-formed under ∇′.

    unfold-⊢ : ∇ » Γ ⊢ A → ∇′ » Γ ⊢ A
    unfold-⊢ (Uⱼ ⊢Γ) = Uⱼ (unfold-⊢′ ⊢Γ)
    unfold-⊢ (ℕⱼ ⊢Γ) = ℕⱼ (unfold-⊢′ ⊢Γ)
    unfold-⊢ (Emptyⱼ ⊢Γ) = Emptyⱼ (unfold-⊢′ ⊢Γ)
    unfold-⊢ (Unitⱼ ⊢Γ ok) = Unitⱼ (unfold-⊢′ ⊢Γ) ok
    unfold-⊢ (ΠΣⱼ ⊢A ok) = ΠΣⱼ (unfold-⊢ ⊢A) ok
    unfold-⊢ (Idⱼ ⊢A ⊢t ⊢u) =
      Idⱼ (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t) (unfold-⊢∷ ⊢u)
    unfold-⊢ (univ ⊢A) = univ (unfold-⊢∷ ⊢A)

    -- Terms that are well-formed under ∇ are well-formed under ∇′.

    unfold-⊢∷ : ∇ » Γ ⊢ t ∷ A → ∇′ » Γ ⊢ t ∷ A
    unfold-⊢∷ (Uⱼ ⊢Γ) = Uⱼ (unfold-⊢′ ⊢Γ)
    unfold-⊢∷ (ΠΣⱼ ⊢t₁ ⊢t₂ ok) =
      ΠΣⱼ (unfold-⊢∷ ⊢t₁) (unfold-⊢∷ ⊢t₂) ok
    unfold-⊢∷ (ℕⱼ ⊢Γ) = ℕⱼ (unfold-⊢′ ⊢Γ)
    unfold-⊢∷ (Emptyⱼ ⊢Γ) = Emptyⱼ (unfold-⊢′ ⊢Γ)
    unfold-⊢∷ (Unitⱼ ⊢Γ ok) = Unitⱼ (unfold-⊢′ ⊢Γ) ok
    unfold-⊢∷ (conv ⊢t A≡A′) =
      conv (unfold-⊢∷ ⊢t) (unfold-⊢≡ A≡A′)
    unfold-⊢∷ (var ⊢Γ x∈) = var (unfold-⊢′ ⊢Γ) x∈
    unfold-⊢∷ (defn ⊢Γ α↦t A≡A′) =
      defn (unfold-⊢′ ⊢Γ) (unfold-↦∈ φ↜ α↦t) A≡A′
    unfold-⊢∷ (lamⱼ ⊢A ⊢t ok) =
      lamⱼ (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t) ok
    unfold-⊢∷ (⊢t₁ ∘ⱼ ⊢t₂) =
      unfold-⊢∷ ⊢t₁ ∘ⱼ unfold-⊢∷ ⊢t₂
    unfold-⊢∷ (prodⱼ ⊢A ⊢t₁ ⊢t₂ ok) =
      prodⱼ (unfold-⊢ ⊢A)
            (unfold-⊢∷ ⊢t₁)
            (unfold-⊢∷ ⊢t₂)
            ok
    unfold-⊢∷ (fstⱼ ⊢A ⊢t) =
      fstⱼ (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t)
    unfold-⊢∷ (sndⱼ ⊢A ⊢t) =
      sndⱼ (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t)
    unfold-⊢∷ (prodrecⱼ ⊢A ⊢t ⊢t′ ok) =
      prodrecⱼ (unfold-⊢ ⊢A)
              (unfold-⊢∷ ⊢t)
              (unfold-⊢∷ ⊢t′)
              ok
    unfold-⊢∷ (zeroⱼ ⊢Γ) = zeroⱼ (unfold-⊢′ ⊢Γ)
    unfold-⊢∷ (sucⱼ ⊢t) = sucⱼ (unfold-⊢∷ ⊢t)
    unfold-⊢∷ (natrecⱼ ⊢t₀ ⊢tₛ ⊢t) =
      natrecⱼ (unfold-⊢∷ ⊢t₀)
              (unfold-⊢∷ ⊢tₛ)
              (unfold-⊢∷ ⊢t)
    unfold-⊢∷ (emptyrecⱼ ⊢A ⊢t) =
      emptyrecⱼ (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t)
    unfold-⊢∷ (starⱼ ⊢Γ ok) = starⱼ (unfold-⊢′ ⊢Γ) ok
    unfold-⊢∷ (unitrecⱼ ⊢A ⊢t ⊢t′ ok) =
      unitrecⱼ (unfold-⊢ ⊢A)
              (unfold-⊢∷ ⊢t)
              (unfold-⊢∷ ⊢t′)
              ok
    unfold-⊢∷ (Idⱼ ⊢A ⊢t₁ ⊢t₂) =
      Idⱼ (unfold-⊢∷ ⊢A)
          (unfold-⊢∷ ⊢t₁)
          (unfold-⊢∷ ⊢t₂)
    unfold-⊢∷ (rflⱼ ⊢t) = rflⱼ (unfold-⊢∷ ⊢t)
    unfold-⊢∷ (Jⱼ ⊢t ⊢A ⊢tᵣ ⊢t′ ⊢tₚ) =
      Jⱼ (unfold-⊢∷ ⊢t)
        (unfold-⊢ ⊢A)
        (unfold-⊢∷ ⊢tᵣ)
        (unfold-⊢∷ ⊢t′)
        (unfold-⊢∷ ⊢tₚ)
    unfold-⊢∷ (Kⱼ ⊢A ⊢tᵣ ⊢tₚ ok) =
      Kⱼ (unfold-⊢ ⊢A)
        (unfold-⊢∷ ⊢tᵣ)
        (unfold-⊢∷ ⊢tₚ)
        ok
    unfold-⊢∷ ([]-congⱼ ⊢A ⊢t₁ ⊢t₂ ⊢tₚ ok) =
      []-congⱼ (unfold-⊢ ⊢A)
              (unfold-⊢∷ ⊢t₁)
              (unfold-⊢∷ ⊢t₂)
              (unfold-⊢∷ ⊢tₚ) ok

    -- Type equalities that hold under ∇ hold under ∇′.

    unfold-⊢≡ : ∇ » Γ ⊢ A ≡ B → ∇′ » Γ ⊢ A ≡ B
    unfold-⊢≡ (univ A≡A′) = univ (unfold-⊢≡∷ A≡A′)
    unfold-⊢≡ (refl ⊢A) = refl (unfold-⊢ ⊢A)
    unfold-⊢≡ (sym A≡A′) = sym (unfold-⊢≡ A≡A′)
    unfold-⊢≡ (trans A≡A′ A′≡A″) =
      trans (unfold-⊢≡ A≡A′) (unfold-⊢≡ A′≡A″)
    unfold-⊢≡ (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) =
      ΠΣ-cong (unfold-⊢≡ A₁≡A₂) (unfold-⊢≡ B₁≡B₂) ok
    unfold-⊢≡ (Id-cong A≡A′ t₁≡t₂ u₁≡u₂) =
      Id-cong (unfold-⊢≡ A≡A′)
              (unfold-⊢≡∷ t₁≡t₂)
              (unfold-⊢≡∷ u₁≡u₂)

    -- Term equalities that hold under ∇ hold under ∇′.

    unfold-⊢≡∷ : ∇ » Γ ⊢ t ≡ u ∷ A → ∇′ » Γ ⊢ t ≡ u ∷ A
    unfold-⊢≡∷ (refl ⊢t) = refl (unfold-⊢∷ ⊢t)
    unfold-⊢≡∷ (sym ⊢A t≡t′) =
      sym (unfold-⊢ ⊢A) (unfold-⊢≡∷ t≡t′)
    unfold-⊢≡∷ (trans t≡t′ t′≡t″) =
      trans (unfold-⊢≡∷ t≡t′) (unfold-⊢≡∷ t′≡t″)
    unfold-⊢≡∷ (conv t≡t′ A≡A′) =
      conv (unfold-⊢≡∷ t≡t′) (unfold-⊢≡ A≡A′)
    unfold-⊢≡∷ (δ-red ⊢Γ α↦t A≡A′ t≡t′) =
      δ-red (unfold-⊢′ ⊢Γ) (unfold-↦∷∈ φ↜ α↦t) A≡A′ t≡t′
    unfold-⊢≡∷ (ΠΣ-cong t₁≡t₂ u₁≡u₂ ok) =
      ΠΣ-cong (unfold-⊢≡∷ t₁≡t₂) (unfold-⊢≡∷ u₁≡u₂) ok
    unfold-⊢≡∷ (app-cong t₁≡t₂ u₁≡u₂) =
      app-cong (unfold-⊢≡∷ t₁≡t₂) (unfold-⊢≡∷ u₁≡u₂)
    unfold-⊢≡∷ (β-red ⊢A ⊢t ⊢x eq ok) =
      β-red (unfold-⊢ ⊢A)
            (unfold-⊢∷ ⊢t)
            (unfold-⊢∷ ⊢x)
            eq ok
    unfold-⊢≡∷ (η-eq ⊢A ⊢t ⊢t′ t≡t′ ok) =
      η-eq (unfold-⊢ ⊢A)
          (unfold-⊢∷ ⊢t)
          (unfold-⊢∷ ⊢t′)
          (unfold-⊢≡∷ t≡t′)
          ok
    unfold-⊢≡∷ (fst-cong ⊢A t≡t′) =
      fst-cong (unfold-⊢ ⊢A) (unfold-⊢≡∷ t≡t′)
    unfold-⊢≡∷ (snd-cong ⊢A t≡t′) =
      snd-cong (unfold-⊢ ⊢A) (unfold-⊢≡∷ t≡t′)
    unfold-⊢≡∷ (Σ-β₁ ⊢A ⊢t ⊢t′ eq ok) =
      Σ-β₁ (unfold-⊢ ⊢A)
          (unfold-⊢∷ ⊢t)
          (unfold-⊢∷ ⊢t′)
          eq ok
    unfold-⊢≡∷ (Σ-β₂ ⊢A ⊢t ⊢t′ eq ok) =
      Σ-β₂ (unfold-⊢ ⊢A)
          (unfold-⊢∷ ⊢t)
          (unfold-⊢∷ ⊢t′)
          eq ok
    unfold-⊢≡∷ (Σ-η ⊢A ⊢t ⊢t′ fst≡ snd≡ ok) =
      Σ-η (unfold-⊢ ⊢A)
          (unfold-⊢∷ ⊢t)
          (unfold-⊢∷ ⊢t′)
          (unfold-⊢≡∷ fst≡)
          (unfold-⊢≡∷ snd≡)
          ok
    unfold-⊢≡∷ (prod-cong ⊢A t₁≡t₂ u₁≡u₂ ok) =
      prod-cong (unfold-⊢ ⊢A)
                (unfold-⊢≡∷ t₁≡t₂)
                (unfold-⊢≡∷ u₁≡u₂)
                ok
    unfold-⊢≡∷ (prodrec-cong A≡A′ t₁≡t₂ u₁≡u₂ ok) =
      prodrec-cong (unfold-⊢≡ A≡A′)
                  (unfold-⊢≡∷ t₁≡t₂)
                  (unfold-⊢≡∷ u₁≡u₂)
                  ok
    unfold-⊢≡∷ (prodrec-β ⊢A ⊢t₁ ⊢t₂ ⊢tᵣ eq ok) =
      prodrec-β (unfold-⊢ ⊢A)
                (unfold-⊢∷ ⊢t₁)
                (unfold-⊢∷ ⊢t₂)
                (unfold-⊢∷ ⊢tᵣ)
                eq ok
    unfold-⊢≡∷ (suc-cong t≡t′) =
      suc-cong (unfold-⊢≡∷ t≡t′)
    unfold-⊢≡∷ (natrec-cong A≡A′ 0≡ s≡ t≡t′) =
      natrec-cong (unfold-⊢≡ A≡A′)
                  (unfold-⊢≡∷ 0≡)
                  (unfold-⊢≡∷ s≡)
                  (unfold-⊢≡∷ t≡t′)
    unfold-⊢≡∷ (natrec-zero ⊢t₀ ⊢tₛ) =
      natrec-zero (unfold-⊢∷ ⊢t₀) (unfold-⊢∷ ⊢tₛ)
    unfold-⊢≡∷ (natrec-suc ⊢t₀ ⊢tₛ ⊢t) =
      natrec-suc (unfold-⊢∷ ⊢t₀)
                (unfold-⊢∷ ⊢tₛ)
                (unfold-⊢∷ ⊢t)
    unfold-⊢≡∷ (emptyrec-cong A≡A′ t≡t′) =
      emptyrec-cong (unfold-⊢≡ A≡A′) (unfold-⊢≡∷ t≡t′)
    unfold-⊢≡∷ (unitrec-cong A≡A′ t≡t′ r≡ ok no-η) =
      unitrec-cong (unfold-⊢≡ A≡A′)
                  (unfold-⊢≡∷ t≡t′)
                  (unfold-⊢≡∷ r≡)
                  ok no-η
    unfold-⊢≡∷ (unitrec-β ⊢A ⊢t ok no-η) =
      unitrec-β (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t) ok no-η
    unfold-⊢≡∷ (unitrec-β-η ⊢A ⊢t ⊢tᵣ ok η) =
      unitrec-β-η (unfold-⊢ ⊢A)
                  (unfold-⊢∷ ⊢t)
                  (unfold-⊢∷ ⊢tᵣ)
                  ok η
    unfold-⊢≡∷ (η-unit ⊢t ⊢t′ η) =
      η-unit (unfold-⊢∷ ⊢t) (unfold-⊢∷ ⊢t′) η
    unfold-⊢≡∷ (Id-cong A≡A′ t₁≡t₂ u₁≡u₂) =
      Id-cong (unfold-⊢≡∷ A≡A′)
              (unfold-⊢≡∷ t₁≡t₂)
              (unfold-⊢≡∷ u₁≡u₂)
    unfold-⊢≡∷ (J-cong A≡A′ ⊢t t≡t′ B₁≡B₂ r≡ x≡ p≡) =
      J-cong (unfold-⊢≡ A≡A′)
            (unfold-⊢∷ ⊢t)
            (unfold-⊢≡∷ t≡t′)
            (unfold-⊢≡ B₁≡B₂)
            (unfold-⊢≡∷ r≡)
            (unfold-⊢≡∷ x≡)
            (unfold-⊢≡∷ p≡)
    unfold-⊢≡∷ (K-cong A≡A′ t≡t′ B₁≡B₂ r≡ p≡ ok) =
      K-cong (unfold-⊢≡ A≡A′)
            (unfold-⊢≡∷ t≡t′)
            (unfold-⊢≡ B₁≡B₂)
            (unfold-⊢≡∷ r≡)
            (unfold-⊢≡∷ p≡)
            ok
    unfold-⊢≡∷ ([]-cong-cong A≡A′ t₁≡t₂ u₁≡u₂ p≡p′ ok) =
      []-cong-cong (unfold-⊢≡ A≡A′)
                  (unfold-⊢≡∷ t₁≡t₂)
                  (unfold-⊢≡∷ u₁≡u₂)
                  (unfold-⊢≡∷ p≡p′) ok
    unfold-⊢≡∷ (J-β ⊢t ⊢A ⊢tᵣ eq) =
      J-β (unfold-⊢∷ ⊢t)
          (unfold-⊢ ⊢A)
          (unfold-⊢∷ ⊢tᵣ)
          eq
    unfold-⊢≡∷ (K-β ⊢A ⊢t ok) =
      K-β (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t) ok
    unfold-⊢≡∷ ([]-cong-β ⊢t eq ok) =
      []-cong-β (unfold-⊢∷ ⊢t) eq ok
    unfold-⊢≡∷ (equality-reflection ok ⊢Id ⊢t) =
      equality-reflection ok (unfold-⊢ ⊢Id) (unfold-⊢∷ ⊢t)

  opaque

    -- Reductions that hold under ∇ hold under ∇′.

    unfold-⇒∷ : ∇ » Γ ⊢ t ⇒ u ∷ A → ∇′ » Γ ⊢ t ⇒ u ∷ A
    unfold-⇒∷ (conv t⇒t′ A≡A′) =
      conv (unfold-⇒∷ t⇒t′) (unfold-⊢≡ A≡A′)
    unfold-⇒∷ (δ-red ⊢Γ α↦t A≡A′ T≡T′) =
      δ-red (unfold-⊢′ ⊢Γ) (unfold-↦∷∈ φ↜ α↦t) A≡A′ T≡T′
    unfold-⇒∷ (app-subst t⇒t′ ⊢a) =
      app-subst (unfold-⇒∷ t⇒t′) (unfold-⊢∷ ⊢a)
    unfold-⇒∷ (β-red ⊢A ⊢t ⊢x eq ok) =
      β-red (unfold-⊢ ⊢A)
            (unfold-⊢∷ ⊢t)
            (unfold-⊢∷ ⊢x)
            eq ok
    unfold-⇒∷ (fst-subst ⊢A t⇒t′) =
      fst-subst (unfold-⊢ ⊢A) (unfold-⇒∷ t⇒t′)
    unfold-⇒∷ (snd-subst ⊢A t⇒t′) =
      snd-subst (unfold-⊢ ⊢A) (unfold-⇒∷ t⇒t′)
    unfold-⇒∷ (Σ-β₁ ⊢A ⊢t ⊢t′ eq ok) =
      Σ-β₁ (unfold-⊢ ⊢A)
          (unfold-⊢∷ ⊢t)
          (unfold-⊢∷ ⊢t′)
          eq ok
    unfold-⇒∷ (Σ-β₂ ⊢A ⊢t ⊢t′ eq ok) =
      Σ-β₂ (unfold-⊢ ⊢A)
          (unfold-⊢∷ ⊢t)
          (unfold-⊢∷ ⊢t′)
          eq ok
    unfold-⇒∷ (prodrec-subst ⊢A ⊢a t⇒t′ ok) =
      prodrec-subst (unfold-⊢ ⊢A)
                    (unfold-⊢∷ ⊢a)
                    (unfold-⇒∷ t⇒t′)
                    ok
    unfold-⇒∷ (prodrec-β ⊢A ⊢t ⊢t₂ ⊢tᵣ eq ok) =
      prodrec-β (unfold-⊢ ⊢A)
                (unfold-⊢∷ ⊢t)
                (unfold-⊢∷ ⊢t₂)
                (unfold-⊢∷ ⊢tᵣ)
                eq ok
    unfold-⇒∷ (natrec-subst ⊢t₀ ⊢tₛ t⇒t′) =
      natrec-subst (unfold-⊢∷ ⊢t₀)
                  (unfold-⊢∷ ⊢tₛ)
                  (unfold-⇒∷ t⇒t′)
    unfold-⇒∷ (natrec-zero ⊢t₀ ⊢tₛ) =
      natrec-zero (unfold-⊢∷ ⊢t₀) (unfold-⊢∷ ⊢tₛ)
    unfold-⇒∷ (natrec-suc ⊢t₀ ⊢tₛ ⊢t) =
      natrec-suc (unfold-⊢∷ ⊢t₀)
                (unfold-⊢∷ ⊢tₛ)
                (unfold-⊢∷ ⊢t)
    unfold-⇒∷ (emptyrec-subst ⊢A t⇒t′) =
      emptyrec-subst (unfold-⊢ ⊢A) (unfold-⇒∷ t⇒t′)
    unfold-⇒∷ (unitrec-subst ⊢A ⊢a t⇒t′ ok no-η) =
      unitrec-subst (unfold-⊢ ⊢A)
                    (unfold-⊢∷ ⊢a)
                    (unfold-⇒∷ t⇒t′)
                    ok no-η
    unfold-⇒∷ (unitrec-β ⊢A ⊢t ok no-η) =
      unitrec-β (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t) ok no-η
    unfold-⇒∷ (unitrec-β-η ⊢A ⊢t ⊢tᵣ ok η) =
      unitrec-β-η (unfold-⊢ ⊢A)
                  (unfold-⊢∷ ⊢t)
                  (unfold-⊢∷ ⊢tᵣ)
                  ok η
    unfold-⇒∷ (J-subst ⊢t ⊢A ⊢r ⊢p w⇒w′) =
      J-subst (unfold-⊢∷ ⊢t)
              (unfold-⊢ ⊢A)
              (unfold-⊢∷ ⊢r)
              (unfold-⊢∷ ⊢p)
              (unfold-⇒∷ w⇒w′)
    unfold-⇒∷ (K-subst ⊢A ⊢r t⇒t′ ok) =
      K-subst (unfold-⊢ ⊢A)
              (unfold-⊢∷ ⊢r)
              (unfold-⇒∷ t⇒t′)
              ok
    unfold-⇒∷ ([]-cong-subst ⊢A ⊢a ⊢a′ t⇒t′ ok) =
      []-cong-subst (unfold-⊢ ⊢A)
                    (unfold-⊢∷ ⊢a)
                    (unfold-⊢∷ ⊢a′)
                    (unfold-⇒∷ t⇒t′)
                    ok
    unfold-⇒∷ (J-β ⊢t ⊢t′ t≡t′ ⊢A A≡ ⊢tᵣ) =
      J-β (unfold-⊢∷ ⊢t)
          (unfold-⊢∷ ⊢t′)
          (unfold-⊢≡∷ t≡t′)
          (unfold-⊢ ⊢A)
          (unfold-⊢≡ A≡)
          (unfold-⊢∷ ⊢tᵣ)
    unfold-⇒∷ (K-β ⊢A ⊢t ok) =
      K-β (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t) ok
    unfold-⇒∷ ([]-cong-β ⊢A ⊢t ⊢t′ t≡t′ ok) =
      []-cong-β (unfold-⊢ ⊢A)
                (unfold-⊢∷ ⊢t)
                (unfold-⊢∷ ⊢t′)
                (unfold-⊢≡∷ t≡t′)
                ok

  opaque

    -- Reductions that hold under ∇ hold under ∇′.

    unfold-⇒ : ∇ » Γ ⊢ A ⇒ B → ∇′ » Γ ⊢ A ⇒ B
    unfold-⇒ (univ A⇒B) = univ (unfold-⇒∷ A⇒B)

  opaque

    -- Reductions that hold under ∇ hold under ∇′.

    unfold-⇒* : ∇ » Γ ⊢ A ⇒* B → ∇′ » Γ ⊢ A ⇒* B
    unfold-⇒* (id ⊢A)      = id (unfold-⊢ ⊢A)
    unfold-⇒* (A⇒X ⇨ X⇒*B) = unfold-⇒ A⇒X ⇨ unfold-⇒* X⇒*B

  opaque

    -- Reductions that hold under ∇ hold under ∇′.

    unfold-⇒*∷ : ∇ » Γ ⊢ t ⇒* u ∷ A → ∇′ » Γ ⊢ t ⇒* u ∷ A
    unfold-⇒*∷ (id ⊢t)      = id (unfold-⊢∷ ⊢t)
    unfold-⇒*∷ (t⇒x ⇨ x⇒*u) = unfold-⇒∷ t⇒x ⇨ unfold-⇒*∷ x⇒*u

module Explicit (mode-eq : unfolding-mode PE.≡ explicit) where

  private opaque

    _! : φ » ∇′ ↜ ∇ → {φ′ : Unfolding n} → φ ⊔ᵒᵗ φ′ » ∇′ ↜ ∇
    φ↜ ! with unfolding-mode
    ...     | explicit   = φ↜
    ...     | transitive = case mode-eq of λ ()

  opaque

    no-unfold-» :
      Opacity-allowed →
      ∃₃ λ (∇ ∇′ : DCon (Term 0) 2) (φ : Unfolding 2) →
           φ » ∇′ ↜ ∇ × » ∇ × ¬ » ∇′
    no-unfold-» ok =
      let ∇₁ = ε ∙⟨ opa ε ⟩[ ℕ ∷ U 0 ]
          ∇ = ∇₁ ∙⟨ opa (ε ¹) ⟩[ zero ∷ defn 0 ]
          ∇′ = ∇₁ ∙⟨ tra ⟩[ zero ∷ defn 0 ]
          ∇₁⊢ε = ε ∙ᵒ⟨ ok , ε ⟩[ ℕⱼ εε ∷ Uⱼ εε ]
          ∇₁ᵗ⊢ε = ε ∙ᵗ[ ℕⱼ εε ]
          »∇ = ∙ᵒ⟨ ok , ε ! ¹ᵒ ⟩[
            conv (zeroⱼ ∇₁ᵗ⊢ε) (sym (univ (δ-red ∇₁ᵗ⊢ε here PE.refl PE.refl))) ∷
            univ (defn ∇₁⊢ε here PE.refl) ]
          not »∇′ = ℕ≢ne {V = Lift _ ⊤} ⦃ ε ⦄
                         (defn (there here))
                         (sym (inversion-zero (wf-↦∷∈ here »∇′)))
      in  ∇ , ∇′ , ε ⁰ ¹ , (ε ⁰ !) ¹ᵒ , »∇ , not

module Transitive (mode-eq : unfolding-mode PE.≡ transitive) where

  opaque

    comm-⊔ᵒᵗ : (φ φ′ : Unfolding n) → φ ⊔ᵒᵗ φ′ PE.≡ φ′ ⊔ᵒᵗ φ
    comm-⊔ᵒᵗ φ φ′ = begin
      φ ⊔ᵒᵗ φ′  ≡⟨ ⊔ᵒᵗ≡⊔ᵒ mode-eq ⟩
      φ ⊔ᵒ φ′   ≡⟨ comm-⊔ᵒ φ φ′ ⟩
      φ′ ⊔ᵒ φ   ≡˘⟨ ⊔ᵒᵗ≡⊔ᵒ mode-eq ⟩
      φ′ ⊔ᵒᵗ φ  ∎

  private opaque

    a1[23] : (φ φ′ φ″ : Unfolding n) → φ ⊔ᵒᵗ (φ′ ⊔ᵒᵗ φ″) PE.≡ (φ ⊔ᵒ φ′) ⊔ᵒᵗ φ″
    a1[23] φ φ′ φ″ = begin
      φ ⊔ᵒᵗ (φ′ ⊔ᵒᵗ φ″)  ≡⟨ assoc-⊔ᵒᵗ φ φ′ φ″ ⟩
      (φ ⊔ᵒᵗ φ′) ⊔ᵒᵗ φ″  ≡⟨ PE.cong (_⊔ᵒᵗ φ″) (⊔ᵒᵗ≡⊔ᵒ mode-eq) ⟩
      (φ ⊔ᵒ φ′) ⊔ᵒᵗ φ″   ∎

  private opaque

    a[13]2 : (φ φ′ φ″ : Unfolding n) → (φ ⊔ᵒᵗ φ″) ⊔ᵒᵗ φ′ PE.≡ (φ ⊔ᵒ φ′) ⊔ᵒᵗ φ″
    a[13]2 φ φ′ φ″ = begin
      (φ ⊔ᵒᵗ φ″) ⊔ᵒᵗ φ′  ≡˘⟨ assoc-⊔ᵒᵗ φ φ″ φ′ ⟩
      φ ⊔ᵒᵗ (φ″ ⊔ᵒᵗ φ′)  ≡⟨ PE.cong (φ ⊔ᵒᵗ_) (comm-⊔ᵒᵗ φ″ φ′) ⟩
      φ ⊔ᵒᵗ (φ′ ⊔ᵒᵗ φ″)  ≡⟨ assoc-⊔ᵒᵗ φ φ′ φ″ ⟩
      (φ ⊔ᵒᵗ φ′) ⊔ᵒᵗ φ″  ≡⟨ PE.cong (_⊔ᵒᵗ φ″) (⊔ᵒᵗ≡⊔ᵒ mode-eq) ⟩
      (φ ⊔ᵒ φ′) ⊔ᵒᵗ φ″   ∎

  opaque

    join-»↜ : φ » ∇′ ↜ ∇ → φ′ » ∇″ ↜ ∇′ → φ ⊔ᵒᵗ φ′ » ∇″ ↜ ∇
    join-»↜ φ↜ φ′↜ =
      PE.subst (_» _ ↜ _) (PE.sym (⊔ᵒᵗ≡⊔ᵒ mode-eq)) (join′ φ↜ φ′↜)
      where
      join′ : φ » ∇′ ↜ ∇ → φ′ » ∇″ ↜ ∇′ → φ ⊔ᵒ φ′ » ∇″ ↜ ∇
      join′ ε ε = ε
      join′ (φ↜ ⁰) (φ′↜ ⁰) = join′ φ↜ φ′↜ ⁰
      join′ (φ↜ ⁰) (φ′↜ ¹ᵒ) =
        PE.subst (_» _ ↜ _) (a1[23] _ _ _) (join-»↜ φ↜ φ′↜) ¹ᵒ
      join′ (φ↜ ⁰) (φ′↜ ¹ᵗ) = join′ φ↜ φ′↜ ¹ᵗ
      join′ (φ↜ ¹ᵒ) (φ′↜ ⁰) =
        PE.subst (_» _ ↜ _) (a[13]2 _ _ _) (join-»↜ φ↜ φ′↜) ¹ᵒ
      join′ (φ↜ ¹ᵒ) (φ′↜ ¹ᵗ) =
        PE.subst (_» _ ↜ _) (a[13]2 _ _ _) (join-»↜ φ↜ φ′↜) ¹ᵒ
      join′ (φ↜ ¹ᵗ) (φ′↜ ⁰) = join′ φ↜ φ′↜ ¹ᵗ
      join′ (φ↜ ¹ᵗ) (φ′↜ ¹ᵗ) = join′ φ↜ φ′↜ ¹ᵗ

  opaque

    unjoin-»↜ : φ′ ⊔ᵒᵗ φ » ∇″ ↜ ∇ → φ » ∇′ ↜ ∇ → φ′ » ∇″ ↜ ∇′
    unjoin-»↜ φ′φ↜ φ↜ =
      unjoin′ (PE.subst (_» _ ↜ _) (⊔ᵒᵗ≡⊔ᵒ mode-eq) φ′φ↜) φ↜
      where
      unjoin′ : φ′ ⊔ᵒ φ » ∇″ ↜ ∇ → φ » ∇′ ↜ ∇ → φ′ » ∇″ ↜ ∇′
      unjoin′ {φ′ = ε} {φ = ε} ε ε = ε
      unjoin′ {φ′ = φ′ ⁰} {φ = φ ⁰} (φ′φ↜ ⁰) (φ↜ ⁰) = unjoin′ φ′φ↜ φ↜ ⁰
      unjoin′ {φ′ = φ′ ¹} {φ = φ ⁰} (φ′φ↜ ¹ᵒ) (φ↜ ⁰) =
        unjoin-»↜ (PE.subst (_» _ ↜ _) (PE.sym (a[13]2 _ _ _)) φ′φ↜) φ↜ ¹ᵒ
      unjoin′ {φ′ = φ′ ¹} {φ = φ ⁰} (φ′φ↜ ¹ᵗ) (φ↜ ⁰) = unjoin′ φ′φ↜ φ↜ ¹ᵗ
      unjoin′ {φ′ = φ′ ⁰} {φ = φ ¹} (φ′φ↜ ¹ᵒ) (φ↜ ¹ᵒ) =
        unjoin-»↜ (PE.subst (_» _ ↜ _) (PE.sym (a1[23] _ _ _)) φ′φ↜) φ↜ ⁰
      unjoin′ {φ′ = φ′ ⁰} {φ = φ ¹} (φ′φ↜ ¹ᵗ) (φ↜ ¹ᵗ) = unjoin′ φ′φ↜ φ↜ ⁰
      unjoin′ {φ′ = φ′ ¹} {φ = φ ¹} (φ′φ↜ ¹ᵒ) (φ↜ ¹ᵒ) =
        unjoin-»↜ (PE.subst (_» _ ↜ _) (PE.sym (a1[23] _ _ _)) φ′φ↜) φ↜ ¹ᵗ
      unjoin′ {φ′ = φ′ ¹} {φ = φ ¹} (φ′φ↜ ¹ᵗ) (φ↜ ¹ᵗ) = unjoin′ φ′φ↜ φ↜ ¹ᵗ

  -- If ∇′ is a transparentisation of the well-formed definition
  -- context ∇, then ∇′ is well-formed.

  unfold-» : φ » ∇′ ↜ ∇ → » ∇ → » ∇′

  -- Other preservation lemmas related to transparentisation.

  module _ (φ» : φ » ∇′ ↜ ∇) where
    open Unconditional φ» (unfold-» φ») public

  unfold-» ε       ε                         = ε
  unfold-» (φ↜ ⁰)  ∙ᵒ⟨ ok , φ′↜ ⟩[ ⊢t ∷ ⊢A ] =
    let _ , φ″↜ = total-»↜ _ _
    in  ∙ᵒ⟨ ok , φ″↜ ⟩[ unfold-⊢∷ (unjoin-»↜ (join-»↜ φ↜ φ″↜) φ′↜) ⊢t
                      ∷ unfold-⊢ φ↜ ⊢A
                      ]
  unfold-» (φ↜ ¹ᵒ) ∙ᵒ⟨ ok , φ′↜ ⟩[ ⊢t ∷ ⊢A ] = ∙ᵗ[ unfold-⊢∷ (unjoin-»↜ φ↜ φ′↜) ⊢t ]
  unfold-» (φ↜ ⁰)              ∙ᵗ[ ⊢t      ] = ∙ᵗ[ unfold-⊢∷ φ↜ ⊢t ]
  unfold-» (φ↜ ¹ᵗ)             ∙ᵗ[ ⊢t      ] = ∙ᵗ[ unfold-⊢∷ φ↜ ⊢t ]
