------------------------------------------------------------------------
-- Some properties related to transparentisation
------------------------------------------------------------------------

open import Definition.Typed.Variant
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Transparentisation
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant hiding (ℕ≢ne)
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Identity R
open import Definition.Typed.Properties.Admissible.Lift R
open import Definition.Typed.Properties.Admissible.Pi-Sigma R
open import Definition.Typed.Properties.Definition R
open import Definition.Typed.Well-formed R

open import Tools.Function
import Tools.Level as L
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Unit
open import Tools.Vec as Vec using (ε)

private
  variable
    n α : Nat
    ∇ ∇′ ∇″ : DCon (Term 0) _
    Γ : Con Term _
    A B t u : Term _
    l l₁ l₂ : Lvl _
    V : Set a
    φ φ′ : Unfolding _

opaque
  unfolding Trans

  -- If α has type A in ∇, then α has the same type in every
  -- transparentisation of ∇.

  unfold-↦∈ : α ↦∷ A ∈ ∇ → α ↦∷ A ∈ Trans φ ∇
  unfold-↦∈ {∇ = ε}           ()
  unfold-↦∈ {∇ = _ ∙⟨ tra ⟩!} here =
    here
  unfold-↦∈ {∇ = _ ∙⟨ opa _ ⟩!} {φ = _ ⁰} here =
    here
  unfold-↦∈ {∇ = _ ∙⟨ opa _ ⟩!} {φ = _ ¹} here =
    here
  unfold-↦∈ {∇ = _ ∙⟨ tra ⟩!} (there α↦) =
    there (unfold-↦∈ α↦)
  unfold-↦∈ {∇ = _ ∙⟨ opa _ ⟩!} {φ = _ ⁰} (there α↦) =
    there (unfold-↦∈ α↦)
  unfold-↦∈ {∇ = _ ∙⟨ opa _ ⟩!} {φ = _ ¹} (there α↦) =
    there (unfold-↦∈ α↦)

opaque
  unfolding Trans

  -- If α has the body t and the type A in ∇, then α has the same body
  -- and type in every transparentisation of ∇.

  unfold-↦∷∈ : α ↦ t ∷ A ∈ ∇ → α ↦ t ∷ A ∈ Trans φ ∇
  unfold-↦∷∈ {∇ = ε}           ()
  unfold-↦∷∈ {∇ = _ ∙⟨ tra ⟩!} here =
    here
  unfold-↦∷∈ {∇ = _ ∙⟨ tra ⟩!} (there α↦) =
    there (unfold-↦∷∈ α↦)
  unfold-↦∷∈ {∇ = _ ∙⟨ opa _ ⟩!} {φ = _ ⁰} (there α↦) =
    there (unfold-↦∷∈ α↦)
  unfold-↦∷∈ {∇ = _ ∙⟨ opa _ ⟩!} {φ = _ ¹} (there α↦) =
    there (unfold-↦∷∈ α↦)

-- The following module is re-exported from the module Transitive
-- below. It uses the assumption that Trans φ ∇ is well-formed
-- whenever ∇ is.

module Unconditional (»-Trans : » ∇ → » Trans φ ∇) where

  opaque mutual

    -- Varible contexts that are well-formed under ∇ are well-formed
    -- under Trans φ ∇.

    unfold-⊢′ : ∇ »⊢ Γ → Trans φ ∇ »⊢ Γ
    unfold-⊢′ (ε »∇) = ε (»-Trans »∇)
    unfold-⊢′ (∙ ⊢A) = ∙ unfold-⊢ ⊢A

    -- Types that are well-formed under ∇ are well-formed under
    -- Trans φ ∇.

    unfold-⊢ : ∇ » Γ ⊢ A → Trans φ ∇ » Γ ⊢ A
    unfold-⊢ (Levelⱼ ok ⊢Γ) =
      Levelⱼ ok (unfold-⊢′ ⊢Γ)
    unfold-⊢ (Liftⱼ ⊢l ⊢A) =
      Liftⱼ (unfold-⊢∷L ⊢l) (unfold-⊢ ⊢A)
    unfold-⊢ (ΠΣⱼ ⊢A ok) = ΠΣⱼ (unfold-⊢ ⊢A) ok
    unfold-⊢ (Idⱼ ⊢A ⊢t ⊢u) =
      Idⱼ (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t) (unfold-⊢∷ ⊢u)
    unfold-⊢ (univ ⊢A) = univ (unfold-⊢∷ ⊢A)

    -- Terms that are well-formed under ∇ are well-formed under
    -- Trans φ ∇.

    unfold-⊢∷ : ∇ » Γ ⊢ t ∷ A → Trans φ ∇ » Γ ⊢ t ∷ A
    unfold-⊢∷ (Levelⱼ ⊢Γ ok) =
      Levelⱼ (unfold-⊢′ ⊢Γ) ok
    unfold-⊢∷ (zeroᵘⱼ ok ⊢Γ) =
      zeroᵘⱼ ok (unfold-⊢′ ⊢Γ)
    unfold-⊢∷ (sucᵘⱼ ⊢l) =
      sucᵘⱼ (unfold-⊢∷ ⊢l)
    unfold-⊢∷ (supᵘⱼ ⊢l₁ ⊢l₂) =
      supᵘⱼ (unfold-⊢∷ ⊢l₁) (unfold-⊢∷ ⊢l₂)
    unfold-⊢∷ (Uⱼ ⊢l) = Uⱼ (unfold-⊢∷L ⊢l)
    unfold-⊢∷ (Liftⱼ _ ⊢l ⊢A) =
      Liftⱼ′ (unfold-⊢∷L ⊢l) (unfold-⊢∷ ⊢A)
    unfold-⊢∷ (liftⱼ ⊢l _ ⊢t) =
      liftⱼ′ (unfold-⊢∷L ⊢l) (unfold-⊢∷ ⊢t)
    unfold-⊢∷ (lowerⱼ ⊢t) =
      lowerⱼ (unfold-⊢∷ ⊢t)
    unfold-⊢∷ (ΠΣⱼ _ ⊢t₁ ⊢t₂ ok) =
      ΠΣⱼ′ (unfold-⊢∷ ⊢t₁) (unfold-⊢∷ ⊢t₂) ok
    unfold-⊢∷ (ℕⱼ ⊢Γ) = ℕⱼ (unfold-⊢′ ⊢Γ)
    unfold-⊢∷ (Emptyⱼ ⊢Γ) = Emptyⱼ (unfold-⊢′ ⊢Γ)
    unfold-⊢∷ (Unitⱼ ⊢Γ ok) = Unitⱼ (unfold-⊢′ ⊢Γ) ok
    unfold-⊢∷ (conv ⊢t A≡A′) =
      conv (unfold-⊢∷ ⊢t) (unfold-⊢≡ A≡A′)
    unfold-⊢∷ (var ⊢Γ x∈) = var (unfold-⊢′ ⊢Γ) x∈
    unfold-⊢∷ (defn ⊢Γ α↦t A≡A′) =
      defn (unfold-⊢′ ⊢Γ) (unfold-↦∈ α↦t) A≡A′
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
    unfold-⊢∷ ([]-congⱼ ⊢l _ _ _ ⊢tₚ ok) =
      []-congⱼ′ ok (unfold-⊢∷L ⊢l) (unfold-⊢∷ ⊢tₚ)

    -- Levels that are well-formed under ∇ are well-formed under
    -- Trans φ ∇.

    unfold-⊢∷L : ∇ » Γ ⊢ l ∷Level → Trans φ ∇ » Γ ⊢ l ∷Level
    unfold-⊢∷L (term ok ⊢l) =
      term ok (unfold-⊢∷ ⊢l)
    unfold-⊢∷L (literal ok ⊢Γ) =
      literal ok (unfold-⊢′ ⊢Γ)

    -- Type equalities that hold under ∇ hold under Trans φ ∇.

    unfold-⊢≡ : ∇ » Γ ⊢ A ≡ B → Trans φ ∇ » Γ ⊢ A ≡ B
    unfold-⊢≡ (univ A≡A′) = univ (unfold-⊢≡∷ A≡A′)
    unfold-⊢≡ (refl ⊢A) = refl (unfold-⊢ ⊢A)
    unfold-⊢≡ (sym A≡A′) = sym (unfold-⊢≡ A≡A′)
    unfold-⊢≡ (trans A≡A′ A′≡A″) =
      trans (unfold-⊢≡ A≡A′) (unfold-⊢≡ A′≡A″)
    unfold-⊢≡ (U-cong l₁≡l₂) =
      U-cong (unfold-⊢≡∷ l₁≡l₂)
    unfold-⊢≡ (Lift-cong l₁≡l₂ A₁≡A₂) =
      Lift-cong (unfold-⊢≡∷L l₁≡l₂) (unfold-⊢≡ A₁≡A₂)
    unfold-⊢≡ (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) =
      ΠΣ-cong (unfold-⊢≡ A₁≡A₂) (unfold-⊢≡ B₁≡B₂) ok
    unfold-⊢≡ (Id-cong A≡A′ t₁≡t₂ u₁≡u₂) =
      Id-cong (unfold-⊢≡ A≡A′)
              (unfold-⊢≡∷ t₁≡t₂)
              (unfold-⊢≡∷ u₁≡u₂)

    -- Term equalities that hold under ∇ hold under Trans φ ∇.

    unfold-⊢≡∷ : ∇ » Γ ⊢ t ≡ u ∷ A → Trans φ ∇ » Γ ⊢ t ≡ u ∷ A
    unfold-⊢≡∷ (refl ⊢t) = refl (unfold-⊢∷ ⊢t)
    unfold-⊢≡∷ (sym ⊢A t≡t′) =
      sym (unfold-⊢ ⊢A) (unfold-⊢≡∷ t≡t′)
    unfold-⊢≡∷ (trans t≡t′ t′≡t″) =
      trans (unfold-⊢≡∷ t≡t′) (unfold-⊢≡∷ t′≡t″)
    unfold-⊢≡∷ (conv t≡t′ A≡A′) =
      conv (unfold-⊢≡∷ t≡t′) (unfold-⊢≡ A≡A′)
    unfold-⊢≡∷ (δ-red ⊢Γ α↦t A≡A′ t≡t′) =
      δ-red (unfold-⊢′ ⊢Γ) (unfold-↦∷∈ α↦t) A≡A′ t≡t′
    unfold-⊢≡∷ (sucᵘ-cong l₁≡l₂) =
      sucᵘ-cong (unfold-⊢≡∷ l₁≡l₂)
    unfold-⊢≡∷ (supᵘ-cong l₁₁≡l₂₁ l₁₂≡l₂₂) =
      supᵘ-cong (unfold-⊢≡∷ l₁₁≡l₂₁) (unfold-⊢≡∷ l₁₂≡l₂₂)
    unfold-⊢≡∷ (supᵘ-zeroˡ ⊢l) =
      supᵘ-zeroˡ (unfold-⊢∷ ⊢l)
    unfold-⊢≡∷ (supᵘ-sucᵘ ⊢l₁ ⊢l₂) =
      supᵘ-sucᵘ (unfold-⊢∷ ⊢l₁) (unfold-⊢∷ ⊢l₂)
    unfold-⊢≡∷ (supᵘ-assoc ⊢l₁ ⊢l₂ ⊢l₃) =
      supᵘ-assoc (unfold-⊢∷ ⊢l₁) (unfold-⊢∷ ⊢l₂) (unfold-⊢∷ ⊢l₃)
    unfold-⊢≡∷ (supᵘ-comm ⊢l₁ ⊢l₂) =
      supᵘ-comm (unfold-⊢∷ ⊢l₁) (unfold-⊢∷ ⊢l₂)
    unfold-⊢≡∷ (supᵘ-idem ⊢l) =
      supᵘ-idem (unfold-⊢∷ ⊢l)
    unfold-⊢≡∷ (supᵘ-sub ⊢l) =
      supᵘ-sub (unfold-⊢∷ ⊢l)
    unfold-⊢≡∷ (U-cong l₁≡l₂) =
      U-cong (unfold-⊢≡∷ l₁≡l₂)
    unfold-⊢≡∷ (Lift-cong _ _ l₁≡l₂ A₁≡A₂) =
      Lift-cong′ (unfold-⊢≡∷L l₁≡l₂) (unfold-⊢≡∷ A₁≡A₂)
    unfold-⊢≡∷ (lower-cong t₁≡t₂) =
      lower-cong (unfold-⊢≡∷ t₁≡t₂)
    unfold-⊢≡∷ (Lift-β _ ⊢t) =
      Lift-β′ (unfold-⊢∷ ⊢t)
    unfold-⊢≡∷ (Lift-η _ _ ⊢t₁ ⊢t₂ lower-t₁≡lower-t₂) =
      Lift-η′ (unfold-⊢∷ ⊢t₁) (unfold-⊢∷ ⊢t₂)
        (unfold-⊢≡∷ lower-t₁≡lower-t₂)
    unfold-⊢≡∷ (ΠΣ-cong ⊢l t₁≡t₂ u₁≡u₂ ok) =
      ΠΣ-cong (unfold-⊢∷L ⊢l) (unfold-⊢≡∷ t₁≡t₂) (unfold-⊢≡∷ u₁≡u₂) ok
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
    unfold-⊢≡∷ ([]-cong-cong l₁≡l₂ A≡A′ t₁≡t₂ u₁≡u₂ p≡p′ ok) =
      []-cong-cong (unfold-⊢≡∷L l₁≡l₂) (unfold-⊢≡ A≡A′)
        (unfold-⊢≡∷ t₁≡t₂) (unfold-⊢≡∷ u₁≡u₂) (unfold-⊢≡∷ p≡p′) ok
    unfold-⊢≡∷ (J-β ⊢t ⊢A ⊢tᵣ eq) =
      J-β (unfold-⊢∷ ⊢t)
          (unfold-⊢ ⊢A)
          (unfold-⊢∷ ⊢tᵣ)
          eq
    unfold-⊢≡∷ (K-β ⊢A ⊢t ok) =
      K-β (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t) ok
    unfold-⊢≡∷ ([]-cong-β ⊢l ⊢t PE.refl ok) =
      []-cong-β-≡ (unfold-⊢∷L ⊢l) (refl (unfold-⊢∷ ⊢t)) ok
    unfold-⊢≡∷ (equality-reflection ok ⊢Id ⊢t) =
      equality-reflection ok (unfold-⊢ ⊢Id) (unfold-⊢∷ ⊢t)

    -- Level equalities that hold under ∇ hold under Trans φ ∇.

    unfold-⊢≡∷L :
      ∇ » Γ ⊢ l₁ ≡ l₂ ∷Level → Trans φ ∇ » Γ ⊢ l₁ ≡ l₂ ∷Level
    unfold-⊢≡∷L (term ok l₁≡l₂) =
      term ok (unfold-⊢≡∷ l₁≡l₂)
    unfold-⊢≡∷L (literal ok ⊢Γ) =
      literal ok (unfold-⊢′ ⊢Γ)

  opaque

    -- Reductions that hold under ∇ hold under Trans φ ∇.

    unfold-⇒∷ : ∇ » Γ ⊢ t ⇒ u ∷ A → Trans φ ∇ » Γ ⊢ t ⇒ u ∷ A
    unfold-⇒∷ (conv t⇒t′ A≡A′) =
      conv (unfold-⇒∷ t⇒t′) (unfold-⊢≡ A≡A′)
    unfold-⇒∷ (δ-red ⊢Γ α↦t A≡A′ T≡T′) =
      δ-red (unfold-⊢′ ⊢Γ) (unfold-↦∷∈ α↦t) A≡A′ T≡T′
    unfold-⇒∷ (supᵘ-substˡ l₁⇒l₂ ⊢l₃) =
      supᵘ-substˡ (unfold-⇒∷ l₁⇒l₂) (unfold-⊢∷ ⊢l₃)
    unfold-⇒∷ (supᵘ-substʳ ⊢l₁ l₂⇒l₃) =
      supᵘ-substʳ (unfold-⊢∷ ⊢l₁) (unfold-⇒∷ l₂⇒l₃)
    unfold-⇒∷ (supᵘ-zeroˡ ⊢l) =
      supᵘ-zeroˡ (unfold-⊢∷ ⊢l)
    unfold-⇒∷ (supᵘ-zeroʳ ⊢l) =
      supᵘ-zeroʳ (unfold-⊢∷ ⊢l)
    unfold-⇒∷ (supᵘ-sucᵘ ⊢l₁ ⊢l₂) =
      supᵘ-sucᵘ (unfold-⊢∷ ⊢l₁) (unfold-⊢∷ ⊢l₂)
    unfold-⇒∷ (lower-subst t⇒u) =
      lower-subst (unfold-⇒∷ t⇒u)
    unfold-⇒∷ (Lift-β _ ⊢t) =
      Lift-β⇒ (unfold-⊢∷ ⊢t)
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
    unfold-⇒∷ ([]-cong-subst ⊢l t⇒t′ ok) =
      []-cong-subst (unfold-⊢∷L ⊢l) (unfold-⇒∷ t⇒t′) ok
    unfold-⇒∷ (J-β ⊢t ⊢t′ t≡t′ ⊢A A≡ ⊢tᵣ) =
      J-β (unfold-⊢∷ ⊢t)
          (unfold-⊢∷ ⊢t′)
          (unfold-⊢≡∷ t≡t′)
          (unfold-⊢ ⊢A)
          (unfold-⊢≡ A≡)
          (unfold-⊢∷ ⊢tᵣ)
    unfold-⇒∷ (K-β ⊢A ⊢t ok) =
      K-β (unfold-⊢ ⊢A) (unfold-⊢∷ ⊢t) ok
    unfold-⇒∷ ([]-cong-β ⊢l t≡t′ ok) =
      []-cong-β (unfold-⊢∷L ⊢l) (unfold-⊢≡∷ t≡t′) ok

  opaque

    -- Reductions that hold under ∇ hold under Trans φ ∇.

    unfold-⇒ : ∇ » Γ ⊢ A ⇒ B → Trans φ ∇ » Γ ⊢ A ⇒ B
    unfold-⇒ (univ A⇒B) = univ (unfold-⇒∷ A⇒B)

  opaque

    -- Reductions that hold under ∇ hold under Trans φ ∇.

    unfold-⇒* : ∇ » Γ ⊢ A ⇒* B → Trans φ ∇ » Γ ⊢ A ⇒* B
    unfold-⇒* (id ⊢A)      = id (unfold-⊢ ⊢A)
    unfold-⇒* (A⇒X ⇨ X⇒*B) = unfold-⇒ A⇒X ⇨ unfold-⇒* X⇒*B

  opaque

    -- Reductions that hold under ∇ hold under Trans φ ∇.

    unfold-⇒*∷ : ∇ » Γ ⊢ t ⇒* u ∷ A → Trans φ ∇ » Γ ⊢ t ⇒* u ∷ A
    unfold-⇒*∷ (id ⊢t)      = id (unfold-⊢∷ ⊢t)
    unfold-⇒*∷ (t⇒x ⇨ x⇒*u) = unfold-⇒∷ t⇒x ⇨ unfold-⇒*∷ x⇒*u

module Transitive (mode-eq : unfolding-mode PE.≡ transitive) where

  opaque

    comm-⊔ᵒᵗ : (φ φ′ : Unfolding n) → φ ⊔ᵒᵗ φ′ PE.≡ φ′ ⊔ᵒᵗ φ
    comm-⊔ᵒᵗ φ φ′ = begin
      φ ⊔ᵒᵗ φ′  ≡⟨ ⊔ᵒᵗ≡⊔ᵒ mode-eq ⟩
      φ ⊔ᵒ φ′   ≡⟨ comm-⊔ᵒ φ φ′ ⟩
      φ′ ⊔ᵒ φ   ≡˘⟨ ⊔ᵒᵗ≡⊔ᵒ mode-eq ⟩
      φ′ ⊔ᵒᵗ φ  ∎

  private

    -- A module used in the implementation of unfold-» below.

    module U {n} {∇ : DCon (Term 0) n} {φ : Unfolding n}
             (unfold-» : » ∇ → » Trans φ ∇) =
      Unconditional unfold-»

  opaque
    unfolding Trans

    -- If ∇ is well-formed, then Trans φ ∇ is well-formed.

    unfold-» : » ∇ → » Trans φ ∇
    unfold-» ε =
      ε
    unfold-» ∙ᵗ[ ⊢t ] =
      ∙ᵗ[ U.unfold-⊢∷ unfold-» ⊢t ]
    unfold-» {φ = φ ⁰} (∙ᵒ⟨_⟩[_∷_] {φ = φ′} {∇} ok ⊢t ⊢A) =
      ∙ᵒ⟨ ok ⟩[ PE.subst₃ _⊢_∷_
                  (PE.cong (_» _)
                     (Trans φ (Trans φ′ ∇)  ≡⟨ Trans-trans ⟩
                      Trans (φ′ ⊔ᵒ φ) ∇     ≡⟨ PE.cong (flip Trans _) $ comm-⊔ᵒ _ _ ⟩
                      Trans (φ ⊔ᵒ φ′) ∇     ≡˘⟨ Trans-trans ⟩
                      Trans φ′ (Trans φ ∇)  ∎))
                  PE.refl PE.refl $
                U.unfold-⊢∷ unfold-» ⊢t
              ∷ U.unfold-⊢ unfold-» ⊢A
              ]
    unfold-» {φ = φ ¹} (∙ᵒ⟨_⟩[_∷_] {φ = φ′} {∇} ok ⊢t ⊢A) =
      ∙ᵗ[ PE.subst₃ _⊢_∷_
            (PE.cong (_» _)
               (Trans φ (Trans φ′ ∇)  ≡⟨ Trans-transᵗ mode-eq ⟩
                Trans (φ′ ⊔ᵒᵗ φ) ∇    ≡⟨ PE.cong (flip Trans _) $ comm-⊔ᵒᵗ _ _ ⟩
                Trans (φ ⊔ᵒᵗ φ′) ∇    ∎))
            PE.refl PE.refl $
          U.unfold-⊢∷ unfold-» ⊢t
        ]

  -- Other preservation lemmas related to transparentisation.

  module _ {∇ : DCon (Term 0) n} {φ : Unfolding n} where
    open Unconditional (unfold-» {∇ = ∇} {φ = φ}) public
