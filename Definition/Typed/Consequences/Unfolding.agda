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
  
  private opaque

    ⊔ᵒᵗ-eq : (φ φ′ : Unfolding n) → φ ⊔ᵒᵗ φ′ PE.≡ φ ⊔ᵒ φ′
    ⊔ᵒᵗ-eq φ φ′ with unfolding-mode
    ...            | explicit   = case mode-eq of λ ()
    ...            | transitive = PE.refl

  opaque

    comm-⊔ᵒᵗ : (φ φ′ : Unfolding n) → φ ⊔ᵒᵗ φ′ PE.≡ φ′ ⊔ᵒᵗ φ
    comm-⊔ᵒᵗ φ φ′ = begin
      φ ⊔ᵒᵗ φ′  ≡⟨ ⊔ᵒᵗ-eq φ φ′ ⟩
      φ ⊔ᵒ φ′   ≡⟨ comm-⊔ᵒ φ φ′ ⟩
      φ′ ⊔ᵒ φ   ≡˘⟨ ⊔ᵒᵗ-eq φ′ φ ⟩
      φ′ ⊔ᵒᵗ φ  ∎

  private opaque

    a1[23] : (φ φ′ φ″ : Unfolding n) → φ ⊔ᵒᵗ (φ′ ⊔ᵒᵗ φ″) PE.≡ (φ ⊔ᵒ φ′) ⊔ᵒᵗ φ″
    a1[23] φ φ′ φ″ = begin
      φ ⊔ᵒᵗ (φ′ ⊔ᵒᵗ φ″)  ≡⟨ assoc-⊔ᵒᵗ φ φ′ φ″ ⟩
      (φ ⊔ᵒᵗ φ′) ⊔ᵒᵗ φ″  ≡⟨ PE.cong (_⊔ᵒᵗ φ″) (⊔ᵒᵗ-eq φ φ′) ⟩
      (φ ⊔ᵒ φ′) ⊔ᵒᵗ φ″   ∎

  private opaque

    a[13]2 : (φ φ′ φ″ : Unfolding n) → (φ ⊔ᵒᵗ φ″) ⊔ᵒᵗ φ′ PE.≡ (φ ⊔ᵒ φ′) ⊔ᵒᵗ φ″
    a[13]2 φ φ′ φ″ = begin
      (φ ⊔ᵒᵗ φ″) ⊔ᵒᵗ φ′  ≡˘⟨ assoc-⊔ᵒᵗ φ φ″ φ′ ⟩
      φ ⊔ᵒᵗ (φ″ ⊔ᵒᵗ φ′)  ≡⟨ PE.cong (φ ⊔ᵒᵗ_) (comm-⊔ᵒᵗ φ″ φ′) ⟩
      φ ⊔ᵒᵗ (φ′ ⊔ᵒᵗ φ″)  ≡⟨ assoc-⊔ᵒᵗ φ φ′ φ″ ⟩
      (φ ⊔ᵒᵗ φ′) ⊔ᵒᵗ φ″  ≡⟨ PE.cong (_⊔ᵒᵗ φ″) (⊔ᵒᵗ-eq φ φ′) ⟩
      (φ ⊔ᵒ φ′) ⊔ᵒᵗ φ″   ∎

  opaque

    join-»↜ : φ » ∇′ ↜ ∇ → φ′ » ∇″ ↜ ∇′ → φ ⊔ᵒᵗ φ′ » ∇″ ↜ ∇
    join-»↜ φ↜ φ′↜ = PE.subst (_» _ ↜ _) (PE.sym (⊔ᵒᵗ-eq _ _)) (join′ φ↜ φ′↜)
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
    unjoin-»↜ φ′φ↜ φ↜ = unjoin′ (PE.subst (_» _ ↜ _) (⊔ᵒᵗ-eq _ _) φ′φ↜) φ↜
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

  opaque

    unfold-↦∈ : φ » ∇′ ↜ ∇ → α ↦∷ A ∈ ∇ → α ↦∷ A ∈ ∇′
    unfold-↦∈ ε       ()
    unfold-↦∈ (φ↜ ⁰)  here         = here
    unfold-↦∈ (φ↜ ¹ᵒ) here         = here
    unfold-↦∈ (φ↜ ¹ᵗ) here         = here
    unfold-↦∈ (φ↜ ⁰)  (there α↦∷A) = there (unfold-↦∈ φ↜ α↦∷A)
    unfold-↦∈ (φ↜ ¹ᵒ) (there α↦∷A) = there (unfold-↦∈ φ↜ α↦∷A)
    unfold-↦∈ (φ↜ ¹ᵗ) (there α↦∷A) = there (unfold-↦∈ φ↜ α↦∷A)

  opaque

    unfold-↦∷∈ : φ » ∇′ ↜ ∇ → α ↦ t ∷ A ∈ ∇ → α ↦ t ∷ A ∈ ∇′
    unfold-↦∷∈ ε       ()
    unfold-↦∷∈ (φ↜ ⁰)  here        = here
    unfold-↦∷∈ (φ↜ ¹ᵗ) here        = here
    unfold-↦∷∈ (φ↜ ⁰)  (there α↦t) = there (unfold-↦∷∈ φ↜ α↦t)
    unfold-↦∷∈ (φ↜ ¹ᵒ) (there α↦t) = there (unfold-↦∷∈ φ↜ α↦t)
    unfold-↦∷∈ (φ↜ ¹ᵗ) (there α↦t) = there (unfold-↦∷∈ φ↜ α↦t)

  opaque mutual

    unfold-» : φ » ∇′ ↜ ∇ → » ∇ → » ∇′
    unfold-» ε       ε                         = ε
    unfold-» (φ↜ ⁰)  ∙ᵒ⟨ ok , φ′↜ ⟩[ ⊢t ∷ ⊢A ] =
      let _ , φ″↜ = total-»↜ _ _
      in  ∙ᵒ⟨ ok , φ″↜ ⟩[ unfold-⊢∷ (unjoin-»↜ (join-»↜ φ↜ φ″↜) φ′↜) ⊢t
                        ∷ unfold-⊢ φ↜ ⊢A
                        ]
    unfold-» (φ↜ ¹ᵒ) ∙ᵒ⟨ ok , φ′↜ ⟩[ ⊢t ∷ ⊢A ] = ∙ᵗ[ unfold-⊢∷ (unjoin-»↜ φ↜ φ′↜) ⊢t ]
    unfold-» (φ↜ ⁰)              ∙ᵗ[ ⊢t      ] = ∙ᵗ[ unfold-⊢∷ φ↜ ⊢t ]
    unfold-» (φ↜ ¹ᵗ)             ∙ᵗ[ ⊢t      ] = ∙ᵗ[ unfold-⊢∷ φ↜ ⊢t ]

    unfold-⊢′ : φ » ∇′ ↜ ∇ → ∇ »⊢ Γ → ∇′ »⊢ Γ
    unfold-⊢′ φ↜ (ε »∇) = ε (unfold-» φ↜ »∇)
    unfold-⊢′ φ↜ (∙ ⊢A) = ∙ unfold-⊢ φ↜ ⊢A

    unfold-⊢ : φ » ∇′ ↜ ∇ → ∇ » Γ ⊢ A → ∇′ » Γ ⊢ A
    unfold-⊢ φ↜ (Uⱼ ⊢Γ) = Uⱼ (unfold-⊢′ φ↜ ⊢Γ)
    unfold-⊢ φ↜ (ℕⱼ ⊢Γ) = ℕⱼ (unfold-⊢′ φ↜ ⊢Γ)
    unfold-⊢ φ↜ (Emptyⱼ ⊢Γ) = Emptyⱼ (unfold-⊢′ φ↜ ⊢Γ)
    unfold-⊢ φ↜ (Unitⱼ ⊢Γ ok) = Unitⱼ (unfold-⊢′ φ↜ ⊢Γ) ok
    unfold-⊢ φ↜ (ΠΣⱼ ⊢A ok) = ΠΣⱼ (unfold-⊢ φ↜ ⊢A) ok
    unfold-⊢ φ↜ (Idⱼ ⊢A ⊢t ⊢u) =
      Idⱼ (unfold-⊢ φ↜ ⊢A) (unfold-⊢∷ φ↜ ⊢t) (unfold-⊢∷ φ↜ ⊢u)
    unfold-⊢ φ↜ (univ ⊢A) = univ (unfold-⊢∷ φ↜ ⊢A)

    unfold-⊢∷ : φ » ∇′ ↜ ∇ → ∇ » Γ ⊢ t ∷ A → ∇′ » Γ ⊢ t ∷ A
    unfold-⊢∷ φ↜ (Uⱼ ⊢Γ) = Uⱼ (unfold-⊢′ φ↜ ⊢Γ)
    unfold-⊢∷ φ↜ (ΠΣⱼ ⊢t₁ ⊢t₂ ok) =
      ΠΣⱼ (unfold-⊢∷ φ↜ ⊢t₁) (unfold-⊢∷ φ↜ ⊢t₂) ok
    unfold-⊢∷ φ↜ (ℕⱼ ⊢Γ) = ℕⱼ (unfold-⊢′ φ↜ ⊢Γ)
    unfold-⊢∷ φ↜ (Emptyⱼ ⊢Γ) = Emptyⱼ (unfold-⊢′ φ↜ ⊢Γ)
    unfold-⊢∷ φ↜ (Unitⱼ ⊢Γ ok) = Unitⱼ (unfold-⊢′ φ↜ ⊢Γ) ok
    unfold-⊢∷ φ↜ (conv ⊢t A≡A′) =
      conv (unfold-⊢∷ φ↜ ⊢t) (unfold-⊢≡ φ↜ A≡A′)
    unfold-⊢∷ φ↜ (var ⊢Γ x∈) = var (unfold-⊢′ φ↜ ⊢Γ) x∈
    unfold-⊢∷ φ↜ (defn ⊢Γ α↦t A≡A′) =
      defn (unfold-⊢′ φ↜ ⊢Γ) (unfold-↦∈ φ↜ α↦t) A≡A′
    unfold-⊢∷ φ↜ (lamⱼ ⊢A ⊢t ok) =
      lamⱼ (unfold-⊢ φ↜ ⊢A) (unfold-⊢∷ φ↜ ⊢t) ok
    unfold-⊢∷ φ↜ (⊢t₁ ∘ⱼ ⊢t₂) =
      unfold-⊢∷ φ↜ ⊢t₁ ∘ⱼ unfold-⊢∷ φ↜ ⊢t₂
    unfold-⊢∷ φ↜ (prodⱼ ⊢A ⊢t₁ ⊢t₂ ok) =
      prodⱼ (unfold-⊢ φ↜ ⊢A)
            (unfold-⊢∷ φ↜ ⊢t₁)
            (unfold-⊢∷ φ↜ ⊢t₂)
            ok
    unfold-⊢∷ φ↜ (fstⱼ ⊢A ⊢t) =
      fstⱼ (unfold-⊢ φ↜ ⊢A) (unfold-⊢∷ φ↜ ⊢t)
    unfold-⊢∷ φ↜ (sndⱼ ⊢A ⊢t) =
      sndⱼ (unfold-⊢ φ↜ ⊢A) (unfold-⊢∷ φ↜ ⊢t)
    unfold-⊢∷ φ↜ (prodrecⱼ ⊢A ⊢t ⊢t′ ok) =
      prodrecⱼ (unfold-⊢ φ↜ ⊢A)
              (unfold-⊢∷ φ↜ ⊢t)
              (unfold-⊢∷ φ↜ ⊢t′)
              ok
    unfold-⊢∷ φ↜ (zeroⱼ ⊢Γ) = zeroⱼ (unfold-⊢′ φ↜ ⊢Γ)
    unfold-⊢∷ φ↜ (sucⱼ ⊢t) = sucⱼ (unfold-⊢∷ φ↜ ⊢t)
    unfold-⊢∷ φ↜ (natrecⱼ ⊢t₀ ⊢tₛ ⊢t) =
      natrecⱼ (unfold-⊢∷ φ↜ ⊢t₀)
              (unfold-⊢∷ φ↜ ⊢tₛ)
              (unfold-⊢∷ φ↜ ⊢t)
    unfold-⊢∷ φ↜ (emptyrecⱼ ⊢A ⊢t) =
      emptyrecⱼ (unfold-⊢ φ↜ ⊢A) (unfold-⊢∷ φ↜ ⊢t)
    unfold-⊢∷ φ↜ (starⱼ ⊢Γ ok) = starⱼ (unfold-⊢′ φ↜ ⊢Γ) ok
    unfold-⊢∷ φ↜ (unitrecⱼ ⊢A ⊢t ⊢t′ ok) =
      unitrecⱼ (unfold-⊢ φ↜ ⊢A)
              (unfold-⊢∷ φ↜ ⊢t)
              (unfold-⊢∷ φ↜ ⊢t′)
              ok
    unfold-⊢∷ φ↜ (Idⱼ ⊢A ⊢t₁ ⊢t₂) =
      Idⱼ (unfold-⊢∷ φ↜ ⊢A)
          (unfold-⊢∷ φ↜ ⊢t₁)
          (unfold-⊢∷ φ↜ ⊢t₂)
    unfold-⊢∷ φ↜ (rflⱼ ⊢t) = rflⱼ (unfold-⊢∷ φ↜ ⊢t)
    unfold-⊢∷ φ↜ (Jⱼ ⊢t ⊢A ⊢tᵣ ⊢t′ ⊢tₚ) =
      Jⱼ (unfold-⊢∷ φ↜ ⊢t)
        (unfold-⊢ φ↜ ⊢A)
        (unfold-⊢∷ φ↜ ⊢tᵣ)
        (unfold-⊢∷ φ↜ ⊢t′)
        (unfold-⊢∷ φ↜ ⊢tₚ)
    unfold-⊢∷ φ↜ (Kⱼ ⊢A ⊢tᵣ ⊢tₚ ok) =
      Kⱼ (unfold-⊢ φ↜ ⊢A)
        (unfold-⊢∷ φ↜ ⊢tᵣ)
        (unfold-⊢∷ φ↜ ⊢tₚ)
        ok
    unfold-⊢∷ φ↜ ([]-congⱼ ⊢A ⊢t₁ ⊢t₂ ⊢tₚ ok) =
      []-congⱼ (unfold-⊢ φ↜ ⊢A)
              (unfold-⊢∷ φ↜ ⊢t₁)
              (unfold-⊢∷ φ↜ ⊢t₂)
              (unfold-⊢∷ φ↜ ⊢tₚ) ok

    unfold-⊢≡ : φ » ∇′ ↜ ∇ → ∇ » Γ ⊢ A ≡ B → ∇′ » Γ ⊢ A ≡ B
    unfold-⊢≡ φ↜ (univ A≡A′) = univ (unfold-⊢≡∷ φ↜ A≡A′)
    unfold-⊢≡ φ↜ (refl ⊢A) = refl (unfold-⊢ φ↜ ⊢A)
    unfold-⊢≡ φ↜ (sym A≡A′) = sym (unfold-⊢≡ φ↜ A≡A′)
    unfold-⊢≡ φ↜ (trans A≡A′ A′≡A″) =
      trans (unfold-⊢≡ φ↜ A≡A′) (unfold-⊢≡ φ↜ A′≡A″)
    unfold-⊢≡ φ↜ (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) =
      ΠΣ-cong (unfold-⊢≡ φ↜ A₁≡A₂) (unfold-⊢≡ φ↜ B₁≡B₂) ok
    unfold-⊢≡ φ↜ (Id-cong A≡A′ t₁≡t₂ u₁≡u₂) =
      Id-cong (unfold-⊢≡ φ↜ A≡A′)
              (unfold-⊢≡∷ φ↜ t₁≡t₂)
              (unfold-⊢≡∷ φ↜ u₁≡u₂)

    unfold-⊢≡∷ : φ » ∇′ ↜ ∇ → ∇ » Γ ⊢ t ≡ u ∷ A → ∇′ » Γ ⊢ t ≡ u ∷ A
    unfold-⊢≡∷ φ↜ (refl ⊢t) = refl (unfold-⊢∷ φ↜ ⊢t)
    unfold-⊢≡∷ φ↜ (sym ⊢A t≡t′) =
      sym (unfold-⊢ φ↜ ⊢A) (unfold-⊢≡∷ φ↜ t≡t′)
    unfold-⊢≡∷ φ↜ (trans t≡t′ t′≡t″) =
      trans (unfold-⊢≡∷ φ↜ t≡t′) (unfold-⊢≡∷ φ↜ t′≡t″)
    unfold-⊢≡∷ φ↜ (conv t≡t′ A≡A′) =
      conv (unfold-⊢≡∷ φ↜ t≡t′) (unfold-⊢≡ φ↜ A≡A′)
    unfold-⊢≡∷ φ↜ (δ-red ⊢Γ α↦t A≡A′ t≡t′) =
      δ-red (unfold-⊢′ φ↜ ⊢Γ) (unfold-↦∷∈ φ↜ α↦t) A≡A′ t≡t′
    unfold-⊢≡∷ φ↜ (ΠΣ-cong t₁≡t₂ u₁≡u₂ ok) =
      ΠΣ-cong (unfold-⊢≡∷ φ↜ t₁≡t₂) (unfold-⊢≡∷ φ↜ u₁≡u₂) ok
    unfold-⊢≡∷ φ↜ (app-cong t₁≡t₂ u₁≡u₂) =
      app-cong (unfold-⊢≡∷ φ↜ t₁≡t₂) (unfold-⊢≡∷ φ↜ u₁≡u₂)
    unfold-⊢≡∷ φ↜ (β-red ⊢A ⊢t ⊢x eq ok) =
      β-red (unfold-⊢ φ↜ ⊢A)
            (unfold-⊢∷ φ↜ ⊢t)
            (unfold-⊢∷ φ↜ ⊢x)
            eq ok
    unfold-⊢≡∷ φ↜ (η-eq ⊢A ⊢t ⊢t′ t≡t′ ok) =
      η-eq (unfold-⊢ φ↜ ⊢A)
          (unfold-⊢∷ φ↜ ⊢t)
          (unfold-⊢∷ φ↜ ⊢t′)
          (unfold-⊢≡∷ φ↜ t≡t′)
          ok
    unfold-⊢≡∷ φ↜ (fst-cong ⊢A t≡t′) =
      fst-cong (unfold-⊢ φ↜ ⊢A) (unfold-⊢≡∷ φ↜ t≡t′)
    unfold-⊢≡∷ φ↜ (snd-cong ⊢A t≡t′) =
      snd-cong (unfold-⊢ φ↜ ⊢A) (unfold-⊢≡∷ φ↜ t≡t′)
    unfold-⊢≡∷ φ↜ (Σ-β₁ ⊢A ⊢t ⊢t′ eq ok) =
      Σ-β₁ (unfold-⊢ φ↜ ⊢A)
          (unfold-⊢∷ φ↜ ⊢t)
          (unfold-⊢∷ φ↜ ⊢t′)
          eq ok
    unfold-⊢≡∷ φ↜ (Σ-β₂ ⊢A ⊢t ⊢t′ eq ok) =
      Σ-β₂ (unfold-⊢ φ↜ ⊢A)
          (unfold-⊢∷ φ↜ ⊢t)
          (unfold-⊢∷ φ↜ ⊢t′)
          eq ok
    unfold-⊢≡∷ φ↜ (Σ-η ⊢A ⊢t ⊢t′ fst≡ snd≡ ok) =
      Σ-η (unfold-⊢ φ↜ ⊢A)
          (unfold-⊢∷ φ↜ ⊢t)
          (unfold-⊢∷ φ↜ ⊢t′)
          (unfold-⊢≡∷ φ↜ fst≡)
          (unfold-⊢≡∷ φ↜ snd≡)
          ok
    unfold-⊢≡∷ φ↜ (prod-cong ⊢A t₁≡t₂ u₁≡u₂ ok) =
      prod-cong (unfold-⊢ φ↜ ⊢A)
                (unfold-⊢≡∷ φ↜ t₁≡t₂)
                (unfold-⊢≡∷ φ↜ u₁≡u₂)
                ok
    unfold-⊢≡∷ φ↜ (prodrec-cong A≡A′ t₁≡t₂ u₁≡u₂ ok) =
      prodrec-cong (unfold-⊢≡ φ↜ A≡A′)
                  (unfold-⊢≡∷ φ↜ t₁≡t₂)
                  (unfold-⊢≡∷ φ↜ u₁≡u₂)
                  ok
    unfold-⊢≡∷ φ↜ (prodrec-β ⊢A ⊢t₁ ⊢t₂ ⊢tᵣ eq ok) =
      prodrec-β (unfold-⊢ φ↜ ⊢A)
                (unfold-⊢∷ φ↜ ⊢t₁)
                (unfold-⊢∷ φ↜ ⊢t₂)
                (unfold-⊢∷ φ↜ ⊢tᵣ)
                eq ok
    unfold-⊢≡∷ φ↜ (suc-cong t≡t′) =
      suc-cong (unfold-⊢≡∷ φ↜ t≡t′)
    unfold-⊢≡∷ φ↜ (natrec-cong A≡A′ 0≡ s≡ t≡t′) =
      natrec-cong (unfold-⊢≡ φ↜ A≡A′)
                  (unfold-⊢≡∷ φ↜ 0≡)
                  (unfold-⊢≡∷ φ↜ s≡)
                  (unfold-⊢≡∷ φ↜ t≡t′)
    unfold-⊢≡∷ φ↜ (natrec-zero ⊢t₀ ⊢tₛ) =
      natrec-zero (unfold-⊢∷ φ↜ ⊢t₀) (unfold-⊢∷ φ↜ ⊢tₛ)
    unfold-⊢≡∷ φ↜ (natrec-suc ⊢t₀ ⊢tₛ ⊢t) =
      natrec-suc (unfold-⊢∷ φ↜ ⊢t₀)
                (unfold-⊢∷ φ↜ ⊢tₛ)
                (unfold-⊢∷ φ↜ ⊢t)
    unfold-⊢≡∷ φ↜ (emptyrec-cong A≡A′ t≡t′) =
      emptyrec-cong (unfold-⊢≡ φ↜ A≡A′) (unfold-⊢≡∷ φ↜ t≡t′)
    unfold-⊢≡∷ φ↜ (unitrec-cong A≡A′ t≡t′ r≡ ok no-η) =
      unitrec-cong (unfold-⊢≡ φ↜ A≡A′)
                  (unfold-⊢≡∷ φ↜ t≡t′)
                  (unfold-⊢≡∷ φ↜ r≡)
                  ok no-η
    unfold-⊢≡∷ φ↜ (unitrec-β ⊢A ⊢t ok no-η) =
      unitrec-β (unfold-⊢ φ↜ ⊢A) (unfold-⊢∷ φ↜ ⊢t) ok no-η
    unfold-⊢≡∷ φ↜ (unitrec-β-η ⊢A ⊢t ⊢tᵣ ok η) =
      unitrec-β-η (unfold-⊢ φ↜ ⊢A)
                  (unfold-⊢∷ φ↜ ⊢t)
                  (unfold-⊢∷ φ↜ ⊢tᵣ)
                  ok η
    unfold-⊢≡∷ φ↜ (η-unit ⊢t ⊢t′ η) =
      η-unit (unfold-⊢∷ φ↜ ⊢t) (unfold-⊢∷ φ↜ ⊢t′) η
    unfold-⊢≡∷ φ↜ (Id-cong A≡A′ t₁≡t₂ u₁≡u₂) =
      Id-cong (unfold-⊢≡∷ φ↜ A≡A′)
              (unfold-⊢≡∷ φ↜ t₁≡t₂)
              (unfold-⊢≡∷ φ↜ u₁≡u₂)
    unfold-⊢≡∷ φ↜ (J-cong A≡A′ ⊢t t≡t′ B₁≡B₂ r≡ x≡ p≡) =
      J-cong (unfold-⊢≡ φ↜ A≡A′)
            (unfold-⊢∷ φ↜ ⊢t)
            (unfold-⊢≡∷ φ↜ t≡t′)
            (unfold-⊢≡ φ↜ B₁≡B₂)
            (unfold-⊢≡∷ φ↜ r≡)
            (unfold-⊢≡∷ φ↜ x≡)
            (unfold-⊢≡∷ φ↜ p≡)
    unfold-⊢≡∷ φ↜ (K-cong A≡A′ t≡t′ B₁≡B₂ r≡ p≡ ok) =
      K-cong (unfold-⊢≡ φ↜ A≡A′)
            (unfold-⊢≡∷ φ↜ t≡t′)
            (unfold-⊢≡ φ↜ B₁≡B₂)
            (unfold-⊢≡∷ φ↜ r≡)
            (unfold-⊢≡∷ φ↜ p≡)
            ok
    unfold-⊢≡∷ φ↜ ([]-cong-cong A≡A′ t₁≡t₂ u₁≡u₂ p≡p′ ok) =
      []-cong-cong (unfold-⊢≡ φ↜ A≡A′)
                  (unfold-⊢≡∷ φ↜ t₁≡t₂)
                  (unfold-⊢≡∷ φ↜ u₁≡u₂)
                  (unfold-⊢≡∷ φ↜ p≡p′) ok
    unfold-⊢≡∷ φ↜ (J-β ⊢t ⊢A ⊢tᵣ eq) =
      J-β (unfold-⊢∷ φ↜ ⊢t)
          (unfold-⊢ φ↜ ⊢A)
          (unfold-⊢∷ φ↜ ⊢tᵣ)
          eq
    unfold-⊢≡∷ φ↜ (K-β ⊢A ⊢t ok) =
      K-β (unfold-⊢ φ↜ ⊢A) (unfold-⊢∷ φ↜ ⊢t) ok
    unfold-⊢≡∷ φ↜ ([]-cong-β ⊢t eq ok) =
      []-cong-β (unfold-⊢∷ φ↜ ⊢t) eq ok
    unfold-⊢≡∷ φ↜ (equality-reflection ok ⊢Id ⊢t) =
      equality-reflection ok (unfold-⊢ φ↜ ⊢Id) (unfold-⊢∷ φ↜ ⊢t)

  opaque
    
    unfold-⇒∷ : φ » ∇′ ↜ ∇ → ∇ » Γ ⊢ t ⇒ u ∷ A → ∇′ » Γ ⊢ t ⇒ u ∷ A
    unfold-⇒∷ φ↜ (conv t⇒t′ A≡A′) =
      conv (unfold-⇒∷ φ↜ t⇒t′) (unfold-⊢≡ φ↜ A≡A′)
    unfold-⇒∷ φ↜ (δ-red ⊢Γ α↦t A≡A′ T≡T′) =
      δ-red (unfold-⊢′ φ↜ ⊢Γ) (unfold-↦∷∈ φ↜ α↦t) A≡A′ T≡T′
    unfold-⇒∷ φ↜ (app-subst t⇒t′ ⊢a) =
      app-subst (unfold-⇒∷ φ↜ t⇒t′) (unfold-⊢∷ φ↜ ⊢a)
    unfold-⇒∷ φ↜ (β-red ⊢A ⊢t ⊢x eq ok) =
      β-red (unfold-⊢ φ↜ ⊢A)
            (unfold-⊢∷ φ↜ ⊢t)
            (unfold-⊢∷ φ↜ ⊢x)
            eq ok
    unfold-⇒∷ φ↜ (fst-subst ⊢A t⇒t′) =
      fst-subst (unfold-⊢ φ↜ ⊢A) (unfold-⇒∷ φ↜ t⇒t′)
    unfold-⇒∷ φ↜ (snd-subst ⊢A t⇒t′) =
      snd-subst (unfold-⊢ φ↜ ⊢A) (unfold-⇒∷ φ↜ t⇒t′)
    unfold-⇒∷ φ↜ (Σ-β₁ ⊢A ⊢t ⊢t′ eq ok) =
      Σ-β₁ (unfold-⊢ φ↜ ⊢A)
          (unfold-⊢∷ φ↜ ⊢t)
          (unfold-⊢∷ φ↜ ⊢t′)
          eq ok
    unfold-⇒∷ φ↜ (Σ-β₂ ⊢A ⊢t ⊢t′ eq ok) =
      Σ-β₂ (unfold-⊢ φ↜ ⊢A)
          (unfold-⊢∷ φ↜ ⊢t)
          (unfold-⊢∷ φ↜ ⊢t′)
          eq ok
    unfold-⇒∷ φ↜ (prodrec-subst ⊢A ⊢a t⇒t′ ok) =
      prodrec-subst (unfold-⊢ φ↜ ⊢A)
                    (unfold-⊢∷ φ↜ ⊢a) 
                    (unfold-⇒∷ φ↜ t⇒t′) 
                    ok
    unfold-⇒∷ φ↜ (prodrec-β ⊢A ⊢t ⊢t₂ ⊢tᵣ eq ok) =
      prodrec-β (unfold-⊢ φ↜ ⊢A)
                (unfold-⊢∷ φ↜ ⊢t)
                (unfold-⊢∷ φ↜ ⊢t₂)
                (unfold-⊢∷ φ↜ ⊢tᵣ)
                eq ok
    unfold-⇒∷ φ↜ (natrec-subst ⊢t₀ ⊢tₛ t⇒t′) =
      natrec-subst (unfold-⊢∷ φ↜ ⊢t₀)
                  (unfold-⊢∷ φ↜ ⊢tₛ)
                  (unfold-⇒∷ φ↜ t⇒t′)
    unfold-⇒∷ φ↜ (natrec-zero ⊢t₀ ⊢tₛ) =
      natrec-zero (unfold-⊢∷ φ↜ ⊢t₀) (unfold-⊢∷ φ↜ ⊢tₛ)
    unfold-⇒∷ φ↜ (natrec-suc ⊢t₀ ⊢tₛ ⊢t) =
      natrec-suc (unfold-⊢∷ φ↜ ⊢t₀)
                (unfold-⊢∷ φ↜ ⊢tₛ)
                (unfold-⊢∷ φ↜ ⊢t)
    unfold-⇒∷ φ↜ (emptyrec-subst ⊢A t⇒t′) =
      emptyrec-subst (unfold-⊢ φ↜ ⊢A) (unfold-⇒∷ φ↜ t⇒t′)
    unfold-⇒∷ φ↜ (unitrec-subst ⊢A ⊢a t⇒t′ ok no-η) =
      unitrec-subst (unfold-⊢ φ↜ ⊢A)
                    (unfold-⊢∷ φ↜ ⊢a)
                    (unfold-⇒∷ φ↜ t⇒t′)
                    ok no-η
    unfold-⇒∷ φ↜ (unitrec-β ⊢A ⊢t ok no-η) =
      unitrec-β (unfold-⊢ φ↜ ⊢A) (unfold-⊢∷ φ↜ ⊢t) ok no-η
    unfold-⇒∷ φ↜ (unitrec-β-η ⊢A ⊢t ⊢tᵣ ok η) =
      unitrec-β-η (unfold-⊢ φ↜ ⊢A)
                  (unfold-⊢∷ φ↜ ⊢t)
                  (unfold-⊢∷ φ↜ ⊢tᵣ)
                  ok η
    unfold-⇒∷ φ↜ (J-subst ⊢t ⊢A ⊢r ⊢p w⇒w′) =
      J-subst (unfold-⊢∷ φ↜ ⊢t)
              (unfold-⊢ φ↜ ⊢A)
              (unfold-⊢∷ φ↜ ⊢r)
              (unfold-⊢∷ φ↜ ⊢p)
              (unfold-⇒∷ φ↜ w⇒w′)
    unfold-⇒∷ φ↜ (K-subst ⊢A ⊢r t⇒t′ ok) =
      K-subst (unfold-⊢ φ↜ ⊢A)
              (unfold-⊢∷ φ↜ ⊢r)
              (unfold-⇒∷ φ↜ t⇒t′)
              ok
    unfold-⇒∷ φ↜ ([]-cong-subst ⊢A ⊢a ⊢a′ t⇒t′ ok) =
      []-cong-subst (unfold-⊢ φ↜ ⊢A)
                    (unfold-⊢∷ φ↜ ⊢a)
                    (unfold-⊢∷ φ↜ ⊢a′)
                    (unfold-⇒∷ φ↜ t⇒t′)
                    ok
    unfold-⇒∷ φ↜ (J-β ⊢t ⊢t′ t≡t′ ⊢A A≡ ⊢tᵣ) =
      J-β (unfold-⊢∷ φ↜ ⊢t)
          (unfold-⊢∷ φ↜ ⊢t′)
          (unfold-⊢≡∷ φ↜ t≡t′)
          (unfold-⊢ φ↜ ⊢A)
          (unfold-⊢≡ φ↜ A≡)
          (unfold-⊢∷ φ↜ ⊢tᵣ)
    unfold-⇒∷ φ↜ (K-β ⊢A ⊢t ok) =
      K-β (unfold-⊢ φ↜ ⊢A) (unfold-⊢∷ φ↜ ⊢t) ok
    unfold-⇒∷ φ↜ ([]-cong-β ⊢A ⊢t ⊢t′ t≡t′ ok) =
      []-cong-β (unfold-⊢ φ↜ ⊢A)
                (unfold-⊢∷ φ↜ ⊢t)
                (unfold-⊢∷ φ↜ ⊢t′)
                (unfold-⊢≡∷ φ↜ t≡t′)
                ok

  opaque

    unfold-⇒ : φ » ∇′ ↜ ∇ → ∇ » Γ ⊢ A ⇒ B → ∇′ » Γ ⊢ A ⇒ B
    unfold-⇒ φ↜ (univ A⇒B) = univ (unfold-⇒∷ φ↜ A⇒B)

  opaque

    unfold-⇒* : φ » ∇′ ↜ ∇ → ∇ » Γ ⊢ A ⇒* B → ∇′ » Γ ⊢ A ⇒* B
    unfold-⇒* φ↜ (id ⊢A)      = id (unfold-⊢ φ↜ ⊢A)
    unfold-⇒* φ↜ (A⇒X ⇨ X⇒*B) = unfold-⇒ φ↜ A⇒X ⇨ unfold-⇒* φ↜ X⇒*B

  opaque

    unfold-⇒*∷ : φ » ∇′ ↜ ∇ → ∇ » Γ ⊢ t ⇒* u ∷ A → ∇′ » Γ ⊢ t ⇒* u ∷ A
    unfold-⇒*∷ φ↜ (id ⊢t)      = id (unfold-⊢∷ φ↜ ⊢t)
    unfold-⇒*∷ φ↜ (t⇒x ⇨ x⇒*u) = unfold-⇒∷ φ↜ t⇒x ⇨ unfold-⇒*∷ φ↜ x⇒*u
