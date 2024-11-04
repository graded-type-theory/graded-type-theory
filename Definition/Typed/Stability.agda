------------------------------------------------------------------------
-- A direct proof of stability
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Stability
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R
open import Definition.Untyped M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ

private variable
  n       : Nat
  x       : Fin _
  Γ Δ Η   : Con Term _
  A B t u : Term _
  σ σ₁ σ₂ : Subst _ _

-- Equality of contexts.

infix 24 _∙⟨_∣_⟩

data ⊢_≡_ : (_ _ : Con Term n) → Set a where
  ε       : ⊢ ε ≡ ε
  _∙⟨_∣_⟩ : ⊢ Γ ≡ Δ → Δ ⊢ B → Δ ⊢ A ≡ B → ⊢ Γ ∙ A ≡ Δ ∙ B

opaque

  -- A variant of _∙⟨_∣_⟩.

  infix 24 _∙⟨_⟩

  _∙⟨_⟩ : ⊢ Γ ≡ Δ → Δ ⊢ A → ⊢ Γ ∙ A ≡ Δ ∙ A
  Γ≡Δ ∙⟨ ⊢A ⟩ = Γ≡Δ ∙⟨ ⊢A ∣ refl ⊢A ⟩

opaque

  -- A well-formedness lemma for ⊢_≡_.

  wf-⊢≡ʳ : ⊢ Γ ≡ Δ → ⊢ Δ
  wf-⊢≡ʳ ε                 = ε
  wf-⊢≡ʳ (Γ≡Δ ∙⟨ ⊢B ∣ _ ⟩) = wf-⊢≡ʳ Γ≡Δ ∙ ⊢B

opaque

  -- Reflexivity for ⊢_≡_.

  reflConEq : ⊢ Γ → ⊢ Γ ≡ Γ
  reflConEq ε         = ε
  reflConEq (⊢Γ ∙ ⊢A) = reflConEq ⊢Γ ∙⟨ ⊢A ⟩

opaque

  -- Stability for _∷_∈_.

  stability-⊢∈ :
    ⊢ Γ ≡ Δ → x ∷ A ∈ Γ →
    ∃ λ B → Δ ⊢ A ≡ B × x ∷ B ∈ Δ
  stability-⊢∈ (Γ≡Δ ∙⟨ ⊢B ∣ A≡B ⟩) here =
    _ , wkEq₁ ⊢B A≡B , here
  stability-⊢∈ (Γ≡Δ ∙⟨ ⊢B ∣ _ ⟩) (there x∈) =
    Σ.map wk1 (Σ.map (wkEq₁ ⊢B) there) $
    stability-⊢∈ Γ≡Δ x∈

opaque mutual

  -- Stability for _⊢_.

  stability-⊢ : ⊢ Γ ≡ Δ → Γ ⊢ A → Δ ⊢ A
  stability-⊢ Γ≡Δ (Uⱼ _) =
    Uⱼ (wf-⊢≡ʳ Γ≡Δ)
  stability-⊢ Γ≡Δ (univ ⊢A) =
    univ (stability-⊢∷ Γ≡Δ ⊢A)
  stability-⊢ Γ≡Δ (ΠΣⱼ ⊢A ⊢B ok) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    ΠΣⱼ ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) ok
  stability-⊢ Γ≡Δ (Emptyⱼ _) =
    Emptyⱼ (wf-⊢≡ʳ Γ≡Δ)
  stability-⊢ Γ≡Δ (Unitⱼ _ ok) =
    Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok
  stability-⊢ Γ≡Δ (ℕⱼ _) =
    ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
  stability-⊢ Γ≡Δ (Idⱼ ⊢t ⊢u) =
    Idⱼ (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u)

  -- Stability for _⊢_≡_.

  stability-⊢≡ : ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B → Δ ⊢ A ≡ B
  stability-⊢≡ Γ≡Δ (refl ⊢A) =
    refl (stability-⊢ Γ≡Δ ⊢A)
  stability-⊢≡ Γ≡Δ (sym B≡A) =
    sym (stability-⊢≡ Γ≡Δ B≡A)
  stability-⊢≡ Γ≡Δ (trans A≡B B≡C) =
    trans (stability-⊢≡ Γ≡Δ A≡B) (stability-⊢≡ Γ≡Δ B≡C)
  stability-⊢≡ Γ≡Δ (univ A≡B) =
    univ (stability-⊢≡∷ Γ≡Δ A≡B)
  stability-⊢≡ Γ≡Δ (ΠΣ-cong ⊢A₁ A₁≡B₁ A₂≡B₂ ok) =
    let ⊢A₁′ = stability-⊢ Γ≡Δ ⊢A₁ in
    ΠΣ-cong ⊢A₁′ (stability-⊢≡ Γ≡Δ A₁≡B₁)
      (stability-⊢≡ (Γ≡Δ ∙⟨ ⊢A₁′ ⟩) A₂≡B₂) ok
  stability-⊢≡ Γ≡Δ (Id-cong A≡B t₁≡u₁ t₂≡u₂) =
    Id-cong (stability-⊢≡ Γ≡Δ A≡B) (stability-⊢≡∷ Γ≡Δ t₁≡u₁)
      (stability-⊢≡∷ Γ≡Δ t₂≡u₂)

  -- Stability for _⊢_∷_.

  stability-⊢∷ : ⊢ Γ ≡ Δ → Γ ⊢ t ∷ A → Δ ⊢ t ∷ A
  stability-⊢∷ Γ≡Δ (conv ⊢t B≡A) =
    conv (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢≡ Γ≡Δ B≡A)
  stability-⊢∷ Γ≡Δ (var _ x∈Γ) =
    let _ , A≡B , x∈Δ = stability-⊢∈ Γ≡Δ x∈Γ in
    conv (var (wf-⊢≡ʳ Γ≡Δ) x∈Δ) (sym A≡B)
  stability-⊢∷ Γ≡Δ (Uⱼ _) =
    Uⱼ (wf-⊢≡ʳ Γ≡Δ)
  stability-⊢∷ Γ≡Δ (ΠΣⱼ ⊢A ⊢B ok) =
    let ⊢A′ = stability-⊢∷ Γ≡Δ ⊢A in
    ΠΣⱼ ⊢A′ (stability-⊢∷ (Γ≡Δ ∙⟨ univ ⊢A′ ⟩) ⊢B) ok
  stability-⊢∷ Γ≡Δ (lamⱼ ⊢A ⊢t ok) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    lamⱼ ⊢A′ (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢t) ok
  stability-⊢∷ Γ≡Δ (⊢t ∘ⱼ ⊢u) =
    stability-⊢∷ Γ≡Δ ⊢t ∘ⱼ stability-⊢∷ Γ≡Δ ⊢u
  stability-⊢∷ Γ≡Δ (prodⱼ ⊢A ⊢B ⊢t ⊢u ok) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    prodⱼ ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t)
      (stability-⊢∷ Γ≡Δ ⊢u) ok
  stability-⊢∷ Γ≡Δ (fstⱼ ⊢A ⊢B ⊢t) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    fstⱼ ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t)
  stability-⊢∷ Γ≡Δ (sndⱼ ⊢A ⊢B ⊢t) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    sndⱼ ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t)
  stability-⊢∷ Γ≡Δ (prodrecⱼ ⊢A ⊢B ⊢C ⊢t ⊢u ok) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A
        ⊢B′ = stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B
        ⊢Σ  = ΠΣⱼ ⊢A′ ⊢B′ ok
    in
    prodrecⱼ ⊢A′ ⊢B′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢Σ ⟩) ⊢C)
      (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ ⊢B′ ⟩) ⊢u) ok
  stability-⊢∷ Γ≡Δ (Emptyⱼ _) =
    Emptyⱼ (wf-⊢≡ʳ Γ≡Δ)
  stability-⊢∷ Γ≡Δ (emptyrecⱼ ⊢A ⊢t) =
    emptyrecⱼ (stability-⊢ Γ≡Δ ⊢A) (stability-⊢∷ Γ≡Δ ⊢t)
  stability-⊢∷ Γ≡Δ (Unitⱼ _ ok) =
    Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok
  stability-⊢∷ Γ≡Δ (starⱼ _ ok) =
    starⱼ (wf-⊢≡ʳ Γ≡Δ) ok
  stability-⊢∷ Γ≡Δ (unitrecⱼ ⊢A ⊢t ⊢u ok) =
    unitrecⱼ (stability-⊢ (Γ≡Δ ∙⟨ Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok ⟩) ⊢A)
      (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u) ok
  stability-⊢∷ Γ≡Δ (ℕⱼ _) =
    ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
  stability-⊢∷ Γ≡Δ (zeroⱼ _) =
    zeroⱼ (wf-⊢≡ʳ Γ≡Δ)
  stability-⊢∷ Γ≡Δ (sucⱼ ⊢t) =
    sucⱼ (stability-⊢∷ Γ≡Δ ⊢t)
  stability-⊢∷ Γ≡Δ (natrecⱼ ⊢A ⊢t ⊢u ⊢v) =
    let ⊢ℕ  = ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
        ⊢A′ = stability-⊢ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A
    in
    natrecⱼ ⊢A′ (stability-⊢∷ Γ≡Δ ⊢t)
      (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A′ ⟩) ⊢u)
      (stability-⊢∷ Γ≡Δ ⊢v)
  stability-⊢∷ Γ≡Δ (Idⱼ ⊢A ⊢t ⊢u) =
    Idⱼ (stability-⊢∷ Γ≡Δ ⊢A) (stability-⊢∷ Γ≡Δ ⊢t)
      (stability-⊢∷ Γ≡Δ ⊢u)
  stability-⊢∷ Γ≡Δ (rflⱼ ⊢t) =
    rflⱼ (stability-⊢∷ Γ≡Δ ⊢t)
  stability-⊢∷ Γ≡Δ (Jⱼ ⊢A ⊢t ⊢B ⊢u ⊢v ⊢w) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A
        ⊢t′ = stability-⊢∷ Γ≡Δ ⊢t
    in
    Jⱼ ⊢A′ ⊢t′
      (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ Idⱼ (wkTerm₁ ⊢A′ ⊢t′) (var₀ ⊢A′) ⟩)
         ⊢B)
      (stability-⊢∷ Γ≡Δ ⊢u) (stability-⊢∷ Γ≡Δ ⊢v) (stability-⊢∷ Γ≡Δ ⊢w)
  stability-⊢∷ Γ≡Δ (Kⱼ ⊢t ⊢B ⊢u ⊢v ok) =
    let ⊢t′ = stability-⊢∷ Γ≡Δ ⊢t in
    Kⱼ ⊢t′ (stability-⊢ (Γ≡Δ ∙⟨ Idⱼ ⊢t′ ⊢t′ ⟩) ⊢B)
      (stability-⊢∷ Γ≡Δ ⊢u) (stability-⊢∷ Γ≡Δ ⊢v) ok
  stability-⊢∷ Γ≡Δ ([]-congⱼ ⊢t ⊢u ⊢v ok) =
    []-congⱼ (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u)
      (stability-⊢∷ Γ≡Δ ⊢v) ok

  -- Stability for _⊢_≡_∷_.

  stability-⊢≡∷ : ⊢ Γ ≡ Δ → Γ ⊢ t ≡ u ∷ A → Δ ⊢ t ≡ u ∷ A
  stability-⊢≡∷ Γ≡Δ (refl ⊢t) =
    refl (stability-⊢∷ Γ≡Δ ⊢t)
  stability-⊢≡∷ Γ≡Δ (sym t₂≡t₁) =
    sym (stability-⊢≡∷ Γ≡Δ t₂≡t₁)
  stability-⊢≡∷ Γ≡Δ (trans t₁≡t₂ t₂≡t₃) =
    trans (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡∷ Γ≡Δ t₂≡t₃)
  stability-⊢≡∷ Γ≡Δ (conv t₁≡t₂ B≡A) =
    conv (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡ Γ≡Δ B≡A)
  stability-⊢≡∷ Γ≡Δ (ΠΣ-cong ⊢A₁ A₁≡A₂ B₁≡B₂ ok) =
    let ⊢A₁′ = stability-⊢ Γ≡Δ ⊢A₁ in
    ΠΣ-cong ⊢A₁′ (stability-⊢≡∷ Γ≡Δ A₁≡A₂)
      (stability-⊢≡∷ (Γ≡Δ ∙⟨ ⊢A₁′ ⟩) B₁≡B₂) ok
  stability-⊢≡∷ Γ≡Δ (app-cong t₁≡t₂ u₁≡u₂) =
    app-cong (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡∷ Γ≡Δ u₁≡u₂)
  stability-⊢≡∷ Γ≡Δ (β-red ⊢A ⊢B ⊢t ⊢u eq ok) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    β-red ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B)
      (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢t) (stability-⊢∷ Γ≡Δ ⊢u) eq ok
  stability-⊢≡∷ Γ≡Δ (η-eq ⊢A ⊢t₁ ⊢t₂ t₁0≡t₂0) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    η-eq ⊢A′ (stability-⊢∷ Γ≡Δ ⊢t₁) (stability-⊢∷ Γ≡Δ ⊢t₂)
      (stability-⊢≡∷ (Γ≡Δ ∙⟨ ⊢A′ ⟩) t₁0≡t₂0)
  stability-⊢≡∷ Γ≡Δ (fst-cong ⊢A ⊢B t₁≡t₂) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    fst-cong ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B)
      (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
  stability-⊢≡∷ Γ≡Δ (snd-cong ⊢A ⊢B t₁≡t₂) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    snd-cong ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B)
      (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
  stability-⊢≡∷ Γ≡Δ (Σ-β₁ ⊢A ⊢B ⊢t₁ ⊢t₂ eq ok) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    Σ-β₁ ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t₁)
      (stability-⊢∷ Γ≡Δ ⊢t₂) eq ok
  stability-⊢≡∷ Γ≡Δ (Σ-β₂ ⊢A ⊢B ⊢t₁ ⊢t₂ eq ok) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    Σ-β₂ ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t₁)
      (stability-⊢∷ Γ≡Δ ⊢t₂) eq ok
  stability-⊢≡∷ Γ≡Δ (Σ-η ⊢A ⊢B ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    Σ-η ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t₁)
      (stability-⊢∷ Γ≡Δ ⊢t₂) (stability-⊢≡∷ Γ≡Δ fst-t₁≡fst-t₂)
      (stability-⊢≡∷ Γ≡Δ snd-t₁≡snd-t₂)
  stability-⊢≡∷ Γ≡Δ (prod-cong ⊢A ⊢B t₁≡t₂ u₁≡u₂ ok) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A in
    prod-cong ⊢A′ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B)
      (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡∷ Γ≡Δ u₁≡u₂) ok
  stability-⊢≡∷ Γ≡Δ (prodrec-cong ⊢A ⊢B C₁≡C₂ t₁≡t₂ u₁≡u₂ ok) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A
        ⊢B′ = stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B
    in
    prodrec-cong ⊢A′ ⊢B′ (stability-⊢≡ (Γ≡Δ ∙⟨ ΠΣⱼ ⊢A′ ⊢B′ ok ⟩) C₁≡C₂)
      (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (stability-⊢≡∷ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ ⊢B′ ⟩) u₁≡u₂) ok
  stability-⊢≡∷ Γ≡Δ (prodrec-β ⊢A ⊢B ⊢C ⊢t ⊢u ⊢v eq ok) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A
        ⊢B′ = stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B
    in
    prodrec-β ⊢A′ ⊢B′ (stability-⊢ (Γ≡Δ ∙⟨ ΠΣⱼ ⊢A′ ⊢B′ ok ⟩) ⊢C)
      (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u)
      (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ ⊢B′ ⟩) ⊢v) eq ok
  stability-⊢≡∷ Γ≡Δ (emptyrec-cong A₁≡A₂ t₁≡t₂) =
    emptyrec-cong (stability-⊢≡ Γ≡Δ A₁≡A₂) (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
  stability-⊢≡∷ Γ≡Δ (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ ok no-η) =
    unitrec-cong (stability-⊢≡ (Γ≡Δ ∙⟨ Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok ⟩) A₁≡A₂)
      (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡∷ Γ≡Δ u₁≡u₂) ok no-η
  stability-⊢≡∷ Γ≡Δ (unitrec-β ⊢A ⊢t ok no-η) =
    unitrec-β (stability-⊢ (Γ≡Δ ∙⟨ Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok ⟩) ⊢A)
      (stability-⊢∷ Γ≡Δ ⊢t) ok no-η
  stability-⊢≡∷ Γ≡Δ (unitrec-β-η ⊢A ⊢t ⊢u ok no-η) =
    unitrec-β-η (stability-⊢ (Γ≡Δ ∙⟨ Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok ⟩) ⊢A)
      (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u) ok no-η
  stability-⊢≡∷ Γ≡Δ (η-unit ⊢t₁ ⊢t₂ η) =
    η-unit (stability-⊢∷ Γ≡Δ ⊢t₁) (stability-⊢∷ Γ≡Δ ⊢t₂) η
  stability-⊢≡∷ Γ≡Δ (suc-cong t₁≡t₂) =
    suc-cong (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
  stability-⊢≡∷ Γ≡Δ (natrec-cong ⊢A₁ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) =
    let ⊢ℕ   = ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
        ⊢A₁′ = stability-⊢ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A₁
    in
    natrec-cong ⊢A₁′ (stability-⊢≡ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) A₁≡A₂)
      (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (stability-⊢≡∷ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A₁′ ⟩) u₁≡u₂)
      (stability-⊢≡∷ Γ≡Δ v₁≡v₂)
  stability-⊢≡∷ Γ≡Δ (natrec-zero ⊢A ⊢t ⊢u) =
    let ⊢ℕ  = ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
        ⊢A′ = stability-⊢ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A
    in
    natrec-zero ⊢A′ (stability-⊢∷ Γ≡Δ ⊢t)
      (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A′ ⟩) ⊢u)
  stability-⊢≡∷ Γ≡Δ (natrec-suc ⊢A ⊢t ⊢u ⊢v) =
    let ⊢ℕ  = ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
        ⊢A′ = stability-⊢ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A
    in
    natrec-suc ⊢A′ (stability-⊢∷ Γ≡Δ ⊢t)
      (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A′ ⟩) ⊢u) (stability-⊢∷ Γ≡Δ ⊢v)
  stability-⊢≡∷ Γ≡Δ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-cong (stability-⊢≡∷ Γ≡Δ A₁≡A₂) (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (stability-⊢≡∷ Γ≡Δ u₁≡u₂)
  stability-⊢≡∷
    Γ≡Δ (J-cong ⊢A₁ A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    let ⊢A₁′ = stability-⊢ Γ≡Δ ⊢A₁
        ⊢t₁′ = stability-⊢∷ Γ≡Δ ⊢t₁
    in
    J-cong ⊢A₁′ (stability-⊢≡ Γ≡Δ A₁≡A₂) ⊢t₁′ (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (stability-⊢≡
         (Γ≡Δ ∙⟨ ⊢A₁′ ⟩ ∙⟨ Idⱼ (wkTerm₁ ⊢A₁′ ⊢t₁′) (var₀ ⊢A₁′) ⟩)
         B₁≡B₂)
      (stability-⊢≡∷ Γ≡Δ u₁≡u₂) (stability-⊢≡∷ Γ≡Δ v₁≡v₂)
      (stability-⊢≡∷ Γ≡Δ w₁≡w₂)
  stability-⊢≡∷ Γ≡Δ (J-β ⊢A ⊢t ⊢B ⊢u eq) =
    let ⊢A′ = stability-⊢ Γ≡Δ ⊢A
        ⊢t′ = stability-⊢∷ Γ≡Δ ⊢t
    in
    J-β ⊢A′ ⊢t′
      (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ Idⱼ (wkTerm₁ ⊢A′ ⊢t′) (var₀ ⊢A′) ⟩)
         ⊢B)
      (stability-⊢∷ Γ≡Δ ⊢u) eq
  stability-⊢≡∷ Γ≡Δ (K-cong A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) =
    let ⊢t₁′ = stability-⊢∷ Γ≡Δ ⊢t₁ in
    K-cong (stability-⊢≡ Γ≡Δ A₁≡A₂) ⊢t₁′ (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (stability-⊢≡ (Γ≡Δ ∙⟨ Idⱼ ⊢t₁′ ⊢t₁′ ⟩) B₁≡B₂)
      (stability-⊢≡∷ Γ≡Δ u₁≡u₂) (stability-⊢≡∷ Γ≡Δ v₁≡v₂) ok
  stability-⊢≡∷ Γ≡Δ (K-β ⊢t ⊢B ⊢u ok) =
    let ⊢t′ = stability-⊢∷ Γ≡Δ ⊢t in
    K-β ⊢t′ (stability-⊢ (Γ≡Δ ∙⟨ Idⱼ ⊢t′ ⊢t′ ⟩) ⊢B)
      (stability-⊢∷ Γ≡Δ ⊢u) ok
  stability-⊢≡∷ Γ≡Δ ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) =
    []-cong-cong (stability-⊢≡ Γ≡Δ A₁≡A₂) (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (stability-⊢≡∷ Γ≡Δ u₁≡u₂) (stability-⊢≡∷ Γ≡Δ v₁≡v₂) ok
  stability-⊢≡∷ Γ≡Δ ([]-cong-β ⊢t eq ok) =
    []-cong-β (stability-⊢∷ Γ≡Δ ⊢t) eq ok

opaque

  -- Stability for _⊢ˢ_∷_.

  stability-⊢ˢ∷ˡ : ⊢ Δ ≡ Η → Δ ⊢ˢ σ ∷ Γ → Η ⊢ˢ σ ∷ Γ
  stability-⊢ˢ∷ˡ _   id        = id
  stability-⊢ˢ∷ˡ Δ≡Η (⊢σ , ⊢t) =
    stability-⊢ˢ∷ˡ Δ≡Η ⊢σ , stability-⊢∷ Δ≡Η ⊢t

opaque

  -- Stability for _⊢ˢ_≡_∷_.

  stability-⊢ˢ≡∷ˡ : ⊢ Δ ≡ Η → Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → Η ⊢ˢ σ₁ ≡ σ₂ ∷ Γ
  stability-⊢ˢ≡∷ˡ _   id              = id
  stability-⊢ˢ≡∷ˡ Δ≡Η (σ₁≡σ₂ , t₁≡t₂) =
    stability-⊢ˢ≡∷ˡ Δ≡Η σ₁≡σ₂ , stability-⊢≡∷ Δ≡Η t₁≡t₂
