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
open import Definition.Typed.Size R
open import Definition.Typed.Weakening R
open import Definition.Untyped M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Size

private variable
  n       : Nat
  x       : Fin _
  Γ Δ Η   : Con Term _
  A B t u : Term _
  σ σ₁ σ₂ : Subst _ _
  s s₂    : Size

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

private

  -- Below several properties are proved simultaneously using
  -- well-founded induction. The properties are collected in the
  -- record type P.

  record P (s : Size) : Set a where
    no-eta-equality
    field
      stability-⊢ :
        ⊢ Γ ≡ Δ →
        (⊢A : Γ ⊢ A) →
        size-⊢ ⊢A PE.≡ s →
        Δ ⊢ A
      stability-⊢≡ :
        ⊢ Γ ≡ Δ →
        (A≡B : Γ ⊢ A ≡ B) →
        size-⊢≡ A≡B PE.≡ s →
        Δ ⊢ A ≡ B
      stability-⊢∷ :
        ⊢ Γ ≡ Δ →
        (⊢t : Γ ⊢ t ∷ A) →
        size-⊢∷ ⊢t PE.≡ s →
        Δ ⊢ t ∷ A
      stability-⊢≡∷ :
        ⊢ Γ ≡ Δ →
        (t≡u : Γ ⊢ t ≡ u ∷ A) →
        size-⊢≡∷ t≡u PE.≡ s →
        Δ ⊢ t ≡ u ∷ A

-- Variants of the fields of P.

private module Variants (hyp : ∀ {s₁} → s₁ <ˢ s₂ → P s₁) where

  opaque

    -- Variants of the fields of P.

    stability-⊢′ :
      ⊢ Γ ≡ Δ →
      (⊢A : Γ ⊢ A) →
      size-⊢ ⊢A <ˢ s₂ →
      Δ ⊢ A
    stability-⊢′ Γ≡Δ ⊢A <s₂ = P.stability-⊢ (hyp <s₂) Γ≡Δ ⊢A PE.refl

    stability-⊢≡′ :
      ⊢ Γ ≡ Δ →
      (A≡B : Γ ⊢ A ≡ B) →
      size-⊢≡ A≡B <ˢ s₂ →
      Δ ⊢ A ≡ B
    stability-⊢≡′ Γ≡Δ A≡B <s₂ = P.stability-⊢≡ (hyp <s₂) Γ≡Δ A≡B PE.refl

    stability-⊢∷′ :
      ⊢ Γ ≡ Δ →
      (⊢t : Γ ⊢ t ∷ A) →
      size-⊢∷ ⊢t <ˢ s₂ →
      Δ ⊢ t ∷ A
    stability-⊢∷′ Γ≡Δ ⊢t <s₂ = P.stability-⊢∷ (hyp <s₂) Γ≡Δ ⊢t PE.refl

    stability-⊢≡∷′ :
      ⊢ Γ ≡ Δ →
      (t≡u : Γ ⊢ t ≡ u ∷ A) →
      size-⊢≡∷ t≡u <ˢ s₂ →
      Δ ⊢ t ≡ u ∷ A
    stability-⊢≡∷′ Γ≡Δ t≡u <s₂ =
      P.stability-⊢≡∷ (hyp <s₂) Γ≡Δ t≡u PE.refl

-- The type P s is inhabited for every s.

private module Inhabited where

  opaque
    unfolding size-⊢

    -- Stability for _⊢_.

    stability-⊢ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ⊢ Γ ≡ Δ →
      (⊢A : Γ ⊢ A) →
      size-⊢ ⊢A PE.≡ s₂ →
      Δ ⊢ A
    stability-⊢ hyp Γ≡Δ = let open Variants hyp in λ where
      (Uⱼ _) _ →
        Uⱼ (wf-⊢≡ʳ Γ≡Δ)
      (univ ⊢A) PE.refl →
        univ (stability-⊢∷′ Γ≡Δ ⊢A (↙ ◻))
      (ΠΣⱼ ⊢B ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        ΠΣⱼ (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ◻)) ok
      (Emptyⱼ _) _ →
        Emptyⱼ (wf-⊢≡ʳ Γ≡Δ)
      (Unitⱼ _ ok) _ →
        Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok
      (ℕⱼ _) _ →
        ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
      (Idⱼ ⊢t ⊢u) PE.refl →
        Idⱼ (stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻)) (stability-⊢∷′ Γ≡Δ ⊢u (↘ ◻))

  opaque
    unfolding size-⊢≡

    -- Stability for _⊢_≡_.

    stability-⊢≡ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ⊢ Γ ≡ Δ →
      (A≡B : Γ ⊢ A ≡ B) →
      size-⊢≡ A≡B PE.≡ s₂ →
      Δ ⊢ A ≡ B
    stability-⊢≡ hyp Γ≡Δ = let open Variants hyp in λ where
      (refl ⊢A) PE.refl →
        refl (stability-⊢′ Γ≡Δ ⊢A (↙ ◻))
      (sym B≡A) PE.refl →
        sym (stability-⊢≡′ Γ≡Δ B≡A (↙ ◻))
      (trans A≡B B≡C) PE.refl →
        trans (stability-⊢≡′ Γ≡Δ A≡B (↙ ◻))
          (stability-⊢≡′ Γ≡Δ B≡C (↘ ◻))
      (univ A≡B) PE.refl →
        univ (stability-⊢≡∷′ Γ≡Δ A≡B (↙ ◻))
      (ΠΣ-cong A₁≡B₁ A₂≡B₂ ok) PE.refl →
        let _ , (⊢A₁ , A₁<) = ∙⊢≡→⊢-<ˢ A₂≡B₂
            ⊢A₁′            = stability-⊢′ Γ≡Δ ⊢A₁ (<ˢ-trans A₁< (↘ ◻))
        in
        ΠΣ-cong (stability-⊢≡′ Γ≡Δ A₁≡B₁ (↙ ◻))
          (stability-⊢≡′ (Γ≡Δ ∙⟨ ⊢A₁′ ⟩) A₂≡B₂ (↘ ◻)) ok
      (Id-cong A≡B t₁≡u₁ t₂≡u₂) PE.refl →
        Id-cong (stability-⊢≡′ Γ≡Δ A≡B (↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₁≡u₁ (↘ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₂≡u₂ (↘ ↘ ◻))

  opaque
    unfolding size-⊢∷

    -- Stability for _⊢_∷_.

    stability-⊢∷ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ⊢ Γ ≡ Δ →
      (⊢t : Γ ⊢ t ∷ A) →
      size-⊢∷ ⊢t PE.≡ s₂ →
      Δ ⊢ t ∷ A
    stability-⊢∷ hyp Γ≡Δ = let open Variants hyp in λ where
      (conv ⊢t B≡A) PE.refl →
        conv (stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻)) (stability-⊢≡′ Γ≡Δ B≡A (↘ ◻))
      (var _ x∈Γ) _ →
        let _ , A≡B , x∈Δ = stability-⊢∈ Γ≡Δ x∈Γ in
        conv (var (wf-⊢≡ʳ Γ≡Δ) x∈Δ) (sym A≡B)
      (Uⱼ _) _ →
        Uⱼ (wf-⊢≡ʳ Γ≡Δ)
      (ΠΣⱼ ⊢A ⊢B ok) PE.refl →
        let ⊢A′ = stability-⊢∷′ Γ≡Δ ⊢A (↙ ◻) in
        ΠΣⱼ ⊢A′ (stability-⊢∷′ (Γ≡Δ ∙⟨ univ ⊢A′ ⟩) ⊢B (↘ ◻)) ok
      (lamⱼ ⊢t ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢∷→⊢-<ˢ ⊢t
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        lamⱼ (stability-⊢∷′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢t (↙ ◻)) ok
      (⊢t ∘ⱼ ⊢u) PE.refl →
        stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻) ∘ⱼ stability-⊢∷′ Γ≡Δ ⊢u (↘ ◻)
      (prodⱼ ⊢B ⊢t ⊢u ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        prodⱼ (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t (↘ ↙ ◻)) (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↘ ◻))
          ok
      (fstⱼ ⊢B ⊢t) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        fstⱼ (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t (↘ ◻))
      (sndⱼ ⊢B ⊢t) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        sndⱼ (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t (↘ ◻))
      (prodrecⱼ ⊢C ⊢t ⊢u ok) PE.refl →
        let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢∷→⊢-<ˢ ⊢u
            ⊢A′                       = stability-⊢′ Γ≡Δ ⊢A $
                                        <ˢ-trans A< (↘ ↘ ◻)
            ⊢B′                       = stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B $
                                        <ˢ-trans B< (↘ ↘ ◻)
        in
        prodrecⱼ (stability-⊢′ (Γ≡Δ ∙⟨ ΠΣⱼ ⊢B′ ok ⟩) ⊢C (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t (↘ ↙ ◻))
          (stability-⊢∷′ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ ⊢B′ ⟩) ⊢u (↘ ↘ ◻)) ok
      (Emptyⱼ _) _ →
        Emptyⱼ (wf-⊢≡ʳ Γ≡Δ)
      (emptyrecⱼ ⊢A ⊢t) PE.refl →
        emptyrecⱼ (stability-⊢′ Γ≡Δ ⊢A (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t (↘ ◻))
      (Unitⱼ _ ok) _ →
        Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok
      (starⱼ _ ok) _ →
        starⱼ (wf-⊢≡ʳ Γ≡Δ) ok
      (unitrecⱼ ⊢A ⊢t ⊢u ok) PE.refl →
        unitrecⱼ
          (stability-⊢′ (Γ≡Δ ∙⟨ Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok ⟩) ⊢A (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t (↘ ↙ ◻)) (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↘ ◻))
          ok
      (ℕⱼ _) _ →
        ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
      (zeroⱼ _) _ →
        zeroⱼ (wf-⊢≡ʳ Γ≡Δ)
      (sucⱼ ⊢t) PE.refl →
        sucⱼ (stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻))
      (natrecⱼ ⊢t ⊢u ⊢v) PE.refl →
        let ⊢ℕ            = ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
            _ , (⊢A , A<) = ∙⊢∷→⊢-<ˢ ⊢u
            ⊢A′           = stability-⊢′ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A $
                            <ˢ-trans A< (↘ ↙ ◻)
        in
        natrecⱼ (stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻))
          (stability-⊢∷′ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A′ ⟩) ⊢u (↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢v (↘ ↘ ◻))
      (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
        Idⱼ (stability-⊢∷′ Γ≡Δ ⊢A (↙ ◻)) (stability-⊢∷′ Γ≡Δ ⊢t (↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↘ ◻))
      (rflⱼ ⊢t) PE.refl →
        rflⱼ (stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻))
      (Jⱼ ⊢t ⊢B ⊢u ⊢v ⊢w) PE.refl →
        let _ , (⊢A , A<) , _ = ∙∙⊢→⊢-<ˢ ⊢B
            ⊢A′               = stability-⊢′ Γ≡Δ ⊢A $
                                <ˢ-trans A< (↙ ↘ ◻)
            ⊢t′               = stability-⊢∷′ Γ≡Δ ⊢t (↙ ↙ ◻)
        in
        Jⱼ ⊢t′
          (stability-⊢′
             (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ Idⱼ (wkTerm₁ ⊢A′ ⊢t′) (var₀ ⊢A′) ⟩) ⊢B
             (↙ ↘ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢v (↘ ↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢w (↘ ↘ ↘ ◻))
      (Kⱼ ⊢t ⊢B ⊢u ⊢v ok) PE.refl →
        let ⊢t′ = stability-⊢∷′ Γ≡Δ ⊢t (↙ ↙ ◻) in
        Kⱼ ⊢t′ (stability-⊢′ (Γ≡Δ ∙⟨ Idⱼ ⊢t′ ⊢t′ ⟩) ⊢B (↙ ↘ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↙ ◻)) (stability-⊢∷′ Γ≡Δ ⊢v (↘ ↘ ◻))
          ok
      ([]-congⱼ ⊢t ⊢u ⊢v ok) PE.refl →
        []-congⱼ (stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↙ ◻)) (stability-⊢∷′ Γ≡Δ ⊢v (↘ ↘ ◻))
          ok

  opaque
    unfolding size-⊢≡∷

    -- Stability for _⊢_≡_∷_.

    stability-⊢≡∷ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ⊢ Γ ≡ Δ →
      (t≡u : Γ ⊢ t ≡ u ∷ A) →
      size-⊢≡∷ t≡u PE.≡ s₂ →
      Δ ⊢ t ≡ u ∷ A
    stability-⊢≡∷ hyp Γ≡Δ = let open Variants hyp in λ where
      (refl ⊢t) PE.refl →
        refl (stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻))
      (sym t₂≡t₁) PE.refl →
        sym (stability-⊢≡∷′ Γ≡Δ t₂≡t₁ (↙ ◻))
      (trans t₁≡t₂ t₂≡t₃) PE.refl →
        trans (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₂≡t₃ (↘ ◻))
      (conv t₁≡t₂ B≡A) PE.refl →
        conv (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↙ ◻))
          (stability-⊢≡′ Γ≡Δ B≡A (↘ ◻))
      (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) PE.refl →
        let _ , (⊢A₁ , A₁<) = ∙⊢≡∷→⊢-<ˢ B₁≡B₂
            ⊢A₁′            = stability-⊢′ Γ≡Δ ⊢A₁ (<ˢ-trans A₁< (↘ ◻))
        in
        ΠΣ-cong (stability-⊢≡∷′ Γ≡Δ A₁≡A₂ (↙ ◻))
          (stability-⊢≡∷′ (Γ≡Δ ∙⟨ ⊢A₁′ ⟩) B₁≡B₂ (↘ ◻)) ok
      (app-cong t₁≡t₂ u₁≡u₂) PE.refl →
        app-cong (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ u₁≡u₂ (↘ ◻))
      (β-red ⊢B ⊢t ⊢u eq ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        β-red (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ◻))
          (stability-⊢∷′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢t (↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↘ ◻)) eq ok
      (η-eq ⊢t₁ ⊢t₂ t₁0≡t₂0) PE.refl →
        let _ , (⊢A , A<) = ∙⊢≡∷→⊢-<ˢ t₁0≡t₂0
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↘ ↘ ◻))
        in
        η-eq (stability-⊢∷′ Γ≡Δ ⊢t₁ (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t₂ (↘ ↙ ◻))
          (stability-⊢≡∷′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) t₁0≡t₂0 (↘ ↘ ◻))
      (fst-cong ⊢B t₁≡t₂) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        fst-cong (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↘ ◻))
      (snd-cong ⊢B t₁≡t₂) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        snd-cong (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↘ ◻))
      (Σ-β₁ ⊢B ⊢t₁ ⊢t₂ eq ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        Σ-β₁ (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t₁ (↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t₂ (↘ ↘ ◻)) eq ok
      (Σ-β₂ ⊢B ⊢t₁ ⊢t₂ eq ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        Σ-β₂ (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t₁ (↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t₂ (↘ ↘ ◻)) eq ok
      (Σ-η ⊢B ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ↙ ◻))
        in
        Σ-η (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t₁ (↙ ↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t₂ (↙ ↘ ↘ ◻))
          (stability-⊢≡∷′ Γ≡Δ fst-t₁≡fst-t₂ (↘ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ snd-t₁≡snd-t₂ (↘ ↘ ◻))
      (prod-cong ⊢B t₁≡t₂ u₁≡u₂ ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢′ Γ≡Δ ⊢A (<ˢ-trans A< (↙ ◻))
        in
        prod-cong (stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B (↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↘ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ u₁≡u₂ (↘ ↘ ◻)) ok
      (prodrec-cong C₁≡C₂ t₁≡t₂ u₁≡u₂ ok) PE.refl →
        let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢≡∷→⊢-<ˢ u₁≡u₂
            ⊢A′                       = stability-⊢′ Γ≡Δ ⊢A $
                                        <ˢ-trans A< (↘ ↘ ◻)
            ⊢B′                       = stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B $
                                        <ˢ-trans B< (↘ ↘ ◻)
        in
        prodrec-cong (stability-⊢≡′ (Γ≡Δ ∙⟨ ΠΣⱼ ⊢B′ ok ⟩) C₁≡C₂ (↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↘ ↙ ◻))
          (stability-⊢≡∷′ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ ⊢B′ ⟩) u₁≡u₂ (↘ ↘ ◻)) ok
      (prodrec-β ⊢C ⊢t ⊢u ⊢v eq ok) PE.refl →
        let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢∷→⊢-<ˢ ⊢v
            ⊢A′                       = stability-⊢′ Γ≡Δ ⊢A $
                                        <ˢ-trans A< (↘ ↘ ◻)
            ⊢B′                       = stability-⊢′ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B $
                                        <ˢ-trans B< (↘ ↘ ◻)
        in
        prodrec-β (stability-⊢′ (Γ≡Δ ∙⟨ ΠΣⱼ ⊢B′ ok ⟩) ⊢C (↙ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t (↙ ↘ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↙ ◻))
          (stability-⊢∷′ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ ⊢B′ ⟩) ⊢v (↘ ↘ ◻)) eq ok
      (emptyrec-cong A₁≡A₂ t₁≡t₂) PE.refl →
        emptyrec-cong (stability-⊢≡′ Γ≡Δ A₁≡A₂ (↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↘ ◻))
      (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ ok no-η) PE.refl →
        unitrec-cong
          (stability-⊢≡′ (Γ≡Δ ∙⟨ Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok ⟩) A₁≡A₂ (↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↘ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ u₁≡u₂ (↘ ↘ ◻)) ok no-η
      (unitrec-β ⊢A ⊢t ok no-η) PE.refl →
        unitrec-β
          (stability-⊢′ (Γ≡Δ ∙⟨ Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok ⟩) ⊢A (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t (↘ ◻)) ok no-η
      (unitrec-β-η ⊢A ⊢t ⊢u ok no-η) PE.refl →
        unitrec-β-η
          (stability-⊢′ (Γ≡Δ ∙⟨ Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok ⟩) ⊢A (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t (↘ ↙ ◻)) (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↘ ◻))
          ok no-η
      (η-unit ⊢t₁ ⊢t₂ η) PE.refl →
        η-unit (stability-⊢∷′ Γ≡Δ ⊢t₁ (↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢t₂ (↘ ◻)) η
      (suc-cong t₁≡t₂) PE.refl →
        suc-cong (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↙ ◻))
      (natrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) PE.refl →
        let ⊢ℕ              = ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
            _ , (⊢A₁ , A₁<) = ∙⊢≡∷→⊢-<ˢ u₁≡u₂
            ⊢A₁′            = stability-⊢′ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A₁ $
                              <ˢ-trans A₁< (↘ ↙ ◻)
        in
        natrec-cong (stability-⊢≡′ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) A₁≡A₂ (↙ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↙ ↘ ◻))
          (stability-⊢≡∷′ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A₁′ ⟩) u₁≡u₂ (↘ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ v₁≡v₂ (↘ ↘ ◻))
      (natrec-zero ⊢t ⊢u) PE.refl →
        let ⊢ℕ            = ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
            _ , (⊢A , A<) = ∙⊢∷→⊢-<ˢ ⊢u
            ⊢A′           = stability-⊢′ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A $
                            <ˢ-trans A< (↘ ◻)
        in
        natrec-zero (stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻))
          (stability-⊢∷′ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A′ ⟩) ⊢u (↘ ◻))
      (natrec-suc ⊢t ⊢u ⊢v) PE.refl →
        let ⊢ℕ            = ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
            _ , (⊢A , A<) = ∙⊢∷→⊢-<ˢ ⊢u
            ⊢A′           = stability-⊢′ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A $
                            <ˢ-trans A< (↘ ↙ ◻)
        in
        natrec-suc (stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻))
          (stability-⊢∷′ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A′ ⟩) ⊢u (↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢v (↘ ↘ ◻))
      (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
        Id-cong (stability-⊢≡∷′ Γ≡Δ A₁≡A₂ (↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↘ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ u₁≡u₂ (↘ ↘ ◻))
      (J-cong A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) PE.refl →
        let _ , (⊢A₁ , A₁<) , _ = ∙∙⊢≡→⊢-<ˢ B₁≡B₂
            ⊢A₁′                = stability-⊢′ Γ≡Δ ⊢A₁ $
                                  <ˢ-trans A₁< (↘ ↙ ↙ ◻)
            ⊢t₁′                = stability-⊢∷′ Γ≡Δ ⊢t₁ (↙ ↘ ↙ ◻)
        in
        J-cong (stability-⊢≡′ Γ≡Δ A₁≡A₂ (↙ ↙ ◻)) ⊢t₁′
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↙ ↘ ↘ ◻))
          (stability-⊢≡′
             (Γ≡Δ ∙⟨ ⊢A₁′ ⟩ ∙⟨ Idⱼ (wkTerm₁ ⊢A₁′ ⊢t₁′) (var₀ ⊢A₁′) ⟩)
             B₁≡B₂ (↘ ↙ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ u₁≡u₂ (↘ ↙ ↘ ◻))
          (stability-⊢≡∷′ Γ≡Δ v₁≡v₂ (↘ ↘ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ w₁≡w₂ (↘ ↘ ↘ ◻))
      (J-β ⊢t ⊢B ⊢u eq) PE.refl →
        let _ , (⊢A , A<) , _ = ∙∙⊢→⊢-<ˢ ⊢B
            ⊢A′               = stability-⊢′ Γ≡Δ ⊢A $
                                <ˢ-trans A< (↘ ↙ ◻)
            ⊢t′               = stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻)
        in
        J-β ⊢t′
          (stability-⊢′
             (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ Idⱼ (wkTerm₁ ⊢A′ ⊢t′) (var₀ ⊢A′) ⟩) ⊢B
             (↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↘ ◻)) eq
      (K-cong A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
        let ⊢t₁′ = stability-⊢∷′ Γ≡Δ ⊢t₁ (↙ ↘ ↙ ◻) in
        K-cong (stability-⊢≡′ Γ≡Δ A₁≡A₂ (↙ ↙ ◻)) ⊢t₁′
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↙ ↘ ↘ ◻))
          (stability-⊢≡′ (Γ≡Δ ∙⟨ Idⱼ ⊢t₁′ ⊢t₁′ ⟩) B₁≡B₂ (↘ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ u₁≡u₂ (↘ ↘ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ v₁≡v₂ (↘ ↘ ↘ ◻)) ok
      (K-β ⊢t ⊢B ⊢u ok) PE.refl →
        let ⊢t′ = stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻) in
        K-β ⊢t′ (stability-⊢′ (Γ≡Δ ∙⟨ Idⱼ ⊢t′ ⊢t′ ⟩) ⊢B (↘ ↙ ◻))
          (stability-⊢∷′ Γ≡Δ ⊢u (↘ ↘ ◻)) ok
      ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
        []-cong-cong (stability-⊢≡′ Γ≡Δ A₁≡A₂ (↙ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ t₁≡t₂ (↙ ↘ ◻))
          (stability-⊢≡∷′ Γ≡Δ u₁≡u₂ (↘ ↙ ◻))
          (stability-⊢≡∷′ Γ≡Δ v₁≡v₂ (↘ ↘ ◻)) ok
      ([]-cong-β ⊢t eq ok) PE.refl →
        []-cong-β (stability-⊢∷′ Γ≡Δ ⊢t (↙ ◻)) eq ok

  opaque

    -- The type P s is inhabited for every s.

    P-inhabited : P s
    P-inhabited =
      well-founded-induction P
        (λ _ hyp →
           record
             { stability-⊢   = stability-⊢   hyp
             ; stability-⊢≡  = stability-⊢≡  hyp
             ; stability-⊢∷  = stability-⊢∷  hyp
             ; stability-⊢≡∷ = stability-⊢≡∷ hyp
             })
        _

opaque

  -- Stability for _⊢_.

  stability-⊢ : ⊢ Γ ≡ Δ → Γ ⊢ A → Δ ⊢ A
  stability-⊢ Γ≡Δ ⊢A =
    P.stability-⊢ Inhabited.P-inhabited Γ≡Δ ⊢A PE.refl

opaque

  -- Stability for _⊢_≡_.

  stability-⊢≡ : ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B → Δ ⊢ A ≡ B
  stability-⊢≡ Γ≡Δ A≡B =
    P.stability-⊢≡ Inhabited.P-inhabited Γ≡Δ A≡B PE.refl

opaque

  -- Stability for _⊢_∷_.

  stability-⊢∷ : ⊢ Γ ≡ Δ → Γ ⊢ t ∷ A → Δ ⊢ t ∷ A
  stability-⊢∷ Γ≡Δ ⊢t =
    P.stability-⊢∷ Inhabited.P-inhabited Γ≡Δ ⊢t PE.refl

opaque

  -- Stability for _⊢_≡_∷_.

  stability-⊢≡∷ : ⊢ Γ ≡ Δ → Γ ⊢ t ≡ u ∷ A → Δ ⊢ t ≡ u ∷ A
  stability-⊢≡∷ Γ≡Δ t≡u =
    P.stability-⊢≡∷ Inhabited.P-inhabited Γ≡Δ t≡u PE.refl

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
