------------------------------------------------------------------------
-- A variant of Definition.Typed.Stability with fewer dependencies
------------------------------------------------------------------------

{-# OPTIONS --backtracking-instance-search #-}

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Stability.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Inversion.Primitive R
open import Definition.Typed.Properties.Admissible.Level.Primitive R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Definition.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Size R
open import Definition.Typed.Weakening R
open import Definition.Untyped M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Size
open import Tools.Size.Instances

private variable
  m n     : Nat
  ∇       : DCon (Term 0) _
  x       : Fin _
  Γ Δ Η   : Con Term _
  𝓙       : Judgement _
  A B t u : Term _
  l l₁ l₂ : Lvl _
  σ σ₁ σ₂ : Subst _ _
  s s₂    : Size

-- Equality of contexts.

infix 24 _∙⟨_∣_⟩

data _»⊢_≡_ : (∇ : DCon (Term 0) m) (_ _ : Con Term n) → Set a where
  ε       : » ∇ → ∇ »⊢ ε ≡ ε
  _∙⟨_∣_⟩ : ∇ »⊢ Γ ≡ Δ → ∇ » Δ ⊢ B → ∇ » Δ ⊢ A ≡ B → ∇ »⊢ Γ ∙ A ≡ Δ ∙ B

opaque

  -- A variant of _∙⟨_∣_⟩.

  infix 24 _∙⟨_⟩

  _∙⟨_⟩ : ∇ »⊢ Γ ≡ Δ → ∇ » Δ ⊢ A → ∇ »⊢ Γ ∙ A ≡ Δ ∙ A
  Γ≡Δ ∙⟨ ⊢A ⟩ = Γ≡Δ ∙⟨ ⊢A ∣ refl ⊢A ⟩

opaque

  -- A well-formedness lemma for ⊢_≡_.

  wf-⊢≡ʳ : ∇ »⊢ Γ ≡ Δ → ∇ »⊢ Δ
  wf-⊢≡ʳ (ε »∇)          = ε »∇
  wf-⊢≡ʳ (_ ∙⟨ ⊢B ∣ _ ⟩) = ∙ ⊢B

opaque

  -- Reflexivity for ⊢_≡_.

  reflConEq : ∇ »⊢ Γ → ∇ »⊢ Γ ≡ Γ
  reflConEq (ε »∇) = ε »∇
  reflConEq (∙ ⊢A) = reflConEq (wf ⊢A) ∙⟨ ⊢A ⟩

opaque

  -- A variant of _∙⟨_∣_⟩.

  refl-∙⟨_∣_⟩ : ∇ » Γ ⊢ B → ∇ » Γ ⊢ A ≡ B → ∇ »⊢ Γ ∙ A ≡ Γ ∙ B
  refl-∙⟨ ⊢B ∣ A≡B ⟩ = reflConEq (wf ⊢B) ∙⟨ ⊢B ∣ A≡B ⟩

opaque

  -- A glassification lemma for _»⊢_≡_.

  glassify-»⊢≡ : ∇ »⊢ Γ ≡ Δ → glassify ∇ »⊢ Γ ≡ Δ
  glassify-»⊢≡ (ε »∇) =
    ε (glassify-» »∇)
  glassify-»⊢≡ (Γ≡Δ ∙⟨ ⊢B ∣ A≡B ⟩) =
    glassify-»⊢≡ Γ≡Δ ∙⟨ glassify-⊢ ⊢B ∣ glassify-⊢≡ A≡B ⟩

opaque

  -- Stability for _∷_∈_.

  stability-⊢∈ :
    ∇ »⊢ Γ ≡ Δ → x ∷ A ∈ Γ →
    ∃ λ B → ∇ » Δ ⊢ A ≡ B × x ∷ B ∈ Δ
  stability-⊢∈ (ε ⊢ε)              ()
  stability-⊢∈ (Γ≡Δ ∙⟨ ⊢B ∣ A≡B ⟩) here =
    _ , wk₁ ⊢B A≡B , here
  stability-⊢∈ (Γ≡Δ ∙⟨ ⊢B ∣ _ ⟩) (there x∈) =
    Σ.map wk1 (Σ.map (wk₁ ⊢B) there) $
    stability-⊢∈ Γ≡Δ x∈

private

  -- Below several properties are proved simultaneously using
  -- well-founded induction. The properties are collected in the
  -- record type P.

  record P (s : Size) : Set a where
    no-eta-equality
    field
      stability-⊢ :
        ∇ »⊢ Γ ≡ Δ →
        (⊢A : ∇ » Γ ⊢ A) →
        size ⊢A PE.≡ s →
        ∇ » Δ ⊢ A
      stability-⊢≡ :
        ∇ »⊢ Γ ≡ Δ →
        (A≡B : ∇ » Γ ⊢ A ≡ B) →
        size A≡B PE.≡ s →
        ∇ » Δ ⊢ A ≡ B
      stability-⊢∷ :
        ∇ »⊢ Γ ≡ Δ →
        (⊢t : ∇ » Γ ⊢ t ∷ A) →
        size ⊢t PE.≡ s →
        ∇ » Δ ⊢ t ∷ A
      stability-⊢∷L :
        ∇ »⊢ Γ ≡ Δ →
        (⊢l : ∇ » Γ ⊢ l ∷Level) →
        size ⊢l PE.≡ s →
        ∇ » Δ ⊢ l ∷Level
      stability-⊢≡∷ :
        ∇ »⊢ Γ ≡ Δ →
        (t≡u : ∇ » Γ ⊢ t ≡ u ∷ A) →
        size t≡u PE.≡ s →
        ∇ » Δ ⊢ t ≡ u ∷ A
      stability-⊢≡∷L :
        ∇ »⊢ Γ ≡ Δ →
        (l₁≡l₂ : ∇ » Γ ⊢ l₁ ≡ l₂ ∷Level) →
        size l₁≡l₂ PE.≡ s →
        ∇ » Δ ⊢ l₁ ≡ l₂ ∷Level

-- Variants of the fields of P.

private module Variants (hyp : ∀ {s₁} → s₁ <ˢ s₂ → P s₁) where

  opaque

    -- Variants of the fields of P.

    stability-⊢ :
      ∇ »⊢ Γ ≡ Δ →
      (⊢A : ∇ » Γ ⊢ A)
      ⦃ lt : size ⊢A <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ A
    stability-⊢ Γ≡Δ ⊢A ⦃ lt ⦄ = P.stability-⊢ (hyp lt) Γ≡Δ ⊢A PE.refl

    stability-⊢≡ :
      ∇ »⊢ Γ ≡ Δ →
      (A≡B : ∇ » Γ ⊢ A ≡ B)
      ⦃ lt : size A≡B <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ A ≡ B
    stability-⊢≡ Γ≡Δ A≡B ⦃ lt ⦄ =
      P.stability-⊢≡ (hyp lt) Γ≡Δ A≡B PE.refl

    stability-⊢∷ :
      ∇ »⊢ Γ ≡ Δ →
      (⊢t : ∇ » Γ ⊢ t ∷ A)
      ⦃ lt : size ⊢t <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ t ∷ A
    stability-⊢∷ Γ≡Δ ⊢t ⦃ lt ⦄ = P.stability-⊢∷ (hyp lt) Γ≡Δ ⊢t PE.refl

    stability-⊢∷L :
      ∇ »⊢ Γ ≡ Δ →
      (⊢l : ∇ » Γ ⊢ l ∷Level)
      ⦃ lt : size ⊢l <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ l ∷Level
    stability-⊢∷L Γ≡Δ ⊢l ⦃ lt ⦄ =
      P.stability-⊢∷L (hyp lt) Γ≡Δ ⊢l PE.refl

    stability-⊢≡∷ :
      ∇ »⊢ Γ ≡ Δ →
      (t≡u : ∇ » Γ ⊢ t ≡ u ∷ A)
      ⦃ lt : size t≡u <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ t ≡ u ∷ A
    stability-⊢≡∷ Γ≡Δ t≡u ⦃ lt ⦄ =
      P.stability-⊢≡∷ (hyp lt) Γ≡Δ t≡u PE.refl

    stability-⊢≡∷L :
      ∇ »⊢ Γ ≡ Δ →
      (l₁≡l₂ : ∇ » Γ ⊢ l₁ ≡ l₂ ∷Level)
      ⦃ lt : size l₁≡l₂ <ˢ s₂ ⦄ →
      ∇ » Δ ⊢ l₁ ≡ l₂ ∷Level
    stability-⊢≡∷L Γ≡Δ l₁≡l₂ ⦃ lt ⦄ =
      P.stability-⊢≡∷L (hyp lt) Γ≡Δ l₁≡l₂ PE.refl

-- The type P s is inhabited for every s.

private module Inhabited where

  opaque
    unfolding size

    -- Stability for _⊢_.

    stability-⊢′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ∇ »⊢ Γ ≡ Δ →
      (⊢A : ∇ » Γ ⊢ A) →
      size ⊢A PE.≡ s₂ →
      ∇ » Δ ⊢ A
    stability-⊢′ hyp Γ≡Δ = let open Variants hyp in λ where
      (Levelⱼ ok _) _ →
        Levelⱼ ok (wf-⊢≡ʳ Γ≡Δ)
      (univ ⊢A) PE.refl →
        univ (stability-⊢∷ Γ≡Δ ⊢A)
      (Liftⱼ ⊢l ⊢A) PE.refl →
        Liftⱼ (stability-⊢∷L Γ≡Δ ⊢l) (stability-⊢ Γ≡Δ ⊢A)
      (ΠΣⱼ ⊢B ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        ΠΣⱼ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) ok
      (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
        Idⱼ (stability-⊢ Γ≡Δ ⊢A) (stability-⊢∷ Γ≡Δ ⊢t)
          (stability-⊢∷ Γ≡Δ ⊢u)

  opaque
    unfolding size

    -- Stability for _⊢_≡_.

    stability-⊢≡′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ∇ »⊢ Γ ≡ Δ →
      (A≡B : ∇ » Γ ⊢ A ≡ B) →
      size A≡B PE.≡ s₂ →
      ∇ » Δ ⊢ A ≡ B
    stability-⊢≡′ hyp Γ≡Δ = let open Variants hyp in λ where
      (refl ⊢A) PE.refl →
        refl (stability-⊢ Γ≡Δ ⊢A)
      (sym B≡A) PE.refl →
        sym (stability-⊢≡ Γ≡Δ B≡A)
      (trans A≡B B≡C) PE.refl →
        trans (stability-⊢≡ Γ≡Δ A≡B) (stability-⊢≡ Γ≡Δ B≡C)
      (univ A≡B) PE.refl →
        univ (stability-⊢≡∷ Γ≡Δ A≡B)
      (U-cong l₁≡l₂) PE.refl →
        U-cong (stability-⊢≡∷ Γ≡Δ l₁≡l₂)
      (Lift-cong l₁≡l₂ A≡B) PE.refl →
        Lift-cong (stability-⊢≡∷L Γ≡Δ l₁≡l₂) (stability-⊢≡ Γ≡Δ A≡B)
      (ΠΣ-cong A₁≡B₁ A₂≡B₂ ok) PE.refl →
        let _ , (⊢A₁ , A₁<) = ∙⊢→⊢-<ˢ A₂≡B₂
            ⊢A₁′            = stability-⊢ Γ≡Δ ⊢A₁
                                ⦃ lt = <ˢ-trans A₁< ! ⦄
        in
        ΠΣ-cong (stability-⊢≡ Γ≡Δ A₁≡B₁)
          (stability-⊢≡ (Γ≡Δ ∙⟨ ⊢A₁′ ⟩) A₂≡B₂) ok
      (Id-cong A≡B t₁≡u₁ t₂≡u₂) PE.refl →
        Id-cong (stability-⊢≡ Γ≡Δ A≡B) (stability-⊢≡∷ Γ≡Δ t₁≡u₁)
          (stability-⊢≡∷ Γ≡Δ t₂≡u₂)

  opaque
    unfolding size

    -- Stability for _⊢_∷_.

    stability-⊢∷′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ∇ »⊢ Γ ≡ Δ →
      (⊢t : ∇ » Γ ⊢ t ∷ A) →
      size ⊢t PE.≡ s₂ →
      ∇ » Δ ⊢ t ∷ A
    stability-⊢∷′ hyp Γ≡Δ = let open Variants hyp in λ where
      (conv ⊢t B≡A) PE.refl →
        conv (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢≡ Γ≡Δ B≡A)
      (var _ x∈Γ) _ →
        let _ , A≡B , x∈Δ = stability-⊢∈ Γ≡Δ x∈Γ in
        conv (var (wf-⊢≡ʳ Γ≡Δ) x∈Δ) (sym A≡B)
      (defn ⊢Γ α↦t A≡A′) PE.refl →
        defn (wf-⊢≡ʳ Γ≡Δ) α↦t A≡A′
      (Levelⱼ _ ok) _ →
        Levelⱼ (wf-⊢≡ʳ Γ≡Δ) ok
      (zeroᵘⱼ ok _) _ →
        zeroᵘⱼ ok (wf-⊢≡ʳ Γ≡Δ)
      (sucᵘⱼ ⊢t) PE.refl →
        sucᵘⱼ (stability-⊢∷ Γ≡Δ ⊢t)
      (supᵘⱼ ⊢t ⊢u) PE.refl →
        supᵘⱼ (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u)
      (Uⱼ ⊢l) PE.refl →
        Uⱼ (stability-⊢∷L Γ≡Δ ⊢l)
      (Liftⱼ ⊢l₁ ⊢l₂ ⊢A) PE.refl →
        Liftⱼ (stability-⊢∷L Γ≡Δ ⊢l₁) (stability-⊢∷L Γ≡Δ ⊢l₂)
          (stability-⊢∷ Γ≡Δ ⊢A)
      (liftⱼ ⊢l ⊢A ⊢t) PE.refl →
        liftⱼ (stability-⊢∷L Γ≡Δ ⊢l) (stability-⊢ Γ≡Δ ⊢A)
          (stability-⊢∷ Γ≡Δ ⊢t)
      (lowerⱼ x) PE.refl →
        lowerⱼ (stability-⊢∷ Γ≡Δ x)
      (ΠΣⱼ l ⊢A ⊢B ok) PE.refl →
        let ⊢A′ = stability-⊢∷ Γ≡Δ ⊢A in
        ΠΣⱼ (stability-⊢∷L Γ≡Δ l) ⊢A′
          (stability-⊢∷ (Γ≡Δ ∙⟨ univ ⊢A′ ⟩) ⊢B) ok
      (lamⱼ ⊢B ⊢t ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢t
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
            Γ∙A≡Δ∙A       = Γ≡Δ ∙⟨ ⊢A′ ⟩
        in
        lamⱼ (stability-⊢ Γ∙A≡Δ∙A ⊢B) (stability-⊢∷ Γ∙A≡Δ∙A ⊢t) ok
      (⊢t ∘ⱼ ⊢u) PE.refl →
        stability-⊢∷ Γ≡Δ ⊢t ∘ⱼ stability-⊢∷ Γ≡Δ ⊢u
      (prodⱼ ⊢B ⊢t ⊢u ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        prodⱼ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t)
          (stability-⊢∷ Γ≡Δ ⊢u) ok
      (fstⱼ ⊢B ⊢t) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        fstⱼ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t)
      (sndⱼ ⊢B ⊢t) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        sndⱼ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t)
      (prodrecⱼ ⊢C ⊢t ⊢u ok) PE.refl →
        let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢→⊢-<ˢ ⊢u
            ⊢A′                       = stability-⊢ Γ≡Δ ⊢A
                                          ⦃ lt = <ˢ-trans A< ! ⦄
            ⊢B′                       = stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B
                                          ⦃ lt = <ˢ-trans B< ! ⦄
        in
        prodrecⱼ (stability-⊢ (Γ≡Δ ∙⟨ ΠΣⱼ ⊢B′ ok ⟩) ⊢C)
          (stability-⊢∷ Γ≡Δ ⊢t)
          (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ ⊢B′ ⟩) ⊢u) ok
      (Emptyⱼ _) _ →
        Emptyⱼ (wf-⊢≡ʳ Γ≡Δ)
      (emptyrecⱼ ⊢A ⊢t) PE.refl →
        emptyrecⱼ (stability-⊢ Γ≡Δ ⊢A) (stability-⊢∷ Γ≡Δ ⊢t)
      (Unitⱼ ⊢Γ ok) PE.refl →
        Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok
      (starⱼ ⊢Γ ok) PE.refl →
        starⱼ (wf-⊢≡ʳ Γ≡Δ) ok
      (unitrecⱼ ⊢A ⊢t ⊢u ok) PE.refl →
        unitrecⱼ
          (stability-⊢ (Γ≡Δ ∙⟨ univ (Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok) ⟩) ⊢A)
          (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u) ok
      (ℕⱼ _) _ →
        ℕⱼ (wf-⊢≡ʳ Γ≡Δ)
      (zeroⱼ _) _ →
        zeroⱼ (wf-⊢≡ʳ Γ≡Δ)
      (sucⱼ ⊢t) PE.refl →
        sucⱼ (stability-⊢∷ Γ≡Δ ⊢t)
      (natrecⱼ ⊢t ⊢u ⊢v) PE.refl →
        let ⊢ℕ            = univ (ℕⱼ (wf-⊢≡ʳ Γ≡Δ))
            _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢u
            ⊢A′           = stability-⊢ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A
                              ⦃ lt = <ˢ-trans A< ! ⦄
        in
        natrecⱼ (stability-⊢∷ Γ≡Δ ⊢t)
          (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A′ ⟩) ⊢u) (stability-⊢∷ Γ≡Δ ⊢v)
      (Idⱼ ⊢A ⊢t ⊢u) PE.refl →
        Idⱼ (stability-⊢∷ Γ≡Δ ⊢A) (stability-⊢∷ Γ≡Δ ⊢t)
          (stability-⊢∷ Γ≡Δ ⊢u)
      (rflⱼ ⊢t) PE.refl →
        rflⱼ (stability-⊢∷ Γ≡Δ ⊢t)
      (Jⱼ ⊢t ⊢B ⊢u ⊢v ⊢w) PE.refl →
        let _ , (⊢A , A<) , _ = ∙∙⊢→⊢-<ˢ ⊢B
            ⊢A′               = stability-⊢ Γ≡Δ ⊢A
                                  ⦃ lt = <ˢ-trans A< ! ⦄
            ⊢t′               = stability-⊢∷ Γ≡Δ ⊢t
        in
        Jⱼ ⊢t′
          (stability-⊢
             (Γ≡Δ
                ∙⟨ ⊢A′ ⟩
                ∙⟨ Idⱼ (wk₁ ⊢A′ ⊢A′) (wk₁ ⊢A′ ⊢t′) (var₀ ⊢A′) ⟩)
             ⊢B)
          (stability-⊢∷ Γ≡Δ ⊢u) (stability-⊢∷ Γ≡Δ ⊢v)
          (stability-⊢∷ Γ≡Δ ⊢w)
      (Kⱼ ⊢B ⊢u ⊢v ok) PE.refl →
        let _ , ⊢Id                   = ∙⊢→⊢-<ˢ ⊢B
            (⊢A , A<) , (⊢t , t<) , _ = inversion-Id-⊢-<ˢ ⊢Id
            ⊢A′                       = stability-⊢ Γ≡Δ ⊢A
                                          ⦃ lt = <ˢ-trans A< ! ⦄
            ⊢t′                       = stability-⊢∷ Γ≡Δ ⊢t
                                          ⦃ lt = <ˢ-trans t< ! ⦄
        in
        Kⱼ (stability-⊢ (Γ≡Δ ∙⟨ Idⱼ ⊢A′ ⊢t′ ⊢t′ ⟩) ⊢B)
          (stability-⊢∷ Γ≡Δ ⊢u) (stability-⊢∷ Γ≡Δ ⊢v) ok
      ([]-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v ok) PE.refl →
        []-congⱼ (stability-⊢∷L Γ≡Δ ⊢l) (stability-⊢ Γ≡Δ ⊢A)
          (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u)
          (stability-⊢∷ Γ≡Δ ⊢v) ok

  opaque
    unfolding size

    -- Stability for _⊢_∷Level.

    stability-⊢∷L′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ∇ »⊢ Γ ≡ Δ →
      (⊢l : ∇ » Γ ⊢ l ∷Level) →
      size ⊢l PE.≡ s₂ →
      ∇ » Δ ⊢ l ∷Level
    stability-⊢∷L′ hyp Γ≡Δ = let open Variants hyp in λ where
      (term ok ⊢l) PE.refl →
        term ok (stability-⊢∷ Γ≡Δ ⊢l)
      (literal ok _) _ →
        literal ok (wf-⊢≡ʳ Γ≡Δ)

  opaque
    unfolding size

    -- Stability for _⊢_≡_∷_.

    stability-⊢≡∷′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ∇ »⊢ Γ ≡ Δ →
      (t≡u : ∇ » Γ ⊢ t ≡ u ∷ A) →
      size t≡u PE.≡ s₂ →
      ∇ » Δ ⊢ t ≡ u ∷ A
    stability-⊢≡∷′ hyp Γ≡Δ = let open Variants hyp in λ where
      (refl ⊢t) PE.refl →
        refl (stability-⊢∷ Γ≡Δ ⊢t)
      (sym ⊢A t₂≡t₁) PE.refl →
        sym (stability-⊢ Γ≡Δ ⊢A) (stability-⊢≡∷ Γ≡Δ t₂≡t₁)
      (trans t₁≡t₂ t₂≡t₃) PE.refl →
        trans (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡∷ Γ≡Δ t₂≡t₃)
      (conv t₁≡t₂ B≡A) PE.refl →
        conv (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡ Γ≡Δ B≡A)
      (δ-red ⊢Γ α↦t A≡A′ t≡t′) PE.refl →
        δ-red (wf-⊢≡ʳ Γ≡Δ) α↦t A≡A′ t≡t′
      (sucᵘ-cong t₁≡t₂) PE.refl →
        sucᵘ-cong (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (supᵘ-cong t₁≡t₂ u₁≡u₂) PE.refl →
        supᵘ-cong (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡∷ Γ≡Δ u₁≡u₂)
      (supᵘ-zeroˡ l) PE.refl →
        supᵘ-zeroˡ (stability-⊢∷ Γ≡Δ l)
      (supᵘ-sucᵘ l₁ l₂) PE.refl →
        supᵘ-sucᵘ (stability-⊢∷ Γ≡Δ l₁) (stability-⊢∷ Γ≡Δ l₂)
      (supᵘ-assoc l₁ l₂ l₃) PE.refl →
        supᵘ-assoc (stability-⊢∷ Γ≡Δ l₁) (stability-⊢∷ Γ≡Δ l₂) (stability-⊢∷ Γ≡Δ l₃)
      (supᵘ-comm l₁ l₂) PE.refl →
        supᵘ-comm (stability-⊢∷ Γ≡Δ l₁) (stability-⊢∷ Γ≡Δ l₂)
      (supᵘ-idem ⊢l) PE.refl →
        supᵘ-idem (stability-⊢∷ Γ≡Δ ⊢l)
      (supᵘ-sub ⊢l) PE.refl →
        supᵘ-sub (stability-⊢∷ Γ≡Δ ⊢l)
      (U-cong l₁≡l₂) PE.refl →
        U-cong (stability-⊢≡∷ Γ≡Δ l₁≡l₂)
      (Lift-cong ⊢l₁ ⊢l₂ l₂≡l₃ A₁≡A₂) PE.refl →
        Lift-cong (stability-⊢∷L Γ≡Δ ⊢l₁) (stability-⊢∷L Γ≡Δ ⊢l₂)
          (stability-⊢≡∷L Γ≡Δ l₂≡l₃) (stability-⊢≡∷ Γ≡Δ A₁≡A₂)
      (lower-cong x) PE.refl →
        lower-cong (stability-⊢≡∷ Γ≡Δ x)
      (Lift-β x₁ x₂) PE.refl →
        Lift-β (stability-⊢ Γ≡Δ x₁) (stability-⊢∷ Γ≡Δ x₂)
      (Lift-η ⊢l ⊢A ⊢t ⊢u lower-t≡lower-u) PE.refl →
        Lift-η (stability-⊢∷L Γ≡Δ ⊢l) (stability-⊢ Γ≡Δ ⊢A)
          (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u)
          (stability-⊢≡∷ Γ≡Δ lower-t≡lower-u)
      (ΠΣ-cong ⊢l A₁≡A₂ B₁≡B₂ ok) PE.refl →
        let _ , (⊢A₁ , A₁<) = ∙⊢→⊢-<ˢ B₁≡B₂
            ⊢A₁′            = stability-⊢ Γ≡Δ ⊢A₁
                                ⦃ lt = <ˢ-trans A₁< ! ⦄
        in
        ΠΣ-cong (stability-⊢∷L Γ≡Δ ⊢l) (stability-⊢≡∷ Γ≡Δ A₁≡A₂)
          (stability-⊢≡∷ (Γ≡Δ ∙⟨ ⊢A₁′ ⟩) B₁≡B₂) ok
      (app-cong t₁≡t₂ u₁≡u₂) PE.refl →
        app-cong (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡∷ Γ≡Δ u₁≡u₂)
      (β-red ⊢B ⊢t ⊢u eq ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        β-red (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B)
          (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢t) (stability-⊢∷ Γ≡Δ ⊢u) eq ok
      (η-eq ⊢B ⊢t₁ ⊢t₂ t₁0≡t₂0 ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ t₁0≡t₂0
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
            Γ∙A≡Δ∙A       = Γ≡Δ ∙⟨ ⊢A′ ⟩
        in
        η-eq (stability-⊢ Γ∙A≡Δ∙A ⊢B) (stability-⊢∷ Γ≡Δ ⊢t₁)
          (stability-⊢∷ Γ≡Δ ⊢t₂) (stability-⊢≡∷ Γ∙A≡Δ∙A t₁0≡t₂0) ok
      (fst-cong ⊢B t₁≡t₂) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        fst-cong (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B)
          (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (snd-cong ⊢B t₁≡t₂) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        snd-cong (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B)
          (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (Σ-β₁ ⊢B ⊢t₁ ⊢t₂ eq ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        Σ-β₁ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t₁)
          (stability-⊢∷ Γ≡Δ ⊢t₂) eq ok
      (Σ-β₂ ⊢B ⊢t₁ ⊢t₂ eq ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        Σ-β₂ (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t₁)
          (stability-⊢∷ Γ≡Δ ⊢t₂) eq ok
      (Σ-η ⊢B ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂ ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        Σ-η (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B) (stability-⊢∷ Γ≡Δ ⊢t₁)
          (stability-⊢∷ Γ≡Δ ⊢t₂) (stability-⊢≡∷ Γ≡Δ fst-t₁≡fst-t₂)
          (stability-⊢≡∷ Γ≡Δ snd-t₁≡snd-t₂) ok
      (prod-cong ⊢B t₁≡t₂ u₁≡u₂ ok) PE.refl →
        let _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢B
            ⊢A′           = stability-⊢ Γ≡Δ ⊢A ⦃ lt = <ˢ-trans A< ! ⦄
        in
        prod-cong (stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B)
          (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡∷ Γ≡Δ u₁≡u₂) ok
      (prodrec-cong C₁≡C₂ t₁≡t₂ u₁≡u₂ ok) PE.refl →
        let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢→⊢-<ˢ u₁≡u₂
            ⊢A′                       = stability-⊢ Γ≡Δ ⊢A
                                          ⦃ lt = <ˢ-trans A< ! ⦄
            ⊢B′                       = stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B
                                          ⦃ lt = <ˢ-trans B< ! ⦄
        in
        prodrec-cong (stability-⊢≡ (Γ≡Δ ∙⟨ ΠΣⱼ ⊢B′ ok ⟩) C₁≡C₂)
          (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
          (stability-⊢≡∷ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ ⊢B′ ⟩) u₁≡u₂) ok
      (prodrec-β ⊢C ⊢t ⊢u ⊢v eq ok) PE.refl →
        let _ , (⊢A , A<) , (⊢B , B<) = ∙∙⊢→⊢-<ˢ ⊢v
            ⊢A′                       = stability-⊢ Γ≡Δ ⊢A
                                          ⦃ lt = <ˢ-trans A< ! ⦄
            ⊢B′                       = stability-⊢ (Γ≡Δ ∙⟨ ⊢A′ ⟩) ⊢B
                                          ⦃ lt = <ˢ-trans B< ! ⦄
        in
        prodrec-β (stability-⊢ (Γ≡Δ ∙⟨ ΠΣⱼ ⊢B′ ok ⟩) ⊢C)
          (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u)
          (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢A′ ⟩ ∙⟨ ⊢B′ ⟩) ⊢v) eq ok
      (emptyrec-cong A₁≡A₂ t₁≡t₂) PE.refl →
        emptyrec-cong (stability-⊢≡ Γ≡Δ A₁≡A₂) (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ ok no-η) PE.refl →
        unitrec-cong
          (stability-⊢≡ (Γ≡Δ ∙⟨ univ (Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok) ⟩) A₁≡A₂)
          (stability-⊢≡∷ Γ≡Δ t₁≡t₂) (stability-⊢≡∷ Γ≡Δ u₁≡u₂) ok no-η
      (unitrec-β ⊢A ⊢t ok no-η) PE.refl →
        unitrec-β
          (stability-⊢ (Γ≡Δ ∙⟨ univ (Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok) ⟩) ⊢A)
          (stability-⊢∷ Γ≡Δ ⊢t) ok no-η
      (unitrec-β-η ⊢A ⊢t ⊢u ok no-η) PE.refl →
        unitrec-β-η
          (stability-⊢ (Γ≡Δ ∙⟨ univ (Unitⱼ (wf-⊢≡ʳ Γ≡Δ) ok) ⟩) ⊢A)
          (stability-⊢∷ Γ≡Δ ⊢t) (stability-⊢∷ Γ≡Δ ⊢u) ok no-η
      (η-unit ⊢t₁ ⊢t₂ η) PE.refl →
        η-unit (stability-⊢∷ Γ≡Δ ⊢t₁) (stability-⊢∷ Γ≡Δ ⊢t₂) η
      (suc-cong t₁≡t₂) PE.refl →
        suc-cong (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
      (natrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) PE.refl →
        let ⊢ℕ              = univ (ℕⱼ (wf-⊢≡ʳ Γ≡Δ))
            _ , (⊢A₁ , A₁<) = ∙⊢→⊢-<ˢ u₁≡u₂
            ⊢A₁′            = stability-⊢ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A₁
                                ⦃ lt = <ˢ-trans A₁< ! ⦄
        in
        natrec-cong (stability-⊢≡ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) A₁≡A₂)
          (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
          (stability-⊢≡∷ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A₁′ ⟩) u₁≡u₂)
          (stability-⊢≡∷ Γ≡Δ v₁≡v₂)
      (natrec-zero ⊢t ⊢u) PE.refl →
        let ⊢ℕ            = univ (ℕⱼ (wf-⊢≡ʳ Γ≡Δ))
            _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢u
            ⊢A′           = stability-⊢ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A
                              ⦃ lt = <ˢ-trans A< ! ⦄
        in
        natrec-zero (stability-⊢∷ Γ≡Δ ⊢t)
          (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A′ ⟩) ⊢u)
      (natrec-suc ⊢t ⊢u ⊢v) PE.refl →
        let ⊢ℕ            = univ (ℕⱼ (wf-⊢≡ʳ Γ≡Δ))
            _ , (⊢A , A<) = ∙⊢→⊢-<ˢ ⊢u
            ⊢A′           = stability-⊢ (Γ≡Δ ∙⟨ ⊢ℕ ⟩) ⊢A
                              ⦃ lt = <ˢ-trans A< ! ⦄
        in
        natrec-suc (stability-⊢∷ Γ≡Δ ⊢t)
          (stability-⊢∷ (Γ≡Δ ∙⟨ ⊢ℕ ⟩ ∙⟨ ⊢A′ ⟩) ⊢u) (stability-⊢∷ Γ≡Δ ⊢v)
      (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) PE.refl →
        Id-cong (stability-⊢≡∷ Γ≡Δ A₁≡A₂) (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
          (stability-⊢≡∷ Γ≡Δ u₁≡u₂)
      (J-cong A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) PE.refl →
        let _ , (⊢A₁ , A₁<) , _ = ∙∙⊢→⊢-<ˢ B₁≡B₂
            ⊢A₁′                = stability-⊢ Γ≡Δ ⊢A₁
                                    ⦃ lt = <ˢ-trans A₁< ! ⦄
            ⊢t₁′                = stability-⊢∷ Γ≡Δ ⊢t₁
        in
        J-cong (stability-⊢≡ Γ≡Δ A₁≡A₂) ⊢t₁′
          (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
          (stability-⊢≡
             (Γ≡Δ
                ∙⟨ ⊢A₁′ ⟩
                ∙⟨ Idⱼ (wk₁ ⊢A₁′ ⊢A₁′) (wk₁ ⊢A₁′ ⊢t₁′)
                     (var₀ ⊢A₁′) ⟩)
             B₁≡B₂)
          (stability-⊢≡∷ Γ≡Δ u₁≡u₂) (stability-⊢≡∷ Γ≡Δ v₁≡v₂)
          (stability-⊢≡∷ Γ≡Δ w₁≡w₂)
      (J-β ⊢t ⊢B ⊢u eq) PE.refl →
        let _ , (⊢A , A<) , _ = ∙∙⊢→⊢-<ˢ ⊢B
            ⊢A′               = stability-⊢ Γ≡Δ ⊢A
                                  ⦃ lt = <ˢ-trans A< ! ⦄
            ⊢t′               = stability-⊢∷ Γ≡Δ ⊢t
        in
        J-β ⊢t′
          (stability-⊢
             (Γ≡Δ
                ∙⟨ ⊢A′ ⟩
                ∙⟨ Idⱼ (wk₁ ⊢A′ ⊢A′) (wk₁ ⊢A′ ⊢t′) (var₀ ⊢A′) ⟩)
             ⊢B)
          (stability-⊢∷ Γ≡Δ ⊢u) eq
      (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
        let _ , ⊢Id                       = ∙⊢→⊢-<ˢ B₁≡B₂
            (⊢A₁ , A₁<) , (⊢t₁ , t₁<) , _ = inversion-Id-⊢-<ˢ ⊢Id
            ⊢A₁′                          = stability-⊢ Γ≡Δ ⊢A₁
                                              ⦃ lt = <ˢ-trans A₁< ! ⦄
            ⊢t₁′                          = stability-⊢∷ Γ≡Δ ⊢t₁
                                              ⦃ lt = <ˢ-trans t₁< ! ⦄
        in
        K-cong (stability-⊢≡ Γ≡Δ A₁≡A₂) (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
          (stability-⊢≡ (Γ≡Δ ∙⟨ Idⱼ ⊢A₁′ ⊢t₁′ ⊢t₁′ ⟩) B₁≡B₂)
          (stability-⊢≡∷ Γ≡Δ u₁≡u₂) (stability-⊢≡∷ Γ≡Δ v₁≡v₂) ok
      (K-β ⊢B ⊢u ok) PE.refl →
        let _ , ⊢Id                   = ∙⊢→⊢-<ˢ ⊢B
            (⊢A , A<) , (⊢t , t<) , _ = inversion-Id-⊢-<ˢ ⊢Id
            ⊢A′                       = stability-⊢ Γ≡Δ ⊢A
                                          ⦃ lt = <ˢ-trans A< ! ⦄
            ⊢t′                       = stability-⊢∷ Γ≡Δ ⊢t
                                          ⦃ lt = <ˢ-trans t< ! ⦄
        in
        K-β (stability-⊢ (Γ≡Δ ∙⟨ Idⱼ ⊢A′ ⊢t′ ⊢t′ ⟩) ⊢B)
          (stability-⊢∷ Γ≡Δ ⊢u) ok
      ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) PE.refl →
        []-cong-cong (stability-⊢≡∷L Γ≡Δ l₁≡l₂)
          (stability-⊢≡ Γ≡Δ A₁≡A₂) (stability-⊢≡∷ Γ≡Δ t₁≡t₂)
          (stability-⊢≡∷ Γ≡Δ u₁≡u₂) (stability-⊢≡∷ Γ≡Δ v₁≡v₂) ok
      ([]-cong-β ⊢l ⊢t eq ok) PE.refl →
        []-cong-β (stability-⊢∷L Γ≡Δ ⊢l) (stability-⊢∷ Γ≡Δ ⊢t) eq ok
      (equality-reflection ok ⊢Id ⊢v) PE.refl →
        equality-reflection ok (stability-⊢ Γ≡Δ ⊢Id)
          (stability-⊢∷ Γ≡Δ ⊢v)

  opaque
    unfolding size

    -- Stability for _⊢_≡_∷Level.

    stability-⊢≡∷L′ :
      (∀ {s₁} → s₁ <ˢ s₂ → P s₁) →
      ∇ »⊢ Γ ≡ Δ →
      (l₁≡l₂ : ∇ » Γ ⊢ l₁ ≡ l₂ ∷Level) →
      size l₁≡l₂ PE.≡ s₂ →
      ∇ » Δ ⊢ l₁ ≡ l₂ ∷Level
    stability-⊢≡∷L′ hyp Γ≡Δ = let open Variants hyp in λ where
      (term ok l₁≡l₂) PE.refl →
        term ok (stability-⊢≡∷ Γ≡Δ l₁≡l₂)
      (literal ok _) _ →
        literal ok (wf-⊢≡ʳ Γ≡Δ)

  opaque

    -- The type P s is inhabited for every s.

    P-inhabited : P s
    P-inhabited =
      well-founded-induction P
        (λ _ hyp →
           record
             { stability-⊢    = stability-⊢′    hyp
             ; stability-⊢≡   = stability-⊢≡′   hyp
             ; stability-⊢∷   = stability-⊢∷′   hyp
             ; stability-⊢∷L  = stability-⊢∷L′  hyp
             ; stability-⊢≡∷  = stability-⊢≡∷′  hyp
             ; stability-⊢≡∷L = stability-⊢≡∷L′ hyp
             })
        _

opaque

  -- Stability for several kinds of judgements.

  stability-⊢ : ∇ »⊢ Γ ≡ Δ → ∇ » Γ ⊢[ 𝓙 ] → ∇ » Δ ⊢[ 𝓙 ]
  stability-⊢ {𝓙 = [ctxt]} Γ≡Δ _ =
    wf-⊢≡ʳ Γ≡Δ
  stability-⊢ {𝓙 = [ _ type]} Γ≡Δ ⊢𝓙 =
    P.stability-⊢ Inhabited.P-inhabited Γ≡Δ ⊢𝓙 PE.refl
  stability-⊢ {𝓙 = [ _ ≡ _ type]} Γ≡Δ ⊢𝓙 =
    P.stability-⊢≡ Inhabited.P-inhabited Γ≡Δ ⊢𝓙 PE.refl
  stability-⊢ {𝓙 = [ _ ∷ _ ]} Γ≡Δ ⊢𝓙 =
    P.stability-⊢∷ Inhabited.P-inhabited Γ≡Δ ⊢𝓙 PE.refl
  stability-⊢ {𝓙 = [ _ ≡ _ ∷ _ ]} Γ≡Δ ⊢𝓙 =
    P.stability-⊢≡∷ Inhabited.P-inhabited Γ≡Δ ⊢𝓙 PE.refl
  stability-⊢ {𝓙 = [ _ ∷Level]} Γ≡Δ ⊢𝓙 =
    P.stability-⊢∷L Inhabited.P-inhabited Γ≡Δ ⊢𝓙 PE.refl
  stability-⊢ {𝓙 = [ _ ≡ _ ∷Level]} Γ≡Δ ⊢𝓙 =
    P.stability-⊢≡∷L Inhabited.P-inhabited Γ≡Δ ⊢𝓙 PE.refl
