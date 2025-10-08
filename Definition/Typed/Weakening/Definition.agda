------------------------------------------------------------------------
-- Weakening lemmas for the definition context
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Weakening.Definition
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Whnf M type-variant

open import Definition.Typed R
open import Definition.Typed.Properties.Definition.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Weakening R

open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE

private
  variable
    m n n′ k α : Nat
    ∇ ∇′ ∇″ : DCon (Term 0) _
    Γ Δ : Con Term _
    t t′ A A′ : Term _
    V : Set a
    φ : Unfolding _
    ω : Opacity _
    ρ : Wk _ _

------------------------------------------------------------------------
-- Well-typed definition context extensions

data DWkStep (∇ : DCon (Term 0) n) (A : Term 0) (t : Term 0) : Opacity n → Set a where
  opa : Opacity-allowed
      → ∇ » ε ⊢ A
      → Trans φ ∇ » ε ⊢ t ∷ A
      → DWkStep ∇ A t (opa φ)
  tra : ∇ » ε ⊢ t ∷ A
      → DWkStep ∇ A t tra

-- » ∇′ ⊇ ∇ means that ∇′ is a well-formed extension of ∇.

infix 4 »_⊇_

data »_⊇_ : DCon (Term 0) m → DCon (Term 0) n → Set a where
  id   : {∇′ : DCon (Term 0) m} {∇ : DCon (Term 0) n}
         (eq : m PE.≡ n) →
         PE.subst (DCon (Term 0)) eq ∇′ PE.≡ ∇ → » ∇′ ⊇ ∇
  step : » ∇′ ⊇ ∇
       → DWkStep ∇′ A t ω
       → » ∇′ ∙⟨ ω ⟩[ t ∷ A ] ⊇ ∇

pattern id⊇ = id PE.refl PE.refl
pattern stepᵒ ξ⊇ ok ⊢A ⊢t = step ξ⊇ (opa ok ⊢A ⊢t)
pattern stepᵗ ξ⊇ ⊢t = step ξ⊇ (tra ⊢t)
pattern stepᵒ₁ ok ⊢A ⊢t = stepᵒ id⊇ ok ⊢A ⊢t
pattern stepᵗ₁ ⊢t = stepᵗ id⊇ ⊢t

opaque

  -- The relation »_⊇_ is transitive.

  »⊇-trans : » ∇″ ⊇ ∇′ → » ∇′ ⊇ ∇ → » ∇″ ⊇ ∇
  »⊇-trans id⊇            ∇′⊇∇ = ∇′⊇∇
  »⊇-trans (step ∇″⊇∇′ s) ∇′⊇∇ = step (»⊇-trans ∇″⊇∇′ ∇′⊇∇) s

opaque

  -- If ∇′ is a well-formed extension of a well-formed definition
  -- context, then ∇′ is a well-formed definition context.

  wf-»⊇ : » ∇′ ⊇ ∇ → » ∇ → » ∇′
  wf-»⊇ id⊇                 »∇ = »∇
  wf-»⊇ (stepᵒ ξ⊇ ok ⊢A ⊢t) »∇ = ∙ᵒ⟨ ok ⟩[ ⊢t ∷ ⊢A ]
  wf-»⊇ (stepᵗ ξ⊇ ⊢t)       »∇ = ∙ᵗ[ ⊢t ]

opaque

  -- If ∇′ is an extension of ∇, then the length of ∇′ is at least as
  -- large as the length of ∇.

  ⊇→≤ :
    {∇  : DCon (Term 0) n}
    {∇′ : DCon (Term 0) n′} →
    » ∇′ ⊇ ∇ →
    n ≤ n′
  ⊇→≤ id⊇           = ≤-refl
  ⊇→≤ (step ∇′⊇∇ _) = ≤-trans (⊇→≤ ∇′⊇∇) (n≤1+n _)

opaque

  -- If ∇ is well-formed, then ∇ is an extension of the empty
  -- definition context.

  »⊇ε : » ∇ → » ∇ ⊇ ε
  »⊇ε ε =
    id⊇
  »⊇ε ∙ᵗ[ ⊢t ] =
    stepᵗ (»⊇ε (defn-wf (wfTerm ⊢t))) ⊢t
  »⊇ε ∙ᵒ⟨ ok ⟩[ ⊢t ∷ ⊢A ] =
    stepᵒ (»⊇ε (defn-wf (wf ⊢A))) ok ⊢A ⊢t

------------------------------------------------------------------------
-- Weakening for properties of definitions

opaque

  -- A definition weakening lemma for the definition context.

  there*-↦∈ : » ∇′ ⊇ ∇ → α ↦∷ A ∈ ∇ → α ↦∷ A ∈ ∇′
  there*-↦∈ id⊇         α↦t = α↦t
  there*-↦∈ (step ξ⊇ s) α↦t = there (there*-↦∈ ξ⊇ α↦t)

opaque

  -- A definition weakening lemma for the definition context.

  there*-↦∷∈ : » ∇′ ⊇ ∇ → α ↦ t ∷ A ∈ ∇ → α ↦ t ∷ A ∈ ∇′
  there*-↦∷∈ id⊇         α↦t = α↦t
  there*-↦∷∈ (step ξ⊇ s) α↦t = there (there*-↦∷∈ ξ⊇ α↦t)

opaque

  -- A definition weakening lemma for the definition context.

  there*-↦⊘∈ : » ∇′ ⊇ ∇ → α ↦⊘∷ A ∈ ∇ → α ↦⊘∷ A ∈ ∇′
  there*-↦⊘∈ id⊇         α↦t = α↦t
  there*-↦⊘∈ (step ξ⊇ s) α↦t = there (there*-↦⊘∈ ξ⊇ α↦t)

------------------------------------------------------------------------
-- A glassification lemma

opaque

  -- A glassification lemma for _»_⊇_.

  glassify-»⊇ : » ∇′ ⊇ ∇ → » glassify ∇′ ⊇ glassify ∇
  glassify-»⊇ id⊇ =
    id⊇
  glassify-»⊇ (stepᵗ ξ⊇ ⊢t) =
    stepᵗ (glassify-»⊇ ξ⊇) (glassify-⊢∷ ⊢t)
  glassify-»⊇ (stepᵒ ξ⊇ _ _ ⊢t) =
    stepᵗ (glassify-»⊇ ξ⊇)
      (PE.subst₃ _⊢_∷_
         (PE.cong (_» _) glassify-factor) PE.refl PE.refl $
       glassify-⊢∷ ⊢t)

------------------------------------------------------------------------
-- Weakening for typing derivations

opaque mutual

  -- Single-weakening lemmas for the definition context.

  defn-wk′ : » ∇′ ⊇ ∇ → ∇ »⊢ Γ → ∇′ »⊢ Γ
  defn-wk′ ξ⊇ (ε »∇) = ε (wf-»⊇ ξ⊇ »∇)
  defn-wk′ ξ⊇ (∙ ⊢Γ) = ∙ defn-wk ξ⊇ ⊢Γ

  defn-wk : » ∇′ ⊇ ∇ → ∇ » Γ ⊢ A → ∇′ » Γ ⊢ A
  defn-wk ξ⊇ (Uⱼ ⊢Γ) = Uⱼ (defn-wk′ ξ⊇ ⊢Γ)
  defn-wk ξ⊇ (ℕⱼ ⊢Γ) = ℕⱼ (defn-wk′ ξ⊇ ⊢Γ)
  defn-wk ξ⊇ (Emptyⱼ ⊢Γ) = Emptyⱼ (defn-wk′ ξ⊇ ⊢Γ)
  defn-wk ξ⊇ (Unitⱼ ⊢Γ ok) = Unitⱼ (defn-wk′ ξ⊇ ⊢Γ) ok
  defn-wk ξ⊇ (ΠΣⱼ ⊢A ok) = ΠΣⱼ (defn-wk ξ⊇ ⊢A) ok
  defn-wk ξ⊇ (Idⱼ ⊢A ⊢t₁ ⊢t₂) =
    Idⱼ (defn-wk ξ⊇ ⊢A)
        (defn-wkTerm ξ⊇ ⊢t₁)
        (defn-wkTerm ξ⊇ ⊢t₂)
  defn-wk ξ⊇ (univ ⊢A) = univ (defn-wkTerm ξ⊇ ⊢A)

  defn-wkTerm : » ∇′ ⊇ ∇ → ∇ » Γ ⊢ t ∷ A → ∇′ » Γ ⊢ t ∷ A
  defn-wkTerm ξ⊇ (Uⱼ ⊢Γ) = Uⱼ (defn-wk′ ξ⊇ ⊢Γ)
  defn-wkTerm ξ⊇ (ΠΣⱼ ⊢t₁ ⊢t₂ ok) =
    ΠΣⱼ (defn-wkTerm ξ⊇ ⊢t₁) (defn-wkTerm ξ⊇ ⊢t₂) ok
  defn-wkTerm ξ⊇ (ℕⱼ ⊢Γ) = ℕⱼ (defn-wk′ ξ⊇ ⊢Γ)
  defn-wkTerm ξ⊇ (Emptyⱼ ⊢Γ) = Emptyⱼ (defn-wk′ ξ⊇ ⊢Γ)
  defn-wkTerm ξ⊇ (Unitⱼ ⊢Γ ok) = Unitⱼ (defn-wk′ ξ⊇ ⊢Γ) ok
  defn-wkTerm ξ⊇ (conv ⊢t A≡A′) =
    conv (defn-wkTerm ξ⊇ ⊢t) (defn-wkEq ξ⊇ A≡A′)
  defn-wkTerm ξ⊇ (var ⊢Γ x∈) = var (defn-wk′ ξ⊇ ⊢Γ) x∈
  defn-wkTerm ξ⊇ (defn ⊢Γ α↦t A≡A′) =
    defn (defn-wk′ ξ⊇ ⊢Γ) (there*-↦∈ ξ⊇ α↦t) A≡A′
  defn-wkTerm ξ⊇ (lamⱼ ⊢A ⊢t ok) =
    lamⱼ (defn-wk ξ⊇ ⊢A) (defn-wkTerm ξ⊇ ⊢t) ok
  defn-wkTerm ξ⊇ (⊢t₁ ∘ⱼ ⊢t₂) =
    defn-wkTerm ξ⊇ ⊢t₁ ∘ⱼ defn-wkTerm ξ⊇ ⊢t₂
  defn-wkTerm ξ⊇ (prodⱼ ⊢A ⊢t₁ ⊢t₂ ok) =
    prodⱼ (defn-wk ξ⊇ ⊢A)
          (defn-wkTerm ξ⊇ ⊢t₁)
          (defn-wkTerm ξ⊇ ⊢t₂)
          ok
  defn-wkTerm ξ⊇ (fstⱼ ⊢A ⊢t) =
    fstⱼ (defn-wk ξ⊇ ⊢A) (defn-wkTerm ξ⊇ ⊢t)
  defn-wkTerm ξ⊇ (sndⱼ ⊢A ⊢t) =
    sndⱼ (defn-wk ξ⊇ ⊢A) (defn-wkTerm ξ⊇ ⊢t)
  defn-wkTerm ξ⊇ (prodrecⱼ ⊢A ⊢t ⊢t′ ok) =
    prodrecⱼ (defn-wk ξ⊇ ⊢A)
             (defn-wkTerm ξ⊇ ⊢t)
             (defn-wkTerm ξ⊇ ⊢t′)
             ok
  defn-wkTerm ξ⊇ (zeroⱼ ⊢Γ) = zeroⱼ (defn-wk′ ξ⊇ ⊢Γ)
  defn-wkTerm ξ⊇ (sucⱼ ⊢t) = sucⱼ (defn-wkTerm ξ⊇ ⊢t)
  defn-wkTerm ξ⊇ (natrecⱼ ⊢t₀ ⊢tₛ ⊢t) =
    natrecⱼ (defn-wkTerm ξ⊇ ⊢t₀)
            (defn-wkTerm ξ⊇ ⊢tₛ)
            (defn-wkTerm ξ⊇ ⊢t)
  defn-wkTerm ξ⊇ (emptyrecⱼ ⊢A ⊢t) =
    emptyrecⱼ (defn-wk ξ⊇ ⊢A) (defn-wkTerm ξ⊇ ⊢t)
  defn-wkTerm ξ⊇ (starⱼ ⊢Γ ok) = starⱼ (defn-wk′ ξ⊇ ⊢Γ) ok
  defn-wkTerm ξ⊇ (unitrecⱼ ⊢A ⊢t ⊢t′ ok) =
    unitrecⱼ (defn-wk ξ⊇ ⊢A)
             (defn-wkTerm ξ⊇ ⊢t)
             (defn-wkTerm ξ⊇ ⊢t′)
             ok
  defn-wkTerm ξ⊇ (Idⱼ ⊢A ⊢t₁ ⊢t₂) =
    Idⱼ (defn-wkTerm ξ⊇ ⊢A)
        (defn-wkTerm ξ⊇ ⊢t₁)
        (defn-wkTerm ξ⊇ ⊢t₂)
  defn-wkTerm ξ⊇ (rflⱼ ⊢t) = rflⱼ (defn-wkTerm ξ⊇ ⊢t)
  defn-wkTerm ξ⊇ (Jⱼ ⊢t ⊢A ⊢tᵣ ⊢t′ ⊢tₚ) =
    Jⱼ (defn-wkTerm ξ⊇ ⊢t)
       (defn-wk ξ⊇ ⊢A)
       (defn-wkTerm ξ⊇ ⊢tᵣ)
       (defn-wkTerm ξ⊇ ⊢t′)
       (defn-wkTerm ξ⊇ ⊢tₚ)
  defn-wkTerm ξ⊇ (Kⱼ ⊢A ⊢tᵣ ⊢tₚ ok) =
    Kⱼ (defn-wk ξ⊇ ⊢A)
       (defn-wkTerm ξ⊇ ⊢tᵣ)
       (defn-wkTerm ξ⊇ ⊢tₚ)
       ok
  defn-wkTerm ξ⊇ ([]-congⱼ ⊢A ⊢t₁ ⊢t₂ ⊢tₚ ok) =
    []-congⱼ (defn-wk ξ⊇ ⊢A)
             (defn-wkTerm ξ⊇ ⊢t₁)
             (defn-wkTerm ξ⊇ ⊢t₂)
             (defn-wkTerm ξ⊇ ⊢tₚ) ok

  defn-wkEq : » ∇′ ⊇ ∇ → ∇ » Γ ⊢ A ≡ A′ → ∇′ » Γ ⊢ A ≡ A′
  defn-wkEq ξ⊇ (univ A≡A′) = univ (defn-wkEqTerm ξ⊇ A≡A′)
  defn-wkEq ξ⊇ (refl ⊢A) = refl (defn-wk ξ⊇ ⊢A)
  defn-wkEq ξ⊇ (sym A≡A′) = sym (defn-wkEq ξ⊇ A≡A′)
  defn-wkEq ξ⊇ (trans A≡A′ A′≡A″) =
    trans (defn-wkEq ξ⊇ A≡A′) (defn-wkEq ξ⊇ A′≡A″)
  defn-wkEq ξ⊇ (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) =
    ΠΣ-cong (defn-wkEq ξ⊇ A₁≡A₂) (defn-wkEq ξ⊇ B₁≡B₂) ok
  defn-wkEq ξ⊇ (Id-cong A≡A′ t₁≡t₂ u₁≡u₂) =
    Id-cong (defn-wkEq ξ⊇ A≡A′)
            (defn-wkEqTerm ξ⊇ t₁≡t₂)
            (defn-wkEqTerm ξ⊇ u₁≡u₂)

  defn-wkEqTerm : » ∇′ ⊇ ∇ → ∇ » Γ ⊢ t ≡ t′ ∷ A → ∇′ » Γ ⊢ t ≡ t′ ∷ A
  defn-wkEqTerm ξ⊇ (refl ⊢t) = refl (defn-wkTerm ξ⊇ ⊢t)
  defn-wkEqTerm ξ⊇ (sym ⊢A t≡t′) =
    sym (defn-wk ξ⊇ ⊢A) (defn-wkEqTerm ξ⊇ t≡t′)
  defn-wkEqTerm ξ⊇ (trans t≡t′ t′≡t″) =
    trans (defn-wkEqTerm ξ⊇ t≡t′) (defn-wkEqTerm ξ⊇ t′≡t″)
  defn-wkEqTerm ξ⊇ (conv t≡t′ A≡A′) =
    conv (defn-wkEqTerm ξ⊇ t≡t′) (defn-wkEq ξ⊇ A≡A′)
  defn-wkEqTerm ξ⊇ (δ-red ⊢Γ α↦t A≡A′ t≡t′) =
    δ-red (defn-wk′ ξ⊇ ⊢Γ) (there*-↦∷∈ ξ⊇ α↦t) A≡A′ t≡t′
  defn-wkEqTerm ξ⊇ (ΠΣ-cong t₁≡t₂ u₁≡u₂ ok) =
    ΠΣ-cong (defn-wkEqTerm ξ⊇ t₁≡t₂) (defn-wkEqTerm ξ⊇ u₁≡u₂) ok
  defn-wkEqTerm ξ⊇ (app-cong t₁≡t₂ u₁≡u₂) =
    app-cong (defn-wkEqTerm ξ⊇ t₁≡t₂) (defn-wkEqTerm ξ⊇ u₁≡u₂)
  defn-wkEqTerm ξ⊇ (β-red ⊢A ⊢t ⊢x eq ok) =
    β-red (defn-wk ξ⊇ ⊢A)
          (defn-wkTerm ξ⊇ ⊢t)
          (defn-wkTerm ξ⊇ ⊢x)
          eq ok
  defn-wkEqTerm ξ⊇ (η-eq ⊢A ⊢t ⊢t′ t≡t′ ok) =
    η-eq (defn-wk ξ⊇ ⊢A)
         (defn-wkTerm ξ⊇ ⊢t)
         (defn-wkTerm ξ⊇ ⊢t′)
         (defn-wkEqTerm ξ⊇ t≡t′)
         ok
  defn-wkEqTerm ξ⊇ (fst-cong ⊢A t≡t′) =
    fst-cong (defn-wk ξ⊇ ⊢A) (defn-wkEqTerm ξ⊇ t≡t′)
  defn-wkEqTerm ξ⊇ (snd-cong ⊢A t≡t′) =
    snd-cong (defn-wk ξ⊇ ⊢A) (defn-wkEqTerm ξ⊇ t≡t′)
  defn-wkEqTerm ξ⊇ (Σ-β₁ ⊢A ⊢t ⊢t′ eq ok) =
    Σ-β₁ (defn-wk ξ⊇ ⊢A)
         (defn-wkTerm ξ⊇ ⊢t)
         (defn-wkTerm ξ⊇ ⊢t′)
         eq ok
  defn-wkEqTerm ξ⊇ (Σ-β₂ ⊢A ⊢t ⊢t′ eq ok) =
    Σ-β₂ (defn-wk ξ⊇ ⊢A)
         (defn-wkTerm ξ⊇ ⊢t)
         (defn-wkTerm ξ⊇ ⊢t′)
         eq ok
  defn-wkEqTerm ξ⊇ (Σ-η ⊢A ⊢t ⊢t′ fst≡ snd≡ ok) =
    Σ-η (defn-wk ξ⊇ ⊢A)
        (defn-wkTerm ξ⊇ ⊢t)
        (defn-wkTerm ξ⊇ ⊢t′)
        (defn-wkEqTerm ξ⊇ fst≡)
        (defn-wkEqTerm ξ⊇ snd≡)
        ok
  defn-wkEqTerm ξ⊇ (prod-cong ⊢A t₁≡t₂ u₁≡u₂ ok) =
    prod-cong (defn-wk ξ⊇ ⊢A)
              (defn-wkEqTerm ξ⊇ t₁≡t₂)
              (defn-wkEqTerm ξ⊇ u₁≡u₂)
              ok
  defn-wkEqTerm ξ⊇ (prodrec-cong A≡A′ t₁≡t₂ u₁≡u₂ ok) =
    prodrec-cong (defn-wkEq ξ⊇ A≡A′)
                 (defn-wkEqTerm ξ⊇ t₁≡t₂)
                 (defn-wkEqTerm ξ⊇ u₁≡u₂)
                 ok
  defn-wkEqTerm ξ⊇ (prodrec-β ⊢A ⊢t₁ ⊢t₂ ⊢tᵣ eq ok) =
    prodrec-β (defn-wk ξ⊇ ⊢A)
              (defn-wkTerm ξ⊇ ⊢t₁)
              (defn-wkTerm ξ⊇ ⊢t₂)
              (defn-wkTerm ξ⊇ ⊢tᵣ)
              eq ok
  defn-wkEqTerm ξ⊇ (suc-cong t≡t′) =
    suc-cong (defn-wkEqTerm ξ⊇ t≡t′)
  defn-wkEqTerm ξ⊇ (natrec-cong A≡A′ 0≡ s≡ t≡t′) =
    natrec-cong (defn-wkEq ξ⊇ A≡A′)
                (defn-wkEqTerm ξ⊇ 0≡)
                (defn-wkEqTerm ξ⊇ s≡)
                (defn-wkEqTerm ξ⊇ t≡t′)
  defn-wkEqTerm ξ⊇ (natrec-zero ⊢t₀ ⊢tₛ) =
    natrec-zero (defn-wkTerm ξ⊇ ⊢t₀) (defn-wkTerm ξ⊇ ⊢tₛ)
  defn-wkEqTerm ξ⊇ (natrec-suc ⊢t₀ ⊢tₛ ⊢t) =
    natrec-suc (defn-wkTerm ξ⊇ ⊢t₀)
               (defn-wkTerm ξ⊇ ⊢tₛ)
               (defn-wkTerm ξ⊇ ⊢t)
  defn-wkEqTerm ξ⊇ (emptyrec-cong A≡A′ t≡t′) =
    emptyrec-cong (defn-wkEq ξ⊇ A≡A′) (defn-wkEqTerm ξ⊇ t≡t′)
  defn-wkEqTerm ξ⊇ (unitrec-cong A≡A′ t≡t′ r≡ ok no-η) =
    unitrec-cong (defn-wkEq ξ⊇ A≡A′)
                 (defn-wkEqTerm ξ⊇ t≡t′)
                 (defn-wkEqTerm ξ⊇ r≡)
                 ok no-η
  defn-wkEqTerm ξ⊇ (unitrec-β ⊢A ⊢t ok no-η) =
    unitrec-β (defn-wk ξ⊇ ⊢A) (defn-wkTerm ξ⊇ ⊢t) ok no-η
  defn-wkEqTerm ξ⊇ (unitrec-β-η ⊢A ⊢t ⊢tᵣ ok η) =
    unitrec-β-η (defn-wk ξ⊇ ⊢A)
                (defn-wkTerm ξ⊇ ⊢t)
                (defn-wkTerm ξ⊇ ⊢tᵣ)
                ok η
  defn-wkEqTerm ξ⊇ (η-unit ⊢t ⊢t′ η) =
    η-unit (defn-wkTerm ξ⊇ ⊢t) (defn-wkTerm ξ⊇ ⊢t′) η
  defn-wkEqTerm ξ⊇ (Id-cong A≡A′ t₁≡t₂ u₁≡u₂) =
    Id-cong (defn-wkEqTerm ξ⊇ A≡A′)
            (defn-wkEqTerm ξ⊇ t₁≡t₂)
            (defn-wkEqTerm ξ⊇ u₁≡u₂)
  defn-wkEqTerm ξ⊇ (J-cong A≡A′ ⊢t t≡t′ B₁≡B₂ r≡ x≡ p≡) =
    J-cong (defn-wkEq ξ⊇ A≡A′)
           (defn-wkTerm ξ⊇ ⊢t)
           (defn-wkEqTerm ξ⊇ t≡t′)
           (defn-wkEq ξ⊇ B₁≡B₂)
           (defn-wkEqTerm ξ⊇ r≡)
           (defn-wkEqTerm ξ⊇ x≡)
           (defn-wkEqTerm ξ⊇ p≡)
  defn-wkEqTerm ξ⊇ (K-cong A≡A′ t≡t′ B₁≡B₂ r≡ p≡ ok) =
    K-cong (defn-wkEq ξ⊇ A≡A′)
           (defn-wkEqTerm ξ⊇ t≡t′)
           (defn-wkEq ξ⊇ B₁≡B₂)
           (defn-wkEqTerm ξ⊇ r≡)
           (defn-wkEqTerm ξ⊇ p≡)
           ok
  defn-wkEqTerm ξ⊇ ([]-cong-cong A≡A′ t₁≡t₂ u₁≡u₂ p≡p′ ok) =
    []-cong-cong (defn-wkEq ξ⊇ A≡A′)
                 (defn-wkEqTerm ξ⊇ t₁≡t₂)
                 (defn-wkEqTerm ξ⊇ u₁≡u₂)
                 (defn-wkEqTerm ξ⊇ p≡p′) ok
  defn-wkEqTerm ξ⊇ (J-β ⊢t ⊢A ⊢tᵣ eq) =
    J-β (defn-wkTerm ξ⊇ ⊢t)
        (defn-wk ξ⊇ ⊢A)
        (defn-wkTerm ξ⊇ ⊢tᵣ)
        eq
  defn-wkEqTerm ξ⊇ (K-β ⊢A ⊢t ok) =
    K-β (defn-wk ξ⊇ ⊢A) (defn-wkTerm ξ⊇ ⊢t) ok
  defn-wkEqTerm ξ⊇ ([]-cong-β ⊢t eq ok) =
    []-cong-β (defn-wkTerm ξ⊇ ⊢t) eq ok
  defn-wkEqTerm ξ⊇ (equality-reflection ok ⊢Id ⊢t) =
    equality-reflection ok (defn-wk ξ⊇ ⊢Id) (defn-wkTerm ξ⊇ ⊢t)

------------------------------------------------------------------------
-- Weakening for weakenings

opaque

  -- A definitional weakening lemma for weakenings.

  defn-wkWkʷ : » ∇′ ⊇ ∇ → ∇ » ρ ∷ʷ Δ ⊇ Γ → ∇′ » ρ ∷ʷ Δ ⊇ Γ
  defn-wkWkʷ ξ⊇ ρ = ∷⊇→∷ʷ⊇ (∷ʷ⊇→∷⊇ ρ) (defn-wk′ ξ⊇ (wf-∷ʷ⊇ ρ))

------------------------------------------------------------------------
-- Weakening for reduction

opaque

  -- A reduction weakening lemma for the definition context.

  defn-wkRedTerm : » ∇′ ⊇ ∇ → ∇ » Γ ⊢ t ⇒ t′ ∷ A → ∇′ » Γ ⊢ t ⇒ t′ ∷ A
  defn-wkRedTerm ξ⊇ (conv t⇒t′ A≡A′) =
    conv (defn-wkRedTerm ξ⊇ t⇒t′) (defn-wkEq ξ⊇ A≡A′)
  defn-wkRedTerm ξ⊇ (δ-red ⊢Γ α↦t A≡A′ T≡T′) =
    δ-red (defn-wk′ ξ⊇ ⊢Γ) (there*-↦∷∈ ξ⊇ α↦t) A≡A′ T≡T′
  defn-wkRedTerm ξ⊇ (app-subst t⇒t′ ⊢a) =
    app-subst (defn-wkRedTerm ξ⊇ t⇒t′) (defn-wkTerm ξ⊇ ⊢a)
  defn-wkRedTerm ξ⊇ (β-red ⊢A ⊢t ⊢x eq ok) =
    β-red (defn-wk ξ⊇ ⊢A)
          (defn-wkTerm ξ⊇ ⊢t)
          (defn-wkTerm ξ⊇ ⊢x)
          eq ok
  defn-wkRedTerm ξ⊇ (fst-subst ⊢A t⇒t′) =
    fst-subst (defn-wk ξ⊇ ⊢A) (defn-wkRedTerm ξ⊇ t⇒t′)
  defn-wkRedTerm ξ⊇ (snd-subst ⊢A t⇒t′) =
    snd-subst (defn-wk ξ⊇ ⊢A) (defn-wkRedTerm ξ⊇ t⇒t′)
  defn-wkRedTerm ξ⊇ (Σ-β₁ ⊢A ⊢t ⊢t′ eq ok) =
    Σ-β₁ (defn-wk ξ⊇ ⊢A)
         (defn-wkTerm ξ⊇ ⊢t)
         (defn-wkTerm ξ⊇ ⊢t′)
         eq ok
  defn-wkRedTerm ξ⊇ (Σ-β₂ ⊢A ⊢t ⊢t′ eq ok) =
    Σ-β₂ (defn-wk ξ⊇ ⊢A)
         (defn-wkTerm ξ⊇ ⊢t)
         (defn-wkTerm ξ⊇ ⊢t′)
         eq ok
  defn-wkRedTerm ξ⊇ (prodrec-subst ⊢A ⊢a t⇒t′ ok) =
    prodrec-subst (defn-wk ξ⊇ ⊢A)
                  (defn-wkTerm ξ⊇ ⊢a)
                  (defn-wkRedTerm ξ⊇ t⇒t′)
                  ok
  defn-wkRedTerm ξ⊇ (prodrec-β ⊢A ⊢t ⊢t₂ ⊢tᵣ eq ok) =
    prodrec-β (defn-wk ξ⊇ ⊢A)
              (defn-wkTerm ξ⊇ ⊢t)
              (defn-wkTerm ξ⊇ ⊢t₂)
              (defn-wkTerm ξ⊇ ⊢tᵣ)
              eq ok
  defn-wkRedTerm ξ⊇ (natrec-subst ⊢t₀ ⊢tₛ t⇒t′) =
    natrec-subst (defn-wkTerm ξ⊇ ⊢t₀)
                 (defn-wkTerm ξ⊇ ⊢tₛ)
                 (defn-wkRedTerm ξ⊇ t⇒t′)
  defn-wkRedTerm ξ⊇ (natrec-zero ⊢t₀ ⊢tₛ) =
    natrec-zero (defn-wkTerm ξ⊇ ⊢t₀) (defn-wkTerm ξ⊇ ⊢tₛ)
  defn-wkRedTerm ξ⊇ (natrec-suc ⊢t₀ ⊢tₛ ⊢t) =
    natrec-suc (defn-wkTerm ξ⊇ ⊢t₀)
               (defn-wkTerm ξ⊇ ⊢tₛ)
               (defn-wkTerm ξ⊇ ⊢t)
  defn-wkRedTerm ξ⊇ (emptyrec-subst ⊢A t⇒t′) =
    emptyrec-subst (defn-wk ξ⊇ ⊢A) (defn-wkRedTerm ξ⊇ t⇒t′)
  defn-wkRedTerm ξ⊇ (unitrec-subst ⊢A ⊢a t⇒t′ ok no-η) =
    unitrec-subst (defn-wk ξ⊇ ⊢A)
                  (defn-wkTerm ξ⊇ ⊢a)
                  (defn-wkRedTerm ξ⊇ t⇒t′)
                  ok no-η
  defn-wkRedTerm ξ⊇ (unitrec-β ⊢A ⊢t ok no-η) =
    unitrec-β (defn-wk ξ⊇ ⊢A) (defn-wkTerm ξ⊇ ⊢t) ok no-η
  defn-wkRedTerm ξ⊇ (unitrec-β-η ⊢A ⊢t ⊢tᵣ ok η) =
    unitrec-β-η (defn-wk ξ⊇ ⊢A)
                (defn-wkTerm ξ⊇ ⊢t)
                (defn-wkTerm ξ⊇ ⊢tᵣ)
                ok η
  defn-wkRedTerm ξ⊇ (J-subst ⊢t ⊢A ⊢r ⊢p w⇒w′) =
    J-subst (defn-wkTerm ξ⊇ ⊢t)
            (defn-wk ξ⊇ ⊢A)
            (defn-wkTerm ξ⊇ ⊢r)
            (defn-wkTerm ξ⊇ ⊢p)
            (defn-wkRedTerm ξ⊇ w⇒w′)
  defn-wkRedTerm ξ⊇ (K-subst ⊢A ⊢r t⇒t′ ok) =
    K-subst (defn-wk ξ⊇ ⊢A)
            (defn-wkTerm ξ⊇ ⊢r)
            (defn-wkRedTerm ξ⊇ t⇒t′)
            ok
  defn-wkRedTerm ξ⊇ ([]-cong-subst ⊢A ⊢a ⊢a′ t⇒t′ ok) =
    []-cong-subst (defn-wk ξ⊇ ⊢A)
                  (defn-wkTerm ξ⊇ ⊢a)
                  (defn-wkTerm ξ⊇ ⊢a′)
                  (defn-wkRedTerm ξ⊇ t⇒t′)
                  ok
  defn-wkRedTerm ξ⊇ (J-β ⊢t ⊢t′ t≡t′ ⊢A A≡ ⊢tᵣ) =
    J-β (defn-wkTerm ξ⊇ ⊢t)
        (defn-wkTerm ξ⊇ ⊢t′)
        (defn-wkEqTerm ξ⊇ t≡t′)
        (defn-wk ξ⊇ ⊢A)
        (defn-wkEq ξ⊇ A≡)
        (defn-wkTerm ξ⊇ ⊢tᵣ)
  defn-wkRedTerm ξ⊇ (K-β ⊢A ⊢t ok) =
    K-β (defn-wk ξ⊇ ⊢A) (defn-wkTerm ξ⊇ ⊢t) ok
  defn-wkRedTerm ξ⊇ ([]-cong-β ⊢A ⊢t ⊢t′ t≡t′ ok) =
    []-cong-β (defn-wk ξ⊇ ⊢A)
              (defn-wkTerm ξ⊇ ⊢t)
              (defn-wkTerm ξ⊇ ⊢t′)
              (defn-wkEqTerm ξ⊇ t≡t′)
              ok

opaque

  -- A reduction weakening lemma for the definition context.

  defn-wkRed : » ∇′ ⊇ ∇ → ∇ » Γ ⊢ A ⇒ A′ → ∇′ » Γ ⊢ A ⇒ A′
  defn-wkRed ξ⊇ (univ A⇒A′) = univ (defn-wkRedTerm ξ⊇ A⇒A′)

opaque

  -- A multi-step reduction weakening lemma for the definition context.

  defn-wkRed* : » ∇′ ⊇ ∇ → ∇ » Γ ⊢ A ⇒* A′ → ∇′ » Γ ⊢ A ⇒* A′
  defn-wkRed* ξ⊇ (id ⊢A)       = id (defn-wk ξ⊇ ⊢A)
  defn-wkRed* ξ⊇ (A⇒X ⇨ X⇒*A′) = defn-wkRed ξ⊇ A⇒X ⇨ defn-wkRed* ξ⊇ X⇒*A′

opaque

  -- A multi-step reduction weakening lemma for the definition context.

  defn-wkRed*Term :
    » ∇′ ⊇ ∇ → ∇ » Γ ⊢ t ⇒* t′ ∷ A → ∇′ » Γ ⊢ t ⇒* t′ ∷ A
  defn-wkRed*Term ξ⊇ (id ⊢t)       = id (defn-wkTerm ξ⊇ ⊢t)
  defn-wkRed*Term ξ⊇ (t⇒x ⇨ x⇒*t′) =
    defn-wkRedTerm ξ⊇ t⇒x ⇨ defn-wkRed*Term ξ⊇ x⇒*t′

------------------------------------------------------------------------
-- Weakening for WHNF properties

opaque

  -- A neutral term weakening lemma for the definition context.

  defn-wkNeutral : » ∇′ ⊇ ∇ → Neutral V ∇ t → Neutral V ∇′ t
  defn-wkNeutral ξ⊇ (defn α↦⊘)     = defn (there*-↦⊘∈ ξ⊇ α↦⊘)
  defn-wkNeutral ξ⊇ (var ok x)     = var ok x
  defn-wkNeutral ξ⊇ (∘ₙ b)         = ∘ₙ (defn-wkNeutral ξ⊇ b)
  defn-wkNeutral ξ⊇ (fstₙ b)       = fstₙ (defn-wkNeutral ξ⊇ b)
  defn-wkNeutral ξ⊇ (sndₙ b)       = sndₙ (defn-wkNeutral ξ⊇ b)
  defn-wkNeutral ξ⊇ (natrecₙ b)    = natrecₙ (defn-wkNeutral ξ⊇ b)
  defn-wkNeutral ξ⊇ (prodrecₙ b)   = prodrecₙ (defn-wkNeutral ξ⊇ b)
  defn-wkNeutral ξ⊇ (emptyrecₙ b)  = emptyrecₙ (defn-wkNeutral ξ⊇ b)
  defn-wkNeutral ξ⊇ (unitrecₙ x b) = unitrecₙ x (defn-wkNeutral ξ⊇ b)
  defn-wkNeutral ξ⊇ (Jₙ b)         = Jₙ (defn-wkNeutral ξ⊇ b)
  defn-wkNeutral ξ⊇ (Kₙ b)         = Kₙ (defn-wkNeutral ξ⊇ b)
  defn-wkNeutral ξ⊇ ([]-congₙ b)   = []-congₙ (defn-wkNeutral ξ⊇ b)

opaque

  -- A WHNF weakening lemma for the definition context.

  defn-wkWhnf : » ∇′ ⊇ ∇ → Whnf ∇ t → Whnf ∇′ t
  defn-wkWhnf ξ⊇ Uₙ     = Uₙ
  defn-wkWhnf ξ⊇ ΠΣₙ    = ΠΣₙ
  defn-wkWhnf ξ⊇ ℕₙ     = ℕₙ
  defn-wkWhnf ξ⊇ Unitₙ  = Unitₙ
  defn-wkWhnf ξ⊇ Emptyₙ = Emptyₙ
  defn-wkWhnf ξ⊇ Idₙ    = Idₙ
  defn-wkWhnf ξ⊇ lamₙ   = lamₙ
  defn-wkWhnf ξ⊇ zeroₙ  = zeroₙ
  defn-wkWhnf ξ⊇ sucₙ   = sucₙ
  defn-wkWhnf ξ⊇ starₙ  = starₙ
  defn-wkWhnf ξ⊇ prodₙ  = prodₙ
  defn-wkWhnf ξ⊇ rflₙ   = rflₙ
  defn-wkWhnf ξ⊇ (ne n) = ne (defn-wkNeutral ξ⊇ n)

opaque

  -- A WHNF view weakening lemma for the definition context.

  defn-wkNatural : » ∇′ ⊇ ∇ → Natural V ∇ t → Natural V ∇′ t
  defn-wkNatural ξ⊇ sucₙ   = sucₙ
  defn-wkNatural ξ⊇ zeroₙ  = zeroₙ
  defn-wkNatural ξ⊇ (ne n) = ne (defn-wkNeutral ξ⊇ n)

opaque

  -- A WHNF view weakening lemma for the definition context.

  defn-wkType : » ∇′ ⊇ ∇ → Type V ∇ t → Type V ∇′ t
  defn-wkType ξ⊇ Uₙ     = Uₙ
  defn-wkType ξ⊇ ΠΣₙ    = ΠΣₙ
  defn-wkType ξ⊇ ℕₙ     = ℕₙ
  defn-wkType ξ⊇ Emptyₙ = Emptyₙ
  defn-wkType ξ⊇ Unitₙ  = Unitₙ
  defn-wkType ξ⊇ Idₙ    = Idₙ
  defn-wkType ξ⊇ (ne n) = ne (defn-wkNeutral ξ⊇ n)

opaque

  -- A WHNF view weakening lemma for the definition context.

  defn-wkFunction : » ∇′ ⊇ ∇ → Function V ∇ t → Function V ∇′ t
  defn-wkFunction ξ⊇ lamₙ   = lamₙ
  defn-wkFunction ξ⊇ (ne n) = ne (defn-wkNeutral ξ⊇ n)

opaque

  -- A WHNF view weakening lemma for the definition context.

  defn-wkProduct : » ∇′ ⊇ ∇ → Product V ∇ t → Product V ∇′ t
  defn-wkProduct ξ⊇ prodₙ  = prodₙ
  defn-wkProduct ξ⊇ (ne n) = ne (defn-wkNeutral ξ⊇ n)

opaque

  -- A WHNF view weakening lemma for the definition context.

  defn-wkIdentity : » ∇′ ⊇ ∇ → Identity V ∇ t → Identity V ∇′ t
  defn-wkIdentity ξ⊇ rflₙ   = rflₙ
  defn-wkIdentity ξ⊇ (ne n) = ne (defn-wkNeutral ξ⊇ n)

opaque

  -- A normalization weakening lemma for the definition context.

  defn-wkRed↘ : » ∇′ ⊇ ∇ → ∇ » Γ ⊢ A ↘ A′ → ∇′ » Γ ⊢ A ↘ A′
  defn-wkRed↘ ξ⊇ (A⇒*A′ , w) = defn-wkRed* ξ⊇ A⇒*A′ , defn-wkWhnf ξ⊇ w

opaque

  -- A normalization weakening lemma for the definition context.

  defn-wkRed↘Term : » ∇′ ⊇ ∇ → ∇ » Γ ⊢ t ↘ t′ ∷ A → ∇′ » Γ ⊢ t ↘ t′ ∷ A
  defn-wkRed↘Term ξ⊇ (t⇒*t′ , w) = defn-wkRed*Term ξ⊇ t⇒*t′ , defn-wkWhnf ξ⊇ w
