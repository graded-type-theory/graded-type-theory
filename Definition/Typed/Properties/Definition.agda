------------------------------------------------------------------------
-- Lemmas related to definitions
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Definition
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Admissible.Equality R
open import Definition.Typed.Properties.Admissible.Identity R
open import Definition.Typed.Properties.Admissible.Pi R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Admissible.Unit R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Variant
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private
  variable
    n α : Nat
    ∇ ∇′ ∇″ : DCon (Term 0) _
    Γ : Con Term _
    t u v w A B C : Term _
    V : Set a
    φ : Unfolding _

------------------------------------------------------------------------
-- Lemmas about opacity

opaque

  opaque-ok : » ∇ → α ↦⊘∷ A ∈ ∇ → Opacity-allowed
  opaque-ok ε                       ()
  opaque-ok ∙ᵒ⟨ ok , _ ⟩[ _  ∷ ⊢A ] here        = ok
  opaque-ok           ∙ᵗ[ ⊢t      ] (there α↦⊘) = opaque-ok (defn-wf (wfTerm ⊢t)) α↦⊘
  opaque-ok ∙ᵒ⟨ ok , _ ⟩[ _  ∷ ⊢A ] (there α↦⊘) = opaque-ok (defn-wf (wf ⊢A)) α↦⊘

opaque

  ne-opaque-ok : » ∇ → Neutral⁻ ∇ t → Opacity-allowed
  ne-opaque-ok »∇ (defn α↦t)     = opaque-ok »∇ α↦t
  ne-opaque-ok »∇ (var ok _)     = ⊥-elim (Lift.lower ok)
  ne-opaque-ok »∇ (∘ₙ b)         = ne-opaque-ok »∇ b
  ne-opaque-ok »∇ (fstₙ b)       = ne-opaque-ok »∇ b
  ne-opaque-ok »∇ (sndₙ b)       = ne-opaque-ok »∇ b
  ne-opaque-ok »∇ (natrecₙ b)    = ne-opaque-ok »∇ b
  ne-opaque-ok »∇ (prodrecₙ b)   = ne-opaque-ok »∇ b
  ne-opaque-ok »∇ (emptyrecₙ b)  = ne-opaque-ok »∇ b
  ne-opaque-ok »∇ (unitrecₙ _ b) = ne-opaque-ok »∇ b
  ne-opaque-ok »∇ (Jₙ b)         = ne-opaque-ok »∇ b
  ne-opaque-ok »∇ (Kₙ b)         = ne-opaque-ok »∇ b
  ne-opaque-ok »∇ ([]-congₙ b)   = ne-opaque-ok »∇ b

------------------------------------------------------------------------
-- Lemmas about unfoldings

opaque

  ε-⊔ᵒᵗ : ε ⊔ᵒᵗ ε PE.≡ ε
  ε-⊔ᵒᵗ with unfolding-mode
  ...      | explicit   = PE.refl
  ...      | transitive = PE.refl

opaque

  assoc-⊔ᵒ : (φ φ′ φ″ : Unfolding n) → φ ⊔ᵒ (φ′ ⊔ᵒ φ″) PE.≡ (φ ⊔ᵒ φ′) ⊔ᵒ φ″
  assoc-⊔ᵒ ε ε ε = PE.refl
  assoc-⊔ᵒ (φ ⁰) (φ′ ⁰) (φ″ ⁰) = PE.cong _⁰ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ⁰) (φ′ ⁰) (φ″ ¹) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ⁰) (φ′ ¹) (φ″ ⁰) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ⁰) (φ′ ¹) (φ″ ¹) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ¹) (φ′ ⁰) (φ″ ⁰) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ¹) (φ′ ⁰) (φ″ ¹) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ¹) (φ′ ¹) (φ″ ⁰) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)
  assoc-⊔ᵒ (φ ¹) (φ′ ¹) (φ″ ¹) = PE.cong _¹ (assoc-⊔ᵒ φ φ′ φ″)

opaque

  comm-⊔ᵒ : (φ φ′ : Unfolding n) → φ ⊔ᵒ φ′ PE.≡ φ′ ⊔ᵒ φ
  comm-⊔ᵒ ε ε = PE.refl
  comm-⊔ᵒ (φ ⁰) (φ′ ⁰) = PE.cong _⁰ (comm-⊔ᵒ φ φ′)
  comm-⊔ᵒ (φ ⁰) (φ′ ¹) = PE.cong _¹ (comm-⊔ᵒ φ φ′)
  comm-⊔ᵒ (φ ¹) (φ′ ⁰) = PE.cong _¹ (comm-⊔ᵒ φ φ′)
  comm-⊔ᵒ (φ ¹) (φ′ ¹) = PE.cong _¹ (comm-⊔ᵒ φ φ′)

opaque

  assoc-⊔ᵒᵗ : (φ φ′ φ″ : Unfolding n) → φ ⊔ᵒᵗ (φ′ ⊔ᵒᵗ φ″) PE.≡ (φ ⊔ᵒᵗ φ′) ⊔ᵒᵗ φ″
  assoc-⊔ᵒᵗ φ φ′ φ″ with unfolding-mode
  ...          | explicit   = PE.refl
  ...          | transitive = assoc-⊔ᵒ φ φ′ φ″

opaque

  ones-⊔ᵒᵗ : (φ : Unfolding n) → ones n ⊔ᵒᵗ φ PE.≡ ones n
  ones-⊔ᵒᵗ with unfolding-mode
  ...         | explicit   = λ _ → PE.refl
  ...         | transitive = ones-⊔ᵒ

opaque

  ones-»↜ : (∇ : DCon (Term 0) n) → ones n » glassify ∇ ↜ ∇
  ones-»↜ ε                       = ε
  ones-»↜ (∇ ∙⟨ tra   ⟩[ t ∷ A ]) = ones-»↜ ∇ ¹ᵗ
  ones-»↜ (∇ ∙⟨ opa φ ⟩[ t ∷ A ]) =
    PE.subst (_» glassify ∇ ↜ ∇) (PE.sym (ones-⊔ᵒᵗ φ)) (ones-»↜ ∇) ¹ᵒ

opaque

  unique-»↜ : φ » ∇′ ↜ ∇ → φ » ∇″ ↜ ∇ → ∇′ PE.≡ ∇″
  unique-»↜ ε       ε        = PE.refl
  unique-»↜ (φ↜ ⁰)  (φ↜′ ⁰)  = PE.cong _ (unique-»↜ φ↜ φ↜′)
  unique-»↜ (φ↜ ¹ᵒ) (φ↜′ ¹ᵒ) = PE.cong _ (unique-»↜ φ↜ φ↜′)
  unique-»↜ (φ↜ ¹ᵗ) (φ↜′ ¹ᵗ) = PE.cong _ (unique-»↜ φ↜ φ↜′)

opaque

  total-»↜ : (φ : Unfolding n) (∇ : DCon (Term 0) n) → ∃ λ ∇′ → φ » ∇′ ↜ ∇
  total-»↜ ε ε = ε , ε
  total-»↜ (φ ⁰) (∇ ∙⟨ ω ⟩[ t ∷ A ]) =
    let ∇′ , φ↜ = total-»↜ φ ∇
    in  ∇′ ∙⟨ ω ⟩[ t ∷ A ] , φ↜ ⁰
  total-»↜ (φ ¹) (∇ ∙⟨ opa φ′ ⟩[ t ∷ A ]) =
    let ∇′ , φ↜ = total-»↜ (φ ⊔ᵒᵗ φ′) ∇
    in  ∇′ ∙⟨ tra ⟩[ t ∷ A ] , φ↜ ¹ᵒ
  total-»↜ (φ ¹) (∇ ∙⟨ tra ⟩[ t ∷ A ]) =
    let ∇′ , φ↜ = total-»↜ φ ∇
    in  ∇′ ∙⟨ tra ⟩[ t ∷ A ] , φ↜ ¹ᵗ

------------------------------------------------------------------------
-- Lemmas about glassified contexts

opaque

  glassify-factor : φ » ∇′ ↜ ∇ → glassify ∇′ PE.≡ glassify ∇
  glassify-factor ε      = PE.refl
  glassify-factor (u ⁰)  = PE.cong (_∙⟨ _ ⟩[ _ ∷ _ ]) (glassify-factor u)
  glassify-factor (u ¹ᵗ) = PE.cong (_∙⟨ _ ⟩[ _ ∷ _ ]) (glassify-factor u)
  glassify-factor (u ¹ᵒ) = PE.cong (_∙⟨ _ ⟩[ _ ∷ _ ]) (glassify-factor u)

opaque

  glassify-idem : (∇ : DCon (Term 0) n) → glassify (glassify ∇) PE.≡ glassify ∇
  glassify-idem = glassify-factor ∘→ ones-»↜

opaque

  glass-no-ne⁻ : ¬ Neutral⁻ (glassify ∇) t
  glass-no-ne⁻ (defn α↦⊘)     = glass-↦⊘∈ α↦⊘
  glass-no-ne⁻ (var ok x)     = Lift.lower ok
  glass-no-ne⁻ (∘ₙ b)         = glass-no-ne⁻ b
  glass-no-ne⁻ (fstₙ b)       = glass-no-ne⁻ b
  glass-no-ne⁻ (sndₙ b)       = glass-no-ne⁻ b
  glass-no-ne⁻ (natrecₙ b)    = glass-no-ne⁻ b
  glass-no-ne⁻ (prodrecₙ b)   = glass-no-ne⁻ b
  glass-no-ne⁻ (emptyrecₙ b)  = glass-no-ne⁻ b
  glass-no-ne⁻ (unitrecₙ _ b) = glass-no-ne⁻ b
  glass-no-ne⁻ (Jₙ b)         = glass-no-ne⁻ b
  glass-no-ne⁻ (Kₙ b)         = glass-no-ne⁻ b
  glass-no-ne⁻ ([]-congₙ b)   = glass-no-ne⁻ b

opaque

  glass-ne : Neutral V (glassify ∇) t → V
  glass-ne b = case dichotomy-ne b of λ where
    (inj₁ b⁻) → ⊥-elim (glass-no-ne⁻ b⁻)
    (inj₂ ok) → ok

opaque

  glass-closed-no-ne : {t : Term 0} → ¬ Neutral V (glassify ∇) t
  glass-closed-no-ne = glass-no-ne⁻ ∘→ closed-ne

------------------------------------------------------------------------
-- Glassification lemmas

opaque mutual

  glassify-» : » ∇ → » glassify ∇
  glassify-» ε = ε
  glassify-» ∙ᵒ⟨ ok , φ↜ ⟩[ ⊢t ∷ ⊢A ] =
    ∙ᵗ[ PE.subst (_» _ ⊢ _ ∷ _) (glassify-factor φ↜) (glassify-⊢∷ ⊢t) ]
  glassify-» ∙ᵗ[ ⊢t ] = ∙ᵗ[ glassify-⊢∷ ⊢t ]

  glassify-⊢′ : ∇ »⊢ Γ → glassify ∇ »⊢ Γ
  glassify-⊢′ (ε »∇) = ε (glassify-» »∇)
  glassify-⊢′ (∙ ⊢A) = ∙ glassify-⊢ ⊢A

  glassify-⊢ : ∇ » Γ ⊢ A → glassify ∇ » Γ ⊢ A
  glassify-⊢ (Uⱼ ⊢Γ) = Uⱼ (glassify-⊢′ ⊢Γ)
  glassify-⊢ (ℕⱼ ⊢Γ) = ℕⱼ (glassify-⊢′ ⊢Γ)
  glassify-⊢ (Emptyⱼ ⊢Γ) = Emptyⱼ (glassify-⊢′ ⊢Γ)
  glassify-⊢ (Unitⱼ ⊢Γ ok) = Unitⱼ (glassify-⊢′ ⊢Γ) ok
  glassify-⊢ (ΠΣⱼ ⊢A ok) = ΠΣⱼ (glassify-⊢ ⊢A) ok
  glassify-⊢ (Idⱼ ⊢A ⊢t ⊢u) =
    Idⱼ (glassify-⊢ ⊢A) (glassify-⊢∷ ⊢t) (glassify-⊢∷ ⊢u)
  glassify-⊢ (univ ⊢A) = univ (glassify-⊢∷ ⊢A)

  glassify-⊢∷ : ∇ » Γ ⊢ t ∷ A → glassify ∇ » Γ ⊢ t ∷ A
  glassify-⊢∷ (Uⱼ ⊢Γ) = Uⱼ (glassify-⊢′ ⊢Γ)
  glassify-⊢∷ (ΠΣⱼ ⊢t₁ ⊢t₂ ok) =
    ΠΣⱼ (glassify-⊢∷ ⊢t₁) (glassify-⊢∷ ⊢t₂) ok
  glassify-⊢∷ (ℕⱼ ⊢Γ) = ℕⱼ (glassify-⊢′ ⊢Γ)
  glassify-⊢∷ (Emptyⱼ ⊢Γ) = Emptyⱼ (glassify-⊢′ ⊢Γ)
  glassify-⊢∷ (Unitⱼ ⊢Γ ok) = Unitⱼ (glassify-⊢′ ⊢Γ) ok
  glassify-⊢∷ (conv ⊢t A≡A′) =
    conv (glassify-⊢∷ ⊢t) (glassify-⊢≡ A≡A′)
  glassify-⊢∷ (var ⊢Γ x∈) = var (glassify-⊢′ ⊢Γ) x∈
  glassify-⊢∷ (defn ⊢Γ α↦t A≡A′) =
    defn (glassify-⊢′ ⊢Γ) (glassify-↦∈ α↦t) A≡A′
  glassify-⊢∷ (lamⱼ ⊢A ⊢t ok) =
    lamⱼ (glassify-⊢ ⊢A) (glassify-⊢∷ ⊢t) ok
  glassify-⊢∷ (⊢t₁ ∘ⱼ ⊢t₂) =
    glassify-⊢∷ ⊢t₁ ∘ⱼ glassify-⊢∷ ⊢t₂
  glassify-⊢∷ (prodⱼ ⊢A ⊢t₁ ⊢t₂ ok) =
    prodⱼ (glassify-⊢ ⊢A)
          (glassify-⊢∷ ⊢t₁)
          (glassify-⊢∷ ⊢t₂)
          ok
  glassify-⊢∷ (fstⱼ ⊢A ⊢t) =
    fstⱼ (glassify-⊢ ⊢A) (glassify-⊢∷ ⊢t)
  glassify-⊢∷ (sndⱼ ⊢A ⊢t) =
    sndⱼ (glassify-⊢ ⊢A) (glassify-⊢∷ ⊢t)
  glassify-⊢∷ (prodrecⱼ ⊢A ⊢t ⊢t′ ok) =
    prodrecⱼ (glassify-⊢ ⊢A)
             (glassify-⊢∷ ⊢t)
             (glassify-⊢∷ ⊢t′)
             ok
  glassify-⊢∷ (zeroⱼ ⊢Γ) = zeroⱼ (glassify-⊢′ ⊢Γ)
  glassify-⊢∷ (sucⱼ ⊢t) = sucⱼ (glassify-⊢∷ ⊢t)
  glassify-⊢∷ (natrecⱼ ⊢t₀ ⊢tₛ ⊢t) =
    natrecⱼ (glassify-⊢∷ ⊢t₀)
            (glassify-⊢∷ ⊢tₛ)
            (glassify-⊢∷ ⊢t)
  glassify-⊢∷ (emptyrecⱼ ⊢A ⊢t) =
    emptyrecⱼ (glassify-⊢ ⊢A) (glassify-⊢∷ ⊢t)
  glassify-⊢∷ (starⱼ ⊢Γ ok) = starⱼ (glassify-⊢′ ⊢Γ) ok
  glassify-⊢∷ (unitrecⱼ ⊢A ⊢t ⊢t′ ok) =
    unitrecⱼ (glassify-⊢ ⊢A)
             (glassify-⊢∷ ⊢t)
             (glassify-⊢∷ ⊢t′)
             ok
  glassify-⊢∷ (Idⱼ ⊢A ⊢t₁ ⊢t₂) =
    Idⱼ (glassify-⊢∷ ⊢A)
        (glassify-⊢∷ ⊢t₁)
        (glassify-⊢∷ ⊢t₂)
  glassify-⊢∷ (rflⱼ ⊢t) = rflⱼ (glassify-⊢∷ ⊢t)
  glassify-⊢∷ (Jⱼ ⊢t ⊢A ⊢tᵣ ⊢t′ ⊢tₚ) =
    Jⱼ (glassify-⊢∷ ⊢t)
       (glassify-⊢ ⊢A)
       (glassify-⊢∷ ⊢tᵣ)
       (glassify-⊢∷ ⊢t′)
       (glassify-⊢∷ ⊢tₚ)
  glassify-⊢∷ (Kⱼ ⊢A ⊢tᵣ ⊢tₚ ok) =
    Kⱼ (glassify-⊢ ⊢A)
       (glassify-⊢∷ ⊢tᵣ)
       (glassify-⊢∷ ⊢tₚ)
       ok
  glassify-⊢∷ ([]-congⱼ ⊢A ⊢t₁ ⊢t₂ ⊢tₚ ok) =
    []-congⱼ (glassify-⊢ ⊢A)
             (glassify-⊢∷ ⊢t₁)
             (glassify-⊢∷ ⊢t₂)
             (glassify-⊢∷ ⊢tₚ) ok

  glassify-⊢≡ : ∇ » Γ ⊢ A ≡ B → glassify ∇ » Γ ⊢ A ≡ B
  glassify-⊢≡ (univ A≡A′) = univ (glassify-⊢≡∷ A≡A′)
  glassify-⊢≡ (refl ⊢A) = refl (glassify-⊢ ⊢A)
  glassify-⊢≡ (sym A≡A′) = sym (glassify-⊢≡ A≡A′)
  glassify-⊢≡ (trans A≡A′ A′≡A″) =
    trans (glassify-⊢≡ A≡A′) (glassify-⊢≡ A′≡A″)
  glassify-⊢≡ (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) =
    ΠΣ-cong (glassify-⊢≡ A₁≡A₂) (glassify-⊢≡ B₁≡B₂) ok
  glassify-⊢≡ (Id-cong A≡A′ t₁≡t₂ u₁≡u₂) =
    Id-cong (glassify-⊢≡ A≡A′)
            (glassify-⊢≡∷ t₁≡t₂)
            (glassify-⊢≡∷ u₁≡u₂)

  glassify-⊢≡∷ : ∇ » Γ ⊢ t ≡ u ∷ A → glassify ∇ » Γ ⊢ t ≡ u ∷ A
  glassify-⊢≡∷ (refl ⊢t) = refl (glassify-⊢∷ ⊢t)
  glassify-⊢≡∷ (sym ⊢A t≡t′) =
    sym (glassify-⊢ ⊢A) (glassify-⊢≡∷ t≡t′)
  glassify-⊢≡∷ (trans t≡t′ t′≡t″) =
    trans (glassify-⊢≡∷ t≡t′) (glassify-⊢≡∷ t′≡t″)
  glassify-⊢≡∷ (conv t≡t′ A≡A′) =
    conv (glassify-⊢≡∷ t≡t′) (glassify-⊢≡ A≡A′)
  glassify-⊢≡∷ (δ-red ⊢Γ α↦t A≡A′ t≡t′) =
    δ-red (glassify-⊢′ ⊢Γ) (glassify-↦∷∈ α↦t) A≡A′ t≡t′
  glassify-⊢≡∷ (ΠΣ-cong t₁≡t₂ u₁≡u₂ ok) =
    ΠΣ-cong (glassify-⊢≡∷ t₁≡t₂) (glassify-⊢≡∷ u₁≡u₂) ok
  glassify-⊢≡∷ (app-cong t₁≡t₂ u₁≡u₂) =
    app-cong (glassify-⊢≡∷ t₁≡t₂) (glassify-⊢≡∷ u₁≡u₂)
  glassify-⊢≡∷ (β-red ⊢A ⊢t ⊢x eq ok) =
    β-red (glassify-⊢ ⊢A)
          (glassify-⊢∷ ⊢t)
          (glassify-⊢∷ ⊢x)
          eq ok
  glassify-⊢≡∷ (η-eq ⊢A ⊢t ⊢t′ t≡t′ ok) =
    η-eq (glassify-⊢ ⊢A)
         (glassify-⊢∷ ⊢t)
         (glassify-⊢∷ ⊢t′)
         (glassify-⊢≡∷ t≡t′)
         ok
  glassify-⊢≡∷ (fst-cong ⊢A t≡t′) =
    fst-cong (glassify-⊢ ⊢A) (glassify-⊢≡∷ t≡t′)
  glassify-⊢≡∷ (snd-cong ⊢A t≡t′) =
    snd-cong (glassify-⊢ ⊢A) (glassify-⊢≡∷ t≡t′)
  glassify-⊢≡∷ (Σ-β₁ ⊢A ⊢t ⊢t′ eq ok) =
    Σ-β₁ (glassify-⊢ ⊢A)
         (glassify-⊢∷ ⊢t)
         (glassify-⊢∷ ⊢t′)
         eq ok
  glassify-⊢≡∷ (Σ-β₂ ⊢A ⊢t ⊢t′ eq ok) =
    Σ-β₂ (glassify-⊢ ⊢A)
         (glassify-⊢∷ ⊢t)
         (glassify-⊢∷ ⊢t′)
         eq ok
  glassify-⊢≡∷ (Σ-η ⊢A ⊢t ⊢t′ fst≡ snd≡ ok) =
    Σ-η (glassify-⊢ ⊢A)
        (glassify-⊢∷ ⊢t)
        (glassify-⊢∷ ⊢t′)
        (glassify-⊢≡∷ fst≡)
        (glassify-⊢≡∷ snd≡)
        ok
  glassify-⊢≡∷ (prod-cong ⊢A t₁≡t₂ u₁≡u₂ ok) =
    prod-cong (glassify-⊢ ⊢A)
              (glassify-⊢≡∷ t₁≡t₂)
              (glassify-⊢≡∷ u₁≡u₂)
              ok
  glassify-⊢≡∷ (prodrec-cong A≡A′ t₁≡t₂ u₁≡u₂ ok) =
    prodrec-cong (glassify-⊢≡ A≡A′)
                 (glassify-⊢≡∷ t₁≡t₂)
                 (glassify-⊢≡∷ u₁≡u₂)
                 ok
  glassify-⊢≡∷ (prodrec-β ⊢A ⊢t₁ ⊢t₂ ⊢tᵣ eq ok) =
    prodrec-β (glassify-⊢ ⊢A)
              (glassify-⊢∷ ⊢t₁)
              (glassify-⊢∷ ⊢t₂)
              (glassify-⊢∷ ⊢tᵣ)
              eq ok
  glassify-⊢≡∷ (suc-cong t≡t′) =
    suc-cong (glassify-⊢≡∷ t≡t′)
  glassify-⊢≡∷ (natrec-cong A≡A′ 0≡ s≡ t≡t′) =
    natrec-cong (glassify-⊢≡ A≡A′)
                (glassify-⊢≡∷ 0≡)
                (glassify-⊢≡∷ s≡)
                (glassify-⊢≡∷ t≡t′)
  glassify-⊢≡∷ (natrec-zero ⊢t₀ ⊢tₛ) =
    natrec-zero (glassify-⊢∷ ⊢t₀) (glassify-⊢∷ ⊢tₛ)
  glassify-⊢≡∷ (natrec-suc ⊢t₀ ⊢tₛ ⊢t) =
    natrec-suc (glassify-⊢∷ ⊢t₀)
               (glassify-⊢∷ ⊢tₛ)
               (glassify-⊢∷ ⊢t)
  glassify-⊢≡∷ (emptyrec-cong A≡A′ t≡t′) =
    emptyrec-cong (glassify-⊢≡ A≡A′) (glassify-⊢≡∷ t≡t′)
  glassify-⊢≡∷ (unitrec-cong A≡A′ t≡t′ r≡ ok no-η) =
    unitrec-cong (glassify-⊢≡ A≡A′)
                 (glassify-⊢≡∷ t≡t′)
                 (glassify-⊢≡∷ r≡)
                 ok no-η
  glassify-⊢≡∷ (unitrec-β ⊢A ⊢t ok no-η) =
    unitrec-β (glassify-⊢ ⊢A) (glassify-⊢∷ ⊢t) ok no-η
  glassify-⊢≡∷ (unitrec-β-η ⊢A ⊢t ⊢tᵣ ok η) =
    unitrec-β-η (glassify-⊢ ⊢A)
                (glassify-⊢∷ ⊢t)
                (glassify-⊢∷ ⊢tᵣ)
                ok η
  glassify-⊢≡∷ (η-unit ⊢t ⊢t′ η) =
    η-unit (glassify-⊢∷ ⊢t) (glassify-⊢∷ ⊢t′) η
  glassify-⊢≡∷ (Id-cong A≡A′ t₁≡t₂ u₁≡u₂) =
    Id-cong (glassify-⊢≡∷ A≡A′)
            (glassify-⊢≡∷ t₁≡t₂)
            (glassify-⊢≡∷ u₁≡u₂)
  glassify-⊢≡∷ (J-cong A≡A′ ⊢t t≡t′ B₁≡B₂ r≡ x≡ p≡) =
    J-cong (glassify-⊢≡ A≡A′)
           (glassify-⊢∷ ⊢t)
           (glassify-⊢≡∷ t≡t′)
           (glassify-⊢≡ B₁≡B₂)
           (glassify-⊢≡∷ r≡)
           (glassify-⊢≡∷ x≡)
           (glassify-⊢≡∷ p≡)
  glassify-⊢≡∷ (K-cong A≡A′ t≡t′ B₁≡B₂ r≡ p≡ ok) =
    K-cong (glassify-⊢≡ A≡A′)
           (glassify-⊢≡∷ t≡t′)
           (glassify-⊢≡ B₁≡B₂)
           (glassify-⊢≡∷ r≡)
           (glassify-⊢≡∷ p≡)
           ok
  glassify-⊢≡∷ ([]-cong-cong A≡A′ t₁≡t₂ u₁≡u₂ p≡p′ ok) =
    []-cong-cong (glassify-⊢≡ A≡A′)
                 (glassify-⊢≡∷ t₁≡t₂)
                 (glassify-⊢≡∷ u₁≡u₂)
                 (glassify-⊢≡∷ p≡p′) ok
  glassify-⊢≡∷ (J-β ⊢t ⊢A ⊢tᵣ eq) =
    J-β (glassify-⊢∷ ⊢t)
        (glassify-⊢ ⊢A)
        (glassify-⊢∷ ⊢tᵣ)
        eq
  glassify-⊢≡∷ (K-β ⊢A ⊢t ok) =
    K-β (glassify-⊢ ⊢A) (glassify-⊢∷ ⊢t) ok
  glassify-⊢≡∷ ([]-cong-β ⊢t eq ok) =
    []-cong-β (glassify-⊢∷ ⊢t) eq ok
  glassify-⊢≡∷ (equality-reflection ok ⊢Id ⊢t) =
    equality-reflection ok (glassify-⊢ ⊢Id) (glassify-⊢∷ ⊢t)

opaque

  glassify-⇒∷ : ∇ » Γ ⊢ t ⇒ u ∷ A → glassify ∇ » Γ ⊢ t ⇒ u ∷ A
  glassify-⇒∷ (conv t⇒t′ A≡A′) =
    conv (glassify-⇒∷ t⇒t′) (glassify-⊢≡ A≡A′)
  glassify-⇒∷ (δ-red ⊢Γ α↦t A≡A′ T≡T′) =
    δ-red (glassify-⊢′ ⊢Γ) (glassify-↦∷∈ α↦t) A≡A′ T≡T′
  glassify-⇒∷ (app-subst t⇒t′ ⊢a) =
    app-subst (glassify-⇒∷ t⇒t′) (glassify-⊢∷ ⊢a)
  glassify-⇒∷ (β-red ⊢A ⊢t ⊢x eq ok) =
    β-red (glassify-⊢ ⊢A)
          (glassify-⊢∷ ⊢t)
          (glassify-⊢∷ ⊢x)
          eq ok
  glassify-⇒∷ (fst-subst ⊢A t⇒t′) =
    fst-subst (glassify-⊢ ⊢A) (glassify-⇒∷ t⇒t′)
  glassify-⇒∷ (snd-subst ⊢A t⇒t′) =
    snd-subst (glassify-⊢ ⊢A) (glassify-⇒∷ t⇒t′)
  glassify-⇒∷ (Σ-β₁ ⊢A ⊢t ⊢t′ eq ok) =
    Σ-β₁ (glassify-⊢ ⊢A)
         (glassify-⊢∷ ⊢t)
         (glassify-⊢∷ ⊢t′)
         eq ok
  glassify-⇒∷ (Σ-β₂ ⊢A ⊢t ⊢t′ eq ok) =
    Σ-β₂ (glassify-⊢ ⊢A)
         (glassify-⊢∷ ⊢t)
         (glassify-⊢∷ ⊢t′)
         eq ok
  glassify-⇒∷ (prodrec-subst ⊢A ⊢a t⇒t′ ok) =
    prodrec-subst (glassify-⊢ ⊢A)
                  (glassify-⊢∷ ⊢a)
                  (glassify-⇒∷ t⇒t′)
                  ok
  glassify-⇒∷ (prodrec-β ⊢A ⊢t ⊢t₂ ⊢tᵣ eq ok) =
    prodrec-β (glassify-⊢ ⊢A)
              (glassify-⊢∷ ⊢t)
              (glassify-⊢∷ ⊢t₂)
              (glassify-⊢∷ ⊢tᵣ)
              eq ok
  glassify-⇒∷ (natrec-subst ⊢t₀ ⊢tₛ t⇒t′) =
    natrec-subst (glassify-⊢∷ ⊢t₀)
                 (glassify-⊢∷ ⊢tₛ)
                 (glassify-⇒∷ t⇒t′)
  glassify-⇒∷ (natrec-zero ⊢t₀ ⊢tₛ) =
    natrec-zero (glassify-⊢∷ ⊢t₀) (glassify-⊢∷ ⊢tₛ)
  glassify-⇒∷ (natrec-suc ⊢t₀ ⊢tₛ ⊢t) =
    natrec-suc (glassify-⊢∷ ⊢t₀)
               (glassify-⊢∷ ⊢tₛ)
               (glassify-⊢∷ ⊢t)
  glassify-⇒∷ (emptyrec-subst ⊢A t⇒t′) =
    emptyrec-subst (glassify-⊢ ⊢A) (glassify-⇒∷ t⇒t′)
  glassify-⇒∷ (unitrec-subst ⊢A ⊢a t⇒t′ ok no-η) =
    unitrec-subst (glassify-⊢ ⊢A)
                  (glassify-⊢∷ ⊢a)
                  (glassify-⇒∷ t⇒t′)
                  ok no-η
  glassify-⇒∷ (unitrec-β ⊢A ⊢t ok no-η) =
    unitrec-β (glassify-⊢ ⊢A) (glassify-⊢∷ ⊢t) ok no-η
  glassify-⇒∷ (unitrec-β-η ⊢A ⊢t ⊢tᵣ ok η) =
    unitrec-β-η (glassify-⊢ ⊢A)
                (glassify-⊢∷ ⊢t)
                (glassify-⊢∷ ⊢tᵣ)
                ok η
  glassify-⇒∷ (J-subst ⊢t ⊢A ⊢r ⊢p w⇒w′) =
    J-subst (glassify-⊢∷ ⊢t)
            (glassify-⊢ ⊢A)
            (glassify-⊢∷ ⊢r)
            (glassify-⊢∷ ⊢p)
            (glassify-⇒∷ w⇒w′)
  glassify-⇒∷ (K-subst ⊢A ⊢r t⇒t′ ok) =
    K-subst (glassify-⊢ ⊢A)
            (glassify-⊢∷ ⊢r)
            (glassify-⇒∷ t⇒t′)
            ok
  glassify-⇒∷ ([]-cong-subst ⊢A ⊢a ⊢a′ t⇒t′ ok) =
    []-cong-subst (glassify-⊢ ⊢A)
                  (glassify-⊢∷ ⊢a)
                  (glassify-⊢∷ ⊢a′)
                  (glassify-⇒∷ t⇒t′)
                  ok
  glassify-⇒∷ (J-β ⊢t ⊢t′ t≡t′ ⊢A A≡ ⊢tᵣ) =
    J-β (glassify-⊢∷ ⊢t)
        (glassify-⊢∷ ⊢t′)
        (glassify-⊢≡∷ t≡t′)
        (glassify-⊢ ⊢A)
        (glassify-⊢≡ A≡)
        (glassify-⊢∷ ⊢tᵣ)
  glassify-⇒∷ (K-β ⊢A ⊢t ok) =
    K-β (glassify-⊢ ⊢A) (glassify-⊢∷ ⊢t) ok
  glassify-⇒∷ ([]-cong-β ⊢A ⊢t ⊢t′ t≡t′ ok) =
    []-cong-β (glassify-⊢ ⊢A)
              (glassify-⊢∷ ⊢t)
              (glassify-⊢∷ ⊢t′)
              (glassify-⊢≡∷ t≡t′)
              ok

opaque

  glassify-⇒ : ∇ » Γ ⊢ A ⇒ B → glassify ∇ » Γ ⊢ A ⇒ B
  glassify-⇒ (univ A⇒B) = univ (glassify-⇒∷ A⇒B)

opaque

  glassify-⇒* : ∇ » Γ ⊢ A ⇒* B → glassify ∇ » Γ ⊢ A ⇒* B
  glassify-⇒* (id ⊢A)      = id (glassify-⊢ ⊢A)
  glassify-⇒* (A⇒X ⇨ X⇒*B) = glassify-⇒ A⇒X ⇨ glassify-⇒* X⇒*B

opaque

  glassify-⇒*∷ : ∇ » Γ ⊢ t ⇒* u ∷ A → glassify ∇ » Γ ⊢ t ⇒* u ∷ A
  glassify-⇒*∷ (id ⊢t)      = id (glassify-⊢∷ ⊢t)
  glassify-⇒*∷ (t⇒x ⇨ x⇒*u) = glassify-⇒∷ t⇒x ⇨ glassify-⇒*∷ x⇒*u

------------------------------------------------------------------------
-- Opaque[_∷_]

-- A definition context with a single opaque definition of the given
-- type (the second argument) that is equal to the given term (the
-- first argument).

Opaque[_∷_] : Term 0 → Term 0 → DCon (Term 0) 1
Opaque[ t ∷ A ] = ε ∙⟨ opa ε ⟩[ t ∷ A ]

opaque

  -- There are no transparent definitions in Opaque[ u ∷ B ].

  ¬↦∷∈Opaque : ¬ α ↦ t ∷ A ∈ Opaque[ u ∷ B ]
  ¬↦∷∈Opaque (there ())

opaque

  -- If t has type A and opaque definitions are allowed, then
  -- Opaque[ t ∷ A ] is well-formed.

  »Opaque : Opacity-allowed → ε » ε ⊢ t ∷ A → » Opaque[ t ∷ A ]
  »Opaque ok ⊢t = ∙ᵒ⟨ ok , ε ⟩[ ⊢t ∷ wf-⊢∷ ⊢t ]

-- Below it is assumed that opaque definitions are allowed, and that
-- there are three closed terms A, t and u that satisfy ε » ε ⊢ u ∷ A
-- (there are no requirements on t).

module _
  (ok : Opacity-allowed)
  {A t u : Term 0}
  (⊢t : ε » ε ⊢ u ∷ A)
  where

  opaque mutual

    -- If Γ is well-formed under Opaque[ t ∷ A ] and α points to B in
    -- Opaque[ t ∷ A ], then defn α has type wk wk₀ B under
    -- Opaque[ u ∷ A ] and Γ.

    definition-irrelevant-defn :
      Opaque[ t ∷ A ] »⊢ Γ → α ↦∷ B ∈ Opaque[ t ∷ A ] →
      Opaque[ u ∷ A ] » Γ ⊢ defn α ∷ wk wk₀ B
    definition-irrelevant-defn ⊢Γ here =
      defn (definition-irrelevant-»⊢ ⊢Γ) here PE.refl
    definition-irrelevant-defn ⊢Γ (there ())

    -- Any context that is well-formed under Opaque[ t ∷ A ] is also
    -- well-formed under Opaque[ u ∷ A ].

    definition-irrelevant-»⊢ : Opaque[ t ∷ A ] »⊢ Γ → Opaque[ u ∷ A ] »⊢ Γ
    definition-irrelevant-»⊢ (ε _)  = ε (»Opaque ok ⊢t)
    definition-irrelevant-»⊢ (∙ ⊢A) = ∙ definition-irrelevant-⊢ ⊢A

    -- Any type that is well-formed under Opaque[ t ∷ A ] is also
    -- well-formed under Opaque[ u ∷ A ].

    definition-irrelevant-⊢ :
      Opaque[ t ∷ A ] » Γ ⊢ B → Opaque[ u ∷ A ] » Γ ⊢ B
    definition-irrelevant-⊢ (Uⱼ ⊢Γ) =
      Uⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢ (univ ⊢A) =
      univ (definition-irrelevant-⊢∷ ⊢A)
    definition-irrelevant-⊢ (Emptyⱼ ⊢Γ) =
      Emptyⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢ (Unitⱼ ⊢Γ ok) =
      Unitⱼ (definition-irrelevant-»⊢ ⊢Γ) ok
    definition-irrelevant-⊢ (ΠΣⱼ ⊢A ok) =
      ΠΣⱼ (definition-irrelevant-⊢ ⊢A) ok
    definition-irrelevant-⊢ (ℕⱼ ⊢Γ) =
      ℕⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢ (Idⱼ ⊢A ⊢t ⊢u) =
      Idⱼ (definition-irrelevant-⊢ ⊢A) (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u)

    -- Any term that is well-typed under Opaque[ t ∷ A ] is also
    -- well-typed under Opaque[ u ∷ A ].

    definition-irrelevant-⊢∷ :
      Opaque[ t ∷ A ] » Γ ⊢ v ∷ B →
      Opaque[ u ∷ A ] » Γ ⊢ v ∷ B
    definition-irrelevant-⊢∷ (conv ⊢t B≡A) =
      conv (definition-irrelevant-⊢∷ ⊢t) (definition-irrelevant-⊢≡ B≡A)
    definition-irrelevant-⊢∷ (var ⊢Γ x∈) =
      var (definition-irrelevant-»⊢ ⊢Γ) x∈
    definition-irrelevant-⊢∷ (defn ⊢Γ α↦ PE.refl) =
      definition-irrelevant-defn ⊢Γ α↦
    definition-irrelevant-⊢∷ (Uⱼ ⊢Γ) =
      Uⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢∷ (Emptyⱼ ⊢Γ) =
      Emptyⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢∷ (emptyrecⱼ ⊢A ⊢t) =
      emptyrecⱼ (definition-irrelevant-⊢ ⊢A)
        (definition-irrelevant-⊢∷ ⊢t)
    definition-irrelevant-⊢∷ (Unitⱼ ⊢Γ ok) =
      Unitⱼ (definition-irrelevant-»⊢ ⊢Γ) ok
    definition-irrelevant-⊢∷ (starⱼ ⊢Γ ok) =
      starⱼ (definition-irrelevant-»⊢ ⊢Γ) ok
    definition-irrelevant-⊢∷ (unitrecⱼ ⊢A ⊢t ⊢u ok) =
      unitrecⱼ (definition-irrelevant-⊢ ⊢A) (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u) ok
    definition-irrelevant-⊢∷ (ΠΣⱼ ⊢A ⊢B ok) =
      ΠΣⱼ (definition-irrelevant-⊢∷ ⊢A) (definition-irrelevant-⊢∷ ⊢B) ok
    definition-irrelevant-⊢∷ (lamⱼ ⊢B ⊢t ok) =
      lamⱼ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢t) ok
    definition-irrelevant-⊢∷ (⊢t ∘ⱼ ⊢u) =
      definition-irrelevant-⊢∷ ⊢t ∘ⱼ definition-irrelevant-⊢∷ ⊢u
    definition-irrelevant-⊢∷ (prodⱼ ⊢B ⊢t ⊢u ok) =
      prodⱼ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u) ok
    definition-irrelevant-⊢∷ (fstⱼ ⊢B ⊢t) =
      fstⱼ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢t)
    definition-irrelevant-⊢∷ (sndⱼ ⊢B ⊢t) =
      sndⱼ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢t)
    definition-irrelevant-⊢∷ (prodrecⱼ ⊢A ⊢t ⊢u ok) =
      prodrecⱼ (definition-irrelevant-⊢ ⊢A) (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u) ok
    definition-irrelevant-⊢∷ (ℕⱼ ⊢Γ) =
      ℕⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢∷ (zeroⱼ ⊢Γ) =
      zeroⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢∷ (sucⱼ ⊢t) =
      sucⱼ (definition-irrelevant-⊢∷ ⊢t)
    definition-irrelevant-⊢∷ (natrecⱼ ⊢t ⊢u ⊢v) =
      natrecⱼ (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u) (definition-irrelevant-⊢∷ ⊢v)
    definition-irrelevant-⊢∷ (Idⱼ ⊢A ⊢t ⊢u) =
      Idⱼ (definition-irrelevant-⊢∷ ⊢A) (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u)
    definition-irrelevant-⊢∷ (rflⱼ ⊢t) =
      rflⱼ (definition-irrelevant-⊢∷ ⊢t)
    definition-irrelevant-⊢∷ (Jⱼ _ ⊢B ⊢u _ ⊢w) =
      Jⱼ′ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢u)
        (definition-irrelevant-⊢∷ ⊢w)
    definition-irrelevant-⊢∷ (Kⱼ ⊢B ⊢u ⊢v ok) =
      Kⱼ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢u)
        (definition-irrelevant-⊢∷ ⊢v) ok
    definition-irrelevant-⊢∷ ([]-congⱼ _ _ _ ⊢v ok) =
      []-congⱼ′ ok (definition-irrelevant-⊢∷ ⊢v)

    -- Definitional equalities that hold under Opaque[ t ∷ A ] also
    -- hold under Opaque[ u ∷ A ].

    definition-irrelevant-⊢≡ :
      Opaque[ t ∷ A ] » Γ ⊢ B ≡ C →
      Opaque[ u ∷ A ] » Γ ⊢ B ≡ C
    definition-irrelevant-⊢≡ = λ where
      (refl ⊢A) →
        refl (definition-irrelevant-⊢ ⊢A)
      (sym B≡A) →
        sym (definition-irrelevant-⊢≡ B≡A)
      (trans A≡B B≡C) →
        trans (definition-irrelevant-⊢≡ A≡B)
          (definition-irrelevant-⊢≡ B≡C)
      (univ A≡B) →
        univ (definition-irrelevant-⊢≡∷ A≡B)
      (ΠΣ-cong A₁≡B₁ A₂≡B₂ ok) →
        ΠΣ-cong (definition-irrelevant-⊢≡ A₁≡B₁)
          (definition-irrelevant-⊢≡ A₂≡B₂) ok
      (Id-cong A≡B t₁≡u₁ t₂≡u₂) →
        Id-cong (definition-irrelevant-⊢≡ A≡B)
          (definition-irrelevant-⊢≡∷ t₁≡u₁)
          (definition-irrelevant-⊢≡∷ t₂≡u₂)

    -- Definitional equalities that hold under Opaque[ t ∷ A ] also
    -- hold under Opaque[ u ∷ A ].

    definition-irrelevant-⊢≡∷ :
      Opaque[ t ∷ A ] » Γ ⊢ v ≡ w ∷ B →
      Opaque[ u ∷ A ] » Γ ⊢ v ≡ w ∷ B
    definition-irrelevant-⊢≡∷ = λ where
      (refl ⊢t) →
        refl (definition-irrelevant-⊢∷ ⊢t)
      (sym _ t₂≡t₁) →
        sym′ (definition-irrelevant-⊢≡∷ t₂≡t₁)
      (trans t₁≡t₂ t₂≡t₃) →
        trans (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ t₂≡t₃)
      (conv t₁≡t₂ B≡A) →
        conv (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡ B≡A)
      (δ-red _ α↦t _ _) →
        ⊥-elim (¬↦∷∈Opaque α↦t)
      (emptyrec-cong A₁≡A₂ t₁≡t₂) →
        emptyrec-cong (definition-irrelevant-⊢≡ A₁≡A₂)
         (definition-irrelevant-⊢≡∷ t₁≡t₂)
      (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ _ _) →
        unitrec-cong′ (definition-irrelevant-⊢≡ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
      (unitrec-β ⊢A ⊢t _ _) →
        unitrec-β-≡ (definition-irrelevant-⊢ ⊢A)
          (definition-irrelevant-⊢∷ ⊢t)
      (unitrec-β-η ⊢A ⊢t ⊢u _ η) →
        unitrec-β-η-≡ (definition-irrelevant-⊢ ⊢A)
          (definition-irrelevant-⊢∷ ⊢t) (definition-irrelevant-⊢∷ ⊢u) η
      (η-unit ⊢t₁ ⊢t₂ ok) →
        η-unit (definition-irrelevant-⊢∷ ⊢t₁)
          (definition-irrelevant-⊢∷ ⊢t₂) ok
      (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) →
        ΠΣ-cong (definition-irrelevant-⊢≡∷ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ B₁≡B₂) ok
      (app-cong t₁≡t₂ u₁≡u₂) →
        app-cong (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
      (β-red _ ⊢t ⊢u PE.refl ok) →
        β-red-≡ (definition-irrelevant-⊢∷ ⊢t)
          (definition-irrelevant-⊢∷ ⊢u) ok
      (η-eq ⊢B ⊢t₁ ⊢t₂ t₁0≡t₂0 ok) →
        η-eq′ (definition-irrelevant-⊢∷ ⊢t₁)
          (definition-irrelevant-⊢∷ ⊢t₂)
          (definition-irrelevant-⊢≡∷ t₁0≡t₂0)
      (fst-cong _ t₁≡t₂) →
        fst-cong′ (definition-irrelevant-⊢≡∷ t₁≡t₂)
      (Σ-β₁ ⊢B ⊢t₁ ⊢t₂ PE.refl ok) →
        Σ-β₁-≡ (definition-irrelevant-⊢ ⊢B)
          (definition-irrelevant-⊢∷ ⊢t₁) (definition-irrelevant-⊢∷ ⊢t₂)
           ok
      (snd-cong _ t₁≡t₂) →
        snd-cong′ (definition-irrelevant-⊢≡∷ t₁≡t₂)
      (Σ-β₂ ⊢B ⊢t₁ ⊢t₂ PE.refl ok) →
        Σ-β₂-≡ (definition-irrelevant-⊢ ⊢B)
          (definition-irrelevant-⊢∷ ⊢t₁) (definition-irrelevant-⊢∷ ⊢t₂)
          ok
      (Σ-η _ ⊢t₁ ⊢t₂ fst≡fst snd≡snd _) →
        Σ-η′ (definition-irrelevant-⊢∷ ⊢t₁)
          (definition-irrelevant-⊢∷ ⊢t₂)
          (definition-irrelevant-⊢≡∷ fst≡fst)
          (definition-irrelevant-⊢≡∷ snd≡snd)
      (prod-cong ⊢B t₁≡t₂ u₁≡u₂ ok) →
        prod-cong (definition-irrelevant-⊢ ⊢B)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂) ok
      (prodrec-cong C₁≡C₂ t₁≡t₂ u₁≡u₂ ok) →
        prodrec-cong′ (definition-irrelevant-⊢≡ C₁≡C₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
      (prodrec-β ⊢C ⊢t ⊢u ⊢v PE.refl ok) →
        prodrec-β-≡ (definition-irrelevant-⊢ ⊢C)
          (definition-irrelevant-⊢∷ ⊢t) (definition-irrelevant-⊢∷ ⊢u)
          (definition-irrelevant-⊢∷ ⊢v)
      (suc-cong t₁≡t₂) →
        suc-cong (definition-irrelevant-⊢≡∷ t₁≡t₂)
      (natrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) →
        natrec-cong (definition-irrelevant-⊢≡ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
          (definition-irrelevant-⊢≡∷ v₁≡v₂)
      (natrec-zero ⊢t ⊢u) →
        natrec-zero (definition-irrelevant-⊢∷ ⊢t)
          (definition-irrelevant-⊢∷ ⊢u)
      (natrec-suc ⊢t ⊢u ⊢v) →
        natrec-suc (definition-irrelevant-⊢∷ ⊢t)
          (definition-irrelevant-⊢∷ ⊢u) (definition-irrelevant-⊢∷ ⊢v)
      (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) →
        Id-cong (definition-irrelevant-⊢≡∷ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
      (J-cong A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) →
        J-cong′ (definition-irrelevant-⊢≡ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡ B₁≡B₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
          (definition-irrelevant-⊢≡∷ v₁≡v₂)
          (definition-irrelevant-⊢≡∷ w₁≡w₂)
      (J-β ⊢t ⊢B ⊢u PE.refl) →
        J-β-≡ (definition-irrelevant-⊢∷ ⊢t) (definition-irrelevant-⊢ ⊢B)
          (definition-irrelevant-⊢∷ ⊢u)
      (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) →
        K-cong (definition-irrelevant-⊢≡ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡ B₁≡B₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
          (definition-irrelevant-⊢≡∷ v₁≡v₂) ok
      (K-β ⊢B ⊢u ok) →
        K-β (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢u)
          ok
      ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) →
        []-cong-cong (definition-irrelevant-⊢≡ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
          (definition-irrelevant-⊢≡∷ v₁≡v₂) ok
      ([]-cong-β ⊢t PE.refl ok) →
        []-cong-β (definition-irrelevant-⊢∷ ⊢t) PE.refl ok
      (equality-reflection ok ⊢Id ⊢v) →
        equality-reflection ok (definition-irrelevant-⊢ ⊢Id)
          (definition-irrelevant-⊢∷ ⊢v)
