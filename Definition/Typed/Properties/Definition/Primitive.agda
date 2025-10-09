------------------------------------------------------------------------
-- Some lemmas related to definitions
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Definition.Primitive
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Variant

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

private variable
  α n     : Nat
  ∇ ∇′ ∇″ : DCon _ _
  Γ       : Con _ _
  A B t u : Term _
  V       : Set a
  φ φ₁ φ₂ : Unfolding _

------------------------------------------------------------------------
-- Lemmas about opacity

opaque

  opaque-ok : » ∇ → α ↦⊘∷ A ∈ ∇ → Opacity-allowed
  opaque-ok ε                       ()
  opaque-ok ∙ᵒ⟨ ok , _ ⟩[ _  ∷ ⊢A ] here =
    ok
  opaque-ok ∙ᵗ[ ⊢t ] (there α↦⊘) =
    opaque-ok (defn-wf (wfTerm ⊢t)) α↦⊘
  opaque-ok ∙ᵒ⟨ ok , _ ⟩[ _  ∷ ⊢A ] (there α↦⊘) =
    opaque-ok (defn-wf (wf ⊢A)) α↦⊘

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

opaque

  -- If opacity is not allowed, then well-formed definition contexts
  -- are transparent.

  »→Transparent : ¬ Opacity-allowed → » ∇ → Transparent ∇
  »→Transparent _ ε =
    PE.refl
  »→Transparent no-opacity ∙ᵒ⟨ allowed , _ ⟩[ _ ∷ _ ] =
    ⊥-elim $ no-opacity allowed
  »→Transparent no-opacity ∙ᵗ[ ⊢t ] =
    PE.cong _∙! $
    »→Transparent no-opacity (defn-wf (wfTerm ⊢t))

------------------------------------------------------------------------
-- Lemmas about unfoldings

opaque

  -- If the transitive unfolding mode is used, then _⊔ᵒᵗ_ is pointwise
  -- equal to _⊔ᵒ_.

  ⊔ᵒᵗ≡⊔ᵒ :
    unfolding-mode PE.≡ transitive →
    φ₁ ⊔ᵒᵗ φ₂ PE.≡ φ₁ ⊔ᵒ φ₂
  ⊔ᵒᵗ≡⊔ᵒ eq with unfolding-mode
  ⊔ᵒᵗ≡⊔ᵒ _  | transitive = PE.refl
  ⊔ᵒᵗ≡⊔ᵒ () | explicit

opaque

  -- If the explicit unfolding mode is used, then φ₁ ⊔ᵒᵗ φ₂ is equal
  -- to φ₁.

  ⊔ᵒᵗ≡const :
    unfolding-mode PE.≡ explicit →
    φ₁ ⊔ᵒᵗ φ₂ PE.≡ φ₁
  ⊔ᵒᵗ≡const eq with unfolding-mode
  ⊔ᵒᵗ≡const _  | explicit   = PE.refl
  ⊔ᵒᵗ≡const () | transitive

opaque

  ε-⊔ᵒᵗ : ε ⊔ᵒᵗ ε PE.≡ ε
  ε-⊔ᵒᵗ with unfolding-mode
  ...      | explicit   = PE.refl
  ...      | transitive = PE.refl

opaque

  assoc-⊔ᵒ :
    (φ φ′ φ″ : Unfolding n) → φ ⊔ᵒ (φ′ ⊔ᵒ φ″) PE.≡ (φ ⊔ᵒ φ′) ⊔ᵒ φ″
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

  assoc-⊔ᵒᵗ :
    (φ φ′ φ″ : Unfolding n) → φ ⊔ᵒᵗ (φ′ ⊔ᵒᵗ φ″) PE.≡ (φ ⊔ᵒᵗ φ′) ⊔ᵒᵗ φ″
  assoc-⊔ᵒᵗ φ φ′ φ″ with unfolding-mode
  ...          | explicit   = PE.refl
  ...          | transitive = assoc-⊔ᵒ φ φ′ φ″

opaque

  ones-⊔ᵒᵗ : (φ : Unfolding n) → ones n ⊔ᵒᵗ φ PE.≡ ones n
  ones-⊔ᵒᵗ with unfolding-mode
  ...         | explicit   = λ _ → PE.refl
  ...         | transitive = ones-⊔ᵒ

------------------------------------------------------------------------
-- Lemmas about transparentisation

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

  total-»↜ :
    (φ : Unfolding n) (∇ : DCon (Term 0) n) → ∃ λ ∇′ → φ » ∇′ ↜ ∇
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
  glassify-factor ε =
    PE.refl
  glassify-factor (u ⁰) =
    PE.cong (_∙⟨ _ ⟩[ _ ∷ _ ]) (glassify-factor u)
  glassify-factor (u ¹ᵗ) =
    PE.cong (_∙⟨ _ ⟩[ _ ∷ _ ]) (glassify-factor u)
  glassify-factor (u ¹ᵒ) =
    PE.cong (_∙⟨ _ ⟩[ _ ∷ _ ]) (glassify-factor u)

opaque

  glassify-idem :
    (∇ : DCon (Term 0) n) → glassify (glassify ∇) PE.≡ glassify ∇
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
    ∙ᵗ[ PE.subst₃ _⊢_∷_
          (PE.cong (_» _) (glassify-factor φ↜)) PE.refl PE.refl
          (glassify-⊢∷ ⊢t)
      ]
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
