------------------------------------------------------------------------
-- Sizes of derivations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Size
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Untyped M
open import Definition.Typed R

open import Tools.Size

private variable
  Γ       : Con Term _
  A B t u : Term _

opaque mutual

  -- The size of a derivation.

  size-⊢′ : ⊢ Γ → Size
  size-⊢′ ε         = leaf
  size-⊢′ (⊢Γ ∙ ⊢A) = size-⊢′ ⊢Γ ⊕ size-⊢ ⊢A

  -- The size of a derivation.

  size-⊢ : Γ ⊢ A → Size
  size-⊢ (Uⱼ ⊢Γ)      = node (size-⊢′ ⊢Γ)
  size-⊢ (univ ⊢A)    = node (size-⊢∷ ⊢A)
  size-⊢ (ΠΣⱼ ⊢B _)   = node (size-⊢ ⊢B)
  size-⊢ (Emptyⱼ ⊢Γ)  = node (size-⊢′ ⊢Γ)
  size-⊢ (Unitⱼ ⊢Γ _) = node (size-⊢′ ⊢Γ)
  size-⊢ (ℕⱼ ⊢Γ)      = node (size-⊢′ ⊢Γ)
  size-⊢ (Idⱼ ⊢t ⊢u)  = size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u

  -- The size of a derivation.

  size-⊢∷ : Γ ⊢ t ∷ A → Size
  size-⊢∷ (conv ⊢t B≡A) =
    size-⊢∷ ⊢t ⊕ size-⊢≡ B≡A
  size-⊢∷ (var ⊢Γ _) =
    node (size-⊢′ ⊢Γ)
  size-⊢∷ (Uⱼ ⊢Γ) =
    node (size-⊢′ ⊢Γ)
  size-⊢∷ (ΠΣⱼ ⊢A ⊢B _) =
    size-⊢∷ ⊢A ⊕ size-⊢∷ ⊢B
  size-⊢∷ (lamⱼ ⊢t _) =
    node (size-⊢∷ ⊢t)
  size-⊢∷ (⊢t ∘ⱼ ⊢u) =
    size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢∷ (prodⱼ ⊢B ⊢t ⊢u _) =
    size-⊢ ⊢B ⊕ size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢∷ (fstⱼ ⊢B ⊢t) =
    size-⊢ ⊢B ⊕ size-⊢∷ ⊢t
  size-⊢∷ (sndⱼ ⊢B ⊢t) =
    size-⊢ ⊢B ⊕ size-⊢∷ ⊢t
  size-⊢∷ (prodrecⱼ ⊢C ⊢t ⊢u _) =
    size-⊢ ⊢C ⊕ size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢∷ (Emptyⱼ ⊢Γ) =
    node (size-⊢′ ⊢Γ)
  size-⊢∷ (emptyrecⱼ ⊢A ⊢t) =
    size-⊢ ⊢A ⊕ size-⊢∷ ⊢t
  size-⊢∷ (Unitⱼ ⊢Γ _) =
    node (size-⊢′ ⊢Γ)
  size-⊢∷ (starⱼ ⊢Γ _) =
    node (size-⊢′ ⊢Γ)
  size-⊢∷ (unitrecⱼ ⊢A ⊢t ⊢u _) =
    size-⊢ ⊢A ⊕ size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢∷ (ℕⱼ ⊢Γ) =
    node (size-⊢′ ⊢Γ)
  size-⊢∷ (zeroⱼ ⊢Γ) =
    node (size-⊢′ ⊢Γ)
  size-⊢∷ (sucⱼ ⊢t) =
    node (size-⊢∷ ⊢t)
  size-⊢∷ (natrecⱼ ⊢t ⊢u ⊢v) =
    size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u ⊕ size-⊢∷ ⊢v
  size-⊢∷ (Idⱼ ⊢A ⊢t ⊢u) =
    size-⊢∷ ⊢A ⊕ size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢∷ (rflⱼ ⊢t) =
    node (size-⊢∷ ⊢t)
  size-⊢∷ (Jⱼ ⊢t ⊢B ⊢u ⊢v ⊢w) =
    (size-⊢∷ ⊢t ⊕ size-⊢ ⊢B) ⊕
    (size-⊢∷ ⊢u ⊕ size-⊢∷ ⊢v ⊕ size-⊢∷ ⊢w)
  size-⊢∷ (Kⱼ ⊢t ⊢B ⊢u ⊢v _) =
    (size-⊢∷ ⊢t ⊕ size-⊢ ⊢B) ⊕ (size-⊢∷ ⊢u ⊕ size-⊢∷ ⊢v)
  size-⊢∷ ([]-congⱼ ⊢t ⊢u ⊢v _) =
    size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u ⊕ size-⊢∷ ⊢v

  -- The size of a derivation.

  size-⊢≡ : Γ ⊢ A ≡ B → Size
  size-⊢≡ (univ A≡B) =
    node (size-⊢≡∷ A≡B)
  size-⊢≡ (refl ⊢A) =
    node (size-⊢ ⊢A)
  size-⊢≡ (sym B≡A) =
    node (size-⊢≡ B≡A)
  size-⊢≡ (trans A≡B B≡C) =
    size-⊢≡ A≡B ⊕ size-⊢≡ B≡C
  size-⊢≡ (ΠΣ-cong A₁≡B₁ A₂≡B₂ _) =
    size-⊢≡ A₁≡B₁ ⊕ size-⊢≡ A₂≡B₂
  size-⊢≡ (Id-cong A≡B t₁≡u₁ t₂≡u₂) =
    size-⊢≡ A≡B ⊕ size-⊢≡∷ t₁≡u₁ ⊕ size-⊢≡∷ t₂≡u₂

  -- The size of a derivation.

  size-⊢≡∷ : Γ ⊢ t ≡ u ∷ A → Size
  size-⊢≡∷ (refl ⊢t) =
    node (size-⊢∷ ⊢t)
  size-⊢≡∷ (sym u≡t) =
    node (size-⊢≡∷ u≡t)
  size-⊢≡∷ (trans t≡u u≡v) =
    size-⊢≡∷ t≡u ⊕ size-⊢≡∷ u≡v
  size-⊢≡∷ (conv t≡u B≡A) =
    size-⊢≡∷ t≡u ⊕ size-⊢≡ B≡A
  size-⊢≡∷ (ΠΣ-cong A₁≡B₁ A₂≡B₂ _) =
    size-⊢≡∷ A₁≡B₁ ⊕ size-⊢≡∷ A₂≡B₂
  size-⊢≡∷ (app-cong t₁≡u₁ t₂≡u₂) =
    size-⊢≡∷ t₁≡u₁ ⊕ size-⊢≡∷ t₂≡u₂
  size-⊢≡∷ (β-red ⊢B ⊢t ⊢u _ _) =
    size-⊢ ⊢B ⊕ size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢≡∷ (η-eq ⊢t₁ ⊢t₂ t₁0≡t₂0) =
    size-⊢∷ ⊢t₁ ⊕ size-⊢∷ ⊢t₂ ⊕ size-⊢≡∷ t₁0≡t₂0
  size-⊢≡∷ (fst-cong ⊢B t≡u) =
    size-⊢ ⊢B ⊕ size-⊢≡∷ t≡u
  size-⊢≡∷ (snd-cong ⊢B t≡u) =
    size-⊢ ⊢B ⊕ size-⊢≡∷ t≡u
  size-⊢≡∷ (Σ-β₁ ⊢B ⊢t ⊢u _ _) =
    size-⊢ ⊢B ⊕ size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢≡∷ (Σ-β₂ ⊢B ⊢t ⊢u _ _) =
    size-⊢ ⊢B ⊕ size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢≡∷ (Σ-η ⊢B ⊢t ⊢u fst-t≡fst-u snd-t≡snd-u) =
    (size-⊢ ⊢B ⊕ size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u) ⊕
    (size-⊢≡∷ fst-t≡fst-u ⊕ size-⊢≡∷ snd-t≡snd-u)
  size-⊢≡∷ (prod-cong ⊢B t₁≡u₁ t₂≡u₂ _) =
    size-⊢ ⊢B ⊕ size-⊢≡∷ t₁≡u₁ ⊕ size-⊢≡∷ t₂≡u₂
  size-⊢≡∷ (prodrec-cong C≡D t₁≡u₁ t₂≡u₂ _) =
    size-⊢≡ C≡D ⊕ size-⊢≡∷ t₁≡u₁ ⊕ size-⊢≡∷ t₂≡u₂
  size-⊢≡∷ (prodrec-β ⊢C ⊢t ⊢u ⊢v _ _) =
    (size-⊢ ⊢C ⊕ size-⊢∷ ⊢t) ⊕ (size-⊢∷ ⊢u ⊕ size-⊢∷ ⊢v)
  size-⊢≡∷ (emptyrec-cong A≡B t≡u) =
    size-⊢≡ A≡B ⊕ size-⊢≡∷ t≡u
  size-⊢≡∷ (unitrec-cong A≡B t₁≡u₁ t₂≡u₂ _ _) =
    size-⊢≡ A≡B ⊕ size-⊢≡∷ t₁≡u₁ ⊕ size-⊢≡∷ t₂≡u₂
  size-⊢≡∷ (unitrec-β ⊢A ⊢t _ _) =
    size-⊢ ⊢A ⊕ size-⊢∷ ⊢t
  size-⊢≡∷ (unitrec-β-η ⊢A ⊢t ⊢u _ _) =
    size-⊢ ⊢A ⊕ size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢≡∷ (η-unit ⊢t ⊢u _) =
    size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢≡∷ (suc-cong t≡u) =
    node (size-⊢≡∷ t≡u)
  size-⊢≡∷ (natrec-cong A≡B t₁≡u₁ t₂≡u₂ t₃≡u₃) =
    (size-⊢≡ A≡B ⊕ size-⊢≡∷ t₁≡u₁) ⊕ (size-⊢≡∷ t₂≡u₂ ⊕ size-⊢≡∷ t₃≡u₃)
  size-⊢≡∷ (natrec-zero ⊢t ⊢u) =
    size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u
  size-⊢≡∷ (natrec-suc ⊢t ⊢u ⊢v) =
    size-⊢∷ ⊢t ⊕ size-⊢∷ ⊢u ⊕ size-⊢∷ ⊢v
  size-⊢≡∷ (Id-cong A≡B t₁≡u₁ t₂≡u₂) =
    size-⊢≡∷ A≡B ⊕ size-⊢≡∷ t₁≡u₁ ⊕ size-⊢≡∷ t₂≡u₂
  size-⊢≡∷ (J-cong A₁≡B₁ ⊢t₁ t₁≡u₁ A₂≡B₂ t₂≡u₂ t₃≡u₃ t₄≡u₄) =
    (size-⊢≡ A₁≡B₁ ⊕ size-⊢∷ ⊢t₁ ⊕ size-⊢≡∷ t₁≡u₁) ⊕
    ((size-⊢≡ A₂≡B₂ ⊕ size-⊢≡∷ t₂≡u₂) ⊕
     (size-⊢≡∷ t₃≡u₃ ⊕ size-⊢≡∷ t₄≡u₄))
  size-⊢≡∷ (K-cong A₁≡B₁ ⊢t₁ t₁≡u₁ A₂≡B₂ t₂≡u₂ t₃≡u₃ _) =
    (size-⊢≡ A₁≡B₁ ⊕ size-⊢∷ ⊢t₁ ⊕ size-⊢≡∷ t₁≡u₁) ⊕
    (size-⊢≡ A₂≡B₂ ⊕ size-⊢≡∷ t₂≡u₂ ⊕ size-⊢≡∷ t₃≡u₃)
  size-⊢≡∷ ([]-cong-cong A≡B t₁≡u₁ t₂≡u₂ t₃≡u₃ _) =
    (size-⊢≡ A≡B ⊕ size-⊢≡∷ t₁≡u₁) ⊕ (size-⊢≡∷ t₂≡u₂ ⊕ size-⊢≡∷ t₃≡u₃)
  size-⊢≡∷ (J-β ⊢t ⊢B ⊢u _) =
    size-⊢∷ ⊢t ⊕ size-⊢ ⊢B ⊕ size-⊢∷ ⊢u
  size-⊢≡∷ (K-β ⊢t ⊢B ⊢u _) =
    size-⊢∷ ⊢t ⊕ size-⊢ ⊢B ⊕ size-⊢∷ ⊢u
  size-⊢≡∷ ([]-cong-β ⊢t _ _) =
    node (size-⊢∷ ⊢t)
