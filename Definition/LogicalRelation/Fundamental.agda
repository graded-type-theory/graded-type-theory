------------------------------------------------------------------------
-- The fundamental lemma of the logical relation for validity.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Fundamental
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M

open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Substitution.Introductions R
import Definition.LogicalRelation.Substitution.Introductions.Erased R
  as Erased
open import Definition.LogicalRelation.Substitution.Weakening R

import Graded.Derived.Erased.Untyped 𝕄 as E

open import Tools.Product
open import Tools.Nat using (Nat)
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Con Term n
    Δ : Con Term m
    σ σ₁ σ₂ σ′ : Subst m n
    A A₁ A₂ B t t₁ t₂ u : Term _
    ⊩Γ : ⊩ᵛ _

opaque mutual

  -- Fundamental theorem for contexts.
  valid : ⊢ Γ → ⊩ᵛ Γ
  valid ε        = ε
  valid (_ ∙ ⊢A) = ⊩ᵛ-∙-intro (fundamental-⊩ᵛ ⊢A)

  -- Fundamental theorem for types.
  fundamental-⊩ᵛ : Γ ⊢ A → Γ ⊩ᵛ⟨ ¹ ⟩ A
  fundamental-⊩ᵛ (ℕⱼ ⊢Γ) =
    ℕᵛ (valid ⊢Γ)
  fundamental-⊩ᵛ (Emptyⱼ ⊢Γ) =
    Emptyᵛ (valid ⊢Γ)
  fundamental-⊩ᵛ (Unitⱼ ⊢Γ ok) =
    Unitᵛ (valid ⊢Γ) ok
  fundamental-⊩ᵛ (Uⱼ ⊢Γ) =
    ⊩ᵛU (valid ⊢Γ)
  fundamental-⊩ᵛ (ΠΣⱼ ⊢A ⊢B ok) =
    ΠΣᵛ ok (fundamental-⊩ᵛ ⊢A) (fundamental-⊩ᵛ ⊢B)
  fundamental-⊩ᵛ (Idⱼ ⊢t ⊢u) =
    Idᵛ (fundamental-⊩ᵛ∷ ⊢t) (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ (univ ⊢A) =
    ⊩ᵛ∷U→⊩ᵛ (fundamental-⊩ᵛ∷ ⊢A)

  -- Fundamental theorem for type equality.
  fundamental-⊩ᵛ≡ : Γ ⊢ A ≡ B → Γ ⊩ᵛ⟨ ¹ ⟩ A ≡ B
  fundamental-⊩ᵛ≡ (univ A≡B) =
    ⊩ᵛ≡∷U→⊩ᵛ≡ (fundamental-⊩ᵛ≡∷ A≡B)
  fundamental-⊩ᵛ≡ (refl ⊢A) =
    refl-⊩ᵛ≡ (fundamental-⊩ᵛ ⊢A)
  fundamental-⊩ᵛ≡ (sym A≡B) =
    sym-⊩ᵛ≡ (fundamental-⊩ᵛ≡ A≡B)
  fundamental-⊩ᵛ≡ (trans A≡B B≡C) =
    trans-⊩ᵛ≡ (fundamental-⊩ᵛ≡ A≡B) (fundamental-⊩ᵛ≡ B≡C)
  fundamental-⊩ᵛ≡ (ΠΣ-cong _ A₁≡A₂ B₁≡B₂ ok) =
    ΠΣ-congᵛ ok (fundamental-⊩ᵛ≡ A₁≡A₂) (fundamental-⊩ᵛ≡ B₁≡B₂)
  fundamental-⊩ᵛ≡ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-congᵛ (fundamental-⊩ᵛ≡ A₁≡A₂) (fundamental-⊩ᵛ≡∷ t₁≡t₂)
      (fundamental-⊩ᵛ≡∷ u₁≡u₂)

  -- Fundamental theorem for terms.
  fundamental-⊩ᵛ∷ : Γ ⊢ t ∷ A → Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A
  fundamental-⊩ᵛ∷ (ℕⱼ ⊢Γ) =
    ℕᵗᵛ (valid ⊢Γ)
  fundamental-⊩ᵛ∷ (Emptyⱼ ⊢Γ) =
    Emptyᵗᵛ (valid ⊢Γ)
  fundamental-⊩ᵛ∷ (Unitⱼ ⊢Γ ok) =
    Unitᵗᵛ (valid ⊢Γ) ok
  fundamental-⊩ᵛ∷ (ΠΣⱼ ⊢A ⊢B ok) =
    ΠΣᵗᵛ ok (fundamental-⊩ᵛ∷ ⊢A) (fundamental-⊩ᵛ∷ ⊢B)
  fundamental-⊩ᵛ∷ (var ⊢Γ x∈Γ) =
    emb-⊩ᵛ∷ ≤¹ (varᵛ x∈Γ (valid ⊢Γ) .proj₂)
  fundamental-⊩ᵛ∷ (lamⱼ ⊢A ⊢t ok) =
    lamᵛ ok (fundamental-⊩ᵛ ⊢A) (fundamental-⊩ᵛ∷ ⊢t)
  fundamental-⊩ᵛ∷ (⊢t ∘ⱼ ⊢u) =
    ∘ᵛ (fundamental-⊩ᵛ∷ ⊢t) (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ∷ (prodⱼ _ ⊢B ⊢t ⊢u ok) =
    prodᵛ ok (fundamental-⊩ᵛ ⊢B) (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ∷ (fstⱼ _ _ ⊢t) =
    fstᵛ (fundamental-⊩ᵛ∷ ⊢t)
  fundamental-⊩ᵛ∷ (sndⱼ _ _ ⊢t) =
    sndᵛ (fundamental-⊩ᵛ∷ ⊢t)
  fundamental-⊩ᵛ∷ (zeroⱼ ⊢Γ) =
    zeroᵛ (valid ⊢Γ)
  fundamental-⊩ᵛ∷ (sucⱼ ⊢t) =
    sucᵛ (fundamental-⊩ᵛ∷ ⊢t)
  fundamental-⊩ᵛ∷ (natrecⱼ ⊢A ⊢t ⊢u ⊢v) =
    natrecᵛ (fundamental-⊩ᵛ ⊢A) (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ᵛ∷ ⊢u) (fundamental-⊩ᵛ∷ ⊢v)
  fundamental-⊩ᵛ∷ (emptyrecⱼ ⊢A ⊢t) =
    emptyrecᵛ (fundamental-⊩ᵛ ⊢A) (fundamental-⊩ᵛ∷ ⊢t)
  fundamental-⊩ᵛ∷ (starⱼ ⊢Γ ok) =
    starᵛ (valid ⊢Γ) ok
  fundamental-⊩ᵛ∷ (conv ⊢t A≡B) =
    conv-⊩ᵛ∷ (fundamental-⊩ᵛ≡ A≡B) (fundamental-⊩ᵛ∷ ⊢t)
  fundamental-⊩ᵛ∷ (prodrecⱼ _ _ ⊢C ⊢t ⊢u _) =
    prodrecᵛ (fundamental-⊩ᵛ ⊢C) (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ∷ (unitrecⱼ ⊢A ⊢t ⊢u _) =
    unitrecᵛ (fundamental-⊩ᵛ ⊢A) (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ∷ (Idⱼ ⊢A ⊢t ⊢u) =
    Idᵗᵛ (fundamental-⊩ᵛ∷ ⊢A) (fundamental-⊩ᵛ∷ ⊢t) (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ∷ (rflⱼ ⊢t) =
    rflᵛ (fundamental-⊩ᵛ∷ ⊢t)
  fundamental-⊩ᵛ∷ (Jⱼ _ _ ⊢B ⊢u _ ⊢w) =
    Jᵛ (fundamental-⊩ᵛ ⊢B) (fundamental-⊩ᵛ∷ ⊢u) (fundamental-⊩ᵛ∷ ⊢w)
  fundamental-⊩ᵛ∷ (Kⱼ _ ⊢B ⊢u ⊢v ok) =
    Kᵛ ok (fundamental-⊩ᵛ ⊢B) (fundamental-⊩ᵛ∷ ⊢u) (fundamental-⊩ᵛ∷ ⊢v)
  fundamental-⊩ᵛ∷ ([]-congⱼ ⊢t ⊢u ⊢v ok) =
    []-congᵛ ok (fundamental-⊩ᵛ∷ ⊢v)

  -- Fundamental theorem for term equality.
  fundamental-⊩ᵛ≡∷ : Γ ⊢ t ≡ u ∷ A → Γ ⊩ᵛ⟨ ¹ ⟩ t ≡ u ∷ A
  fundamental-⊩ᵛ≡∷ (refl ⊢t) =
    refl-⊩ᵛ≡∷ (fundamental-⊩ᵛ∷ ⊢t)
  fundamental-⊩ᵛ≡∷ (sym t≡u) =
    sym-⊩ᵛ≡∷ (fundamental-⊩ᵛ≡∷ t≡u)
  fundamental-⊩ᵛ≡∷ (trans t≡u u≡v) =
    trans-⊩ᵛ≡∷ (fundamental-⊩ᵛ≡∷ t≡u) (fundamental-⊩ᵛ≡∷ u≡v)
  fundamental-⊩ᵛ≡∷ (conv t≡u A≡B) =
    conv-⊩ᵛ≡∷ (fundamental-⊩ᵛ≡ A≡B) (fundamental-⊩ᵛ≡∷ t≡u)
  fundamental-⊩ᵛ≡∷ (ΠΣ-cong _ A₁≡A₂ B₁≡B₂ ok) =
    ΠΣ-congᵗᵛ ok (fundamental-⊩ᵛ≡∷ A₁≡A₂) (fundamental-⊩ᵛ≡∷ B₁≡B₂)
  fundamental-⊩ᵛ≡∷ (app-cong t₁≡t₂ u₁≡u₂) =
    ∘-congᵛ (fundamental-⊩ᵛ≡∷ t₁≡t₂) (fundamental-⊩ᵛ≡∷ u₁≡u₂)
  fundamental-⊩ᵛ≡∷ (β-red _ _ ⊢t ⊢u PE.refl ok) =
    β-redᵛ ok (fundamental-⊩ᵛ∷ ⊢t) (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ≡∷ (η-eq _ ⊢t₁ ⊢t₂ wk1-t₁∘0≡wk1-t₂∘0) =
    η-eqᵛ (fundamental-⊩ᵛ∷ ⊢t₁) (fundamental-⊩ᵛ∷ ⊢t₂)
      (fundamental-⊩ᵛ≡∷ wk1-t₁∘0≡wk1-t₂∘0)
  fundamental-⊩ᵛ≡∷ (suc-cong t≡u) =
    suc-congᵛ (fundamental-⊩ᵛ≡∷ t≡u)
  fundamental-⊩ᵛ≡∷ (natrec-cong _ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) =
    natrec-congᵛ (fundamental-⊩ᵛ≡ A₁≡A₂) (fundamental-⊩ᵛ≡∷ t₁≡t₂)
      (fundamental-⊩ᵛ≡∷ u₁≡u₂) (fundamental-⊩ᵛ≡∷ v₁≡v₂)
  fundamental-⊩ᵛ≡∷ (natrec-zero ⊢A ⊢t ⊢u) =
    natrec-zeroᵛ (fundamental-⊩ᵛ ⊢A) (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ≡∷ (natrec-suc ⊢A ⊢t ⊢u ⊢v) =
    natrec-sucᵛ (fundamental-⊩ᵛ ⊢A) (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ᵛ∷ ⊢u) (fundamental-⊩ᵛ∷ ⊢v)
  fundamental-⊩ᵛ≡∷ (emptyrec-cong F≡F′ n≡n′) =
    emptyrec-congᵛ (fundamental-⊩ᵛ≡ F≡F′) (fundamental-⊩ᵛ≡∷ n≡n′)
  fundamental-⊩ᵛ≡∷ (η-unit ⊢t ⊢u η) =
    η-unitᵛ (fundamental-⊩ᵛ∷ ⊢t) (fundamental-⊩ᵛ∷ ⊢u) η
  fundamental-⊩ᵛ≡∷ (fst-cong _ _ t₁≡t₂) =
    fst-congᵛ (fundamental-⊩ᵛ≡∷ t₁≡t₂)
  fundamental-⊩ᵛ≡∷ (snd-cong _ _ t₁≡t₂) =
    snd-congᵛ (fundamental-⊩ᵛ≡∷ t₁≡t₂)
  fundamental-⊩ᵛ≡∷ (prod-cong _ ⊢B t₁≡t₂ u₁≡u₂ ok) =
    prod-congᵛ ok (fundamental-⊩ᵛ ⊢B) (fundamental-⊩ᵛ≡∷ t₁≡t₂)
      (fundamental-⊩ᵛ≡∷ u₁≡u₂)
  fundamental-⊩ᵛ≡∷ (Σ-β₁ _ ⊢B ⊢t ⊢u PE.refl ok) =
    Σ-β₁ᵛ ok (fundamental-⊩ᵛ ⊢B) (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ≡∷ (Σ-β₂ _ ⊢B ⊢t ⊢u PE.refl ok) =
    Σ-β₂ᵛ ok (fundamental-⊩ᵛ ⊢B) (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ≡∷ (Σ-η _ _ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂) =
    Σ-ηᵛ (fundamental-⊩ᵛ∷ ⊢t₁) (fundamental-⊩ᵛ∷ ⊢t₂)
      (fundamental-⊩ᵛ≡∷ fst-t₁≡fst-t₂) (fundamental-⊩ᵛ≡∷ snd-t₁≡snd-t₂)
  fundamental-⊩ᵛ≡∷ (prodrec-cong _ _ C₁≡C₂ t₁≡t₂ u₁≡u₂ _) =
    prodrec-congᵛ (fundamental-⊩ᵛ≡ C₁≡C₂) (fundamental-⊩ᵛ≡∷ t₁≡t₂)
      (fundamental-⊩ᵛ≡∷ u₁≡u₂)
  fundamental-⊩ᵛ≡∷ (prodrec-β _ _ ⊢C ⊢t ⊢u ⊢v PE.refl _) =
    prodrec-βᵛ (fundamental-⊩ᵛ ⊢C) (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ᵛ∷ ⊢u) (fundamental-⊩ᵛ∷ ⊢v)
  fundamental-⊩ᵛ≡∷ (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ _ _) =
    unitrec-congᵛ (fundamental-⊩ᵛ≡ A₁≡A₂) (fundamental-⊩ᵛ≡∷ t₁≡t₂)
      (fundamental-⊩ᵛ≡∷ u₁≡u₂)
  fundamental-⊩ᵛ≡∷ (unitrec-β ⊢A ⊢u _ no-η) =
    unitrec-βᵛ (fundamental-⊩ᵛ ⊢A) (fundamental-⊩ᵛ∷ ⊢u) no-η
  fundamental-⊩ᵛ≡∷ (unitrec-β-η ⊢A ⊢t ⊢u _ η) =
    unitrec-β-ηᵛ (fundamental-⊩ᵛ ⊢A) (fundamental-⊩ᵛ∷ ⊢t)
      (fundamental-⊩ᵛ∷ ⊢u) η
  fundamental-⊩ᵛ≡∷ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-congᵗᵛ (fundamental-⊩ᵛ≡∷ A₁≡A₂) (fundamental-⊩ᵛ≡∷ t₁≡t₂)
      (fundamental-⊩ᵛ≡∷ u₁≡u₂)
  fundamental-⊩ᵛ≡∷ (J-cong _ A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    J-congᵛ (fundamental-⊩ᵛ≡ A₁≡A₂) (fundamental-⊩ᵛ≡∷ t₁≡t₂)
      (fundamental-⊩ᵛ≡ B₁≡B₂) (fundamental-⊩ᵛ≡∷ u₁≡u₂)
      (fundamental-⊩ᵛ≡∷ v₁≡v₂) (fundamental-⊩ᵛ≡∷ w₁≡w₂)
  fundamental-⊩ᵛ≡∷ (K-cong A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) =
    K-congᵛ ok (fundamental-⊩ᵛ≡ A₁≡A₂) (fundamental-⊩ᵛ≡∷ t₁≡t₂)
      (fundamental-⊩ᵛ≡ B₁≡B₂) (fundamental-⊩ᵛ≡∷ u₁≡u₂)
      (fundamental-⊩ᵛ≡∷ v₁≡v₂)
  fundamental-⊩ᵛ≡∷ ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) =
    []-cong-congᵛ ok (fundamental-⊩ᵛ≡ A₁≡A₂) (fundamental-⊩ᵛ≡∷ t₁≡t₂)
      (fundamental-⊩ᵛ≡∷ u₁≡u₂) (fundamental-⊩ᵛ≡∷ v₁≡v₂)
  fundamental-⊩ᵛ≡∷ (J-β _ ⊢t ⊢B ⊢u PE.refl) =
    J-βᵛ (fundamental-⊩ᵛ∷ ⊢t) (fundamental-⊩ᵛ ⊢B) (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ≡∷ (K-β _ ⊢B ⊢u ok) =
    K-βᵛ ok (fundamental-⊩ᵛ ⊢B) (fundamental-⊩ᵛ∷ ⊢u)
  fundamental-⊩ᵛ≡∷ ([]-cong-β ⊢t PE.refl ok) =
    []-cong-βᵛ ok (fundamental-⊩ᵛ∷ ⊢t)

opaque

  -- Fundamental theorem for substitutions.

  fundamental-⊩ˢ∷ : ⊢ Δ → ⊢ Γ → Δ ⊢ˢ σ ∷ Γ → Δ ⊩ˢ σ ∷ Γ
  fundamental-⊩ˢ∷ ⊢Δ ε _ =
    ⊩ˢ∷ε⇔ .proj₂ ⊢Δ
  fundamental-⊩ˢ∷ ⊢Δ (⊢Γ ∙ ⊢A) (⊢tail , ⊢head) =
    ⊩ˢ∷∙⇔′ .proj₂
      ( (_ , fundamental-⊩ᵛ ⊢A)
      , (_ , ⊩ᵛ∷→⊩∷ (fundamental-⊩ᵛ∷ ⊢head))
      , fundamental-⊩ˢ∷ ⊢Δ ⊢Γ ⊢tail
      )

opaque

  -- Fundamental theorem for substitution equality.

  fundamental-⊩ˢ≡∷ : ⊢ Δ → ⊢ Γ → Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ
  fundamental-⊩ˢ≡∷ ⊢Δ ε _ =
    ⊩ˢ≡∷ε⇔ .proj₂ ⊢Δ
  fundamental-⊩ˢ≡∷ ⊢Δ (⊢Γ ∙ ⊢A) (tail≡tail , head≡head) =
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( (_ , fundamental-⊩ᵛ ⊢A)
      , (_ , ⊩ᵛ≡∷→⊩≡∷ (fundamental-⊩ᵛ≡∷ head≡head))
      , fundamental-⊩ˢ≡∷ ⊢Δ ⊢Γ tail≡tail
      )
