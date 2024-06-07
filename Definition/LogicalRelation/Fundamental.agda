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
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Introductions R
import Definition.LogicalRelation.Substitution.Introductions.Erased R
  as Erased
import Definition.LogicalRelation.Substitution.Irrelevance R as S
open import Definition.LogicalRelation.Substitution.Weakening R

import Graded.Derived.Erased.Untyped 𝕄 as E

open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.Unit
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

opaque
 unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_ _⊩ᵛ⟨_⟩_∷_ _⊩ᵛ⟨_⟩_≡_∷_

 mutual
  -- Fundamental theorem for contexts.
  valid : ⊢ Γ → ⊩ᵛ Γ
  valid ε = ε
  valid (⊢Γ ∙ A) = let [Γ] , [A] = fundamental A in [Γ] ∙ [A]


  -- Fundamental theorem for types.
  fundamental : ∀ {A} (⊢A : Γ ⊢ A) → Σ (⊩ᵛ Γ) (λ [Γ] → Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
  fundamental (ℕⱼ ⊢Γ) =
    ℕᵛ (valid ⊢Γ)
  fundamental (Emptyⱼ x) = Emptyᵛ (valid x)
  fundamental (Unitⱼ ⊢Γ ok) =
    Unitᵛ (valid ⊢Γ) ok
  fundamental (Uⱼ ⊢Γ) =
    ⊩ᵛU (valid ⊢Γ)
  fundamental (ΠΣⱼ ⊢A ⊢B ok) =
    ΠΣᵛ ok (fundamental ⊢A) (fundamental ⊢B)
  fundamental (Idⱼ ⊢t ⊢u) =
    Idᵛ (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
  fundamental (univ ⊢A) =
    ⊩ᵛ∷U→⊩ᵛ (fundamentalTerm ⊢A)

  -- Fundamental theorem for type equality.
  fundamentalEq : ∀ {A B} → Γ ⊢ A ≡ B
    → ∃  λ ([Γ] : ⊩ᵛ Γ)
    → ∃₂ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) ([B] : Γ ⊩ᵛ⟨ ¹ ⟩ B / [Γ])
    → Γ ⊩ᵛ⟨ ¹ ⟩ A ≡ B / [Γ] / [A]
  fundamentalEq (univ A≡B) =
    ⊩ᵛ≡∷U→⊩ᵛ≡ (fundamentalTermEq A≡B)
  fundamentalEq (refl ⊢A) =
    refl-⊩ᵛ≡ (fundamental ⊢A)
  fundamentalEq (sym A≡B) =
    sym-⊩ᵛ≡ (fundamentalEq A≡B)
  fundamentalEq (trans A≡B B≡C) =
    trans-⊩ᵛ≡ (fundamentalEq A≡B) (fundamentalEq B≡C)
  fundamentalEq (ΠΣ-cong _ A₁≡A₂ B₁≡B₂ ok) =
    ΠΣ-congᵛ ok (fundamentalEq A₁≡A₂) (fundamentalEq B₁≡B₂)
  fundamentalEq (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-congᵛ (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂)

  -- Fundamental theorem for terms.
  fundamentalTerm : ∀ {A t} → Γ ⊢ t ∷ A
    → ∃ λ ([Γ] : ⊩ᵛ Γ)
    → ∃ λ ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ])
    → Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A / [Γ] / [A]
  fundamentalTerm (ℕⱼ ⊢Γ) =
    ℕᵗᵛ (valid ⊢Γ)
  fundamentalTerm (Emptyⱼ x) =
    Emptyᵗᵛ (valid x)
  fundamentalTerm (Unitⱼ ⊢Γ ok) =
    Unitᵗᵛ (valid ⊢Γ) ok
  fundamentalTerm (ΠΣⱼ {G = B} ⊢A ⊢B ok) =
    ΠΣᵗᵛ {B = B} ok (fundamentalTerm ⊢A) (fundamentalTerm ⊢B)
  fundamentalTerm (var ⊢Γ x∈Γ) =
    emb-⊩ᵛ∷ ≤¹ (varᵛ x∈Γ (valid ⊢Γ) .proj₂)
  fundamentalTerm (lamⱼ {t} ⊢A ⊢t ok) =
    lamᵛ {t = t} ok (fundamental ⊢A) (fundamentalTerm ⊢t)
  fundamentalTerm (_∘ⱼ_ {t = t} ⊢t ⊢u) =
    ∘ᵛ {t = t} (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
  fundamentalTerm (prodⱼ {u} _ ⊢B ⊢t ⊢u ok) =
    prodᵛ {u = u} ok (fundamental ⊢B) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u)
  fundamentalTerm (fstⱼ {t} _ _ ⊢t) =
    fstᵛ {t = t} (fundamentalTerm ⊢t)
  fundamentalTerm (sndⱼ _ _ ⊢t) =
    sndᵛ (fundamentalTerm ⊢t)
  fundamentalTerm (zeroⱼ ⊢Γ) =
    zeroᵛ (valid ⊢Γ)
  fundamentalTerm (sucⱼ {n = t} ⊢t) =
    sucᵛ {t = t} (fundamentalTerm ⊢t)
  fundamentalTerm (natrecⱼ {z = t} {s = u} ⊢A ⊢t ⊢u ⊢v) =
    natrecᵛ {t = t} {u = u} (fundamental ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u) (fundamentalTerm ⊢v)
  fundamentalTerm (emptyrecⱼ {t = t} ⊢A ⊢t) =
    emptyrecᵛ {t = t} (fundamental ⊢A) (fundamentalTerm ⊢t)
  fundamentalTerm (starⱼ ⊢Γ ok) =
    starᵛ (valid ⊢Γ) ok
  fundamentalTerm (conv {t} ⊢t A≡B) =
    conv-⊩ᵛ∷ {t = t} (fundamentalEq A≡B) (fundamentalTerm ⊢t)
  fundamentalTerm (prodrecⱼ {u} _ _ ⊢C ⊢t ⊢u _) =
    prodrecᵛ {u = u} (fundamental ⊢C) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u)
  fundamentalTerm (unitrecⱼ {u} ⊢A ⊢t ⊢u _) =
    unitrecᵛ {u = u} (fundamental ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u)
  fundamentalTerm (Idⱼ {t} {u} ⊢A ⊢t ⊢u) =
    Idᵗᵛ {t = t} {u = u} (fundamentalTerm ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u)
  fundamentalTerm (rflⱼ ⊢t) =
    rflᵛ (fundamentalTerm ⊢t)
  fundamentalTerm (Jⱼ {u} _ _ ⊢B ⊢u _ ⊢w) =
    Jᵛ {u = u} (fundamental ⊢B) (fundamentalTerm ⊢u)
      (fundamentalTerm ⊢w)
  fundamentalTerm (Kⱼ {u} _ ⊢B ⊢u ⊢v ok) =
    Kᵛ {u = u} ok (fundamental ⊢B) (fundamentalTerm ⊢u)
      (fundamentalTerm ⊢v)
  fundamentalTerm ([]-congⱼ {v} ⊢t ⊢u ⊢v ok) =
    []-congᵛ {v = v} ok (fundamentalTerm ⊢v)

  -- Fundamental theorem for term equality.
  fundamentalTermEq : ∀ {A t t′} → Γ ⊢ t ≡ t′ ∷ A
                    → ∃ λ ([Γ] : ⊩ᵛ Γ) →
                      [ Γ ⊩ᵛ⟨ ¹ ⟩ t ≡ t′ ∷ A / [Γ] ]
  fundamentalTermEq (refl ⊢t) =
    refl-⊩ᵛ≡∷ (fundamentalTerm ⊢t)
  fundamentalTermEq (sym t≡u) =
    sym-⊩ᵛ≡∷ (fundamentalTermEq t≡u)
  fundamentalTermEq (trans t≡u u≡v) =
    trans-⊩ᵛ≡∷ (fundamentalTermEq t≡u) (fundamentalTermEq u≡v)
  fundamentalTermEq (conv t≡u A≡B) =
    conv-⊩ᵛ≡∷ (fundamentalEq A≡B) (fundamentalTermEq t≡u)
  fundamentalTermEq (ΠΣ-cong _ A₁≡A₂ B₁≡B₂ ok) =
    ΠΣ-congᵗᵛ ok (fundamentalTermEq A₁≡A₂) (fundamentalTermEq B₁≡B₂)
  fundamentalTermEq (app-cong t₁≡t₂ u₁≡u₂) =
    ∘-congᵛ (fundamentalTermEq t₁≡t₂) (fundamentalTermEq u₁≡u₂)
  fundamentalTermEq (β-red _ _ ⊢t ⊢u PE.refl ok) =
    β-redᵛ ok (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
  fundamentalTermEq (η-eq _ ⊢t₁ ⊢t₂ wk1-t₁∘0≡wk1-t₂∘0) =
    η-eqᵛ (fundamentalTerm ⊢t₁) (fundamentalTerm ⊢t₂)
      (fundamentalTermEq wk1-t₁∘0≡wk1-t₂∘0)
  fundamentalTermEq (suc-cong t≡u) =
    suc-congᵛ (fundamentalTermEq t≡u)
  fundamentalTermEq (natrec-cong _ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) =
    natrec-congᵛ (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂) (fundamentalTermEq v₁≡v₂)
  fundamentalTermEq (natrec-zero ⊢A ⊢t ⊢u) =
    natrec-zeroᵛ (fundamental ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u)
  fundamentalTermEq (natrec-suc ⊢A ⊢t ⊢u ⊢v) =
    natrec-sucᵛ (fundamental ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u) (fundamentalTerm ⊢v)
  fundamentalTermEq (emptyrec-cong F≡F′ n≡n′) =
    emptyrec-congᵛ (fundamentalEq F≡F′) (fundamentalTermEq n≡n′)
  fundamentalTermEq (η-unit ⊢t ⊢u η) =
    η-unitᵛ (fundamentalTerm ⊢t) (fundamentalTerm ⊢u) η
  fundamentalTermEq (fst-cong _ _ t₁≡t₂) =
    fst-congᵛ (fundamentalTermEq t₁≡t₂)
  fundamentalTermEq (snd-cong _ _ t₁≡t₂) =
    snd-congᵛ (fundamentalTermEq t₁≡t₂)
  fundamentalTermEq (prod-cong _ ⊢B t₁≡t₂ u₁≡u₂ ok) =
    prod-congᵛ ok (fundamental ⊢B) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂)
  fundamentalTermEq (Σ-β₁ _ ⊢B ⊢t ⊢u PE.refl ok) =
    Σ-β₁ᵛ ok (fundamental ⊢B) (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
  fundamentalTermEq (Σ-β₂ _ ⊢B ⊢t ⊢u PE.refl ok) =
    Σ-β₂ᵛ ok (fundamental ⊢B) (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
  fundamentalTermEq (Σ-η _ _ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂) =
    Σ-ηᵛ (fundamentalTerm ⊢t₁) (fundamentalTerm ⊢t₂)
      (fundamentalTermEq fst-t₁≡fst-t₂)
      (fundamentalTermEq snd-t₁≡snd-t₂)
  fundamentalTermEq (prodrec-cong _ _ C₁≡C₂ t₁≡t₂ u₁≡u₂ _) =
    prodrec-congᵛ (fundamentalEq C₁≡C₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂)
  fundamentalTermEq (prodrec-β _ _ ⊢C ⊢t ⊢u ⊢v PE.refl _) =
    prodrec-βᵛ (fundamental ⊢C) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u) (fundamentalTerm ⊢v)
  fundamentalTermEq (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ _ _) =
    unitrec-congᵛ (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂)
  fundamentalTermEq (unitrec-β ⊢A ⊢u _ no-η) =
    unitrec-βᵛ (fundamental ⊢A) (fundamentalTerm ⊢u) no-η
  fundamentalTermEq (unitrec-β-η ⊢A ⊢t ⊢u _ η) =
    unitrec-β-ηᵛ (fundamental ⊢A) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u) η
  fundamentalTermEq (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    Id-congᵗᵛ (fundamentalTermEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂)
  fundamentalTermEq (J-cong _ A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    J-congᵛ (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalEq B₁≡B₂) (fundamentalTermEq u₁≡u₂)
      (fundamentalTermEq v₁≡v₂) (fundamentalTermEq w₁≡w₂)
  fundamentalTermEq (K-cong A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) =
    K-congᵛ ok (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalEq B₁≡B₂) (fundamentalTermEq u₁≡u₂)
      (fundamentalTermEq v₁≡v₂)
  fundamentalTermEq ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) =
    []-cong-congᵛ ok (fundamentalEq A₁≡A₂) (fundamentalTermEq t₁≡t₂)
      (fundamentalTermEq u₁≡u₂) (fundamentalTermEq v₁≡v₂)
  fundamentalTermEq (J-β _ ⊢t ⊢B ⊢u PE.refl) =
    J-βᵛ (fundamentalTerm ⊢t) (fundamental ⊢B) (fundamentalTerm ⊢u)
  fundamentalTermEq (K-β _ ⊢B ⊢u ok) =
    K-βᵛ ok (fundamental ⊢B) (fundamentalTerm ⊢u)
  fundamentalTermEq ([]-cong-β ⊢t PE.refl ok) =
    []-cong-βᵛ ok (fundamentalTerm ⊢t)

-- Fundamental theorem for substitutions.
fundamentalSubst : (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ˢ σ ∷ Γ
      → ∃ λ [Γ] → Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ
fundamentalSubst ε ⊢Δ [σ] = ε , lift tt
fundamentalSubst (⊢Γ ∙ ⊢A) ⊢Δ ([tailσ] , [headσ]) =
  let [Γ] , [A] = fundamental ⊢A
      [Δ] , [A]′ , [t] = fundamentalTerm [headσ]
      [Γ]′ , [σ] = fundamentalSubst ⊢Γ ⊢Δ [tailσ]
      [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [idA]  = proj₁ (unwrap [A]′ (soundContext [Δ]) (idSubstS [Δ]))
      [idA]′ = proj₁ (unwrap [A] ⊢Δ [tailσ]′)
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
  in  [Γ] ∙ [A] , ([tailσ]′
  ,   irrelevanceTerm″ (subst-id _) (subst-id _) [idA] [idA]′ [idt])

-- Fundamental theorem for substitution equality.
fundamentalSubstEq : (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ˢ σ ≡ σ′ ∷ Γ
      → ∃₂ λ [Γ] [σ]
      → ∃  λ ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
      → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
fundamentalSubstEq ε ⊢Δ σ = ε , lift tt , lift tt , lift tt
fundamentalSubstEq (⊢Γ ∙ ⊢A) ⊢Δ (tailσ≡σ′ , headσ≡σ′) =
  let [Γ] , [A] = fundamental ⊢A
      [Γ]′ , [tailσ] , [tailσ′] , [tailσ≡σ′] = fundamentalSubstEq ⊢Γ ⊢Δ tailσ≡σ′
      [Δ] , modelsTermEq [A]′ [t] [t′] [t≡t′] = fundamentalTermEq headσ≡σ′
      [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ]
      [tailσ′]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ′]
      [tailσ≡σ′]′ = S.irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ] [tailσ]′ [tailσ≡σ′]
      [idA]  = proj₁ (unwrap [A]′ (soundContext [Δ]) (idSubstS [Δ]))
      [idA]′ = proj₁ (unwrap [A] ⊢Δ [tailσ]′)
      [idA]″ = proj₁ (unwrap [A] ⊢Δ [tailσ′]′)
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
      [idt′] = proj₁ ([t′] (soundContext [Δ]) (idSubstS [Δ]))
      [idt≡t′]  = [t≡t′] (soundContext [Δ]) (idSubstS [Δ])
  in  [Γ] ∙ [A]
  ,   ([tailσ]′ , irrelevanceTerm″ (subst-id _) (subst-id _) [idA] [idA]′ [idt])
  ,   ([tailσ′]′ , convTerm₁ [idA]′ [idA]″
                             (proj₂ (unwrap [A] ⊢Δ [tailσ]′) [tailσ′]′ [tailσ≡σ′]′)
                             (irrelevanceTerm″ (subst-id _) (subst-id _)
                                                [idA] [idA]′ [idt′]))
  ,   ([tailσ≡σ′]′ , irrelevanceEqTerm″ (subst-id _) (subst-id _) (subst-id _)
                                         [idA] [idA]′ [idt≡t′])

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- A variant of fundamental.

  fundamental-⊩ᵛ : Γ ⊢ A → Γ ⊩ᵛ⟨ ¹ ⟩ A
  fundamental-⊩ᵛ = fundamental

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_

  -- A variant of fundamentalEq.

  fundamental-⊩ᵛ≡ : Γ ⊢ A ≡ B → Γ ⊩ᵛ⟨ ¹ ⟩ A ≡ B
  fundamental-⊩ᵛ≡ = fundamentalEq

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_

  -- A variant of fundamentalTerm.

  fundamental-⊩ᵛ∷ : Γ ⊢ t ∷ A → Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A
  fundamental-⊩ᵛ∷ = fundamentalTerm

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_∷_

  -- A variant of fundamentalTermEq.

  fundamental-⊩ᵛ≡∷ : Γ ⊢ t ≡ u ∷ A → Γ ⊩ᵛ⟨ ¹ ⟩ t ≡ u ∷ A
  fundamental-⊩ᵛ≡∷ = fundamentalTermEq

opaque
  unfolding _⊩ˢ_∷_

  -- A variant of fundamentalSubst.

  fundamental-⊩ˢ∷ : ⊢ Δ → ⊢ Γ → Δ ⊢ˢ σ ∷ Γ → Δ ⊩ˢ σ ∷ Γ
  fundamental-⊩ˢ∷ ⊢Δ ⊢Γ ⊢σ =
    case fundamentalSubst ⊢Γ ⊢Δ ⊢σ of λ
      (_ , ⊩σ) →
    _ , _ , ⊩σ

opaque
  unfolding _⊩ˢ_≡_∷_

  -- A variant of fundamentalSubstEq.

  fundamental-⊩ˢ≡∷ : ⊢ Δ → ⊢ Γ → Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ
  fundamental-⊩ˢ≡∷ ⊢Δ ⊢Γ σ₁≡σ₂ =
    case fundamentalSubstEq ⊢Γ ⊢Δ σ₁≡σ₂ of λ
      (_ , σ₁≡σ₂) →
    _ , _ , σ₁≡σ₂
