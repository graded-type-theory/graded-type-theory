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
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions R
import Definition.LogicalRelation.Substitution.Introductions.Erased R
  as Erased

import Graded.Derived.Erased.Untyped 𝕄 as E

open import Tools.Function
open import Tools.Product
open import Tools.Unit
open import Tools.Sum
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
  valid ε        = ⊩ᵛε⇔ .proj₂ _
  valid (_ ∙ ⊢A) = ⊩ᵛ-∙-intro (fundamental-⊩ᵛ ⊢A .proj₂)


  -- Fundamental theorem for types.
  fundamental-⊩ᵛ : Γ ⊢ A → Γ ⊩ᵛ A
  fundamental-⊩ᵛ (ℕⱼ ⊢Γ) =
    0 , ℕᵛ (valid ⊢Γ)
  fundamental-⊩ᵛ (Emptyⱼ x) =
    0 , Emptyᵛ (valid x)
  fundamental-⊩ᵛ (Unitⱼ ⊢Γ ok) =
    _ , Unitᵛ (valid ⊢Γ) ok
  fundamental-⊩ᵛ (Uⱼ ⊢Γ) =
    _ , ⊩ᵛU (valid ⊢Γ)
  fundamental-⊩ᵛ (ΠΣⱼ ⊢A ⊢B ok)
    with fundamental-⊩ᵛ ⊢A | fundamental-⊩ᵛ ⊢B
  … | l₁ , ⊩A | l₂ , ⊩B =
    l₁ ⊔ᵘ l₂ , ΠΣᵛ ok (emb-⊩ᵛ ≤ᵘ⊔ᵘʳ ⊩A) (emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩B)
  fundamental-⊩ᵛ (Idⱼ ⊢t ⊢u) =
    _ , Idᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ (univ ⊢A) =
    _ , ⊩ᵛ∷U→⊩ᵛ (fundamental-⊩ᵛ∷ ⊢A .proj₂)

  -- Fundamental theorem for type equality.
  fundamental-⊩ᵛ≡ : Γ ⊢ A ≡ B → Γ ⊩ᵛ A ≡ B
  fundamental-⊩ᵛ≡ (univ A≡B) =
    let a = ⊩ᵛ≡∷U→⊩ᵛ≡ (proj₂ (fundamental-⊩ᵛ≡∷ A≡B))
    in _ , a
  fundamental-⊩ᵛ≡ (refl ⊢A) =
    let [refl] = refl-⊩ᵛ≡ (proj₂ (fundamental-⊩ᵛ ⊢A))
    in _ , [refl]
  fundamental-⊩ᵛ≡ (sym A≡B) =
    let [sym] = sym-⊩ᵛ≡ (proj₂ (fundamental-⊩ᵛ≡ A≡B))
    in _ , [sym]
  fundamental-⊩ᵛ≡ (trans A≡B B≡C) =
    let l₁ , A≡B = fundamental-⊩ᵛ≡ A≡B
        l₂ , B≡C = fundamental-⊩ᵛ≡ B≡C
    in
    l₁ ⊔ᵘ l₂ , trans-⊩ᵛ≡ (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘʳ A≡B) (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘˡ B≡C)
  fundamental-⊩ᵛ≡ (ΠΣ-cong _ A₁≡A₂ B₁≡B₂ ok) =
    let l₁ , A₁≡A₂ = fundamental-⊩ᵛ≡ A₁≡A₂
        l₂ , B₁≡B₂ = fundamental-⊩ᵛ≡ B₁≡B₂
    in
    l₁ ⊔ᵘ l₂ , ΠΣ-congᵛ ok (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘʳ A₁≡A₂) (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘˡ B₁≡B₂)
  fundamental-⊩ᵛ≡ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
     _ , (Id-congᵛ (fundamental-⊩ᵛ≡ A₁≡A₂ .proj₂)
                   (proj₂ (fundamental-⊩ᵛ≡∷ t₁≡t₂))
                   (proj₂ (fundamental-⊩ᵛ≡∷ u₁≡u₂)))

  -- Fundamental theorem for terms.
  fundamental-⊩ᵛ∷ : Γ ⊢ t ∷ A → Γ ⊩ᵛ t ∷ A
  fundamental-⊩ᵛ∷ (ℕⱼ ⊢Γ) =
    1 , ℕᵗᵛ (valid ⊢Γ)
  fundamental-⊩ᵛ∷ (Emptyⱼ x) =
    1 , Emptyᵗᵛ (valid x)
  fundamental-⊩ᵛ∷ (Unitⱼ ⊢Γ ok) =
    _ , Unitᵗᵛ (valid ⊢Γ) ok
  fundamental-⊩ᵛ∷ (ΠΣⱼ ⊢A ⊢B ok) =
      _
    , ΠΣᵗᵛ ok (emb-⊩ᵛ∷ ≤ᵘ⊔ᵘʳ $ fundamental-⊩ᵛ∷ ⊢A .proj₂)
        (emb-⊩ᵛ∷ ≤ᵘ⊔ᵘˡ $ fundamental-⊩ᵛ∷ ⊢B .proj₂)
  fundamental-⊩ᵛ∷ (var ⊢Γ x∈Γ) =
    _ , varᵛ x∈Γ (valid ⊢Γ) .proj₂
  fundamental-⊩ᵛ∷ (lamⱼ ⊢A ⊢t ok) =
    let l₁ , ⊩t = fundamental-⊩ᵛ∷ ⊢t
        l₂ , ⊩A = fundamental-⊩ᵛ ⊢A
    in
    l₁ ⊔ᵘ l₂ , lamᵛ ok (emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩A) (emb-⊩ᵛ∷ ≤ᵘ⊔ᵘʳ ⊩t)
  fundamental-⊩ᵛ∷ (⊢t ∘ⱼ ⊢u) =
    let l₁ , ⊩t = fundamental-⊩ᵛ∷ ⊢t
        l₂ , ⊩u = fundamental-⊩ᵛ∷ ⊢u
    in
    l₁ ⊔ᵘ l₂ , ∘ᵛ (emb-⊩ᵛ∷ ≤ᵘ⊔ᵘʳ ⊩t) ⊩u
  fundamental-⊩ᵛ∷ (prodⱼ _ ⊢B ⊢t ⊢u ok) =
    let l₁ , ⊩t = fundamental-⊩ᵛ∷ ⊢t
        l₂ , ⊩B = fundamental-⊩ᵛ ⊢B
    in
      l₁ ⊔ᵘ l₂
    , prodᵛ ok (emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩B) (emb-⊩ᵛ∷ ≤ᵘ⊔ᵘʳ ⊩t)
        (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ∷ (fstⱼ _ _ ⊢t) =
    _ , fstᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (sndⱼ _ _ ⊢t) =
    _ , sndᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (zeroⱼ ⊢Γ) =
    0 , zeroᵛ (valid ⊢Γ)
  fundamental-⊩ᵛ∷ (sucⱼ ⊢t) =
    _ , sucᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (natrecⱼ ⊢A ⊢t ⊢u ⊢v) =
      _
    , natrecᵛ (fundamental-⊩ᵛ ⊢A .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂)
        (fundamental-⊩ᵛ∷ ⊢u .proj₂) (fundamental-⊩ᵛ∷ ⊢v .proj₂)
  fundamental-⊩ᵛ∷ (emptyrecⱼ ⊢A ⊢t) =
    let l , ⊩A = fundamental-⊩ᵛ ⊢A
        _ , ⊩t = fundamental-⊩ᵛ∷ ⊢t
    in
    l , emptyrecᵛ ⊩A ⊩t
  fundamental-⊩ᵛ∷ (starⱼ ⊢Γ ok) =
    _ , starᵛ (valid ⊢Γ) ok
  fundamental-⊩ᵛ∷ (conv ⊢t A≡B) =
    let l , A≡B = fundamental-⊩ᵛ≡ A≡B in
    l , conv-⊩ᵛ∷ A≡B (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (prodrecⱼ _ _ ⊢C ⊢t ⊢u _) =
    _ , prodrecᵛ (fundamental-⊩ᵛ ⊢C .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ∷ (unitrecⱼ ⊢A ⊢t ⊢u _) =
    _ , unitrecᵛ (fundamental-⊩ᵛ ⊢A .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      (proj₂ (fundamental-⊩ᵛ∷ ⊢u))
  fundamental-⊩ᵛ∷ (Idⱼ ⊢A ⊢t ⊢u) =
    _
    , Idᵗᵛ (fundamental-⊩ᵛ∷ ⊢A .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂)
        (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ∷ (rflⱼ ⊢t) =
    _ , rflᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (Jⱼ _ _ ⊢B ⊢u _ ⊢w) =
      _
    , Jᵛ (fundamental-⊩ᵛ ⊢B .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂)
        (fundamental-⊩ᵛ∷ ⊢w .proj₂)
  fundamental-⊩ᵛ∷ (Kⱼ _ ⊢B ⊢u ⊢v ok) =
      _
    , Kᵛ ok (fundamental-⊩ᵛ ⊢B .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂)
        (fundamental-⊩ᵛ∷ ⊢v .proj₂)
  fundamental-⊩ᵛ∷ ([]-congⱼ ⊢t ⊢u ⊢v ok) =
    _ , []-congᵛ ok (fundamental-⊩ᵛ∷ ⊢v .proj₂)
  fundamental-⊩ᵛ∷ (Uⱼ ⊢Γ) =
    _ , ⊩ᵛU∷U (valid ⊢Γ)

  -- Fundamental theorem for term equality.
  fundamental-⊩ᵛ≡∷ : Γ ⊢ t ≡ u ∷ A → Γ ⊩ᵛ t ≡ u ∷ A
  fundamental-⊩ᵛ≡∷ (refl ⊢t) =
    _ , refl-⊩ᵛ≡∷ (proj₂ (fundamental-⊩ᵛ∷ ⊢t))
  fundamental-⊩ᵛ≡∷ (sym t≡u) =
    _ , sym-⊩ᵛ≡∷ (proj₂ (fundamental-⊩ᵛ≡∷ t≡u))
  fundamental-⊩ᵛ≡∷ (trans t≡u u≡v) =
    let l , [u≡v] = fundamental-⊩ᵛ≡∷ u≡v
    in l , trans-⊩ᵛ≡∷ (proj₂ (fundamental-⊩ᵛ≡∷ t≡u)) [u≡v]
  fundamental-⊩ᵛ≡∷ (conv t≡u A≡B) =
    _ , conv-⊩ᵛ≡∷ (proj₂ (fundamental-⊩ᵛ≡ A≡B)) (proj₂ (fundamental-⊩ᵛ≡∷ t≡u))
  fundamental-⊩ᵛ≡∷ (ΠΣ-cong _ A₁≡A₂ B₁≡B₂ ok) =
      _
    , ΠΣ-congᵗᵛ ok (emb-⊩ᵛ≡∷ ≤ᵘ⊔ᵘʳ $ fundamental-⊩ᵛ≡∷ A₁≡A₂ .proj₂)
        (emb-⊩ᵛ≡∷ ≤ᵘ⊔ᵘˡ $ fundamental-⊩ᵛ≡∷ B₁≡B₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (app-cong t₁≡t₂ u₁≡u₂) =
    _ , ∘-congᵛ (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂) (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (β-red _ _ ⊢t ⊢u PE.refl ok) =
    _ , β-redᵛ ok (fundamental-⊩ᵛ∷ ⊢t .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ≡∷ (η-eq _ ⊢t₁ ⊢t₂ wk1-t₁∘0≡wk1-t₂∘0) =
    _ , η-eqᵛ (fundamental-⊩ᵛ∷ ⊢t₁ .proj₂) (fundamental-⊩ᵛ∷ ⊢t₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ wk1-t₁∘0≡wk1-t₂∘0 .proj₂)
  fundamental-⊩ᵛ≡∷ (suc-cong t≡u) =
    _ , suc-congᵛ (proj₂ (fundamental-⊩ᵛ≡∷ t≡u))
  fundamental-⊩ᵛ≡∷ (natrec-cong _ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) = _ ,
    natrec-congᵛ (proj₂ (fundamental-⊩ᵛ≡ A₁≡A₂)) (proj₂ (fundamental-⊩ᵛ≡∷ t₁≡t₂))
      (proj₂ (fundamental-⊩ᵛ≡∷ u₁≡u₂)) (proj₂ (fundamental-⊩ᵛ≡∷ v₁≡v₂))
  fundamental-⊩ᵛ≡∷ (natrec-zero ⊢A ⊢t ⊢u) = _ ,
    natrec-zeroᵛ (proj₂ (fundamental-⊩ᵛ ⊢A)) (proj₂ (fundamental-⊩ᵛ∷ ⊢t))
      (proj₂ (fundamental-⊩ᵛ∷ ⊢u))
  fundamental-⊩ᵛ≡∷ (natrec-suc ⊢A ⊢t ⊢u ⊢v) = _ ,
    natrec-sucᵛ (proj₂ (fundamental-⊩ᵛ ⊢A)) (proj₂ (fundamental-⊩ᵛ∷ ⊢t))
      (proj₂ (fundamental-⊩ᵛ∷ ⊢u)) (proj₂ (fundamental-⊩ᵛ∷ ⊢v))
  fundamental-⊩ᵛ≡∷ (emptyrec-cong F≡F′ n≡n′) = _ ,
    emptyrec-congᵛ (proj₂ (fundamental-⊩ᵛ≡ F≡F′)) (proj₂ (fundamental-⊩ᵛ≡∷ n≡n′))
  fundamental-⊩ᵛ≡∷ (η-unit ⊢t ⊢u η) = _ ,
    η-unitᵛ (proj₂ (fundamental-⊩ᵛ∷ ⊢t)) (proj₂ (fundamental-⊩ᵛ∷ ⊢u)) η
  fundamental-⊩ᵛ≡∷ (fst-cong _ _ t₁≡t₂) =
    _ , fst-congᵛ (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (snd-cong _ _ t₁≡t₂) =
    _ , snd-congᵛ (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (prod-cong _ ⊢B t₁≡t₂ u₁≡u₂ ok) =
    let l₁ , t₁≡t₂ = fundamental-⊩ᵛ≡∷ t₁≡t₂
        l₂ , ⊩B    = fundamental-⊩ᵛ ⊢B
    in
      l₁ ⊔ᵘ l₂
    , prod-congᵛ ok (emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩B) (emb-⊩ᵛ≡∷ ≤ᵘ⊔ᵘʳ t₁≡t₂)
        (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (Σ-β₁ _ ⊢B ⊢t ⊢u PE.refl ok) =
    _ , Σ-β₁ᵛ ok (fundamental-⊩ᵛ ⊢B .proj₂)
      (fundamental-⊩ᵛ∷ ⊢t .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ≡∷ (Σ-β₂ _ ⊢B ⊢t ⊢u PE.refl ok) =
    _ , Σ-β₂ᵛ ok (fundamental-⊩ᵛ ⊢B .proj₂)
      (fundamental-⊩ᵛ∷ ⊢t .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ≡∷ (Σ-η _ _ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂) =
    _ , Σ-ηᵛ (fundamental-⊩ᵛ∷ ⊢t₁ .proj₂) (fundamental-⊩ᵛ∷ ⊢t₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ fst-t₁≡fst-t₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ snd-t₁≡snd-t₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (prodrec-cong _ _ C₁≡C₂ t₁≡t₂ u₁≡u₂ _) =
    _ , prodrec-congᵛ (fundamental-⊩ᵛ≡ C₁≡C₂ .proj₂) (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (prodrec-β _ _ ⊢C ⊢t ⊢u ⊢v PE.refl _) =
    _ , prodrec-βᵛ (fundamental-⊩ᵛ ⊢C .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      (fundamental-⊩ᵛ∷ ⊢u .proj₂) (fundamental-⊩ᵛ∷ ⊢v .proj₂)
  fundamental-⊩ᵛ≡∷ (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ _ _) = _ ,
    unitrec-congᵛ (proj₂ (fundamental-⊩ᵛ≡ A₁≡A₂)) (proj₂ (fundamental-⊩ᵛ≡∷ t₁≡t₂))
      (proj₂ (fundamental-⊩ᵛ≡∷ u₁≡u₂))
  fundamental-⊩ᵛ≡∷ (unitrec-β ⊢A ⊢u _ no-η) = _ ,
    unitrec-βᵛ (proj₂ (fundamental-⊩ᵛ ⊢A)) (proj₂ (fundamental-⊩ᵛ∷ ⊢u)) no-η
  fundamental-⊩ᵛ≡∷ (unitrec-β-η ⊢A ⊢t ⊢u _ η) =
    _ , unitrec-β-ηᵛ (fundamental-⊩ᵛ ⊢A .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      (fundamental-⊩ᵛ∷ ⊢u .proj₂) η
  fundamental-⊩ᵛ≡∷ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    _ , Id-congᵗᵛ (proj₂ (fundamental-⊩ᵛ≡∷ A₁≡A₂)) (proj₂ (fundamental-⊩ᵛ≡∷ t₁≡t₂))
      (proj₂ (fundamental-⊩ᵛ≡∷ u₁≡u₂))
  fundamental-⊩ᵛ≡∷ (J-cong _ A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) = _ ,
    J-congᵛ (proj₂ (fundamental-⊩ᵛ≡ A₁≡A₂)) (proj₂ (fundamental-⊩ᵛ≡∷ t₁≡t₂))
      (proj₂ (fundamental-⊩ᵛ≡ B₁≡B₂)) (proj₂ (fundamental-⊩ᵛ≡∷ u₁≡u₂))
      (proj₂ (fundamental-⊩ᵛ≡∷ v₁≡v₂)) (proj₂ (fundamental-⊩ᵛ≡∷ w₁≡w₂))
  fundamental-⊩ᵛ≡∷ (K-cong A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) = _ ,
    K-congᵛ ok (proj₂ (fundamental-⊩ᵛ≡ A₁≡A₂)) (proj₂ (fundamental-⊩ᵛ≡∷ t₁≡t₂))
      (proj₂ (fundamental-⊩ᵛ≡ B₁≡B₂)) (proj₂ (fundamental-⊩ᵛ≡∷ u₁≡u₂))
      (proj₂ (fundamental-⊩ᵛ≡∷ v₁≡v₂))
  fundamental-⊩ᵛ≡∷ ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) = _ ,
    []-cong-congᵛ ok (proj₂ (fundamental-⊩ᵛ≡ A₁≡A₂)) (proj₂ (fundamental-⊩ᵛ≡∷ t₁≡t₂))
      (proj₂ (fundamental-⊩ᵛ≡∷ u₁≡u₂)) (proj₂ (fundamental-⊩ᵛ≡∷ v₁≡v₂))
  fundamental-⊩ᵛ≡∷ (J-β _ ⊢t ⊢B ⊢u PE.refl) = _ ,
    J-βᵛ (proj₂ (fundamental-⊩ᵛ∷ ⊢t)) (proj₂ (fundamental-⊩ᵛ ⊢B))
    (proj₂ (fundamental-⊩ᵛ∷ ⊢u))
  fundamental-⊩ᵛ≡∷ (K-β _ ⊢B ⊢u ok) = _ ,
    K-βᵛ ok (proj₂ (fundamental-⊩ᵛ ⊢B)) (proj₂ (fundamental-⊩ᵛ∷ ⊢u))
  fundamental-⊩ᵛ≡∷ ([]-cong-β ⊢t PE.refl ok) = _ ,
    []-cong-βᵛ ok (proj₂ (fundamental-⊩ᵛ∷ ⊢t))

opaque

  -- Fundamental theorem for substitutions.

  fundamental-⊩ˢ∷ : ⊢ Δ → ⊢ Γ → Δ ⊢ˢ σ ∷ Γ → Δ ⊩ˢ σ ∷ Γ
  fundamental-⊩ˢ∷ ⊢Δ ε _ =
    ⊩ˢ∷ε⇔ .proj₂ ⊢Δ
  fundamental-⊩ˢ∷ ⊢Δ (⊢Γ ∙ ⊢A) (⊢tail , ⊢head) =
    ⊩ˢ∷∙⇔′ .proj₂
      ( (_ , fundamental-⊩ᵛ ⊢A .proj₂)
      , (_ , ⊩ᵛ∷→⊩∷ (fundamental-⊩ᵛ∷ ⊢head .proj₂))
      , fundamental-⊩ˢ∷ ⊢Δ ⊢Γ ⊢tail
      )

opaque

  -- Fundamental theorem for substitution equality.

  fundamental-⊩ˢ≡∷ : ⊢ Δ → ⊢ Γ → Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ
  fundamental-⊩ˢ≡∷ ⊢Δ ε _ =
    ⊩ˢ≡∷ε⇔ .proj₂ ⊢Δ
  fundamental-⊩ˢ≡∷ ⊢Δ (⊢Γ ∙ ⊢A) (tail≡tail , head≡head) =
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( (_ , fundamental-⊩ᵛ ⊢A .proj₂)
      , (_ , ⊩ᵛ≡∷→⊩≡∷ (fundamental-⊩ᵛ≡∷ head≡head .proj₂))
      , fundamental-⊩ˢ≡∷ ⊢Δ ⊢Γ tail≡tail
      )
