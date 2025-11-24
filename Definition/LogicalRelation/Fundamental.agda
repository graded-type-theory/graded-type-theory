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
import Definition.Untyped.Erased 𝕄 as E
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation.Substitution R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution.Introductions R ⦃ eqrel ⦄

open import Tools.Product
open import Tools.Nat using (Nat)
import Tools.PropositionalEquality as PE
open import Tools.Sum

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
  valid ε      = ⊩ᵛε⇔ .proj₂ _
  valid (∙ ⊢A) = ⊩ᵛ-∙-intro (fundamental-⊩ᵛ ⊢A .proj₂)


  -- Fundamental theorem for types.
  fundamental-⊩ᵛ : Γ ⊢ A → ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A
  fundamental-⊩ᵛ (Levelⱼ ok ⊢Γ) =
    0ᵘ , Levelᵛ (Level-allowed⇔⊎ .proj₂ (inj₂ ok)) (valid ⊢Γ)
  fundamental-⊩ᵛ (Liftⱼ ⊢l ⊢A) =
    _ , Liftᵛ (fundamental-⊩ᵛ∷L ⊢l .proj₂) (fundamental-⊩ᵛ ⊢A .proj₂)
  fundamental-⊩ᵛ ⊢ΠΣ@(ΠΣⱼ ⊢B _) =
    let _ , ⊩B = fundamental-⊩ᵛ ⊢B
        _ , ⊩A = wf-∙-⊩ᵛ ⊩B
    in
    _ , ΠΣᵛ ⊢ΠΣ (emb-⊩ᵛ ≤ᵘ⊔ᵘʳ ⊩A) (emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩B)
  fundamental-⊩ᵛ (Idⱼ _ ⊢t ⊢u) =
    _ , Idᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ (univ ⊢A) =
    _ , ⊩ᵛ∷U→⊩ᵛ (fundamental-⊩ᵛ∷ ⊢A .proj₂)

  -- Fundamental theorem for type equality.
  fundamental-⊩ᵛ≡ : Γ ⊢ A ≡ B → ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A ≡ B
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
  fundamental-⊩ᵛ≡ (U-cong l₁≡l₂) =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≡l₂ .proj₁) in
    _ , ⊩ᵛU≡U ok (fundamental-⊩ᵛ≡∷ l₁≡l₂ .proj₂)
  fundamental-⊩ᵛ≡ (Lift-cong l₁≡l₂ A≡B) =
    _ ,
    Lift-congᵛ (fundamental-⊩ᵛ≡∷L l₁≡l₂ .proj₂)
      (fundamental-⊩ᵛ≡ A≡B .proj₂)
  fundamental-⊩ᵛ≡ ΠΣ≡ΠΣ@(ΠΣ-cong A₁≡A₂ B₁≡B₂ _) =
    let l₁ , A₁≡A₂ = fundamental-⊩ᵛ≡ A₁≡A₂
        l₂ , B₁≡B₂ = fundamental-⊩ᵛ≡ B₁≡B₂
    in
    l₁ ⊔ᵘ l₂ ,
    ΠΣ-congᵛ ΠΣ≡ΠΣ (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘʳ A₁≡A₂) (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘˡ B₁≡B₂)
  fundamental-⊩ᵛ≡ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
     _ , (Id-congᵛ (fundamental-⊩ᵛ≡ A₁≡A₂ .proj₂)
                   (proj₂ (fundamental-⊩ᵛ≡∷ t₁≡t₂))
                   (proj₂ (fundamental-⊩ᵛ≡∷ u₁≡u₂)))

  -- Fundamental theorem for terms.
  fundamental-⊩ᵛ∷ : Γ ⊢ t ∷ A → ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ t ∷ A
  fundamental-⊩ᵛ∷ (Levelⱼ ⊢Γ ok) =
    _ , Levelᵗᵛ (valid ⊢Γ) ok
  fundamental-⊩ᵛ∷ (zeroᵘⱼ ok ⊢Γ) =
    0ᵘ , zeroᵘᵛ ok (valid ⊢Γ)
  fundamental-⊩ᵛ∷ (sucᵘⱼ ⊢l) =
    let ok = inversion-Level-⊢ (wf-⊢∷ ⊢l) in
    _ , sucᵘᵛ ok (fundamental-⊩ᵛ∷ ⊢l .proj₂)
  fundamental-⊩ᵛ∷ (supᵘⱼ ⊢l₁ ⊢l₂) =
    _ , supᵘᵛ (fundamental-⊩ᵛ∷ ⊢l₁ .proj₂) (fundamental-⊩ᵛ∷ ⊢l₂ .proj₂)
  fundamental-⊩ᵛ∷ (Liftⱼ ⊢l₁ ⊢l₂ ⊢A) =
    _ ,
    Liftᵗᵛ
      (fundamental-⊩ᵛ∷L ⊢l₁ .proj₂)
      (fundamental-⊩ᵛ∷L ⊢l₂ .proj₂)
      (fundamental-⊩ᵛ∷ ⊢A .proj₂)
  fundamental-⊩ᵛ∷ (liftⱼ ⊢l₂ ⊢A ⊢t) =
    _ ,
    liftᵛ
      (fundamental-⊩ᵛ∷L ⊢l₂ .proj₂)
      (fundamental-⊩ᵛ ⊢A .proj₂)
      (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (lowerⱼ ⊢t) =
    _ , lowerᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (ℕⱼ ⊢Γ) =
    _ , ℕᵗᵛ (valid ⊢Γ)
  fundamental-⊩ᵛ∷ (Emptyⱼ x) =
    _ , Emptyᵗᵛ (valid x)
  fundamental-⊩ᵛ∷ (Unitⱼ ⊢Γ ok) =
    _ , Unitᵗᵛ (valid ⊢Γ) ok
  fundamental-⊩ᵛ∷ ⊢ΠΣ@(ΠΣⱼ ⊢l ⊢A ⊢B _) =
    _ ,
    ΠΣᵗᵛ ⊢ΠΣ (fundamental-⊩ᵛ∷L ⊢l .proj₂)
      (fundamental-⊩ᵛ∷ ⊢A .proj₂) (fundamental-⊩ᵛ∷ ⊢B .proj₂)
  fundamental-⊩ᵛ∷ (var ⊢Γ x∈Γ) =
    _ , varᵛ x∈Γ (valid ⊢Γ) .proj₂
  fundamental-⊩ᵛ∷ (lamⱼ _ ⊢t ok) =
    let l₁ , ⊩t = fundamental-⊩ᵛ∷ ⊢t
        l₂ , ⊩A = wf-∙-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
    in
    l₁ ⊔ᵘ l₂ , lamᵛ ok ⊢t (emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩A) (emb-⊩ᵛ∷ ≤ᵘ⊔ᵘʳ ⊩t)
  fundamental-⊩ᵛ∷ (⊢t ∘ⱼ ⊢u) =
    let l₁ , ⊩t = fundamental-⊩ᵛ∷ ⊢t
        l₂ , ⊩u = fundamental-⊩ᵛ∷ ⊢u
    in
    l₁ ⊔ᵘ l₂ , ∘ᵛ (emb-⊩ᵛ∷ ≤ᵘ⊔ᵘʳ ⊩t) ⊩u
  fundamental-⊩ᵛ∷ (prodⱼ ⊢B ⊢t ⊢u ok) =
    let l₁ , ⊩t = fundamental-⊩ᵛ∷ ⊢t
        l₂ , ⊩B = fundamental-⊩ᵛ ⊢B
    in
      l₁ ⊔ᵘ l₂
    , prodᵛ ok ⊢B (emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩B) (emb-⊩ᵛ∷ ≤ᵘ⊔ᵘʳ ⊩t)
        (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ∷ (fstⱼ _ ⊢t) =
    _ , fstᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (sndⱼ _ ⊢t) =
    _ , sndᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (zeroⱼ ⊢Γ) =
    0ᵘ , zeroᵛ (valid ⊢Γ)
  fundamental-⊩ᵛ∷ (sucⱼ ⊢t) =
    _ , sucᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (natrecⱼ ⊢t ⊢u ⊢v) =
    let _ , ⊩u = fundamental-⊩ᵛ∷ ⊢u in
    _ ,
    natrecᵛ (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ ⊩u) .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂) ⊢u
      ⊩u (fundamental-⊩ᵛ∷ ⊢v .proj₂)
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
  fundamental-⊩ᵛ∷ (prodrecⱼ ⊢C ⊢t ⊢u _) =
    _ ,
    prodrecᵛ ⊢C (fundamental-⊩ᵛ ⊢C .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      ⊢u (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ∷ (unitrecⱼ ⊢A ⊢t ⊢u _) =
    _ ,
    unitrecᵛ ⊢A (fundamental-⊩ᵛ ⊢A .proj₂)
      (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ∷ (Idⱼ ⊢A ⊢t ⊢u) =
    _
    , Idᵗᵛ (fundamental-⊩ᵛ∷ ⊢A .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂)
        (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ∷ (rflⱼ ⊢t) =
    _ , rflᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷ (Jⱼ _ ⊢B ⊢u _ ⊢w) =
      _
    , Jᵛ ⊢B (fundamental-⊩ᵛ ⊢B .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂)
        (fundamental-⊩ᵛ∷ ⊢w .proj₂)
  fundamental-⊩ᵛ∷ (Kⱼ ⊢B ⊢u ⊢v ok) =
      _
    , Kᵛ ok ⊢B (fundamental-⊩ᵛ ⊢B .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂)
        (fundamental-⊩ᵛ∷ ⊢v .proj₂)
  fundamental-⊩ᵛ∷ ([]-congⱼ ⊢l _ _ _ ⊢v ok) =
    _ ,
    []-congᵛ ok (fundamental-⊩ᵛ∷L ⊢l .proj₂) (fundamental-⊩ᵛ∷ ⊢v .proj₂)
  fundamental-⊩ᵛ∷ (Uⱼ ⊢l) =
    _ , ⊩ᵛU∷U (fundamental-⊩ᵛ∷L ⊢l .proj₂)

  -- The fundamental theorem for levels.
  fundamental-⊩ᵛ∷L : Γ ⊢ t ∷Level → ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ t ∷Level
  fundamental-⊩ᵛ∷L (term ok ⊢t) =
    _ , term-⊩ᵛ∷L ok (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ∷L (literal not-ok ⊢Γ t-lit) =
    0ᵘ , literal-⊩ᵛ∷L not-ok (valid ⊢Γ) t-lit

  -- Fundamental theorem for term equality.
  fundamental-⊩ᵛ≡∷ : Γ ⊢ t ≡ u ∷ A → ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A
  fundamental-⊩ᵛ≡∷ (refl ⊢t) =
    _ , refl-⊩ᵛ≡∷ (proj₂ (fundamental-⊩ᵛ∷ ⊢t))
  fundamental-⊩ᵛ≡∷ (sym _ t≡u) =
    _ , sym-⊩ᵛ≡∷ (proj₂ (fundamental-⊩ᵛ≡∷ t≡u))
  fundamental-⊩ᵛ≡∷ (trans t≡u u≡v) =
    let l , [u≡v] = fundamental-⊩ᵛ≡∷ u≡v
    in l , trans-⊩ᵛ≡∷ (proj₂ (fundamental-⊩ᵛ≡∷ t≡u)) [u≡v]
  fundamental-⊩ᵛ≡∷ (conv t≡u A≡B) =
    _ , conv-⊩ᵛ≡∷ (proj₂ (fundamental-⊩ᵛ≡ A≡B)) (proj₂ (fundamental-⊩ᵛ≡∷ t≡u))
  fundamental-⊩ᵛ≡∷ (sucᵘ-cong l₁≡l₂) =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≡l₂ .proj₁) in
    _ , sucᵘ-congᵛ ok (fundamental-⊩ᵛ≡∷ l₁≡l₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (supᵘ-cong l₁≡l₂ l₃≡l₄) =
    _ , supᵘ-congᵛ (fundamental-⊩ᵛ≡∷ l₁≡l₂ .proj₂) (fundamental-⊩ᵛ≡∷ l₃≡l₄ .proj₂)
  fundamental-⊩ᵛ≡∷ (supᵘ-zeroˡ ⊢l) =
    _ , supᵘ-zeroˡᵛ (fundamental-⊩ᵛ∷ ⊢l .proj₂)
  fundamental-⊩ᵛ≡∷ (supᵘ-sucᵘ ⊢l₁ ⊢l₂) =
    _ , supᵘ-sucᵘᵛ (fundamental-⊩ᵛ∷ ⊢l₁ .proj₂) (fundamental-⊩ᵛ∷ ⊢l₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (supᵘ-assoc ⊢l₁ ⊢l₂ ⊢l₃) =
    _ , supᵘ-assocᵛ
      (fundamental-⊩ᵛ∷ ⊢l₁ .proj₂)
      (fundamental-⊩ᵛ∷ ⊢l₂ .proj₂)
      (fundamental-⊩ᵛ∷ ⊢l₃ .proj₂)
  fundamental-⊩ᵛ≡∷ (supᵘ-comm ⊢l₁ ⊢l₂) =
    _ , supᵘ-commᵛ (fundamental-⊩ᵛ∷ ⊢l₁ .proj₂) (fundamental-⊩ᵛ∷ ⊢l₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (supᵘ-idem ⊢l) =
    _ , supᵘ-idemᵛ (fundamental-⊩ᵛ∷ ⊢l .proj₂)
  fundamental-⊩ᵛ≡∷ (supᵘ-sub ⊢l) =
    _ , supᵘ-subᵛ (fundamental-⊩ᵛ∷ ⊢l .proj₂)
  fundamental-⊩ᵛ≡∷ (U-cong l₁≡l₂) =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≡l₂ .proj₁) in
    _ , ⊩ᵛU≡U∷U ok (fundamental-⊩ᵛ≡∷ l₁≡l₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (Lift-cong ⊢l₁ _ l₂≡l₂′ A≡B) =
    _ ,
    Lift-congᵗᵛ
      (fundamental-⊩ᵛ∷L ⊢l₁ .proj₂)
      (fundamental-⊩ᵛ≡∷L l₂≡l₂′ .proj₂)
      (fundamental-⊩ᵛ≡∷ A≡B .proj₂)
  fundamental-⊩ᵛ≡∷ (lower-cong t≡u) = _ , lower-congᵛ (fundamental-⊩ᵛ≡∷ t≡u .proj₂)
  fundamental-⊩ᵛ≡∷ (Lift-β ⊢A ⊢u) =
    _ , Lift-βᵛ
      (fundamental-⊩ᵛ ⊢A .proj₂)
      (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ≡∷ (Lift-η ⊢l₂ ⊢A ⊢t ⊢u t≡u) =
    _ ,
    Lift-ηᵛ
      (fundamental-⊩ᵛ∷L ⊢l₂ .proj₂)
      (fundamental-⊩ᵛ ⊢A .proj₂)
      (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      (fundamental-⊩ᵛ∷ ⊢u .proj₂)
      (fundamental-⊩ᵛ≡∷ t≡u .proj₂)
  fundamental-⊩ᵛ≡∷ ΠΣ≡ΠΣ@(ΠΣ-cong ⊢l A₁≡A₂ B₁≡B₂ ok) =
      _
    , ΠΣ-congᵗᵛ ΠΣ≡ΠΣ
        (fundamental-⊩ᵛ∷L ⊢l .proj₂)
        (fundamental-⊩ᵛ≡∷ A₁≡A₂ .proj₂)
        (fundamental-⊩ᵛ≡∷ B₁≡B₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (app-cong t₁≡t₂ u₁≡u₂) =
    _ , ∘-congᵛ (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂) (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (β-red _ ⊢t ⊢u PE.refl ok) =
    _ ,
    β-redᵛ ok ⊢t (fundamental-⊩ᵛ∷ ⊢t .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ≡∷ (η-eq _ ⊢t₁ ⊢t₂ wk1-t₁∘0≡wk1-t₂∘0 _) =
    _ ,
    η-eqᵛ ⊢t₁ (fundamental-⊩ᵛ∷ ⊢t₁ .proj₂) ⊢t₂
      (fundamental-⊩ᵛ∷ ⊢t₂ .proj₂) wk1-t₁∘0≡wk1-t₂∘0
      (fundamental-⊩ᵛ≡∷ wk1-t₁∘0≡wk1-t₂∘0 .proj₂)
  fundamental-⊩ᵛ≡∷ (suc-cong t≡u) =
    _ , suc-congᵛ (proj₂ (fundamental-⊩ᵛ≡∷ t≡u))
  fundamental-⊩ᵛ≡∷ (natrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) =
    _ ,
    natrec-congᵛ A₁≡A₂ (fundamental-⊩ᵛ≡ A₁≡A₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂) u₁≡u₂
      (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂) (fundamental-⊩ᵛ≡∷ v₁≡v₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (natrec-zero ⊢t ⊢u) =
    _ ,
    natrec-zeroᵛ (fundamental-⊩ᵛ∷ ⊢t .proj₂) ⊢u
  fundamental-⊩ᵛ≡∷ (natrec-suc ⊢t ⊢u ⊢v) =
    let _ , ⊩u = fundamental-⊩ᵛ∷ ⊢u in
    _ ,
    natrec-sucᵛ (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ ⊩u) .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      ⊢u ⊩u (fundamental-⊩ᵛ∷ ⊢v .proj₂)
  fundamental-⊩ᵛ≡∷ (emptyrec-cong F≡F′ n≡n′) = _ ,
    emptyrec-congᵛ (proj₂ (fundamental-⊩ᵛ≡ F≡F′)) (proj₂ (fundamental-⊩ᵛ≡∷ n≡n′))
  fundamental-⊩ᵛ≡∷ (η-unit ⊢t ⊢u ok η) = _ ,
    η-unitᵛ (proj₂ (fundamental-⊩ᵛ∷ ⊢t)) (proj₂ (fundamental-⊩ᵛ∷ ⊢u)) η
  fundamental-⊩ᵛ≡∷ (fst-cong _ t₁≡t₂) =
    _ , fst-congᵛ (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (snd-cong _ t₁≡t₂) =
    _ , snd-congᵛ (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (prod-cong ⊢B t₁≡t₂ u₁≡u₂ ok) =
    let l₁ , t₁≡t₂ = fundamental-⊩ᵛ≡∷ t₁≡t₂
        l₂ , ⊩B    = fundamental-⊩ᵛ ⊢B
    in
      l₁ ⊔ᵘ l₂
    , prod-congᵛ ok ⊢B (emb-⊩ᵛ ≤ᵘ⊔ᵘˡ ⊩B) (emb-⊩ᵛ≡∷ ≤ᵘ⊔ᵘʳ t₁≡t₂)
        (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (Σ-β₁ ⊢B ⊢t ⊢u PE.refl ok) =
    _ , Σ-β₁ᵛ ok ⊢B (fundamental-⊩ᵛ∷ ⊢t .proj₂) ⊢u
  fundamental-⊩ᵛ≡∷ (Σ-β₂ ⊢B ⊢t ⊢u PE.refl ok) =
    _ ,
    Σ-β₂ᵛ ok ⊢B (fundamental-⊩ᵛ ⊢B .proj₂) (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      ⊢u (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ≡∷ (Σ-η _ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂ _) =
    _ , Σ-ηᵛ (fundamental-⊩ᵛ∷ ⊢t₁ .proj₂) (fundamental-⊩ᵛ∷ ⊢t₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ fst-t₁≡fst-t₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ snd-t₁≡snd-t₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (prodrec-cong C₁≡C₂ t₁≡t₂ u₁≡u₂ _) =
    _ ,
    prodrec-congᵛ C₁≡C₂ (fundamental-⊩ᵛ≡ C₁≡C₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂) u₁≡u₂
      (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (prodrec-β ⊢C ⊢t ⊢u ⊢v PE.refl _) =
    _ ,
    prodrec-βᵛ ⊢C (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      (fundamental-⊩ᵛ∷ ⊢u .proj₂) ⊢v (fundamental-⊩ᵛ∷ ⊢v .proj₂)
  fundamental-⊩ᵛ≡∷ (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ _ _) =
    _ ,
    unitrec-congᵛ A₁≡A₂
      (fundamental-⊩ᵛ≡ A₁≡A₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂) (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (unitrec-β ⊢A ⊢t _ no-η) =
    _ ,
    unitrec-βᵛ ⊢A
      (fundamental-⊩ᵛ ⊢A .proj₂)
      (fundamental-⊩ᵛ∷ ⊢t .proj₂)
      no-η
  fundamental-⊩ᵛ≡∷ (unitrec-β-η ⊢A ⊢t ⊢u _ η) =
    _ ,
    unitrec-β-ηᵛ ⊢A
      (fundamental-⊩ᵛ ⊢A .proj₂)
      (fundamental-⊩ᵛ∷ ⊢t .proj₂) (fundamental-⊩ᵛ∷ ⊢u .proj₂) η
  fundamental-⊩ᵛ≡∷ (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    _ , Id-congᵗᵛ (proj₂ (fundamental-⊩ᵛ≡∷ A₁≡A₂)) (proj₂ (fundamental-⊩ᵛ≡∷ t₁≡t₂))
      (proj₂ (fundamental-⊩ᵛ≡∷ u₁≡u₂))
  fundamental-⊩ᵛ≡∷ (J-cong A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) =
    _ ,
    J-congᵛ (fundamental-⊩ᵛ≡ A₁≡A₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂) B₁≡B₂
      (fundamental-⊩ᵛ≡ B₁≡B₂ .proj₂) (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ v₁≡v₂ .proj₂) (fundamental-⊩ᵛ≡∷ w₁≡w₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) =
    _ ,
    K-congᵛ ok (fundamental-⊩ᵛ≡ A₁≡A₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂) B₁≡B₂
      (fundamental-⊩ᵛ≡ B₁≡B₂ .proj₂) (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ v₁≡v₂ .proj₂)
  fundamental-⊩ᵛ≡∷ ([]-cong-cong l₁≡l₂ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) =
    _ ,
    []-cong-congᵛ ok (fundamental-⊩ᵛ≡∷L l₁≡l₂ .proj₂)
      (fundamental-⊩ᵛ≡ A₁≡A₂ .proj₂) (fundamental-⊩ᵛ≡∷ t₁≡t₂ .proj₂)
      (fundamental-⊩ᵛ≡∷ u₁≡u₂ .proj₂) (fundamental-⊩ᵛ≡∷ v₁≡v₂ .proj₂)
  fundamental-⊩ᵛ≡∷ (J-β ⊢t ⊢B ⊢u PE.refl) =
    _ , J-βᵛ ⊢t ⊢B (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ≡∷ (K-β ⊢B ⊢u ok) =
    _ , K-βᵛ ok ⊢B (fundamental-⊩ᵛ∷ ⊢u .proj₂)
  fundamental-⊩ᵛ≡∷ ([]-cong-β ⊢l ⊢t PE.refl ok) =
    _ ,
    []-cong-βᵛ ok (fundamental-⊩ᵛ∷L ⊢l .proj₂)
      (fundamental-⊩ᵛ∷ ⊢t .proj₂)
  fundamental-⊩ᵛ≡∷ (equality-reflection ok _ ⊢v) =
    _ , equality-reflectionᵛ ok (fundamental-⊩ᵛ∷ ⊢v .proj₂)

  -- The fundamental theorem for level equality.
  fundamental-⊩ᵛ≡∷L : Γ ⊢ t ≡ u ∷Level → ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷Level
  fundamental-⊩ᵛ≡∷L (term ok t≡u) =
    _ , term ok (fundamental-⊩ᵛ≡∷ t≡u .proj₂)
  fundamental-⊩ᵛ≡∷L (literal not-ok ⊢Γ t-lit) =
    0ᵘ , literal! not-ok (valid ⊢Γ) t-lit

opaque

  -- Fundamental theorem for substitutions.

  fundamental-⊩ˢ∷ : ⊢ Γ → Δ ⊢ˢʷ σ ∷ Γ → Δ ⊩ˢ σ ∷ Γ
  fundamental-⊩ˢ∷ ε ⊢σ =
    ⊩ˢ∷ε⇔ .proj₂ (⊢ˢʷ∷ε⇔ .proj₁ ⊢σ)
  fundamental-⊩ˢ∷ (∙ ⊢A) ⊢σ =
    let ⊢σ₊ , ⊢σ₀ = ⊢ˢʷ∷∙⇔ .proj₁ ⊢σ in
    ⊩ˢ∷∙⇔′ .proj₂
      ( (_ , fundamental-⊩ᵛ ⊢A .proj₂)
      , (_ , ⊩ᵛ∷→⊩∷ (fundamental-⊩ᵛ∷ ⊢σ₀ .proj₂))
      , fundamental-⊩ˢ∷ (wf ⊢A) ⊢σ₊
      )

opaque

  -- Fundamental theorem for substitution equality.

  fundamental-⊩ˢ≡∷ : ⊢ Γ → Δ ⊢ˢʷ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ
  fundamental-⊩ˢ≡∷ ε σ₁≡σ₂ =
    ⊩ˢ≡∷ε⇔ .proj₂ (⊢ˢʷ≡∷ε⇔ .proj₁ σ₁≡σ₂)
  fundamental-⊩ˢ≡∷ (∙ ⊢A) σ₁≡σ₂ =
    let σ₁₊≡σ₂₊ , _ , _ , σ₁₀≡σ₂₀ = ⊢ˢʷ≡∷∙⇔ .proj₁ σ₁≡σ₂ in
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( (_ , fundamental-⊩ᵛ ⊢A .proj₂)
      , (_ , ⊩ᵛ≡∷→⊩≡∷ (fundamental-⊩ᵛ≡∷ σ₁₀≡σ₂₀ .proj₂))
      , fundamental-⊩ˢ≡∷ (wf ⊢A) σ₁₊≡σ₂₊
      )
