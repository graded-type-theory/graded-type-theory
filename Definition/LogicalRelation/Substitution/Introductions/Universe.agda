------------------------------------------------------------------------
-- Validity of the universe type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Hidden.Levels R as L
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product as Σ
open import Tools.Empty
import Tools.PropositionalEquality as PE

private
  variable
    n       : Nat
    Γ       : Con Term n
    A B     : Term n
    l l′ l″ : Universe-level
    k       : LogRelKit

------------------------------------------------------------------------
-- Some characterisation lemmas

private

  -- A lemma used below.

  U⇒*U→≡ : Γ ⊢ U l :⇒*: U l′ → l PE.≡ l′
  U⇒*U→≡ {Γ} {l} {l′} =
    Γ ⊢ U l :⇒*: U l′ →⟨ red ⟩
    Γ ⊢ U l ⇒* U l′   →⟨ flip whnfRed* Uₙ ⟩
    U l PE.≡ U l′     →⟨ (λ { PE.refl → PE.refl }) ⟩
    l PE.≡ l′         □

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩⟨⟩U⇔ :
    Γ ⊩⟨ l′ ⟩ U l ⇔
    (l <ᵘ l′ × ⊢ Γ)
  ⊩⟨⟩U⇔ =
      lemma ∘→ U-elim
    , (λ (l<l′ , ⊢Γ) → Uᵣ (Uᵣ _ l<l′ (idRed:*: (Uⱼ ⊢Γ))))
    where
    lemma :
      Γ ⊩⟨ l′ ⟩U U l →
      l <ᵘ l′ × ⊢ Γ
    lemma (noemb (Uᵣ _ l<l′ U⇒*U@([ ⊢U , _ , _ ]))) =
      case U⇒*U→≡ U⇒*U of λ {
        PE.refl →
      l<l′ , wf ⊢U }
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map ≤ᵘ-step idᶠ (lemma ⊩U)
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map ≤ᵘ-step idᶠ (lemma (emb p ⊩U))

opaque
  unfolding _⊩_

  -- A characterisation lemma for _⊩_.

  ⊩U⇔ : Γ ⊩ U l ⇔ ⊢ Γ
  ⊩U⇔ {Γ} {l} =
    Γ ⊩ U l                   ⇔⟨ id⇔ ⟩
    (∃ λ l′ → Γ ⊩⟨ l′ ⟩ U l)  ⇔⟨ (Σ-cong-⇔ λ _ → ⊩⟨⟩U⇔) ⟩
    (∃ λ l′ → l <ᵘ l′ × ⊢ Γ)  ⇔⟨ proj₂ ∘→ proj₂ , (λ ⊢Γ → 1+ l , ≤ᵘ-refl , ⊢Γ) ⟩
    ⊢ Γ                       □⇔

opaque
  unfolding _⊩_∷_

  -- A characterisation lemma for _⊩_∷_.

  ⊩∷U⇔ :
    Γ ⊩ A ∷ U l ⇔
    (Γ ⊩⟨ l ⟩ A × ∃ λ B → Γ ⊢ A :⇒*: B ∷ U l × Type B × Γ ⊢ B ≅ B ∷ U l)
  ⊩∷U⇔ {l} =
      (λ (_ , ⊩U , ⊩A) →
         lemma (U-elim ⊩U) (irrelevanceTerm ⊩U (U-intr (U-elim ⊩U)) ⊩A))
    , (λ (⊩A , B , A⇒*B , B-type , B≅B) →
           1+ l
         , Uᵣ (Uᵣ _ ≤ᵘ-refl (idRed:*: (Uⱼ (wfTerm (⊢t-redₜ A⇒*B)))))
         , Uₜ B A⇒*B B-type B≅B ⊩A)
    where
    lemma :
      (⊩U : Γ ⊩⟨ l′ ⟩U U l) →
      Γ ⊩⟨ l′ ⟩ A ∷ U l / U-intr ⊩U →
      (Γ ⊩⟨ l ⟩ A ×
       ∃ λ B → Γ ⊢ A :⇒*: B ∷ U l × Type B × Γ ⊢ B ≅ B ∷ U l)
    lemma ⊩U@(noemb (Uᵣ l l<l′ U⇒*U)) (Uₜ B A⇒*B B-type B≅B ⊩A) =
      case U⇒*U→≡ U⇒*U of λ {
        PE.refl →
        PE.subst (λ k → LogRelKit._⊩_ k _ _) (PE.sym (kit≡kit′ l<l′)) ⊩A
      , B , A⇒*B , B-type , B≅B }
    lemma (emb ≤ᵘ-refl     ⊩U) = lemma ⊩U
    lemma (emb (≤ᵘ-step p) ⊩U) = lemma (emb p ⊩U)

opaque

  -- A variant of ⊩∷U⇔.

  Type→⊩∷U⇔ :
    Type A →
    Γ ⊩ A ∷ U l ⇔
    ((Γ ⊩⟨ l ⟩ A) × Γ ⊢ A ∷ U l × Γ ⊢ A ≅ A ∷ U l)
  Type→⊩∷U⇔ {A} {Γ} {l} A-type =
    Γ ⊩ A ∷ U l                                            ⇔⟨ ⊩∷U⇔ ⟩

    ((Γ ⊩⟨ l ⟩ A) × ∃ λ B → Γ ⊢ A :⇒*: B ∷ U l × Type B ×
     Γ ⊢ B ≅ B ∷ U l)
                                                           ⇔⟨ id⇔
                                                                ×-cong-⇔
                                                              ( (λ (_ , A⇒*B , _ , B≅B) →
                                                                  case whnfRed*Term (redₜ A⇒*B) (typeWhnf A-type) of λ {
                                                                    PE.refl →
                                                                  ⊢t-redₜ A⇒*B , B≅B })
                                                              , (λ (⊢A , A≅A) → _ , idRedTerm:*: ⊢A , A-type , A≅A)
                                                              )
                                                            ⟩

    (Γ ⊩⟨ l ⟩ A) × Γ ⊢ A ∷ U l × Γ ⊢ A ≅ A ∷ U l           □⇔

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩⟨⟩U≡⇔ :
    Γ ⊩⟨ l′ ⟩ U l ≡ A ⇔
    (l <ᵘ l′ × Γ ⊢ A :⇒*: U l × Γ ⊩⟨ l′ ⟩ A)
  ⊩⟨⟩U≡⇔ {l′} {l} =
      (λ (⊩U , ⊩A , U≡A) →
         let l<l′ , A⇒*U =
               lemma (U-elim ⊩U)
                 (irrelevanceEq ⊩U (U-intr (U-elim ⊩U)) U≡A)
         in l<l′ , A⇒*U , ⊩A)
    , (λ (l<l′ , A⇒*U@([ _ , ⊢U , _ ]) , ⊩A) →
         Uᵣ (Uᵣ l l<l′ (idRed:*: ⊢U)) , ⊩A , A⇒*U)
    where
    lemma :
      (⊩U : Γ ⊩⟨ l″ ⟩U U l) →
      Γ ⊩⟨ l″ ⟩ U l ≡ A / U-intr ⊩U →
      l <ᵘ l″ × Γ ⊢ A :⇒*: U l
    lemma ⊩U@(noemb (Uᵣ _ l<l″ U⇒*U)) A⇒*U =
      case U⇒*U→≡ U⇒*U of λ {
        PE.refl →
      l<l″ , A⇒*U }
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map ≤ᵘ-step idᶠ ∘→ lemma ⊩U
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map ≤ᵘ-step idᶠ ∘→ lemma (emb p ⊩U)

opaque
  unfolding _⊩_ _⊩_≡_

  -- A characterisation lemma for _⊩_≡_.

  ⊩U≡⇔ :
    Γ ⊩ U l ≡ A ⇔
    (Γ ⊢ A :⇒*: U l × Γ ⊩ A)
  ⊩U≡⇔ {Γ} {l} {A} =
    Γ ⊩ U l ≡ A                                        ⇔⟨ id⇔ ⟩
    (∃ λ l′ → Γ ⊩⟨ l′ ⟩ U l ≡ A)                       ⇔⟨ (Σ-cong-⇔ λ _ → ⊩⟨⟩U≡⇔) ⟩
    (∃ λ l′ → l <ᵘ l′ × Γ ⊢ A :⇒*: U l × Γ ⊩⟨ l′ ⟩ A)  ⇔⟨ (λ (_ , _ , A⇒*U , ⊩A) → A⇒*U , _ , ⊩A)
                                                        , (λ (A⇒*U , l′ , ⊩A) → l′ ⊔ᵘ 1+ l , ≤ᵘ⊔ᵘˡ {l₁ = l′} , A⇒*U , emb-≤-⊩ ≤ᵘ⊔ᵘʳ ⊩A)
                                                        ⟩
    Γ ⊢ A :⇒*: U l × Γ ⊩ A                             □⇔

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩_≡_∷_

  -- A characterisation lemma for _⊩_≡_∷_.

  ⊩≡∷U⇔ :
    Γ ⊩ A ≡ B ∷ U l ⇔
    (Γ ⊩⟨ l ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A :⇒*: A′ ∷ U l ×
     Γ ⊢ B :⇒*: B′ ∷ U l ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U l)
  ⊩≡∷U⇔ {l} =
      (λ (_ , ⊩U , _ , _ , A≡B) →
         lemma (U-elim ⊩U)
           (irrelevanceEqTerm ⊩U (U-intr (U-elim ⊩U)) A≡B))
    , (λ ((⊩A , ⊩B , A≡B) , _ , _ ,
          A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′) →
           1+ l
         , Uᵣ′ _ ≤ᵘ-refl (idRed:*: (Uⱼ (wfTerm (⊢t-redₜ A⇒*A′))))
         , Uₜ _ A⇒*A′ A′-type (≅ₜ-trans A′≅B′ (≅ₜ-sym A′≅B′)) ⊩A
         , Uₜ _ B⇒*B′ B′-type (≅ₜ-trans (≅ₜ-sym A′≅B′) A′≅B′) ⊩B
         , Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B)
    where
    lemma :
      (⊩U : Γ ⊩⟨ l′ ⟩U U l) →
      Γ ⊩⟨ l′ ⟩ A ≡ B ∷ U l / U-intr ⊩U →
      Γ ⊩⟨ l ⟩ A ≡ B ×
      ∃₂ λ A′ B′ →
      Γ ⊢ A :⇒*: A′ ∷ U l ×
      Γ ⊢ B :⇒*: B′ ∷ U l ×
      Type A′ ×
      Type B′ ×
      Γ ⊢ A′ ≅ B′ ∷ U l
    lemma
      {l′}
      ⊩U@(noemb (Uᵣ _ l<l′ U⇒*U))
      (Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B) =
        case U⇒*U→≡ U⇒*U of λ {
            PE.refl →
          ( ⊩<⇔⊩ l<l′ .proj₁ ⊩A
          , ⊩<⇔⊩ l<l′ .proj₁ ⊩B
          , ⊩<≡⇔⊩≡ l<l′ .proj₁ A≡B
          )
        , _ , _ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′ }
    lemma (emb ≤ᵘ-refl     ⊩U) = lemma ⊩U
    lemma (emb (≤ᵘ-step p) ⊩U) = lemma (emb p ⊩U)

opaque

  -- A variant of ⊩≡∷U⇔.

  Type→⊩≡∷U⇔ :
    Type A →
    Type B →
    Γ ⊩ A ≡ B ∷ U l ⇔
    ((Γ ⊩⟨ l ⟩ A ≡ B) ×
     Γ ⊢ A ∷ U l ×
     Γ ⊢ B ∷ U l ×
     Γ ⊢ A ≅ B ∷ U l)
  Type→⊩≡∷U⇔ {A} {B} {Γ} {l} A-type B-type =
    Γ ⊩ A ≡ B ∷ U l         ⇔⟨ ⊩≡∷U⇔ ⟩

    ((Γ ⊩⟨ l ⟩ A ≡ B) ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A :⇒*: A′ ∷ U l ×
     Γ ⊢ B :⇒*: B′ ∷ U l ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U l)     ⇔⟨ (λ (A≡B , _ , _ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′) →
                                  case whnfRed*Term (redₜ A⇒*A′) (typeWhnf A-type) of λ {
                                    PE.refl →
                                  case whnfRed*Term (redₜ B⇒*B′) (typeWhnf B-type) of λ {
                                    PE.refl →
                                  A≡B , ⊢t-redₜ A⇒*A′ , ⊢t-redₜ B⇒*B′ , A′≅B′ }})
                             , (λ (A≡B ,  ⊢A , ⊢B , A≅B) →
                                    A≡B , _ , _
                                  , idRedTerm:*: ⊢A , idRedTerm:*: ⊢B
                                  , A-type , B-type , A≅B)
                             ⟩
    (Γ ⊩⟨ l ⟩ A ≡ B) ×
    Γ ⊢ A ∷ U l ×
    Γ ⊢ B ∷ U l ×
    Γ ⊢ A ≅ B ∷ U l         □⇔

------------------------------------------------------------------------
-- Validity

opaque

  -- Validity of U.

  ⊩ᵛU : ⊩ᵛ Γ → Γ ⊩ᵛ U l
  ⊩ᵛU {Γ} {l} ⊩Γ =
    ⊩ᵛ⇔ .proj₂
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ              →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                           →⟨ (λ ⊢Δ → idRed:*: (Uⱼ ⊢Δ) , ⊩U⇔ .proj₂ ⊢Δ) ⟩
          Δ ⊢ U l :⇒*: U l × (Δ ⊩ U l)  ⇔˘⟨ ⊩U≡⇔ ⟩→
          Δ ⊩ U l ≡ U l                 □
      )

opaque

  -- Validity of U, seen as a term former.

  ⊩ᵛU∷U : ⊩ᵛ Γ → Γ ⊩ᵛ U l ∷ U (1+ l)
  ⊩ᵛU∷U {Γ} {l} ⊩Γ =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛU ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                          →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩

          ⊢ Δ                                       →⟨ (λ ⊢Δ → ⊩⟨⟩U⇔ .proj₂ (≤ᵘ-refl , ⊢Δ) , Uⱼ ⊢Δ , ≅-Urefl ⊢Δ) ⟩

          (Δ ⊩⟨ 1+ l ⟩ U l) × Δ ⊢ U l ∷ U (1+ l) ×
          Δ ⊢ U l ≅ U l ∷ U (1+ l)                  ⇔˘⟨ Type→⊩∷U⇔ Uₙ ⟩→

          Δ ⊩ U l ∷ U (1+ l)                        →⟨ L.refl-⊩≡∷ ⟩

          Δ ⊩ U l ≡ U l ∷ U (1+ l)                  □
      )

opaque

  -- Validity of one of the typing rules called univ.

  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ A ∷ U l →
    Γ ⊩ᵛ A
  ⊩ᵛ∷U→⊩ᵛ ⊩A∷U =
    case ⊩ᵛ∷⇔ .proj₁ ⊩A∷U of λ
      (⊩U , A≡A∷U) →
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , L.⊩≡-intro ∘→ proj₁ ∘→ ⊩≡∷U⇔ .proj₁ ∘→ A≡A∷U
      )

opaque

  -- Validity of another of the typing rules called univ.

  ⊩ᵛ≡∷U→⊩ᵛ≡ :
    Γ ⊩ᵛ A ≡ B ∷ U l →
    Γ ⊩ᵛ A ≡ B
  ⊩ᵛ≡∷U→⊩ᵛ≡ A≡B∷U =
    case ⊩ᵛ≡∷⇔ .proj₁ A≡B∷U of λ
      (⊩U , A≡B∷U) →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , L.⊩≡-intro ∘→ proj₁ ∘→ ⊩≡∷U⇔ .proj₁ ∘→ A≡B∷U
      )
