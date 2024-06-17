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
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R

open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n    : Nat
    Γ    : Con Term n
    A B  : Term n
    l l′ : TypeLevel
    k    : LogRelKit

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩U⇔ :
    Γ ⊩⟨ l ⟩ U ⇔
    ((∃ λ l′ → l′ < l) × ⊢ Γ)
  ⊩U⇔ =
      (λ ⊩U → lemma (U-elim ⊩U))
    , (λ ((l′ , l′<l) , ⊢Γ) →
         Uᵣ (Uᵣ l′ l′<l ⊢Γ))
    where
    lemma :
      Γ ⊩⟨ l ⟩U →
      (∃ λ l′ → l′ < l) × ⊢ Γ
    lemma (noemb (Uᵣ l′ l′<l ⊢Γ)) =
      (l′ , l′<l) , ⊢Γ
    lemma (emb 0<1 ⊩U) =
      case lemma ⊩U of λ where
        ((_ , ()) , _)

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷U⇔ :
    Γ ⊩⟨ l ⟩ A ∷ U ⇔
    ((∃ λ l′ → l′ < l × Γ ⊩⟨ l′ ⟩ A) ×
     (∃ λ B → Γ ⊢ A :⇒*: B ∷ U × Type B × Γ ⊢ B ≅ B ∷ U))
  ⊩∷U⇔ =
      (λ (⊩U , ⊩A) →
         lemma (U-elim ⊩U) (irrelevanceTerm ⊩U (U-intr (U-elim ⊩U)) ⊩A))
    , (λ ((l′ , l′<l , ⊩A) , B , A⇒*B , B-type , B≅B) →
           Uᵣ (Uᵣ l′ l′<l (wfTerm (⊢t-redₜ A⇒*B)))
         , Uₜ B A⇒*B B-type B≅B
             (PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ l′<l) ⊩A))
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U) →
      Γ ⊩⟨ l ⟩ A ∷ U / U-intr ⊩U →
      (∃ λ l′ → l′ < l × Γ ⊩⟨ l′ ⟩ A) ×
      (∃ λ B → Γ ⊢ A :⇒*: B ∷ U × Type B × Γ ⊢ B ≅ B ∷ U)
    lemma (noemb (Uᵣ l′ l′<l _)) (Uₜ B A⇒*B B-type B≅B ⊩A) =
        ( l′ , l′<l
        , PE.subst (λ k → LogRelKit._⊩_ k _ _) (PE.sym (kit≡kit′ l′<l))
            ⊩A
        )
      , B , A⇒*B , B-type , B≅B
    lemma (emb 0<1 ⊩U) ⊩A =
      case lemma ⊩U ⊩A of λ where
        ((_ , () , _) , _)

opaque

  -- A variant of ⊩∷U⇔.

  Type→⊩∷U⇔ :
    Type A →
    Γ ⊩⟨ l ⟩ A ∷ U ⇔
    ((∃ λ l′ → l′ < l × Γ ⊩⟨ l′ ⟩ A) ×
     Γ ⊢ A ∷ U ×
     Γ ⊢ A ≅ A ∷ U)
  Type→⊩∷U⇔ {A} {Γ} {l} A-type =
    Γ ⊩⟨ l ⟩ A ∷ U                                       ⇔⟨ ⊩∷U⇔ ⟩

    (∃ λ l′ → l′ < l × Γ ⊩⟨ l′ ⟩ A) ×
    (∃ λ B → Γ ⊢ A :⇒*: B ∷ U × Type B × Γ ⊢ B ≅ B ∷ U)  ⇔⟨ id⇔
                                                              ×-cong-⇔
                                                            ( (λ (_ , A⇒*B , _ , B≅B) →
                                                                 case whnfRed*Term (redₜ A⇒*B) (typeWhnf A-type) of λ {
                                                                   PE.refl →
                                                                 ⊢t-redₜ A⇒*B , B≅B })
                                                            , (λ (⊢A , A≅A) → _ , idRedTerm:*: ⊢A , A-type , A≅A)
                                                            )
                                                          ⟩
    (∃ λ l′ → l′ < l × Γ ⊩⟨ l′ ⟩ A) ×
    Γ ⊢ A ∷ U ×
    Γ ⊢ A ≅ A ∷ U                                        □⇔

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩U≡⇔ :
    Γ ⊩⟨ l ⟩ U ≡ A ⇔
    ((∃ λ l′ → l′ < l) × ⊢ Γ × A PE.≡ U)
  ⊩U≡⇔ =
      (λ (⊩U , _ , U≡A) →
         lemma (U-elim ⊩U) (irrelevanceEq ⊩U (U-intr (U-elim ⊩U)) U≡A))
    , (λ where
         ((l′ , l′<l) , ⊢Γ , PE.refl) →
           let ⊩U = Uᵣ (Uᵣ l′ l′<l ⊢Γ) in
           ⊩U , ⊩U , PE.refl)
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U) →
      Γ ⊩⟨ l ⟩ U ≡ A / U-intr ⊩U →
      (∃ λ l′ → l′ < l) × ⊢ Γ × A PE.≡ U
    lemma (noemb (Uᵣ l′ l′<l ⊢Γ)) A≡U =
      (l′ , l′<l) , ⊢Γ , A≡U
    lemma (emb 0<1 ⊩U) ⊩A =
      case lemma ⊩U ⊩A of λ where
        ((_ , ()) , _)

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷U⇔ :
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U ⇔
    ((∃₂ λ l′ (l′<l : l′ < l) → Γ ⊩⟨ l′ ⟩ A ≡ B) ×
     (∃₂ λ A′ B′ →
      Γ ⊢ A :⇒*: A′ ∷ U ×
      Γ ⊢ B :⇒*: B′ ∷ U ×
      Type A′ ×
      Type B′ ×
      Γ ⊢ A′ ≅ B′ ∷ U))
  ⊩≡∷U⇔ =
      (λ (⊩U , _ , _ , A≡B) →
         lemma₃ (U-elim ⊩U)
           (irrelevanceEqTerm ⊩U (U-intr (U-elim ⊩U)) A≡B))
    , (λ ( (l′ , l′<l , ⊩A , ⊩B , A≡B)
         , (A′ , B′ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′)
         ) →
         let ⊩A =
               PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ l′<l) ⊩A
             ⊩B =
               PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ l′<l) ⊩B
         in
           Uᵣ (Uᵣ l′ l′<l (wfTerm (⊢t-redₜ A⇒*A′)))
         , Uₜ A′ A⇒*A′ A′-type (≅ₜ-trans A′≅B′ (≅ₜ-sym A′≅B′)) ⊩A
         , Uₜ B′ B⇒*B′ B′-type (≅ₜ-trans (≅ₜ-sym A′≅B′) A′≅B′) ⊩B
         , Uₜ₌ A′ B′ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B
             (lemma₂ (kit≡kit′ l′<l) A≡B))
    where
    lemma₁ :
      {l′<l : l′ < l}
      {⊩A : LogRelKit._⊩_ (kit′ l′<l) Γ A}
      (eq : k PE.≡ kit′ l′<l) →
      LogRelKit._⊩_≡_/_ (kit′ l′<l) Γ A B ⊩A →
      LogRelKit._⊩_≡_/_ k Γ A B
        (PE.subst (λ k → LogRelKit._⊩_ k _ _) (PE.sym eq) ⊩A)
    lemma₁ PE.refl A≡B = A≡B

    lemma₂ :
      {l′<l : l′ < l}
      {⊩A : LogRelKit._⊩_ k Γ A}
      (eq : k PE.≡ kit′ l′<l) →
      LogRelKit._⊩_≡_/_ k Γ A B ⊩A →
      LogRelKit._⊩_≡_/_ (kit′ l′<l) Γ A B
        (PE.subst (λ k → LogRelKit._⊩_ k _ _) eq ⊩A)
    lemma₂ PE.refl A≡B = A≡B

    lemma₃ :
      (⊩U : Γ ⊩⟨ l ⟩U) →
      Γ ⊩⟨ l ⟩ A ≡ B ∷ U / U-intr ⊩U →
      (∃₂ λ l′ (l′<l : l′ < l) → Γ ⊩⟨ l′ ⟩ A ≡ B) ×
      (∃₂ λ A′ B′ →
       Γ ⊢ A :⇒*: A′ ∷ U ×
       Γ ⊢ B :⇒*: B′ ∷ U ×
       Type A′ ×
       Type B′ ×
       Γ ⊢ A′ ≅ B′ ∷ U)
    lemma₃ (emb 0<1 ⊩U) A≡B =
      case lemma₃ ⊩U A≡B of λ where
        ((_ , () , _) , _)
    lemma₃
      (noemb (Uᵣ l′ l′<l _))
      (Uₜ₌ A′ B′ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B) =
        ( l′ , l′<l
        , ( PE.subst (λ k → LogRelKit._⊩_ k _ _)
              (PE.sym (kit≡kit′ l′<l)) ⊩A
          , PE.subst (λ k → LogRelKit._⊩_ k _ _)
              (PE.sym (kit≡kit′ l′<l)) ⊩B
          , lemma₁ (kit≡kit′ l′<l) A≡B
          )
        )
      , (A′ , B′ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′)

opaque

  -- A variant of ⊩≡∷U⇔.

  Type→⊩≡∷U⇔ :
    Type A →
    Type B →
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U ⇔
    (Γ ⊢ A ∷ U ×
     Γ ⊢ B ∷ U ×
     Γ ⊢ A ≅ B ∷ U ×
     ∃₂ λ l′ (l′<l : l′ < l) → Γ ⊩⟨ l′ ⟩ A ≡ B)
  Type→⊩≡∷U⇔ {A} {B} {Γ} {l} A-type B-type =
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U                           ⇔⟨ ⊩≡∷U⇔ ⟩

    (∃₂ λ l′ (l′<l : l′ < l) → Γ ⊩⟨ l′ ⟩ A ≡ B) ×
    (∃₂ λ A′ B′ →
     Γ ⊢ A :⇒*: A′ ∷ U ×
     Γ ⊢ B :⇒*: B′ ∷ U ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U)                            ⇔⟨ (λ ((_ , l′<l , A≡B) , (_ , _ , A⇒*A′ , B⇒*B′ , _ , _ , A′≅B′)) →
                                                       case whnfRed*Term (redₜ A⇒*A′) (typeWhnf A-type) of λ {
                                                         PE.refl →
                                                       case whnfRed*Term (redₜ B⇒*B′) (typeWhnf B-type) of λ {
                                                         PE.refl →
                                                       ⊢t-redₜ A⇒*A′ , ⊢t-redₜ B⇒*B′ , A′≅B′ , _ , l′<l , A≡B }})
                                                  , (λ (⊢A , ⊢B , A≅B , _ , l′<l , A≡B) →
                                                         (_ , l′<l , A≡B)
                                                       , ( _ , _ , idRedTerm:*: ⊢A , idRedTerm:*: ⊢B
                                                         , A-type , B-type , A≅B
                                                         ))
                                                  ⟩
    Γ ⊢ A ∷ U ×
    Γ ⊢ B ∷ U ×
    Γ ⊢ A ≅ B ∷ U ×
    (∃₂ λ l′ (l′<l : l′ < l) → Γ ⊩⟨ l′ ⟩ A ≡ B)  □⇔

------------------------------------------------------------------------
-- Validity

opaque

  -- Validity of U.

  ⊩ᵛU : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ ¹ ⟩ U
  ⊩ᵛU {Γ} ⊩Γ =
    ⊩ᵛ⇔ .proj₂
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                  →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                               →⟨ (λ ⊢Δ → (_ , 0<1) , ⊢Δ , PE.refl) ⟩
          (∃ λ l → l < ¹) × ⊢ Δ × U PE.≡ U  ⇔˘⟨ ⊩U≡⇔ ⟩→
          Δ ⊩⟨ ¹ ⟩ U ≡ U                    □
      )

opaque

  -- Validity of one of the typing rules called univ.

  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U →
    Γ ⊩ᵛ⟨ l′ ⟩ A
  ⊩ᵛ∷U→⊩ᵛ ⊩A∷U =
    case ⊩ᵛ∷⇔ .proj₁ ⊩A∷U of λ
      (⊩U , A≡A∷U) →
    emb-⊩ᵛ ⁰≤ $
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , λ σ₁≡σ₂ →
          case ⊩≡∷U⇔ .proj₁ $ A≡A∷U σ₁≡σ₂ of λ {
            ((_ , 0<1 , ⊩A[σ₁]≡A[σ₂]) , _) →
          ⊩A[σ₁]≡A[σ₂] }
      )

opaque

  -- Validity of another of the typing rules called univ.

  ⊩ᵛ≡∷U→⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B ∷ U →
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B
  ⊩ᵛ≡∷U→⊩ᵛ≡ A≡B∷U =
    case ⊩ᵛ≡∷⇔ .proj₁ A≡B∷U of λ
      (⊩U , A≡B∷U) →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , λ σ₁≡σ₂ →
          case ⊩≡∷U⇔ .proj₁ $ A≡B∷U σ₁≡σ₂ of λ {
            ((_ , 0<1 , A≡B) , _) →
          emb-⊩≡ ⁰≤ A≡B }
      )
