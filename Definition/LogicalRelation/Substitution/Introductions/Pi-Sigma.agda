------------------------------------------------------------------------
-- Validity for Π- and Σ-types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Var R
import Definition.LogicalRelation.Weakening R as W

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as TW using (_∷_⊇_)

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  n                         : Nat
  Γ Δ                       : Con Term _
  A A₁ A₂ B B₁ B₂ C t t₁ t₂ : Term _
  σ σ₁ σ₂                   : Subst _ _
  p p₁ p₂ q q₁ q₂           : M
  l l′                      : TypeLevel
  b b₁ b₂                   : BinderMode

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ΠΣ⇔ :
    {A : Term n} {B : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (ΠΣ-allowed b p q ×
     ⊢ Γ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      Δ ⊩⟨ l ⟩ wk ρ A ×
      (∀ {t u} →
       Δ ⊩⟨ l ⟩ t ≡ u ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B [ u ]₀)))
  ⊩ΠΣ⇔ {n} {b} {p} {q} {A} {B} =
      lemma ∘→ B-elim _
    , (λ (ok , ⊢Γ , rest) →
         case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) $
              rest TW.id ⊢Γ .proj₁ of λ
           ⊩A →
         case escape ⊩A of λ
           ⊢A →
         case ⊢Γ ∙ ⊢A of λ
           ⊢Γ∙A →
         case var ⊢Γ∙A here of λ
           ⊢x0 →
         case PE.subst (λ B → _ ⊩⟨ _ ⟩ B ≡ B) (wkSingleSubstId _) $
              rest (TW.step TW.id) ⊢Γ∙A .proj₂ $
              refl-⊩≡∷ $
              neutral-⊩∷ (W.wk (TW.step TW.id) ⊢Γ∙A ⊩A) (var _) ⊢x0
                (~-var ⊢x0) of λ
           B≡B →
         case escape $ wf-⊩≡ B≡B .proj₁ of λ
           ⊢B →
         Bᵣ (BM b p q)
           (Bᵣ _ _ (idRed:*: (ΠΣⱼ ⊢A ⊢B ok)) ⊢A ⊢B
              (≅-ΠΣ-cong ⊢A (escape-⊩≡ $ refl-⊩≡ ⊩A) (escape-⊩≡ B≡B) ok)
              (λ ρ⊇ ⊢Δ → rest ρ⊇ ⊢Δ .proj₁)
              (λ ρ⊇ ⊢Δ ⊩t →
                 wf-⊩≡
                   (rest ρ⊇ ⊢Δ .proj₂ $
                    refl-⊩≡∷ (rest _ _ .proj₁ , ⊩t))
                   .proj₁)
              (λ ρ⊇ ⊢Δ ⊩t ⊩u t≡u →
                 ⊩≡→⊩≡/
                   (wf-⊩≡
                      (rest ρ⊇ ⊢Δ .proj₂ $
                       refl-⊩≡∷ (rest _ _ .proj₁ , ⊩t))
                      .proj₁) $
                 rest ρ⊇ ⊢Δ .proj₂ (rest _ _ .proj₁ , ⊩t , ⊩u , t≡u))
              ok))
    where
    lemma :
      Γ ⊩⟨ l ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
      ΠΣ-allowed b p q ×
      ⊢ Γ ×
      (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
       ρ ∷ Δ ⊇ Γ → ⊢ Δ →
       Δ ⊩⟨ l ⟩ wk ρ A ×
       (∀ {t u} →
        Δ ⊩⟨ l ⟩ t ≡ u ∷ wk ρ A →
        Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B [ u ]₀))
    lemma (emb 0<1 ⊩ΠΣ) =
      case lemma ⊩ΠΣ of λ
        (ok , ⊢Γ , rest) →
        ok , ⊢Γ
      , λ ρ⊇ ⊢Δ →
          case rest ρ⊇ ⊢Δ of λ
            (⊩A , B≡B) →
          emb 0<1 ⊩A , emb-⊩≡ (emb 0<1) ∘→ B≡B ∘→ level-⊩≡∷ ⊩A
    lemma (noemb (Bᵣ _ _ ⇒*ΠΣ ⊢A _ _ ⊩wk-A ⊩wk-B wk-B≡wk-B ok)) =
      case B-PE-injectivity _ _ $ whnfRed* (red ⇒*ΠΣ) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
        ok , wf ⊢A
      , λ ρ⊇ ⊢Δ →
          let ⊩wk-ρ-A = ⊩wk-A ρ⊇ ⊢Δ in
            ⊩wk-ρ-A
          , λ (⊩wk-ρ-A′ , ⊩t , ⊩u , t≡u) →
              case irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩t of λ
                ⊩t →
              case irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩u of λ
                ⊩u →
                ⊩wk-B ρ⊇ ⊢Δ ⊩t
              , ⊩wk-B ρ⊇ ⊢Δ ⊩u
              , wk-B≡wk-B ρ⊇ ⊢Δ ⊩t ⊩u
                  (irrelevanceEqTerm ⊩wk-ρ-A′ ⊩wk-ρ-A t≡u) }

opaque

  -- A variant of ⊩ΠΣ⇔.

  ⊩ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    ΠΣ-allowed b p q × Γ ⊩⟨ l ⟩ A × Γ ∙ A ⊩⟨ l ⟩ B
  ⊩ΠΣ→ ⊩ΠΣ =
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ of λ
      (ok , ⊢Γ , rest) →
    case rest TW.id ⊢Γ of λ
      (⊩wk-id-A , _) →
    case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩wk-id-A of λ
      ⊩A →
    case rest (TW.step TW.id) (⊢→⊢∙ $ escape-⊩ ⊩A) of λ
      (⊩wk₁-A , wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀) →
      ok , ⊩A
    , PE.subst (_⊩⟨_⟩_ _ _) (wkSingleSubstId _)
        (proj₁ $ wf-⊩≡ $
         wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀ $
         refl-⊩≡∷ (⊩var here ⊩wk₁-A))

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡⇔ :
    {C : Term n} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C ⇔
    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ×
     Γ ⊩⟨ l ⟩ C ×
     ∃₂ λ A′ B′ → Γ ⊢ C :⇒*: ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      Δ ⊩⟨ l ⟩ wk ρ A ≡ wk ρ A′ ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B′ [ t ]₀)))
  ⊩ΠΣ≡⇔ =
      (λ (⊩ΠΣ , ⊩C , ΠΣ≡C) →
         case B-elim _ ⊩ΠΣ of λ
           ⊩ΠΣ′ →
           ⊩ΠΣ , ⊩C
         , lemma₁ refl ⊩ΠΣ′ ⊩C (irrelevanceEq ⊩ΠΣ (B-intr _ ⊩ΠΣ′) ΠΣ≡C))
    , (λ (⊩ΠΣ , ⊩C , _ , _ , C⇒* , rest) →
         case B-elim _ ⊩ΠΣ of λ
           ⊩ΠΣ′ →
         B-intr _ ⊩ΠΣ′ , ⊩C , lemma₂ ⊩ΠΣ′ C⇒* rest)
    where
    lemma₁ :
      l′ ≤ l →
      (⊩ΠΣ : Γ ⊩⟨ l′ ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) →
      Γ ⊩⟨ l ⟩ C →
      Γ ⊩⟨ l′ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C / B-intr _ ⊩ΠΣ →
      ∃₂ λ A′ B′ → Γ ⊢ C :⇒*: ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
      (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
       ρ ∷ Δ ⊇ Γ → ⊢ Δ →
       Δ ⊩⟨ l ⟩ wk ρ A ≡ wk ρ A′ ×
       (∀ {t} →
        Δ ⊩⟨ l ⟩ t ∷ wk ρ A →
        Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B′ [ t ]₀))
    lemma₁ ¹≤l (emb 0<1 ⊩ΠΣ) ⊩C ΠΣ≡C =
      lemma₁ (≤-trans (emb 0<1) ¹≤l) ⊩ΠΣ ⊩C ΠΣ≡C
    lemma₁
      l′≤l (noemb (Bᵣ _ _ ⇒*ΠΣ ⊢A _ _ ⊩wk-A ⊩wk-B _ ok)) ⊩C
      (B₌ _ _ ⇒*ΠΣ′ _ wk-A≡wk-A′ wk-B≡wk-B′) =
      case B-PE-injectivity _ _ $ whnfRed* (red ⇒*ΠΣ) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
        _ , _ , ⇒*ΠΣ′
      , λ ρ⊇ ⊢Δ →
          case ⊩ΠΣ⇔ .proj₁ (wf-⊩≡ (⊩-⇒* ⇒*ΠΣ′ ⊩C) .proj₂)
                 .proj₂ .proj₂ ρ⊇ ⊢Δ of λ
            (⊩wk-ρ-A′ , wk-ρ⇑-B′≡wk-ρ⇑-B′) →
          case   emb-≤-⊩ l′≤l (⊩wk-A ρ⊇ ⊢Δ)
               , ⊩wk-ρ-A′
               , emb-≤-≡ (wk-A≡wk-A′ ρ⊇ ⊢Δ) of λ
            wk-ρ-A≡wk-ρ-A′ →
            wk-ρ-A≡wk-ρ-A′
          , λ ⊩t@(⊩wk-ρ-A , ⊩t′) →
              let ⊩wk-ρ⇑-B[t] =
                    ⊩wk-B ρ⊇ ⊢Δ
                      (irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ρ⊇ ⊢Δ) ⊩t′)
                  ⊩wk-ρ⇑-B[t]′ = emb-≤-⊩ l′≤l ⊩wk-ρ⇑-B[t]
              in
                ⊩wk-ρ⇑-B[t]′
              , wf-⊩≡
                  (wk-ρ⇑-B′≡wk-ρ⇑-B′ $
                   refl-⊩≡∷ (conv-⊩∷ wk-ρ-A≡wk-ρ-A′ ⊩t))
                  .proj₁
              , irrelevanceEq ⊩wk-ρ⇑-B[t] ⊩wk-ρ⇑-B[t]′
                  (wk-B≡wk-B′ ρ⊇ ⊢Δ $
                   irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ρ⊇ ⊢Δ) ⊩t′) }

    lemma₂ :
      (⊩ΠΣ : Γ ⊩⟨ l′ ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) →
      Γ ⊢ C :⇒*: ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
      (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
       ρ ∷ Δ ⊇ Γ → ⊢ Δ →
       Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
       (∀ {t} →
        Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
        Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀)) →
      Γ ⊩⟨ l′ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ C / B-intr _ ⊩ΠΣ
    lemma₂ (emb 0<1 ⊩ΠΣ₁) C⇒* rest =
      lemma₂ ⊩ΠΣ₁ C⇒* rest
    lemma₂
      {B₁} {B₂} (noemb ⊩ΠΣ₁@(Bᵣ _ _ ⇒*ΠΣ₁ ⊢A₁ _ _ ⊩wk-A₁ ⊩wk-B₁ _ ok))
      C⇒* rest =
      case B-PE-injectivity _ _ $ whnfRed* (red ⇒*ΠΣ₁) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      case PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wk-id _) (wk-id _) $
           rest TW.id (wf ⊢A₁) .proj₁ of λ
        A₁≡A₂ →
      case ⊢→⊢∙ ⊢A₁ of λ
        ⊢Γ∙A₁ →
      case var ⊢Γ∙A₁ here of λ
        ⊢x0 →
      case PE.subst₂ (_⊩⟨_⟩_≡_ _ _) {y = B₁} {v = B₂}
             (wkSingleSubstId _) (wkSingleSubstId _) $
           rest (TW.step TW.id) ⊢Γ∙A₁ .proj₂ $
           neutral-⊩∷ (W.wk (TW.step TW.id) ⊢Γ∙A₁ (wf-⊩≡ A₁≡A₂ .proj₁))
             (var _) ⊢x0 (~-var ⊢x0) of λ
        B₁≡B₂ →
      _ ⊩⟨ _ ⟩ _ ≡ _ / Bᵣ _ ⊩ΠΣ₁ ∋
      B₌ _ _ C⇒* (≅-ΠΣ-cong ⊢A₁ (escape-⊩≡ A₁≡A₂) (escape-⊩≡ B₁≡B₂) ok)
        (λ ρ⊇ ⊢Δ → ⊩≡→⊩≡/ (⊩wk-A₁ ρ⊇ ⊢Δ) (rest ρ⊇ ⊢Δ .proj₁))
        (λ ρ⊇ ⊢Δ ⊩t →
           case rest ρ⊇ ⊢Δ of λ
             (wk-ρ-A₁≡wk-ρ-A₂ , wk-ρ⇑-B₁≡wk-ρ⇑-B₂) →
           case wf-⊩≡ wk-ρ-A₁≡wk-ρ-A₂ .proj₁ of λ
             ⊩wk-ρ-A₁ →
           ⊩≡→⊩≡/ (⊩wk-B₁ ρ⊇ ⊢Δ ⊩t) $
           wk-ρ⇑-B₁≡wk-ρ⇑-B₂
             ( ⊩wk-ρ-A₁
             , irrelevanceTerm (⊩wk-A₁ ρ⊇ ⊢Δ) ⊩wk-ρ-A₁ ⊩t
             )) }

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡ΠΣ⇔ :
    {A₁ A₂ : Term n} {B₁ B₂ : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ⇔
    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
     Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀)))
  ⊩ΠΣ≡ΠΣ⇔
    {n} {Γ} {l} {b₁} {p₁} {q₁} {b₂} {p₂} {q₂} {A₁} {A₂} {B₁} {B₂} =

    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂  ⇔⟨ ⊩ΠΣ≡⇔ ⟩

    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
     Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     ∃₂ λ A B →
     Γ ⊢ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ :⇒*: ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A ▹ B ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B [ t ]₀)))       ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ ⊩ΠΣ₂ →
                                                                            (λ (_ , _ , ΠΣ⇒*ΠΣ , rest) →
                                                                               case whnfRed* (red ΠΣ⇒*ΠΣ) ΠΣₙ of λ {
                                                                                 PE.refl →
                                                                               PE.refl , PE.refl , PE.refl , rest })
                                                                          , λ { (PE.refl , PE.refl , PE.refl , rest) →
                                                                                _ , _ , idRed:*: (escape-⊩ ⊩ΠΣ₂) , rest }) ⟩
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
    b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
    (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
     ρ ∷ Δ ⊇ Γ → ⊢ Δ →
     Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
     (∀ {t} →
      Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
      Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀))        □⇔

opaque

  -- A variant of ⊩ΠΣ≡ΠΣ⇔.

  ⊩ΠΣ≡ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    ΠΣ-allowed b₁ p₁ q₁ × b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ × Γ ∙ A₁ ⊩⟨ l ⟩ B₁ ≡ B₂
  ⊩ΠΣ≡ΠΣ→ ΠΣ≡ΠΣ =
    case ⊩ΠΣ≡ΠΣ⇔ .proj₁ ΠΣ≡ΠΣ of λ
      (⊩ΠΣ₁ , _ , b₁≡b₂ , p₁≡p₂ , q₁≡q₂ , rest) →
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ₁ of λ
      (ok , ⊢Γ , _) →
    case rest TW.id ⊢Γ of λ
      (wk-id-A₁≡wk-id-A₂ , _) →
    case PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wk-id _) (wk-id _)
           wk-id-A₁≡wk-id-A₂ of λ
      A₁≡A₂ →
    case rest (TW.step TW.id)
           (⊢→⊢∙ $ escape-⊩ $ wf-⊩≡ A₁≡A₂ .proj₁) of λ
      (wk₁-A₁≡wk₁-A₂ , wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀) →
      ok , b₁≡b₂ , p₁≡p₂ , q₁≡q₂ , A₁≡A₂
    , PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wkSingleSubstId _) (wkSingleSubstId _)
        (wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀ $
         ⊩var here (wf-⊩≡ wk₁-A₁≡wk₁-A₂ .proj₁))

-- See also ⊩ᵛΠΣ⇔ below.

------------------------------------------------------------------------
-- Some substitution lemmas

opaque

  -- A substitution lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩⟨ l ⟩ B₁ [ t₁ ]₀ ≡ B₂ [ t₂ ]₀
  ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ {B₁} {B₂} {t₁} {t₂} ΠΣ≡ΠΣ t₁≡t₂ =
    case ⊩ΠΣ≡ΠΣ⇔ .proj₁ ΠΣ≡ΠΣ of λ
      (⊩ΠΣ₁ , _ , _ , _ , _ , rest) →
    case ⊩ΠΣ→ ⊩ΠΣ₁ of λ
      (_ , ⊩A₁ , _) →
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ₁ of λ
      (_ , ⊢Γ , rest₁) →
    B₁ [ t₁ ]₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁) $
                   rest₁ TW.id ⊢Γ .proj₂ $
                   PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk-id _) $
                   level-⊩≡∷ ⊩A₁ t₁≡t₂ ⟩⊩
    B₁ [ t₂ ]₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₂) $
                   rest TW.id ⊢Γ .proj₂ $
                   PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk-id _) $
                   level-⊩∷ ⊩A₁ $
                   wf-⊩≡∷ t₁≡t₂ .proj₂ ⟩⊩∎
    B₂ [ t₂ ]₀  ∎

opaque

  -- A substitution lemma for _⊩⟨_⟩_.

  ⊩ΠΣ→⊩∷→⊩[]₀ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ B [ t ]₀
  ⊩ΠΣ→⊩∷→⊩[]₀ ⊩ΠΣ ⊩t =
    wf-⊩≡ (⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩ΠΣ) (refl-⊩≡∷ ⊩t)) .proj₁

------------------------------------------------------------------------
-- Validity of Π and Σ, seen as type formers

opaque

  -- Reducibility for Π and Σ, seen as type formers.

  ⊩ΠΣ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) [ σ ]
  ⊩ΠΣ {A} {B} ok ⊩A ⊩B ⊩σ =
    ⊩ΠΣ⇔ .proj₂
      ( ok
      , escape-⊩ˢ∷ ⊩σ .proj₁
      , λ ρ⊇ ⊢Η →
            PE.subst (_⊩⟨_⟩_ _ _) (PE.sym $ wk-subst A)
              (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ ⊩ˢ∷-•ₛ ⊢Η ρ⊇ ⊩σ)
          , λ t≡u →
              PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ singleSubstWkComp _ _ B)
                (PE.sym $ singleSubstWkComp _ _ B) $
              ⊩ᵛ⇔ .proj₁ ⊩B .proj₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ( _ , ⊩A
                  , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A) t≡u
                  )
                , refl-⊩ˢ≡∷ (⊩ˢ∷-•ₛ ⊢Η ρ⊇ ⊩σ)
                )
      )

opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as type
  -- formers.

  ⊩ΠΣ≡ΠΣ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ]
  ⊩ΠΣ≡ΠΣ {A₁} {A₂} {B₁} {B₂} ok A₁≡A₂ B₁≡B₂ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ A₁≡A₂ ⊩B₂ of λ
      ⊩B₂ →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    ⊩ΠΣ≡ΠΣ⇔ .proj₂
      ( ⊩ΠΣ ok ⊩A₁ ⊩B₁ ⊩σ₁
      , ⊩ΠΣ ok ⊩A₂ ⊩B₂ ⊩σ₂
      , PE.refl , PE.refl , PE.refl
      , λ ρ⊇ ⊢Η →
            PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (PE.sym $ wk-subst A₁)
              (PE.sym $ wk-subst A₂)
              (⊩ᵛ≡⇔′ .proj₁ A₁≡A₂ .proj₂ .proj₂ $
               ⊩ˢ≡∷-•ₛ ⊢Η ρ⊇ σ₁≡σ₂)
          , λ ⊩t →
              PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ singleSubstWkComp _ _ B₁)
                (PE.sym $ singleSubstWkComp _ _ B₂) $
              ⊩ᵛ≡⇔′ .proj₁ B₁≡B₂ .proj₂ .proj₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ( _ , ⊩A₁
                  , refl-⊩≡∷
                      (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk-subst A₁) ⊩t)
                  )
                , ⊩ˢ≡∷-•ₛ ⊢Η ρ⊇ σ₁≡σ₂
                )
      )

opaque

  -- Validity of Π and Σ, seen as type formers.

  ΠΣᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  ΠΣᵛ ok ⊩A ⊩B =
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ ⊩A
      , ⊩ΠΣ≡ΠΣ ok (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡ ⊩B)
      )

opaque

  -- Validity of equality preservation for Π and Σ, seen as type
  -- formers.

  ΠΣ-congᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂
  ΠΣ-congᵛ ok A₁≡A₂ B₁≡B₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ A₁≡A₂ ⊩B₂ of λ
      ⊩B₂ →
    ⊩ᵛ≡⇔ .proj₂
      ( ΠΣᵛ ok ⊩A₁ ⊩B₁
      , ΠΣᵛ ok ⊩A₂ ⊩B₂
      , ⊩ΠΣ≡ΠΣ ok A₁≡A₂ B₁≡B₂ ∘→ refl-⊩ˢ≡∷
      )

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛΠΣ⇔ :
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (ΠΣ-allowed b p q × Γ ⊩ᵛ⟨ l ⟩ A × Γ ∙ A ⊩ᵛ⟨ l ⟩ B)
  ⊩ᵛΠΣ⇔ {B} =
      (λ ⊩ΠΣAB →
         case ⊩ᵛ⇔ .proj₁ ⊩ΠΣAB of λ
           (⊩Γ , ΠΣAB≡ΠΣAB) →
         case ⊩ᵛ⇔ .proj₂
                ( ⊩Γ
                , proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
                  ⊩ΠΣ≡ΠΣ→ ∘→ ΠΣAB≡ΠΣAB
                ) of λ
           ⊩A →
           ⊩ΠΣ⇔ .proj₁
             (wf-⊩≡ (ΠΣAB≡ΠΣAB (refl-⊩ˢ≡∷ $ ⊩ˢ∷-idSubst ⊩Γ)) .proj₁)
             .proj₁
         , ⊩A
         , ⊩ᵛ⇔ .proj₂
             ( ⊩ᵛ-∙-intro ⊩A
             , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
                 case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
                   ((_ , _ , head-σ₁≡head-σ₂) , tail-σ₁≡tail-σ₂) →
                 B [ σ₁ ]                             ≡˘⟨ substVar-to-subst consSubst-η B ⟩⊩≡
                 B [ consSubst (tail σ₁) (head σ₁) ]  ≡˘⟨ singleSubstComp _ _ B ⟩⊩≡
                 B [ tail σ₁ ⇑ ] [ head σ₁ ]₀         ≡⟨ ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (ΠΣAB≡ΠΣAB tail-σ₁≡tail-σ₂) head-σ₁≡head-σ₂ ⟩⊩∎≡
                 B [ tail σ₂ ⇑ ] [ head σ₂ ]₀         ≡⟨ singleSubstComp _ _ B ⟩
                 B [ consSubst (tail σ₂) (head σ₂) ]  ≡⟨ substVar-to-subst consSubst-η B ⟩
                 B [ σ₂ ]                             ∎
             ))
    , (λ (ok , ⊩A , ⊩B) → ΠΣᵛ ok ⊩A ⊩B)
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Validity of Π and Σ, seen as term formers

opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as term
  -- formers.

  ⊩ΠΣ≡ΠΣ∷U :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ ∷ U →
    Γ ∙ A₁ ⊩ᵛ⟨ l′ ⟩ B₁ ≡ B₂ ∷ U →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ] ∷ U
  ⊩ΠΣ≡ΠΣ∷U ok A₁≡A₂∷U B₁≡B₂∷U σ₁≡σ₂ =
    case ⊩∷U⇔ .proj₁ (⊩ᵛ∷→⊩∷ (wf-⊩ᵛ≡∷ A₁≡A₂∷U .proj₁)) of λ
      ((l″ , l″<l , _) , _) →
    case ⊩ᵛ≡∷U→⊩ᵛ≡ {l′ = l″} A₁≡A₂∷U of λ
      A₁≡A₂ →
    case ⊩ᵛ≡∷U→⊩ᵛ≡ {l′ = l″} B₁≡B₂∷U of λ
      B₁≡B₂ →
    case ⊩ᵛ≡∷⇔′ .proj₁ A₁≡A₂∷U .proj₂ .proj₂ σ₁≡σ₂ of λ
      A₁[σ₁]≡A₂[σ₂]∷U →
    case ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ B₁≡B₂∷U σ₁≡σ₂ of λ
      B₁[σ₁⇑]≡B₂[σ₂⇑]∷U →
    case wf-⊩≡∷ A₁[σ₁]≡A₂[σ₂]∷U of λ
      (⊩A₁[σ₁] , ⊩A₂[σ₂]) →
    case wf-⊩≡∷ B₁[σ₁⇑]≡B₂[σ₂⇑]∷U of λ
      (⊩B₁[σ₁] , _) →
    case ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ (conv-∙-⊩ᵛ∷ A₁≡A₂ (wf-⊩ᵛ≡∷ B₁≡B₂∷U .proj₂)) $
         wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₂ of λ
      ⊩B₂[σ₂] →
    case escape-⊩∷ ⊩A₁[σ₁] of λ
      ⊢A₁[σ₁] →
    case escape-⊩∷ ⊩B₁[σ₁] of λ
      ⊢B₁[σ₁] →
    Type→⊩≡∷U⇔ ΠΣₙ ΠΣₙ .proj₂
      ( ΠΣⱼ ⊢A₁[σ₁] ⊢B₁[σ₁] ok
      , ΠΣⱼ (escape-⊩∷ ⊩A₂[σ₂]) (escape-⊩∷ ⊩B₂[σ₂]) ok
      , ≅ₜ-ΠΣ-cong (univ ⊢A₁[σ₁]) (escape-⊩≡∷ A₁[σ₁]≡A₂[σ₂]∷U)
          (escape-⊩≡∷ B₁[σ₁⇑]≡B₂[σ₂⇑]∷U) ok
      , ( _ , l″<l
        , ⊩ᵛ≡⇔′ .proj₁ (ΠΣ-congᵛ ok A₁≡A₂ B₁≡B₂) .proj₂ .proj₂ σ₁≡σ₂
        )
      )

opaque

  -- Validity of Π and Σ, seen as term formers.

  ΠΣᵗᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U →
    Γ ∙ A ⊩ᵛ⟨ l′ ⟩ B ∷ U →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U
  ΠΣᵗᵛ ok ⊩A ⊩B =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛ∷⇔ .proj₁ ⊩A .proj₁
      , ⊩ΠΣ≡ΠΣ∷U ok (refl-⊩ᵛ≡∷ ⊩A) (refl-⊩ᵛ≡∷ ⊩B)
      )

opaque

  -- Validity of equality preservation for Π and Σ, seen as term
  -- formers.

  ΠΣ-congᵗᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ ∷ U →
    Γ ∙ A₁ ⊩ᵛ⟨ l′ ⟩ B₁ ≡ B₂ ∷ U →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷ U
  ΠΣ-congᵗᵛ {l} ok A₁≡A₂ B₁≡B₂ =
    case wf-⊩ᵛ≡∷ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡∷ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ∷ (⊩ᵛ≡∷U→⊩ᵛ≡ {l′ = l} A₁≡A₂) ⊩B₂ of λ
      ⊩B₂ →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ΠΣᵗᵛ ok ⊩A₁ ⊩B₁
      , ΠΣᵗᵛ ok ⊩A₂ ⊩B₂
      , ⊩ΠΣ≡ΠΣ∷U ok A₁≡A₂ B₁≡B₂ ∘→ refl-⊩ˢ≡∷
      )
