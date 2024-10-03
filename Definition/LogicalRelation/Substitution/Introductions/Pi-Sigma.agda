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
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Var R
import Definition.LogicalRelation.Weakening R as W
open import Definition.LogicalRelation.Weakening.Restricted R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
import Definition.Typed.Weakening R as TW
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  n                         : Nat
  Γ Δ                       : Con Term _
  A A₁ A₂ B B₁ B₂ C t t₁ t₂ : Term _
  σ σ₁ σ₂                   : Subst _ _
  p p₁ p₂ q q₁ q₂           : M
  l l′ l₁ l₁′ l₂ l₂′        : Universe-level
  b b₁ b₂                   : BinderMode

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ΠΣ⇔ :
    {A : Term n} {B : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (Γ ⊢≅ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷʳ Δ ⊇ Γ →
      Δ ⊩⟨ l ⟩ wk ρ A ×
      (∀ {t u} →
       Δ ⊩⟨ l ⟩ t ≡ u ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B [ u ]₀)))
  ⊩ΠΣ⇔ {n} {b} {p} {q} {A} {B} =
      lemma ∘→ B-elim _
    , (λ (ΠΣ≅ΠΣ , rest) →
         let ⊢ΠΣ , _    = wf-⊢≡ (≅-eq ΠΣ≅ΠΣ)
             _ , _ , ok = inversion-ΠΣ ⊢ΠΣ
         in
         Bᵣ (BM b p q)
           (Bᵣ _ _ (id ⊢ΠΣ) ΠΣ≅ΠΣ
              (λ ρ⊇ → rest ρ⊇ .proj₁)
              (λ ρ⊇ ⊩t →
                 wf-⊩≡
                   (rest ρ⊇ .proj₂ $
                    refl-⊩≡∷ (rest _ .proj₁ , ⊩t))
                   .proj₁)
              (λ ρ⊇ ⊩t ⊩u t≡u →
                 ⊩≡→⊩≡/
                   (wf-⊩≡
                      (rest ρ⊇ .proj₂ $
                       refl-⊩≡∷ (rest _ .proj₁ , ⊩t))
                      .proj₁) $
                 rest ρ⊇ .proj₂ (rest _ .proj₁ , ⊩t , ⊩u , t≡u))
              ok))
    where
    lemma :
      Γ ⊩⟨ l ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
      Γ ⊢≅ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ×
      (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
       ρ ∷ʷʳ Δ ⊇ Γ →
       Δ ⊩⟨ l ⟩ wk ρ A ×
       (∀ {t u} →
        Δ ⊩⟨ l ⟩ t ≡ u ∷ wk ρ A →
        Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B [ u ]₀))
    lemma (emb p ⊩ΠΣ) =
      case lemma ⊩ΠΣ of λ
        (B≅B , rest) →
        B≅B
      , λ ρ⊇ →
          case rest ρ⊇ of λ
            (⊩A , B≡B) →
            emb p (PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ p) ⊩A)
          , emb-⊩≡ (<ᵘ→≤ᵘ p) ∘→ B≡B ∘→ level-⊩≡∷ ⊩A
    lemma (noemb (Bᵣ _ _ ⇒*ΠΣ ΠΣ≅ΠΣ ⊩wk-A ⊩wk-B wk-B≡wk-B _)) =
      case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
        ΠΣ≅ΠΣ
      , λ ρ⊇ →
          let ⊩wk-ρ-A = ⊩wk-A ρ⊇ in
            ⊩wk-ρ-A
          , λ (⊩wk-ρ-A′ , ⊩t , ⊩u , t≡u) →
              case irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩t of λ
                ⊩t →
              case irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩u of λ
                ⊩u →
                ⊩wk-B ρ⊇ ⊩t
              , ⊩wk-B ρ⊇ ⊩u
              , wk-B≡wk-B ρ⊇ ⊩t ⊩u
                  (irrelevanceEqTerm ⊩wk-ρ-A′ ⊩wk-ρ-A t≡u) }

opaque

  -- A variant of ⊩ΠΣ⇔.

  ⊩ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    ΠΣ-allowed b p q ×
    Γ ⊩⟨ l ⟩ A × (Neutrals-included → Γ ∙ A ⊩⟨ l ⟩ B)
  ⊩ΠΣ→ ⊩ΠΣ =
    let ⊢A , _ , ok  = inversion-ΠΣ (escape-⊩ ⊩ΠΣ)
        _ , hyp      = ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ
        ⊩wk-id-A , _ = hyp (id (wf ⊢A))
        ⊩A           = PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩wk-id-A
    in
        ok , ⊩A
      , λ inc →
        case hyp (included inc (TW.stepʷ TW.id (escape-⊩ ⊩A))) of λ
          (⊩wk₁-A , wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀) →
        PE.subst (_⊩⟨_⟩_ _ _) (wkSingleSubstId _)
          (proj₁ $ wf-⊩≡ $
           wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀ $
           refl-⊩≡∷ (⊩var inc here ⊩wk₁-A))

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡⇔ :
    {C : Term n} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C ⇔
    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ×
     Γ ⊩⟨ l ⟩ C ×
     ∃₂ λ A′ B′ → Γ ⊢ C ⇒* ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≅ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷʳ Δ ⊇ Γ →
      Δ ⊩⟨ l ⟩ wk ρ A ≡ wk ρ A′ ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B′ [ t ]₀)))
  ⊩ΠΣ≡⇔ =
      (λ (⊩ΠΣ , ⊩C , ΠΣ≡C) →
         case B-elim _ ⊩ΠΣ of λ
           ⊩ΠΣ′ →
           ⊩ΠΣ , ⊩C
         , lemma₁ ≤ᵘ-refl ⊩ΠΣ′ ⊩C
             (irrelevanceEq ⊩ΠΣ (B-intr _ ⊩ΠΣ′) ΠΣ≡C))
    , (λ (⊩ΠΣ , ⊩C , _ , _ , C⇒* , ΠΣ≅ΠΣ , rest) →
         case B-elim _ ⊩ΠΣ of λ
           ⊩ΠΣ′ →
         B-intr _ ⊩ΠΣ′ , ⊩C , lemma₂ ⊩ΠΣ′ C⇒* ΠΣ≅ΠΣ rest)
    where
    lemma₁ :
      l′ ≤ᵘ l →
      (⊩ΠΣ : Γ ⊩⟨ l′ ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) →
      Γ ⊩⟨ l ⟩ C →
      Γ ⊩⟨ l′ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C / B-intr _ ⊩ΠΣ →
      ∃₂ λ A′ B′ → Γ ⊢ C ⇒* ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
      Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≅ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
      (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
       ρ ∷ʷʳ Δ ⊇ Γ →
       Δ ⊩⟨ l ⟩ wk ρ A ≡ wk ρ A′ ×
       (∀ {t} →
        Δ ⊩⟨ l ⟩ t ∷ wk ρ A →
        Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B′ [ t ]₀))
    lemma₁ l′≤l (emb l″<l′ ⊩ΠΣ₁) ⊩ΠΣ₂ ΠΣ≡ΠΣ =
      lemma₁ (≤ᵘ-trans (<ᵘ→≤ᵘ l″<l′) l′≤l) ⊩ΠΣ₁ ⊩ΠΣ₂
        (irrelevanceEq (B-intr _ (emb l″<l′ ⊩ΠΣ₁)) (B-intr _ ⊩ΠΣ₁)
           ΠΣ≡ΠΣ)
    lemma₁
      l′≤l (noemb (Bᵣ _ _ ⇒*ΠΣ _ ⊩wk-A ⊩wk-B _ ok)) ⊩C
      (B₌ _ _ ⇒*ΠΣ′ ΠΣ≅ΠΣ wk-A≡wk-A′ wk-B≡wk-B′) =
      case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
        _ , _ , ⇒*ΠΣ′ , ΠΣ≅ΠΣ
      , λ ρ⊇ →
          case ⊩ΠΣ⇔ .proj₁ (wf-⊩≡ (⊩-⇒* ⇒*ΠΣ′ ⊩C) .proj₂)
                 .proj₂ ρ⊇ of λ
            (⊩wk-ρ-A′ , wk-ρ⇑-B′≡wk-ρ⇑-B′) →
          case   emb-≤-⊩ l′≤l (⊩wk-A ρ⊇)
               , ⊩wk-ρ-A′
               , emb-≤-⊩≡ (wk-A≡wk-A′ ρ⊇) of λ
            wk-ρ-A≡wk-ρ-A′ →
            wk-ρ-A≡wk-ρ-A′
          , λ ⊩t@(⊩wk-ρ-A , ⊩t′) →
              let ⊩wk-ρ⇑-B[t] =
                    ⊩wk-B ρ⊇ (irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ρ⊇) ⊩t′)
                  ⊩wk-ρ⇑-B[t]′ = emb-≤-⊩ l′≤l ⊩wk-ρ⇑-B[t]
              in
                ⊩wk-ρ⇑-B[t]′
              , wf-⊩≡
                  (wk-ρ⇑-B′≡wk-ρ⇑-B′ $
                   refl-⊩≡∷ (conv-⊩∷ wk-ρ-A≡wk-ρ-A′ ⊩t))
                  .proj₁
              , irrelevanceEq ⊩wk-ρ⇑-B[t] ⊩wk-ρ⇑-B[t]′
                  (wk-B≡wk-B′ ρ⊇ $
                   irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ρ⊇) ⊩t′) }

    lemma₂ :
      (⊩ΠΣ : Γ ⊩⟨ l′ ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) →
      Γ ⊢ C ⇒* ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
      Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≅ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
      (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
       ρ ∷ʷʳ Δ ⊇ Γ →
       Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
       (∀ {t} →
        Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
        Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀)) →
      Γ ⊩⟨ l′ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ C / B-intr _ ⊩ΠΣ
    lemma₂ (emb ≤ᵘ-refl     ⊩ΠΣ₁) = lemma₂ ⊩ΠΣ₁
    lemma₂ (emb (≤ᵘ-step p) ⊩ΠΣ₁) = lemma₂ (emb p ⊩ΠΣ₁)
    lemma₂
      (noemb ⊩ΠΣ₁@(Bᵣ _ _ ⇒*ΠΣ₁ _ ⊩wk-A₁ ⊩wk-B₁ _ ok))
      C⇒* ΠΣ≅ΠΣ rest =
      case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ₁ ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      _ ⊩⟨ _ ⟩ _ ≡ _ / Bᵣ _ ⊩ΠΣ₁ ∋
      B₌ _ _ C⇒* ΠΣ≅ΠΣ
        (λ ρ⊇ → ⊩≡→⊩≡/ (⊩wk-A₁ ρ⊇) (rest ρ⊇ .proj₁))
        (λ ρ⊇ ⊩t →
           case rest ρ⊇ of λ
             (wk-ρ-A₁≡wk-ρ-A₂ , wk-ρ⇑-B₁≡wk-ρ⇑-B₂) →
           case wf-⊩≡ wk-ρ-A₁≡wk-ρ-A₂ .proj₁ of λ
             ⊩wk-ρ-A₁ →
           ⊩≡→⊩≡/ (⊩wk-B₁ ρ⊇ ⊩t) $
           wk-ρ⇑-B₁≡wk-ρ⇑-B₂
             ( ⊩wk-ρ-A₁
             , irrelevanceTerm (⊩wk-A₁ ρ⊇) ⊩wk-ρ-A₁ ⊩t
             )) }

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡ΠΣ⇔ :
    {A₁ A₂ : Term n} {B₁ B₂ : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ⇔
    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
     Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     Γ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≅ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷʳ Δ ⊇ Γ →
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
     Γ ⊢ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ⇒* ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A ▹ B ×
     Γ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≅ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A ▹ B ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ʷʳ Δ ⊇ Γ →
      Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B [ t ]₀)))       ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ ⊩ΠΣ₂ →
                                                                            (λ (_ , _ , ΠΣ⇒*ΠΣ , ΠΣ≅ΠΣ , rest) →
                                                                               case whnfRed* ΠΣ⇒*ΠΣ ΠΣₙ of λ {
                                                                                 PE.refl →
                                                                               ΠΣ≅ΠΣ , PE.refl , PE.refl , PE.refl , rest })
                                                                          , (λ { (ΠΣ≅ΠΣ , PE.refl , PE.refl , PE.refl , rest) →
                                                                                  _ , _ , id (escape-⊩ ⊩ΠΣ₂) , ΠΣ≅ΠΣ , rest })) ⟩
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
    Γ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≅ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
    b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
    (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
     ρ ∷ʷʳ Δ ⊇ Γ →
     Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
     (∀ {t} →
      Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
      Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀))        □⇔

opaque

  -- A variant of ⊩ΠΣ≡ΠΣ⇔.

  ⊩ΠΣ≡ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    ΠΣ-allowed b₁ p₁ q₁ × b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ × (Neutrals-included → Γ ∙ A₁ ⊩⟨ l ⟩ B₁ ≡ B₂)
  ⊩ΠΣ≡ΠΣ→ ΠΣ≡ΠΣ =
    let ⊩ΠΣ₁ , _ , ΠΣ≅ΠΣ , b₁≡b₂ , p₁≡p₂ , q₁≡q₂ , rest =
          ⊩ΠΣ≡ΠΣ⇔ .proj₁ ΠΣ≡ΠΣ
        ok , ⊩A₁ , _ = ⊩ΠΣ→ ⊩ΠΣ₁
    in
      ok , b₁≡b₂ , p₁≡p₂ , q₁≡q₂
    , PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wk-id _) (wk-id _)
        (rest (id (wfEq (≅-eq ΠΣ≅ΠΣ))) .proj₁)
    , λ inc →
        let wk₁-A₁≡wk₁-A₂ ,
              wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀ =
              rest (included inc (TW.stepʷ TW.id (escape ⊩A₁)))
        in
        PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wkSingleSubstId _) (wkSingleSubstId _)
          (wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀ $
           ⊩var inc here (wf-⊩≡ wk₁-A₁≡wk₁-A₂ .proj₁))

-- See also ⊩ᵛΠΣ→ and ⊩ᵛΠΣ⇔ below.

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
      (⊩ΠΣ₁ , _ , _ , _ , _ , _ , rest) →
    case ⊩ΠΣ→ ⊩ΠΣ₁ of λ
      (_ , ⊩A₁ , _) →
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ₁ of λ
      (ΠΣ≅ΠΣ , rest₁) →
    case wf (wf-⊢≡ (≅-eq ΠΣ≅ΠΣ) .proj₁) of λ
      ⊢Γ →
    B₁ [ t₁ ]₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁) $
                   rest₁ (id ⊢Γ) .proj₂ $
                   PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk-id _) $
                   level-⊩≡∷ ⊩A₁ t₁≡t₂ ⟩⊩
    B₁ [ t₂ ]₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₂) $
                   rest (id ⊢Γ) .proj₂ $
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
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Neutrals-included-or-empty Δ →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) [ σ ]
  ⊩ΠΣ {A} {B} ⊢ΠΣ ⊩A ⊩B inc ⊩σ =
    ⊩ΠΣ⇔ .proj₂
      ( with-inc-⊢≅ (refl $ subst-⊢ ⊢ΠΣ (escape-⊩ˢ∷ inc ⊩σ .proj₂))
          (λ inc →
             ≅-ΠΣ-cong
               (R.escape-⊩≡ (inj₁ inc) $
                R.refl-⊩≡ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ)
               (R.escape-⊩≡ (inj₁ inc) $
                R.refl-⊩≡ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩B (⊩ˢ∷-liftSubst ⊩A ⊩σ)))
               (inversion-ΠΣ ⊢ΠΣ .proj₂ .proj₂))
      , λ ρ⊇ →
          let inc = wk-Neutrals-included-or-empty ρ⊇ .proj₂ inc
              ρ⊇  = λ _ → ∷ʷʳ⊇→∷ʷ⊇ ρ⊇
          in
            PE.subst (_⊩⟨_⟩_ _ _) (PE.sym $ wk-subst A)
              (R.⊩→ inc $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ ⊩ˢ∷-•ₛ ρ⊇ ⊩σ)
          , λ t≡u →
              PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ singleSubstWkComp _ _ B)
                (PE.sym $ singleSubstWkComp _ _ B) $
              R.⊩≡→ inc $
              ⊩ᵛ⇔ .proj₁ ⊩B .proj₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ( _ , ⊩A
                  , (R.→⊩≡∷ $
                     PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A) t≡u)
                  )
                , refl-⊩ˢ≡∷ (⊩ˢ∷-•ₛ ρ⊇ ⊩σ)
                )
      )

opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as type
  -- formers.

  ⊩ΠΣ≡ΠΣ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Neutrals-included-or-empty Δ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ]
  ⊩ΠΣ≡ΠΣ {A₁} {B₁} {A₂} {B₂} ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂ inc σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ A₁≡A₂ ⊩B₂ of λ
      ⊩B₂ →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case wf-⊢≡ ΠΣ≡ΠΣ of λ
      (⊢ΠΣ₁ , ⊢ΠΣ₂) →
    ⊩ΠΣ≡ΠΣ⇔ .proj₂
      ( ⊩ΠΣ ⊢ΠΣ₁ ⊩A₁ ⊩B₁ inc ⊩σ₁
      , ⊩ΠΣ ⊢ΠΣ₂ ⊩A₂ ⊩B₂ inc ⊩σ₂
      , with-inc-⊢≅ (subst-⊢≡ ΠΣ≡ΠΣ (escape-⊩ˢ≡∷ inc σ₁≡σ₂ .proj₂))
          (λ inc →
             ≅-ΠΣ-cong
               (R.escape-⊩≡ (inj₁ inc) $
                ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ σ₁≡σ₂)
               (R.escape-⊩≡ (inj₁ inc) $
                ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
                ⊩ˢ≡∷-liftSubst ⊩A₁ σ₁≡σ₂)
               (inversion-ΠΣ ⊢ΠΣ₁ .proj₂ .proj₂))
      , PE.refl , PE.refl , PE.refl
      , λ ρ⊇ →
          let inc = wk-Neutrals-included-or-empty ρ⊇ .proj₂ inc
              ρ⊇  = λ _ → ∷ʷʳ⊇→∷ʷ⊇ ρ⊇
          in
            PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
              (PE.sym $ wk-subst A₁) (PE.sym $ wk-subst A₂)
              (R.⊩≡→ inc $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ $ ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂)
          , λ ⊩t →
              PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ singleSubstWkComp _ _ B₁)
                (PE.sym $ singleSubstWkComp _ _ B₂) $
              R.⊩≡→ inc $
              ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ( _ , ⊩A₁
                  , (R.refl-⊩≡∷ $
                     PE.subst (R._⊩⟨_⟩_∷_ _ _ _) (wk-subst A₁) $
                     R.→⊩∷ ⊩t)
                  )
                , ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂
                )
      )

opaque

  -- Validity of equality preservation for Π and Σ, seen as type
  -- formers.

  ΠΣ-congᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂
  ΠΣ-congᵛ ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂ =
    ⊩ᵛ≡⇔ʰ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁)
      , ⊩ΠΣ≡ΠΣ ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂
      )

opaque

  -- Validity of Π and Σ, seen as type formers.

  ΠΣᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  ΠΣᵛ ⊢ΠΣ ⊩A ⊩B =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $ ΠΣ-congᵛ (refl ⊢ΠΣ) (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡ ⊩B)

opaque

  -- A kind of inversion lemma for Π- and Σ-types.

  ⊩ᵛΠΣ→ :
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    (Neutrals-included-or-empty Γ → ΠΣ-allowed b p q) ×
    Γ ⊩ᵛ⟨ l ⟩ A × Γ ∙ A ⊩ᵛ⟨ l ⟩ B
  ⊩ᵛΠΣ→ {B} ⊩ΠΣAB =
    case ⊩ᵛ⇔ʰ .proj₁ ⊩ΠΣAB of λ
      (⊩Γ , ΠΣAB≡ΠΣAB) →
    case ⊩ᵛ⇔ʰ .proj₂
           ( ⊩Γ
           , λ inc →
               proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
               ⊩ΠΣ≡ΠΣ→ ∘→ ΠΣAB≡ΠΣAB inc
           ) of λ
      ⊩A →
      (λ inc → ⊩ΠΣ→ (R.⊩→ inc (⊩ᵛ→⊩ ⊩ΠΣAB)) .proj₁)
    , ⊩A
    , ⊩ᵛ⇔ʰ .proj₂
        ( ⊩ᵛ-∙-intro ⊩A
        , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} inc σ₁≡σ₂ →
            case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
              ((_ , _ , head-σ₁≡head-σ₂) , tail-σ₁≡tail-σ₂) →
            B [ σ₁ ]                             ≡˘⟨ substVar-to-subst consSubst-η B ⟩⊩≡
            B [ consSubst (tail σ₁) (head σ₁) ]  ≡˘⟨ singleSubstComp _ _ B ⟩⊩≡
            B [ tail σ₁ ⇑ ] [ head σ₁ ]₀         ≡⟨ ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (ΠΣAB≡ΠΣAB inc tail-σ₁≡tail-σ₂) (R.⊩≡∷→ inc head-σ₁≡head-σ₂) ⟩⊩∎≡
            B [ tail σ₂ ⇑ ] [ head σ₂ ]₀         ≡⟨ singleSubstComp _ _ B ⟩
            B [ consSubst (tail σ₂) (head σ₂) ]  ≡⟨ substVar-to-subst consSubst-η B ⟩
            B [ σ₂ ]                             ∎
        )
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛΠΣ⇔ :
    Neutrals-included →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (ΠΣ-allowed b p q × Γ ⊩ᵛ⟨ l ⟩ A × Γ ∙ A ⊩ᵛ⟨ l ⟩ B)
  ⊩ᵛΠΣ⇔ {B} inc =
      Σ.map (_$ inj₁ inc) idᶠ ∘→ ⊩ᵛΠΣ→
    , (λ (ok , ⊩A , ⊩B) →
         ΠΣᵛ (ΠΣⱼ (escape-⊩ᵛ (inj₁ inc) ⊩B) ok) ⊩A ⊩B)
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Validity of Π and Σ, seen as term formers

opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as term
  -- formers.

  ⊩ΠΣ≡ΠΣ∷U :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷
      U (l₁ ⊔ᵘ l₂) →
    Γ ⊩ᵛ⟨ l₁′ ⟩ A₁ ≡ A₂ ∷ U l₁ →
    Γ ∙ A₁ ⊩ᵛ⟨ l₂′ ⟩ B₁ ≡ B₂ ∷ U l₂ →
    Neutrals-included-or-empty Δ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ 1+ (l₁ ⊔ᵘ l₂) ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ] ∷ U (l₁ ⊔ᵘ l₂)
  ⊩ΠΣ≡ΠΣ∷U ΠΣ≡ΠΣ A₁≡A₂∷U B₁≡B₂∷U inc σ₁≡σ₂ =
    case ⊩ᵛ≡∷U→⊩ᵛ≡ A₁≡A₂∷U of λ
      A₁≡A₂ →
    case ⊩ᵛ≡∷U→⊩ᵛ≡ B₁≡B₂∷U of λ
      B₁≡B₂ →
    case ⊩ᵛ≡∷⇔ .proj₁ A₁≡A₂∷U .proj₂ σ₁≡σ₂ of λ
      A₁[σ₁]≡A₂[σ₂]∷U →
    case ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ B₁≡B₂∷U σ₁≡σ₂ of λ
      B₁[σ₁⇑]≡B₂[σ₂⇑]∷U →
    Type→⊩≡∷U⇔ ΠΣₙ ΠΣₙ .proj₂
      ( ≤ᵘ-refl
      , (R.⊩≡→ inc $
         ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[]
           (ΠΣ-congᵛ (univ ΠΣ≡ΠΣ) (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘʳ A₁≡A₂)
              (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘˡ B₁≡B₂))
           σ₁≡σ₂)
      , with-inc-⊢≅∷ (subst-⊢≡∷ ΠΣ≡ΠΣ (escape-⊩ˢ≡∷ inc σ₁≡σ₂ .proj₂))
          (λ inc →
             let _ , _ , ok =
                   inversion-ΠΣ (wf-⊢≡ (univ ΠΣ≡ΠΣ) .proj₁)
             in
             ≅ₜ-ΠΣ-cong (R.escape-⊩≡∷ (inj₁ inc) A₁[σ₁]≡A₂[σ₂]∷U)
               (R.escape-⊩≡∷ (inj₁ inc) B₁[σ₁⇑]≡B₂[σ₂⇑]∷U) ok)
      )

opaque

  -- Validity of equality preservation for Π and Σ, seen as term
  -- formers.

  ΠΣ-congᵗᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷
      U (l₁ ⊔ᵘ l₂) →
    Γ ⊩ᵛ⟨ l₁′ ⟩ A₁ ≡ A₂ ∷ U l₁ →
    Γ ∙ A₁ ⊩ᵛ⟨ l₂′ ⟩ B₁ ≡ B₂ ∷ U l₂ →
    Γ ⊩ᵛ⟨ 1+ (l₁ ⊔ᵘ l₂) ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡
      ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷ U (l₁ ⊔ᵘ l₂)
  ΠΣ-congᵗᵛ ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛU (wf-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ A₁≡A₂ .proj₁)))
      , ⊩ΠΣ≡ΠΣ∷U ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂
      )

opaque

  -- Validity of Π and Σ, seen as term formers.

  ΠΣᵗᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U (l₁ ⊔ᵘ l₂) →
    Γ ⊩ᵛ⟨ l₁′ ⟩ A ∷ U l₁ →
    Γ ∙ A ⊩ᵛ⟨ l₂′ ⟩ B ∷ U l₂ →
    Γ ⊩ᵛ⟨ 1+ (l₁ ⊔ᵘ l₂) ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U (l₁ ⊔ᵘ l₂)
  ΠΣᵗᵛ ⊢ΠΣ ⊩A ⊩B =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ⊩ᵛU (wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩A))
      , ⊩ΠΣ≡ΠΣ∷U (refl ⊢ΠΣ) (refl-⊩ᵛ≡∷ ⊩A) (refl-⊩ᵛ≡∷ ⊩B)
      )
