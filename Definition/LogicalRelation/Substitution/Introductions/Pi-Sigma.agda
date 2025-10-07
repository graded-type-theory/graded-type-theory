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
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  n κ                       : Nat
  ∇                         : DCon (Term 0) _
  Δ Η                       : Con Term _
  Γ                         : Cons _ _
  A A₁ A₂ B B₁ B₂ C t t₁ t₂ : Term _
  σ σ₁ σ₂                   : Subst _ _
  p p₁ p₂ q q₁ q₂           : M
  l l′ l₁ l₁′ l₂ l₂′        : Universe-level
  b b₁ b₂                   : BinderMode

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_ wf-⊩≡∷

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ΠΣ⇔ :
    {A : Term n} {B : Term (1+ n)} →
    ∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (∇ » Δ ⊢≅ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ×
     (∀ {κ′} {∇′ : DCon (Term 0) κ′} → » ∇′ ⊇ ∇ →
      ∀ {m} {ρ : Wk m n} {Η : Con Term m} →
      ∇′ » ρ ∷ʷʳ Η ⊇ Δ →
      ∇′ » Η ⊩⟨ l ⟩ wk ρ A ×
      (∀ {t u} →
       ∇′ » Η ⊩⟨ l ⟩ t ≡ u ∷ wk ρ A →
       ∇′ » Η ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B [ u ]₀)))
  ⊩ΠΣ⇔ {n} {b} {p} {q} {A} {B} =
      (λ ⊩AB →
        case B-view ⊩AB of λ {
          (Bᵣ (Bᵣ _ _ ⇒*ΠΣ ΠΣ≅ΠΣ ⊩wk-A ⊩wk-B wk-B≡wk-B _)) →
        case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ ΠΣₙ of λ {
          (PE.refl , PE.refl , _) →
          ΠΣ≅ΠΣ
        , λ ξ⊇ ρ⊇ →
            let ⊩wk-ρ-A = ⊩wk-A ξ⊇ ρ⊇ in
              ⊩wk-ρ-A
            , λ t≡u′@(⊩wk-ρ-A′ , t≡u) →
                let (_ , ⊩t) , (_ , ⊩u) = wf-⊩≡∷ t≡u′
                    ⊩t = irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩t
                    ⊩u = irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩u
                in
                  ⊩wk-B ξ⊇ ρ⊇ ⊩t
                , ⊩wk-B ξ⊇ ρ⊇ ⊩u
                , wk-B≡wk-B ξ⊇ ρ⊇ ⊩t ⊩u
                    (irrelevanceEqTerm ⊩wk-ρ-A′ ⊩wk-ρ-A t≡u) }})
    , (λ (ΠΣ≅ΠΣ , rest) →
         let ⊢ΠΣ , _    = wf-⊢≡ (≅-eq ΠΣ≅ΠΣ)
             _ , _ , ok = inversion-ΠΣ ⊢ΠΣ
         in
         Bᵣ (BM b p q)
           (Bᵣ _ _ (id ⊢ΠΣ) ΠΣ≅ΠΣ
              (λ ξ⊇ ρ⊇ → rest ξ⊇ ρ⊇ .proj₁)
              (λ ξ⊇ ρ⊇ ⊩t →
                 wf-⊩≡
                   (rest ξ⊇ ρ⊇ .proj₂ $
                    refl-⊩≡∷ (rest ξ⊇ _ .proj₁ , ⊩t))
                   .proj₁)
              (λ ξ⊇ ρ⊇ ⊩t _ t≡u →
                 ⊩≡→⊩≡/
                   (wf-⊩≡
                      (rest ξ⊇ ρ⊇ .proj₂ $
                       refl-⊩≡∷ (rest ξ⊇ _ .proj₁ , ⊩t))
                      .proj₁) $
                 rest ξ⊇ ρ⊇ .proj₂ (rest ξ⊇ _ .proj₁ , t≡u))
              ok))

opaque

  -- A variant of ⊩ΠΣ⇔.

  ⊩ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    ΠΣ-allowed b p q ×
    Γ ⊩⟨ l ⟩ A × (⦃ inc : Var-included ⦄ → Γ »∙ A ⊩⟨ l ⟩ B)
  ⊩ΠΣ→ ⊩ΠΣ =
    let ⊢A , _ , ok  = inversion-ΠΣ (escape-⊩ ⊩ΠΣ)
        _ , hyp      = ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ
        ⊩wk-id-A , _ = hyp id⊇ (id (wf ⊢A))
        ⊩A           = PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩wk-id-A
    in
        ok , ⊩A
      , (case hyp id⊇ (includedʷʳ (TW.stepʷ TW.id (escape-⊩ ⊩A))) of λ
           (⊩wk₁-A , wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀) →
         PE.subst (_⊩⟨_⟩_ _ _) (wkSingleSubstId _)
           (proj₁ $ wf-⊩≡ $
            wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀ $
            refl-⊩≡∷ (⊩var here ⊩wk₁-A)))

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡⇔ :
    {C : Term n} →
    ∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C ⇔
    (∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ×
     ∇ » Δ ⊩⟨ l ⟩ C ×
     ∃₂ λ A′ B′ → ∇ » Δ ⊢ C ⇒* ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     ∇ » Δ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≅ ΠΣ⟨ b ⟩ p , q ▷ A′ ▹ B′ ×
     (∀ {κ′} {∇′ : DCon (Term 0) κ′} → » ∇′ ⊇ ∇ →
      ∀ {m} {ρ : Wk m n} {Η : Con Term m} →
      ∇′ » ρ ∷ʷʳ Η ⊇ Δ →
      ∇′ » Η ⊩⟨ l ⟩ wk ρ A ≡ wk ρ A′ ×
      (∀ {t} →
       ∇′ » Η ⊩⟨ l ⟩ t ∷ wk ρ A →
       ∇′ » Η ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B′ [ t ]₀)))
  ⊩ΠΣ≡⇔ =
      (λ (⊩ΠΣ , ⊩C , ΠΣ≡C) →
         case B-view ⊩ΠΣ of λ {
           (Bᵣ (Bᵣ _ _ ⇒*ΠΣ _ ⊩wk-A ⊩wk-B _ ok)) →
         case ΠΣ≡C of λ
           (B₌ _ _ ⇒*ΠΣ′ ΠΣ≅ΠΣ wk-A≡wk-A′ wk-B≡wk-B′) →
         case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ ΠΣₙ of λ {
           (PE.refl , PE.refl , _) →
           ⊩ΠΣ , ⊩C
          , _ , _ , ⇒*ΠΣ′ , ΠΣ≅ΠΣ
          , λ ξ⊇ ρ⊇ →
              case ⊩ΠΣ⇔ .proj₁ (wf-⊩≡ (⊩-⇒* ⇒*ΠΣ′ ⊩C) .proj₂)
                    .proj₂ ξ⊇ ρ⊇ of λ
                (⊩wk-ρ-A′ , wk-ρ⇑-B′≡wk-ρ⇑-B′) →
              case ⊩wk-A ξ⊇ ρ⊇ , ⊩wk-ρ-A′ , wk-A≡wk-A′ ξ⊇ ρ⊇ of λ
                wk-ρ-A≡wk-ρ-A′ →
                wk-ρ-A≡wk-ρ-A′
              , λ ⊩t@(⊩wk-ρ-A , ⊩t′) →
                  let ⊩wk-ρ⇑-B[t] =
                        ⊩wk-B ξ⊇ ρ⊇
                          (irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ξ⊇ ρ⊇) ⊩t′)
                      ⊩wk-ρ⇑-B[t]′ = ⊩wk-ρ⇑-B[t]
                  in
                    ⊩wk-ρ⇑-B[t]′
                  , wf-⊩≡
                      (wk-ρ⇑-B′≡wk-ρ⇑-B′ $
                      refl-⊩≡∷ (conv-⊩∷ wk-ρ-A≡wk-ρ-A′ ⊩t))
                      .proj₁
                  , irrelevanceEq ⊩wk-ρ⇑-B[t] ⊩wk-ρ⇑-B[t]′
                      (wk-B≡wk-B′ ξ⊇ ρ⊇ $
                      irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ξ⊇ ρ⊇) ⊩t′) }})
    , (λ (⊩ΠΣ , ⊩C , _ , _ , C⇒* , ΠΣ≅ΠΣ , rest) →
         case B-view ⊩ΠΣ of λ {
           (Bᵣ ⊩ΠΣ₁@(Bᵣ _ _ ⇒*ΠΣ₁ _ ⊩wk-A₁ ⊩wk-B₁ _ ok)) →
         case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ₁ ΠΣₙ of λ {
           (PE.refl , PE.refl , _) →
         Bᵣ _ ⊩ΠΣ₁ , ⊩C ,
         (_ ⊩⟨ _ ⟩ _ ≡ _ / Bᵣ _ ⊩ΠΣ₁ ∋
         B₌ _ _ C⇒* ΠΣ≅ΠΣ
           (λ ξ⊇ ρ⊇ → ⊩≡→⊩≡/ (⊩wk-A₁ ξ⊇ ρ⊇) (rest ξ⊇ ρ⊇ .proj₁))
           (λ ξ⊇ ρ⊇ ⊩t →
             case rest ξ⊇ ρ⊇ of λ
               (wk-ρ-A₁≡wk-ρ-A₂ , wk-ρ⇑-B₁≡wk-ρ⇑-B₂) →
             case wf-⊩≡ wk-ρ-A₁≡wk-ρ-A₂ .proj₁ of λ
               ⊩wk-ρ-A₁ →
             ⊩≡→⊩≡/ (⊩wk-B₁ ξ⊇ ρ⊇ ⊩t) $
             wk-ρ⇑-B₁≡wk-ρ⇑-B₂
               ( ⊩wk-ρ-A₁
               , irrelevanceTerm (⊩wk-A₁ ξ⊇ ρ⊇) ⊩wk-ρ-A₁ ⊩t
               ))) }})

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡ΠΣ⇔ :
    {A₁ A₂ : Term n} {B₁ B₂ : Term (1+ n)} →
    ∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ⇔
    (∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
     ∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     ∇ » Δ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≅ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
     (∀ {κ′} {∇′ : DCon (Term 0) κ′} → » ∇′ ⊇ ∇ →
      ∀ {m} {ρ : Wk m n} {Η : Con Term m} →
      ∇′ » ρ ∷ʷʳ Η ⊇ Δ →
      ∇′ » Η ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
      (∀ {t} →
       ∇′ » Η ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
       ∇′ » Η ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀)))
  ⊩ΠΣ≡ΠΣ⇔
    {n} {∇} {Δ} {l} {b₁} {p₁} {q₁} {b₂} {p₂} {q₂} {A₁} {A₂} {B₁} {B₂} =

    ∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂  ⇔⟨ ⊩ΠΣ≡⇔ ⟩

    (∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
     ∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
     ∃₂ λ A B →
     ∇ » Δ ⊢ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ⇒* ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A ▹ B ×
     ∇ » Δ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≅ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A ▹ B ×
     (∀ {κ′} {∇′ : DCon (Term 0) κ′} → » ∇′ ⊇ ∇ →
      ∀ {m} {ρ : Wk m n} {Η : Con Term m} →
      ∇′ » ρ ∷ʷʳ Η ⊇ Δ →
      ∇′ » Η ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A ×
      (∀ {t} →
       ∇′ » Η ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
       ∇′ » Η ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B [ t ]₀)))      ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ ⊩ΠΣ₂ →
                                                                                (λ (_ , _ , ΠΣ⇒*ΠΣ , ΠΣ≅ΠΣ , rest) →
                                                                                   case whnfRed* ΠΣ⇒*ΠΣ ΠΣₙ of λ {
                                                                                     PE.refl →
                                                                                   ΠΣ≅ΠΣ , PE.refl , PE.refl , PE.refl , rest })
                                                                              , (λ { (ΠΣ≅ΠΣ , PE.refl , PE.refl , PE.refl , rest) →
                                                                                      _ , _ , id (escape-⊩ ⊩ΠΣ₂) , ΠΣ≅ΠΣ , rest })) ⟩
    ∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ×
    ∇ » Δ ⊩⟨ l ⟩ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
    ∇ » Δ ⊢ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≅ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ ×
    b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
    (∀ {κ′} {∇′ : DCon (Term 0) κ′} → » ∇′ ⊇ ∇ →
     ∀ {m} {ρ : Wk m n} {Η : Con Term m} →
     ∇′ » ρ ∷ʷʳ Η ⊇ Δ →
     ∇′ » Η ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
     (∀ {t} →
      ∇′ » Η ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
      ∇′ » Η ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀))       □⇔

opaque

  -- A variant of ⊩ΠΣ≡ΠΣ⇔.

  ⊩ΠΣ≡ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂ ▹ B₂ →
    ΠΣ-allowed b₁ p₁ q₁ × b₁ PE.≡ b₂ × p₁ PE.≡ p₂ × q₁ PE.≡ q₂ ×
    Γ ⊩⟨ l ⟩ A₁ ≡ A₂ ×
    (⦃ inc : Var-included ⦄ → Γ »∙ A₁ ⊩⟨ l ⟩ B₁ ≡ B₂)
  ⊩ΠΣ≡ΠΣ→ ΠΣ≡ΠΣ =
    let ⊩ΠΣ₁ , _ , ΠΣ≅ΠΣ , b₁≡b₂ , p₁≡p₂ , q₁≡q₂ , rest =
          ⊩ΠΣ≡ΠΣ⇔ .proj₁ ΠΣ≡ΠΣ
        ok , ⊩A₁ , _ = ⊩ΠΣ→ ⊩ΠΣ₁
    in
      ok , b₁≡b₂ , p₁≡p₂ , q₁≡q₂
    , PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wk-id _) (wk-id _)
        (rest id⊇ (id (wfEq (≅-eq ΠΣ≅ΠΣ))) .proj₁)
    , let wk₁-A₁≡wk₁-A₂ ,
            wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀ =
            rest id⊇ (includedʷʳ (TW.stepʷ TW.id (escape ⊩A₁)))
      in
      PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wkSingleSubstId _) (wkSingleSubstId _)
        (wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀ $
         ⊩var here (wf-⊩≡ wk₁-A₁≡wk₁-A₂ .proj₁))

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
                   rest₁ id⊇ (id ⊢Γ) .proj₂ $
                   PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk-id _) $
                   level-⊩≡∷ ⊩A₁ t₁≡t₂ ⟩⊩
    B₁ [ t₂ ]₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₂) $
                   rest id⊇ (id ⊢Γ) .proj₂ $
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
    ∇ » Δ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A →
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B →
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) [ σ ]
  ⊩ΠΣ {A} {B} ⊢ΠΣ ⊩A ⊩B ⊩σ =
    ⊩ΠΣ⇔ .proj₂
      ( with-inc-⊢≅ (refl $ subst-⊢ ⊢ΠΣ (escape-⊩ˢ∷ ⊩σ .proj₂))
          (≅-ΠΣ-cong
             (R.escape-⊩≡ $
              R.refl-⊩≡ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ)
             (R.escape-⊩≡ ⦃ inc = included ⦄ $
              R.refl-⊩≡ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩B (⊩ˢ∷-liftSubst ⊩A ⊩σ)))
             (inversion-ΠΣ ⊢ΠΣ .proj₂ .proj₂))
      , λ ξ⊇ ρ⊇ →
          let instance
                inc = wk-Var-included-or-empty← ρ⊇
              ρ⊇ = ∷ʷʳ⊇→∷ʷ⊇ ρ⊇
              ⊩A = defn-wk-⊩ᵛ ξ⊇ ⊩A
              ⊩B = defn-wk-⊩ᵛ ξ⊇ ⊩B
              ⊩σ = defn-wk-⊩ˢ∷ ξ⊇ ⊩σ
          in
            PE.subst (_⊩⟨_⟩_ _ _) (PE.sym $ wk-subst A)
              (R.⊩→ $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ ⊩ˢ∷-•ₛ ρ⊇ ⊩σ)
          , λ t≡u →
              PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ singleSubstWkComp _ _ B)
                (PE.sym $ singleSubstWkComp _ _ B) $
              R.⊩≡→ $
              ⊩ᵛ⇔ .proj₁ ⊩B .proj₂ id⊇ $
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
    ∇ » Δ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
    ∇ » Δ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    ∇ » Δ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ]
  ⊩ΠΣ≡ΠΣ {A₁} {B₁} {A₂} {B₂} ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂ ⦃ inc ⦄ σ₁≡σ₂ =
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
      ( ⊩ΠΣ ⊢ΠΣ₁ ⊩A₁ ⊩B₁ ⊩σ₁
      , ⊩ΠΣ ⊢ΠΣ₂ ⊩A₂ ⊩B₂ ⊩σ₂
      , with-inc-⊢≅ (subst-⊢≡ ΠΣ≡ΠΣ (escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂))
          (≅-ΠΣ-cong
             (R.escape-⊩≡ $
              ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ σ₁≡σ₂)
             (R.escape-⊩≡ ⦃ inc = included ⦄ $
              ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
              ⊩ˢ≡∷-liftSubst ⊩A₁ σ₁≡σ₂)
             (inversion-ΠΣ ⊢ΠΣ₁ .proj₂ .proj₂))
      , PE.refl , PE.refl , PE.refl
      , λ ξ⊇ ρ⊇ →
          let instance
                inc = wk-Var-included-or-empty← ρ⊇
              ρ⊇ = ∷ʷʳ⊇→∷ʷ⊇ ρ⊇
              A₁≡A₂ = defn-wk-⊩ᵛ≡ ξ⊇ A₁≡A₂
              B₁≡B₂ = defn-wk-⊩ᵛ≡ ξ⊇ B₁≡B₂
              σ₁≡σ₂ = defn-wk-⊩ˢ≡∷ ξ⊇ σ₁≡σ₂
          in
            PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
              (PE.sym $ wk-subst A₁) (PE.sym $ wk-subst A₂)
              (R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ $ ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂)
          , λ ⊩t →
              PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ singleSubstWkComp _ _ B₁)
                (PE.sym $ singleSubstWkComp _ _ B₂) $
              R.⊩≡→ $
              ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ( _ , defn-wk-⊩ᵛ ξ⊇ ⊩A₁
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
    Γ »∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂
  ΠΣ-congᵛ ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂ =
    ⊩ᵛ≡⇔ʰ .proj₂ $
      ( wf-⊩ᵛ (wf-⊩ᵛ≡ A₁≡A₂ .proj₁)
      , λ ξ⊇ → ⊩ΠΣ≡ΠΣ (defn-wkEq ξ⊇ ΠΣ≡ΠΣ)
                      (defn-wk-⊩ᵛ≡ ξ⊇ A₁≡A₂)
                      (defn-wk-⊩ᵛ≡ ξ⊇ B₁≡B₂)
      )

opaque

  -- Validity of Π and Σ, seen as type formers.

  ΠΣᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  ΠΣᵛ ⊢ΠΣ ⊩A ⊩B =
    ⊩ᵛ⇔⊩ᵛ≡ .proj₂ $ ΠΣ-congᵛ (refl ⊢ΠΣ) (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡ ⊩B)

opaque

  -- A kind of inversion lemma for Π- and Σ-types.

  ⊩ᵛΠΣ→ :
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    (⦃ inc : Var-included or-empty (Γ .vars) ⦄ → ΠΣ-allowed b p q) ×
    Γ ⊩ᵛ⟨ l ⟩ A × Γ »∙ A ⊩ᵛ⟨ l ⟩ B
  ⊩ᵛΠΣ→ {B} ⊩ΠΣAB =
    case ⊩ᵛ⇔ʰ .proj₁ ⊩ΠΣAB of λ
      (⊩Γ , ΠΣAB≡ΠΣAB) →
    case ⊩ᵛ⇔ʰ .proj₂
           ( ⊩Γ
           , λ ξ⊇ → proj₁ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→ proj₂ ∘→
                    ⊩ΠΣ≡ΠΣ→ ∘→ ΠΣAB≡ΠΣAB ξ⊇
           ) of λ
      ⊩A →
      ⊩ΠΣ→ (R.⊩→ (⊩ᵛ→⊩ ⊩ΠΣAB)) .proj₁
    , ⊩A
    , ⊩ᵛ⇔ʰ .proj₂
        ( ⊩ᵛ-∙-intro ⊩A
        , λ {_ _} ξ⊇ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
            case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
              ((_ , _ , head-σ₁≡head-σ₂) , tail-σ₁≡tail-σ₂) →
            B [ σ₁ ]                             ≡˘⟨ substVar-to-subst consSubst-η B ⟩⊩≡
            B [ consSubst (tail σ₁) (head σ₁) ]  ≡˘⟨ singleSubstComp _ _ B ⟩⊩≡
            B [ tail σ₁ ⇑ ] [ head σ₁ ]₀         ≡⟨ ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (ΠΣAB≡ΠΣAB ξ⊇ tail-σ₁≡tail-σ₂) (R.⊩≡∷→ head-σ₁≡head-σ₂) ⟩⊩∎≡
            B [ tail σ₂ ⇑ ] [ head σ₂ ]₀         ≡⟨ singleSubstComp _ _ B ⟩
            B [ consSubst (tail σ₂) (head σ₂) ]  ≡⟨ substVar-to-subst consSubst-η B ⟩
            B [ σ₂ ]                             ∎
        )
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛΠΣ⇔ :
    ⦃ inc : Var-included ⦄ →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (ΠΣ-allowed b p q × Γ ⊩ᵛ⟨ l ⟩ A × Γ »∙ A ⊩ᵛ⟨ l ⟩ B)
  ⊩ᵛΠΣ⇔ {B} =
      Σ.map (λ ok → ok ⦃ inc = included ⦄) idᶠ ∘→ ⊩ᵛΠΣ→
    , (λ (ok , ⊩A , ⊩B) →
         ΠΣᵛ (ΠΣⱼ (escape-⊩ᵛ ⦃ inc = included ⦄ ⊩B) ok) ⊩A ⊩B)
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Validity of Π and Σ, seen as term formers

opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as term
  -- formers.

  ⊩ΠΣ≡ΠΣ∷U :
    ∇ » Δ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷
      U (l₁ ⊔ᵘ l₂) →
    ∇ » Δ ⊩ᵛ⟨ l₁′ ⟩ A₁ ≡ A₂ ∷ U l₁ →
    ∇ » Δ ∙ A₁ ⊩ᵛ⟨ l₂′ ⟩ B₁ ≡ B₂ ∷ U l₂ →
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ 1+ (l₁ ⊔ᵘ l₂) ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ] ∷ U (l₁ ⊔ᵘ l₂)
  ⊩ΠΣ≡ΠΣ∷U ΠΣ≡ΠΣ A₁≡A₂∷U B₁≡B₂∷U σ₁≡σ₂ =
    case ⊩ᵛ≡∷U→⊩ᵛ≡ A₁≡A₂∷U of λ
      A₁≡A₂ →
    case ⊩ᵛ≡∷U→⊩ᵛ≡ B₁≡B₂∷U of λ
      B₁≡B₂ →
    case ⊩ᵛ≡∷⇔ .proj₁ A₁≡A₂∷U .proj₂ id⊇ σ₁≡σ₂ of λ
      A₁[σ₁]≡A₂[σ₂]∷U →
    case ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ B₁≡B₂∷U σ₁≡σ₂ of λ
      B₁[σ₁⇑]≡B₂[σ₂⇑]∷U →
    Type→⊩≡∷U⇔ ΠΣₙ ΠΣₙ .proj₂
      ( ≤ᵘ-refl
      , (R.⊩≡→ $
         ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[]
           (ΠΣ-congᵛ (univ ΠΣ≡ΠΣ) (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘʳ A₁≡A₂)
              (emb-⊩ᵛ≡ ≤ᵘ⊔ᵘˡ B₁≡B₂))
           σ₁≡σ₂)
      , with-inc-⊢≅∷ (subst-⊢≡∷ ΠΣ≡ΠΣ (escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂))
          (let _ , _ , ok =
                 inversion-ΠΣ (wf-⊢≡ (univ ΠΣ≡ΠΣ) .proj₁)
           in
           ≅ₜ-ΠΣ-cong (R.escape-⊩≡∷ A₁[σ₁]≡A₂[σ₂]∷U)
             (R.escape-⊩≡∷ ⦃ inc = included ⦄ B₁[σ₁⇑]≡B₂[σ₂⇑]∷U) ok)
      )

opaque

  -- Validity of equality preservation for Π and Σ, seen as term
  -- formers.

  ΠΣ-congᵗᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷
      U (l₁ ⊔ᵘ l₂) →
    Γ ⊩ᵛ⟨ l₁′ ⟩ A₁ ≡ A₂ ∷ U l₁ →
    Γ »∙ A₁ ⊩ᵛ⟨ l₂′ ⟩ B₁ ≡ B₂ ∷ U l₂ →
    Γ ⊩ᵛ⟨ 1+ (l₁ ⊔ᵘ l₂) ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡
      ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷ U (l₁ ⊔ᵘ l₂)
  ΠΣ-congᵗᵛ ΠΣ≡ΠΣ A₁≡A₂ B₁≡B₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛU (wf-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ A₁≡A₂ .proj₁)))
      , λ ξ⊇ → ⊩ΠΣ≡ΠΣ∷U (defn-wkEqTerm ξ⊇ ΠΣ≡ΠΣ)
                        (defn-wk-⊩ᵛ≡∷ ξ⊇ A₁≡A₂)
                        (defn-wk-⊩ᵛ≡∷ ξ⊇ B₁≡B₂)
      )

opaque

  -- Validity of Π and Σ, seen as term formers.

  ΠΣᵗᵛ :
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U (l₁ ⊔ᵘ l₂) →
    Γ ⊩ᵛ⟨ l₁′ ⟩ A ∷ U l₁ →
    Γ »∙ A ⊩ᵛ⟨ l₂′ ⟩ B ∷ U l₂ →
    Γ ⊩ᵛ⟨ 1+ (l₁ ⊔ᵘ l₂) ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U (l₁ ⊔ᵘ l₂)
  ΠΣᵗᵛ ⊢ΠΣ ⊩A ⊩B =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ⊩ᵛU (wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩A))
      , λ ξ⊇ → ⊩ΠΣ≡ΠΣ∷U (refl (defn-wkTerm ξ⊇ ⊢ΠΣ))
                        (refl-⊩ᵛ≡∷ (defn-wk-⊩ᵛ∷ ξ⊇ ⊩A))
                        (refl-⊩ᵛ≡∷ (defn-wk-⊩ᵛ∷ ξ⊇ ⊩B))
      )
