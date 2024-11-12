------------------------------------------------------------------------
-- Validity for Π-types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Pi
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
  Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma R
open import Definition.LogicalRelation.Substitution.Introductions.Var R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction.Primitive R
open import Definition.Typed.Reasoning.Reduction.Well-typed R
open import Definition.Typed.RedSteps R
open import Definition.Typed.Weakening R as W using (_∷ʷ_⊇_)

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  m n                 : Nat
  Γ Δ                 : Con Term _
  A B t t₁ t₂ u u₁ u₂ : Term _
  ρ                   : Wk _ _
  σ σ₁ σ₂             : Subst _ _
  p q                 : M
  l l′ l″             : Universe-level

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Π⇔ :
    {A : Term n} {B : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ t ∷ Π p , q ▷ A ▹ B ⇔
    (Γ ⊩⟨ l ⟩ Π p , q ▷ A ▹ B ×
     ∃ λ u →
     Γ ⊢ t :⇒*: u ∷ Π p , q ▷ A ▹ B ×
     Function u ×
     Γ ⊢≅ u ∷ Π p , q ▷ A ▹ B ×
     ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
     ρ ∷ʷ Δ ⊇ Γ →
     Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
     Δ ⊩⟨ l ⟩ wk ρ u ∘⟨ p ⟩ v₁ ≡ wk ρ u ∘⟨ p ⟩ v₂ ∷
       wk (lift ρ) B [ v₁ ]₀)
  ⊩∷Π⇔ {n} {Γ} {t} {p} {q} {A} {B} =
      (λ (⊩Π , ⊩t) →
         case B-elim _ ⊩Π of λ
           ⊩Π′ →
         ⊩Π , lemma₁ ⊩Π′ (irrelevanceTerm ⊩Π (B-intr _ ⊩Π′) ⊩t))
    , (λ (⊩Π , rest) →
         case B-elim _ ⊩Π of λ
           ⊩Π′ →
         B-intr _ ⊩Π′ , lemma₂ ≤ᵘ-refl ⊩Π′ rest)
    where
    lemma₁ :
      (⊩Π : Γ ⊩⟨ l ⟩B⟨ BΠ p q ⟩ Π p , q ▷ A ▹ B) →
      Γ ⊩⟨ l ⟩ t ∷ Π p , q ▷ A ▹ B / B-intr (BΠ p q) ⊩Π →
      ∃ λ u →
      Γ ⊢ t :⇒*: u ∷ Π p , q ▷ A ▹ B ×
      Function u ×
      Γ ⊢≅ u ∷ Π p , q ▷ A ▹ B ×
      ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
      ρ ∷ʷ Δ ⊇ Γ →
      Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
      Δ ⊩⟨ l ⟩ wk ρ u ∘⟨ p ⟩ v₁ ≡ wk ρ u ∘⟨ p ⟩ v₂ ∷
        wk (lift ρ) B [ v₁ ]₀
    lemma₁ (emb ≤ᵘ-refl ⊩Π) ⊩t =
      case lemma₁ ⊩Π  ⊩t  of λ
        (u , t⇒*u , u-fun , u≅u , rest) →
        u , t⇒*u , u-fun , u≅u
      , λ ρ⊇ v₁≡v₂ →
          emb-⊩≡∷ (≤ᵘ-step ≤ᵘ-refl) $ rest ρ⊇ $
          level-⊩≡∷
            (⊩ΠΣ⇔ .proj₁ (B-intr _ ⊩Π) .proj₂ .proj₂ ρ⊇ .proj₁)
            v₁≡v₂
    lemma₁ (emb (≤ᵘ-step l<) ⊩Π) ⊩t =
      let u , t⇒*u , u-fun , u≅u , rest = lemma₁ (emb l< ⊩Π) ⊩t in
        u , t⇒*u , u-fun , u≅u , λ ρ⊇ v₁≡v₂ →
          emb-⊩≡∷ (≤ᵘ-step ≤ᵘ-refl) $ rest ρ⊇ $
            level-⊩≡∷
              (⊩ΠΣ⇔ .proj₁ (B-intr _ (emb l< ⊩Π))
                .proj₂ .proj₂ ρ⊇ .proj₁)
              v₁≡v₂
    lemma₁
      {l} ⊩Π@(noemb (Bᵣ _ _ Π⇒*Π _ ⊩wk-A ⊩wk-B _ _))
      (u , t⇒*u , u-fun , u≅u , u∘≡u∘ , u∷) =
      case B-PE-injectivity _ _ $ whnfRed* (red Π⇒*Π) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      (∃ λ u →
       Γ ⊢ t :⇒*: u ∷ Π p , q ▷ A ▹ B ×
       Function u ×
       Γ ⊢≅ u ∷ Π p , q ▷ A ▹ B ×
       ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
       ρ ∷ʷ Δ ⊇ Γ →
       Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk ρ u ∘⟨ p ⟩ v₁ ≡ wk ρ u ∘⟨ p ⟩ v₂ ∷
         wk (lift ρ) B [ v₁ ]₀) ∋
        u , t⇒*u , u-fun , u≅u
      , λ ρ⊇ (⊩wk-ρ-A , ⊩v , ⊩w , v≡w) →
          case irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ρ⊇) ⊩v of λ
            ⊩v′ →
          case irrelevanceTerm ⊩wk-ρ-A (⊩wk-A ρ⊇) ⊩w of λ
            ⊩w′ →
            ⊩wk-B ρ⊇ ⊩v′
          , u∷ ρ⊇ ⊩v′
          , convTerm₁ (⊩wk-B ρ⊇ ⊩w′) (⊩wk-B ρ⊇ ⊩v′)
              (⊩≡→⊩≡/ (⊩wk-B ρ⊇ ⊩w′) $
               ⊩ΠΣ⇔ .proj₁ (B-intr _ ⊩Π) .proj₂ .proj₂ ρ⊇ .proj₂ $
               sym-⊩≡∷ (⊩wk-ρ-A , ⊩v , ⊩w , v≡w))
              (u∷ ρ⊇ ⊩w′)
          , u∘≡u∘ ρ⊇ ⊩v′ ⊩w′
              (irrelevanceEqTerm ⊩wk-ρ-A (⊩wk-A ρ⊇) v≡w) }

    lemma₂ :
      l′ ≤ᵘ l →
      (⊩Π : Γ ⊩⟨ l′ ⟩B⟨ BΠ p q ⟩ Π p , q ▷ A ▹ B) →
      (∃ λ u →
       Γ ⊢ t :⇒*: u ∷ Π p , q ▷ A ▹ B ×
       Function u ×
       Γ ⊢≅ u ∷ Π p , q ▷ A ▹ B ×
       ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
       ρ ∷ʷ Δ ⊇ Γ →
       Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk ρ u ∘⟨ p ⟩ v₁ ≡ wk ρ u ∘⟨ p ⟩ v₂ ∷
         wk (lift ρ) B [ v₁ ]₀) →
      Γ ⊩⟨ l′ ⟩ t ∷ Π p , q ▷ A ▹ B / B-intr (BΠ p q) ⊩Π
    lemma₂ l′≤l (emb l″<l′ ⊩Π) rest =
      irrelevanceTerm (B-intr _ ⊩Π) (B-intr _ (emb l″<l′ ⊩Π)) $
      lemma₂ (≤ᵘ-trans (<ᵘ→≤ᵘ l″<l′) l′≤l) ⊩Π rest
    lemma₂
      l′≤l ⊩Π@(noemb (Bᵣ _ _ Π⇒*Π _ ⊩wk-A ⊩wk-B _ _))
      (u , t⇒*u , u-fun , u≅u , rest) =
      case B-PE-injectivity _ _ $ whnfRed* (red Π⇒*Π) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      _ ⊩⟨ _ ⟩ _ ∷ _ / B-intr _ ⊩Π ∋
        u , t⇒*u , u-fun , u≅u
      , (λ ρ⊇ ⊩v₁ ⊩v₂ v₁≡v₂ →
           let ⊩wk-ρ-A = ⊩wk-A ρ⊇ in
           case emb-≤-⊩ l′≤l ⊩wk-ρ-A of λ
             ⊩wk-ρ-A′ →
           ⊩≡∷→⊩≡∷/ (⊩wk-B ρ⊇ ⊩v₁) $
           rest ρ⊇
             ( ⊩wk-ρ-A′
             , irrelevanceTerm ⊩wk-ρ-A ⊩wk-ρ-A′ ⊩v₁
             , irrelevanceTerm ⊩wk-ρ-A ⊩wk-ρ-A′ ⊩v₂
             , irrelevanceEqTerm ⊩wk-ρ-A ⊩wk-ρ-A′ v₁≡v₂
             ))
      , (λ ρ⊇ ⊩v →
           let ⊩wk-ρ-A = ⊩wk-A ρ⊇ in
           case emb-≤-⊩ l′≤l ⊩wk-ρ-A of λ
             ⊩wk-ρ-A′ →
           ⊩∷→⊩∷/ (⊩wk-B ρ⊇ ⊩v) $
           proj₁ $ wf-⊩≡∷ $
           rest ρ⊇ $
           refl-⊩≡∷ (⊩wk-ρ-A′ , irrelevanceTerm ⊩wk-ρ-A ⊩wk-ρ-A′ ⊩v)) }

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Π⇔ :
    {A : Term n} {B : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B ⇔
    (Γ ⊩⟨ l ⟩ Π p , q ▷ A ▹ B ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t₁ :⇒*: u₁ ∷ Π p , q ▷ A ▹ B ×
     Γ ⊢ t₂ :⇒*: u₂ ∷ Π p , q ▷ A ▹ B ×
     Function u₁ ×
     Function u₂ ×
     Γ ⊢ u₁ ≅ u₂ ∷ Π p , q ▷ A ▹ B ×
     ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
     ρ ∷ʷ Δ ⊇ Γ →
     Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
     Δ ⊩⟨ l ⟩ wk ρ u₁ ∘⟨ p ⟩ v₁ ≡ wk ρ u₂ ∘⟨ p ⟩ v₂ ∷
       wk (lift ρ) B [ v₁ ]₀)
  ⊩≡∷Π⇔ {n} {Γ} {t₁} {t₂} {p} {q} {A} {B} =
      (λ (⊩Π , _ , _ , t₁≡t₂) →
         case B-elim _ ⊩Π of λ
           ⊩Π′ →
         ⊩Π , lemma₁ ⊩Π′ (irrelevanceEqTerm ⊩Π (B-intr _ ⊩Π′) t₁≡t₂))
    , (λ (⊩Π , rest) →
         case B-elim _ ⊩Π of λ
           ⊩Π′ →
         B-intr _ ⊩Π′ , lemma₂ ≤ᵘ-refl ⊩Π′ rest)
    where
    lemma₁ :
      (⊩Π : Γ ⊩⟨ l ⟩B⟨ BΠ p q ⟩ Π p , q ▷ A ▹ B) →
      Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B / B-intr (BΠ p q) ⊩Π →
      ∃₂ λ u₁ u₂ →
      Γ ⊢ t₁ :⇒*: u₁ ∷ Π p , q ▷ A ▹ B ×
      Γ ⊢ t₂ :⇒*: u₂ ∷ Π p , q ▷ A ▹ B ×
      Function u₁ ×
      Function u₂ ×
      Γ ⊢ u₁ ≅ u₂ ∷ Π p , q ▷ A ▹ B ×
      ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
      ρ ∷ʷ Δ ⊇ Γ →
      Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
      Δ ⊩⟨ l ⟩ wk ρ u₁ ∘⟨ p ⟩ v₁ ≡ wk ρ u₂ ∘⟨ p ⟩ v₂ ∷
        wk (lift ρ) B [ v₁ ]₀
    lemma₁ (emb ≤ᵘ-refl ⊩Π) t₁≡t₂ =
      case lemma₁ ⊩Π t₁≡t₂ of λ
        (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂ , rest) →
        u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂
      , λ ρ⊇ v₁≡v₂ →
          emb-⊩≡∷ (≤ᵘ-step ≤ᵘ-refl) $ rest ρ⊇ $
          level-⊩≡∷
            (⊩ΠΣ⇔ .proj₁ (B-intr _ ⊩Π) .proj₂ .proj₂ ρ⊇ .proj₁)
            v₁≡v₂
    lemma₁ (emb (≤ᵘ-step l<) ⊩Π) t₁≡t₂ =
      case lemma₁ (emb l< ⊩Π) t₁≡t₂ of λ
        (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂ , rest) →
        u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂
      , λ ρ⊇ v₁≡v₂ →
          emb-⊩≡∷ (≤ᵘ-step ≤ᵘ-refl) $ rest ρ⊇ $
          level-⊩≡∷
            (⊩ΠΣ⇔ .proj₁ (B-intr _ (emb l< ⊩Π)) .proj₂ .proj₂ ρ⊇ .proj₁)
            v₁≡v₂
    lemma₁
      {l} ⊩Π@(noemb (Bᵣ _ _ Π⇒*Π _ ⊩wk-A ⊩wk-B _ _))
      (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂ , ⊩t₁ , ⊩t₂ ,
       rest) =
      let ⊩Π′ = B-intr _ ⊩Π in
      case B-PE-injectivity _ _ $ whnfRed* (red Π⇒*Π) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      case ⊩∷Π⇔ .proj₁ (⊩∷-intro ⊩Π′ ⊩t₁) of λ
        (_ , _ , t₁⇒*u₁′ , u₁′-fun , _ , rest₁) →
      case ⊩∷Π⇔ .proj₁ (⊩∷-intro ⊩Π′ ⊩t₂) of λ
        (_ , _ , t₂⇒*u₂′ , u₂′-fun , _ , rest₂) →
      case whrDet*Term (redₜ t₁⇒*u₁ , functionWhnf u₁-fun)
             (redₜ t₁⇒*u₁′ , functionWhnf u₁′-fun) of λ {
        PE.refl →
      case whrDet*Term (redₜ t₂⇒*u₂ , functionWhnf u₂-fun)
             (redₜ t₂⇒*u₂′ , functionWhnf u₂′-fun) of λ {
        PE.refl →
      (∃₂ λ u₁ u₂ →
       Γ ⊢ t₁ :⇒*: u₁ ∷ Π p , q ▷ A ▹ B ×
       Γ ⊢ t₂ :⇒*: u₂ ∷ Π p , q ▷ A ▹ B ×
       Function u₁ ×
       Function u₂ ×
       Γ ⊢ u₁ ≅ u₂ ∷ Π p , q ▷ A ▹ B ×
       ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
       ρ ∷ʷ Δ ⊇ Γ →
       Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk ρ u₁ ∘⟨ p ⟩ v₁ ≡ wk ρ u₂ ∘⟨ p ⟩ v₂ ∷
         wk (lift ρ) B [ v₁ ]₀) ∋
        u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂
      , λ {_} {ρ = ρ} {_} {v₁ = v₁} {v₂ = v₂} ρ⊇ v₁≡v₂ →
          case rest₂ ρ⊇ v₁≡v₂ of λ
            wk-ρ-u₂∘v₁≡wk-ρ-u₂∘v₂ →
          wk ρ u₁ ∘⟨ p ⟩ v₁  ≡⟨ ⊩≡∷-intro (⊩wk-B ρ⊇ _)
                                  (wf-⊩≡∷ (rest₁ ρ⊇ v₁≡v₂) .proj₁)
                                  (wf-⊩≡∷ wk-ρ-u₂∘v₁≡wk-ρ-u₂∘v₂ .proj₁) $
                                rest ρ⊇ $
                                ⊩∷→⊩∷/ (⊩wk-A ρ⊇) $ wf-⊩≡∷ v₁≡v₂ .proj₁ ⟩⊩∷
          wk ρ u₂ ∘⟨ p ⟩ v₁  ≡⟨ wk-ρ-u₂∘v₁≡wk-ρ-u₂∘v₂ ⟩⊩∷∎
          wk ρ u₂ ∘⟨ p ⟩ v₂  ∎ }}}

    lemma₂ :
      l′ ≤ᵘ l →
      (⊩Π : Γ ⊩⟨ l′ ⟩B⟨ BΠ p q ⟩ Π p , q ▷ A ▹ B) →
      (∃₂ λ u₁ u₂ →
       Γ ⊢ t₁ :⇒*: u₁ ∷ Π p , q ▷ A ▹ B ×
       Γ ⊢ t₂ :⇒*: u₂ ∷ Π p , q ▷ A ▹ B ×
       Function u₁ ×
       Function u₂ ×
       Γ ⊢ u₁ ≅ u₂ ∷ Π p , q ▷ A ▹ B ×
       ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v₁ v₂} →
       ρ ∷ʷ Δ ⊇ Γ →
       Δ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk ρ u₁ ∘⟨ p ⟩ v₁ ≡ wk ρ u₂ ∘⟨ p ⟩ v₂ ∷
         wk (lift ρ) B [ v₁ ]₀) →
      let ⊩Π′ = B-intr (BΠ p q) ⊩Π in
      Γ ⊩⟨ l′ ⟩ t₁ ∷ Π p , q ▷ A ▹ B / ⊩Π′ ×
      Γ ⊩⟨ l′ ⟩ t₂ ∷ Π p , q ▷ A ▹ B / ⊩Π′ ×
      Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B / ⊩Π′
    lemma₂ l′≤l (emb l″<l′ ⊩Π) rest =
      let ⊩Π₁ = B-intr _ ⊩Π
          ⊩Π₂ = B-intr _ (emb l″<l′ ⊩Π)
      in
      case lemma₂ (≤ᵘ-trans (<ᵘ→≤ᵘ l″<l′) l′≤l) ⊩Π rest of λ
        (⊩t₁ , ⊩t₂ , t₁≡t₂) →
        irrelevanceTerm ⊩Π₁ ⊩Π₂ ⊩t₁
      , irrelevanceTerm ⊩Π₁ ⊩Π₂ ⊩t₂
      , irrelevanceEqTerm ⊩Π₁ ⊩Π₂ t₁≡t₂
    lemma₂
      l′≤l ⊩Π@(noemb (Bᵣ _ _ Π⇒*Π _ ⊩wk-A ⊩wk-B _ _))
      (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂ , rest) =
      case B-PE-injectivity _ _ $ whnfRed* (red Π⇒*Π) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      let ⊩Π′ = B-intr _ ⊩Π in
      case ⊩∷→⊩∷/ ⊩Π′ $
           ⊩∷Π⇔ .proj₂
             ( ⊩Π′
             , u₁ , t₁⇒*u₁ , u₁-fun , ≅ₜ-trans u₁≅u₂ (≅ₜ-sym u₁≅u₂)
             , λ {_} {ρ = ρ} {_} {v₁ = v₁} {v₂ = v₂} ρ⊇ v₁≡v₂ →
                 case emb-⊩≡∷ l′≤l v₁≡v₂ of λ
                   v₁≡v₂′ →
                 wk ρ u₁ ∘⟨ p ⟩ v₁  ≡⟨ rest ρ⊇ v₁≡v₂′ ⟩⊩∷
                 wk ρ u₂ ∘⟨ p ⟩ v₂  ≡˘⟨ conv-⊩≡∷
                                          (sym-⊩≡ $
                                           ⊩ΠΣ⇔ .proj₁ ⊩Π′ .proj₂ .proj₂ ρ⊇ .proj₂ v₁≡v₂) $
                                        rest ρ⊇ (refl-⊩≡∷ (wf-⊩≡∷ v₁≡v₂′ .proj₂)) ⟩⊩∷∎
                 wk ρ u₁ ∘⟨ p ⟩ v₂  ∎
             ) of λ
        ⊩t₁ →
      case ⊩∷→⊩∷/ ⊩Π′ $
           ⊩∷Π⇔ .proj₂
             ( ⊩Π′
             , u₂ , t₂⇒*u₂ , u₂-fun , ≅ₜ-trans (≅ₜ-sym u₁≅u₂) u₁≅u₂
             , λ {_} {ρ = ρ} {_} {v₁ = v₁} {v₂ = v₂} ρ⊇ v₁≡v₂ →
                 case emb-⊩≡∷ l′≤l v₁≡v₂ of λ
                   v₁≡v₂′ →
                 wk ρ u₂ ∘⟨ p ⟩ v₁  ≡˘⟨ rest ρ⊇ (refl-⊩≡∷ (wf-⊩≡∷ v₁≡v₂′ .proj₁)) ⟩⊩∷
                 wk ρ u₁ ∘⟨ p ⟩ v₁  ≡⟨ level-⊩≡∷
                                         (wf-⊩≡
                                            (⊩ΠΣ⇔ .proj₁ ⊩Π′ .proj₂ .proj₂ ρ⊇ .proj₂ v₁≡v₂)
                                            .proj₁) $
                                       rest ρ⊇ v₁≡v₂′ ⟩⊩∷∎
                 wk ρ u₂ ∘⟨ p ⟩ v₂  ∎
             ) of λ
        ⊩t₂ →
      _ ⊩⟨ _ ⟩ _ ∷ _ / ⊩Π′ × _ ⊩⟨ _ ⟩ _ ∷ _ / ⊩Π′ ×
        _ ⊩⟨ _ ⟩ _ ≡ _ ∷ _ / ⊩Π′ ∋
        ⊩t₁ , ⊩t₂
      , ( u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-fun , u₂-fun , u₁≅u₂
        , ⊩t₁ , ⊩t₂
        , λ ρ⊇ ⊩v →
            ⊩≡∷→⊩≡∷/ (⊩wk-B ρ⊇ ⊩v) $
            rest ρ⊇ $
            refl-⊩≡∷ $ emb-⊩∷ l′≤l $
            ⊩∷-intro (⊩wk-A ρ⊇) ⊩v
        ) }

------------------------------------------------------------------------
-- Lambdas

opaque

  -- Reducibility of equality between applications of lam.

  ⊩lam≡lam :
    {σ₁ σ₂ : Subst m n} →
    Π-allowed p q →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ lam p t₁ [ σ₁ ] ≡ lam p t₂ [ σ₂ ] ∷
      (Π p , q ▷ A ▹ B) [ σ₁ ]
  ⊩lam≡lam
    {m} {p} {l} {A} {t₁} {t₂} {B} {Δ} {σ₁} {σ₂} ok ⊩A t₁≡t₂ σ₁≡σ₂ =
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case wf-⊩ᵛ∷ ⊩t₁ of λ
      ⊩B →
    case escape-⊩ $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ₁ of λ
      ⊢B[σ₁⇑] →
    case ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ₁ of λ
      ⊩A[σ₁] →
    case escape ⊩A[σ₁] of λ
      ⊢A[σ₁] →
    case lamⱼ ⊢B[σ₁⇑] (escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ ⊩t₁ ⊩σ₁) ok of λ
      ⊢lam-t₁[σ₁] →
    case lamⱼ ⊢B[σ₁⇑]
           (escape-⊩∷ $
            wf-⊩≡∷ (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ (refl-⊩ᵛ≡∷ ⊩t₂) σ₁≡σ₂) .proj₂)
           ok of λ
      ⊢lam-t₂[σ₂] →
    case
      (∀ k (ρ : Wk k m) (Ε : Con Term k) v₁ v₂ →
       ρ ∷ʷ Ε ⊇ Δ →
       Ε ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ (A [ σ₁ ]) →
       Ε ⊩⟨ l ⟩ wk ρ (lam p t₁ [ σ₁ ]) ∘⟨ p ⟩ v₁ ≡
         wk ρ (lam p t₂ [ σ₂ ]) ∘⟨ p ⟩ v₂ ∷
         wk (lift ρ) (B [ σ₁ ⇑ ]) [ v₁ ]₀) ∋
      (λ _ ρ _ v₁ v₂ ρ⊇ v₁≡v₂ →
         case W.wk ρ⊇ ⊢A[σ₁] of λ
           ⊢wk-ρ-A[σ₁] →
         case W.wk ρ⊇ $ escape $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ₂ of λ
           ⊢wk-ρ-A[σ₂] →
         case wf-⊩≡∷ v₁≡v₂ of λ
           (⊩v₁ , ⊩v₂) →
         case conv-⊩∷
                (wk-⊩≡ ρ⊇ $ ⊩ᵛ≡⇔ .proj₁ (refl-⊩ᵛ≡ ⊩A) .proj₂ σ₁≡σ₂)
                ⊩v₂ of λ
           ⊩v₂ →
         case ⊩ˢ≡∷∙⇔ {σ₁ = consSubst _ _} {σ₂ = consSubst _ _} .proj₂
                ( ( _ , ⊩A
                  , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A) v₁≡v₂
                  )
                , ⊩ˢ≡∷-•ₛ ρ⊇ σ₁≡σ₂
                ) of λ
           ρ•ₛσ₁,v₁≡ρ•ₛσ₂,v₂ →
         lam p (wk (lift ρ) (t₁ [ σ₁ ⇑ ])) ∘⟨ p ⟩ v₁  ⇒⟨ β-red (W.wk (W.liftʷʷ ρ⊇ (⊢wk-ρ-A[σ₁])) (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ₁))
                                                           (W.wkTerm (W.liftʷʷ ρ⊇ (⊢wk-ρ-A[σ₁])) (escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ ⊩t₁ ⊩σ₁))
                                                           (escape-⊩∷ ⊩v₁) PE.refl ok ⟩⊩∷
         wk (lift ρ) (t₁ [ σ₁ ⇑ ]) [ v₁ ]₀ ∷
           wk (lift ρ) (B [ σ₁ ⇑ ]) [ v₁ ]₀           ≡⟨ singleSubstWkComp _ _ t₁ ⟩⊩∷∷≡
                                                       ⟨ singleSubstWkComp _ _ B ⟩⊩∷≡
         t₁ [ consSubst (ρ •ₛ σ₁) v₁ ] ∷
           B [ consSubst (ρ •ₛ σ₁) v₁ ]               ≡⟨ ⊩ᵛ≡∷⇔ .proj₁ t₁≡t₂ .proj₂ ρ•ₛσ₁,v₁≡ρ•ₛσ₂,v₂ ⟩⊩∷∷⇐*
                                                       ⟨ ≅-eq $ escape-⊩≡ $
                                                         ⊩ᵛ≡⇔ .proj₁ (refl-⊩ᵛ≡ ⊩B) .proj₂ ρ•ₛσ₁,v₁≡ρ•ₛσ₂,v₂ ⟩⇒
         t₂ [ consSubst (ρ •ₛ σ₂) v₂ ] ∷
           B [ consSubst (ρ •ₛ σ₂) v₂ ]               ≡˘⟨ singleSubstWkComp _ _ t₂ ⟩⇐∷
                                                       ˘⟨ singleSubstWkComp _ _ B ⟩⇒≡
         wk (lift ρ) (t₂ [ σ₂ ⇑ ]) [ v₂ ]₀ ∷
           wk (lift ρ) (B [ σ₂ ⇑ ]) [ v₂ ]₀           ⇐⟨ β-red (W.wk (W.liftʷʷ ρ⊇ (⊢wk-ρ-A[σ₂])) (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ₂))
                                                           (W.wkTerm (W.liftʷʷ ρ⊇ (⊢wk-ρ-A[σ₂])) (escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ ⊩t₂ ⊩σ₂))
                                                           (escape-⊩∷ ⊩v₂) PE.refl ok
                                                       , PE.subst₂ (_⊢_∷_ _) (PE.sym $ singleSubstWkComp _ _ t₂)
                                                           (PE.sym $ singleSubstWkComp _ _ B) $
                                                         escape-⊩∷ $
                                                         wf-⊩≡∷ (⊩ᵛ∷⇔ .proj₁ ⊩t₂ .proj₂ (sym-⊩ˢ≡∷ ρ•ₛσ₁,v₁≡ρ•ₛσ₂,v₂)) .proj₁
                                                       ⟩∎∷
         lam p (wk (lift ρ) (t₂ [ σ₂ ⇑ ])) ∘⟨ p ⟩ v₂  ∎)
    of λ
      lemma →
    ⊩≡∷Π⇔ .proj₂
      ( ⊩ᵛ→⊩ˢ∷→⊩[] (ΠΣᵛ ok ⊩A ⊩B) ⊩σ₁
      , _ , _
      , idRedTerm:*: ⊢lam-t₁[σ₁]
      , idRedTerm:*: ⊢lam-t₂[σ₂]
      , lamₙ , lamₙ
      , ≅-η-eq ⊢lam-t₁[σ₁] ⊢lam-t₂[σ₂] lamₙ lamₙ
          (escape-⊩≡∷ $
           PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (idWkLiftSubstLemma _ B) $
           lemma _ (step id) _ _ _ (W.stepʷ W.id ⊢A[σ₁]) $
           refl-⊩≡∷ $
           ⊩var here (wk-⊩ (W.stepʷ W.id ⊢A[σ₁]) ⊩A[σ₁]))
      , lemma _ _ _ _ _
      )

opaque

  -- Validity of equality preservation for lam.

  lam-congᵛ :
    Π-allowed p q →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Γ ⊩ᵛ⟨ l ⟩ lam p t₁ ≡ lam p t₂ ∷ Π p , q ▷ A ▹ B
  lam-congᵛ ok ⊩A t₁≡t₂ =
    ⊩ᵛ≡∷⇔ .proj₂
      ( ΠΣᵛ ok ⊩A (wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , ⊩lam≡lam ok ⊩A t₁≡t₂
      )

opaque

  -- Validity of lam.

  lamᵛ :
    Π-allowed p q →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Γ ⊩ᵛ⟨ l ⟩ lam p t ∷ Π p , q ▷ A ▹ B
  lamᵛ ok ⊩A ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    lam-congᵛ ok ⊩A (refl-⊩ᵛ≡∷ ⊩t)

------------------------------------------------------------------------
-- Applications

opaque

  -- Reducibility of equality between applications.

  ⊩∘≡∘ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ A →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ (t₁ ∘⟨ p ⟩ u₁) [ σ₁ ] ≡ (t₂ ∘⟨ p ⟩ u₂) [ σ₂ ] ∷
      B [ u₁ ]₀ [ σ₁ ]
  ⊩∘≡∘ {t₁} {t₂} {p} {B} {u₁} {u₂} {σ₁} {σ₂} t₁≡t₂ u₁≡u₂ σ₁≡σ₂ =
    case ⊩ᵛ≡∷⇔″ .proj₁ t₁≡t₂ of λ
      (⊩t₁ , _ , t₁[]≡t₂[]) →
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    case ⊩ᵛ≡∷⇔ .proj₁ u₁≡u₂ .proj₂ σ₁≡σ₂ of λ
      u₁[σ₁]≡u₂[σ₂] →
    case ⊩ᵛΠΣ⇔ .proj₁ (wf-⊩ᵛ∷ ⊩t₁) of λ
      (_ , ⊩A , ⊩B) →
    case ⊩≡∷Π⇔ .proj₁ (t₁[]≡t₂[] σ₁≡σ₂) of λ
      (_ , t₁′ , t₂′ , t₁[σ₁]⇒*t₁′ , t₂[σ₂]⇒*t₂′ , _ , _ , _ , rest) →
                           ∷ B [ u₁ ]₀ [ σ₁ ]             ⟨ singleSubstLift B _ ⟩⊩∷∷≡
    (t₁ ∘⟨ p ⟩ u₁) [ σ₁ ]  ∷ B [ σ₁ ⇑ ] [ u₁ [ σ₁ ] ]₀  ⇒*⟨ app-subst* (redₜ t₁[σ₁]⇒*t₁′) $
                                                            escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₁ ⊩σ₁ ⟩⊩∷∷
    t₁′ ∘⟨ p ⟩ (u₁ [ σ₁ ])                              ≡⟨ PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
                                                             (PE.cong₃ _∘⟨_⟩_ (wk-id _) PE.refl PE.refl)
                                                             (PE.cong₃ _∘⟨_⟩_ (wk-id _) PE.refl PE.refl)
                                                             (PE.cong₂ _[_]₀ (wk-lift-id (B [ _ ])) PE.refl) $
                                                           rest (W.idʷ (escape-⊩ˢ∷ ⊩σ₁ .proj₁)) $
                                                           PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk-id _) $
                                                           level-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ₁) u₁[σ₁]≡u₂[σ₂] ⟩⊩∷⇐*
                                                          ⟨ ≅-eq $ escape-⊩≡ $
                                                            ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀
                                                              (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ₁) u₁[σ₁]≡u₂[σ₂] ⟩⇒
    t₂′ ∘⟨ p ⟩ (u₂ [ σ₂ ]) ∷ B [ σ₁ ⇑ ] [ u₂ [ σ₂ ] ]₀  ⇐*⟨ app-subst* (redₜ t₂[σ₂]⇒*t₂′) $
                                                            escape-⊩∷ $
                                                            conv-⊩∷ (sym-⊩≡ $ ⊩ᵛ⇔ .proj₁ ⊩A .proj₂ σ₁≡σ₂) $
                                                            ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u₂ ⊩σ₂ ⟩∎∷
    (t₂ ∘⟨ p ⟩ u₂) [ σ₂ ]                               ∎

opaque

  -- Validity of equality preservation for application.

  ∘-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ∘⟨ p ⟩ u₁ ≡ t₂ ∘⟨ p ⟩ u₂ ∷ B [ u₁ ]₀
  ∘-congᵛ t₁≡t₂ u₁≡u₂ =
    case ⊩ᵛΠΣ⇔ .proj₁ $ wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁ of λ
      (_ , _ , ⊩B) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B (wf-⊩ᵛ≡∷ u₁≡u₂ .proj₁)
      , ⊩∘≡∘ t₁≡t₂ u₁≡u₂
      )

opaque

  -- Validity of application.

  ∘ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Π p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∘⟨ p ⟩ u ∷ B [ u ]₀
  ∘ᵛ ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    ∘-congᵛ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

------------------------------------------------------------------------
-- Validity of some equality rules

opaque

  -- Validity of β-reduction.

  β-redᵛ :
    Π-allowed p q →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ lam p t ∘⟨ p ⟩ u ≡ t [ u ]₀ ∷ B [ u ]₀
  β-redᵛ {t} {B} ok ⊩t ⊩u =
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩B →
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst₂ (_⊢_⇒_∷_ _ _) (PE.sym $ singleSubstLift t _)
           (PE.sym $ singleSubstLift B _) $
         β-red (escape-⊩ $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ)
           (escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ ⊩t ⊩σ)
           (escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ) PE.refl ok)
      (⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ ⊩t ⊩u)

private opaque

  -- A lemma used below.

  wk-[]∘≡ :
    (t : Term n) →
    wk ρ (t [ σ ]) ∘⟨ p ⟩ u PE.≡
    (wk1 t ∘⟨ p ⟩ var x0) [ consSubst (ρ •ₛ σ) u ]
  wk-[]∘≡ {ρ} {σ} {u} t =
    PE.cong (_∘⟨ _ ⟩ _)
      (wk ρ (t [ σ ])                  ≡⟨ wk-subst t ⟩
       t [ ρ •ₛ σ ]                    ≡˘⟨ wk1-sgSubst _ _ ⟩
       wk1 (t [ ρ •ₛ σ ]) [ u ]₀       ≡˘⟨ PE.cong _[ _ ] $ wk1-liftSubst t ⟩
       wk1 t [ (ρ •ₛ σ) ⇑ ] [ u ]₀     ≡⟨ singleSubstComp _ _ (wk1 t) ⟩
       wk1 t [ consSubst (ρ •ₛ σ) u ]  ∎)

opaque

  -- Validity of η-equality.

  η-eqᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ∷ Π p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t₂ ∷ Π p , q ▷ A ▹ B →
    Γ ∙ A ⊩ᵛ⟨ l″ ⟩ wk1 t₁ ∘⟨ p ⟩ var x0 ≡ wk1 t₂ ∘⟨ p ⟩ var x0 ∷ B →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Π p , q ▷ A ▹ B
  η-eqᵛ {l} {t₁} {p} {A} {B} {t₂} ⊩t₁ ⊩t₂ wk1-t₁∘0≡wk1-t₂∘0 =
    case wf-⊩ᵛ∷ ⊩t₁ of λ
      ⊩ΠAB →
    case ⊩ᵛΠΣ⇔ .proj₁ ⊩ΠAB of λ
      (_ , ⊩A , ⊩B) →
    ⊩ᵛ≡∷⇔′ .proj₂
      ( ⊩t₁
      , level-⊩ᵛ∷ ⊩ΠAB ⊩t₂
      , λ {m = m} {Δ = Δ} {σ = σ} ⊩σ →
          case ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ of λ
            ⊩A[σ] →
          case escape-⊩ ⊩A[σ] of λ
            ⊢A[σ] →
          case ⊩∷Π⇔ .proj₁ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₁ ⊩σ) of λ
            (⊩ΠAB[σ] , u₁ , t₁[σ]⇒*u₁ , u₁-fun , _ , _) →
          case ⊩∷Π⇔ .proj₁ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ) of λ
            (_ , u₂ , t₂[σ]⇒*u₂ , u₂-fun , _ , _) →
          case
            (∀ k (ρ : Wk k m) (Ε : Con Term k) v₁ v₂ →
             ρ ∷ʷ Ε ⊇ Δ →
             Ε ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ wk ρ (A [ σ ]) →
             Ε ⊩⟨ l ⟩ wk ρ u₁ ∘⟨ p ⟩ v₁ ≡ wk ρ u₂ ∘⟨ p ⟩ v₂ ∷
               wk (lift ρ) (B [ σ ⇑ ]) [ v₁ ]₀) ∋
            (λ _ ρ _ v₁ v₂ ρ⊇ v₁≡v₂ →
               case wf-⊩≡∷ v₁≡v₂ of λ
                 (⊩v₁ , ⊩v₂) →
               case ⊩ᵛ⇔ .proj₁ ⊩B .proj₂ $
                    ⊩ˢ≡∷∙⇔ .proj₂
                      ( ( _ , ⊩A
                        , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A)
                            v₁≡v₂
                        )
                      , refl-⊩ˢ≡∷ (⊩ˢ∷-•ₛ ρ⊇ ⊩σ)
                      ) of λ
                 B[ρ•ₛσ,v₁]≡B[ρ•ₛσ,v₂] →

               wk ρ u₁ ∘⟨ p ⟩ v₁ ∷ wk (lift ρ) (B [ σ ⇑ ]) [ v₁ ]₀  ⇐*⟨ app-subst:*: (W.wkRed:*:Term ρ⊇ t₁[σ]⇒*u₁) (escape-⊩∷ ⊩v₁) ⟩⊩∷∷

               wk ρ (t₁ [ σ ]) ∘⟨ p ⟩ v₁                            ≡⟨ wk-[]∘≡ t₁ ⟩⊩∷≡
                                                                     ⟨ singleSubstWkComp _ _ B ⟩⊩∷≡
               (wk1 t₁ ∘⟨ p ⟩ var x0) [ consSubst (ρ •ₛ σ) v₁ ] ∷
                 B [ consSubst (ρ •ₛ σ) v₁ ]                        ≡⟨ level-⊩≡∷ (wf-⊩≡ B[ρ•ₛσ,v₁]≡B[ρ•ₛσ,v₂] .proj₁) $
                                                                       ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ wk1-t₁∘0≡wk1-t₂∘0
                                                                         (⊩ˢ≡∷-•ₛ ρ⊇ (refl-⊩ˢ≡∷ ⊩σ))
                                                                         (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A) v₁≡v₂) ⟩⊩∷∷:⇒*:
                                                                     ⟨ ≅-eq $ escape-⊩≡ B[ρ•ₛσ,v₁]≡B[ρ•ₛσ,v₂] ⟩:⇒:
               (wk1 t₂ ∘⟨ p ⟩ var x0) [ consSubst (ρ •ₛ σ) v₂ ] ∷
                 B [ consSubst (ρ •ₛ σ) v₂ ]                        ≡˘⟨ wk-[]∘≡ t₂ ⟩:⇒:∷
                                                                     ˘⟨ singleSubstWkComp _ _ B ⟩:⇒:≡
               wk ρ (t₂ [ σ ]) ∘⟨ p ⟩ v₂ ∷
                 wk (lift ρ) (B [ σ ⇑ ]) [ v₂ ]₀                    :⇒*:⟨ app-subst:*: (W.wkRed:*:Term ρ⊇ t₂[σ]⇒*u₂) (escape-⊩∷ ⊩v₂) ⟩∎∷

               wk ρ u₂ ∘⟨ p ⟩ v₂                                    ∎)
          of λ
            lemma →
          ⊩≡∷Π⇔ .proj₂
            ( ⊩ΠAB[σ]
            , u₁ , u₂ , t₁[σ]⇒*u₁ , t₂[σ]⇒*u₂ , u₁-fun , u₂-fun
            , ≅-η-eq (⊢u-redₜ t₁[σ]⇒*u₁) (⊢u-redₜ t₂[σ]⇒*u₂)
                u₁-fun u₂-fun
                (PE.subst (_⊢_≅_∷_ _ _ _) (idWkLiftSubstLemma _ B) $
                 escape-⊩≡∷ $
                 lemma _ _ _ _ _ (W.stepʷ W.id ⊢A[σ]) $
                 refl-⊩≡∷ $
                 ⊩var here (wk-⊩ (W.stepʷ W.id ⊢A[σ]) ⊩A[σ]))
            , lemma _ _ _ _ _
            )
      )
