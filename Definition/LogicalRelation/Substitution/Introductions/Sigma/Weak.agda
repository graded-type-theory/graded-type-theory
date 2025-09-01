------------------------------------------------------------------------
-- Validity for weak Σ-types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module
  Definition.LogicalRelation.Substitution.Introductions.Sigma.Weak
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
  Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma R
open import Definition.LogicalRelation.Substitution.Introductions.Var R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Substitution R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  m n                                           : Nat
  ∇                                             : DCon (Term 0) _
  Δ Η                                           : Con Term _
  Γ                                             : Cons _ _
  A B C C₁ C₂ t t₁ t₁₁ t₁₂ t₂ t₂₁ t₂₂ u u₁ u₂ v : Term _
  σ σ₁ σ₂                                       : Subst _ _
  p q q′ r                                      : M
  l l′ l″ l‴                                    : Universe-level

------------------------------------------------------------------------
-- Some characterisation lemmas

-- A type used to state ⊩∷Σʷ⇔.

infix 4 _⊩⟨_⟩_∷Σʷ_,_▷_▹_

data _⊩⟨_⟩_∷Σʷ_,_▷_▹_
       (Γ : Cons m n) (l : Universe-level) :
       Term n → M → M → Term n → Term (1+ n) → Set a where
  prodₙ :
    Γ ⊩⟨ l ⟩ t₁ ∷ A →
    Γ ⊩⟨ l ⟩ t₂ ∷ B [ t₁ ]₀ →
    Γ ⊩⟨ l ⟩ prodʷ p t₁ t₂ ∷Σʷ p , q ▷ A ▹ B
  ne :
    Neutralₗ (Γ .defs) t →
    Γ ⊢~ t ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊩⟨ l ⟩ t ∷Σʷ p , q ▷ A ▹ B

opaque

  -- If Γ ⊩⟨ l ⟩ t ∷Σʷ p , q ▷ A ▹ B holds, then t is a product.

  ⊩∷Σʷ→Product : Γ ⊩⟨ l ⟩ t ∷Σʷ p , q ▷ A ▹ B → Productₗ (Γ .defs) t
  ⊩∷Σʷ→Product = λ where
    (prodₙ _ _) → prodₙ
    (ne t-ne _) → ne t-ne

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Σʷ⇔ :
    Γ ⊩⟨ l ⟩ t ∷ Σʷ p , q ▷ A ▹ B ⇔
    (Γ ⊩⟨ l ⟩ Σʷ p , q ▷ A ▹ B ×
     ∃ λ u →
     Γ ⊢ t ⇒* u ∷ Σʷ p , q ▷ A ▹ B ×
     Γ ⊢≅ u ∷ Σʷ p , q ▷ A ▹ B ×
     Γ ⊩⟨ l ⟩ u ∷Σʷ p , q ▷ A ▹ B)
  ⊩∷Σʷ⇔ {Γ} {t} {p} {q} {A} {B} =
      (λ (⊩Σ , ⊩t) →
         case B-elim _ ⊩Σ of λ
           ⊩Σ′ →
         ⊩Σ , lemma₁ ⊩Σ′ (irrelevanceTerm ⊩Σ (B-intr _ ⊩Σ′) ⊩t))
    , (λ (⊩Σ , rest) →
         case B-elim _ ⊩Σ of λ
           ⊩Σ′ →
         B-intr _ ⊩Σ′ , lemma₂ ⊩Σ′ rest)
    where
    lemma₁ :
      (⊩Σ : Γ ⊩⟨ l ⟩B⟨ BΣ 𝕨 p q ⟩ Σʷ p , q ▷ A ▹ B) →
      Γ ⊩⟨ l ⟩ t ∷ Σʷ p , q ▷ A ▹ B / B-intr (BΣ 𝕨 p q) ⊩Σ →
      ∃ λ u →
      Γ ⊢ t ⇒* u ∷ Σʷ p , q ▷ A ▹ B ×
      Γ ⊢≅ u ∷ Σʷ p , q ▷ A ▹ B ×
      Γ ⊩⟨ l ⟩ u ∷Σʷ p , q ▷ A ▹ B
    lemma₁ (emb ≤ᵘ-refl ⊩Σ) ⊩t =
      case lemma₁ ⊩Σ ⊩t of λ
        (u , t⇒*u , u≅u , u-val) →
        u , t⇒*u , u≅u
      , (case u-val of λ where
           (prodₙ ⊩u₁ ⊩u₂) →
             prodₙ (emb-⊩∷ (≤ᵘ-step ≤ᵘ-refl) ⊩u₁)
               (emb-⊩∷ (≤ᵘ-step ≤ᵘ-refl) ⊩u₂)
           (ne u-ne u~u) →
             ne u-ne u~u)
    lemma₁ (emb (≤ᵘ-step l<) ⊩Σ) ⊩t =
      case lemma₁ (emb l< ⊩Σ) ⊩t of λ
        (u , t⇒*u , u≅u , u-val) →
        u , t⇒*u , u≅u
      , (case u-val of λ where
           (prodₙ ⊩u₁ ⊩u₂) →
             prodₙ (emb-⊩∷ (≤ᵘ-step ≤ᵘ-refl) ⊩u₁)
               (emb-⊩∷ (≤ᵘ-step ≤ᵘ-refl) ⊩u₂)
           (ne u-ne u~u) →
             ne u-ne u~u)
    lemma₁
      {l} ⊩Σ@(noemb (Bᵣ _ _ Σ⇒*Σ _ ⊩wk-A ⊩wk-B _ _))
      (u , t⇒*u , u≅u , u-prod , rest) =
      case B-PE-injectivity _ _ $ whnfRed* Σ⇒*Σ ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      (∃ λ u →
       Γ ⊢ t ⇒* u ∷ Σʷ p , q ▷ A ▹ B ×
       Γ ⊢≅ u ∷ Σʷ p , q ▷ A ▹ B ×
       Γ ⊩⟨ l ⟩ u ∷Σʷ p , q ▷ A ▹ B) ∋
        u , t⇒*u , u≅u
      , (case PE.singleton u-prod of λ where
           (prodₙ , PE.refl) →
             case rest of λ {
               (PE.refl , ⊩u₁ , ⊩u₂ , PE.refl) →
             prodₙ
               (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk-id _)
                  (⊩wk-A id _ , ⊩u₁))
               (PE.subst (_⊩⟨_⟩_∷_ _ _ _)
                  (PE.cong _[ _ ]₀ $ wk-lift-id B)
                  (⊩wk-B id _ _ , ⊩u₂)) }
           (ne u-ne , PE.refl) → ne u-ne rest) }

    lemma₂ :
      (⊩Σ : Γ ⊩⟨ l′ ⟩B⟨ BΣ 𝕨 p q ⟩ Σʷ p , q ▷ A ▹ B) →
      (∃ λ u →
       Γ ⊢ t ⇒* u ∷ Σʷ p , q ▷ A ▹ B ×
       Γ ⊢≅ u ∷ Σʷ p , q ▷ A ▹ B ×
       Γ ⊩⟨ l ⟩ u ∷Σʷ p , q ▷ A ▹ B) →
      Γ ⊩⟨ l′ ⟩ t ∷ Σʷ p , q ▷ A ▹ B / B-intr (BΣ 𝕨 p q) ⊩Σ
    lemma₂ (emb 0<1 ⊩Σ) rest =
      irrelevanceTerm (B-intr _ ⊩Σ) (B-intr _ (emb 0<1 ⊩Σ)) $
      lemma₂ ⊩Σ rest
    lemma₂
      ⊩Σ@(noemb (Bᵣ _ _ Σ⇒*Σ _ ⊩wk-A ⊩wk-B _ _))
      (u , t⇒*u , u≅u , u-val) =
      case B-PE-injectivity _ _ $ whnfRed* Σ⇒*Σ ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      _ ⊩⟨ _ ⟩ _ ∷ _ / B-intr _ ⊩Σ ∋
        u , t⇒*u , u≅u
      , (case u-val of λ where
           (prodₙ ⊩u₁ ⊩u₂) →
               prodₙ
             , PE.refl
             , ⊩∷→⊩∷/ (⊩wk-A id _)
                 (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk-id _) ⊩u₁)
             , ⊩∷→⊩∷/ (⊩wk-B id _ _)
                 (PE.subst (_⊩⟨_⟩_∷_ _ _ _)
                    (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id B) ⊩u₂)
             , PE.refl
           (ne u-ne ~u) →
             ne u-ne , ~u) }

-- A type used to state ⊩≡∷Σʷ⇔.

infix 4 _⊩⟨_⟩_≡_∷Σʷ_,_▷_▹_

data _⊩⟨_⟩_≡_∷Σʷ_,_▷_▹_
       (Γ : Cons m n) (l : Universe-level) :
       Term n → Term n → M → M → Term n → Term (1+ n) → Set a where
  prodₙ :
    Γ ⊩⟨ l ⟩ t₁₁ ≡ t₂₁ ∷ A →
    Γ ⊩⟨ l ⟩ t₁₂ ≡ t₂₂ ∷ B [ t₁₁ ]₀ →
    Γ ⊩⟨ l ⟩ prodʷ p t₁₁ t₁₂ ≡ prodʷ p t₂₁ t₂₂ ∷Σʷ p , q ▷ A ▹ B
  ne :
    Neutralₗ (Γ .defs) t₁ →
    Neutralₗ (Γ .defs) t₂ →
    Γ ⊢ t₁ ~ t₂ ∷ Σʷ p , q ▷ A ▹ B →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷Σʷ p , q ▷ A ▹ B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Σʷ⇔ :
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Σʷ p , q ▷ A ▹ B ⇔
    (Γ ⊩⟨ l ⟩ Σʷ p , q ▷ A ▹ B ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t₁ ⇒* u₁ ∷ Σʷ p , q ▷ A ▹ B ×
     Γ ⊢ t₂ ⇒* u₂ ∷ Σʷ p , q ▷ A ▹ B ×
     Γ ⊢ u₁ ≅ u₂ ∷ Σʷ p , q ▷ A ▹ B ×
     Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷Σʷ p , q ▷ A ▹ B)
  ⊩≡∷Σʷ⇔ {B} =
      (λ (⊩Σ , _ , _ , t₁≡t₂) →
         case B-elim _ ⊩Σ of λ
           ⊩Σ′ →
         ⊩Σ , lemma₁ ⊩Σ′ (irrelevanceEqTerm ⊩Σ (B-intr _ ⊩Σ′) t₁≡t₂))
    , (λ (⊩Σ , rest) →
         case B-elim _ ⊩Σ of λ
           ⊩Σ′ →
         B-intr _ ⊩Σ′ , lemma₂ ⊩Σ′ rest)
    where
    lemma₁ :
      (⊩Σ : Γ ⊩⟨ l ⟩B⟨ BΣ 𝕨 p q ⟩ Σʷ p , q ▷ A ▹ B) →
      Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Σʷ p , q ▷ A ▹ B / B-intr (BΣ 𝕨 p q) ⊩Σ →
      ∃₂ λ u₁ u₂ →
      Γ ⊢ t₁ ⇒* u₁ ∷ Σʷ p , q ▷ A ▹ B ×
      Γ ⊢ t₂ ⇒* u₂ ∷ Σʷ p , q ▷ A ▹ B ×
      Γ ⊢ u₁ ≅ u₂ ∷ Σʷ p , q ▷ A ▹ B ×
      Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷Σʷ p , q ▷ A ▹ B
    lemma₁ (emb ≤ᵘ-refl ⊩Σ) t₁≡t₂ =
      case lemma₁ ⊩Σ t₁≡t₂ of λ
        (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≅u₂ , u₁≡u₂) →
        u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≅u₂
      , (case u₁≡u₂ of λ where
           (prodₙ u₁₁≡u₂₁ u₁₂≡u₂₂) →
             prodₙ (emb-⊩≡∷ (≤ᵘ-step ≤ᵘ-refl) u₁₁≡u₂₁)
               (emb-⊩≡∷ (≤ᵘ-step ≤ᵘ-refl) u₁₂≡u₂₂)
           (ne u₁-ne u₂-ne u₁~u₂) →
             ne u₁-ne u₂-ne u₁~u₂)
    lemma₁ (emb (≤ᵘ-step l<) ⊩Σ) t₁≡t₂ =
      case lemma₁ (emb l< ⊩Σ) t₁≡t₂ of λ
        (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≅u₂ , u₁≡u₂) →
        u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≅u₂
      , (case u₁≡u₂ of λ where
           (prodₙ u₁₁≡u₂₁ u₁₂≡u₂₂) →
             prodₙ (emb-⊩≡∷ (≤ᵘ-step ≤ᵘ-refl) u₁₁≡u₂₁)
               (emb-⊩≡∷ (≤ᵘ-step ≤ᵘ-refl) u₁₂≡u₂₂)
           (ne u₁-ne u₂-ne u₁~u₂) →
             ne u₁-ne u₂-ne u₁~u₂)
    lemma₁
      ⊩Σ@(noemb (Bᵣ _ _ Σ⇒*Σ _ ⊩wk-A ⊩wk-B wk-B≡wk-B _))
      (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≅u₂ , ⊩t₁ , ⊩t₂ ,
       u₁-prod , u₂-prod , rest) =
      let ⊩Σ′ = B-intr _ ⊩Σ in
      case B-PE-injectivity _ _ $ whnfRed* Σ⇒*Σ ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
        u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≅u₂
      , (case PE.singleton u₁-prod of λ where
           (ne u₁-ne , PE.refl) →
             case PE.singleton u₂-prod of λ {
               (prodₙ    , PE.refl) → ⊥-elim (Lift.lower rest);
               (ne u₂-ne , PE.refl) → ne u₁-ne u₂-ne rest }
           (prodₙ , PE.refl) →
             case PE.singleton u₂-prod of λ {
               (ne _  , PE.refl) → ⊥-elim (Lift.lower rest);
               (prodₙ , PE.refl) →
             (case rest of λ {
               (_ , _ , ⊩u₁₁ , ⊩u₂₁ , ⊩u₁₂ , ⊩u₂₂ , u₁₁≡u₂₁ , u₁₂≡u₂₂) →
             case ⊩∷Σʷ⇔ .proj₁ (⊩∷-intro ⊩Σ′ ⊩t₁) of λ
               (_ , _ , t₁⇒*u₁′ , _ , ⊩u₁′) →
             case ⊩∷Σʷ⇔ .proj₁ (⊩∷-intro ⊩Σ′ ⊩t₂) of λ
               (_ , _ , t₂⇒*u₂′ , _ , ⊩u₂′) →
             case whrDet*Term
                    (t₁⇒*u₁′ , productWhnf (⊩∷Σʷ→Product ⊩u₁′))
                    (t₁⇒*u₁ , prodₙ) of λ {
               PE.refl →
             case whrDet*Term
                    (t₂⇒*u₂′ , productWhnf (⊩∷Σʷ→Product ⊩u₂′))
                    (t₂⇒*u₂ , prodₙ) of λ {
               PE.refl →
             case ⊩u₁′ of λ {
               (ne () _);
               (prodₙ _ _) →
             case ⊩u₂′ of λ {
               (ne () _);
               (prodₙ _ _) →
             prodₙ
               (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-id _)
                  (⊩wk-A id _ , ⊩u₁₁ , ⊩u₂₁ , u₁₁≡u₂₁))
               (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                  (PE.cong _[ _ ]₀ $ wk-lift-id B)
                  ( ⊩wk-B id _ _ , ⊩u₁₂
                  , convTerm₁ (⊩wk-B id _ _) (⊩wk-B id _ _)
                      (wk-B≡wk-B id _ ⊩u₂₁ ⊩u₁₁ $
                       symEqTerm (⊩wk-A id _) u₁₁≡u₂₁)
                      ⊩u₂₂
                  , u₁₂≡u₂₂
                  )) }}}}})}) }

    lemma₂ :
      (⊩Σ : Γ ⊩⟨ l′ ⟩B⟨ BΣ 𝕨 p q ⟩ Σʷ p , q ▷ A ▹ B) →
      (∃₂ λ u₁ u₂ →
       Γ ⊢ t₁ ⇒* u₁ ∷ Σʷ p , q ▷ A ▹ B ×
       Γ ⊢ t₂ ⇒* u₂ ∷ Σʷ p , q ▷ A ▹ B ×
       Γ ⊢ u₁ ≅ u₂ ∷ Σʷ p , q ▷ A ▹ B ×
       Γ ⊩⟨ l ⟩ u₁ ≡ u₂ ∷Σʷ p , q ▷ A ▹ B) →
      let ⊩Σ′ = B-intr (BΣ 𝕨 p q) ⊩Σ in
      Γ ⊩⟨ l′ ⟩ t₁ ∷ Σʷ p , q ▷ A ▹ B / ⊩Σ′ ×
      Γ ⊩⟨ l′ ⟩ t₂ ∷ Σʷ p , q ▷ A ▹ B / ⊩Σ′ ×
      Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ Σʷ p , q ▷ A ▹ B / ⊩Σ′
    lemma₂ (emb 0<1 ⊩Σ) rest =
      let ⊩Σ₁ = B-intr _ ⊩Σ
          ⊩Σ₂ = B-intr _ (emb 0<1 ⊩Σ)
      in
      case lemma₂ ⊩Σ rest of λ
        (⊩t₁ , ⊩t₂ , t₁≡t₂) →
        irrelevanceTerm ⊩Σ₁ ⊩Σ₂ ⊩t₁
      , irrelevanceTerm ⊩Σ₁ ⊩Σ₂ ⊩t₂
      , irrelevanceEqTerm ⊩Σ₁ ⊩Σ₂ t₁≡t₂
    lemma₂
      ⊩Σ@(noemb (Bᵣ _ _ Σ⇒*Σ _ ⊩wk-A ⊩wk-B _ _))
      (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≅u₂ , u₁≡u₂) =
      case B-PE-injectivity _ _ $ whnfRed* Σ⇒*Σ ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      let ⊩Σ′       = B-intr _ ⊩Σ
          ≅u₁ , ≅u₂ = wf-⊢≅∷ u₁≅u₂
      in
      case ⊩ΠΣ→ ⊩Σ′ of λ
        (_ , ⊩A , _) →
      case ⊩∷→⊩∷/ ⊩Σ′ $
           ⊩∷Σʷ⇔ .proj₂
             ( ⊩Σ′
             , u₁ , t₁⇒*u₁ , ≅u₁
             , (case u₁≡u₂ of λ where
                  (prodₙ u₁₁≡u₂₁ u₁₂≡u₂₂) →
                    case wf-⊩≡∷ u₁₁≡u₂₁ of λ
                      (⊩u₁₁ , _) →
                    prodₙ (level-⊩∷ ⊩A ⊩u₁₁)
                      (level-⊩∷ (⊩ΠΣ→⊩∷→⊩[]₀ ⊩Σ′ ⊩u₁₁) $
                       wf-⊩≡∷ u₁₂≡u₂₂ .proj₁)
                  (ne u₁-ne _ u₁~u₂) →
                    ne u₁-ne (wf-⊢~∷ u₁~u₂ .proj₁))
             ) of λ
        ⊩t₁ →
      case ⊩∷→⊩∷/ ⊩Σ′ $
           ⊩∷Σʷ⇔ .proj₂
             ( ⊩Σ′
             , u₂ , t₂⇒*u₂ , ≅u₂
             , (case u₁≡u₂ of λ where
                  (prodₙ u₁₁≡u₂₁ u₁₂≡u₂₂) →
                    case wf-⊩≡∷ u₁₁≡u₂₁ of λ
                      (_ , ⊩u₂₁) →
                    prodₙ (level-⊩∷ ⊩A ⊩u₂₁)
                      (conv-⊩∷
                         (⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩Σ′) u₁₁≡u₂₁) $
                       wf-⊩≡∷ u₁₂≡u₂₂ .proj₂)
                  (ne _ u₂-ne u₁~u₂) →
                    ne u₂-ne (wf-⊢~∷ u₁~u₂ .proj₂))
             ) of λ
        ⊩t₂ →
      _ ⊩⟨ _ ⟩ _ ∷ _ / ⊩Σ′ × _ ⊩⟨ _ ⟩ _ ∷ _ / ⊩Σ′ ×
        _ ⊩⟨ _ ⟩ _ ≡ _ ∷ _ / ⊩Σ′ ∋
        ⊩t₁ , ⊩t₂
      , ( u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≅u₂ , ⊩t₁ , ⊩t₂
        , (case u₁≡u₂ of λ where
             (prodₙ u₁₁≡u₂₁ u₁₂≡u₂₂) →
               case wf-⊩≡∷ u₁₁≡u₂₁ of λ
                 (⊩u₁₁ , ⊩u₂₁) →
               case wf-⊩≡∷ u₁₂≡u₂₂ of λ
                 (⊩u₁₂ , ⊩u₂₂) →
                 prodₙ , prodₙ , PE.refl , PE.refl
               , ⊩∷→⊩∷/ (⊩wk-A id _)
                   (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk-id _) ⊩u₁₁)
               , ⊩∷→⊩∷/ (⊩wk-A id _)
                   (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk-id _) ⊩u₂₁)
               , ⊩∷→⊩∷/ (⊩wk-B id _ _)
                   (PE.subst (_⊩⟨_⟩_∷_ _ _ _)
                      (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id B) ⊩u₁₂)
               , ⊩∷→⊩∷/ (⊩wk-B id _ _)
                   (PE.subst (_⊩⟨_⟩_∷_ _ _ _)
                      (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id B) $
                    conv-⊩∷ (⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩Σ′) u₁₁≡u₂₁)
                      ⊩u₂₂)
               , ⊩≡∷→⊩≡∷/ (⊩wk-A id _)
                   (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk-id _)
                      u₁₁≡u₂₁)
               , ⊩≡∷→⊩≡∷/ (⊩wk-B id _ _)
                   (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                      (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id B) u₁₂≡u₂₂)
             (ne u₁-ne u₂-ne u₁~u₂) →
               ne u₁-ne , ne u₂-ne , u₁~u₂)
        ) }

------------------------------------------------------------------------
-- Pairs

opaque

  -- Reducibility of equality between applications of prodʷ.

  ⊩prodʷ≡prodʷ :
    Γ »∙ A ⊢ B →
    Γ ⊩⟨ l ⟩ Σʷ p , q ▷ A ▹ B →
    Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩⟨ l″ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊩⟨ l ⟩ prodʷ p t₁ u₁ ≡ prodʷ p t₂ u₂ ∷ Σʷ p , q ▷ A ▹ B
  ⊩prodʷ≡prodʷ {B} {p} {t₁} {t₂} {u₁} {u₂} ⊢B ⊩ΣAB t₁≡t₂ u₁≡u₂ =
    case ⊩ΠΣ→ ⊩ΣAB of λ
      (ok , ⊩A , _) →
    case wf-⊩≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case wf-⊩≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case conv-⊩∷ (⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩ΣAB) t₁≡t₂) ⊩u₂ of λ
      ⊩u₂ →
    ⊩≡∷Σʷ⇔ .proj₂
      ( ⊩ΣAB
      , _ , _
      , id (prodⱼ ⊢B (escape-⊩∷ ⊩t₁) (escape-⊩∷ ⊩u₁) ok)
      , id (prodⱼ ⊢B (escape-⊩∷ ⊩t₂) (escape-⊩∷ ⊩u₂) ok)
      , ≅-prod-cong ⊢B (escape-⊩≡∷ t₁≡t₂) (escape-⊩≡∷ u₁≡u₂) ok
      , prodₙ (level-⊩≡∷ ⊩A t₁≡t₂)
          (level-⊩≡∷ (⊩ΠΣ→⊩∷→⊩[]₀ ⊩ΣAB ⊩t₁) u₁≡u₂)
      )

private opaque

  -- Reducibility of equality between applications of prodʷ.

  ⊩prodʷ[]≡prodʷ[] :
    Σʷ-allowed p q →
    ∇ » Δ ∙ A ⊢ B →
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B →
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A →
    ∇ » Δ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ prodʷ p t₁ u₁ [ σ₁ ] ≡ prodʷ p t₂ u₂ [ σ₂ ] ∷
      (Σʷ p , q ▷ A ▹ B) [ σ₁ ]
  ⊩prodʷ[]≡prodʷ[] {B} ok ⊢B ⊩B t₁≡t₂ u₁≡u₂ σ₁≡σ₂ =
    case wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁ of λ
      ⊩A →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , _) →
    ⊩prodʷ≡prodʷ (subst-⊢-⇑ ⊢B (escape-⊩ˢ∷ ⊩σ₁ .proj₂))
      (⊩ΠΣ (ΠΣⱼ ⊢B ok) ⊩A ⊩B ⊩σ₁)
      (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂)
      (R.⊩≡∷→ $
       PE.subst (R._⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B _) $
       ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂)

opaque

  -- Validity of equality preservation for prodʷ.

  prodʷ-congᵛ :
    Σʷ-allowed p q →
    Γ »∙ A ⊢ B →
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ prodʷ p t₁ u₁ ≡ prodʷ p t₂ u₂ ∷ Σʷ p , q ▷ A ▹ B
  prodʷ-congᵛ ok ⊢B ⊩B t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ΠΣᵛ (ΠΣⱼ ⊢B ok) (wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁) ⊩B
      , λ ξ⊇ → ⊩prodʷ[]≡prodʷ[] ok
                                (defn-wk ξ⊇ ⊢B)
                                (defn-wk-⊩ᵛ ξ⊇ ⊩B)
                                (defn-wk-⊩ᵛ≡∷ ξ⊇ t₁≡t₂)
                                (defn-wk-⊩ᵛ≡∷ ξ⊇ u₁≡u₂)
      )

opaque

  -- Validity of prodʷ.

  prodʷᵛ :
    Σʷ-allowed p q →
    Γ »∙ A ⊢ B →
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ B [ t ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ prodʷ p t u ∷ Σʷ p , q ▷ A ▹ B
  prodʷᵛ ok ⊢B ⊩B ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    prodʷ-congᵛ ok ⊢B ⊩B (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)

------------------------------------------------------------------------
-- The eliminator prodrec

private opaque

  -- A lemma used below.

  [1,0]↑²[⇑⇑][]₁₀≡[⇑][,]₀ :
    ∀ A →
    A [ prodʷ p (var x1) (var x0) ]↑² [ σ ⇑ ⇑ ] [ t , u ]₁₀ PE.≡
    A [ σ ⇑ ] [ prodʷ p t u ]₀
  [1,0]↑²[⇑⇑][]₁₀≡[⇑][,]₀ {p} {σ} {t} {u} A =
    A [ prodʷ p (var x1) (var x0) ]↑² [ σ ⇑ ⇑ ] [ t , u ]₁₀  ≡⟨ PE.cong _[ _ , _ ]₁₀ $ subst-β-prodrec A _ ⟩
    A [ σ ⇑ ] [ prodʷ p (var x1) (var x0) ]↑² [ t , u ]₁₀    ≡⟨ [1,0]↑²[,] (A [ _ ]) ⟩
    A [ σ ⇑ ] [ prodʷ p t u ]₀                               ∎

opaque

  -- Reducibility of equality between applications of prodrec.

  ⊩prodrec≡prodrec :
    ∇ » Δ ∙ Σʷ p , q′ ▷ A ▹ B ⊢ C₁ ≡ C₂ →
    ∇ » Δ ∙ Σʷ p , q′ ▷ A ▹ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    ∇ » Δ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ Σʷ p , q′ ▷ A ▹ B →
    ∇ » Δ ∙ A ∙ B ⊢ u₁ ≡ u₂ ∷ C₁ [ prodʷ p (var x1) (var x0) ]↑² →
    ∇ » Δ ∙ A ∙ B ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ C₁ [ prodʷ p (var x1) (var x0) ]↑² →
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ prodrec r p q C₁ t₁ u₁ [ σ₁ ] ≡
      prodrec r p q C₂ t₂ u₂ [ σ₂ ] ∷ C₁ [ t₁ ]₀ [ σ₁ ]
  ⊩prodrec≡prodrec
    {∇} {p} {q′} {A} {B} {C₁} {C₂} {l} {t₁} {t₂} {u₁} {u₂} {Η} {σ₁} {σ₂}
    {r} {q} ⊢C₁≡C₂ C₁≡C₂ t₁≡t₂ ⊢u₁≡u₂ u₁≡u₂ σ₁≡σ₂ =
    case wf-⊢≡ ⊢C₁≡C₂ of λ
      (⊢C₁ , ⊢C₂) →
    case wf-⊩ᵛ≡ C₁≡C₂ of λ
      (⊩C₁ , _) →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , _) →
    case escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂ of λ
      ⊢σ₁≡σ₂ →
    case wf-⊢ˢʷ≡∷ ⊢σ₁≡σ₂ of λ
      (_ , ⊢σ₁ , ⊢σ₂) →
    case subst-⊢-⇑ ⊢C₁ ⊢σ₁ of λ
      ⊢C₁[σ₁⇑] →
    case subst-⊢-⇑ ⊢C₂ ⊢σ₂ of λ
      ⊢C₂[σ₂⇑] →
    case R.⊩≡→ $
         ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (refl-⊩ᵛ≡ $ wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
           σ₁≡σ₂ of λ
      ΣAB[σ₁]≡ΣAB[σ₂] →
    case ⊩ΠΣ→ (wf-⊩≡ ΣAB[σ₁]≡ΣAB[σ₂] .proj₁) of λ
      (ok , _ , _) →
    case ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂ of λ
      t₁[σ₁]≡t₂[σ₂] →
    case wf-⊩≡∷ $ R.⊩≡∷→ t₁[σ₁]≡t₂[σ₂] of λ
      (⊩t₁[σ₁] , ⊩t₂[σ₂]) →
    case conv-⊩∷ ΣAB[σ₁]≡ΣAB[σ₂] ⊩t₂[σ₂] of λ
      ⊩t₂[σ₂] →
    case wf-⊢≡∷ ⊢u₁≡u₂ of λ
      (_ , ⊢u₁ , ⊢u₂) →
    case PE.subst (_⊢_∷_ _ _) (subst-β-prodrec C₁ _) $
         subst-⊢∷-⇑ ⊢u₁ ⊢σ₁ of λ
      ⊢u₁[σ₁⇑⇑] →
    case PE.subst (_⊢_∷_ _ _) (subst-β-prodrec C₂ _) $
         subst-⊢∷-⇑ (conv ⊢u₂ (subst↑²TypeEq-prod ⊢C₁≡C₂)) ⊢σ₂ of λ
      ⊢u₂[σ₂⇑⇑] →
    case ⊩≡∷Σʷ⇔ .proj₁ $ R.⊩≡∷→ t₁[σ₁]≡t₂[σ₂] of λ
      (_ , v₁ , v₂ , t₁[σ₁]⇒*v₁ , t₂[σ₂]⇒*v₂ , _ , v₁≡v₂∷Σʷ) →
    case conv* t₂[σ₂]⇒*v₂ $
         ≅-eq $ escape-⊩≡ ΣAB[σ₁]≡ΣAB[σ₂] of λ
      t₂[σ₂]⇒*v₂ →
    case ⊩∷-⇒* t₁[σ₁]⇒*v₁ ⊩t₁[σ₁] of λ
      t₁[σ₁]≡v₁ →
    case ⊩∷-⇒* t₂[σ₂]⇒*v₂ ⊩t₂[σ₂] of λ
      t₂[σ₂]≡v₂ →
    case
      v₁                                      ≡˘⟨ t₁[σ₁]≡v₁ ⟩⊩∷
      t₁ [ σ₁ ] ∷ (Σʷ p , q′ ▷ A ▹ B) [ σ₁ ]  ≡⟨ R.⊩≡∷→ t₁[σ₁]≡t₂[σ₂] ⟩⊩∷∷
                                               ⟨ ΣAB[σ₁]≡ΣAB[σ₂] ⟩⊩∷
      t₂ [ σ₂ ] ∷ (Σʷ p , q′ ▷ A ▹ B) [ σ₂ ]  ≡⟨ t₂[σ₂]≡v₂ ⟩⊩∷∎∷
      v₂                                      ∎
    of λ
      v₁≡v₂ →
    case R.⊩≡→ $
         ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ C₁≡C₂ σ₁≡σ₂ (R.→⊩≡∷ v₁≡v₂) of λ
      C₁[σ₁⇑][v₁]≡C₂[σ₂⇑][v₂] →
    case wf-⊩≡ C₁[σ₁⇑][v₁]≡C₂[σ₂⇑][v₂] of λ
      (⊩C₁[σ₁⇑][v₁] , _) →
    case ≅-eq $ escape-⊩≡ C₁[σ₁⇑][v₁]≡C₂[σ₂⇑][v₂] of λ
      C₁[σ₁⇑][v₁]≡C₂[σ₂⇑][v₂] →
    case
      ∇ » Η ⊩⟨ l ⟩ prodrec r p q (C₁ [ σ₁ ⇑ ]) v₁ (u₁ [ σ₁ ⇑ ⇑ ]) ≡
        prodrec r p q (C₂ [ σ₂ ⇑ ]) v₂ (u₂ [ σ₂ ⇑ ⇑ ]) ∷
        C₁ [ σ₁ ⇑ ] [ v₁ ]₀ ∋
      (case v₁≡v₂∷Σʷ of λ where
         (prodₙ {t₁₁ = v₁₁} {t₂₁ = v₂₁} {t₁₂ = v₁₂} {t₂₂ = v₂₂}
            v₁₁≡v₂₁ v₁₂≡v₂₂) →
           case wf-⊩≡∷ v₁₁≡v₂₁ of λ
             (⊩v₁₁ , ⊩v₂₁) →
           case conv-⊩∷
                  (⊩ΠΣ≡ΠΣ→ ΣAB[σ₁]≡ΣAB[σ₂]
                     .proj₂ .proj₂ .proj₂ .proj₂ .proj₁)
                  ⊩v₂₁ of λ
             ⊩v₂₁ →
           case wf-⊩≡∷ v₁₂≡v₂₂ of λ
             (⊩v₁₂ , ⊩v₂₂) →
           case conv-⊩∷ (⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ ΣAB[σ₁]≡ΣAB[σ₂] v₁₁≡v₂₁)
                  ⊩v₂₂ of λ
             ⊩v₂₂ →

           prodrec r p q (C₁ [ σ₁ ⇑ ]) (prodʷ p v₁₁ v₁₂) (u₁ [ σ₁ ⇑ ⇑ ])  ⇒⟨ prodrec-β ⊢C₁[σ₁⇑] (escape-⊩∷ ⊩v₁₁) (escape-⊩∷ ⊩v₁₂)
                                                                               ⊢u₁[σ₁⇑⇑] PE.refl ok ⟩⊩∷
           u₁ [ σ₁ ⇑ ⇑ ] [ v₁₁ , v₁₂ ]₁₀ ∷ C₁ [ σ₁ ⇑ ] [ v₁ ]₀            ≡⟨ level-⊩≡∷ ⊩C₁[σ₁⇑][v₁] $
                                                                             PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) ([1,0]↑²[⇑⇑][]₁₀≡[⇑][,]₀ C₁) $
                                                                             R.⊩≡∷→ $
                                                                             ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷
                                                                               u₁≡u₂ σ₁≡σ₂ (R.→⊩≡∷ v₁₁≡v₂₁) (R.→⊩≡∷ v₁₂≡v₂₂) ⟩⊩∷∷⇐*
                                                                           ⟨ C₁[σ₁⇑][v₁]≡C₂[σ₂⇑][v₂] ⟩⇒
           u₂ [ σ₂ ⇑ ⇑ ] [ v₂₁ , v₂₂ ]₁₀ ∷ C₂ [ σ₂ ⇑ ] [ v₂ ]₀            ⇐⟨ prodrec-β ⊢C₂[σ₂⇑] (escape-⊩∷ ⊩v₂₁) (escape-⊩∷ ⊩v₂₂)
                                                                               ⊢u₂[σ₂⇑⇑] PE.refl ok
                                                                           ⟩∎∷
           prodrec r p q (C₂ [ σ₂ ⇑ ]) (prodʷ p v₂₁ v₂₂) (u₂ [ σ₂ ⇑ ⇑ ])  ∎

         (ne v₁-ne v₂-ne v₁~v₂) →
           neutral-⊩≡∷ ⊩C₁[σ₁⇑][v₁]
             (prodrecₙ v₁-ne) (prodrecₙ v₂-ne) $
           ~-prodrec
             (with-inc-⊢≅ (subst-⊢≡ ⊢C₁≡C₂ (⊢ˢʷ≡∷-⇑ (≅-eq (escape-⊩≡ ΣAB[σ₁]≡ΣAB[σ₂])) ⊢σ₁≡σ₂)) $
              R.escape-⊩≡ ⦃ inc = included ⦄ $
              ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] C₁≡C₂ σ₁≡σ₂)
             v₁~v₂
             (PE.subst (_⊢_≅_∷_ _ _ _) (subst-β-prodrec C₁ _) $
              with-inc-⊢≅∷ (subst-⊢≡∷-⇑ ⊢u₁≡u₂ ⊢σ₁≡σ₂) $
              R.escape-⊩≡∷ ⦃ inc = included ⦄ $
              ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ u₁≡u₂ σ₁≡σ₂) ok)
    of λ
      lemma →
                                  ∷ C₁ [ t₁ ]₀ [ σ₁ ]             ⟨ singleSubstLift C₁ _ ⟩⊩∷∷≡

    prodrec r p q C₁ t₁ u₁ [ σ₁ ] ∷ C₁ [ σ₁ ⇑ ] [ t₁ [ σ₁ ] ]₀  ⇒*⟨ prodrec-subst* ⊢C₁[σ₁⇑] t₁[σ₁]⇒*v₁ ⊢u₁[σ₁⇑⇑] ⟩⊩∷∷

    prodrec r p q (C₁ [ σ₁ ⇑ ]) v₁ (u₁ [ σ₁ ⇑ ⇑ ])              ≡⟨ conv-⊩≡∷
                                                                     (R.⊩≡→ $
                                                                      ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩C₁)
                                                                        (refl-⊩ˢ≡∷ ⊩σ₁) (R.→⊩≡∷ $ sym-⊩≡∷ t₁[σ₁]≡v₁))
                                                                     lemma ⟩⊩∷⇐*
                                                                 ⟨ ≅-eq $ R.escape-⊩≡ $
                                                                   ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ C₁≡C₂ σ₁≡σ₂ t₁[σ₁]≡t₂[σ₂] ⟩⇒
    prodrec r p q (C₂ [ σ₂ ⇑ ]) v₂ (u₂ [ σ₂ ⇑ ⇑ ]) ∷
      C₂ [ σ₂ ⇑ ] [ t₂ [ σ₂ ] ]₀                                ⇐*⟨ prodrec-subst* ⊢C₂[σ₂⇑] t₂[σ₂]⇒*v₂ ⊢u₂[σ₂⇑⇑] ⟩∎∷
    prodrec r p q C₂ t₂ u₂ [ σ₂ ]                               ∎

opaque

  -- Validity of equality preservation for prodrec.

  prodrec-congᵛ :
    Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C₁ ≡ C₂ →
    Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    Γ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ Σʷ p , q′ ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ u₁ ≡ u₂ ∷ C₁ [ prodʷ p (var x1) (var x0) ]↑² →
    Γ »∙ A »∙ B ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ C₁ [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊩ᵛ⟨ l ⟩ prodrec r p q C₁ t₁ u₁ ≡ prodrec r p q C₂ t₂ u₂ ∷
      C₁ [ t₁ ]₀
  prodrec-congᵛ ⊢C₁≡C₂ C₁≡C₂ t₁≡t₂ ⊢u₁≡u₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ (wf-⊩ᵛ≡ C₁≡C₂ .proj₁) (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)
      , λ ξ⊇ → ⊩prodrec≡prodrec (defn-wkEq ξ⊇ ⊢C₁≡C₂)
                                (defn-wk-⊩ᵛ≡ ξ⊇ C₁≡C₂)
                                (defn-wk-⊩ᵛ≡∷ ξ⊇ t₁≡t₂)
                                (defn-wkEqTerm ξ⊇ ⊢u₁≡u₂)
                                (defn-wk-⊩ᵛ≡∷ ξ⊇ u₁≡u₂)
      )

opaque

  -- Validity of prodrec.

  prodrecᵛ :
    Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C →
    Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊩ᵛ⟨ l ⟩ C →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ Σʷ p , q′ ▷ A ▹ B →
    Γ »∙ A »∙ B ⊢ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ »∙ A »∙ B ⊩ᵛ⟨ l″ ⟩ u ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊩ᵛ⟨ l ⟩ prodrec r p q C t u ∷ C [ t ]₀
  prodrecᵛ ⊢C ⊩C ⊩t ⊢u ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    prodrec-congᵛ (refl ⊢C) (refl-⊩ᵛ≡ ⊩C) (refl-⊩ᵛ≡∷ ⊩t) (refl ⊢u)
      (refl-⊩ᵛ≡∷ ⊩u)

opaque

  -- Validity of prodrec-β.

  prodrec-βᵛ :
    Γ »∙ Σʷ p , q′ ▷ A ▹ B ⊢ C →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ B [ t ]₀ →
    Γ »∙ A »∙ B ⊢ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ »∙ A »∙ B ⊩ᵛ⟨ l ⟩ v ∷ C [ prodʷ p (var x1) (var x0) ]↑² →
    Γ ⊩ᵛ⟨ l ⟩ prodrec r p q C (prodʷ p t u) v ≡ v [ t , u ]₁₀ ∷
      C [ prodʷ p t u ]₀
  prodrec-βᵛ {B} {C} {v} ⊢C ⊩t ⊩u ⊢v ⊩v =
    ⊩ᵛ∷-⇐
      (λ ξ⊇ ⊩σ →
         let _ , ⊢σ = escape-⊩ˢ∷ ⊩σ
             ⊢C = defn-wk ξ⊇ ⊢C
             ⊩t = defn-wk-⊩ᵛ∷ ξ⊇ ⊩t
             ⊩u = defn-wk-⊩ᵛ∷ ξ⊇ ⊩u
             ⊢v = defn-wkTerm ξ⊇ ⊢v
             ⊩v = defn-wk-⊩ᵛ∷ ξ⊇ ⊩v
         in
         PE.subst₂ (_⊢_⇒_∷_ _ _) (PE.sym $ [,]-[]-commute v)
           (PE.sym $ singleSubstLift C _) $
         prodrec-β-⇒ (subst-⊢-⇑ ⊢C ⊢σ)
           (R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
            R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩u ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (subst-β-prodrec C _) $
            subst-⊢∷-⇑ ⊢v ⊢σ))
      (PE.subst (_⊩ᵛ⟨_⟩_∷_ _ _ _) ([1,0]↑²[,] C) $
       ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ ⊩v ⊩t ⊩u)
