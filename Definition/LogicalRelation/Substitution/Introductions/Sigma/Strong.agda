------------------------------------------------------------------------
-- Validity for strong Σ-types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module
  Definition.LogicalRelation.Substitution.Introductions.Sigma.Strong
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
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import
  Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma R
open import Definition.LogicalRelation.Weakening.Restricted R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Substitution R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  ∇                   : DCon (Term 0) _
  Δ Η                 : Con Term _
  Γ                   : Cons _ _
  A B t t₁ t₂ u u₁ u₂ : Term _
  σ₁ σ₂               : Subst _ _
  p q                 : M
  l l′ l″ l‴          : Universe-level

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Σˢ⇔ :
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B ⇔
    (Γ ⊩⟨ l ⟩ Σˢ p , q ▷ A ▹ B ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t₁ ⇒* u₁ ∷ Σˢ p , q ▷ A ▹ B ×
     Γ ⊢ t₂ ⇒* u₂ ∷ Σˢ p , q ▷ A ▹ B ×
     Productᵃₗ (Γ .defs) u₁ ×
     Productᵃₗ (Γ .defs) u₂ ×
     Γ ⊢ u₁ ≅ u₂ ∷ Σˢ p , q ▷ A ▹ B ×
     Γ ⊩⟨ l ⟩ fst p u₁ ≡ fst p u₂ ∷ A ×
     Γ ⊩⟨ l ⟩ snd p u₁ ≡ snd p u₂ ∷ B [ fst p u₁ ]₀)
  ⊩≡∷Σˢ⇔ {Γ} {l} {t₁} {t₂} {p} {q} {A} {B} =
      (λ (⊩Σ , t₁≡t₂) →
         case B-view ⊩Σ of λ {
           (Bᵣ (Bᵣ _ _ Σ⇒*Σ _ ⊩wk-A ⊩wk-B _ _)) →
         case t₁≡t₂ of λ
           (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≅u₂ ,
            u₁-prod , u₂-prod , ⊩fst-u₁ , _ , fst≡fst , snd≡snd) →
         case B-PE-injectivity _ _ $ whnfRed* Σ⇒*Σ ΠΣₙ of λ {
           (PE.refl , PE.refl , _) →
         ⊩Σ ,
         ((∃₂ λ u₁ u₂ →
          Γ ⊢ t₁ ⇒* u₁ ∷ Σˢ p , q ▷ A ▹ B ×
          Γ ⊢ t₂ ⇒* u₂ ∷ Σˢ p , q ▷ A ▹ B ×
          Productᵃₗ (Γ .defs) u₁ ×
          Productᵃₗ (Γ .defs) u₂ ×
          Γ ⊢ u₁ ≅ u₂ ∷ Σˢ p , q ▷ A ▹ B ×
          Γ ⊩⟨ l ⟩ fst p u₁ ≡ fst p u₂ ∷ A ×
          Γ ⊩⟨ l ⟩ snd p u₁ ≡ snd p u₂ ∷ B [ fst p u₁ ]₀) ∋
           u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-prod , u₂-prod , u₁≅u₂
         , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-id _)
             (⊩wk-A _ _ , fst≡fst)
         , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.cong _[ _ ]₀ $ wk-lift-id B)
             (⊩wk-B _ _ ⊩fst-u₁ , snd≡snd)) }})
    , (λ (⊩Σ , rest) →
         case B-view ⊩Σ of λ {
           (Bᵣ ⊩Σ′@(Bᵣ _ _ Σ⇒*Σ A≡A ⊩wk-A ⊩wk-B _ _)) →
         case rest of λ
           (u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁-prod , u₂-prod , u₁≅u₂ ,
            fst≡fst , snd≡snd) →
         case B-PE-injectivity _ _ $ whnfRed* Σ⇒*Σ ΠΣₙ of λ {
           (PE.refl , PE.refl , _) →
         let ⊩wk-id-A  = ⊩wk-A _ (id (wfEq (≅-eq A≡A))) in
         case wf-⊩≡∷ $
              level-⊩≡∷ (PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩wk-id-A)
                fst≡fst of λ
           (⊩fst-u₁ , ⊩fst-u₂) →
         case ⊩∷→⊩∷/ ⊩wk-id-A $
              PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk-id _) ⊩fst-u₁ of λ
           ⊩fst-u₁′ →
         case ⊩∷→⊩∷/ ⊩wk-id-A $
              PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk-id _) ⊩fst-u₂ of λ
           ⊩fst-u₂′ →
         case ⊩≡∷→⊩≡∷/ ⊩wk-id-A $
              PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk-id _) fst≡fst of λ
           fst≡fst′ →
         Bᵣ _ ⊩Σ′ ,
         (_ ⊩⟨ _ ⟩ _ ≡ _ ∷ _ / Bᵣ _ ⊩Σ′ ∋
         u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , u₁≅u₂ ,
         u₁-prod , u₂-prod , ⊩fst-u₁′ , ⊩fst-u₂′ , fst≡fst′ ,
         ⊩≡∷→⊩≡∷/ (⊩wk-B _ _ ⊩fst-u₁′)
           (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
              (PE.sym $ PE.cong _[ _ ] $ wk-lift-id B) snd≡snd)) }})

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Σˢ⇔ :
    Γ ⊩⟨ l ⟩ t ∷ Σˢ p , q ▷ A ▹ B ⇔
    (Γ ⊩⟨ l ⟩ Σˢ p , q ▷ A ▹ B ×
     ∃ λ u →
     Γ ⊢ t ⇒* u ∷ Σˢ p , q ▷ A ▹ B ×
     Productᵃₗ (Γ .defs) u ×
     Γ ⊢≅ u ∷ Σˢ p , q ▷ A ▹ B ×
     Γ ⊩⟨ l ⟩ fst p u ∷ A ×
     Γ ⊩⟨ l ⟩ snd p u ∷ B [ fst p u ]₀)
  ⊩∷Σˢ⇔ {Γ} {l} {t} {p} {q} {A} {B} =
    Γ ⊩⟨ l ⟩ t ∷ Σˢ p , q ▷ A ▹ B                     ⇔⟨ ⊩∷⇔⊩≡∷ ⟩

    Γ ⊩⟨ l ⟩ t ≡ t ∷ Σˢ p , q ▷ A ▹ B                 ⇔⟨ ⊩≡∷Σˢ⇔ ⟩

    (Γ ⊩⟨ l ⟩ Σˢ p , q ▷ A ▹ B ×
     ∃₂ λ u₁ u₂ →
     Γ ⊢ t ⇒* u₁ ∷ Σˢ p , q ▷ A ▹ B ×
     Γ ⊢ t ⇒* u₂ ∷ Σˢ p , q ▷ A ▹ B ×
     Productᵃₗ (Γ .defs) u₁ ×
     Productᵃₗ (Γ .defs) u₂ ×
     Γ ⊢ u₁ ≅ u₂ ∷ Σˢ p , q ▷ A ▹ B ×
     Γ ⊩⟨ l ⟩ fst p u₁ ≡ fst p u₂ ∷ A ×
     Γ ⊩⟨ l ⟩ snd p u₁ ≡ snd p u₂ ∷ B [ fst p u₁ ]₀)  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                            ( (λ (_ , t⇒*u₁ , t⇒*u₂ , u₁-prod , u₂-prod ,
                                                                  u₁≅u₂ , fst≡fst , snd≡snd) →
                                                                 t⇒*u₁ , u₁-prod , wf-⊢≅∷ u₁≅u₂ .proj₁ ,
                                                                 wf-⊩≡∷ fst≡fst .proj₁ , wf-⊩≡∷ snd≡snd .proj₁)
                                                            , (λ (t⇒*u , u-prod , ≅u , ⊩fst , ⊩snd) →
                                                                 _ , t⇒*u , t⇒*u , u-prod , u-prod , ≅u ,
                                                                 refl-⊩≡∷ ⊩fst , refl-⊩≡∷ ⊩snd)
                                                            )) ⟩
    (Γ ⊩⟨ l ⟩ Σˢ p , q ▷ A ▹ B ×
     ∃ λ u →
     Γ ⊢ t ⇒* u ∷ Σˢ p , q ▷ A ▹ B ×
     Productᵃₗ (Γ .defs) u ×
     Γ ⊢≅ u ∷ Σˢ p , q ▷ A ▹ B ×
     Γ ⊩⟨ l ⟩ fst p u ∷ A ×
     Γ ⊩⟨ l ⟩ snd p u ∷ B [ fst p u ]₀)               □⇔

------------------------------------------------------------------------
-- The projection fst

opaque

  -- Reducibility of equality between applications of fst.

  ⊩fst≡fst :
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊩⟨ l ⟩ fst p t₁ ≡ fst p t₂ ∷ A
  ⊩fst≡fst {t₁} {t₂} {p} t₁≡t₂ =
    case ⊩≡∷Σˢ⇔ .proj₁ t₁≡t₂ of λ
      (_ , u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , _ , _ , _ , fst-u₁≡fst-u₂ , _) →
    fst p t₁  ⇒*⟨ fst-subst* t₁⇒*u₁ ⟩⊩∷
    fst p u₁  ≡⟨ fst-u₁≡fst-u₂ ⟩⊩∷⇐*
    fst p u₂  ⇐*⟨ fst-subst* t₂⇒*u₂ ⟩∎
    fst p t₂  ∎

opaque

  -- Validity of equality preservation for fst.

  fst-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l ⟩ fst p t₁ ≡ fst p t₂ ∷ A
  fst-congᵛ t₁≡t₂ =
    case ⊩ᵛΠΣ→ $ wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁ of λ
      (_ , ⊩A , _) →
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩A
      , λ ξ⊇ → ⊩fst≡fst ∘→ R.⊩≡∷→ ∘→ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t₁≡t₂)
      )

opaque

  -- Validity of fst.

  fstᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l ⟩ fst p t ∷ A
  fstᵛ ⊩t = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $ fst-congᵛ (refl-⊩ᵛ≡∷ ⊩t)

------------------------------------------------------------------------
-- The projection snd

opaque

  -- Reducibility of equality between applications of snd.

  ⊩snd≡snd :
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊩⟨ l ⟩ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]₀
  ⊩snd≡snd {t₁} {t₂} {p} {B} t₁≡t₂ =
    case wf-⊩≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case wf-⊩∷ ⊩t₁ of λ
      ⊩ΣAB →
    case ⊩≡∷Σˢ⇔ .proj₁ t₁≡t₂ of λ
      (_ , u₁ , u₂ , t₁⇒*u₁ , t₂⇒*u₂ , _ , _ , _ , _ , snd-u₁≡snd-u₂) →
    case ⊩∷-⇒* t₁⇒*u₁ ⊩t₁ of λ
      t₁≡u₁ →
    snd p t₁                    ⇒*⟨ snd-subst* t₁⇒*u₁ ⟩⊩∷
    snd p u₁ ∷ B [ fst p t₁ ]₀  ≡⟨ conv-⊩≡∷
                                     (⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩ΣAB) $
                                      sym-⊩≡∷ $ ⊩fst≡fst t₁≡u₁)
                                     snd-u₁≡snd-u₂ ⟩⊩∷∷⇐*
                                 ⟨ ≅-eq $ escape-⊩≡ $
                                   ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩ΣAB) $
                                   ⊩fst≡fst t₁≡t₂ ⟩⇒
    snd p u₂ ∷ B [ fst p t₂ ]₀  ⇐*⟨ snd-subst* t₂⇒*u₂ ⟩∎∷
    snd p t₂                    ∎

opaque

  -- Validity of equality preservation for snd.

  snd-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l ⟩ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]₀
  snd-congᵛ {B} t₁≡t₂ =
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (⊩t₁ , _) →
    case ⊩ᵛΠΣ→ $ wf-⊩ᵛ∷ ⊩t₁ of λ
      (_ , _ , ⊩B) →
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B (fstᵛ ⊩t₁)
      , λ ξ⊇ → PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ singleSubstLift B _) ∘→
               ⊩snd≡snd ∘→ R.⊩≡∷→ ∘→ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ξ⊇ t₁≡t₂)
      )

opaque

  -- Validity of snd.

  sndᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l ⟩ snd p t ∷ B [ fst p t ]₀
  sndᵛ ⊩t =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    snd-congᵛ (refl-⊩ᵛ≡∷ ⊩t)

------------------------------------------------------------------------
-- Equality rules

opaque

  -- Reducibility for Σ-β₁.

  ⊩Σ-β₁ :
    Σˢ-allowed p q →
    Γ »∙ A ⊢ B →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊩⟨ l ⟩ fst p (prodˢ p t u) ≡ t ∷ A
  ⊩Σ-β₁ {p} {B} {t} {u} ok ⊢B ⊩t ⊢u =
    case escape-⊩∷ ⊩t of λ
      ⊢t →
    ⊩∷-⇐*
      (fst p (prodˢ p t u)  ⇒⟨ Σ-β₁ ⊢B ⊢t ⊢u PE.refl ok ⟩
       t                    ∎⟨ ⊢t ⟩⇒)
      ⊩t

opaque

  -- Validity of Σ-β₁.

  Σ-β₁ᵛ :
    Σˢ-allowed p q →
    Γ »∙ A ⊢ B →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ fst p (prodˢ p t u) ≡ t ∷ A
  Σ-β₁ᵛ {B} ok ⊢B ⊩t ⊢u =
    ⊩ᵛ∷-⇐
      (λ ξ⊇ ⊩σ →
         let _ , ⊢σ = escape-⊩ˢ∷ ⊩σ in
         Σ-β₁-⇒ (subst-⊢-⇑ (defn-wk ξ⊇ ⊢B) ⊢σ)
           (R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ξ⊇ ⊩t) ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
            subst-⊢∷-⇑ (defn-wkTerm ξ⊇ ⊢u) ⊢σ)
           ok)
      ⊩t

opaque

  -- Validity of Σ-β₂.

  Σ-β₂ᵛ :
    Σˢ-allowed p q →
    Γ »∙ A ⊢ B →
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊢ u ∷ B [ t ]₀ →
    Γ ⊩ᵛ⟨ l″ ⟩ u ∷ B [ t ]₀ →
    Γ ⊩ᵛ⟨ l″ ⟩ snd p (prodˢ p t u) ≡ u ∷ B [ t ]₀
  Σ-β₂ᵛ {B} ok ⊢B ⊩B ⊩t ⊢u ⊩u =
    ⊩ᵛ∷-⇐
      (λ ξ⊇ ⊩σ →
         let _ , ⊢σ = escape-⊩ˢ∷ ⊩σ in
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift B _) $
         Σ-β₂-⇒ (subst-⊢-⇑ (defn-wk ξ⊇ ⊢B) ⊢σ)
           (R.escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ξ⊇ ⊩t) ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift B _) $
            subst-⊢∷-⇑ (defn-wkTerm ξ⊇ ⊢u) ⊢σ)
           ok)
      ⊩u

opaque

  -- Validity of Σ-η.

  Σ-ηᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t₁ ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t₂ ∷ Σˢ p , q ▷ A ▹ B →
    Γ ⊩ᵛ⟨ l″ ⟩ fst p t₁ ≡ fst p t₂ ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ snd p t₁ ≡ snd p t₂ ∷ B [ fst p t₁ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ Σˢ p , q ▷ A ▹ B
  Σ-ηᵛ {t₁} {p} {B} {t₂} ⊩t₁ ⊩t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂ =
    case wf-⊩ᵛ∷ ⊩t₁ of λ
      ⊩ΣAB →
    case ⊩ᵛΠΣ→ ⊩ΣAB of λ
      (_ , ⊩A , ⊩B) →
    ⊩ᵛ≡∷⇔′ʰ .proj₂
      ( ⊩t₁
      , level-⊩ᵛ∷ ⊩ΣAB ⊩t₂
      , λ {_ _} ξ⊇ {_ _} {σ = σ} ⊩σ →
          case R.⊩→ $ ⊩ᵛ→⊩ˢ∷→⊩[] (defn-wk-⊩ᵛ ξ⊇ ⊩A) ⊩σ of λ
            ⊩A[σ] →
          case refl-⊩ᵛ≡ (defn-wk-⊩ᵛ ξ⊇ ⊩B) of λ
            B≡B →
          case R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ξ⊇ ⊩t₁) ⊩σ of λ
            ⊩t₁[σ] →
          case R.⊩∷→ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (defn-wk-⊩ᵛ∷ ξ⊇ ⊩t₂) ⊩σ of λ
            ⊩t₂[σ] →
          case ⊩∷Σˢ⇔ .proj₁ ⊩t₁[σ] of λ
            (⊩ΣAB[σ] , u₁ , t₁[σ]⇒*u₁ , u₁-prod , _) →
          case ⊩∷Σˢ⇔ .proj₁ ⊩t₂[σ] of λ
            (_ , u₂ , t₂[σ]⇒*u₂ , u₂-prod , _) →
          case ⊩∷-⇒* t₁[σ]⇒*u₁ ⊩t₁[σ] of λ
            t₁[σ]≡u₁ →
          case ⊩∷-⇒* t₂[σ]⇒*u₂ ⊩t₂[σ] of λ
            t₂[σ]≡u₂ →
          case sym-⊩≡∷ $ ⊩fst≡fst t₁[σ]≡u₁ of λ
            fst-u₁≡fst-t₁[σ] →
          case
            fst p u₁        ≡⟨ fst-u₁≡fst-t₁[σ] ⟩⊩∷
            fst p t₁ [ σ ]  ≡⟨ ⊩ᵛ≡∷⇔′ʰ .proj₁ fst-t₁≡fst-t₂ .proj₂ .proj₂ ξ⊇ ⊩σ ⟩⊩∷
            fst p t₂ [ σ ]  ≡⟨ level-⊩≡∷ ⊩A[σ] $ ⊩fst≡fst t₂[σ]≡u₂ ⟩⊩∷∎
            fst p u₂        ∎
          of λ
            fst-u₁≡fst-u₂ →
          case
            snd p u₁       ∷ B [ σ ⇑ ] [ fst p u₁ ]₀        ≡⟨ ⊩snd≡snd $ sym-⊩≡∷ t₁[σ]≡u₁ ⟩⊩∷∷
                                                             ⟨ R.⊩≡→ $
                                                               ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ B≡B (refl-⊩ˢ≡∷ ⊩σ)
                                                                 (R.→⊩≡∷ fst-u₁≡fst-t₁[σ]) ⟩⊩∷
            snd p t₁ [ σ ] ∷ B [ σ ⇑ ] [ fst p t₁ [ σ ] ]₀  ≡⟨ PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B _) $
                                                               ⊩ᵛ≡∷⇔′ʰ .proj₁ snd-t₁≡snd-t₂ .proj₂ .proj₂ ξ⊇ ⊩σ ⟩⊩∷∷
                                                             ⟨ R.⊩≡→ $
                                                               ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ B≡B (refl-⊩ˢ≡∷ ⊩σ) $
                                                               ⊩ᵛ≡∷⇔′ .proj₁ fst-t₁≡fst-t₂ .proj₂ .proj₂ ξ⊇ ⊩σ ⟩⊩∷
            snd p t₂ [ σ ] ∷ B [ σ ⇑ ] [ fst p t₂ [ σ ] ]₀  ≡⟨ ⊩snd≡snd t₂[σ]≡u₂ ⟩⊩∷∎∷
            snd p u₂                                        ∎
          of λ
            snd-u₁≡snd-u₂ →
          ⊩≡∷Σˢ⇔ .proj₂
            ( ⊩ΣAB[σ]
            , u₁ , u₂ , t₁[σ]⇒*u₁ , t₂[σ]⇒*u₂ , u₁-prod , u₂-prod
            , ≅-Σ-η
                (wf-⊢≡∷ (subset*Term t₁[σ]⇒*u₁) .proj₂ .proj₂)
                (wf-⊢≡∷ (subset*Term t₂[σ]⇒*u₂) .proj₂ .proj₂)
                (product↑ _ (Productᵃ→ u₁-prod))
                (product↑ _ (Productᵃ→ u₂-prod))
                (escape-⊩≡∷ fst-u₁≡fst-u₂) (escape-⊩≡∷ snd-u₁≡snd-u₂)
            , fst-u₁≡fst-u₂ , snd-u₁≡snd-u₂
            )
      )

------------------------------------------------------------------------
-- Pairs

opaque

  -- Reducibility of equality between applications of prodˢ.

  ⊩prodˢ≡prodˢ :
    Γ »∙ A ⊢ B →
    Γ ⊩⟨ l ⟩ Σˢ p , q ▷ A ▹ B →
    Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩⟨ l″ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊩⟨ l ⟩ prodˢ p t₁ u₁ ≡ prodˢ p t₂ u₂ ∷ Σˢ p , q ▷ A ▹ B
  ⊩prodˢ≡prodˢ {B} {p} {t₁} {t₂} {u₁} {u₂} ⊢B ⊩ΣAB t₁≡t₂ u₁≡u₂ =
    case ⊩ΠΣ→ ⊩ΣAB of λ
      (ok , ⊩A , _) →
    case wf-⊩≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case wf-⊩≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case conv-⊩∷ (⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩ΣAB) t₁≡t₂) ⊩u₂ of λ
      ⊩u₂ →
    case escape-⊩∷ ⊩t₁ of λ
      ⊢t₁ →
    case escape-⊩∷ ⊩t₂ of λ
      ⊢t₂ →
    case escape-⊩∷ ⊩u₁ of λ
      ⊢u₁ →
    case escape-⊩∷ ⊩u₂ of λ
      ⊢u₂ →
    case prodⱼ ⊢B ⊢t₁ ⊢u₁ ok of λ
      ⊢t₁,u₁ →
    case prodⱼ ⊢B ⊢t₂ ⊢u₂ ok of λ
      ⊢t₂,u₂ →
    case
      fst p (prodˢ p t₁ u₁)  ⇒⟨ Σ-β₁ ⊢B ⊢t₁ ⊢u₁ PE.refl ok ⟩⊩∷
      t₁                     ≡⟨ level-⊩≡∷ ⊩A t₁≡t₂ ⟩⊩∷⇐*
      t₂                     ⇐⟨ Σ-β₁ ⊢B ⊢t₂ ⊢u₂ PE.refl ok ⟩∎
      fst p (prodˢ p t₂ u₂)  ∎
    of λ
      fst≡fst →
    case
                            ∷ B [ fst p (prodˢ p t₁ u₁) ]₀   ⟨ ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩ΣAB) $
                                                               ⊩Σ-β₁ ok ⊢B ⊩t₁ ⊢u₁ ⟩⊩∷∷
      snd p (prodˢ p t₁ u₁) ∷ B [ t₁ ]₀                     ⇒⟨ Σ-β₂ ⊢B ⊢t₁ ⊢u₁ PE.refl ok ⟩⊩∷∷

      u₁                                                    ≡⟨ u₁≡u₂ ⟩⊩∷⇐*
                                                             ⟨ ≅-eq $ escape-⊩≡ $
                                                               ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩ΣAB) t₁≡t₂ ⟩⇒
      u₂                    ∷ B [ t₂ ]₀                     ⇐⟨ Σ-β₂ ⊢B ⊢t₂ ⊢u₂ PE.refl ok ⟩∎∷
      snd p (prodˢ p t₂ u₂)                                 ∎
    of λ
      snd≡snd →
    ⊩≡∷Σˢ⇔ .proj₂
      ( ⊩ΣAB
      , _ , _
      , id ⊢t₁,u₁ , id ⊢t₂,u₂
      , prodₙ , prodₙ
      , ≅-Σ-η ⊢t₁,u₁ ⊢t₂,u₂ prodₙ prodₙ
          (escape-⊩≡∷ fst≡fst) (escape-⊩≡∷ snd≡snd)
      , fst≡fst , snd≡snd
      )

private opaque

  -- Reducibility of equality between applications of prodˢ.

  ⊩prodˢ[]≡prodˢ[] :
    Σˢ-allowed p q →
    ∇ » Δ ∙ A ⊢ B →
    ∇ » Δ ∙ A ⊩ᵛ⟨ l ⟩ B →
    ∇ » Δ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A →
    ∇ » Δ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    ⦃ inc : Var-included or-empty Η ⦄ →
    ∇ » Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    ∇ » Η ⊩⟨ l ⟩ prodˢ p t₁ u₁ [ σ₁ ] ≡ prodˢ p t₂ u₂ [ σ₂ ] ∷
      (Σˢ p , q ▷ A ▹ B) [ σ₁ ]
  ⊩prodˢ[]≡prodˢ[] {B} ok ⊢B ⊩B t₁≡t₂ u₁≡u₂ σ₁≡σ₂ =
    case wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁ of λ
      ⊩A →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , _) →
    ⊩prodˢ≡prodˢ (subst-⊢-⇑ ⊢B (escape-⊩ˢ∷ ⊩σ₁ .proj₂))
      (⊩ΠΣ (ΠΣⱼ ⊢B ok) ⊩A ⊩B ⊩σ₁)
      (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ t₁≡t₂ σ₁≡σ₂)
      (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B _) $
       R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ u₁≡u₂ σ₁≡σ₂)

opaque

  -- Validity of equality preservation for prodˢ.

  prodˢ-congᵛ :
    Σˢ-allowed p q →
    Γ »∙ A ⊢ B →
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ prodˢ p t₁ u₁ ≡ prodˢ p t₂ u₂ ∷ Σˢ p , q ▷ A ▹ B
  prodˢ-congᵛ ok ⊢B ⊩B t₁≡t₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ΠΣᵛ (ΠΣⱼ ⊢B ok) (wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁) ⊩B
      , λ ξ⊇ → ⊩prodˢ[]≡prodˢ[] ok
                                (defn-wk ξ⊇ ⊢B)
                                (defn-wk-⊩ᵛ ξ⊇ ⊩B)
                                (defn-wk-⊩ᵛ≡∷ ξ⊇ t₁≡t₂)
                                (defn-wk-⊩ᵛ≡∷ ξ⊇ u₁≡u₂)
      )

opaque

  -- Validity of prodˢ.

  prodˢᵛ :
    Σˢ-allowed p q →
    Γ »∙ A ⊢ B →
    Γ »∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ B [ t ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ prodˢ p t u ∷ Σˢ p , q ▷ A ▹ B
  prodˢᵛ ok ⊢B ⊩B ⊩t ⊩u =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    prodˢ-congᵛ ok ⊢B ⊩B (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)
