------------------------------------------------------------------------
-- A variant of the logical relation with a hidden reducibility
-- argument, along with variants of some other relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Hidden
  {a} {M : Set a}
  {𝕄 : Modality M}
  {TR : Type-restrictions 𝕄}
  (as : Assumptions TR)
  where

open Assumptions as
open Modality 𝕄 hiding (_≤_; _<_)
open Type-restrictions TR

open import Definition.LogicalRelation TR as L
open import Definition.LogicalRelation.Fundamental.Reducibility TR
open import Definition.LogicalRelation.Hidden TR
import Definition.LogicalRelation.Irrelevance TR as IR
open import Definition.LogicalRelation.Properties TR
open import Definition.LogicalRelation.ShapeView TR
open import Definition.LogicalRelation.Substitution TR
open import Definition.LogicalRelation.Substitution.Introductions TR
import Definition.LogicalRelation.Substitution.Irrelevance TR as IS
open import Definition.LogicalRelation.Substitution.Properties TR
open import Definition.Typed TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Consequences.Syntactic TR
open import Definition.Typed.Properties TR
open import Definition.Typed.RedSteps TR
import Definition.Typed.Weakening TR as W
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Conversion as
open import Graded.Erasure.LogicalRelation.Irrelevance as
open import Graded.Erasure.LogicalRelation.Reduction as
open import Graded.Erasure.LogicalRelation.Subsumption as
open import Graded.Erasure.Target as T using (strict)
import Graded.Erasure.Target.Properties as TP
open import Graded.Mode 𝕄

open import Tools.Bool
open import Tools.Empty
open import Tools.Function
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE using (_≢_)
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

private variable
  n              : Nat
  Γ              : Con Term _
  A B t t′ t₁ t₂ : Term _
  v v′           : T.Term _
  σ              : Subst _ _
  σ′             : T.Subst _ _
  γ δ            : Conₘ _
  p q            : M
  m              : Mode
  s              : Strength
  l l′           : TypeLevel
  ok             : T _

------------------------------------------------------------------------
-- The type formers

opaque

  -- A variant of _®⟨_⟩_∷_/_.

  infix 19 _®⟨_⟩_∷_

  _®⟨_⟩_∷_ : Term k → TypeLevel → T.Term k → Term k → Set a
  t ®⟨ l ⟩ v ∷ A =
    ∃ λ (⊩A : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / ⊩A

opaque

  -- A variant of _®⟨_⟩_∷_◂_/_.

  infix 19 _®⟨_⟩_∷_◂_

  _®⟨_⟩_∷_◂_ : Term k → TypeLevel → T.Term k → Term k → M → Set a
  t ®⟨ l ⟩ v ∷ A ◂ p =
    ∃ (t ®⟨ l ⟩ v ∷ A ◂ p /_)

opaque

  -- A variant of _®_∷[_]_◂_/_/_.

  infix 19 _®_∷[_]_◂_

  _®_∷[_]_◂_ :
    Subst k n → T.Subst k n → Mode → Con Term n → Conₘ n → Set a
  σ ® σ′ ∷[ m ] Γ ◂ γ =
    ∃₂ (σ ® σ′ ∷[ m ] Γ ◂ γ /_/_)

opaque

  -- A variant of _▸_⊩ʳ⟨_⟩_∷[_]_/_/_.

  infix 19 _▸_⊩ʳ⟨_⟩_∷[_]_

  _▸_⊩ʳ⟨_⟩_∷[_]_ :
    Conₘ n → Con Term n → TypeLevel → Term n → Mode → Term n → Set a
  γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A =
    ∃₂ (γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A /_/_)

------------------------------------------------------------------------
-- Some introduction rules

opaque
  unfolding _®⟨_⟩_∷_

  -- An introduction rule.

  hidden-®-intro :
    (⊩A : Δ ⊩⟨ l ⟩ A) →
    t ®⟨ l ⟩ v ∷ A / ⊩A →
    t ®⟨ l ⟩ v ∷ A
  hidden-®-intro = _,_

opaque

  -- A lemma that can sometimes be used to convert the output from the
  -- fundamental lemma.

  hidden-®-intro-fundamental :
    ¬ Trivial →
    (∃₂ λ (⊩Δ : ⊩ᵛ Δ) (⊩A : Δ ⊩ᵛ⟨ l ⟩ A / ⊩Δ) →
     𝟘ᶜ ▸ Δ ⊩ʳ⟨ l ⟩ t ∷[ 𝟙ᵐ ] A / ⊩Δ / ⊩A) →
    t ®⟨ l ⟩ erase str t ∷ A
  hidden-®-intro-fundamental 𝟙≢𝟘 (⊩Δ , ⊩A , ⊩t) =
    case IS.irrelevanceSubst _ _ (soundContext ⊩Δ) ⊢Δ
           (idSubstS ⊩Δ) of λ {
      ⊩σ →
    PE.subst₃ (_®⟨ _ ⟩_∷_) (subst-id _) (TP.subst-id _) (subst-id _) $
    hidden-®-intro (⊩A .unwrap _ ⊩σ .proj₁)
      (⊩t ⊩σ (erasedSubst _ ⊩σ) ◀≢𝟘 𝟙≢𝟘) }

------------------------------------------------------------------------
-- Some characterisation lemmas for _®⟨_⟩_∷_

opaque
  unfolding _®⟨_⟩_∷_ ⊩U⇔

  -- A characterisation lemma for U.

  ®∷U⇔ : t ®⟨ l ⟩ v ∷ U ⇔ ((∃ λ l′ → l′ < l) × t ® v ∷U)
  ®∷U⇔ {t} {l} {v} =
    t ®⟨ l ⟩ v ∷ U                                 ⇔⟨ id⇔ ⟩
    (∃ λ (⊩U : Δ ⊩⟨ l ⟩ U) → t ®⟨ l ⟩ v ∷ U / ⊩U)  ⇔⟨ (λ (⊩U , t®v) →
                                                           ⊩U⇔ .proj₁ ⊩U
                                                         , irrelevanceTerm ⊩U (Uᵣ (extractMaybeEmb (U-elim ⊩U) .proj₂)) t®v)
                                                    , Σ.map (⊩U⇔ .proj₂) idᶠ
                                                    ⟩
    ((∃ λ l′ → l′ < l) × ⊢ Δ) × t ® v ∷U           ⇔⟨ (λ ((<l , _) , t®v) → <l , t®v)
                                                    , (λ (<l , t®v) → (<l , ⊢Δ) , t®v)
                                                    ⟩
    (∃ λ l′ → l′ < l) × t ® v ∷U                   □⇔

opaque
  unfolding _®⟨_⟩_∷_

  -- A characterisation lemma for Empty.

  ®∷Empty⇔ : t ®⟨ l ⟩ v ∷ Empty ⇔ t ® v ∷Empty
  ®∷Empty⇔ =
      (λ (⊩Empty′ , t®v) →
         irrelevanceTerm {l′ = ¹} ⊩Empty′
           (Emptyᵣ (extractMaybeEmb (Empty-elim ⊩Empty′) .proj₂)) t®v)
    , (λ ())

opaque
  unfolding _®⟨_⟩_∷_ ⊩Unit⇔

  -- A characterisation lemma for Unit.

  ®∷Unit⇔ : t ®⟨ l ⟩ v ∷ Unit s ⇔ t ® v ∷Unit⟨ s ⟩
  ®∷Unit⇔ =
      (λ (⊩U , t®v) →
         irrelevanceTerm {l′ = ¹} ⊩U
           (Unitᵣ (extractMaybeEmb (Unit-elim ⊩U) .proj₂)) t®v)
    , (λ t®v →
           ⊩Unit⇔ .proj₂
             ( ⊢Δ
             , (case t®v of λ {
                  (starᵣ t⇒* _) →
                inversion-Unit (syntacticRedTerm t⇒* .proj₁) })
             )
         , t®v)

opaque
  unfolding _®⟨_⟩_∷_ ⊩ℕ⇔

  -- A characterisation lemma for ℕ.

  ®∷ℕ⇔ : t ®⟨ l ⟩ v ∷ ℕ ⇔ t ® v ∷ℕ
  ®∷ℕ⇔ =
      (λ (⊩ℕ′ , t®v) →
         irrelevanceTerm {l′ = ¹} ⊩ℕ′
           (ℕᵣ (extractMaybeEmb (ℕ-elim ⊩ℕ′) .proj₂)) t®v)
    , (⊩ℕ⇔ .proj₂ ⊢Δ ,_)

opaque
  unfolding _®⟨_⟩_∷_ ⊩Id⇔

  -- A characterisation lemma for Id.

  ®∷Id⇔ :
    t ®⟨ l ⟩ v ∷ Id A t₁ t₂ ⇔
    (Δ ⊩⟨ l ⟩ A × t ® v ∷Id⟨ A ⟩⟨ t₁ ⟩⟨ t₂ ⟩)
  ®∷Id⇔ =
      (λ (⊩Id , t®v) →
         case extractMaybeEmb (Id-elim ⊩Id) .proj₂ of λ
           ⊩Id′ →
         case irrelevanceTerm ⊩Id (Idᵣ ⊩Id′) t®v of λ {
           (rflᵣ t⇒* ⇒*↯) →
           wf-⊩∷ (⊩Id⇔ .proj₁ ⊩Id .proj₁)
         , rflᵣ (conv* t⇒* (sym (subset* (red (_⊩ₗId_.⇒*Id ⊩Id′)))))
             ⇒*↯ })
    , (λ (⊩A , t®v) →
           ⊩Id⇔ .proj₂
             (case t®v of λ {
                (rflᵣ t⇒* _) →
              case inversion-Id (syntacticRedTerm t⇒* .proj₁) of λ
                (_ , ⊢t₁ , ⊢t₂) →
                level-⊩∷ ⊩A (reducibleTerm ⊢t₁)
              , level-⊩∷ ⊩A (reducibleTerm ⊢t₂) })
         , t®v)

opaque
  unfolding _®⟨_⟩_∷_ ⊩ΠΣ⇔

  -- A characterisation lemma for Π.

  ®∷Π⇔ :
    t ®⟨ l ⟩ v ∷ Π p , q ▷ A ▹ B ⇔
    (Δ ⊩⟨ l ⟩ Π p , q ▷ A ▹ B ×
     (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
     (∀ t′ → Δ ⊢ t′ ∷ A →
      (p PE.≡ 𝟘 → t ∘⟨ 𝟘 ⟩ t′ ®⟨ l ⟩ app-𝟘 str v ∷ B [ t′ ]₀) ×
      (p ≢ 𝟘 →
       ∀ v′ → t′ ®⟨ l ⟩ v′ ∷ A →
       t ∘⟨ p ⟩ t′ ®⟨ l ⟩ v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀)))
  ®∷Π⇔ {p} {B} =
      (λ (⊩Π , t®v) →
         case extractMaybeEmb′ (B-elim _ ⊩Π) of λ
           (_ , l′≤l , ⊩Π′) →
         case irrelevanceTerm ⊩Π (Bᵣ _ ⊩Π′) t®v of λ
           t®v →
           ⊩Π , t®v .proj₁
         , λ t′ ⊢t′ →
             case B-PE-injectivity (BΠ _ _) (BΠ _ _)
                    (whnfRed* (red (_⊩ₗB⟨_⟩_.D ⊩Π′)) ΠΣₙ) of λ {
               (PE.refl , PE.refl , _) →
             case reducibleTerm $
                  PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-id _) ⊢t′ of λ
               (⊩A , ⊩t′) →
             case IR.irrelevanceTerm ⊩A (_⊩ₗB⟨_⟩_.[F] ⊩Π′ W.id ⊢Δ)
                    ⊩t′ of λ
               ⊩t′ →
             case emb-≤-⊩ l′≤l  $
                  PE.subst (_⊩⟨_⟩_ _ _)
                    (PE.cong _[ _ ]₀ $ wk-lift-id B) $
                  _⊩ₗB⟨_⟩_.[G] ⊩Π′ W.id ⊢Δ ⊩t′ of λ
               ⊩B[t′] →
               (λ { PE.refl →
                    ⊩B[t′]
                  , irrelevanceTerm′ (PE.cong _[ t′ ]₀ $ wk-lift-id B)
                      (_⊩ₗB⟨_⟩_.[G] ⊩Π′ W.id ⊢Δ ⊩t′) ⊩B[t′]
                      (Π-®-𝟘 (is-𝟘? 𝟘) (t®v .proj₂ ⊩t′)) })
             , (λ p≢𝟘 _ t′®v′ →
                    ⊩B[t′]
                  , irrelevanceTerm′ (PE.cong _[ t′ ]₀ $ wk-lift-id B)
                      (_⊩ₗB⟨_⟩_.[G] ⊩Π′ W.id ⊢Δ ⊩t′) ⊩B[t′]
                      (Π-®-ω p≢𝟘 (is-𝟘? p) (t®v .proj₂ ⊩t′)
                         (irrelevanceTerm′ (PE.sym $ wk-id _) (t′®v′ .proj₁)
                            (_⊩ₗB⟨_⟩_.[F] ⊩Π′ W.id ⊢Δ) $
                          t′®v′ .proj₂))) })
    , (λ (⊩Π , v⇒*lam , t®v) →
           ⊩ΠΣ⇔ .proj₂ (⊩ΠΣ⇔ .proj₁ ⊩Π)
         , v⇒*lam
         , λ ⊩t′ → lemma (is-𝟘? p) t®v ⊩t′)
    where
    lemma :
      {⊩A : Δ ⊩⟨ l ⟩ _} {⊩B : Δ ⊩⟨ l ⟩ _}
      (d : Dec (p PE.≡ 𝟘)) →
      (∀ t′ → Δ ⊢ t′ ∷ A →
       (p PE.≡ 𝟘 → t ∘⟨ 𝟘 ⟩ t′ ®⟨ l ⟩ app-𝟘 str v ∷ B [ t′ ]₀) ×
       (p ≢ 𝟘 →
        ∀ v′ → t′ ®⟨ l ⟩ v′ ∷ A →
        t ∘⟨ p ⟩ t′ ®⟨ l ⟩ v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀)) →
      Δ ⊩⟨ l ⟩ t′ ∷ wk id A / ⊩A →
      Π-® l A B t t′ v ⊩A ⊩B p d
    lemma {⊩A} {⊩B} (yes PE.refl) t®v ⊩t′ =
      case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩A of λ
        ⊩A′ →
      case t®v _ (PE.subst (_⊢_∷_ _ _) (wk-id _) $ escape-⊩∷ (⊩A , ⊩t′))
             .proj₁ PE.refl of λ
        (⊩B′ , tt′®v) →
      irrelevanceTerm′ (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id B) ⊩B′ ⊩B
        tt′®v
    lemma {⊩A} {⊩B} (no p≢𝟘) t®v ⊩t′ t′®v′ =
      case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩A of λ
        ⊩A′ →
      case t®v _ (PE.subst (_⊢_∷_ _ _) (wk-id _) $ escape-⊩∷ (⊩A , ⊩t′))
             .proj₂
             p≢𝟘 _ (⊩A′ , irrelevanceTerm′ (wk-id _) ⊩A ⊩A′ t′®v′) of λ
        (⊩B′ , tt′®vv′) →
      irrelevanceTerm′ (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id B) ⊩B′ ⊩B
        tt′®vv′

opaque

  -- A characterisation lemma for non-erased Π.

  ®∷Πω⇔ :
    p ≢ 𝟘 →
    t ®⟨ l ⟩ v ∷ Π p , q ▷ A ▹ B ⇔
    (Δ ⊩⟨ l ⟩ Π p , q ▷ A ▹ B ×
     (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
     (∀ t′ v′ → Δ ⊢ t′ ∷ A → t′ ®⟨ l ⟩ v′ ∷ A →
      t ∘⟨ p ⟩ t′ ®⟨ l ⟩ v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀))
  ®∷Πω⇔ {p} {t} {l} {v} {q} {A} {B} p≢𝟘 =
    t ®⟨ l ⟩ v ∷ Π p , q ▷ A ▹ B                                ⇔⟨ ®∷Π⇔ ⟩

    Δ ⊩⟨ l ⟩ Π p , q ▷ A ▹ B ×
    (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    (∀ t′ → Δ ⊢ t′ ∷ A →
     (p PE.≡ 𝟘 → t ∘⟨ 𝟘 ⟩ t′ ®⟨ l ⟩ app-𝟘 str v ∷ B [ t′ ]₀) ×
     (p ≢ 𝟘 →
      ∀ v′ → t′ ®⟨ l ⟩ v′ ∷ A →
      t ∘⟨ p ⟩ t′ ®⟨ l ⟩ v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀))          ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                                      (λ hyp v′ ⊢t′ → hyp ⊢t′ .proj₂ p≢𝟘 v′)
                                                                    , (λ hyp ⊢t′ → ⊥-elim ∘→ p≢𝟘 , λ _ v′ → hyp v′ ⊢t′)) ⟩
    Δ ⊩⟨ l ⟩ Π p , q ▷ A ▹ B ×
    (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    (∀ t′ v′ → Δ ⊢ t′ ∷ A → t′ ®⟨ l ⟩ v′ ∷ A →
     t ∘⟨ p ⟩ t′ ®⟨ l ⟩ v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀)            □⇔

opaque

  -- A characterisation lemma for erased Π.

  ®∷Π₀⇔ :
    t ®⟨ l ⟩ v ∷ Π 𝟘 , q ▷ A ▹ B ⇔
    (Δ ⊩⟨ l ⟩ Π 𝟘 , q ▷ A ▹ B ×
     (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
     (∀ t′ → Δ ⊢ t′ ∷ A → t ∘⟨ 𝟘 ⟩ t′ ®⟨ l ⟩ app-𝟘 str v ∷ B [ t′ ]₀))
  ®∷Π₀⇔ {t} {l} {v} {q} {A} {B} =
    t ®⟨ l ⟩ v ∷ Π 𝟘 , q ▷ A ▹ B                                      ⇔⟨ ®∷Π⇔ ⟩

    Δ ⊩⟨ l ⟩ Π 𝟘 , q ▷ A ▹ B ×
    (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    (∀ t′ → Δ ⊢ t′ ∷ A →
     (𝟘 PE.≡ 𝟘 → t ∘⟨ 𝟘 ⟩ t′ ®⟨ l ⟩ app-𝟘 str v ∷ B [ t′ ]₀) ×
     (𝟘 ≢ 𝟘 →
      ∀ v′ → t′ ®⟨ l ⟩ v′ ∷ A →
      t ∘⟨ 𝟘 ⟩ t′ ®⟨ l ⟩ v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀))                ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                                            (λ hyp → hyp .proj₁ PE.refl)
                                                                          , (λ hyp → (λ _ → hyp) , ⊥-elim ∘→ (_$ PE.refl))) ⟩
    Δ ⊩⟨ l ⟩ Π 𝟘 , q ▷ A ▹ B ×
    (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    (∀ t′ → Δ ⊢ t′ ∷ A → t ∘⟨ 𝟘 ⟩ t′ ®⟨ l ⟩ app-𝟘 str v ∷ B [ t′ ]₀)  □⇔

opaque
  unfolding _®⟨_⟩_∷_ ⊩ΠΣ⇔

  -- A characterisation lemma for Σ.

  ®∷Σ⇔ :
    t ®⟨ l ⟩ v ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ⇔
    (Δ ⊩⟨ l ⟩ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     ∃₃ λ t₁ t₂ v₂ →
     Δ ⊢ t ⇒* prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     t₂ ®⟨ l ⟩ v₂ ∷ B [ t₁ ]₀ ×
     (p PE.≡ 𝟘 → v T.⇒* v₂) ×
     (p ≢ 𝟘 → ∃ λ v₁ → v T.⇒* T.prod v₁ v₂ × t₁ ®⟨ l ⟩ v₁ ∷ A))
  ®∷Σ⇔ {t} {l} {v} {s} {p} {q} {A} {B} =
      (λ (⊩Σ , t®v) →
         case extractMaybeEmb′ (B-elim _ ⊩Σ) of λ
           (_ , l′≤l , ⊩Σ′) →
         case irrelevanceTerm ⊩Σ (Bᵣ _ ⊩Σ′) t®v of λ
           (t₁ , t₂ , t⇒ , ⊩t₁ , v₂ , t₂®v₂ , rest) →
         case B-PE-injectivity (BΣ _ _ _) (BΣ _ _ _)
                (whnfRed* (red (_⊩ₗB⟨_⟩_.D ⊩Σ′)) ΠΣₙ) of λ {
           (PE.refl , PE.refl , _) →
         let ⊩wk-A     = _⊩ₗB⟨_⟩_.[F] ⊩Σ′ W.id ⊢Δ
             ⊩wk-B[t₁] = _⊩ₗB⟨_⟩_.[G] ⊩Σ′ W.id ⊢Δ ⊩t₁
         in
         case emb-≤-⊩ l′≤l  $
              PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩wk-A of λ
           ⊩A →
         case emb-≤-⊩ l′≤l  $
              PE.subst (_⊩⟨_⟩_ _ _) (PE.cong _[ t₁ ]₀ $ wk-lift-id B)
                ⊩wk-B[t₁] of λ
           ⊩B[t₁] →
         (Δ ⊩⟨ l ⟩ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
          ∃₃ λ t₁ t₂ v₂ →
          Δ ⊢ t ⇒* prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
          t₂ ®⟨ l ⟩ v₂ ∷ B [ t₁ ]₀ ×
          (p PE.≡ 𝟘 → v T.⇒* v₂) ×
          (p ≢ 𝟘 → ∃ λ v₁ → v T.⇒* T.prod v₁ v₂ × t₁ ®⟨ l ⟩ v₁ ∷ A)) ∋
           ⊩Σ , t₁ , t₂ , v₂ , t⇒
         , ( ⊩B[t₁]
           , irrelevanceTerm′ (PE.cong _[ t₁ ]₀ $ wk-lift-id B)
               ⊩wk-B[t₁] ⊩B[t₁] t₂®v₂
           )
         , (λ { PE.refl → Σ-®-𝟘 rest })
         , (λ p≢𝟘 →
              case Σ-®-ω p≢𝟘 rest of λ
                (v₁ , v⇒ , t₁®v₁) →
                v₁ , v⇒
              , (⊩A , irrelevanceTerm′ (wk-id _) ⊩wk-A ⊩A t₁®v₁)) })
    , (λ (⊩Σ , _ , _ , v₂ , t⇒*prod , (⊩B , t₂®v₂) , hyp₁ , hyp₂) →
         case ⊩ΠΣ⇔ .proj₁ ⊩Σ of λ
           ⊩Σ′@(_ , _ , rest) →
         let ⊩wk-A , wk-B≡wk-B = rest W.id ⊢Δ in
         case inversion-prod-Σ $
              syntacticEqTerm (subset*Term t⇒*prod) .proj₂ .proj₂ of λ
           (⊢t₁ , _) →
         case reducible-⊩∷ ⊢t₁ of λ
           (⊩A , ⊩t₁) →
         case IR.irrelevanceTerm′ (PE.sym $ wk-id _) ⊩A ⊩wk-A ⊩t₁ of λ
           ⊩t₁ →
           ⊩ΠΣ⇔ .proj₂ ⊩Σ′ , _ , _ , t⇒*prod , ⊩t₁ , v₂
         , irrelevanceTerm′ (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id B)
             ⊩B (wf-⊩≡ (wk-B≡wk-B (refl-⊩≡∷ (⊩wk-A , ⊩t₁))) .proj₁)
             t₂®v₂
         , (case is-𝟘? p of λ where
              (yes PE.refl) → Σ-®-intro-𝟘 (hyp₁ PE.refl) PE.refl
              (no p≢𝟘)      →
                case hyp₂ p≢𝟘 of λ
                  (v₁ , v⇒*prod , (⊩A′ , t₁®v₁)) →
                Σ-®-intro-ω v₁ v⇒*prod
                  (irrelevanceTerm′ (PE.sym $ wk-id _) ⊩A′ ⊩wk-A t₁®v₁)
                  p≢𝟘))

opaque

  -- A characterisation lemma for non-erased Σ.

  ®∷Σω⇔ :
    p ≢ 𝟘 →
    t ®⟨ l ⟩ v ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ⇔
    (Δ ⊩⟨ l ⟩ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     ∃₄ λ t₁ t₂ v₁ v₂ →
     Δ ⊢ t ⇒* prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     v T.⇒* T.prod v₁ v₂ ×
     t₁ ®⟨ l ⟩ v₁ ∷ A ×
     t₂ ®⟨ l ⟩ v₂ ∷ B [ t₁ ]₀)
  ®∷Σω⇔ {p} {t} {l} {v} {s} {q} {A} {B} p≢𝟘 =
    t ®⟨ l ⟩ v ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B                            ⇔⟨ ®∷Σ⇔ ⟩

    (Δ ⊩⟨ l ⟩ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     ∃₃ λ t₁ t₂ v₂ →
     Δ ⊢ t ⇒* prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     t₂ ®⟨ l ⟩ v₂ ∷ B [ t₁ ]₀ ×
     (p PE.≡ 𝟘 → v T.⇒* v₂) ×
     (p ≢ 𝟘 → ∃ λ v₁ → v T.⇒* T.prod v₁ v₂ × t₁ ®⟨ l ⟩ v₁ ∷ A))  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                       (λ (v₂ , t⇒* , t₂®v₂ , _ , hyp) →
                                                                          case hyp p≢𝟘 of λ
                                                                            (v₁ , v⇒* , t₁®v₁) →
                                                                          v₁ , v₂ , t⇒* , v⇒* , t₁®v₁ , t₂®v₂)
                                                                     , (λ (v₁ , v₂ , t⇒* , v⇒* , t₁®v₁ , t₂®v₂) →
                                                                          v₂ , t⇒* , t₂®v₂ , ⊥-elim ∘→ p≢𝟘 , λ _ → v₁ , v⇒* , t₁®v₁)) ⟩
    (Δ ⊩⟨ l ⟩ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     ∃₄ λ t₁ t₂ v₁ v₂ →
     Δ ⊢ t ⇒* prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     v T.⇒* T.prod v₁ v₂ ×
     t₁ ®⟨ l ⟩ v₁ ∷ A ×
     t₂ ®⟨ l ⟩ v₂ ∷ B [ t₁ ]₀)                                   □⇔

opaque

  -- A characterisation lemma for erased Σ.

  ®∷Σ₀⇔ :
    t ®⟨ l ⟩ v ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ⇔
    (Δ ⊩⟨ l ⟩ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     ∃₃ λ t₁ t₂ v′ →
     Δ ⊢ t ⇒* prod s 𝟘 t₁ t₂ ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     v T.⇒* v′ ×
     t₂ ®⟨ l ⟩ v′ ∷ B [ t₁ ]₀)
  ®∷Σ₀⇔ {t} {l} {v} {s} {q} {A} {B} =
    t ®⟨ l ⟩ v ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B                            ⇔⟨ ®∷Σ⇔ ⟩

    (Δ ⊩⟨ l ⟩ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     ∃₃ λ t₁ t₂ v₂ →
     Δ ⊢ t ⇒* prod s 𝟘 t₁ t₂ ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     t₂ ®⟨ l ⟩ v₂ ∷ B [ t₁ ]₀ ×
     (𝟘 PE.≡ 𝟘 → v T.⇒* v₂) ×
     (𝟘 ≢ 𝟘 → ∃ λ v₁ → v T.⇒* T.prod v₁ v₂ × t₁ ®⟨ l ⟩ v₁ ∷ A))  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                       (λ (t₂®v₂ , hyp , _) → hyp PE.refl , t₂®v₂)
                                                                     , (λ (v⇒* , t₂®v₂) → t₂®v₂ , (λ _ → v⇒*) , ⊥-elim ∘→ (_$ PE.refl))) ⟩
    (Δ ⊩⟨ l ⟩ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     ∃₃ λ t₁ t₂ v′ →
     Δ ⊢ t ⇒* prod s 𝟘 t₁ t₂ ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     v T.⇒* v′ ×
     t₂ ®⟨ l ⟩ v′ ∷ B [ t₁ ]₀)                                   □⇔

------------------------------------------------------------------------
-- Characterisation lemmas for _®⟨_⟩_∷_◂_, _®_∷[_]_◂_ and
-- _▸_⊩ʳ⟨_⟩_∷[_]_

opaque
  unfolding _®⟨_⟩_∷_ _®⟨_⟩_∷_◂_

  -- A characterisation lemma for _®⟨_⟩_∷_◂_.

  ®∷◂⇔ :
    t ®⟨ l ⟩ v ∷ A ◂ p ⇔
    (Δ ⊩⟨ l ⟩ A × (p PE.≡ 𝟘 ⊎ p ≢ 𝟘 × t ®⟨ l ⟩ v ∷ A))
  ®∷◂⇔ {p} with is-𝟘? p
  … | yes p≡𝟘 =
      (λ (⊩A , _) → ⊩A , inj₁ p≡𝟘)
    , (λ (⊩A , _) → ⊩A , _)
  … | no p≢𝟘 =
      (λ t®v@(⊩A , _) → ⊩A , inj₂ (p≢𝟘 , t®v))
    , (λ where
         (_ , inj₁ p≡𝟘)       → ⊥-elim (p≢𝟘 p≡𝟘)
         (_ , inj₂ (_ , t®v)) → t®v)

opaque
  unfolding _®_∷[_]_◂_

  -- A characterisation lemma for _®_∷[_]_◂_.

  ®∷[]ε◂ε⇔ : σ ® σ′ ∷[ m ] ε ◂ ε ⇔ ⊤
  ®∷[]ε◂ε⇔ = _ , λ _ → ε , _ , _

private opaque
  unfolding _®_∷[_]_◂_ _⊩ᵛ⟨_⟩_ _⊩⟨_⟩_∷_ _®⟨_⟩_∷_◂_

  -- A lemma used below.

  ®∷[]∙◂∙←′ :
    (∃₃ λ l₁ l₂ l₃ →
     (Γ ⊩ᵛ⟨ l₁ ⟩ A) ×
     Δ ⊩⟨ l₂ ⟩ head σ ∷ A [ tail σ ] ×
     head σ ®⟨ l₃ ⟩ T.head σ′ ∷ A [ tail σ ] ◂ ⌜ m ⌝ · p) ×
    tail σ ® T.tail σ′ ∷[ m ] Γ ◂ γ →
    σ ® σ′ ∷[ m ] Γ ∙ A ◂ γ ∙ p
  ®∷[]∙◂∙←′
    ( ( _ , _ , _ , (⊩Γ , ⊩A) , (⊩A[tail] , ⊩head)
      , (⊩A[tail]′ , head®head)
      )
    , (⊩Γ′ , ⊩tail , tail®tail)
    ) =
    case IS.irrelevance _ _ ⊩A of λ
      ⊩A′ →
    let ⊩A[tail]″ , _ = ⊩A′ .unwrap _ _ in
      _ ∙ ⊩A′
    , (⊩tail , IR.irrelevanceTerm ⊩A[tail] ⊩A[tail]″ ⊩head)
    , tail®tail , irrelevanceQuant _ ⊩A[tail]′ ⊩A[tail]″ head®head

opaque
  unfolding _®_∷[_]_◂_ _⊩ᵛ⟨_⟩_ _⊩⟨_⟩_∷_ _®⟨_⟩_∷_◂_

  -- Another characterisation lemma for _®_∷[_]_◂_.

  ®∷[]∙◂∙⇔ :
    σ ® σ′ ∷[ m ] Γ ∙ A ◂ γ ∙ p ⇔
    ((∃ λ l →
      (Γ ⊩ᵛ⟨ l ⟩ A) ×
      Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ] ×
      head σ ®⟨ l ⟩ T.head σ′ ∷ A [ tail σ ] ◂ ⌜ m ⌝ · p) ×
     tail σ ® T.tail σ′ ∷[ m ] Γ ◂ γ)
  ®∷[]∙◂∙⇔ =
      (λ where
           (_ ∙ ⊩A , (_ , ⊩head) , tail®tail , head®head) →
               ( _ , (_ , ⊩A) , (⊩A .unwrap _ _ .proj₁ , ⊩head)
               , (_ , head®head)
               )
             , (_ , _ , tail®tail))
    , ®∷[]∙◂∙←′ ∘→
      (λ ((l , rest₁) , rest₂) → (l , l , l , rest₁) , rest₂)

opaque

  -- A variant of ®∷[]∙◂∙⇔.

  ®∷[]∙◂∙⇔′ :
    σ ® σ′ ∷[ m ] Γ ∙ A ◂ γ ∙ p ⇔
    ((∃₃ λ l₁ l₂ l₃ →
      (Γ ⊩ᵛ⟨ l₁ ⟩ A) ×
      Δ ⊩⟨ l₂ ⟩ head σ ∷ A [ tail σ ] ×
      head σ ®⟨ l₃ ⟩ T.head σ′ ∷ A [ tail σ ] ◂ ⌜ m ⌝ · p) ×
     tail σ ® T.tail σ′ ∷[ m ] Γ ◂ γ)
  ®∷[]∙◂∙⇔′ =
      (λ ((l , rest₁) , rest₂) → (l , l , l , rest₁) , rest₂) ∘→
      ®∷[]∙◂∙⇔ .proj₁
    , ®∷[]∙◂∙←′

opaque

  -- One direction of a potential characterisation lemma for
  -- _®_∷[_]_◂_.

  ®∷[]◂→ :
    σ ® σ′ ∷[ m ] Γ ◂ γ →
    ∀ {A x} → x ∷ A ∈ Γ →
    ∃ λ l →
    (Γ ⊩ᵛ⟨ l ⟩ A) ×
    Δ ⊩⟨ l ⟩ var x [ σ ] ∷ A [ σ ] ×
    var x [ σ ] ®⟨ l ⟩ T.var x T.[ σ′ ] ∷ A [ σ ] ◂ ⌜ m ⌝ · γ ⟨ x ⟩
  ®∷[]◂→ {γ = _ ∙ _} σ®σ′ (here {A}) =
    case ®∷[]∙◂∙⇔ .proj₁ σ®σ′ of λ
      ((l , ⊩A , ⊩σ₀ , σ₀®σ′₀) , _) →
      l
    , wk1-⊩ᵛ ⊩A ⊩A
    , PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk1-tail A) ⊩σ₀
    , PE.subst₂ (_®⟨_⟩_∷_◂_ _ _ _) (PE.sym $ wk1-tail A) PE.refl σ₀®σ′₀
  ®∷[]◂→ {γ = _ ∙ _} σ®σ′ (there {A} x∈Γ) =
    case ®∷[]∙◂∙⇔ .proj₁ σ®σ′ of λ
      ((_ , ⊩B , _) , σ₊®σ′₊) →
    case ®∷[]◂→ σ₊®σ′₊ x∈Γ of λ
      (l , ⊩A , ⊩x[σ₊] , x[σ₊]®x[σ′₊]) →
      l
    , wk1-⊩ᵛ ⊩B ⊩A
    , PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk1-tail A) ⊩x[σ₊]
    , PE.subst₂ (_®⟨_⟩_∷_◂_ _ _ _) (PE.sym $ wk1-tail A) PE.refl
        x[σ₊]®x[σ′₊]

-- The other direction holds if a form of strengthening can be
-- proved.

module _
  (strengthen-⊩ᵛ :
     ∀ {n} {Γ : Con Term n} {A B l} →
     Γ ∙ A ⊩ᵛ⟨ l ⟩ wk1 B → Γ ⊩ᵛ⟨ l ⟩ B)
  where opaque

  ®∷[]◂← :
    (∀ {A x} → x ∷ A ∈ Γ →
     ∃ λ l →
     (Γ ⊩ᵛ⟨ l ⟩ A) ×
     Δ ⊩⟨ l ⟩ var x [ σ ] ∷ A [ σ ] ×
     var x [ σ ] ®⟨ l ⟩ T.var x T.[ σ′ ] ∷ A [ σ ] ◂
       ⌜ m ⌝ · γ ⟨ x ⟩) →
    σ ® σ′ ∷[ m ] Γ ◂ γ
  ®∷[]◂← {Γ = ε} {γ = ε} _ =
    ®∷[]ε◂ε⇔ .proj₂ _
  ®∷[]◂← {Γ = Γ ∙ A} {σ} {σ′} {γ = γ ∙ p} hyp =
    case hyp here of λ
      (l , ⊩wk1-A , ⊩σ₀ , σ₀®σ′₀) →
    ®∷[]∙◂∙⇔ .proj₂
      ( ( l , strengthen-⊩ᵛ ⊩wk1-A
        , PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk1-tail A) ⊩σ₀
        , PE.subst₂ (_®⟨_⟩_∷_◂_ _ _ _) (wk1-tail A) PE.refl σ₀®σ′₀
        )
      , (®∷[]◂← λ {A = A} x∈Γ →
         case hyp (there x∈Γ) of λ
           (l , ⊩wk1-A , ⊩x+1[σ] , x+1[σ]®x+1[σ′]) →
           l , strengthen-⊩ᵛ ⊩wk1-A
         , PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk1-tail A) ⊩x+1[σ]
         , PE.subst₂ (_®⟨_⟩_∷_◂_ _ _ _) (wk1-tail A) PE.refl
             x+1[σ]®x+1[σ′])
      )

opaque
  unfolding _▸_⊩ʳ⟨_⟩_∷[_]_ _⊩ᵛ⟨_⟩_ _⊩ˢ_∷_ _®_∷[_]_◂_ _®⟨_⟩_∷_◂_

  -- A characterisation lemma for _▸_⊩ʳ⟨_⟩_∷[_]_.

  ▸⊩ʳ∷⇔ :
    γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A ⇔
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {σ σ′} → Δ ⊩ˢ σ ∷ Γ → σ ® σ′ ∷[ m ] Γ ◂ γ →
      t [ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ] ∷ A [ σ ] ◂ ⌜ m ⌝))
  ▸⊩ʳ∷⇔ =
      (λ (_ , ⊩A , ⊩t) →
           (_ , ⊩A)
         , (λ (_ , _ , ⊩σ) (_ , _ , σ®σ′) →
                _
              , ⊩t (IS.irrelevanceSubst _ _ _ _ ⊩σ)
                  (irrelevanceSubst _ _ _ _ σ®σ′)))
    , (λ ((_ , ⊩A) , hyp) →
           _ , ⊩A
         , λ ⊩σ σ®σ′ →
             case hyp (_ , _ , ⊩σ) (_ , _ , σ®σ′) of λ
               (_ , t[σ]®erase-t[σ′]) →
             irrelevanceQuant _ _ _ t[σ]®erase-t[σ′])

------------------------------------------------------------------------
-- Some subsumption lemmas

opaque
  unfolding _®⟨_⟩_∷_◂_

  -- Subsumption for _®⟨_⟩_∷_◂_.

  subsumption-®∷◂ :
    (p PE.≡ 𝟘 → q PE.≡ 𝟘) →
    t ®⟨ l ⟩ v ∷ A ◂ p →
    t ®⟨ l ⟩ v ∷ A ◂ q
  subsumption-®∷◂ hyp =
    Σ.map idᶠ (flip subsumptionTerm hyp)

opaque
  unfolding _®_∷[_]_◂_

  -- Subsumption for _®_∷[_]_◂_.

  subsumption-®∷[]◂ :
    (∀ x → γ ⟨ x ⟩ PE.≡ 𝟘 → δ ⟨ x ⟩ PE.≡ 𝟘) →
    σ ® σ′ ∷[ m ] Γ ◂ γ →
    σ ® σ′ ∷[ m ] Γ ◂ δ
  subsumption-®∷[]◂ hyp =
    Σ.map idᶠ (Σ.map idᶠ (flip subsumptionSubst hyp))

opaque
  unfolding _▸_⊩ʳ⟨_⟩_∷[_]_

  -- Subsumption for _▸_⊩ʳ⟨_⟩_∷[_]_.

  subsumption-▸⊩ʳ∷[] :
    (∀ x → δ ⟨ x ⟩ PE.≡ 𝟘 → γ ⟨ x ⟩ PE.≡ 𝟘) →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A →
    δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A
  subsumption-▸⊩ʳ∷[] {t} hyp (_ , ⊩A , ⊩ʳt) =
    _ , ⊩A , subsumption {t = t} _ ⊩A ⊩ʳt hyp

opaque
  unfolding _▸_⊩ʳ⟨_⟩_∷[_]_

  -- Another kind of subsumption for _▸_⊩ʳ⟨_⟩_∷[_]_.

  subsumption-▸⊩ʳ∷[]-≤ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
    δ ≤ᶜ γ →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A →
    δ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A
  subsumption-▸⊩ʳ∷[]-≤ {t} δ≤γ (_ , ⊩A , ⊩ʳt) =
    _ , ⊩A , subsumption-≤ t ⊩A ⊩ʳt δ≤γ

------------------------------------------------------------------------
-- Other lemmas

opaque
  unfolding _®⟨_⟩_∷_

  -- Changing type levels for _®⟨_⟩_∷_.

  level-®∷ :
    Δ ⊩⟨ l ⟩ A →
    t ®⟨ l′ ⟩ v ∷ A →
    t ®⟨ l ⟩ v ∷ A
  level-®∷ ⊩A (⊩A′ , t®v) =
    ⊩A , irrelevanceTerm ⊩A′ ⊩A t®v

opaque
  unfolding _®⟨_⟩_∷_◂_

  -- Embedding for _®⟨_⟩_∷_◂_.

  emb-®∷◂ :
    l ≤ l′ →
    t ®⟨ l ⟩ v ∷ A ◂ p →
    t ®⟨ l′ ⟩ v ∷ A ◂ p
  emb-®∷◂ l≤l′ (⊩A , t®v) =
    emb-≤-⊩ l≤l′ ⊩A , irrelevanceQuant _ _ _ t®v

opaque
  unfolding _®⟨_⟩_∷_ _®⟨_⟩_∷_◂_

  -- If t ®⟨ l ⟩ v ∷ A holds, then t ®⟨ l ⟩ v ∷ A ◂ p holds for any p.

  ®∷→®∷◂ :
    t ®⟨ l ⟩ v ∷ A →
    t ®⟨ l ⟩ v ∷ A ◂ p
  ®∷→®∷◂ = Σ.map idᶠ (_◀ _)

opaque
  unfolding _®⟨_⟩_∷_ _®⟨_⟩_∷_◂_

  -- If t ®⟨ l ⟩ v ∷ A ◂ p holds for some non-zero p, then
  -- t ®⟨ l ⟩ v ∷ A holds.

  ®∷→®∷◂ω :
    p ≢ 𝟘 →
    t ®⟨ l ⟩ v ∷ A ◂ p →
    t ®⟨ l ⟩ v ∷ A
  ®∷→®∷◂ω p≢𝟘 = Σ.map idᶠ (_◀≢𝟘 p≢𝟘)

opaque

  -- If p is zero and Δ ⊩⟨ l ⟩ A holds, then t ®⟨ l ⟩ v ∷ A ◂ p holds.

  ®∷◂𝟘 : p PE.≡ 𝟘 → Δ ⊩⟨ l ⟩ A → t ®⟨ l ⟩ v ∷ A ◂ p
  ®∷◂𝟘 p≡𝟘 ⊩A = ®∷◂⇔ .proj₂ (⊩A , inj₁ p≡𝟘)

opaque

  -- If Γ ⊩ᵛ⟨ l ⟩ A is inhabited, then γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ 𝟘ᵐ[ ok ] ] A
  -- holds.

  ▸⊩ʳ∷[𝟘ᵐ] : Γ ⊩ᵛ⟨ l ⟩ A → γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ 𝟘ᵐ[ ok ] ] A
  ▸⊩ʳ∷[𝟘ᵐ] ⊩A =
    ▸⊩ʳ∷⇔ .proj₂
      ( ⊩A
      , λ ⊩σ _ → ®∷◂𝟘 PE.refl (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ)
      )

opaque
  unfolding _®⟨_⟩_∷_

  -- Conversion for _®⟨_⟩_∷_.

  conv-®∷ :
    Δ ⊩⟨ l ⟩ A ≡ B →
    t ®⟨ l ⟩ v ∷ A →
    t ®⟨ l ⟩ v ∷ B
  conv-®∷ A≡B (⊩A , t®v) =
    case wf-⊩≡ A≡B of λ
      (_ , ⊩B) →
    ⊩B , convTermʳ ⊩A ⊩B (≅-eq (escape-⊩≡ A≡B)) t®v

opaque
  unfolding _®⟨_⟩_∷_◂_

  -- Conversion for _®⟨_⟩_∷_◂_.

  conv-®∷◂ :
    Δ ⊩⟨ l ⟩ A ≡ B →
    t ®⟨ l′ ⟩ v ∷ A ◂ p →
    t ®⟨ l ⟩ v ∷ B ◂ p
  conv-®∷◂ A≡B (⊩A , t®v) =
    case wf-⊩≡ A≡B of λ
      (_ , ⊩B) →
    ⊩B , convTermQuantʳ _ _ _ (≅-eq (escape-⊩≡ A≡B)) t®v

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_ _▸_⊩ʳ⟨_⟩_∷[_]_

  -- Conversion for _▸_⊩ʳ⟨_⟩_∷[_]_.

  conv-▸⊩ʳ∷ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    γ ▸ Γ ⊩ʳ⟨ l′ ⟩ t ∷[ m ] A →
    γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] B
  conv-▸⊩ʳ∷ {t} A≡B@(_ , ⊩A , ⊩B , _) (_ , ⊩A′ , ⊩ʳt) =
      _ , ⊩B
    , convʳ {t = t} _ ⊩A ⊩B (≅-eq (escape-⊩ᵛ≡ A≡B))
        (irrelevance {t = t} _ _ ⊩A′ ⊩A ⊩ʳt)

opaque
  unfolding _®⟨_⟩_∷_

  -- Closure under reduction of the target language term for _®⟨_⟩_∷_.

  ®∷-⇒* :
    v T.⇒* v′ →
    t ®⟨ l ⟩ v ∷ A →
    t ®⟨ l ⟩ v′ ∷ A
  ®∷-⇒* v⇒v′ (⊩A , t®v) =
    ⊩A , targetRedSubstTerm*′ ⊩A t®v v⇒v′

opaque
  unfolding _®⟨_⟩_∷_

  -- Closure under expansion for _®⟨_⟩_∷_.

  ®∷-⇐* :
    Δ ⊢ t ⇒* t′ ∷ A →
    v T.⇒* v′ →
    t′ ®⟨ l ⟩ v′ ∷ A →
    t ®⟨ l ⟩ v ∷ A
  ®∷-⇐* t⇒t′ v⇒v′ (⊩A , t′®v′) =
    ⊩A , redSubstTerm* ⊩A t′®v′ t⇒t′ v⇒v′

opaque
  unfolding _®⟨_⟩_∷_◂_

  -- Closure under expansion for _®⟨_⟩_∷_◂_.

  ®∷◂-⇐* :
    Δ ⊢ t ⇒* t′ ∷ A →
    v T.⇒* v′ →
    t′ ®⟨ l ⟩ v′ ∷ A ◂ p →
    t ®⟨ l ⟩ v ∷ A ◂ p
  ®∷◂-⇐* t⇒t′ v⇒v′ (_ , t′®v′) =
    _ , redSubstTerm*-◂ t′®v′ t⇒t′ v⇒v′
