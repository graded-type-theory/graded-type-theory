------------------------------------------------------------------------
-- A variant of the logical relation with a hidden reducibility
-- argument
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
open import Definition.LogicalRelation.Fundamental TR
open import Definition.LogicalRelation.Fundamental.Reducibility TR
open import Definition.LogicalRelation.Hidden TR
import Definition.LogicalRelation.Irrelevance TR as IR
open import Definition.LogicalRelation.ShapeView TR
open import Definition.LogicalRelation.Substitution TR
open import Definition.LogicalRelation.Substitution.Introductions TR
open import Definition.LogicalRelation.Weakening.Restricted TR
open import Definition.Typed TR
open import Definition.Typed.Consequences.Inversion TR
open import Definition.Typed.Inversion TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Well-formed TR
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.LogicalRelation as
open import Graded.Erasure.LogicalRelation.Conversion as
open import Graded.Erasure.LogicalRelation.Irrelevance as
open import Graded.Erasure.LogicalRelation.Reduction as
open import Graded.Erasure.Target as T using (strict)
import Graded.Erasure.Target.Properties as TP
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level using (Lift)
open import Tools.Nat using (Nat)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE using (_≢_)
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Unit

private variable
  n                : Nat
  Γ                : Con Term _
  A B t t′ t₁ t₂ u : Term _
  v v′             : T.Term _
  σ                : Subst _ _
  σ′               : T.Subst _ _
  γ δ              : Conₘ _
  p q              : M
  m                : Mode
  s                : Strength
  l l′             : Universe-level
  ok               : T _

------------------------------------------------------------------------
-- The type former

opaque

  -- A variant of _®⟨_⟩_∷_/_.

  infix 19 _®_∷_

  _®_∷_ : Term k → T.Term k → Term k → Set a
  t ® v ∷ A =
    ∃₂ λ l (⊩A : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / ⊩A

------------------------------------------------------------------------
-- Some characterisation lemmas for _®_∷_

opaque
  unfolding _®_∷_

  -- A characterisation lemma for Level.

  ®∷Level⇔ :
    t ® v ∷ Level ⇔ t ® v ∷U/Level
  ®∷Level⇔ {t} {v} =
    t ® v ∷ Level                                             ⇔⟨ id⇔ ⟩
    (∃₂ λ l (⊩L : Δ ⊩⟨ l ⟩ Level) → t ®⟨ l ⟩ v ∷ Level / ⊩L)  ⇔⟨ (λ (l , ⊩L , t®v) →
                                                                    irrelevanceTerm {l′ = 0ᵘ+ 0} ⊩L (Levelᵣ (Level-elim ⊩L)) t®v)
                                                               , (λ t®v →
                                                                    let ⊩L = ⊩Level⇔ .proj₂ ⊢Δ in
                                                                    0ᵘ+ 0 , ⊩L , irrelevanceTerm {l = 0ᵘ+ 0} (Levelᵣ (Level-elim ⊩L)) ⊩L t®v)
                                                               ⟩
    t ® v ∷U/Level                                            □⇔

opaque
  unfolding _®_∷_

  -- A characterisation lemma for U.

  ®∷U⇔ :
    t ® v ∷ U u ⇔
    (Δ ⊢ u ∷ Level × t ® v ∷U/Level)
  ®∷U⇔ {t} {v} {u} =
    t ® v ∷ U u                                           ⇔⟨ id⇔ ⟩
    (∃₂ λ l (⊩U : Δ ⊩⟨ l ⟩ U u) → t ®⟨ l ⟩ v ∷ U u / ⊩U)  ⇔⟨ (λ (_ , ⊩U , t®v) → (_ , ⊩U) , irrelevanceTerm ⊩U (Uᵣ (U-elim ⊩U)) t®v)
                                                           , (λ ((_ , ⊩U) , t®v) → _ , ⊩U , irrelevanceTerm (Uᵣ (U-elim ⊩U)) ⊩U t®v)
                                                           ⟩
    (∃ λ l → Δ ⊩⟨ l ⟩ U u) × t ® v ∷U/Level               ⇔⟨ (escape-⊩ ∘→ proj₂ , reducible-⊩) ×-cong-⇔ id⇔ ⟩
    (Δ ⊢ U u) × t ® v ∷U/Level                            ⇔⟨ (inversion-U-Level , Uⱼ) ×-cong-⇔ id⇔ ⟩
    Δ ⊢ u ∷ Level × t ® v ∷U/Level                        □⇔

opaque
  unfolding _®_∷_

  -- A characterisation lemma for Empty.

  ®∷Empty⇔ : t ® v ∷ Empty ⇔ t ® v ∷Empty
  ®∷Empty⇔ =
      (λ (_ , ⊩Empty′ , t®v) →
         irrelevanceTerm {l′ = 0ᵘ+ 0} ⊩Empty′
           (Emptyᵣ (Empty-elim ⊩Empty′)) t®v)
    , (λ ())

opaque
  unfolding _®_∷_ ⊩Unit⇔ whrDet*

  -- A characterisation lemma for Unit.

  ®∷Unit⇔ :
    t ® v ∷ Unit s u ⇔
    (Δ ⊢ u ∷ Level × t ® v ∷Unit⟨ s , u ⟩)
  ®∷Unit⇔ {u} =
      (λ (l , ⊩U , t®v) →
         inversion-Unit (escape-⊩ ⊩U) .proj₁ ,
         irrelevanceTerm ⊩U
           (Unitᵣ (Unit-elim (⊩Unit⇔ .proj₂ (⊩Unit⇔ .proj₁ ⊩U)))) t®v)
    , (λ (⊢u , t®v) →
         let ok =
               case t®v of λ {
                 (starᵣ t⇛ _ _) →
               inversion-Unit (wf-⊢∷ (wf-⇛ t⇛ .proj₁)) .proj₂ }
             l , ⊩Unit = reducible-⊩ (Unitⱼ ⊢u ok)
          in
         l , ⊩Unit⇔ .proj₂ (⊩Unit⇔ .proj₁ ⊩Unit) , t®v)

opaque
  unfolding _®_∷_ ⊩ℕ⇔

  -- A characterisation lemma for ℕ.

  ®∷ℕ⇔ : t ® v ∷ ℕ ⇔ t ® v ∷ℕ
  ®∷ℕ⇔ =
      (λ (_ , ⊩ℕ′ , t®v) →
         irrelevanceTerm {l′ = 0ᵘ+ 0} ⊩ℕ′
           (ℕᵣ (ℕ-elim ⊩ℕ′)) t®v)
    , (λ t®v → 0ᵘ+ 0 , ⊩ℕ⇔ .proj₂ ⊢Δ , t®v)

opaque
  unfolding _®_∷_ ⊩Id⇔

  -- A characterisation lemma for Id.

  ®∷Id⇔ :
    t ® v ∷ Id A t₁ t₂ ⇔
    (Δ ⊢ A × t ® v ∷Id⟨ A ⟩⟨ t₁ ⟩⟨ t₂ ⟩)
  ®∷Id⇔ =
      (λ (_ , ⊩Id , t®v) →
         case Id-elim ⊩Id of λ
           ⊩Id′ →
         case irrelevanceTerm ⊩Id (Idᵣ ⊩Id′) t®v of λ {
           (rflᵣ t⇒* ⇒*↯) →
           escape-⊩ (wf-⊩∷ $ ⊩Id⇔ .proj₁ ⊩Id .proj₁)
         , rflᵣ (conv-⇛ t⇒* (sym (subset* (_⊩ₗId_.⇒*Id ⊩Id′))))
             ⇒*↯ })
    , (λ (⊢A , t®v) →
         case reducible-⊩ ⊢A of λ
           (l , ⊩A) →
           l
         , ⊩Id⇔ .proj₂
             (case t®v of λ {
                (rflᵣ t⇒* _) →
              case inversion-Id (wf-⊢∷ (wf-⇛ t⇒* .proj₁)) of λ
                (_ , ⊢t₁ , ⊢t₂) →
                level-⊩∷ ⊩A (reducible-⊩∷ ⊢t₁ .proj₂)
              , level-⊩∷ ⊩A (reducible-⊩∷ ⊢t₂ .proj₂) })
         , t®v)

opaque
  unfolding _®_∷_ ⊩ΠΣ⇔

  -- A characterisation lemma for Π.

  ®∷Π⇔ :
    t ® v ∷ Π p , q ▷ A ▹ B ⇔
    (Δ ⊢ Π p , q ▷ A ▹ B ×
     (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
     (∀ t′ → Δ ⊢ t′ ∷ A →
      (p PE.≡ 𝟘 → t ∘⟨ 𝟘 ⟩ t′ ® app-𝟘 str v ∷ B [ t′ ]₀) ×
      (p ≢ 𝟘 →
       ∀ v′ → t′ ® v′ ∷ A →
       t ∘⟨ p ⟩ t′ ® v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀)))
  ®∷Π⇔ {p} {B} =
      (λ (_ , ⊩Π , t®v) →
         case B-elim ⊩Π of λ {
           ⊩Π′@record{} →
         case irrelevanceTerm ⊩Π (Bᵣ _ ⊩Π′) t®v of λ
           t®v →
           escape-⊩ ⊩Π , t®v .proj₁
         , λ t′ ⊢t′ →
             case B-PE-injectivity (BΠ _ _) (BΠ _ _)
                    (whnfRed* (_⊩ₗB⟨_⟩_.D ⊩Π′) ΠΣₙ) of λ {
               (PE.refl , PE.refl , _) →
             case reducible-⊩∷ $
                  PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-id _) ⊢t′ of λ
               (_ , ⊩A , ⊩t′) →
             case IR.irrelevanceTerm ⊩A (_⊩ₗB⟨_⟩_.[F] ⊩Π′ (id ⊢Δ))
                    ⊩t′ of λ
               ⊩t′ →
             case PE.subst (_⊩⟨_⟩_ _ _)
                    (PE.cong _[ _ ]₀ $ wk-lift-id B) $
                  _⊩ₗB⟨_⟩_.[G] ⊩Π′ (id ⊢Δ) ⊩t′ of λ
               ⊩B[t′] →
               (λ { PE.refl →
                    _ , ⊩B[t′]
                  , irrelevanceTerm′ (PE.cong _[ t′ ]₀ $ wk-lift-id B)
                      (_⊩ₗB⟨_⟩_.[G] ⊩Π′ (id ⊢Δ) ⊩t′) ⊩B[t′]
                      (Π-®-𝟘 (is-𝟘? 𝟘) (t®v .proj₂ ⊩t′)) })
             , (λ p≢𝟘 _ t′®v′ →
                    _ , ⊩B[t′]
                  , irrelevanceTerm′ (PE.cong _[ t′ ]₀ $ wk-lift-id B)
                      (_⊩ₗB⟨_⟩_.[G] ⊩Π′ (id ⊢Δ) ⊩t′) ⊩B[t′]
                      (Π-®-ω p≢𝟘 (is-𝟘? p) (t®v .proj₂ ⊩t′)
                         (irrelevanceTerm′ (PE.sym $ wk-id _)
                            (t′®v′ .proj₂ .proj₁)
                            (_⊩ₗB⟨_⟩_.[F] ⊩Π′ (id ⊢Δ)) $
                          t′®v′ .proj₂ .proj₂))) }})
    , (λ (⊢Π , v⇒*lam , t®v) →
           _
         , ⊩ΠΣ⇔ .proj₂ (⊩ΠΣ⇔ .proj₁ (reducible-⊩ ⊢Π .proj₂))
         , v⇒*lam
         , λ ⊩t′ → lemma (is-𝟘? p) t®v ⊩t′)
    where
    lemma :
      {⊩A : Δ ⊩⟨ l ⟩ _} {⊩B : Δ ⊩⟨ l ⟩ _}
      (d : Dec (p PE.≡ 𝟘)) →
      (∀ t′ → Δ ⊢ t′ ∷ A →
       (p PE.≡ 𝟘 → t ∘⟨ 𝟘 ⟩ t′ ® app-𝟘 str v ∷ B [ t′ ]₀) ×
       (p ≢ 𝟘 →
        ∀ v′ → t′ ® v′ ∷ A →
        t ∘⟨ p ⟩ t′ ® v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀)) →
      Δ ⊩⟨ l ⟩ t′ ∷ wk id A / ⊩A →
      Π-® l A B t t′ v ⊩A ⊩B p d
    lemma {⊩A} {⊩B} (yes PE.refl) t®v ⊩t′ =
      case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩A of λ
        ⊩A′ →
      case t®v _ (PE.subst (_⊢_∷_ _ _) (wk-id _) $ escape-⊩∷ (⊩A , ⊩t′))
             .proj₁ PE.refl of λ
        (_ , ⊩B′ , tt′®v) →
      irrelevanceTerm′ (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id B) ⊩B′ ⊩B
        tt′®v
    lemma {⊩A} {⊩B} (no p≢𝟘) t®v ⊩t′ t′®v′ =
      case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩A of λ
        ⊩A′ →
      case t®v _ (PE.subst (_⊢_∷_ _ _) (wk-id _) $ escape-⊩∷ (⊩A , ⊩t′))
             .proj₂
             p≢𝟘 _
             (_ , ⊩A′ , irrelevanceTerm′ (wk-id _) ⊩A ⊩A′ t′®v′) of λ
        (_ , ⊩B′ , tt′®vv′) →
      irrelevanceTerm′ (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id B) ⊩B′ ⊩B
        tt′®vv′

opaque

  -- A characterisation lemma for non-erased Π.

  ®∷Πω⇔ :
    p ≢ 𝟘 →
    t ® v ∷ Π p , q ▷ A ▹ B ⇔
    (Δ ⊢ Π p , q ▷ A ▹ B ×
     (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
     (∀ t′ v′ → Δ ⊢ t′ ∷ A → t′ ® v′ ∷ A →
      t ∘⟨ p ⟩ t′ ® v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀))
  ®∷Πω⇔ {p} {t} {v} {q} {A} {B} p≢𝟘 =
    t ® v ∷ Π p , q ▷ A ▹ B                                ⇔⟨ ®∷Π⇔ ⟩

    Δ ⊢ Π p , q ▷ A ▹ B ×
    (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    (∀ t′ → Δ ⊢ t′ ∷ A →
     (p PE.≡ 𝟘 → t ∘⟨ 𝟘 ⟩ t′ ® app-𝟘 str v ∷ B [ t′ ]₀) ×
     (p ≢ 𝟘 →
      ∀ v′ → t′ ® v′ ∷ A →
      t ∘⟨ p ⟩ t′ ® v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀))          ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                                 (λ hyp v′ ⊢t′ → hyp ⊢t′ .proj₂ p≢𝟘 v′)
                                                               , (λ hyp ⊢t′ → ⊥-elim ∘→ p≢𝟘 , λ _ v′ → hyp v′ ⊢t′)) ⟩
    Δ ⊢ Π p , q ▷ A ▹ B ×
    (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    (∀ t′ v′ → Δ ⊢ t′ ∷ A → t′ ® v′ ∷ A →
     t ∘⟨ p ⟩ t′ ® v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀)            □⇔

opaque

  -- A characterisation lemma for erased Π.

  ®∷Π₀⇔ :
    t ® v ∷ Π 𝟘 , q ▷ A ▹ B ⇔
    (Δ ⊢ Π 𝟘 , q ▷ A ▹ B ×
     (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
     (∀ t′ → Δ ⊢ t′ ∷ A → t ∘⟨ 𝟘 ⟩ t′ ® app-𝟘 str v ∷ B [ t′ ]₀))
  ®∷Π₀⇔ {t} {v} {q} {A} {B} =
    t ® v ∷ Π 𝟘 , q ▷ A ▹ B                                      ⇔⟨ ®∷Π⇔ ⟩

    Δ ⊢ Π 𝟘 , q ▷ A ▹ B ×
    (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    (∀ t′ → Δ ⊢ t′ ∷ A →
     (𝟘 PE.≡ 𝟘 → t ∘⟨ 𝟘 ⟩ t′ ® app-𝟘 str v ∷ B [ t′ ]₀) ×
     (𝟘 ≢ 𝟘 →
      ∀ v′ → t′ ® v′ ∷ A →
      t ∘⟨ 𝟘 ⟩ t′ ® v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀))                ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Π-cong-⇔ λ _ → Π-cong-⇔ λ _ →
                                                                       (λ hyp → hyp .proj₁ PE.refl)
                                                                     , (λ hyp → (λ _ → hyp) , ⊥-elim ∘→ (_$ PE.refl))) ⟩
    Δ ⊢ Π 𝟘 , q ▷ A ▹ B ×
    (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    (∀ t′ → Δ ⊢ t′ ∷ A → t ∘⟨ 𝟘 ⟩ t′ ® app-𝟘 str v ∷ B [ t′ ]₀)  □⇔

opaque
  unfolding _®_∷_ ⊩ΠΣ⇔

  -- A characterisation lemma for Σ.

  ®∷Σ⇔ :
    t ® v ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ⇔
    (Δ ⊢ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     ∃₃ λ t₁ t₂ v₂ →
     t ⇛ prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     t₂ ® v₂ ∷ B [ t₁ ]₀ ×
     (p PE.≡ 𝟘 → v T.⇒* v₂) ×
     (p ≢ 𝟘 → ∃ λ v₁ → v T.⇒* T.prod v₁ v₂ × t₁ ® v₁ ∷ A))
  ®∷Σ⇔ {t} {v} {s} {p} {q} {A} {B} =
      (λ (_ , ⊩Σ , t®v) →
         case B-elim ⊩Σ of λ {
           ⊩Σ′@record{} →
         case irrelevanceTerm ⊩Σ (Bᵣ _ ⊩Σ′) t®v of λ
           (t₁ , t₂ , t⇒ , ⊩t₁ , v₂ , t₂®v₂ , rest) →
         case B-PE-injectivity (BΣ _ _ _) (BΣ _ _ _)
                (whnfRed* (_⊩ₗB⟨_⟩_.D ⊩Σ′) ΠΣₙ) of λ {
           (PE.refl , PE.refl , _) →
         let ⊩wk-A     = _⊩ₗB⟨_⟩_.[F] ⊩Σ′ (id ⊢Δ)
             ⊩wk-B[t₁] = _⊩ₗB⟨_⟩_.[G] ⊩Σ′ (id ⊢Δ) ⊩t₁
         in
         case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩wk-A of λ
           ⊩A →
         case PE.subst (_⊩⟨_⟩_ _ _) (PE.cong _[ t₁ ]₀ $ wk-lift-id B)
                ⊩wk-B[t₁] of λ
           ⊩B[t₁] →
         (Δ ⊢ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
          ∃₃ λ t₁ t₂ v₂ →
          t ⇛ prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
          t₂ ® v₂ ∷ B [ t₁ ]₀ ×
          (p PE.≡ 𝟘 → v T.⇒* v₂) ×
          (p ≢ 𝟘 → ∃ λ v₁ → v T.⇒* T.prod v₁ v₂ × t₁ ® v₁ ∷ A)) ∋
           escape-⊩ ⊩Σ , t₁ , t₂ , v₂ , t⇒
         , ( _
           , ⊩B[t₁]
           , irrelevanceTerm′ (PE.cong _[ t₁ ]₀ $ wk-lift-id B)
               ⊩wk-B[t₁] ⊩B[t₁] t₂®v₂
           )
         , (λ { PE.refl → Σ-®-𝟘 rest })
         , (λ p≢𝟘 →
              case Σ-®-ω p≢𝟘 rest of λ
                (v₁ , v⇒ , t₁®v₁) →
              v₁ , v⇒ ,
              (_ , ⊩A , irrelevanceTerm′ (wk-id _) ⊩wk-A ⊩A t₁®v₁)) }})
    , (λ (⊢Σ , _ , _ , v₂ , t⇒*prod , (_ , ⊩B , t₂®v₂) , hyp₁ , hyp₂) →
         case ⊩ΠΣ⇔ .proj₁ (reducible-⊩ ⊢Σ .proj₂) of λ
           ⊩Σ′@(_ , rest) →
         let ⊩wk-A , wk-B≡wk-B = rest (id ⊢Δ) in
         case inversion-prod-Σ (wf-⇛ t⇒*prod .proj₂) of λ
           (⊢t₁ , _) →
         case reducible-⊩∷ ⊢t₁ of λ
           (_ , ⊩A , ⊩t₁) →
         case IR.irrelevanceTerm′ (PE.sym $ wk-id _) ⊩A ⊩wk-A ⊩t₁ of λ
           ⊩t₁ →
           _ , ⊩ΠΣ⇔ .proj₂ ⊩Σ′ , _ , _ , t⇒*prod , ⊩t₁ , v₂
         , irrelevanceTerm′ (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id B)
             ⊩B (wf-⊩≡ (wk-B≡wk-B (refl-⊩≡∷ (⊩wk-A , ⊩t₁))) .proj₁)
             t₂®v₂
         , (case is-𝟘? p of λ where
              (yes PE.refl) → Σ-®-intro-𝟘 (hyp₁ PE.refl) PE.refl
              (no p≢𝟘)      →
                case hyp₂ p≢𝟘 of λ
                  (v₁ , v⇒*prod , (_ , ⊩A′ , t₁®v₁)) →
                Σ-®-intro-ω v₁ v⇒*prod
                  (irrelevanceTerm′ (PE.sym $ wk-id _) ⊩A′ ⊩wk-A t₁®v₁)
                  p≢𝟘))

opaque

  -- A characterisation lemma for non-erased Σ.

  ®∷Σω⇔ :
    p ≢ 𝟘 →
    t ® v ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ⇔
    (Δ ⊢ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     ∃₄ λ t₁ t₂ v₁ v₂ →
     t ⇛ prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     v T.⇒* T.prod v₁ v₂ ×
     t₁ ® v₁ ∷ A ×
     t₂ ® v₂ ∷ B [ t₁ ]₀)
  ®∷Σω⇔ {p} {t} {v} {s} {q} {A} {B} p≢𝟘 =
    t ® v ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B                            ⇔⟨ ®∷Σ⇔ ⟩

    (Δ ⊢ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     ∃₃ λ t₁ t₂ v₂ →
     t ⇛ prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     t₂ ® v₂ ∷ B [ t₁ ]₀ ×
     (p PE.≡ 𝟘 → v T.⇒* v₂) ×
     (p ≢ 𝟘 → ∃ λ v₁ → v T.⇒* T.prod v₁ v₂ × t₁ ® v₁ ∷ A))  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                  (λ (v₂ , t⇒* , t₂®v₂ , _ , hyp) →
                                                                     case hyp p≢𝟘 of λ
                                                                       (v₁ , v⇒* , t₁®v₁) →
                                                                     v₁ , v₂ , t⇒* , v⇒* , t₁®v₁ , t₂®v₂)
                                                                , (λ (v₁ , v₂ , t⇒* , v⇒* , t₁®v₁ , t₂®v₂) →
                                                                     v₂ , t⇒* , t₂®v₂ , ⊥-elim ∘→ p≢𝟘 , λ _ → v₁ , v⇒* , t₁®v₁)) ⟩
    (Δ ⊢ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     ∃₄ λ t₁ t₂ v₁ v₂ →
     t ⇛ prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
     v T.⇒* T.prod v₁ v₂ ×
     t₁ ® v₁ ∷ A ×
     t₂ ® v₂ ∷ B [ t₁ ]₀)                                   □⇔

opaque

  -- A characterisation lemma for erased Σ.

  ®∷Σ₀⇔ :
    t ® v ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ⇔
    (Δ ⊢ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     ∃₃ λ t₁ t₂ v′ →
     t ⇛ prod s 𝟘 t₁ t₂ ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     v T.⇒* v′ ×
     t₂ ® v′ ∷ B [ t₁ ]₀)
  ®∷Σ₀⇔ {t} {v} {s} {q} {A} {B} =
    t ® v ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B                            ⇔⟨ ®∷Σ⇔ ⟩

    (Δ ⊢ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     ∃₃ λ t₁ t₂ v₂ →
     t ⇛ prod s 𝟘 t₁ t₂ ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     t₂ ® v₂ ∷ B [ t₁ ]₀ ×
     (𝟘 PE.≡ 𝟘 → v T.⇒* v₂) ×
     (𝟘 ≢ 𝟘 → ∃ λ v₁ → v T.⇒* T.prod v₁ v₂ × t₁ ® v₁ ∷ A))  ⇔⟨ (Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ → Σ-cong-⇔ λ _ →
                                                                  (λ (t₂®v₂ , hyp , _) → hyp PE.refl , t₂®v₂)
                                                                , (λ (v⇒* , t₂®v₂) → t₂®v₂ , (λ _ → v⇒*) , ⊥-elim ∘→ (_$ PE.refl))) ⟩
    (Δ ⊢ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     ∃₃ λ t₁ t₂ v′ →
     t ⇛ prod s 𝟘 t₁ t₂ ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
     v T.⇒* v′ ×
     t₂ ® v′ ∷ B [ t₁ ]₀)                                   □⇔

------------------------------------------------------------------------
-- The type formers _®_∷_◂_, _®_∷[_]_◂_ and _▸_⊩ʳ_∷[_]_

opaque

  -- A variant of _®_∷_ that is trivial (up to _⇔_) when the last
  -- argument is 𝟘.

  infix 19 _®_∷_◂_

  _®_∷_◂_ : Term k → T.Term k → Term k → M → Set a
  t ® v ∷ A ◂ p = p ≢ 𝟘 → t ® v ∷ A

opaque

  -- A logical relation for substitutions.

  infix 19 _®_∷[_]_◂_

  _®_∷[_]_◂_ :
    Subst k n → T.Subst k n → Mode → Con Term n → Conₘ n → Set a
  _ ® _  ∷[ _ ] ε     ◂ ε     = Lift _ ⊤
  σ ® σ′ ∷[ m ] Γ ∙ A ◂ γ ∙ p =
    head σ ® T.head σ′ ∷ A [ tail σ ] ◂ ⌜ m ⌝ · p ×
    tail σ ® T.tail σ′ ∷[ m ] Γ ◂ γ

opaque

  -- Validity with respect to erasure.

  infix 19 _▸_⊩ʳ_∷[_]_

  _▸_⊩ʳ_∷[_]_ : Conₘ n → Con Term n → Term n → Mode → Term n → Set a
  γ ▸ Γ ⊩ʳ t ∷[ m ] A =
    ∀ {σ σ′} →
    Δ ⊩ˢ σ ∷ Γ →
    σ ® σ′ ∷[ m ] Γ ◂ γ →
    t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ σ ] ◂ ⌜ m ⌝

------------------------------------------------------------------------
-- Characterisation lemmas for _®_∷_◂_, _®_∷[_]_◂_ and _▸_⊩ʳ_∷[_]_

opaque
  unfolding _®_∷_◂_

  -- A characterisation lemma for _®_∷_◂_.

  ®∷◂⇔ : t ® v ∷ A ◂ p ⇔ (p ≢ 𝟘 → t ® v ∷ A)
  ®∷◂⇔ = id⇔

opaque
  unfolding _®_∷[_]_◂_

  -- A characterisation lemma for _®_∷[_]_◂_.

  ®∷[]ε◂ε⇔ : σ ® σ′ ∷[ m ] ε ◂ ε ⇔ ⊤
  ®∷[]ε◂ε⇔ {σ} {σ′} {m} =
    σ ® σ′ ∷[ m ] ε ◂ ε  ⇔⟨ id⇔ ⟩
    Lift _ ⊤             ⇔⟨ _ ⟩
    ⊤                    □⇔

opaque
  unfolding _®_∷[_]_◂_

  -- Another characterisation lemma for _®_∷[_]_◂_.

  ®∷[]∙◂∙⇔ :
    σ ® σ′ ∷[ m ] Γ ∙ A ◂ γ ∙ p ⇔
    (head σ ® T.head σ′ ∷ A [ tail σ ] ◂ ⌜ m ⌝ · p ×
     tail σ ® T.tail σ′ ∷[ m ] Γ ◂ γ)
  ®∷[]∙◂∙⇔ = id⇔

opaque

  -- Yet another characterisation lemma for _®_∷[_]_◂_.

  ®∷[]◂⇔ :
    σ ® σ′ ∷[ m ] Γ ◂ γ ⇔
    (∀ {A x} → x ∷ A ∈ Γ →
     σ x ® σ′ x ∷ A [ σ ] ◂ ⌜ m ⌝ · γ ⟨ x ⟩)
  ®∷[]◂⇔ {σ} {σ′} {m} {Γ = ε} {γ = ε} =
    σ ® σ′ ∷[ m ] ε ◂ ε                       ⇔⟨ ®∷[]ε◂ε⇔ ⟩

    ⊤                                         ⇔⟨ (λ _ ()) , _ ⟩

    (∀ {A x} →
     x ∷ A ∈ ε →
     σ x ® σ′ x ∷ A [ σ ] ◂ ⌜ m ⌝ · ε ⟨ x ⟩)  □⇔
  ®∷[]◂⇔ {σ} {σ′} {m} {Γ = Γ ∙ A} {γ = γ ∙ p} =
    σ ® σ′ ∷[ m ] Γ ∙ A ◂ γ ∙ p                                     ⇔⟨ ®∷[]∙◂∙⇔ ⟩

    head σ ® T.head σ′ ∷ A [ tail σ ] ◂ ⌜ m ⌝ · p ×
    tail σ ® T.tail σ′ ∷[ m ] Γ ◂ γ                                 ⇔⟨ id⇔ ×-cong-⇔ ®∷[]◂⇔ ⟩

    head σ ® T.head σ′ ∷ A [ tail σ ] ◂ ⌜ m ⌝ · p ×
    (∀ {B x} → x ∷ B ∈ Γ →
     tail σ x ® T.tail σ′ x ∷ B [ tail σ ] ◂ ⌜ m ⌝ · γ ⟨ x ⟩)       ⇔⟨ PE.subst (flip _⇔_ _)
                                                                         (PE.cong₂ (_®_∷_◂_ _ _) (wk1-tail A) PE.refl) id⇔
                                                                         ×-cong-⇔
                                                                       (implicit-Π-cong-⇔ λ B → implicit-Π-cong-⇔ λ _ →
                                                                        Π-cong-⇔ λ _ →
                                                                        PE.subst (flip _⇔_ _)
                                                                          (PE.cong₂ (_®_∷_◂_ _ _) (wk1-tail B) PE.refl) id⇔) ⟩
    head σ ® T.head σ′ ∷ wk1 A [ σ ] ◂ ⌜ m ⌝ · p ×
    (∀ {B x} → x ∷ B ∈ Γ →
     tail σ x ® T.tail σ′ x ∷ wk1 B [ σ ] ◂ ⌜ m ⌝ · γ ⟨ x ⟩)        ⇔⟨ (λ (hyp₁ , hyp₂) → λ { here → hyp₁; (there x∈) → hyp₂ x∈ })
                                                                     , (λ hyp → hyp here , hyp ∘→ there)
                                                                     ⟩
    (∀ {B x} →
     x ∷ B ∈ Γ ∙ A →
     σ x ® σ′ x ∷ B [ σ ] ◂ ⌜ m ⌝ · (γ ∙ p) ⟨ x ⟩)                  □⇔

opaque
  unfolding _▸_⊩ʳ_∷[_]_

  -- A characterisation lemma for _▸_⊩ʳ_∷[_]_.

  ▸⊩ʳ∷⇔ :
    γ ▸ Γ ⊩ʳ t ∷[ m ] A ⇔
    (∀ {σ σ′} → Δ ⊩ˢ σ ∷ Γ → σ ® σ′ ∷[ m ] Γ ◂ γ →
     t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ σ ] ◂ ⌜ m ⌝)
  ▸⊩ʳ∷⇔ = id⇔

------------------------------------------------------------------------
-- Some subsumption lemmas

opaque

  -- Subsumption for _®_∷_◂_.

  subsumption-®∷◂ :
    (p PE.≡ 𝟘 → q PE.≡ 𝟘) →
    t ® v ∷ A ◂ p →
    t ® v ∷ A ◂ q
  subsumption-®∷◂ {p} {q} {t} {v} {A} hyp =
    t ® v ∷ A ◂ p        ⇔⟨ ®∷◂⇔ ⟩→
    (p ≢ 𝟘 → t ® v ∷ A)  →⟨ _∘→ (_∘→ hyp) ⟩
    (q ≢ 𝟘 → t ® v ∷ A)  ⇔˘⟨ ®∷◂⇔ ⟩→
    t ® v ∷ A ◂ q        □

opaque

  -- Subsumption for _®_∷[_]_◂_.

  subsumption-®∷[]◂ :
    (∀ x → γ ⟨ x ⟩ PE.≡ 𝟘 → δ ⟨ x ⟩ PE.≡ 𝟘) →
    σ ® σ′ ∷[ m ] Γ ◂ γ →
    σ ® σ′ ∷[ m ] Γ ◂ δ
  subsumption-®∷[]◂ {γ = ε} {δ = ε} {σ} {σ′} {m} {Γ = ε} _ =
    σ ® σ′ ∷[ m ] ε ◂ ε  □
  subsumption-®∷[]◂
    {γ = γ ∙ p} {δ = δ ∙ q} {σ} {σ′} {m} {Γ = Γ ∙ A} hyp =
    σ ® σ′ ∷[ m ] Γ ∙ A ◂ γ ∙ p                      ⇔⟨ ®∷[]∙◂∙⇔ ⟩→

    head σ ® T.head σ′ ∷ A [ tail σ ] ◂ ⌜ m ⌝ · p ×
    tail σ ® T.tail σ′ ∷[ m ] Γ ◂ γ                  →⟨ Σ.map
                                                          (subsumption-®∷◂ lemma)
                                                          (subsumption-®∷[]◂ (hyp ∘→ _+1)) ⟩
    head σ ® T.head σ′ ∷ A [ tail σ ] ◂ ⌜ m ⌝ · q ×
    tail σ ® T.tail σ′ ∷[ m ] Γ ◂ δ                  ⇔˘⟨ ®∷[]∙◂∙⇔ ⟩→

    σ ® σ′ ∷[ m ] Γ ∙ A ◂ δ ∙ q                      □
    where
    lemma : ⌜ m ⌝ · p PE.≡ 𝟘 → ⌜ m ⌝ · q PE.≡ 𝟘
    lemma = case PE.singleton m of λ where
      (𝟘ᵐ , PE.refl) →
        𝟘 · p PE.≡ 𝟘  →⟨ (λ _ → ·-zeroˡ _) ⟩
        𝟘 · q PE.≡ 𝟘  □
      (𝟙ᵐ , PE.refl) →
        𝟙 · p PE.≡ 𝟘  ≡⟨ PE.cong (PE._≡ _) $ ·-identityˡ _ ⟩→
        p PE.≡ 𝟘      →⟨ hyp x0 ⟩
        q PE.≡ 𝟘      ≡⟨ PE.cong (PE._≡ _) $ PE.sym $ ·-identityˡ _ ⟩→
        𝟙 · q PE.≡ 𝟘  □

opaque

  -- Subsumption for _▸_⊩ʳ_∷[_]_.

  subsumption-▸⊩ʳ∷[] :
    (∀ x → δ ⟨ x ⟩ PE.≡ 𝟘 → γ ⟨ x ⟩ PE.≡ 𝟘) →
    γ ▸ Γ ⊩ʳ t ∷[ m ] A →
    δ ▸ Γ ⊩ʳ t ∷[ m ] A
  subsumption-▸⊩ʳ∷[] {δ} {γ} {Γ} {t} {m} {A} hyp =
    γ ▸ Γ ⊩ʳ t ∷[ m ] A                                 ⇔⟨ ▸⊩ʳ∷⇔ ⟩→

    (∀ {σ σ′} → Δ ⊩ˢ σ ∷ Γ → σ ® σ′ ∷[ m ] Γ ◂ γ →
     t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ σ ] ◂ ⌜ m ⌝)  →⟨ (_∘→ subsumption-®∷[]◂ hyp) ∘→_ ⟩

    (∀ {σ σ′} → Δ ⊩ˢ σ ∷ Γ → σ ® σ′ ∷[ m ] Γ ◂ δ →
     t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ σ ] ◂ ⌜ m ⌝)  ⇔˘⟨ ▸⊩ʳ∷⇔ ⟩→

    δ ▸ Γ ⊩ʳ t ∷[ m ] A                                 □

opaque

  -- Another kind of subsumption for _▸_⊩ʳ_∷[_]_.

  subsumption-▸⊩ʳ∷[]-≤ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
    δ ≤ᶜ γ →
    γ ▸ Γ ⊩ʳ t ∷[ m ] A →
    δ ▸ Γ ⊩ʳ t ∷[ m ] A
  subsumption-▸⊩ʳ∷[]-≤ δ≤γ =
    subsumption-▸⊩ʳ∷[] (λ _ → ≤ᶜ→⟨⟩≡𝟘→⟨⟩≡𝟘 δ≤γ)

------------------------------------------------------------------------
-- Some lemmas related to grades or modes

opaque

  -- If t ® v ∷ A holds, then t ® v ∷ A ◂ p holds for any p.

  ®∷→®∷◂ :
    t ® v ∷ A →
    t ® v ∷ A ◂ p
  ®∷→®∷◂ t®v = ®∷◂⇔ .proj₂ λ _ → t®v

opaque

  -- If t ® v ∷ A ◂ p holds for some non-zero p, then t ® v ∷ A holds.

  ®∷→®∷◂ω :
    p ≢ 𝟘 →
    t ® v ∷ A ◂ p →
    t ® v ∷ A
  ®∷→®∷◂ω {p} {t} {v} {A} p≢𝟘 =
    t ® v ∷ A ◂ p        ⇔⟨ ®∷◂⇔ ⟩→
    (p ≢ 𝟘 → t ® v ∷ A)  →⟨ _$ p≢𝟘 ⟩
    t ® v ∷ A            □

opaque

  -- If p is zero, then t ® v ∷ A ◂ p holds.

  ®∷◂𝟘 : p PE.≡ 𝟘 → t ® v ∷ A ◂ p
  ®∷◂𝟘 p≡𝟘 = ®∷◂⇔ .proj₂ (⊥-elim ∘→ (_$ p≡𝟘))

opaque

  -- The type γ ▸ Γ ⊩ʳ t ∷[ 𝟘ᵐ[ ok ] ] A is inhabited.

  ▸⊩ʳ∷[𝟘ᵐ] : γ ▸ Γ ⊩ʳ t ∷[ 𝟘ᵐ[ ok ] ] A
  ▸⊩ʳ∷[𝟘ᵐ] = ▸⊩ʳ∷⇔ .proj₂ (λ _ _ → ®∷◂𝟘 PE.refl)

------------------------------------------------------------------------
-- Some lemmas related to substitutions

opaque

  -- A source substitution is related to every (matching) target
  -- substitution with respect to the (matching) zero usage context.

  ®∷[]◂𝟘ᶜ : σ ® σ′ ∷[ m ] Γ ◂ 𝟘ᶜ
  ®∷[]◂𝟘ᶜ {m} =
    ®∷[]◂⇔ .proj₂ λ {_} {x = x} x∈Γ →
    ®∷◂𝟘
      (⌜ m ⌝ · 𝟘ᶜ ⟨ x ⟩  ≡⟨ PE.cong (_·_ _) $ 𝟘ᶜ-lookup x ⟩
       ⌜ m ⌝ · 𝟘         ≡⟨ ·-zeroʳ _ ⟩
       𝟘                 ∎)
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- A lemma that can sometimes be used to convert the output from the
  -- fundamental lemma.

  ▸⊩ʳ∷[]→®∷◂ :
    𝟘ᶜ ▸ Δ ⊩ʳ t ∷[ m ] A →
    t ® erase str t ∷ A ◂ ⌜ m ⌝
  ▸⊩ʳ∷[]→®∷◂ {t} {m} {A} =
    𝟘ᶜ ▸ Δ ⊩ʳ t ∷[ m ] A                                                 ⇔⟨ ▸⊩ʳ∷⇔ ⟩→

    (∀ {σ σ′} → Δ ⊩ˢ σ ∷ Δ → σ ® σ′ ∷[ m ] Δ ◂ 𝟘ᶜ →
     t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ σ ] ◂ ⌜ m ⌝)                   →⟨ (λ hyp → hyp (⊩ˢ∷-idSubst (valid ⊢Δ)) (®∷[]◂𝟘ᶜ)) ⟩

    t [ idSubst ] ® erase str t T.[ T.idSubst ] ∷ A [ idSubst ] ◂ ⌜ m ⌝  ≡⟨ PE.cong₃ (λ t v A → t ® v ∷ A ◂ _)
                                                                              (subst-id _) (TP.subst-id _) (subst-id _) ⟩→
    t ® erase str t ∷ A ◂ ⌜ m ⌝                                          □

opaque

  -- A variant of the previous lemma.

  ▸⊩ʳ∷[𝟙ᵐ]→®∷ :
    ⦃ 𝟘-well-behaved : Has-well-behaved-zero M semiring-with-meet ⦄ →
    𝟘ᶜ ▸ Δ ⊩ʳ t ∷[ 𝟙ᵐ ] A →
    t ® erase str t ∷ A
  ▸⊩ʳ∷[𝟙ᵐ]→®∷ {t} {A} =
    𝟘ᶜ ▸ Δ ⊩ʳ t ∷[ 𝟙ᵐ ] A    →⟨ ▸⊩ʳ∷[]→®∷◂ ⟩
    t ® erase str t ∷ A ◂ 𝟙  →⟨ ®∷→®∷◂ω non-trivial ⟩
    t ® erase str t ∷ A      □

------------------------------------------------------------------------
-- Some conversion lemmas

opaque
  unfolding _®_∷_

  -- Conversion for _®_∷_.

  conv-®∷ :
    Δ ⊩⟨ l ⟩ A ≡ B →
    t ® v ∷ A →
    t ® v ∷ B
  conv-®∷ A≡B (_ , ⊩A , t®v) =
    case wf-⊩≡ A≡B of λ
      (_ , ⊩B) →
    _ , ⊩B , convTermʳ ⊩A ⊩B (≅-eq (escape-⊩≡ A≡B)) t®v

opaque

  -- Conversion for _®_∷_◂_.

  conv-®∷◂ :
    Δ ⊩⟨ l ⟩ A ≡ B →
    t ® v ∷ A ◂ p →
    t ® v ∷ B ◂ p
  conv-®∷◂ {l} {A} {B} {t} {v} {p} A≡B =
    t ® v ∷ A ◂ p        ⇔⟨ ®∷◂⇔ ⟩→
    (p ≢ 𝟘 → t ® v ∷ A)  →⟨ conv-®∷ A≡B ∘→_ ⟩
    (p ≢ 𝟘 → t ® v ∷ B)  ⇔˘⟨ ®∷◂⇔ ⟩→
    t ® v ∷ B ◂ p        □

opaque

  -- Conversion for _▸_⊩ʳ_∷[_]_.

  conv-▸⊩ʳ∷ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    γ ▸ Γ ⊩ʳ t ∷[ m ] A →
    γ ▸ Γ ⊩ʳ t ∷[ m ] B
  conv-▸⊩ʳ∷ {Γ} {l} {A} {B} {γ} {t} {m} A≡B =
    γ ▸ Γ ⊩ʳ t ∷[ m ] A                                 ⇔⟨ ▸⊩ʳ∷⇔ ⟩→

    (∀ {σ σ′} → Δ ⊩ˢ σ ∷ Γ → σ ® σ′ ∷[ m ] Γ ◂ γ →
     t [ σ ] ® erase str t T.[ σ′ ] ∷ A [ σ ] ◂ ⌜ m ⌝)  →⟨ (λ hyp ⊩σ σ®σ′ →
                                                              conv-®∷◂ (⊩ᵛ≡⇔′ʰ .proj₁ A≡B .proj₂ .proj₂ ⊩σ) $
                                                              hyp ⊩σ σ®σ′) ⟩
    (∀ {σ σ′} → Δ ⊩ˢ σ ∷ Γ → σ ® σ′ ∷[ m ] Γ ◂ γ →
     t [ σ ] ® erase str t T.[ σ′ ] ∷ B [ σ ] ◂ ⌜ m ⌝)  ⇔˘⟨ ▸⊩ʳ∷⇔ ⟩→

    γ ▸ Γ ⊩ʳ t ∷[ m ] B                                 □

------------------------------------------------------------------------
-- Closure under reduction or expansion

opaque
  unfolding _®_∷_

  -- Closure under reduction of the target language term for _®_∷_.

  ®∷-⇒* :
    v T.⇒* v′ →
    t ® v ∷ A →
    t ® v′ ∷ A
  ®∷-⇒* v⇒v′ (_ , ⊩A , t®v) =
    _ , ⊩A , targetRedSubstTerm*′ ⊩A t®v v⇒v′

opaque
  unfolding _®_∷_

  -- Closure under expansion for _®_∷_.

  ®∷-⇐* :
    t ⇛ t′ ∷ A →
    v T.⇒* v′ →
    t′ ® v′ ∷ A →
    t ® v ∷ A
  ®∷-⇐* t⇒t′ v⇒v′ (_ , ⊩A , t′®v′) =
    _ , ⊩A , redSubstTerm* ⊩A t′®v′ t⇒t′ v⇒v′

opaque
  unfolding _®_∷_◂_

  -- Closure under expansion for _®_∷_◂_.

  ®∷◂-⇐* :
    t ⇛ t′ ∷ A →
    v T.⇒* v′ →
    t′ ® v′ ∷ A ◂ p →
    t ® v ∷ A ◂ p
  ®∷◂-⇐* {t} {t′} {A} {v} {v′} {p} t⇒t′ v⇒v′ =
    t′ ® v′ ∷ A ◂ p        ⇔⟨ ®∷◂⇔ ⟩→
    (p ≢ 𝟘 → t′ ® v′ ∷ A)  →⟨ ®∷-⇐* t⇒t′ v⇒v′ ∘→_ ⟩
    (p ≢ 𝟘 → t ® v ∷ A)    ⇔˘⟨ ®∷◂⇔ ⟩→
    t ® v ∷ A ◂ p          □
