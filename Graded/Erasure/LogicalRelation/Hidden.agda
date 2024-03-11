------------------------------------------------------------------------
-- A variant of the logical relation with a hidden reducibility
-- argument
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)
open import Tools.Relation

module Graded.Erasure.LogicalRelation.Hidden
  {a} {M : Set a}
  {𝕄 : Modality M}
  (open Modality 𝕄)
  (is-𝟘? : (p : M) → Dec (p ≡ 𝟘))
  {TR : Type-restrictions 𝕄}
  (as : Assumptions TR)
  where

open Assumptions as

open import Definition.LogicalRelation TR as L
open import Definition.LogicalRelation.Fundamental.Reducibility TR
open import Definition.LogicalRelation.ShapeView TR
open import Definition.LogicalRelation.Substitution TR
import Definition.LogicalRelation.Substitution.Irrelevance TR as IS
open import Definition.LogicalRelation.Substitution.Properties TR
open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.Typed.RedSteps TR
import Definition.Typed.Weakening TR as W
open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Properties M

open import Graded.Context 𝕄
open import Graded.Erasure.Extraction 𝕄 is-𝟘?
open import Graded.Erasure.LogicalRelation is-𝟘? as
open import Graded.Erasure.LogicalRelation.Irrelevance is-𝟘? as
open import Graded.Erasure.LogicalRelation.Subsumption is-𝟘? as
import Graded.Erasure.Target as T
import Graded.Erasure.Target.Properties as TP
open import Graded.Mode 𝕄

open import Tools.Function
open import Tools.Product

private variable
  A B t t₁ t₂ : Term _
  v           : T.Term _
  p q         : M
  s           : Strength
  l           : TypeLevel

------------------------------------------------------------------------
-- The type former

opaque

  -- A variant of the logical relation with a hidden reducibility
  -- argument.

  infix 19 _®⟨_⟩_∷_

  _®⟨_⟩_∷_ : Term k → TypeLevel → T.Term k → Term k → Set a
  t ®⟨ l ⟩ v ∷ A =
    ∃ λ (⊩A : Δ ⊩⟨ l ⟩ A) → t ®⟨ l ⟩ v ∷ A / ⊩A

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
    t ®⟨ l ⟩ erase t ∷ A
  hidden-®-intro-fundamental 𝟙≢𝟘 (⊩Δ , ⊩A , ⊩t) =
    case IS.irrelevanceSubst _ _ (soundContext ⊩Δ) ⊢Δ
           (idSubstS ⊩Δ) of λ {
      ⊩σ →
    PE.subst₃ (_®⟨ _ ⟩_∷_) (subst-id _) (TP.subst-id _) (subst-id _) $
    hidden-®-intro (⊩A .unwrap _ ⊩σ .proj₁)
      (⊩t ⊩σ (erasedSubst _ ⊩σ) ◀≢𝟘 𝟙≢𝟘) }

------------------------------------------------------------------------
-- "Rewriting" lemmas for _®⟨_⟩_∷_

opaque
  unfolding _®⟨_⟩_∷_

  -- A rewriting lemma for U.

  ®-U : t ®⟨ l ⟩ v ∷ U → t ® v ∷U
  ®-U (⊩U′ , t®v) =
    irrelevanceTerm ⊩U′
      (Uᵣ (extractMaybeEmb (U-elim ⊩U′) .proj₂)) t®v

opaque
  unfolding _®⟨_⟩_∷_

  -- A rewriting lemma for Empty.

  ®-Empty : t ®⟨ l ⟩ v ∷ Empty → t ® v ∷Empty
  ®-Empty (⊩Empty′ , t®v) =
    irrelevanceTerm {l′ = ¹} ⊩Empty′
      (Emptyᵣ (extractMaybeEmb (Empty-elim ⊩Empty′) .proj₂)) t®v

opaque
  unfolding _®⟨_⟩_∷_

  -- A rewriting lemma for Unit.

  ®-Unit : t ®⟨ l ⟩ v ∷ Unit s → t ® v ∷Unit⟨ s ⟩
  ®-Unit (⊩Unit′ , t®v) =
    irrelevanceTerm {l′ = ¹} ⊩Unit′
      (Unitᵣ (extractMaybeEmb (Unit-elim ⊩Unit′) .proj₂)) t®v

opaque
  unfolding _®⟨_⟩_∷_

  -- A rewriting lemma for ℕ.

  ®-ℕ : t ®⟨ l ⟩ v ∷ ℕ → t ® v ∷ℕ
  ®-ℕ (⊩ℕ′ , t®v) =
    irrelevanceTerm {l′ = ¹} ⊩ℕ′
      (ℕᵣ (extractMaybeEmb (ℕ-elim ⊩ℕ′) .proj₂)) t®v

opaque
  unfolding _®⟨_⟩_∷_

  -- A rewriting lemma for Id.

  ®-Id : t ®⟨ l ⟩ v ∷ Id A t₁ t₂ → t ® v ∷Id⟨ A ⟩⟨ t₁ ⟩⟨ t₂ ⟩
  ®-Id (⊩Id , t®v) =
    case extractMaybeEmb (Id-elim ⊩Id) .proj₂ of λ {
      ⊩Id′ →
    case irrelevanceTerm ⊩Id (Idᵣ ⊩Id′) t®v of λ {
      (rflᵣ t⇒* ⇒*↯) →
    rflᵣ (conv* t⇒* (sym (subset* (red (_⊩ₗId_.⇒*Id ⊩Id′))))) ⇒*↯ }}

opaque
  unfolding _®⟨_⟩_∷_

  -- A rewriting lemma for non-erased Π.

  ®-Π :
    p ≢ 𝟘 →
    t ®⟨ l ⟩ v ∷ Π p , q ▷ A ▹ B →
    (∃ λ v′ → v T.⇒* T.lam v′) ×
    ∃ λ l′ → l′ L.≤ l ×
    ∀ t′ v′ → Δ ⊢ t′ ∷ A → t′ ®⟨ l′ ⟩ v′ ∷ A →
    t ∘⟨ p ⟩ t′ ®⟨ l′ ⟩ v T.∘⟨ T.non-strict ⟩ v′ ∷ B [ t′ ]₀
  ®-Π {p} {B} p≢𝟘 (⊩Π , t®v) =
    lemma (B-elim (BΠ _ _) ⊩Π) $
    irrelevanceTerm ⊩Π (B-intr (BΠ _ _) (B-elim (BΠ _ _) ⊩Π)) t®v
    where
    lemma :
      (⊩Π : Δ ⊩⟨ l ⟩B⟨ BΠ p q ⟩ Π p , q ▷ A ▹ B) →
      t ®⟨ l ⟩ v ∷ Π p , q ▷ A ▹ B / B-intr (BΠ p q) ⊩Π →
      (∃ λ v′ → v T.⇒* T.lam v′) ×
      ∃ λ l′ → l′ L.≤ l ×
      ∀ t′ v′ → Δ ⊢ t′ ∷ A → t′ ®⟨ l′ ⟩ v′ ∷ A →
      t ∘⟨ p ⟩ t′ ®⟨ l′ ⟩ v T.∘⟨ T.non-strict ⟩ v′ ∷ B [ t′ ]₀
    lemma (emb 0<1 ⊩Π) t®v =
      case lemma ⊩Π t®v of λ {
        (⇒*lam , _ , refl , f) →
      ⇒*lam , _ , emb 0<1 , f }
    lemma (noemb ⊩Π) t®v = t®v .proj₁ , _ , refl , λ t′ v′ ⊢t′ t′®v′ →
      case B-PE-injectivity (BΠ _ _) (BΠ _ _)
             (whnfRed* (red (_⊩ₗB⟨_⟩_.D ⊩Π)) ΠΣₙ) of λ {
        (PE.refl , PE.refl , _) →
      case reducibleTerm′ (_⊩ₗB⟨_⟩_.[F] ⊩Π W.id ⊢Δ) $
           PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-id _) ⊢t′ of λ {
        ⊩t′ →
      case PE.subst (_⊩⟨_⟩_ _ _)
             (PE.cong _[ _ ]₀ $ wk-lift-id B) $
           _⊩ₗB⟨_⟩_.[G] ⊩Π W.id ⊢Δ ⊩t′ of λ {
        ⊩B[t′] →
        ⊩B[t′]
      , irrelevanceTerm′ (PE.cong _[ t′ ]₀ $ wk-lift-id B)
          (_⊩ₗB⟨_⟩_.[G] ⊩Π W.id ⊢Δ ⊩t′) ⊩B[t′]
          (Π-®-ω p≢𝟘 (is-𝟘? p) (t®v .proj₂ ⊩t′)
             (irrelevanceTerm′ (PE.sym $ wk-id _) (t′®v′ .proj₁)
                (_⊩ₗB⟨_⟩_.[F] ⊩Π W.id ⊢Δ) $
              t′®v′ .proj₂)) }}}

opaque
  unfolding _®⟨_⟩_∷_

  -- A rewriting lemma for erased Π.

  ®-Π₀ :
    t ®⟨ l ⟩ v ∷ Π 𝟘 , q ▷ A ▹ B →
    (∃ λ v′ → v T.⇒* T.lam v′) ×
    ∃ λ l′ → l′ L.≤ l ×
    ∀ t′ → Δ ⊢ t′ ∷ A →
    t ∘⟨ 𝟘 ⟩ t′ ®⟨ l′ ⟩ v T.∘⟨ T.non-strict ⟩ T.↯ ∷ B [ t′ ]₀
  ®-Π₀ {B} (⊩Π , t®v) =
    lemma (B-elim (BΠ _ _) ⊩Π) $
    irrelevanceTerm ⊩Π (B-intr (BΠ _ _) (B-elim (BΠ _ _) ⊩Π)) t®v
    where
    lemma :
      (⊩Π : Δ ⊩⟨ l ⟩B⟨ BΠ 𝟘 q ⟩ Π 𝟘 , q ▷ A ▹ B) →
      t ®⟨ l ⟩ v ∷ Π 𝟘 , q ▷ A ▹ B / B-intr (BΠ 𝟘 q) ⊩Π →
      (∃ λ v′ → v T.⇒* T.lam v′) ×
      ∃ λ l′ → l′ L.≤ l ×
      ∀ t′ → Δ ⊢ t′ ∷ A →
      t ∘⟨ 𝟘 ⟩ t′ ®⟨ l′ ⟩ v T.∘⟨ T.non-strict ⟩ T.↯ ∷ B [ t′ ]₀
    lemma (emb 0<1 ⊩Π) t®v =
      case lemma ⊩Π t®v of λ {
        (⇒*lam , _ , refl , f) →
      ⇒*lam , _ , emb 0<1 , f }
    lemma (noemb ⊩Π) t®v = t®v .proj₁ , _ , refl , λ t′ ⊢t′ →
      case B-PE-injectivity (BΠ _ _) (BΠ _ _)
             (whnfRed* (red (_⊩ₗB⟨_⟩_.D ⊩Π)) ΠΣₙ) of λ {
        (PE.refl , PE.refl , _) →
      case reducibleTerm′ (_⊩ₗB⟨_⟩_.[F] ⊩Π W.id ⊢Δ) $
           PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-id _) ⊢t′ of λ {
        ⊩t′ →
      case PE.subst (_⊩⟨_⟩_ _ _)
             (PE.cong _[ _ ]₀ $ wk-lift-id B) $
           _⊩ₗB⟨_⟩_.[G] ⊩Π W.id ⊢Δ ⊩t′ of λ {
        ⊩B[t′] →
        ⊩B[t′]
      , irrelevanceTerm′ (PE.cong _[ t′ ]₀ $ wk-lift-id B)
          (_⊩ₗB⟨_⟩_.[G] ⊩Π W.id ⊢Δ ⊩t′) ⊩B[t′]
          (Π-®-𝟘 (is-𝟘? 𝟘) (t®v .proj₂ ⊩t′)) }}}

opaque
  unfolding _®⟨_⟩_∷_

  -- A rewriting lemma for non-erased Σ.

  ®-Σ :
    p ≢ 𝟘 →
    t ®⟨ l ⟩ v ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B →
    ∃ λ l′ → l′ L.≤ l × ∃₄ λ t₁ t₂ v₁ v₂ →
    Δ ⊢ t ⇒* prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
    v T.⇒* T.prod v₁ v₂ ×
    t₁ ®⟨ l′ ⟩ v₁ ∷ A ×
    t₂ ®⟨ l′ ⟩ v₂ ∷ B [ t₁ ]₀
  ®-Σ {p} {B} p≢𝟘 (⊩Σ , t®v) =
    lemma (B-elim (BΣ _ _ _) ⊩Σ) $
    irrelevanceTerm ⊩Σ (B-intr (BΣ _ _ _) (B-elim (BΣ _ _ _) ⊩Σ)) t®v
    where
    lemma :
      (⊩Σ : Δ ⊩⟨ l ⟩B⟨ BΣ s p q ⟩ Σ⟨ s ⟩ p , q ▷ A ▹ B) →
      t ®⟨ l ⟩ v ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B / B-intr (BΣ s p q) ⊩Σ →
      ∃ λ l′ → l′ L.≤ l × ∃₄ λ t₁ t₂ v₁ v₂ →
      Δ ⊢ t ⇒* prod s p t₁ t₂ ∷ Σ⟨ s ⟩ p , q ▷ A ▹ B ×
      v T.⇒* T.prod v₁ v₂ ×
      t₁ ®⟨ l′ ⟩ v₁ ∷ A ×
      t₂ ®⟨ l′ ⟩ v₂ ∷ B [ t₁ ]₀
    lemma (emb 0<1 ⊩Σ) t®v =
      case lemma ⊩Σ t®v of λ {
        (_ , refl , f) →
      _ , emb 0<1 , f }
    lemma (noemb ⊩Σ) (t₁ , t₂ , t⇒ , ⊩t₁ , v₂ , t₂®v₂ , rest) =
      case B-PE-injectivity (BΣ _ _ _) (BΣ _ _ _)
             (whnfRed* (red (_⊩ₗB⟨_⟩_.D ⊩Σ)) ΠΣₙ) of λ {
        (PE.refl , PE.refl , _) →
      case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _)
             (_⊩ₗB⟨_⟩_.[F] ⊩Σ W.id ⊢Δ) of λ {
        ⊩A →
      let ⊩wk-B[t₁] = _⊩ₗB⟨_⟩_.[G] ⊩Σ W.id ⊢Δ ⊩t₁ in
      case PE.subst (_⊩⟨_⟩_ _ _) (PE.cong _[ t₁ ]₀ $ wk-lift-id B)
             ⊩wk-B[t₁] of λ {
        ⊩B[t₁] →
      case Σ-®-ω p≢𝟘 rest of λ {
        (v₁ , v⇒ , t₁®v₁) →
      -- Note that ⊩t₁ is not returned.
        _ , refl , t₁ , t₂ , v₁ , v₂ , t⇒ , v⇒
      , ( ⊩A
        , irrelevanceTerm′ (wk-id _)
            (_⊩ₗB⟨_⟩_.[F] ⊩Σ W.id ⊢Δ) ⊩A t₁®v₁
        )
      , ( ⊩B[t₁]
        , irrelevanceTerm′ (PE.cong _[ t₁ ]₀ $ wk-lift-id B)
            ⊩wk-B[t₁] ⊩B[t₁] t₂®v₂
        ) }}}}

opaque
  unfolding _®⟨_⟩_∷_

  -- A rewriting lemma for erased Σ.

  ®-Σ₀ :
    t ®⟨ l ⟩ v ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B →
    ∃ λ l′ → l′ L.≤ l × ∃₃ λ t₁ t₂ v′ →
    Δ ⊢ t ⇒* prod s 𝟘 t₁ t₂ ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
    v T.⇒* v′ ×
    t₂ ®⟨ l′ ⟩ v′ ∷ B [ t₁ ]₀
  ®-Σ₀ {B} (⊩Σ , t®v) =
    lemma (B-elim (BΣ _ _ _) ⊩Σ) $
    irrelevanceTerm ⊩Σ (B-intr (BΣ _ _ _) (B-elim (BΣ _ _ _) ⊩Σ)) t®v
    where
    lemma :
      (⊩Σ : Δ ⊩⟨ l ⟩B⟨ BΣ s 𝟘 q ⟩ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B) →
      t ®⟨ l ⟩ v ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B / B-intr (BΣ s 𝟘 q) ⊩Σ →
      ∃ λ l′ → l′ L.≤ l × ∃₃ λ t₁ t₂ v′ →
      Δ ⊢ t ⇒* prod s 𝟘 t₁ t₂ ∷ Σ⟨ s ⟩ 𝟘 , q ▷ A ▹ B ×
      v T.⇒* v′ ×
      t₂ ®⟨ l′ ⟩ v′ ∷ B [ t₁ ]₀
    lemma (emb 0<1 ⊩Σ) t®v =
      case lemma ⊩Σ t®v of λ {
        (_ , refl , f) →
      _ , emb 0<1 , f }
    lemma (noemb ⊩Σ) (t₁ , t₂ , t⇒ , ⊩t₁ , v₂ , t₂®v₂ , rest) =
      case B-PE-injectivity (BΣ _ _ _) (BΣ _ _ _)
             (whnfRed* (red (_⊩ₗB⟨_⟩_.D ⊩Σ)) ΠΣₙ) of λ {
        (PE.refl , PE.refl , _) →
      let ⊩wk-B[t₁] = _⊩ₗB⟨_⟩_.[G] ⊩Σ W.id ⊢Δ ⊩t₁ in
      case PE.subst (_⊩⟨_⟩_ _ _) (PE.cong _[ t₁ ]₀ $ wk-lift-id B)
             ⊩wk-B[t₁] of λ {
        ⊩B[t₁] →
      -- Note that ⊩t₁ is not returned.
        _ , refl , t₁ , t₂ , v₂ , t⇒ , Σ-®-𝟘 rest
      , ( ⊩B[t₁]
        , irrelevanceTerm′ (PE.cong _[ t₁ ]₀ $ wk-lift-id B)
            ⊩wk-B[t₁] ⊩B[t₁] t₂®v₂
        ) }}
