------------------------------------------------------------------------
-- A variant of the logical relation with a hidden reducibility
-- argument, along with variants of some other relations
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

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
open Modality 𝕄 hiding (_≤_)

open import Definition.LogicalRelation TR as L
open import Definition.LogicalRelation.Fundamental.Reducibility TR
open import Definition.LogicalRelation.Hidden TR
import Definition.LogicalRelation.Irrelevance TR as IR
open import Definition.LogicalRelation.Properties TR
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
    (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    ∃ λ l′ → l′ L.≤ l ×
    ∀ t′ v′ → Δ ⊢ t′ ∷ A → t′ ®⟨ l′ ⟩ v′ ∷ A →
    t ∘⟨ p ⟩ t′ ®⟨ l′ ⟩ v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀
  ®-Π {p} {B} p≢𝟘 (⊩Π , t®v) =
    lemma (B-elim (BΠ _ _) ⊩Π) $
    irrelevanceTerm ⊩Π (B-intr (BΠ _ _) (B-elim (BΠ _ _) ⊩Π)) t®v
    where
    lemma :
      (⊩Π : Δ ⊩⟨ l ⟩B⟨ BΠ p q ⟩ Π p , q ▷ A ▹ B) →
      t ®⟨ l ⟩ v ∷ Π p , q ▷ A ▹ B / B-intr (BΠ p q) ⊩Π →
      (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
      ∃ λ l′ → l′ L.≤ l ×
      ∀ t′ v′ → Δ ⊢ t′ ∷ A → t′ ®⟨ l′ ⟩ v′ ∷ A →
      t ∘⟨ p ⟩ t′ ®⟨ l′ ⟩ v T.∘⟨ str ⟩ v′ ∷ B [ t′ ]₀
    lemma (emb 0<1 ⊩Π) t®v =
      case lemma ⊩Π t®v of λ {
        (⇒*lam , _ , refl , f) →
      ⇒*lam , _ , emb 0<1 , f }
    lemma (noemb ⊩Π) t®v = t®v .proj₁ , _ , refl , λ t′ v′ ⊢t′ t′®v′ →
      case B-PE-injectivity (BΠ _ _) (BΠ _ _)
             (whnfRed* (red (_⊩ₗB⟨_⟩_.D ⊩Π)) ΠΣₙ) of λ {
        (PE.refl , PE.refl , _) →
      case reducibleTerm $
           PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-id _) ⊢t′ of λ {
        (⊩A , ⊩t′) →
      case IR.irrelevanceTerm ⊩A (_⊩ₗB⟨_⟩_.[F] ⊩Π W.id ⊢Δ) ⊩t′ of λ
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
    (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    ∃ λ l′ → l′ L.≤ l ×
    ∀ t′ → Δ ⊢ t′ ∷ A → t ∘⟨ 𝟘 ⟩ t′ ®⟨ l′ ⟩ app-𝟘 str v ∷ B [ t′ ]₀
  ®-Π₀ {B} (⊩Π , t®v) =
    lemma (B-elim (BΠ _ _) ⊩Π) $
    irrelevanceTerm ⊩Π (B-intr (BΠ _ _) (B-elim (BΠ _ _) ⊩Π)) t®v
    where
    lemma :
      (⊩Π : Δ ⊩⟨ l ⟩B⟨ BΠ 𝟘 q ⟩ Π 𝟘 , q ▷ A ▹ B) →
      t ®⟨ l ⟩ v ∷ Π 𝟘 , q ▷ A ▹ B / B-intr (BΠ 𝟘 q) ⊩Π →
      (str PE.≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
      ∃ λ l′ → l′ L.≤ l ×
      ∀ t′ → Δ ⊢ t′ ∷ A → t ∘⟨ 𝟘 ⟩ t′ ®⟨ l′ ⟩ app-𝟘 str v ∷ B [ t′ ]₀
    lemma (emb 0<1 ⊩Π) t®v =
      case lemma ⊩Π t®v of λ {
        (⇒*lam , _ , refl , f) →
      ⇒*lam , _ , emb 0<1 , f }
    lemma (noemb ⊩Π) t®v = t®v .proj₁ , _ , refl , λ t′ ⊢t′ →
      case B-PE-injectivity (BΠ _ _) (BΠ _ _)
             (whnfRed* (red (_⊩ₗB⟨_⟩_.D ⊩Π)) ΠΣₙ) of λ {
        (PE.refl , PE.refl , _) →
      case reducibleTerm $
           PE.subst (_⊢_∷_ _ _) (PE.sym $ wk-id _) ⊢t′ of λ {
        (⊩A , ⊩t′) →
      case IR.irrelevanceTerm ⊩A (_⊩ₗB⟨_⟩_.[F] ⊩Π W.id ⊢Δ) ⊩t′ of λ
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
      , λ ⊩σ _ → ®∷◂𝟘 PE.refl (⊩ᵛ⇔′ .proj₁ ⊩A .proj₂ .proj₁ ⊩σ)
      )

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
  unfolding _®⟨_⟩_∷_◂_

  -- Closure under expansion for _®⟨_⟩_∷_◂_.

  ®∷◂-⇐* :
    Δ ⊢ t ⇒* t′ ∷ A →
    v T.⇒* v′ →
    t′ ®⟨ l ⟩ v′ ∷ A ◂ p →
    t ®⟨ l ⟩ v ∷ A ◂ p
  ®∷◂-⇐* t⇒t′ v⇒v′ (_ , t′®v′) =
    _ , redSubstTerm*-◂ t′®v′ t⇒t′ v⇒v′
