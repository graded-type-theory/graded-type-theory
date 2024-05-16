------------------------------------------------------------------------
-- Validity of the empty type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Empty
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R

open import Tools.Function
open import Tools.Product

private variable
  Γ Δ : Con Term _
  t u : Term _
  l : TypeLevel

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  --  A characterisation lemma for _⊩⟨_⟩_.

  ⊩Empty⇔ :
    Γ ⊩⟨ l ⟩ Empty ⇔ ⊢ Γ
  ⊩Empty⇔ =
      (λ ⊩Empty → lemma (Empty-elim ⊩Empty))
    , (λ ⊢Γ → Emptyᵣ (idRed:*: (Emptyⱼ ⊢Γ)))
    where
    lemma : Γ ⊩⟨ l ⟩Empty Empty → ⊢ Γ
    lemma (emb 0<1 ⊩Empty) = lemma ⊩Empty
    lemma (noemb d) = wf (⊢A-red d)

opaque
  unfolding _⊩⟨_⟩_∷_ ⊩Empty⇔

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Empty⇔ :
    Γ ⊩⟨ l ⟩ t ∷ Empty ⇔ Γ ⊩Empty t ∷Empty
  ⊩∷Empty⇔ =
      (λ (⊩Empty′ , ⊩t) →
         lemma (Empty-elim ⊩Empty′)
           (irrelevanceTerm ⊩Empty′ (Empty-intr (Empty-elim ⊩Empty′)) ⊩t))
    , (λ ⊩t@(Emptyₜ n d n≡n prop) →
         ⊩Empty⇔ .proj₂ (wfTerm (⊢t-redₜ d)) , ⊩t)
    where
    lemma :
      (⊩Empty : Γ ⊩⟨ l ⟩Empty Empty) →
      Γ ⊩⟨ l ⟩ t ∷ Empty / Empty-intr ⊩Empty →
      Γ ⊩Empty t ∷Empty
    lemma (emb 0<1 ⊩Empty′) ⊩t = lemma ⊩Empty′ ⊩t
    lemma (noemb _) ⊩t = ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_∷_ ⊩Empty⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Empty⇔ : Γ ⊩⟨ l ⟩ t ≡ u ∷ Empty ⇔
    (Γ ⊩Empty t ∷Empty ×
     Γ ⊩Empty u ∷Empty ×
     Γ ⊩Empty t ≡ u ∷Empty)
  ⊩≡∷Empty⇔ =
      (λ (⊩Empty′ , ⊩t , ⊩u , t≡u) →
        lemma (Empty-elim ⊩Empty′)
          (irrelevanceTerm ⊩Empty′ (Empty-intr (Empty-elim ⊩Empty′)) ⊩t)
          (irrelevanceTerm ⊩Empty′ (Empty-intr (Empty-elim ⊩Empty′)) ⊩u)
          (irrelevanceEqTerm ⊩Empty′ (Empty-intr (Empty-elim ⊩Empty′)) t≡u))
    , λ (⊩t@(Emptyₜ _ d _ _) , ⊩u , t≡u) →
        ⊩Empty⇔ .proj₂ (wfTerm (⊢t-redₜ d)) , ⊩t , ⊩u , t≡u
    where
    lemma :
      (⊩Empty : Γ ⊩⟨ l ⟩Empty Empty) →
      Γ ⊩⟨ l ⟩ t ∷ Empty / Empty-intr ⊩Empty →
      Γ ⊩⟨ l ⟩ u ∷ Empty / Empty-intr ⊩Empty →
      Γ ⊩⟨ l ⟩ t ≡ u ∷ Empty / Empty-intr ⊩Empty →
      Γ ⊩Empty t ∷Empty ×
      Γ ⊩Empty u ∷Empty ×
      Γ ⊩Empty t ≡ u ∷Empty
    lemma (emb 0<1 ⊩Empty′) ⊩t ⊩u t≡u = lemma ⊩Empty′ ⊩t ⊩u t≡u
    lemma (noemb _) ⊩t ⊩u t≡u = ⊩t , ⊩u , t≡u

------------------------------------------------------------------------
-- Empty

opaque

  -- Reducibility for Empty.

  ⊩Empty : ⊢ Γ → Γ ⊩⟨ l ⟩ Empty
  ⊩Empty = ⊩Empty⇔ .proj₂

opaque

  -- Validity for Empty, seen as a type formerr.

  Emptyᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ l ⟩ Empty
  Emptyᵛ {Γ} {l} ⊩Γ =
    ⊩ᵛ⇔ .proj₂
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ        →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                     ⇔˘⟨ ⊩Empty⇔ ⟩→
          (Δ ⊩⟨ l ⟩ Empty)        →⟨ refl-⊩≡ ⟩
          Δ ⊩⟨ l ⟩ Empty ≡ Empty  □
      )

opaque

  -- Validity for Empty, seen as a term former.

  Emptyᵗᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ ¹ ⟩ Empty ∷ U
  Emptyᵗᵛ ⊩Γ =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛU ⊩Γ
      , λ σ₁≡σ₂ →
          case escape-⊩ˢ≡∷ σ₁≡σ₂ of λ
            (⊢Δ , _) →
          case Emptyⱼ ⊢Δ of λ
            ⊢Empty →
          Type→⊩≡∷U⇔ Emptyₙ Emptyₙ .proj₂
            ( ⊢Empty , ⊢Empty , ≅ₜ-Emptyrefl ⊢Δ
            , (_ , 0<1 , refl-⊩≡ (⊩Empty ⊢Δ))
            )
      )
