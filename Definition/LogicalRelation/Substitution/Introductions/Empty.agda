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
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R

open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product

private variable
  ∇ : DCon (Term 0) _
  Γ Δ : Con Term _
  A B t u : Term _
  l : Universe-level

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  --  A characterisation lemma for _⊩⟨_⟩_.

  ⊩Empty⇔ :
    ∇ » Γ ⊩⟨ l ⟩ Empty ⇔ ∇ »⊢ Γ
  ⊩Empty⇔ =
      wf ∘→ escape-⊩
    , (λ ⊢Γ → Emptyᵣ (id (Emptyⱼ ⊢Γ)))

opaque
  unfolding _»_⊩⟨_⟩_∷_ ⊩Empty⇔

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Empty⇔ :
    ∇ » Γ ⊩⟨ l ⟩ t ∷ Empty ⇔ ∇ » Γ ⊩Empty t ∷Empty
  ⊩∷Empty⇔ =
      (λ (⊩Empty′ , ⊩t) →
         lemma (Empty-elim ⊩Empty′)
           (irrelevanceTerm ⊩Empty′ (Empty-intr (Empty-elim ⊩Empty′)) ⊩t))
    , (λ ⊩t@(Emptyₜ n d n≡n prop) →
         ⊩Empty⇔ .proj₂ (wfEqTerm (subset*Term d)) , ⊩t)
    where
    lemma :
      (⊩Empty : ∇ » Γ ⊩⟨ l ⟩Empty Empty) →
      ∇ » Γ ⊩⟨ l ⟩ t ∷ Empty / Empty-intr ⊩Empty →
      ∇ » Γ ⊩Empty t ∷Empty
    lemma (emb ≤ᵘ-refl ⊩Empty′) ⊩t = lemma ⊩Empty′ ⊩t
    lemma (emb (≤ᵘ-step s) ⊩Empty′) ⊩t = lemma (emb s ⊩Empty′) ⊩t
    lemma (noemb _) ⊩t = ⊩t

opaque
  unfolding _»_⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Empty≡⇔ : ∇ » Γ ⊩⟨ l ⟩ Empty ≡ A ⇔ ∇ » Γ ⊩Empty Empty ≡ A
  ⊩Empty≡⇔ =
      (λ (⊩Empty , _ , Empty≡A) →
         case Empty-elim ⊩Empty of λ
           ⊩Empty′ →
         lemma ⊩Empty′
           ((irrelevanceEq ⊩Empty) (Empty-intr ⊩Empty′) Empty≡A))
    , (λ Empty≡A →
         case id (Emptyⱼ (wfEq (subset* Empty≡A))) of λ
           Empty⇒*Empty →
         let ⊩Empty = Emptyᵣ Empty⇒*Empty in
           ⊩Empty
         , (redSubst* Empty≡A ⊩Empty) .proj₁
         , Empty≡A)
    where
    lemma :
      (⊩A : ∇ » Γ ⊩⟨ l ⟩Empty A) →
      ∇ » Γ ⊩⟨ l ⟩ A ≡ B / Empty-intr ⊩A →
      ∇ » Γ ⊩Empty A ≡ B
    lemma (noemb _)    A≡B = A≡B
    lemma (emb ≤ᵘ-refl ⊩A) A≡B = lemma ⊩A A≡B
    lemma (emb (≤ᵘ-step l<) ⊩A) A≡B = lemma (emb l< ⊩A) A≡B

opaque
  unfolding _»_⊩⟨_⟩_≡_∷_ ⊩Empty⇔

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Empty⇔ :
    ∇ » Γ ⊩⟨ l ⟩ t ≡ u ∷ Empty ⇔ ∇ » Γ ⊩Empty t ≡ u ∷Empty
  ⊩≡∷Empty⇔ =
      (λ (⊩Empty′ , _ , _ , t≡u) →
        lemma (Empty-elim ⊩Empty′)
          (irrelevanceEqTerm ⊩Empty′ (Empty-intr (Empty-elim ⊩Empty′))
             t≡u))
    , λ t≡u@(Emptyₜ₌ _ _ t⇒*t′ u⇒*u′ t′≅u′ prop) →
        case prop of λ where
          (ne (neNfₜ₌ t′-ne u′-ne t′~u′)) →
            let ≅t′ , ≅u′ = wf-⊢≅∷ t′≅u′
                ~t′ , ~u′ = wf-⊢~∷ t′~u′
            in
              ⊩Empty⇔ .proj₂ (wfEqTerm (subset*Term t⇒*t′))
            , Emptyₜ _ t⇒*t′ ≅t′ (ne (neNfₜ t′-ne ~t′))
            , Emptyₜ _ u⇒*u′ ≅u′ (ne (neNfₜ u′-ne ~u′))
            , t≡u
    where
    lemma :
      (⊩Empty : ∇ » Γ ⊩⟨ l ⟩Empty Empty) →
      ∇ » Γ ⊩⟨ l ⟩ t ≡ u ∷ Empty / Empty-intr ⊩Empty →
      ∇ » Γ ⊩Empty t ≡ u ∷Empty
    lemma (emb ≤ᵘ-refl     ⊩Empty′) = lemma ⊩Empty′
    lemma (emb (≤ᵘ-step s) ⊩Empty′) = lemma (emb s ⊩Empty′)
    lemma (noemb _)                 = idᶠ

------------------------------------------------------------------------
-- Empty

opaque

  -- Reducibility for Empty.

  ⊩Empty : ∇ »⊢ Γ → ∇ » Γ ⊩⟨ l ⟩ Empty
  ⊩Empty = ⊩Empty⇔ .proj₂

opaque

  -- Validity for Empty, seen as a type formerr.

  Emptyᵛ : ∇ »⊩ᵛ Γ → ∇ » Γ ⊩ᵛ⟨ l ⟩ Empty
  Emptyᵛ {∇} {Γ} {l} ⊩Γ =
    ⊩ᵛ⇔ʰ .proj₂
      ( ⊩Γ
      , λ {_} {∇′} {_} ξ⊇ {_} {Δ} {σ₁} {σ₂} →
          ∇′ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ        →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ∇′ »⊢ Δ                      ⇔˘⟨ ⊩Empty⇔ ⟩→
          (∇′ » Δ ⊩⟨ l ⟩ Empty)        →⟨ refl-⊩≡ ⟩
          ∇′ » Δ ⊩⟨ l ⟩ Empty ≡ Empty  □
      )

opaque

  -- Validity for Empty, seen as a term former.

  Emptyᵗᵛ : ∇ »⊩ᵛ Γ → ∇ » Γ ⊩ᵛ⟨ 1 ⟩ Empty ∷ U 0
  Emptyᵗᵛ ⊩Γ =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ⊩ᵛU ⊩Γ
      , λ ξ⊇ σ₁≡σ₂ →
          case escape-⊩ˢ≡∷ σ₁≡σ₂ of λ
            (⊢Δ , _) →
          Type→⊩≡∷U⇔ Emptyₙ Emptyₙ .proj₂
            (≤ᵘ-refl , refl-⊩≡ (⊩Empty ⊢Δ) , ≅ₜ-Emptyrefl ⊢Δ)
      )
