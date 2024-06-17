------------------------------------------------------------------------
-- Validity for natural numbers
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Nat
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
  Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Var R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction.Primitive R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  Γ Δ                               : Con Term _
  A A₁ A₂ B t t₁ t₂ u u₁ u₂ v v₁ v₂ : Term _
  σ₁ σ₂                             : Subst _ _
  l l′ l″ l‴                        : TypeLevel
  p q r                             : M

------------------------------------------------------------------------
-- Characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ℕ⇔ : Γ ⊩⟨ l ⟩ ℕ ⇔ ⊢ Γ
  ⊩ℕ⇔ =
      lemma ∘→ ℕ-elim
    , (λ ⊢Γ → ℕᵣ ([_,_,_] (ℕⱼ ⊢Γ) (ℕⱼ ⊢Γ) (id (ℕⱼ ⊢Γ))))
    where
    lemma : Γ ⊩⟨ l ⟩ℕ ℕ → ⊢ Γ
    lemma (emb 0<1 ⊩ℕ)           = lemma ⊩ℕ
    lemma (noemb [ ⊢ℕ , _ , _ ]) = wf ⊢ℕ

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩ℕ∷U⇔ : Γ ⊩⟨ ¹ ⟩ ℕ ∷ U ⇔ ⊢ Γ
  ⊩ℕ∷U⇔ =
      (λ ⊩ℕ →
         case ⊩∷U⇔ .proj₁ ⊩ℕ of λ
           (_ , _ , ℕ⇒* , _) →
         wfTerm (⊢t-redₜ ℕ⇒*))
    , (λ ⊢Γ →
         ⊩∷U⇔ .proj₂
           ( (_ , 0<1 , ⊩ℕ⇔ .proj₂ ⊢Γ)
           , (_ , idRedTerm:*: (ℕⱼ ⊢Γ) , ℕₙ , ≅ₜ-ℕrefl ⊢Γ)
           ))

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷ℕ⇔ : Γ ⊩⟨ l ⟩ t ∷ ℕ ⇔ Γ ⊩ℕ t ∷ℕ
  ⊩∷ℕ⇔ =
      (λ (⊩ℕ , ⊩t) →
         lemma (ℕ-elim ⊩ℕ)
           ((irrelevanceTerm ⊩ℕ) (ℕ-intr (ℕ-elim ⊩ℕ)) ⊩t))
    , (λ ⊩t →
         ℕᵣ (idRed:*: (ℕⱼ (wfTerm (⊢t-redₜ (_⊩ℕ_∷ℕ.d ⊩t))))) , ⊩t)
    where
    lemma :
      (⊩A : Γ ⊩⟨ l ⟩ℕ A) →
      Γ ⊩⟨ l ⟩ t ∷ A / ℕ-intr ⊩A →
      Γ ⊩ℕ t ∷ℕ
    lemma (noemb _)    ⊩t = ⊩t
    lemma (emb 0<1 ⊩A) ⊩t = lemma ⊩A ⊩t

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩zero∷ℕ⇔ : Γ ⊩⟨ l ⟩ zero ∷ ℕ ⇔ ⊢ Γ
  ⊩zero∷ℕ⇔ =
      wfTerm ∘→ escape-⊩∷
    , (λ ⊢Γ →
         ⊩∷ℕ⇔ .proj₂ $
         ℕₜ _ (idRedTerm:*: (zeroⱼ ⊢Γ)) (≅ₜ-zerorefl ⊢Γ) zeroᵣ)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩suc∷ℕ⇔ :
    Γ ⊩⟨ l ⟩ suc t ∷ ℕ ⇔
    Γ ⊩⟨ l ⟩ t ∷ ℕ
  ⊩suc∷ℕ⇔ {Γ} {l} {t} =
    Γ ⊩⟨ l ⟩ suc t ∷ ℕ  ⇔⟨ ⊩∷ℕ⇔ ⟩
    Γ ⊩ℕ suc t ∷ℕ       ⇔⟨ (λ (ℕₜ _ suc-t⇒*u _ u-ok) →
                              case whnfRed*Term (redₜ suc-t⇒*u) sucₙ of λ {
                                PE.refl →
                              lemma u-ok })
                         , (λ ⊩t@(ℕₜ _ [ ⊢t , _ , t⇒*u ] u≅u u-ok) →
                              let u-whnf = naturalWhnf (natural u-ok) in
                              ℕₜ _ (idRedTerm:*: (sucⱼ ⊢t))
                                (≅-suc-cong $
                                 ≅ₜ-red (id (ℕⱼ (wfTerm ⊢t))) t⇒*u t⇒*u
                                   ℕₙ u-whnf u-whnf u≅u)
                                (sucᵣ ⊩t))
                         ⟩
    Γ ⊩ℕ t ∷ℕ           ⇔˘⟨ ⊩∷ℕ⇔ ⟩
    Γ ⊩⟨ l ⟩ t ∷ ℕ      □⇔
    where
    lemma : Natural-prop Γ (suc t) → Γ ⊩ℕ t ∷ℕ
    lemma (sucᵣ ⊩t) = ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ℕ≡⇔ : Γ ⊩⟨ l ⟩ ℕ ≡ A ⇔ Γ ⊩ℕ ℕ ≡ A
  ⊩ℕ≡⇔ =
      (λ (⊩ℕ , _ , ℕ≡A) →
         lemma (ℕ-elim ⊩ℕ)
           ((irrelevanceEq ⊩ℕ) (ℕ-intr (ℕ-elim ⊩ℕ)) ℕ≡A))
    , (λ ℕ≡A →
         case idRed:*: (ℕⱼ (wfEq (subset* ℕ≡A))) of λ
           ℕ⇒*ℕ →
         let ⊩ℕ = ℕᵣ ℕ⇒*ℕ in
           ⊩ℕ
         , (redSubst* ℕ≡A ⊩ℕ) .proj₁
         , ℕ≡A)
    where
    lemma :
      (⊩A : Γ ⊩⟨ l ⟩ℕ A) →
      Γ ⊩⟨ l ⟩ A ≡ B / ℕ-intr ⊩A →
      Γ ⊩ℕ A ≡ B
    lemma (noemb _)    A≡B = A≡B
    lemma (emb 0<1 ⊩A) A≡B = lemma ⊩A A≡B

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩ℕ≡ℕ∷U⇔ : Γ ⊩⟨ ¹ ⟩ ℕ ≡ ℕ ∷ U ⇔ ⊢ Γ
  ⊩ℕ≡ℕ∷U⇔ =
      (λ ℕ≡ℕ →
         case ⊩≡∷U⇔ .proj₁ ℕ≡ℕ of λ
           (_ , _ , _ , ℕ⇒* , _) →
         wfTerm (⊢t-redₜ ℕ⇒*))
    , (λ ⊢Γ →
         case idRedTerm:*: (ℕⱼ ⊢Γ) of λ
           ℕ⇒*ℕ →
         ⊩≡∷U⇔ .proj₂
           ( (_ , 0<1 , ⊩ℕ≡⇔ .proj₂ (id (ℕⱼ ⊢Γ)))
           , (_ , _ , ℕ⇒*ℕ , ℕ⇒*ℕ , ℕₙ , ℕₙ , ≅ₜ-ℕrefl ⊢Γ)
           ))

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷ℕ⇔ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ ⇔
    (Γ ⊩ℕ t ∷ℕ × Γ ⊩ℕ u ∷ℕ × Γ ⊩ℕ t ≡ u ∷ℕ)
  ⊩≡∷ℕ⇔ =
      (λ (⊩ℕ , ⊩t , ⊩u , t≡u) →
         lemma (ℕ-elim ⊩ℕ)
           ((irrelevanceTerm ⊩ℕ) (ℕ-intr (ℕ-elim ⊩ℕ)) ⊩t)
           ((irrelevanceTerm ⊩ℕ) (ℕ-intr (ℕ-elim ⊩ℕ)) ⊩u)
           ((irrelevanceEqTerm ⊩ℕ) (ℕ-intr (ℕ-elim ⊩ℕ)) t≡u))
    , (λ (⊩t , ⊩u , t≡u) →
         ℕᵣ (idRed:*: (ℕⱼ (wfTerm (⊢t-redₜ (_⊩ℕ_≡_∷ℕ.d t≡u)))))
       , ⊩t , ⊩u , t≡u)
    where
    lemma :
      (⊩A : Γ ⊩⟨ l ⟩ℕ A) →
      Γ ⊩⟨ l ⟩ t ∷ A / ℕ-intr ⊩A →
      Γ ⊩⟨ l ⟩ u ∷ A / ℕ-intr ⊩A →
      Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ℕ-intr ⊩A →
      Γ ⊩ℕ t ∷ℕ × Γ ⊩ℕ u ∷ℕ × Γ ⊩ℕ t ≡ u ∷ℕ
    lemma (noemb _)    ⊩t ⊩u t≡u = ⊩t , ⊩u , t≡u
    lemma (emb 0<1 ⊩A) ⊩t ⊩u t≡u = lemma ⊩A ⊩t ⊩u t≡u

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zero≡zero∷ℕ⇔ : Γ ⊩⟨ l ⟩ zero ≡ zero ∷ ℕ ⇔ ⊢ Γ
  ⊩zero≡zero∷ℕ⇔ {Γ} {l} =
    Γ ⊩⟨ l ⟩ zero ≡ zero ∷ ℕ  ⇔⟨ proj₁ ∘→ wf-⊩≡∷ , refl-⊩≡∷ ⟩
    Γ ⊩⟨ l ⟩ zero ∷ ℕ         ⇔⟨ ⊩zero∷ℕ⇔ ⟩
    ⊢ Γ                       □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩suc≡suc∷ℕ⇔ :
    Γ ⊩⟨ l ⟩ suc t ≡ suc u ∷ ℕ ⇔
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ
  ⊩suc≡suc∷ℕ⇔ {Γ} {l} {t} {u} =
    Γ ⊩⟨ l ⟩ suc t ≡ suc u ∷ ℕ                             ⇔⟨ ⊩≡∷ℕ⇔ ⟩
    Γ ⊩ℕ suc t ∷ℕ × Γ ⊩ℕ suc u ∷ℕ × Γ ⊩ℕ suc t ≡ suc u ∷ℕ  ⇔⟨ ⊩∷ℕ⇔ {l = l} ∘⇔ ⊩suc∷ℕ⇔ ∘⇔ sym⇔ ⊩∷ℕ⇔
                                                                ×-cong-⇔
                                                              ⊩∷ℕ⇔ {l = l} ∘⇔ ⊩suc∷ℕ⇔ ∘⇔ sym⇔ ⊩∷ℕ⇔
                                                                ×-cong-⇔
                                                              (lemma₁ , lemma₂) ⟩
    Γ ⊩ℕ t ∷ℕ × Γ ⊩ℕ u ∷ℕ × Γ ⊩ℕ t ≡ u ∷ℕ                  ⇔˘⟨ ⊩≡∷ℕ⇔ ⟩
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ                                     □⇔
    where
    lemma₀ : [Natural]-prop Γ (suc t) (suc u) → Γ ⊩ℕ t ≡ u ∷ℕ
    lemma₀ (sucᵣ t≡u) = t≡u

    lemma₁ : Γ ⊩ℕ suc t ≡ suc u ∷ℕ → Γ ⊩ℕ t ≡ u ∷ℕ
    lemma₁ (ℕₜ₌ _ _ suc-t⇒*t′ suc-u⇒*u′ _ t′≡u′) =
      case whnfRed*Term (redₜ suc-t⇒*t′) sucₙ of λ {
        PE.refl →
      case whnfRed*Term (redₜ suc-u⇒*u′) sucₙ of λ {
        PE.refl →
      lemma₀ t′≡u′}}

    lemma₂ : Γ ⊩ℕ t ≡ u ∷ℕ → Γ ⊩ℕ suc t ≡ suc u ∷ℕ
    lemma₂
      t≡u@(ℕₜ₌ _ _ [ ⊢t , _ , t⇒*t′ ] [ ⊢u , _ , u⇒*u′ ] t′≅u′ t′≡u′) =
      let t′-ok , u′-ok = split t′≡u′ in
      ℕₜ₌ _ _ (idRedTerm:*: (sucⱼ ⊢t)) (idRedTerm:*: (sucⱼ ⊢u))
        (≅-suc-cong $
         ≅ₜ-red (id (ℕⱼ (wfTerm ⊢t))) t⇒*t′ u⇒*u′ ℕₙ
           (naturalWhnf t′-ok) (naturalWhnf u′-ok) t′≅u′)
        (sucᵣ t≡u)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩zero≡suc∷ℕ⇔ : Γ ⊩⟨ l ⟩ zero ≡ suc t ∷ ℕ ⇔ ⊥
  ⊩zero≡suc∷ℕ⇔ =
      (λ zero≡suc →
         case ⊩≡∷ℕ⇔ .proj₁ zero≡suc of λ
           (_ , _ , ℕₜ₌ _ _ zero⇒* suc⇒* _ rest) →
         case whnfRed*Term (redₜ zero⇒*) zeroₙ of λ {
           PE.refl →
         case whnfRed*Term (redₜ suc⇒*) sucₙ of λ {
           PE.refl →
         case rest of λ where
           (ne (neNfₜ₌ () _ _)) }})
    , ⊥-elim

------------------------------------------------------------------------
-- ℕ

opaque

  -- Validity of ℕ, seen as a type former.

  ℕᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ l ⟩ ℕ
  ℕᵛ {Γ} {l} ⊩Γ =
    ⊩ᵛ⇔ .proj₂
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ  →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ               →⟨ ℕⱼ ⟩
          (Δ ⊢ ℕ)           →⟨ id ⟩
          Δ ⊢ ℕ ⇒* ℕ        ⇔˘⟨ ⊩ℕ≡⇔ ⟩→
          Δ ⊩⟨ l ⟩ ℕ ≡ ℕ    □
      )

opaque

  -- Validity of ℕ, seen as a term former.

  ℕᵗᵛ : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ ¹ ⟩ ℕ ∷ U
  ℕᵗᵛ {Γ} ⊩Γ =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛU ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ    →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                 ⇔˘⟨ ⊩ℕ≡ℕ∷U⇔ ⟩→
          Δ ⊩⟨ ¹ ⟩ ℕ ≡ ℕ ∷ U  □
      )

------------------------------------------------------------------------
-- The constructors zero and suc

opaque

  -- Reducibility of zero.

  ⊩zero :
    ⊢ Γ →
    Γ ⊩⟨ l ⟩ zero ∷ ℕ
  ⊩zero = ⊩zero∷ℕ⇔ .proj₂

opaque

  -- Validity of zero.

  zeroᵛ :
    ⊩ᵛ Γ →
    Γ ⊩ᵛ⟨ l ⟩ zero ∷ ℕ
  zeroᵛ {Γ} {l} ⊩Γ =
    ⊩ᵛ∷⇔ .proj₂
      ( ℕᵛ ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ          →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                       ⇔˘⟨ ⊩zero≡zero∷ℕ⇔ ⟩→
          Δ ⊩⟨ l ⟩ zero ≡ zero ∷ ℕ  □
      )

opaque

  -- Reducibility of suc.

  ⊩suc :
    Γ ⊩⟨ l ⟩ t ∷ ℕ →
    Γ ⊩⟨ l ⟩ suc t ∷ ℕ
  ⊩suc = ⊩suc∷ℕ⇔ .proj₂

opaque

  -- Reducibility of equality between applications of suc.

  ⊩suc≡suc :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ ℕ →
    Γ ⊩⟨ l ⟩ suc t ≡ suc u ∷ ℕ
  ⊩suc≡suc = ⊩suc≡suc∷ℕ⇔ .proj₂

opaque

  -- Validity of suc.

  sucᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ suc t ∷ ℕ
  sucᵛ ⊩t =
    ⊩ᵛ∷⇔ .proj₂
      ( wf-⊩ᵛ∷ ⊩t
      , ⊩suc≡suc ∘→ ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂
      )

opaque

  -- Validity of equality preservation for suc.

  suc-congᵛ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ suc t ≡ suc u ∷ ℕ
  suc-congᵛ t≡u =
    case wf-⊩ᵛ≡∷ t≡u of λ
      (⊩t , ⊩u) →
    ⊩ᵛ≡∷⇔′ .proj₂
      ( sucᵛ ⊩t
      , sucᵛ ⊩u
      , ⊩suc≡suc ∘→ ⊩ᵛ≡∷⇔′ .proj₁ t≡u .proj₂ .proj₂
      )

------------------------------------------------------------------------
-- The eliminator natrec

private opaque

  -- A variant of natrec-subst for _⊢_⇒*_∷_.

  natrec-subst*′ :
    Γ ∙ ℕ ⊢ A →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l′ ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ A [ v₁ ]₀ ≡ A [ v₂ ]₀) →
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊢ v₁ ⇒* v₂ ∷ ℕ →
    Γ ⊩⟨ l′ ⟩ v₂ ∷ ℕ →
    Γ ⊢ natrec p q r A t u v₁ ⇒* natrec p q r A t u v₂ ∷ A [ v₁ ]₀
  natrec-subst*′
    {A} {t} {u} {v₁} {v₂} {p} {q} {r} ⊢A A≡A ⊢t ⊢u v₁⇒*v₂ ⊩v₂ =
    case v₁⇒*v₂ of λ where
      (id ⊢v₁) →
        id (natrecⱼ ⊢A ⊢t ⊢u ⊢v₁)
      (_⇨_ {t′ = v₃} v₁⇒v₃ v₃⇒*v₂) →
        case
          v₁  ⇒⟨ v₁⇒v₃ ⟩⊩∷
          v₃  ∎⟨ wf-⊩≡∷ (⊩∷-⇐* v₃⇒*v₂ ⊩v₂) .proj₁ ⟩⊩∷
        of λ
          v₁≡v₃ →
        natrec p q r A t u v₁ ∷ A [ v₁ ]₀  ⇒⟨ natrec-subst ⊢A ⊢t ⊢u v₁⇒v₃ ⟩∷
                                            ⟨ ≅-eq $ escape-⊩≡ $ A≡A v₁≡v₃ ⟩⇒
        natrec p q r A t u v₃ ∷ A [ v₃ ]₀  ⇒*⟨ natrec-subst*′ ⊢A A≡A ⊢t ⊢u v₃⇒*v₂ ⊩v₂ ⟩∎∷
        natrec p q r A t u v₂              ∎

opaque

  -- A variant of natrec-subst for _⊢_⇒*_∷_.

  natrec-subst* :
    Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊢ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊢ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊢ v₁ ⇒* v₂ ∷ ℕ →
    Γ ⊩⟨ l′ ⟩ v₂ ∷ ℕ →
    Γ ⊢ natrec p q r A t u v₁ ⇒* natrec p q r A t u v₂ ∷ A [ v₁ ]₀
  natrec-subst* ⊩A =
    natrec-subst*′ (escape-⊩ᵛ ⊩A) (⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩A))

private opaque

  -- A lemma used to prove ⊩natrec≡natrec.

  ⊩natrec≡natrec′ :
    Γ ∙ ℕ ⊢ A₁ →
    Γ ∙ ℕ ⊢ A₂ →
    Γ ∙ ℕ ⊢ A₁ ≅ A₂ →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ A₁ [ v₁ ]₀ ≡ A₁ [ v₂ ]₀) →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ A₂ [ v₁ ]₀ ≡ A₂ [ v₂ ]₀) →
    (∀ {v₁ v₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ A₁ [ v₁ ]₀ ≡ A₂ [ v₂ ]₀) →
    Γ ⊢ t₁ ∷ A₁ [ zero ]₀ →
    Γ ⊢ t₂ ∷ A₂ [ zero ]₀ →
    Γ ⊩⟨ l ⟩ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
    Γ ∙ ℕ ∙ A₁ ⊢ u₁ ∷ A₁ [ suc (var x1) ]↑² →
    Γ ∙ ℕ ∙ A₂ ⊢ u₂ ∷ A₂ [ suc (var x1) ]↑² →
    Γ ∙ ℕ ∙ A₁ ⊢ u₁ ≅ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    (∀ {v₁ v₂ w₁ w₂} →
     Γ ⊩⟨ l ⟩ v₁ ≡ v₂ ∷ ℕ →
     Γ ⊩⟨ l ⟩ w₁ ≡ w₂ ∷ A₁ [ v₁ ]₀ →
     Γ ⊩⟨ l ⟩ u₁ [ v₁ , w₁ ]₁₀ ≡ u₂ [ v₂ , w₂ ]₁₀ ∷ A₁ [ suc v₁ ]₀) →
    Γ ⊩ℕ v₁ ∷ℕ →
    Γ ⊩ℕ v₂ ∷ℕ →
    Γ ⊩ℕ v₁ ≡ v₂ ∷ℕ →
    Γ ⊩⟨ l ⟩ natrec p q r A₁ t₁ u₁ v₁ ≡
      natrec p q r A₂ t₂ u₂ v₂ ∷ A₁ [ v₁ ]₀
  ⊩natrec≡natrec′
    {A₁} {A₂} {l} {t₁} {t₂} {u₁} {u₂} {v₁} {v₂} {p} {q} {r}
    ⊢A₁ ⊢A₂ A₁≅A₂ A₁≡A₁ A₂≡A₂ A₁≡A₂ ⊢t₁ ⊢t₂ t₁≡t₂ ⊢u₁ ⊢u₂ u₁≅u₂ u₁≡u₂
    ⊩ℕ-v₁@(ℕₜ v₁′′ v₁⇒*v₁′′ _ v₁′′-prop)
    ⊩ℕ-v₂@(ℕₜ v₂′′ v₂⇒*v₂′′ _ v₂′′-prop)
    ⊩ℕ-v₁≡v₂@(ℕₜ₌ v₁′ v₂′ v₁⇒*v₁′ v₂⇒*v₂′ v₁′≅v₂′ v₁′∼v₂′) =
    -- The terms v₁′ and v₁′′ are equal, as are the terms v₂′
    -- and v₂′′.
    case Σ.map naturalWhnf naturalWhnf $ split v₁′∼v₂′ of λ
      (v₁′-whnf , v₂′-whnf) →
    case whrDet*Term (redₜ v₁⇒*v₁′ , v₁′-whnf)
           (redₜ v₁⇒*v₁′′ , naturalWhnf (natural v₁′′-prop)) of λ {
      PE.refl →
    case whrDet*Term (redₜ v₂⇒*v₂′ , v₂′-whnf)
           (redₜ v₂⇒*v₂′′ , naturalWhnf (natural v₂′′-prop)) of λ {
      PE.refl →

    -- Some definitions related to v₁ and v₂.
    case ⊩≡∷ℕ⇔ {l = l} .proj₂ (⊩ℕ-v₁ , ⊩ℕ-v₂ , ⊩ℕ-v₁≡v₂) of λ
      v₁≡v₂ →
    case wf-⊩≡∷ v₁≡v₂ of λ
      (⊩v₁ , ⊩v₂) →

    -- Some definitions related to v₁′ and v₂′.
    case ⊩∷-⇒* v₁⇒*v₁′ ⊩v₁ of λ
      v₁≡v₁′ →
    case ⊩∷-⇒* v₂⇒*v₂′ ⊩v₂ of λ
      v₂≡v₂′ →
    case wf-⊩≡∷ v₁≡v₁′ .proj₂ of λ
      ⊩v₁′ →
    case wf-⊩≡∷ v₂≡v₂′ .proj₂ of λ
      ⊩v₂′ →
    case
      v₁′  ≡˘⟨ v₁≡v₁′ ⟩⊩∷
      v₁   ≡⟨ v₁≡v₂ ⟩⊩∷
      v₂   ≡⟨ v₂≡v₂′ ⟩⊩∷∎
      v₂′  ∎
    of λ
      v₁′≡v₂′ →
    case A₁≡A₂ v₁′≡v₂′ of λ
      A₁[v₁′]≡A₂[v₂′] →
    case ≅-eq $ escape-⊩≡ A₁[v₁′]≡A₂[v₂′] of λ
      ⊢A₁[v₁′]≡A₂[v₂′] →

    -- The two applications of natrec are equal if applications of
    -- natrec to v₁′ and v₂′ are equal.
    case
      (λ (hyp : _ ⊩⟨ l ⟩ _ ≡ _ ∷ _) →
         natrec p q r A₁ t₁ u₁ v₁ ∷ A₁ [ v₁ ]₀    ⇒*⟨ natrec-subst*′ ⊢A₁ A₁≡A₁ ⊢t₁ ⊢u₁ (redₜ v₁⇒*v₁′) ⊩v₁′ ⟩⊩∷∷
                                                    ⟨ A₁≡A₁ v₁≡v₁′ ⟩⊩∷
         natrec p q r A₁ t₁ u₁ v₁′ ∷ A₁ [ v₁′ ]₀  ≡⟨ hyp ⟩⊩∷∷⇐*
                                                   ⟨ ⊢A₁[v₁′]≡A₂[v₂′] ⟩⇒
                                   ∷ A₂ [ v₂′ ]₀  ˘⟨ ≅-eq $ escape-⊩≡ $ A₂≡A₂ v₂≡v₂′ ⟩⇐
         natrec p q r A₂ t₂ u₂ v₂′ ∷ A₂ [ v₂ ]₀   ⇐*⟨ natrec-subst*′ ⊢A₂ A₂≡A₂ ⊢t₂ ⊢u₂ (redₜ v₂⇒*v₂′) ⊩v₂′ ⟩∎∷
         natrec p q r A₂ t₂ u₂ v₂                 ∎)
    of λ
      lemma →

    lemma
      (case v₁′∼v₂′ of λ where
         -- If v₁′ and v₂′ are equal neutral terms, then one can
         -- conclude by using the fact that the applications of natrec
         -- to v₁′ and v₂′ are equal neutral terms.
         (ne (neNfₜ₌ v₁′-ne v₂′-ne v₁′~v₂′)) →
           neutral-⊩≡∷ (wf-⊩≡ A₁[v₁′]≡A₂[v₂′] .proj₁)
             (natrecₙ v₁′-ne) (natrecₙ v₂′-ne)
             (natrecⱼ ⊢A₁ ⊢t₁ ⊢u₁ (escape-⊩∷ ⊩v₁′))
             (conv (natrecⱼ ⊢A₂ ⊢t₂ ⊢u₂ (escape-⊩∷ ⊩v₂′))
                (sym ⊢A₁[v₁′]≡A₂[v₂′])) $
           ~-natrec ⊢A₁ A₁≅A₂ (escape-⊩≡∷ t₁≡t₂) u₁≅u₂ v₁′~v₂′

         -- If v₁′ and v₂′ are both zero, then one can conclude by
         -- using the rule natrec-zero and the fact that t₁ is equal
         -- to t₂.
         zeroᵣ →
           natrec p q r A₁ t₁ u₁ zero  ⇒⟨ natrec-zero ⊢A₁ ⊢t₁ ⊢u₁ ⟩⊩∷
           t₁ ∷ A₁ [ zero ]₀           ≡⟨ t₁≡t₂ ⟩⊩∷∷⇐*
                                        ⟨ ⊢A₁[v₁′]≡A₂[v₂′] ⟩⇒
           t₂ ∷ A₂ [ zero ]₀           ⇐⟨ natrec-zero ⊢A₂ ⊢t₂ ⊢u₂ , ⊢t₂ ⟩∎∷
           natrec p q r A₂ t₂ u₂ zero  ∎

         -- If v₁′ and v₂′ are applications of suc to equal terms,
         -- then one can conclude by using the rule natrec-suc and an
         -- inductive hypothesis.
         (sucᵣ {n = v₁″} {n′ = v₂″} ⊩ℕ-v₁″≡v₂″) →
           case v₁′′-prop of λ {
             (ne suc-ne) → case _⊩neNf_∷_.neK suc-ne of λ ();
             (sucᵣ ⊩ℕ-v₁″) →
           case v₂′′-prop of λ {
             (ne suc-ne) → case _⊩neNf_∷_.neK suc-ne of λ ();
             (sucᵣ ⊩ℕ-v₂″) →
           case ⊩≡∷ℕ⇔ .proj₂ (⊩ℕ-v₁″ , ⊩ℕ-v₂″ , ⊩ℕ-v₁″≡v₂″) of λ
             v₁″≡v₂″ →
           case wf-⊩≡∷ v₁″≡v₂″ of λ
             (⊩v₁″ , ⊩v₂″) →
           case u₁≡u₂ v₁″≡v₂″ $
                ⊩natrec≡natrec′ ⊢A₁ ⊢A₂ A₁≅A₂ A₁≡A₁ A₂≡A₂ A₁≡A₂
                  ⊢t₁ ⊢t₂ t₁≡t₂ ⊢u₁ ⊢u₂ u₁≅u₂ u₁≡u₂
                  ⊩ℕ-v₁″ ⊩ℕ-v₂″ ⊩ℕ-v₁″≡v₂″ of λ
             u₁[v₁″,nr]≡u₂[v₂″,nr] →

           natrec p q r A₁ t₁ u₁ (suc v₁″)                             ⇒⟨ natrec-suc ⊢A₁ ⊢t₁ ⊢u₁ (escape-⊩∷ ⊩v₁″) ⟩⊩∷
           u₁ [ v₁″ , natrec p q r A₁ t₁ u₁ v₁″ ]₁₀ ∷ A₁ [ suc v₁″ ]₀  ≡⟨ u₁[v₁″,nr]≡u₂[v₂″,nr] ⟩⊩∷∷⇐*
                                                                        ⟨ ⊢A₁[v₁′]≡A₂[v₂′] ⟩⇒
           u₂ [ v₂″ , natrec p q r A₂ t₂ u₂ v₂″ ]₁₀ ∷ A₂ [ suc v₂″ ]₀  ⇐⟨ natrec-suc ⊢A₂ ⊢t₂ ⊢u₂ (escape-⊩∷ ⊩v₂″)
                                                                        , escape-⊩∷ $
                                                                          conv-⊩∷ A₁[v₁′]≡A₂[v₂′] $
                                                                          wf-⊩≡∷ u₁[v₁″,nr]≡u₂[v₂″,nr] .proj₂
                                                                        ⟩∎∷
           natrec p q r A₂ t₂ u₂ (suc v₂″)                             ∎ }}) }}

opaque

  -- Reducibility of equality between applications of natrec.

  ⊩natrec≡natrec :
    Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
    Γ ∙ ℕ ∙ A₁ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    Γ ⊩ᵛ⟨ l‴ ⟩ v₁ ≡ v₂ ∷ ℕ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ natrec p q r A₁ t₁ u₁ v₁ [ σ₁ ] ≡
      natrec p q r A₂ t₂ u₂ v₂ [ σ₂ ] ∷ A₁ [ v₁ ]₀ [ σ₁ ]
  ⊩natrec≡natrec {l} {A₁} {A₂} {σ₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (_ , ⊩t₂) →
    case conv-⊩ᵛ∷
           (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ A₁≡A₂ $
            refl-⊩ᵛ≡∷ $ zeroᵛ {l = l} $ wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t₂))
           ⊩t₂ of λ
      ⊩t₂ →
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case conv-∙-⊩ᵛ∷ A₁≡A₂ $
         conv-⊩ᵛ∷
           (⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² A₁≡A₂ $
            sucᵛ (varᵛ (there here) (wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩u₁)) .proj₂))
         ⊩u₂ of λ
      ⊩u₂ →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →

    case ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] A₁≡A₂ σ₁≡σ₂ of λ
      A₁[σ₁⇑]≡A₂[σ₂⇑] →
    case PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift A₁ _) $
         ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ σ₁≡σ₂ of λ
      t₁[σ₁]≡t₂[σ₂] →
    case PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (natrecSucCase _ A₁) $
         ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ u₁≡u₂ σ₁≡σ₂ of λ
      u₁[σ₁⇑⇑]≡u₂[σ₂⇑⇑] →

    case ⊩≡∷ℕ⇔ .proj₁ $
         ⊩ᵛ≡∷⇔′ .proj₁ v₁≡v₂ .proj₂ .proj₂ σ₁≡σ₂ of λ
      (⊩ℕ-v₁ , ⊩ℕ-v₂ , ⊩ℕ-v₁≡v₂) →

    PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ singleSubstLift A₁ _) $
    ⊩natrec≡natrec′
      (escape $ wf-⊩≡ A₁[σ₁⇑]≡A₂[σ₂⇑] .proj₁)
      (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩A₂ ⊩σ₂)
      (escape-⊩≡ A₁[σ₁⇑]≡A₂[σ₂⇑])
      (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₁) (refl-⊩ˢ≡∷ ⊩σ₁))
      (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩A₂) (refl-⊩ˢ≡∷ ⊩σ₂))
      (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂)
      (escape-⊩∷ $ wf-⊩≡∷ t₁[σ₁]≡t₂[σ₂] .proj₁)
      (PE.subst (_⊢_∷_ _ _) (singleSubstLift A₂ _) $
       escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t₂ ⊩σ₂)
      (level-⊩≡∷
         (wf-⊩≡
            (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $
             refl-⊩≡∷ $ ⊩zero {l = l} $ escape-⊩ˢ∷ ⊩σ₁ .proj₁)
            .proj₁)
         t₁[σ₁]≡t₂[σ₂])
      (escape-⊩∷ $ wf-⊩≡∷ u₁[σ₁⇑⇑]≡u₂[σ₂⇑⇑] .proj₁)
      (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A₂) $
       escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ ⊩u₂ ⊩σ₂)
      (escape-⊩≡∷ u₁[σ₁⇑⇑]≡u₂[σ₂⇑⇑])
      (λ {v₁ = v₁} {v₂ = _} {w₁ = w₁} v₁≡v₂ w₁≡w₂ →
         level-⊩≡∷
           (wf-⊩≡
              (⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ A₁≡A₂ σ₁≡σ₂ $
               ⊩suc≡suc v₁≡v₂)
              .proj₁) $
         PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
           (A₁ [ suc (var x1) ]↑² [ σ₁ ⇑ ⇑ ] [ v₁ , w₁ ]₁₀  ≡⟨ PE.cong _[ _ , _ ]₁₀ $ natrecSucCase _ A₁ ⟩
            A₁ [ σ₁ ⇑ ] [ suc (var x1) ]↑² [ v₁ , w₁ ]₁₀    ≡˘⟨ substComp↑² (A₁ [ _ ]) _ ⟩
            A₁ [ σ₁ ⇑ ] [ suc v₁ ]₀                         ∎) $
         ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ u₁≡u₂ σ₁≡σ₂ v₁≡v₂ w₁≡w₂)
      ⊩ℕ-v₁ ⊩ℕ-v₂ ⊩ℕ-v₁≡v₂
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- Validity of natrec.

  natrecᵛ :
    Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l″ ⟩ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊩ᵛ⟨ l‴ ⟩ v ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ natrec p q r A t u v ∷ A [ v ]₀
  natrecᵛ ⊩A ⊩t ⊩u ⊩v =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩A ⊩v
      , ⊩natrec≡natrec (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u)
          (refl-⊩ᵛ≡∷ ⊩v)
      )

opaque

  -- Validity of equality preservation for natrec.

  natrec-congᵛ :
    Γ ∙ ℕ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ [ zero ]₀ →
    Γ ∙ ℕ ∙ A₁ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A₁ [ suc (var x1) ]↑² →
    Γ ⊩ᵛ⟨ l‴ ⟩ v₁ ≡ v₂ ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ natrec p q r A₁ t₁ u₁ v₁ ≡ natrec p q r A₂ t₂ u₂ v₂ ∷
      A₁ [ v₁ ]₀
  natrec-congᵛ {l} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case wf-⊩ᵛ≡∷ v₁≡v₂ of λ
      (⊩v₁ , ⊩v₂) →
    ⊩ᵛ≡∷⇔′ .proj₂
      ( natrecᵛ ⊩A₁ ⊩t₁ ⊩u₁ ⊩v₁
      , conv-⊩ᵛ∷ (sym-⊩ᵛ≡ (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ A₁≡A₂ v₁≡v₂))
          (natrecᵛ ⊩A₂
             (conv-⊩ᵛ∷
                (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ A₁≡A₂
                   (refl-⊩ᵛ≡∷ (zeroᵛ {l = l} (wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t₁)))))
                ⊩t₂)
             (conv-∙-⊩ᵛ∷ A₁≡A₂ $
              conv-⊩ᵛ∷
                (⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² A₁≡A₂ $
                 sucᵛ $ varᵛ (there here) (wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩u₁)) .proj₂)
                ⊩u₂)
             ⊩v₂)
      , ⊩natrec≡natrec A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂
      )

opaque

  -- Validity of the equality rule called natrec-zero.

  natrec-zeroᵛ :
    Γ ∙ ℕ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l″ ⟩ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊩ᵛ⟨ l ⟩ natrec p q r A t u zero ≡ t ∷ A [ zero ]₀
  natrec-zeroᵛ {A} ⊩A ⊩t ⊩u =
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ singleSubstLift A _) $
         natrec-zero
           (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩A ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
            escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ ⊩u ⊩σ))
      ⊩t

opaque

  -- Validity of the equality rule called natrec-suc.

  natrec-sucᵛ :
    Γ ∙ ℕ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ A [ zero ]₀ →
    Γ ∙ ℕ ∙ A ⊩ᵛ⟨ l ⟩ u ∷ A [ suc (var x1) ]↑² →
    Γ ⊩ᵛ⟨ l‴ ⟩ v ∷ ℕ →
    Γ ⊩ᵛ⟨ l ⟩ natrec p q r A t u (suc v) ≡
      u [ v , natrec p q r A t u v ]₁₀ ∷ A [ suc v ]₀
  natrec-sucᵛ {A} {u} ⊩A ⊩t ⊩u ⊩v =
    ⊩ᵛ∷-⇐
      (λ ⊩σ →
         PE.subst₂ (_⊢_⇒_∷_ _ _) (PE.sym $ [,]-[]-commute u)
           (PE.sym $ singleSubstLift A _) $
         natrec-suc
           (escape $ ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩A ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (singleSubstLift A _) $
            escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ)
           (PE.subst (_⊢_∷_ _ _) (natrecSucCase _ A) $
            escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ ⊩u ⊩σ)
           (escape-⊩∷ $ ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩v ⊩σ))
      (PE.subst (_⊩ᵛ⟨_⟩_∷_ _ _ _) (PE.sym $ substComp↑² A _) $
       ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ ⊩u ⊩v (natrecᵛ ⊩A ⊩t ⊩u ⊩v))
