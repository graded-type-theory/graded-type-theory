------------------------------------------------------------------------
-- Validity of the universe type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R
open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Neutral M type-variant
open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Hidden R {{eqrel}}
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R {{eqrel}}
open import Definition.LogicalRelation.Substitution.Introductions.Level R {{eqrel}}

open import Tools.Function
open import Tools.Nat as N using (Nat; 1+; 2+)
open import Tools.Product as Σ
open import Tools.Empty
import Tools.PropositionalEquality as PE

private
  variable
    n    : Nat
    Γ    : Con Term n
    A B t u : Term n
    l l′ : Universe-level
    k    : LogRelKit

------------------------------------------------------------------------
-- Some characterisation lemmas

private

  -- A lemma used below.

<<<<<<< HEAD
  U⇒*U→≡ : Γ ⊢ U t :⇒*: U u → t PE.≡ u
  U⇒*U→≡ {Γ} {t} {u} =
    Γ ⊢ U t :⇒*: U u →⟨ red ⟩
    Γ ⊢ U t ⇒* U u   →⟨ flip whnfRed* Uₙ ⟩
    U t PE.≡ U u     →⟨ (λ { PE.refl → PE.refl }) ⟩
    t PE.≡ u         □
=======
  U⇒*U→≡ : Γ ⊢ U l ⇒* U l′ → l PE.≡ l′
  U⇒*U→≡ {Γ} {l} {l′} =
    Γ ⊢ U l ⇒* U l′  →⟨ flip whnfRed* Uₙ ⟩
    U l PE.≡ U l′    →⟨ (λ { PE.refl → PE.refl }) ⟩
    l PE.≡ l′        □
>>>>>>> master

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩U⇔ :
    Γ ⊩⟨ l ⟩ U t ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l
  ⊩U⇔ =
<<<<<<< HEAD
      lemma _ ∘→ U-elim
    , λ ([t] , t<l) → Uᵣ′ _ [t] t<l (idRed:*: (Uⱼ (escapeLevel [t])))
    where
    lemma :
      ∀ l → Γ ⊩⟨ l ⟩U U t →
      Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l
    lemma = <ᵘ-rec _ λ where
      l rec (noemb (Uᵣ k [k] k<l U⇒*U@([ ⊢U , _ , _ ]))) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl → [k] , k<l }
      l rec (emb p ⊩U) → Σ.map idᶠ (flip <ᵘ-trans p) (rec p ⊩U)
=======
      lemma ∘→ U-elim
    , (λ (l′<l , ⊢Γ) →
        Uᵣ (Uᵣ _ l′<l (id (Uⱼ ⊢Γ))))
    where
    lemma :
      Γ ⊩⟨ l ⟩U U l′ →
      l′ <ᵘ l × ⊢ Γ
    lemma (noemb (Uᵣ _ l′<l U⇒*U)) =
      case U⇒*U→≡ U⇒*U of λ {
        PE.refl →
      l′<l , wfEq (subset* U⇒*U) }
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map ≤ᵘ-step idᶠ (lemma ⊩U)
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map ≤ᵘ-step idᶠ (lemma (emb p ⊩U))
>>>>>>> master

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷U⇔ :
<<<<<<< HEAD
    Γ ⊩⟨ l ⟩ A ∷ U t ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × Γ ⊩⟨ reflect-level [t] ⟩ A ×
    ∃ λ B → Γ ⊢ A :⇒*: B ∷ U t × Type B × Γ ⊢ B ≅ B ∷ U t
  ⊩∷U⇔ =
      (λ (⊩U , ⊩A) →
         lemma _ (U-elim ⊩U) (irrelevanceTerm ⊩U (U-intr (U-elim ⊩U)) ⊩A))
    , (λ ([t] , t<l , ⊩A , _ , A⇒*B , B-type , B≅B) →
          Uᵣ′ _ [t] t<l (idRed:*: (Uⱼ (escapeLevel [t])))
          , Uₜ _ A⇒*B B-type B≅B (⊩<⇔⊩ t<l .proj₂ ⊩A))
    where
    lemma :
      ∀ l → (⊩U : Γ ⊩⟨ l ⟩U U t) →
      Γ ⊩⟨ l ⟩ A ∷ U t / U-intr ⊩U →
      Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × Γ ⊩⟨ reflect-level [t] ⟩ A ×
      ∃ λ B → Γ ⊢ A :⇒*: B ∷ U t × Type B × Γ ⊢ B ≅ B ∷ U t
    lemma = <ᵘ-rec _ λ where
      l rec (noemb (Uᵣ k [k] k<l U⇒*U)) (Uₜ _ A⇒*B B-type B≅B ⊩A) →
        case U⇒*U→≡ U⇒*U of λ where
          PE.refl → [k] , k<l , ⊩<⇔⊩ k<l .proj₁ ⊩A , _ , A⇒*B , B-type , B≅B
      l rec (emb p     ⊩U) ⊩A → Σ.map idᶠ (Σ.map (flip <ᵘ-trans p) idᶠ) (rec p ⊩U (⊩<∷⇔⊩∷′ p .proj₁ ⊩A))
=======
    Γ ⊩⟨ l ⟩ A ∷ U l′ ⇔
    (l′ <ᵘ l × Γ ⊩⟨ l′ ⟩ A ×
     ∃ λ B → Γ ⊢ A ⇒* B ∷ U l′ × Type B × Γ ⊢≅ B ∷ U l′)
  ⊩∷U⇔ =
      (λ (⊩U , ⊩A) →
         lemma (U-elim ⊩U) (irrelevanceTerm ⊩U (U-intr (U-elim ⊩U)) ⊩A))
    , (λ (l′<l , ⊩A , _ , A⇒*B , B-type , B≅B) →
           Uᵣ (Uᵣ _ l′<l (id (Uⱼ (wfEqTerm (subset*Term A⇒*B)))))
         , Uₜ _ A⇒*B B-type B≅B (⊩<⇔⊩ l′<l .proj₂ ⊩A))
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U l′) →
      Γ ⊩⟨ l ⟩ A ∷ U l′ / U-intr ⊩U →
      (l′ <ᵘ l × Γ ⊩⟨ l′ ⟩ A ×
       ∃ λ B → Γ ⊢ A ⇒* B ∷ U l′ × Type B × Γ ⊢≅ B ∷ U l′)
    lemma (noemb (Uᵣ _ l′<l U⇒*U)) (Uₜ _ A⇒*B B-type B≅B ⊩A) =
      case U⇒*U→≡ U⇒*U of λ {
         PE.refl →
      l′<l , ⊩<⇔⊩ l′<l .proj₁ ⊩A , _ , A⇒*B , B-type , B≅B }
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map ≤ᵘ-step idᶠ ∘→ lemma ⊩U
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map ≤ᵘ-step idᶠ ∘→ lemma (emb p ⊩U)
>>>>>>> master

opaque

  -- A variant of ⊩∷U⇔.

  Type→⊩∷U⇔ :
    Type A →
<<<<<<< HEAD
    Γ ⊩⟨ l ⟩ A ∷ U t ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × (Γ ⊩⟨ reflect-level [t] ⟩ A) ×
     Γ ⊢ A ∷ U t ×
     Γ ⊢ A ≅ A ∷ U t
  Type→⊩∷U⇔ {A} {Γ} {l} {t} A-type =
    Γ ⊩⟨ l ⟩ A ∷ U t                                        ⇔⟨ ⊩∷U⇔ ⟩
    (∃ λ [t] → reflect-level [t] <ᵘ l × (Γ ⊩⟨ reflect-level [t] ⟩ A) ×
     ∃ λ B → Γ ⊢ A :⇒*: B ∷ U t × Type B × Γ ⊢ B ≅ B ∷ U t) ⇔⟨
      Σ-cong-⇔ (λ [t] → id⇔ ×-cong-⇔ id⇔ ×-cong-⇔
        ((λ (_ , A⇒*B , _ , B≅B) → case whnfRed*Term (redₜ A⇒*B) (typeWhnf A-type) of λ where
          PE.refl → ⊢t-redₜ A⇒*B , B≅B)
        , λ (⊢A , A≅A) → _ , idRedTerm:*: ⊢A , A-type , A≅A)) ⟩
    (∃ λ [t] → reflect-level [t] <ᵘ l × (Γ ⊩⟨ reflect-level [t] ⟩ A) × Γ ⊢ A ∷ U t × Γ ⊢ A ≅ A ∷ U t) □⇔
=======
    Γ ⊩⟨ l ⟩ A ∷ U l′ ⇔
    (l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A) × Γ ⊢≅ A ∷ U l′)
  Type→⊩∷U⇔ {A} {Γ} {l} {l′} A-type =
    Γ ⊩⟨ l ⟩ A ∷ U l′                                     ⇔⟨ ⊩∷U⇔ ⟩

    l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A) ×
    (∃ λ B → Γ ⊢ A ⇒* B ∷ U l′ × Type B × Γ ⊢≅ B ∷ U l′)  ⇔⟨ id⇔
                                                               ×-cong-⇔
                                                             id⇔
                                                               ×-cong-⇔
                                                             ( (λ (_ , A⇒*B , _ , B≅B) →
                                                                 case whnfRed*Term A⇒*B (typeWhnf A-type) of λ {
                                                                   PE.refl →
                                                                 B≅B })
                                                             , (λ ≅A → _ , id (wf-⊢≡∷ (≅ₜ-eq ≅A) .proj₂ .proj₁) , A-type , ≅A)
                                                             )
                                                           ⟩

    l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A) × Γ ⊢≅ A ∷ U l′               □⇔
>>>>>>> master

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩U≡⇔ :
<<<<<<< HEAD
    Γ ⊩⟨ l ⟩ U t ≡ A ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l ×
    ∃ λ u → Γ ⊢ A :⇒*: U u × Γ ⊩Level t ≡ u ∷Level × Γ ⊩⟨ l ⟩ A
  ⊩U≡⇔ {Γ} {t} {A} =
      (λ (⊩U , ⊩A , U≡A) →
        Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ (Σ.map idᶠ (_, ⊩A)))) $
        lemma _ (U-elim ⊩U) (irrelevanceEq ⊩U (U-intr (U-elim ⊩U)) U≡A))
      , λ ([t] , t<l , u , A⇒*U@([ _ , ⊢U , _ ]) , t≡u , ⊩A) →
        Uᵣ′ _ [t] t<l (idRed:*: (Uⱼ (escapeLevel [t])))
        , ⊩A
        , U₌ u A⇒*U t≡u
    where
    lemma :
      ∀ l → (⊩U : Γ ⊩⟨ l ⟩U U t) →
      Γ ⊩⟨ l ⟩ U t ≡ A / U-intr ⊩U →
      Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × ∃ λ u → Γ ⊢ A :⇒*: U u × Γ ⊩Level t ≡ u ∷Level
    lemma = <ᵘ-rec _ λ where
      l rec (noemb (Uᵣ k [k] k< U⇒*U)) (U₌ k′ D k≡k′) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl → [k] , k< , k′ , D , k≡k′ }
      l rec (emb p ⊩U) A≡U → Σ.map idᶠ (Σ.map (flip <ᵘ-trans p) idᶠ) (rec p ⊩U (⊩<≡⇔⊩≡′ p .proj₁ A≡U))
=======
    Γ ⊩⟨ l ⟩ U l′ ≡ A ⇔
    (l′ <ᵘ l × Γ ⊢ A ⇒* U l′)
  ⊩U≡⇔ =
      (λ (⊩U , _ , U≡A) →
         lemma (U-elim ⊩U)
           (irrelevanceEq ⊩U (U-intr (U-elim ⊩U)) U≡A))
    , (λ (p , A⇒*U) →
         let _ , ⊢U = wf-⊢≡ (subset* A⇒*U) in
           Uᵣ (Uᵣ _ p (id ⊢U))
         , wf-⊩≡ (⊩-⇐* A⇒*U (⊩U⇔ .proj₂ (p , wf ⊢U))) .proj₁
         , A⇒*U)
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U l′) →
      Γ ⊩⟨ l ⟩ U l′ ≡ A / U-intr ⊩U →
      l′ <ᵘ l × Γ ⊢ A ⇒* U l′
    lemma (noemb (Uᵣ _ p U⇒*U)) A≡U =
      case U⇒*U→≡ U⇒*U of λ {
        PE.refl →
      p , A≡U }
    lemma (emb ≤ᵘ-refl ⊩U) A≡U =
      Σ.map ≤ᵘ-step idᶠ (lemma ⊩U A≡U)
    lemma (emb (≤ᵘ-step p) ⊩U) A≡U =
      Σ.map ≤ᵘ-step idᶠ (lemma (emb p ⊩U) A≡U)
>>>>>>> master

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷U⇔ :
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × Γ ⊩⟨ reflect-level [t] ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
<<<<<<< HEAD
     Γ ⊢ A :⇒*: A′ ∷ U t ×
     Γ ⊢ B :⇒*: B′ ∷ U t ×
=======
     Γ ⊢ A ⇒* A′ ∷ U l′ ×
     Γ ⊢ B ⇒* B′ ∷ U l′ ×
>>>>>>> master
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U t
  ⊩≡∷U⇔ =
      (λ (⊩U , _ , _ , A≡B) →
          lemma (U-elim ⊩U)
            (irrelevanceEqTerm ⊩U (U-intr (U-elim ⊩U)) A≡B))
    , (λ ([t] , t<l , (⊩A , ⊩B , A≡B) , _ , _ ,
          A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′) →
<<<<<<< HEAD
         let ⊩A = ⊩<⇔⊩ t<l .proj₂ ⊩A
             ⊩B = ⊩<⇔⊩ t<l .proj₂ ⊩B
         in
           Uᵣ′ _ [t] t<l (idRed:*: (Uⱼ (escapeLevel [t])))
         , Uₜ _ A⇒*A′ A′-type (≅ₜ-trans A′≅B′ (≅ₜ-sym A′≅B′)) ⊩A
         , Uₜ _ B⇒*B′ B′-type (≅ₜ-trans (≅ₜ-sym A′≅B′) A′≅B′) ⊩B
=======
         let ⊩A        = ⊩<⇔⊩ l′<l .proj₂ ⊩A
             ⊩B        = ⊩<⇔⊩ l′<l .proj₂ ⊩B
             ≅A′ , ≅B′ = wf-⊢≅∷ A′≅B′
         in
           Uᵣ (Uᵣ _ l′<l (id (Uⱼ (wfEqTerm (subset*Term A⇒*A′)))))
         , Uₜ _ A⇒*A′ A′-type ≅A′ ⊩A
         , Uₜ _ B⇒*B′ B′-type ≅B′ ⊩B
>>>>>>> master
         , Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B
             (⊩<≡⇔⊩≡′ t<l .proj₂ A≡B))
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U t) →
      Γ ⊩⟨ l ⟩ A ≡ B ∷ U t / U-intr ⊩U →
      Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × Γ ⊩⟨ reflect-level [t] ⟩ A ≡ B ×
      ∃₂ λ A′ B′ →
<<<<<<< HEAD
      Γ ⊢ A :⇒*: A′ ∷ U t ×
      Γ ⊢ B :⇒*: B′ ∷ U t ×
=======
      Γ ⊢ A ⇒* A′ ∷ U l′ ×
      Γ ⊢ B ⇒* B′ ∷ U l′ ×
>>>>>>> master
      Type A′ ×
      Type B′ ×
      Γ ⊢ A′ ≅ B′ ∷ U t
    lemma
      (noemb (Uᵣ k [k] k<l U⇒*U))
      (Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B) =
        case U⇒*U→≡ U⇒*U of λ where
          PE.refl →
              [k] , k<l
            , (⊩<⇔⊩ k<l .proj₁ ⊩A , ⊩<⇔⊩ k<l .proj₁ ⊩B , ⊩<≡⇔⊩≡ k<l .proj₁ A≡B)
            , _ , _ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′
    lemma (emb p     ⊩U) = {!   !}
    -- lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map idᶠ (Σ.map ≤ᵘ-step idᶠ) ∘→ lemma ⊩U
    -- lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map idᶠ (Σ.map ≤ᵘ-step idᶠ) ∘→ lemma (emb p ⊩U)

opaque

  -- A variant of ⊩≡∷U⇔.

  Type→⊩≡∷U⇔ :
    Type A →
    Type B →
<<<<<<< HEAD
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t ⇔
    Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × (Γ ⊩⟨ reflect-level [t] ⟩ A ≡ B) ×
     Γ ⊢ A ∷ U t ×
     Γ ⊢ B ∷ U t ×
     Γ ⊢ A ≅ B ∷ U t
  Type→⊩≡∷U⇔ {A} {B} {Γ} {l} {t} A-type B-type =
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U t          ⇔⟨ ⊩≡∷U⇔ ⟩
    (Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × Γ ⊩⟨ reflect-level [t] ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A :⇒*: A′ ∷ U t ×
     Γ ⊢ B :⇒*: B′ ∷ U t ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U t)
      ⇔⟨ Σ-cong-⇔ (λ [t] → id⇔ ×-cong-⇔ id⇔ ×-cong-⇔
        ( (λ (A′ , B′ , A⇒*A′ , B⇒*B′ , _ , _ , A′≅B′) →
          case whnfRed*Term (redₜ A⇒*A′) (typeWhnf A-type) of λ {
            PE.refl →
          case whnfRed*Term (redₜ B⇒*B′) (typeWhnf B-type) of λ {
            PE.refl →
          ⊢t-redₜ A⇒*A′ , ⊢t-redₜ B⇒*B′ , A′≅B′ } })
        , λ (⊢A , ⊢B , A≅B) →
          _ , _ , idRedTerm:*: ⊢A , idRedTerm:*: ⊢B , A-type , B-type , A≅B)) ⟩
    (Σ (Γ ⊩Level t ∷Level) λ [t] → reflect-level [t] <ᵘ l × (Γ ⊩⟨ reflect-level [t] ⟩ A ≡ B) ×
     Γ ⊢ A ∷ U t ×
     Γ ⊢ B ∷ U t ×
     Γ ⊢ A ≅ B ∷ U t) □⇔
=======
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U l′ ⇔
    (l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A ≡ B) × Γ ⊢ A ≅ B ∷ U l′)
  Type→⊩≡∷U⇔ {A} {B} {Γ} {l} {l′} A-type B-type =
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U l′          ⇔⟨ ⊩≡∷U⇔ ⟩

    l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A ≡ B) ×
    (∃₂ λ A′ B′ →
     Γ ⊢ A ⇒* A′ ∷ U l′ ×
     Γ ⊢ B ⇒* B′ ∷ U l′ ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U l′)           ⇔⟨ (λ (l′<l , A≡B , A′ , B′ , DA , DB , A′-type , B′-type , A′≅B′) →
                                         case whnfRed*Term DA (typeWhnf A-type) of λ {
                                           PE.refl →
                                         case whnfRed*Term DB (typeWhnf B-type) of λ {
                                           PE.refl →
                                         (l′<l , A≡B , A′≅B′)}})
                                    , (λ (l′<l , A≡B , A≅B) →
                                         let _ , ⊢A , ⊢B = wf-⊢≡∷ (≅ₜ-eq A≅B) in
                                           l′<l , A≡B , _ , _ , id ⊢A , id ⊢B
                                         , A-type , B-type , A≅B)
                                    ⟩
    l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A ≡ B) ×
    Γ ⊢ A ≅ B ∷ U l′               □⇔
>>>>>>> master

------------------------------------------------------------------------
-- Validity

opaque

  -- Validity of U.

  ⊩ᵛU : Γ ⊩ᵛ t ∷ Level → Γ ⊩ᵛ U t
  ⊩ᵛU {Γ} {t} ⊩t =
    ⊩ᵛ⇔ .proj₂
<<<<<<< HEAD
      ( wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
      , λ {_} {Δ} {σ₁} {σ₂} →
          λ σ₁≡σ₂ →
            let (⊩t[σ₁] , ⊩t[σ₂] , ⊩t≡) = ⊩≡∷Level⇔ .proj₁ (⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂ .proj₂)
                ⊢Δ = escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₁
            in
              ω+0 , (
              ⊩U≡⇔ .proj₂ $
                ⊩t[σ₁]
              , <ᵘ-ω
              , t [ σ₂ ]
              , idRed:*: (Uⱼ (escapeLevel ⊩t[σ₂]))
              , ⊩t≡
              , ⊩U⇔ .proj₂ (⊩t[σ₂] , <ᵘ-ω))
=======
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ            →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                         →⟨ (λ ⊢Δ → ≤ᵘ-refl , id (Uⱼ ⊢Δ)) ⟩
          l <ᵘ 1+ l × Δ ⊢ U l ⇒* U l  ⇔˘⟨ ⊩U≡⇔ ⟩→
          Δ ⊩⟨ 1+ l ⟩ U l ≡ U l       □
>>>>>>> master
      )

opaque

  -- Validity of U, seen as a term former.

  ⊩ᵛU∷U : Γ ⊩ᵛ t ∷ Level → Γ ⊩ᵛ U t ∷ U (sucᵘ t)
  ⊩ᵛU∷U {Γ} {t} ⊩t =
    ⊩ᵛ∷⇔ .proj₂
<<<<<<< HEAD
      ( ⊩ᵛU (sucᵘᵛ ⊩t)
      , λ {_} {Δ} {σ₁} {σ₂} →
          -- Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                                         →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩

          -- ⊢ Δ                                                      →⟨ (λ ⊢Δ → ≤ᵘ-refl , ⊩U⇔ .proj₂ (≤ᵘ-refl , ⊢Δ) , Uⱼ ⊢Δ , ≅-Urefl ⊢Δ) ⟩

          -- 1+ l <ᵘ 2+ l × (Δ ⊩⟨ 1+ l ⟩ U l) × Δ ⊢ U l ∷ U (1+ l) ×
          -- Δ ⊢ U l ≅ U l ∷ U (1+ l)                                 →⟨ Type→⊩∷U⇔ Uₙ .proj₂ ⟩

          -- Δ ⊩⟨ 2+ l ⟩ U l ∷ U (1+ l)                               →⟨ refl-⊩≡∷ ⟩

          -- Δ ⊩⟨ 2+ l ⟩ U l ≡ U l ∷ U (1+ l)                         □
          λ σ₁≡σ₂ →
            let ⊩t[σ₁]≡t[σ₂] = ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂ .proj₂
                (⊩t[σ₁] , ⊩t[σ₂] , ⊩t≡) = ⊩≡∷Level⇔ .proj₁ ⊩t[σ₁]≡t[σ₂]
                ⊩1+t[σ₁] : Δ ⊩Level sucᵘ (t [ σ₁ ]) ∷Level
                ⊩1+t[σ₁] = ⊩Level-sucᵘ ⊩t[σ₁]
            in
              ω+0 , (
              Type→⊩≡∷U⇔ Uₙ Uₙ .proj₂ $
                ⊩1+t[σ₁]
              , <ᵘ-ω
              , ⊩U≡⇔ .proj₂
                ( ⊩t[σ₁]
                , reflect-level-suc ⊩t[σ₁]
                , t [ σ₂ ]
                , idRed:*: (Uⱼ (escapeLevel ⊩t[σ₂]))
                , ⊩t≡
                , ⊩U⇔ .proj₂ (⊩t[σ₂] , PE.subst (_<ᵘ _) {!   !} (reflect-level-suc ⊩t[σ₁]))
                )
              , Uⱼ (escapeLevel ⊩t[σ₁])
              , conv (Uⱼ (escapeLevel ⊩t[σ₂])) (U-cong (sucᵘ-cong (sym (≅ₜ-eq (escapeLevelEq ⊩t≡)))))
              , ≅ₜ-U-cong (escapeLevelEq ⊩t≡))
=======
      ( ⊩ᵛU ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                                        →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩

          ⊢ Δ                                                     →⟨ (λ ⊢Δ → ≤ᵘ-refl , ⊩U⇔ .proj₂ (≤ᵘ-refl , ⊢Δ) , ≅-Urefl ⊢Δ) ⟩

          1+ l <ᵘ 2+ l × (Δ ⊩⟨ 1+ l ⟩ U l) × Δ ⊢≅ U l ∷ U (1+ l)  →⟨ Type→⊩∷U⇔ Uₙ .proj₂ ⟩

          Δ ⊩⟨ 2+ l ⟩ U l ∷ U (1+ l)                              →⟨ refl-⊩≡∷ ⟩

          Δ ⊩⟨ 2+ l ⟩ U l ≡ U l ∷ U (1+ l)                        □
>>>>>>> master
      )

opaque

  -- Validity of one of the typing rules called univ.

<<<<<<< HEAD
  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ A ∷ U t →
    Γ ⊩ᵛ A
  ⊩ᵛ∷U→⊩ᵛ ⊩A∷U =
    case ⊩ᵛ∷⇔ .proj₁ ⊩A∷U of λ
      (⊩U , A≡A∷U) →
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , λ σ₁≡σ₂ →
        let ([t] , t<l , A≡A , _) = ⊩≡∷U⇔ .proj₁ (A≡A∷U σ₁≡σ₂ .proj₂) in
        _ , emb-⊩≡ (<ᵘ→≤ᵘ t<l) A≡A
      )

opaque

  -- Validity of another of the typing rules called univ.

=======
>>>>>>> master
  ⊩ᵛ≡∷U→⊩ᵛ≡ :
    Γ ⊩ᵛ A ≡ B ∷ U t →
    Γ ⊩ᵛ A ≡ B
  ⊩ᵛ≡∷U→⊩ᵛ≡ A≡B∷U =
    case ⊩ᵛ≡∷⇔ .proj₁ A≡B∷U of λ
      (⊩U , A≡B∷U) →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , λ σ₁≡σ₂ →
        let ([t] , t<l , A≡B , _) = ⊩≡∷U⇔ .proj₁ (A≡B∷U σ₁≡σ₂ .proj₂) in
        _ , emb-⊩≡ (<ᵘ→≤ᵘ t<l) A≡B
      )

opaque

  -- Validity of another of the typing rules called univ.

  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U l′ →
    Γ ⊩ᵛ⟨ l′ ⟩ A
  ⊩ᵛ∷U→⊩ᵛ = ⊩ᵛ⇔⊩ᵛ≡ .proj₂ ∘→ ⊩ᵛ≡∷U→⊩ᵛ≡ ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁
