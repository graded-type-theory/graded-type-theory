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
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Hidden R {{eqrel}}
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Introductions.Level R

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

  U⇒*U→≡ : Γ ⊢ U t :⇒*: U u → t PE.≡ u
  U⇒*U→≡ {Γ} {t} {u} =
    Γ ⊢ U t :⇒*: U u →⟨ red ⟩
    Γ ⊢ U t ⇒* U u   →⟨ flip whnfRed* Uₙ ⟩
    U t PE.≡ U u     →⟨ (λ { PE.refl → PE.refl }) ⟩
    t PE.≡ u         □

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩U⇔ :
    ([t] : Γ ⊩Level t ∷Level) →
    Γ ⊩⟨ l ⟩ U t ⇔
    (reflect-level [t] <ᵘ l × ⊢ Γ)
  ⊩U⇔ {Γ} {t} [t]@(Levelₜ n [ ⊢t , _ , _ ] n≡n prop) =
      lemma ∘→ U-elim
    , (λ (k<l , ⊢Γ) →
        Uᵣ′ _ [t] k<l (idRed:*: (Uⱼ ⊢t)))
    where
    lemma :
      Γ ⊩⟨ l ⟩U U t →
      reflect-level [t] <ᵘ l × ⊢ Γ
    lemma (noemb (Uᵣ k [k] k<l U⇒*U@([ ⊢U , _ , _ ]))) =
      case U⇒*U→≡ U⇒*U of λ {
        PE.refl →
      PE.subst (_<ᵘ _) (reflect-level-cong [k] [t] PE.refl) k<l , wf ⊢U }
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map ≤ᵘ-step idᶠ (lemma ⊩U)
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map ≤ᵘ-step idᶠ (lemma (emb p ⊩U))

{-
opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷U⇔ :
    Γ ⊩⟨ l ⟩ A ∷ U l′ ⇔
    (l′ <ᵘ l × Γ ⊩⟨ l′ ⟩ A ×
     ∃ λ B → Γ ⊢ A :⇒*: B ∷ U l′ × Type B × Γ ⊢ B ≅ B ∷ U l′)
  ⊩∷U⇔ =
      (λ (⊩U , ⊩A) →
         lemma (U-elim ⊩U) (irrelevanceTerm ⊩U (U-intr (U-elim ⊩U)) ⊩A))
    , (λ (l′<l , ⊩A , _ , A⇒*B , B-type , B≅B) →
           Uᵣ (Uᵣ _ l′<l (idRed:*: (Uⱼ (wfTerm (⊢t-redₜ A⇒*B)))))
         , Uₜ _ A⇒*B B-type B≅B (⊩<⇔⊩ l′<l .proj₂ ⊩A))
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U l′) →
      Γ ⊩⟨ l ⟩ A ∷ U l′ / U-intr ⊩U →
      (l′ <ᵘ l × Γ ⊩⟨ l′ ⟩ A ×
       ∃ λ B → Γ ⊢ A :⇒*: B ∷ U l′ × Type B × Γ ⊢ B ≅ B ∷ U l′)
    lemma (noemb (Uᵣ _ l′<l U⇒*U)) (Uₜ _ A⇒*B B-type B≅B ⊩A) =
      -- case U⇒*U→≡ U⇒*U of λ {
      --    PE.refl →
      -- l′<l , ⊩<⇔⊩ l′<l .proj₁ ⊩A , _ , A⇒*B , B-type , B≅B }
      ?
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map ≤ᵘ-step idᶠ ∘→ lemma ⊩U
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map ≤ᵘ-step idᶠ ∘→ lemma (emb p ⊩U)

opaque

  -- A variant of ⊩∷U⇔.

  Type→⊩∷U⇔ :
    Type A →
    Γ ⊩⟨ l ⟩ A ∷ U l′ ⇔
    (l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A) ×
     Γ ⊢ A ∷ U l′ ×
     Γ ⊢ A ≅ A ∷ U l′)
  Type→⊩∷U⇔ {A} {Γ} {l} {l′} A-type =
    Γ ⊩⟨ l ⟩ A ∷ U l′                                          ⇔⟨ ⊩∷U⇔ ⟩

    l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A) ×
    (∃ λ B → Γ ⊢ A :⇒*: B ∷ U l′ × Type B × Γ ⊢ B ≅ B ∷ U l′)  ⇔⟨ id⇔
                                                                    ×-cong-⇔
                                                                  id⇔
                                                                    ×-cong-⇔
                                                                  ( (λ (_ , A⇒*B , _ , B≅B) →
                                                                      case whnfRed*Term (redₜ A⇒*B) (typeWhnf A-type) of λ {
                                                                        PE.refl →
                                                                      ⊢t-redₜ A⇒*B , B≅B })
                                                                  , (λ (⊢A , A≅A) → _ , idRedTerm:*: ⊢A , A-type , A≅A)
                                                                  )
                                                                ⟩

    l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A) × Γ ⊢ A ∷ U l′ × Γ ⊢ A ≅ A ∷ U l′  □⇔
-}

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩U≡⇔ :
    ([t] : Γ ⊩Level t ∷Level) →
    Γ ⊩⟨ l ⟩ U t ≡ A ⇔
    (reflect-level [t] <ᵘ l × ∃ λ u → Γ ⊢ A :⇒*: U u × Γ ⊩Level t ≡ u ∷Level × Γ ⊩⟨ l ⟩ A)
  ⊩U≡⇔ {Γ} {t} {A} [t] =
      (λ (⊩U , ⊩A , U≡A) →
         Σ.map idᶠ (_, ⊩A) $
         lemma (U-elim ⊩U)
           (irrelevanceEq ⊩U (U-intr (U-elim ⊩U)) U≡A))
      , λ (p , A⇒*U@([ _ , ⊢U , _ ]) , ⊩A) → Uᵣ′ _ [t] p (idRed:*: ⊢U) , ⊩A , U₌ t A⇒*U (reflLevel [t])
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U t) →
      Γ ⊩⟨ l ⟩ U t ≡ A / U-intr ⊩U →
      reflect-level [t] <ᵘ l × Γ ⊢ A :⇒*: U t
    lemma (noemb (Uᵣ k [k] k< U⇒*U)) (U₌ k′ D k≡k′) =
      case U⇒*U→≡ U⇒*U of λ {
        PE.refl →
      -- PE.subst (_<ᵘ _) (reflect-level-cong [k] [t] PE.refl) k< , A≡U }
      {!   !} , {! A≡U  !} }
    lemma (emb ≤ᵘ-refl ⊩U) A≡U =
      Σ.map ≤ᵘ-step idᶠ (lemma ⊩U A≡U)
    lemma (emb (≤ᵘ-step p) ⊩U) A≡U =
      Σ.map ≤ᵘ-step idᶠ (lemma (emb p ⊩U) A≡U)

{-
opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷U⇔ :
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U l′ ⇔
    (l′ <ᵘ l × Γ ⊩⟨ l′ ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A :⇒*: A′ ∷ U l′ ×
     Γ ⊢ B :⇒*: B′ ∷ U l′ ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U l′)
  ⊩≡∷U⇔ =
      (λ (⊩U , _ , _ , A≡B) →
          lemma (U-elim ⊩U)
            (irrelevanceEqTerm ⊩U (U-intr (U-elim ⊩U)) A≡B))
    , (λ (l′<l , (⊩A , ⊩B , A≡B) , _ , _ ,
          A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′) →
         let ⊩A = ⊩<⇔⊩ l′<l .proj₂ ⊩A
             ⊩B = ⊩<⇔⊩ l′<l .proj₂ ⊩B
         in
           Uᵣ (Uᵣ _ l′<l (idRed:*: (Uⱼ (wfTerm (⊢t-redₜ A⇒*A′)))))
         , Uₜ _ A⇒*A′ A′-type (≅ₜ-trans A′≅B′ (≅ₜ-sym A′≅B′)) ⊩A
         , Uₜ _ B⇒*B′ B′-type (≅ₜ-trans (≅ₜ-sym A′≅B′) A′≅B′) ⊩B
         , Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B
             (⊩<≡⇔⊩≡′ l′<l .proj₂ A≡B))
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U l′) →
      Γ ⊩⟨ l ⟩ A ≡ B ∷ U l′ / U-intr ⊩U →
      l′ <ᵘ l × Γ ⊩⟨ l′ ⟩ A ≡ B ×
      ∃₂ λ A′ B′ →
      Γ ⊢ A :⇒*: A′ ∷ U l′ ×
      Γ ⊢ B :⇒*: B′ ∷ U l′ ×
      Type A′ ×
      Type B′ ×
      Γ ⊢ A′ ≅ B′ ∷ U l′
    lemma
      (noemb (Uᵣ _ l′<l U⇒*U))
      (Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B) =
        -- case U⇒*U→≡ U⇒*U of λ {
        --   PE.refl →
        --   l′<l
        -- , ( ⊩<⇔⊩ l′<l .proj₁ ⊩A
        --   , ⊩<⇔⊩ l′<l .proj₁ ⊩B
        --   , ⊩<≡⇔⊩≡ l′<l .proj₁ A≡B
        --   )
        -- , _ , _ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′ }
        ?
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map ≤ᵘ-step idᶠ ∘→ lemma ⊩U
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map ≤ᵘ-step idᶠ ∘→ lemma (emb p ⊩U)

opaque

  -- A variant of ⊩≡∷U⇔.

  Type→⊩≡∷U⇔ :
    Type A →
    Type B →
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U l′ ⇔
    (l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A ≡ B) ×
     Γ ⊢ A ∷ U l′ ×
     Γ ⊢ B ∷ U l′ ×
     Γ ⊢ A ≅ B ∷ U l′)
  Type→⊩≡∷U⇔ {A} {B} {Γ} {l} {l′} A-type B-type =
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U l′          ⇔⟨ ⊩≡∷U⇔ ⟩

    l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A ≡ B) ×
    (∃₂ λ A′ B′ →
     Γ ⊢ A :⇒*: A′ ∷ U l′ ×
     Γ ⊢ B :⇒*: B′ ∷ U l′ ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U l′)           ⇔⟨ (λ (l′<l , A≡B , A′ , B′ , DA , DB , A′-type , B′-type , A′≅B′) →
                                         case whnfRed*Term (redₜ DA) (typeWhnf A-type) of λ {
                                           PE.refl →
                                         case whnfRed*Term (redₜ DB) (typeWhnf B-type) of λ {
                                           PE.refl →
                                         (l′<l , A≡B , ⊢t-redₜ DA , ⊢t-redₜ DB , A′≅B′)}})
                                    , (λ (l′<l , A≡B , ⊢A , ⊢B , A≅B) →
                                           l′<l , A≡B , _ , _
                                         , idRedTerm:*: ⊢A , idRedTerm:*: ⊢B
                                         , A-type , B-type , A≅B)
                                    ⟩
    l′ <ᵘ l × (Γ ⊩⟨ l′ ⟩ A ≡ B) ×
    Γ ⊢ A ∷ U l′ ×
    Γ ⊢ B ∷ U l′ ×
    Γ ⊢ A ≅ B ∷ U l′               □⇔
-}

------------------------------------------------------------------------
-- Validity

opaque

  -- Validity of U.

  ⊩ᵛU : (⊩t : Γ ⊩ᵛ⟨ l ⟩ t ∷ Level) → Γ ⊩ᵛ⟨ 1+ {!   !} ⟩ U t
  ⊩ᵛU {Γ} {t} ⊩t =
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
      , λ {_} {Δ} {σ₁} {σ₂} →
          λ σ₁≡σ₂ →
            let (⊩t[σ₁] , ⊩t[σ₂] , ⊩t≡) = ⊩≡∷Level⇔ .proj₁ (⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂)
                ⊢Δ = escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₁
            in
              -- ⊩U≡⇔ ⊩t[σ₁] .proj₂ $
              -- {!   !}
              -- , {!   !}
              -- , ⊩U⇔ ⊩t[σ₂] .proj₂ ({!   !} , ⊢Δ)
              {!   !}
      )

{-
opaque

  -- Validity of U, seen as a term former.

  ⊩ᵛU∷U : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ 2+ l ⟩ U l ∷ U (1+ l)
  ⊩ᵛU∷U {Γ} {l} ⊩Γ =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛU ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                                         →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩

          ⊢ Δ                                                      →⟨ (λ ⊢Δ → ≤ᵘ-refl , ⊩U⇔ .proj₂ (≤ᵘ-refl , ⊢Δ) , Uⱼ ⊢Δ , ≅-Urefl ⊢Δ) ⟩

          1+ l <ᵘ 2+ l × (Δ ⊩⟨ 1+ l ⟩ U l) × Δ ⊢ U l ∷ U (1+ l) ×
          Δ ⊢ U l ≅ U l ∷ U (1+ l)                                 →⟨ Type→⊩∷U⇔ Uₙ .proj₂ ⟩

          Δ ⊩⟨ 2+ l ⟩ U l ∷ U (1+ l)                               →⟨ refl-⊩≡∷ ⟩

          Δ ⊩⟨ 2+ l ⟩ U l ≡ U l ∷ U (1+ l)                         □
      )

opaque

  -- Validity of one of the typing rules called univ.

  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U l′ →
    Γ ⊩ᵛ⟨ l′ ⟩ A
  ⊩ᵛ∷U→⊩ᵛ ⊩A∷U =
    case ⊩ᵛ∷⇔ .proj₁ ⊩A∷U of λ
      (⊩U , A≡A∷U) →
    emb-⊩ᵛ ≤ᵘ-refl $
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , proj₁ ∘→ proj₂ ∘→ ⊩≡∷U⇔ .proj₁ ∘→ A≡A∷U
      )

opaque

  -- Validity of another of the typing rules called univ.

  ⊩ᵛ≡∷U→⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B ∷ U l′ →
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B
  ⊩ᵛ≡∷U→⊩ᵛ≡ A≡B∷U =
    case ⊩ᵛ≡∷⇔ .proj₁ A≡B∷U of λ
      (⊩U , A≡B∷U) →
    ⊩ᵛ≡⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , proj₁ ∘→ proj₂ ∘→ ⊩≡∷U⇔ .proj₁ ∘→ A≡B∷U
      )
-}
