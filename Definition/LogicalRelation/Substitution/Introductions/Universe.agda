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
open import Definition.Untyped.Neutral M type-variant
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R

open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product as Σ
open import Tools.Empty
import Tools.PropositionalEquality as PE

private
  variable
    n    : Nat
    Γ    : Con Term n
    A B  : Term n
    l l′ : Universe-level
    k    : LogRelKit

------------------------------------------------------------------------
-- Some characterisation lemmas

private

  -- A lemma used below.

  U⇒*U→≡ : Γ ⊢ U l ⇒* U l′ → l PE.≡ l′
  U⇒*U→≡ {Γ} {l} {l′} =
    Γ ⊢ U l ⇒* U l′  →⟨ flip whnfRed* Uₙ ⟩
    U l PE.≡ U l′    →⟨ (λ { PE.refl → PE.refl }) ⟩
    l PE.≡ l′        □

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩U⇔ :
    Γ ⊩⟨ l ⟩ U l′ ⇔
    (l′ <ᵘ l × ⊢ Γ)
  ⊩U⇔ =
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

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷U⇔ :
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

opaque

  -- A variant of ⊩∷U⇔.

  Type→⊩∷U⇔ :
    Type A →
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

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩U≡⇔ :
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

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷U⇔ :
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U l′ ⇔
    (l′ <ᵘ l × Γ ⊩⟨ l′ ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A ⇒* A′ ∷ U l′ ×
     Γ ⊢ B ⇒* B′ ∷ U l′ ×
     Type A′ ×
     Type B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U l′)
  ⊩≡∷U⇔ =
      (λ (⊩U , _ , _ , A≡B) →
          lemma (U-elim ⊩U)
            (irrelevanceEqTerm ⊩U (U-intr (U-elim ⊩U)) A≡B))
    , (λ (l′<l , (⊩A , ⊩B , A≡B) , _ , _ ,
          A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′) →
         let ⊩A        = ⊩<⇔⊩ l′<l .proj₂ ⊩A
             ⊩B        = ⊩<⇔⊩ l′<l .proj₂ ⊩B
             ≅A′ , ≅B′ = wf-⊢≅∷ A′≅B′
         in
           Uᵣ (Uᵣ _ l′<l (id (Uⱼ (wfEqTerm (subset*Term A⇒*A′)))))
         , Uₜ _ A⇒*A′ A′-type ≅A′ ⊩A
         , Uₜ _ B⇒*B′ B′-type ≅B′ ⊩B
         , Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B
             (⊩<≡⇔⊩≡′ l′<l .proj₂ A≡B))
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U l′) →
      Γ ⊩⟨ l ⟩ A ≡ B ∷ U l′ / U-intr ⊩U →
      l′ <ᵘ l × Γ ⊩⟨ l′ ⟩ A ≡ B ×
      ∃₂ λ A′ B′ →
      Γ ⊢ A ⇒* A′ ∷ U l′ ×
      Γ ⊢ B ⇒* B′ ∷ U l′ ×
      Type A′ ×
      Type B′ ×
      Γ ⊢ A′ ≅ B′ ∷ U l′
    lemma
      (noemb (Uᵣ _ l′<l U⇒*U))
      (Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B) =
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
          l′<l
        , ( ⊩<⇔⊩ l′<l .proj₁ ⊩A
          , ⊩<⇔⊩ l′<l .proj₁ ⊩B
          , ⊩<≡⇔⊩≡ l′<l .proj₁ A≡B
          )
        , _ , _ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′ }
    lemma (emb ≤ᵘ-refl     ⊩U) = Σ.map ≤ᵘ-step idᶠ ∘→ lemma ⊩U
    lemma (emb (≤ᵘ-step p) ⊩U) = Σ.map ≤ᵘ-step idᶠ ∘→ lemma (emb p ⊩U)

opaque

  -- A variant of ⊩≡∷U⇔.

  Type→⊩≡∷U⇔ :
    Type A →
    Type B →
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

------------------------------------------------------------------------
-- Validity

opaque

  -- Validity of U.

  ⊩ᵛU : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ 1+ l ⟩ U l
  ⊩ᵛU {Γ} {l} ⊩Γ =
    ⊩ᵛ⇔ .proj₂
      ( ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ            →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ⊢ Δ                         →⟨ (λ ⊢Δ → ≤ᵘ-refl , id (Uⱼ ⊢Δ)) ⟩
          l <ᵘ 1+ l × Δ ⊢ U l ⇒* U l  ⇔˘⟨ ⊩U≡⇔ ⟩→
          Δ ⊩⟨ 1+ l ⟩ U l ≡ U l       □
      )

opaque

  -- Validity of U, seen as a term former.

  ⊩ᵛU∷U : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ 2+ l ⟩ U l ∷ U (1+ l)
  ⊩ᵛU∷U {Γ} {l} ⊩Γ =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛU ⊩Γ
      , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                                        →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩

          ⊢ Δ                                                     →⟨ (λ ⊢Δ → ≤ᵘ-refl , ⊩U⇔ .proj₂ (≤ᵘ-refl , ⊢Δ) , ≅-Urefl ⊢Δ) ⟩

          1+ l <ᵘ 2+ l × (Δ ⊩⟨ 1+ l ⟩ U l) × Δ ⊢≅ U l ∷ U (1+ l)  →⟨ Type→⊩∷U⇔ Uₙ .proj₂ ⟩

          Δ ⊩⟨ 2+ l ⟩ U l ∷ U (1+ l)                              →⟨ refl-⊩≡∷ ⟩

          Δ ⊩⟨ 2+ l ⟩ U l ≡ U l ∷ U (1+ l)                        □
      )

opaque

  -- Validity of one of the typing rules called univ.

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

opaque

  -- Validity of another of the typing rules called univ.

  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U l′ →
    Γ ⊩ᵛ⟨ l′ ⟩ A
  ⊩ᵛ∷U→⊩ᵛ = ⊩ᵛ⇔⊩ᵛ≡ .proj₂ ∘→ ⊩ᵛ≡∷U→⊩ᵛ≡ ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁
