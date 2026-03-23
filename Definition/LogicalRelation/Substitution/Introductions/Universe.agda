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
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R
open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Hidden R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Irrelevance R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties R ⦃ eqrel ⦄
import Definition.LogicalRelation.Hidden.Restricted R as R
open import Definition.LogicalRelation.ShapeView R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Substitution.Introductions.Level R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Nat using (Nat; 1+; 2+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Sum

private variable
  m n           : Nat
  Γ             : Cons m n
  A B t t′ u u′ : Term n
  l l₁ l₂       : Lvl _
  ℓ             : Universe-level
  k             : LogRelKit

------------------------------------------------------------------------
-- Some characterisation lemmas

private

  -- A lemma used below.

  U⇒*U→≡ : Γ ⊢ U l₁ ⇒* U l₂ → l₁ PE.≡ l₂
  U⇒*U→≡ {Γ} {l₁} {l₂} =
    Γ ⊢ U l₁ ⇒* U l₂  →⟨ flip whnfRed* Uₙ ⟩
    U l₁ PE.≡ U l₂    →⟨ (λ { PE.refl → PE.refl }) ⟩
    l₁ PE.≡ l₂        □

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩U⇔ :
    Γ ⊩⟨ ℓ ⟩ U l ⇔
    (∃ λ (⊩l : Γ ⊩Level l ∷Level) → ↑ᵘ ⊩l <ᵘ ℓ)
  ⊩U⇔ =
      (λ ⊩U →
        case U-view ⊩U of λ {
          (Uᵣ (Uᵣ _ _ t<l U⇒*U)) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
        _ , t<l }})
    , (λ (⊩l , l<ℓ) →
        Uᵣ (Uᵣ _ ⊩l l<ℓ (id (⊢U (escapeLevel ⊩l)))))

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩U≡⇔ :
    Γ ⊩⟨ ℓ ⟩ U l ≡ A ⇔
    (∃ λ (⊩l : Γ ⊩Level l ∷Level) →
       ↑ᵘ ⊩l <ᵘ ℓ × ∃ λ l′ → Γ ⊢ A ⇒* U l′ × Γ ⊩Level l ≡ l′ ∷Level)
  ⊩U≡⇔ {ℓ} =
      (λ (⊩U , _ , U≡A) →
        case U-view ⊩U of λ {
          (Uᵣ (Uᵣ _ ⊩l l<ℓ U⇒*U)) →
        case U≡A of λ
          (U₌ _ A⇒*U l≡l′) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
        ⊩l , l<ℓ , _ , A⇒*U , l≡l′ }})
    , (λ (⊩l , l<ℓ , l′ , A⇒*U , l≡l′) →
         let _ , ⊩l′ = wf-Level-eq l≡l′ in
           Uᵣ (Uᵣ _ ⊩l l<ℓ (id (⊢U (escapeLevel ⊩l))))
         , wf-⊩≡
             (⊩-⇐* A⇒*U $
              ⊩U⇔ .proj₂ (⊩l′ , PE.subst (_<ᵘ ℓ) (↑ᵘ-cong l≡l′) l<ℓ))
             .proj₁
         , U₌ _ A⇒*U l≡l′)

opaque

  ⊩U≡U⇔ :
    Γ ⊩⟨ ℓ ⟩ U l₁ ≡ U l₂ ⇔
    (∃ λ (l₁≡l₂ : Γ ⊩Level l₁ ≡ l₂ ∷Level) →
       ↑ᵘ (wf-Level-eq l₁≡l₂ .proj₁) <ᵘ ℓ)
  ⊩U≡U⇔ {Γ} {ℓ} {l₁} {l₂} =
    Γ ⊩⟨ ℓ ⟩ U l₁ ≡ U l₂                                   ⇔⟨ ⊩U≡⇔ ⟩

    (∃ λ ⊩l₁ → ↑ᵘ ⊩l₁ <ᵘ ℓ ×
     ∃ λ l₃ → Γ ⊢ U l₂ ⇒* U l₃ × Γ ⊩Level l₁ ≡ l₃ ∷Level)  ⇔⟨ (λ (_ , l₁<ℓ , _ , U⇒*U , l₁≡l₃) →
                                                                 case U⇒*U→≡ U⇒*U of λ {
                                                                   PE.refl →
                                                                 l₁≡l₃ , PE.subst (_<ᵘ ℓ) ↑ᵘ-irrelevance l₁<ℓ })
                                                            , (λ (l₁≡l₂ , l₁<ℓ) →
                                                                 wf-Level-eq l₁≡l₂ .proj₁ ,
                                                                 PE.subst (_<ᵘ ℓ) ↑ᵘ-irrelevance l₁<ℓ ,
                                                                 _ , id (⊢U (escapeLevel (wf-Level-eq l₁≡l₂ .proj₂))) , l₁≡l₂)
                                                            ⟩
    (∃ λ l₁≡l₂ → ↑ᵘ (wf-Level-eq l₁≡l₂ .proj₁) <ᵘ ℓ)       □⇔

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷U⇔ :
    Γ ⊩⟨ ℓ ⟩ A ≡ B ∷ U l ⇔
    (∃ λ (⊩l : Γ ⊩Level l ∷Level) → ↑ᵘ ⊩l <ᵘ ℓ ×
     Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A ≡ B ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A ⇒* A′ ∷ U l ×
     Γ ⊢ B ⇒* B′ ∷ U l ×
     Typeₗ (Γ .defs) A′ ×
     Typeₗ (Γ .defs) B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U l)
  ⊩≡∷U⇔ =
      (λ (⊩U , A≡B) →
        case U-view ⊩U of λ {
          (Uᵣ (Uᵣ _ ⊩l l<ℓ U⇒*U)) →
        case A≡B of λ
          (Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B) →
        case U⇒*U→≡ U⇒*U of λ {
          PE.refl →
          ⊩l , l<ℓ
        , ( ⊩<⇔⊩ l<ℓ .proj₁ ⊩A
          , ⊩<⇔⊩ l<ℓ .proj₁ ⊩B
          , ⊩<≡⇔⊩≡ l<ℓ .proj₁ A≡B
          )
        , _ , _ , A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′ }})
    , (λ (⊩l , l<ℓ , (⊩A , ⊩B , A≡B) , _ , _ ,
          A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′) →
         let ⊩A = ⊩<⇔⊩ l<ℓ .proj₂ ⊩A
             ⊩B = ⊩<⇔⊩ l<ℓ .proj₂ ⊩B
         in
           Uᵣ (Uᵣ _ ⊩l l<ℓ (id (⊢U (escapeLevel ⊩l))))
         , Uₜ₌ _ _ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B
             (⊩<≡⇔⊩≡′ l<ℓ .proj₂ A≡B))

opaque

  -- A consequence of ⊩≡∷U⇔.

  ⊩≡∷U→ :
    Γ ⊩⟨ ℓ ⟩ A ≡ B ∷ U l →
    Γ ⊩Level l ∷Level × Γ ⊩⟨ ℓ ⟩ A ≡ B
  ⊩≡∷U→ A≡B =
    let ⊩l , <ℓ , A≡B , _ = ⊩≡∷U⇔ .proj₁ A≡B in
    ⊩l , emb-⊩≡ (<ᵘ→≤ᵘ <ℓ) A≡B

opaque

  -- A variant of ⊩≡∷U⇔.

  Type→⊩≡∷U⇔ :
    Typeₗ (Γ .defs) A →
    Typeₗ (Γ .defs) B →
    Γ ⊩⟨ ℓ ⟩ A ≡ B ∷ U l ⇔
    (∃ λ (⊩l : Γ ⊩Level l ∷Level) → ↑ᵘ ⊩l <ᵘ ℓ ×
     (Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A ≡ B) × Γ ⊢ A ≅ B ∷ U l)
  Type→⊩≡∷U⇔ {Γ} {A} {B} {ℓ} {l} A-type B-type =
    Γ ⊩⟨ ℓ ⟩ A ≡ B ∷ U l                           ⇔⟨ ⊩≡∷U⇔ ⟩

    (∃ λ ⊩l → ↑ᵘ ⊩l <ᵘ ℓ × (Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A ≡ B) ×
     ∃₂ λ A′ B′ →
     Γ ⊢ A ⇒* A′ ∷ U l ×
     Γ ⊢ B ⇒* B′ ∷ U l ×
     Typeₗ (Γ .defs) A′ ×
     Typeₗ (Γ .defs) B′ ×
     Γ ⊢ A′ ≅ B′ ∷ U l)                            ⇔⟨ (λ (⊩l , l<ℓ , A≡B , A′ , B′ , DA , DB , A′-type , B′-type , A′≅B′) →
                                                         case whnfRed*Term DA (typeWhnf A-type) of λ {
                                                           PE.refl →
                                                         case whnfRed*Term DB (typeWhnf B-type) of λ {
                                                           PE.refl →
                                                         (⊩l , l<ℓ , A≡B , A′≅B′)}})
                                                    , (λ (⊩l , l<ℓ , A≡B , A≅B) →
                                                         let _ , ⊢A , ⊢B = wf-⊢≡∷ (≅ₜ-eq A≅B) in
                                                         ⊩l , l<ℓ , A≡B , _ , _ , id ⊢A , id ⊢B , A-type , B-type , A≅B)
                                                    ⟩
    (∃ λ ⊩l → ↑ᵘ ⊩l <ᵘ ℓ × (Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A ≡ B) ×
     Γ ⊢ A ≅ B ∷ U l)                              □⇔

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷U⇔ :
    Γ ⊩⟨ ℓ ⟩ A ∷ U l ⇔
    (∃ λ (⊩l : Γ ⊩Level l ∷Level) → ↑ᵘ ⊩l <ᵘ ℓ ×
     Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A ×
     ∃ λ B → Γ ⊢ A ⇒* B ∷ U l × Typeₗ (Γ .defs) B × Γ ⊢≅ B ∷ U l)
  ⊩∷U⇔ {Γ} {ℓ} {A} {l} =
    Γ ⊩⟨ ℓ ⟩ A ∷ U l                                               ⇔⟨ ⊩∷⇔⊩≡∷ ⟩

    Γ ⊩⟨ ℓ ⟩ A ≡ A ∷ U l                                           ⇔⟨ ⊩≡∷U⇔ ⟩

    (∃ λ ⊩l → ↑ᵘ ⊩l <ᵘ ℓ × Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A ≡ A ×
     ∃₂ λ A′ A″ →
     Γ ⊢ A ⇒* A′ ∷ U l ×
     Γ ⊢ A ⇒* A″ ∷ U l ×
     Typeₗ (Γ .defs) A′ ×
     Typeₗ (Γ .defs) A″ ×
     Γ ⊢ A′ ≅ A″ ∷ U l)                                            ⇔⟨ (Σ-cong-⇔ λ _ → id⇔ ×-cong-⇔ sym⇔ ⊩⇔⊩≡ ×-cong-⇔
                                                                         ( (λ (_ , _ , A⇒*A′ , _ , A′-type , _ , A′≅A″) →
                                                                              _ , A⇒*A′ , A′-type , wf-⊢≅∷ A′≅A″ .proj₁)
                                                                         , (λ (_ , A⇒*B , B-type , ≅B) →
                                                                              _ , _ , A⇒*B , A⇒*B , B-type , B-type , ≅B)
                                                                         )) ⟩
    (∃ λ ⊩l → ↑ᵘ ⊩l <ᵘ ℓ × Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A ×
     ∃ λ B → Γ ⊢ A ⇒* B ∷ U l × Typeₗ (Γ .defs) B × Γ ⊢≅ B ∷ U l)  □⇔

opaque

  -- A consequence of ⊩∷U⇔.

  ⊩∷U→ :
    Γ ⊩⟨ ℓ ⟩ A ∷ U l →
    Γ ⊩Level l ∷Level × Γ ⊩⟨ ℓ ⟩ A
  ⊩∷U→ ⊩A =
    let ⊩l , <ℓ , ⊩A , _ = ⊩∷U⇔ .proj₁ ⊩A in
    ⊩l , emb-⊩ (<ᵘ→≤ᵘ <ℓ) ⊩A

opaque

  -- A variant of ⊩∷U⇔.

  Type→⊩∷U⇔ :
    Typeₗ (Γ .defs) A →
    Γ ⊩⟨ ℓ ⟩ A ∷ U l ⇔
    (∃ λ (⊩l : Γ ⊩Level l ∷Level) → ↑ᵘ ⊩l <ᵘ ℓ ×
     (Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A) × Γ ⊢≅ A ∷ U l)
  Type→⊩∷U⇔ {Γ} {A} {ℓ} {l} A-type =
    Γ ⊩⟨ ℓ ⟩ A ∷ U l                                                ⇔⟨ ⊩∷U⇔ ⟩

    (∃ λ ⊩l → ↑ᵘ ⊩l <ᵘ ℓ × (Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A) ×
    (∃ λ B → Γ ⊢ A ⇒* B ∷ U l × Typeₗ (Γ .defs) B × Γ ⊢≅ B ∷ U l))  ⇔⟨ (Σ-cong-⇔ λ _ → id⇔
                                                                         ×-cong-⇔
                                                                       id⇔
                                                                         ×-cong-⇔
                                                                       ( (λ (_ , A⇒*B , _ , B≅B) →
                                                                           case whnfRed*Term A⇒*B (typeWhnf A-type) of λ {
                                                                             PE.refl →
                                                                           B≅B })
                                                                       , (λ ≅A → _ , id (wf-⊢≡∷ (≅ₜ-eq ≅A) .proj₂ .proj₁) , A-type , ≅A)
                                                                       ))
                                                                     ⟩

    (∃ λ ⊩l → ↑ᵘ ⊩l <ᵘ ℓ ×
     (Γ ⊩⟨ ↑ᵘ ⊩l ⟩ A) × Γ ⊢≅ A ∷ U l)                               □⇔

------------------------------------------------------------------------
-- Reducibility

opaque

  -- Reducibility of equality between applications of U, seen as a
  -- term former.

  ⊩U≡U∷U :
    Γ ⊩Level l₁ ≡ l₂ ∷Level → Γ ⊩⟨ ωᵘ·2 ⟩ U l₁ ≡ U l₂ ∷ U (1ᵘ+ l₁)
  ⊩U≡U∷U l₁≡l₂ =
    let ⊩l₁ , ⊩l₂ = wf-Level-eq l₁≡l₂ in
    Type→⊩≡∷U⇔ Uₙ Uₙ .proj₂
      ( ⊩1ᵘ+ ⊩l₁
      , ↑ᵘ<ᵘωᵘ·2
      , ⊩U≡U⇔ .proj₂ (l₁≡l₂ , <ᵘ-1ᵘ+ _ _)
      , ≅ₜ-U-cong (escapeLevelEq l₁≡l₂)
      )

opaque

  -- Validity of one of the typing rules called univ.

  ⊩≡∷U→⊩≡ :
    Γ ⊩⟨ ℓ ⟩ A ≡ B ∷ U l →
    Γ ⊩⟨ ℓ ⟩ A ≡ B
  ⊩≡∷U→⊩≡ A≡B∷U =
    let _ , <ℓ , A≡B , _ = ⊩≡∷U⇔ .proj₁ A≡B∷U in
    emb-⊩≡ (<ᵘ→≤ᵘ <ℓ) A≡B

------------------------------------------------------------------------
-- Validity

opaque

  -- Validity of U.

  ⊩ᵛU : Γ ⊩ᵛ⟨ ℓ ⟩ l ∷Level → Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ U l
  ⊩ᵛU ⊩l =
    ⊩ᵛ⇔ʰ .proj₂
      ( wf-⊩ᵛ∷L ⊩l
      , λ ∇′⊇∇ σ₁≡σ₂ →
          let l[σ₁]≡l[σ₂]     = ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L
                                  (refl-⊩ᵛ≡∷L (defn-wk-⊩ᵛ∷L ∇′⊇∇ ⊩l))
                                  σ₁≡σ₂
              ⊩l[σ₁] , ⊩l[σ₂] = wf-Level-eq l[σ₁]≡l[σ₂]
          in
          ⊩U≡⇔ .proj₂
            ( ⊩l[σ₁]
            , ↑ᵘ<ᵘωᵘ·2
            , _ , id (⊢U (escapeLevel ⊩l[σ₂]))
            , l[σ₁]≡l[σ₂]
            )
      )

opaque

  -- Validity of equality preservation for U, seen as a term former.

  ⊩ᵛU≡U∷U′ :
    Γ ⊩ᵛ⟨ ℓ ⟩ l₁ ≡ l₂ ∷Level →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ U l₁ ≡ U l₂ ∷ U (1ᵘ+ l₁)
  ⊩ᵛU≡U∷U′ {l₁} l₁≡l₂ =
    let ⊩l₁ , ⊩l₂ = wf-⊩ᵛ≡∷L l₁≡l₂ in
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛU (1ᵘ+ᵛ ⊩l₁)
      , λ ∇′⊇∇ →
          PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
            (PE.cong U (PE.sym (1ᵘ+-[] l₁))) ∘→
          ⊩U≡U∷U ∘→ ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (defn-wk-⊩ᵛ≡∷L ∇′⊇∇ l₁≡l₂)
      )

opaque

  -- Validity of equality preservation for U, seen as a term former.

  ⊩ᵛU≡U∷U :
    Level-allowed →
    Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷ Level →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ U (level t) ≡ U (level u) ∷ U (level (sucᵘ t))
  ⊩ᵛU≡U∷U ok t≡u =
    ⊩ᵛU≡U∷U′ (term ok t≡u)

opaque

  -- Validity of U, seen as a term former.

  ⊩ᵛU∷U :
    Γ ⊩ᵛ⟨ ℓ ⟩ l ∷Level →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ U l ∷ U (1ᵘ+ l)
  ⊩ᵛU∷U = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ ⊩ᵛU≡U∷U′ ∘→ ⊩ᵛ∷L⇔⊩ᵛ≡∷L .proj₁

opaque

  -- Validity of one of the typing rules called univ.

  ⊩ᵛ≡∷U→⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ ℓ ⟩ A ≡ B ∷ U l →
    Γ ⊩ᵛ⟨ ℓ ⟩ A ≡ B
  ⊩ᵛ≡∷U→⊩ᵛ≡ A≡B∷U =
    ⊩ᵛ≡⇔ʰ .proj₂
      ( wf-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ A≡B∷U .proj₁))
      , λ ∇′⊇∇ →
          ⊩≡∷U→⊩≡ ∘→ R.⊩≡∷→ ∘→
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇∇ A≡B∷U)
      )

opaque

  -- Validity of another of the typing rules called univ.

  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ A ∷ U l →
    Γ ⊩ᵛ⟨ ℓ ⟩ A
  ⊩ᵛ∷U→⊩ᵛ = ⊩ᵛ⇔⊩ᵛ≡ .proj₂ ∘→ ⊩ᵛ≡∷U→⊩ᵛ≡ ∘→ ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₁

opaque

  -- Validity of equality preservation for U, seen as a type former.

  ⊩ᵛU≡U :
    Level-allowed →
    Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷ Level →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ U (level t) ≡ U (level u)
  ⊩ᵛU≡U ok = ⊩ᵛ≡∷U→⊩ᵛ≡ ∘→ ⊩ᵛU≡U∷U ok

------------------------------------------------------------------------
-- Validity of Level, seen as a term former

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩Level≡Level∷U⇔ :
    Γ ⊩⟨ ωᵘ·2 ⟩ Level ≡ Level ∷ U₀ ⇔ (⊢ Γ × Level-is-small)
  ⊩Level≡Level∷U⇔ =
      (λ Level≡Level →
         case ⊩≡∷U⇔ .proj₁ Level≡Level of λ
           (_ , _ , _ , _ , _ , Level⇒* , _) →
         case inversion-Level (redFirst*Term Level⇒*) of λ
           (_ , ok) →
         wf (subset*Term Level⇒*) , ok)
    , (λ (⊢Γ , ok) →
         let ⊢Level = Levelⱼ ⊢Γ ok in
         case id ⊢Level of λ
           Level⇒*Level →
         ⊩≡∷U⇔ .proj₂
           ( ⊩zeroᵘ ⊢Γ , ↑ᵘ<ᵘωᵘ·2 , ⊩Level≡⇔ .proj₂ (id (univ ⊢Level))
           , (_ , _ , Level⇒*Level , Level⇒*Level , Levelₙ , Levelₙ , ≅ₜ-Levelrefl ⊢Γ ok)
           ))

opaque

  -- Validity of Level, seen as a term former.

  Levelᵗᵛ : ⊩ᵛ Γ → Level-is-small → Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ Level ∷ U₀
  Levelᵗᵛ {Γ} ⊩Γ ok =
    ⊩ᵛ∷⇔ʰ .proj₂
      ( ⊩ᵛU (zeroᵘᵛ′ ⊩Γ)
      , λ {_} {∇′ = ∇′} _ {_} {Η = Δ} {σ₁ = σ₁} {σ₂ = σ₂} →
          ∇′ » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars          →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
          ∇′ »⊢ Δ                              →⟨ _, ok ⟩
          ∇′ »⊢ Δ × Level-is-small             ⇔˘⟨ ⊩Level≡Level∷U⇔ ⟩→
          ∇′ » Δ ⊩⟨ ωᵘ·2 ⟩ Level ≡ Level ∷ U₀  □
      )
