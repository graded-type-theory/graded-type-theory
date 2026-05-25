------------------------------------------------------------------------
-- Validity for quotient types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Quotient
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (Eq : EqRelSet R)
  where

open EqRelSet Eq
open Modality 𝕄
open Type-restrictions R

open import Definition.LogicalRelation _ ⦃ eqrel = Eq ⦄
open import Definition.LogicalRelation.Hidden _ ⦃ eqrel = Eq ⦄
open import Definition.LogicalRelation.Irrelevance _ ⦃ eqrel = Eq ⦄
open import Definition.LogicalRelation.Properties _ ⦃ eqrel = Eq ⦄
import Definition.LogicalRelation.Hidden.Restricted _ ⦃ eqrel = Eq ⦄
  as R
import Definition.LogicalRelation.ShapeView _ ⦃ eqrel = Eq ⦄ as S
open import Definition.LogicalRelation.Substitution _ ⦃ eqrel = Eq ⦄
open import
  Definition.LogicalRelation.Substitution.Introductions.Identity
    _ ⦃ eqrel = Eq ⦄
open import Definition.LogicalRelation.Substitution.Introductions.Level
  _ ⦃ eqrel = Eq ⦄
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe
    _ ⦃ eqrel = Eq ⦄
open import Definition.LogicalRelation.Substitution.Introductions.Var
  _ ⦃ eqrel = Eq ⦄
open import Definition.LogicalRelation.Weakening.Definition
  _ ⦃ eqrel = Eq ⦄
open import Definition.LogicalRelation.Weakening.Restricted
  _ ⦃ eqrel = Eq ⦄

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Reduction R
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Weakening.Combined R
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Identity 𝕄
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Quotient 𝕄
open import Definition.Untyped.Whnf M type-variant

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  m n                                       : Nat
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆                    : Universe-level
  Δ                                         : Con _ _
  Γ                                         : Cons _ _
  A A₁ A₂ B B₁ B₂ C C₁ C₂
    t t₁ t₂ u u₁ u₂ v v₁ v₂ w w₁ w₁″ w₂ w₂″ : Term _
  l                                         : Lvl _
  σ σ₁ σ₂                                   : Subst _ _

------------------------------------------------------------------------
-- A lemma used below

private opaque

  [class-0]↑[⇑][]₀≡ :
    (C : Term (1+ n)) →
    C [ class (var x0) ]↑ [ σ ⇑ ] [ t ]₀ PE.≡
    C [ σ ⇑ ] [ class t ]₀
  [class-0]↑[⇑][]₀≡ {σ} {t} C =
    C [ class (var x0) ]↑ [ σ ⇑ ] [ t ]₀  ≡⟨ PE.cong _[ _ ]₀ ([][]↑-commutes C) ⟩
    C [ σ ⇑ ] [ class (var x0) ]↑ [ t ]₀  ≡⟨ [][]↑-[] 1 (C [ _ ]) ⟩
    C [ σ ⇑ ] [ class t ]₀                ∎

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩Quot⇔ :
    Γ ⊩⟨ ℓ ⟩ Quot A B ⇔
    (Γ ⊢≅ Quot A B ×
     (∀ {κ′ m} {Δ : Cons κ′ m} {ρ : Wk m n} →
      Δ ⊢ʷᵏʳ ρ ∷ Γ →
      Δ ⊩⟨ ℓ ⟩ wk ρ A ×
      (∀ {t₁ t₂ u₁ u₂} →
       Δ ⊩⟨ ℓ ⟩ t₁ ≡ t₂ ∷ wk ρ A →
       Δ ⊩⟨ ℓ ⟩ u₁ ≡ u₂ ∷ wk ρ A →
       Δ ⊩⟨ ℓ ⟩ wk (liftn ρ 2) B [ t₁ , u₁ ]₁₀ ≡
         wk (liftn ρ 2) B [ t₂ , u₂ ]₁₀)))
  ⊩Quot⇔ {A} {B} =
    (λ ⊩Q →
       case S.Quot-view ⊩Q of λ {
         (S.Quot ⊩Q@record{}) →
       let open _⊩ₗQuot_ ⊩Q in
       case whnfRed* ⇒*Quot Quot of λ {
         PE.refl →
       ≅Quot ,
       λ {_ _ _ _} ⊢ρ →
         ⊩Data ⊢ρ ,
         λ {_ _ _ _} t₁≡t₂ u₁≡u₂ →
           let ⊩t₁ , ⊩t₂ = wf-⊩≡∷ t₁≡t₂
               ⊩u₁ , ⊩u₂ = wf-⊩≡∷ u₁≡u₂
               ⊩t₂′      = ⊩∷→⊩∷/ (⊩Data ⊢ρ) ⊩t₂
               ⊩u₂′      = ⊩∷→⊩∷/ (⊩Data ⊢ρ) ⊩u₂
           in
           ⊩≡-intro
             (⊩Rel ⊢ρ (⊩∷→⊩∷/ (⊩Data ⊢ρ) ⊩t₁)
                (⊩∷→⊩∷/ (⊩Data ⊢ρ) ⊩u₁))
             (⊩Rel ⊢ρ ⊩t₂′ ⊩u₂′) $
           Rel≡Rel ⊢ρ _ ⊩t₂′ _ ⊩u₂′
             (⊩≡∷→⊩≡∷/ (⊩Data ⊢ρ) t₁≡t₂)
             (⊩≡∷→⊩≡∷/ (⊩Data ⊢ρ) u₁≡u₂) }}) ,
    (λ (⊢≅Q , rest) →
       let ⊢Q , _ = wf-⊢ (≅-eq ⊢≅Q) in
       Quot record
         { ⇒*Quot = id ⊢Q
         ; ≅Quot  = ⊢≅Q
         ; ⊩Data  = proj₁ ∘→ rest
         ; ⊩Rel   = λ ⊢ρ ⊩t ⊩u →
             let ⊩A , _ = rest ⊢ρ in
             wf-⊩≡
               (rest ⊢ρ .proj₂ (refl-⊩≡∷ (⊩∷-intro ⊩A ⊩t))
                  (refl-⊩≡∷ (⊩∷-intro ⊩A ⊩u)))
               .proj₁
         ; Rel≡Rel = λ ⊢ρ _ _ _ _ t₁≡t₂ u₁≡u₂ →
             let ⊩A , ⊩B = rest ⊢ρ in
             ⊩≡→⊩≡/ _ $
             ⊩B (⊩≡∷-intro ⊩A t₁≡t₂) (⊩≡∷-intro ⊩A u₁≡u₂)
         })

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Quot≡⇔ :
    Γ ⊩⟨ ℓ ⟩ Quot A B ≡ C ⇔
    (Γ ⊩⟨ ℓ ⟩ Quot A B ×
     Γ ⊩⟨ ℓ ⟩ C ×
     ∃₂ λ A′ B′ →
     Γ ⊢ C ⇒* Quot A′ B′ ×
     Γ ⊢ Quot A B ≅ Quot A′ B′ ×
     (∀ {κ′ m} {Δ : Cons κ′ m} {ρ : Wk m n} →
      Δ ⊢ʷᵏʳ ρ ∷ Γ →
      Δ ⊩⟨ ℓ ⟩ wk ρ A ≡ wk ρ A′ ×
      (∀ {t u} →
       Δ ⊩⟨ ℓ ⟩ t ∷ wk ρ A →
       Δ ⊩⟨ ℓ ⟩ u ∷ wk ρ A →
       Δ ⊩⟨ ℓ ⟩ wk (liftn ρ 2) B [ t , u ]₁₀ ≡
         wk (liftn ρ 2) B′ [ t , u ]₁₀)))
  ⊩Quot≡⇔ =
    (λ Q≡ →
       case wf-⊩≡ Q≡ of λ
         (⊩Q , ⊩C) →
       ⊩Q , ⊩C ,
       (case S.Quot-view ⊩Q of λ {
          (S.Quot ⊩Q@record{}) →
        case ⊩≡→⊩≡/ (Quot ⊩Q) Q≡ of λ {
          Q≡Q →
        let open _⊩ₗQuot_ ⊩Q hiding (Rel≡Rel)
            open _⊩ₗQuot_≡_/_ Q≡Q
        in
        _ , _ , ⇒*Quot′ ,
        (case whnfRed* ⇒*Quot Quot of λ {
           PE.refl →
         (Quot≅Quot ,
          λ ⊢ρ →
            let ⊩Data′ , rest =
                  ⊩Quot⇔ .proj₁ (wf-⊩≡ (⊩-⇒* ⇒*Quot′ ⊩C) .proj₂)
                    .proj₂ ⊢ρ
                wk-A≡wk-Data′ =
                  ⊩≡-intro (⊩Data ⊢ρ) ⊩Data′ (Data≡Data ⊢ρ)
            in
            wk-A≡wk-Data′ ,
            λ ⊩t ⊩u →
              ⊩≡-intro _
                (wf-⊩≡
                   (rest (refl-⊩≡∷ (conv-⊩∷ wk-A≡wk-Data′ ⊩t))
                      (refl-⊩≡∷ (conv-⊩∷ wk-A≡wk-Data′ ⊩u)))
                   .proj₁) $
              Rel≡Rel ⊢ρ (⊩∷→⊩∷/ (⊩Data ⊢ρ) ⊩t)
                (⊩∷→⊩∷/ (⊩Data ⊢ρ) ⊩u)) }) }})) ,
    (λ (⊩Q , ⊩C , _ , _ , C⇒* , Q≅Q , rest) →
       case S.Quot-view ⊩Q of λ {
         (S.Quot ⊩Q@record{}) →
       let open _⊩ₗQuot_ ⊩Q in
       case whnfRed* ⇒*Quot Quot of λ {
         PE.refl →
       ⊩≡-intro (Quot ⊩Q) ⊩C record
         { ⇒*Quot′   = C⇒*
         ; Quot≅Quot = Q≅Q
         ; Data≡Data = λ ⊢ρ → ⊩≡→⊩≡/ (⊩Data ⊢ρ) (rest ⊢ρ .proj₁)
         ; Rel≡Rel   = λ ⊢ρ ⊩t ⊩u →
             ⊩≡→⊩≡/ (⊩Rel ⊢ρ ⊩t ⊩u) $
             rest ⊢ρ .proj₂ (⊩∷-intro (⊩Data ⊢ρ) ⊩t)
               (⊩∷-intro (⊩Data ⊢ρ) ⊩u)
         } }})

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩Quot≡Quot⇔ :
    Γ ⊩⟨ ℓ ⟩ Quot A₁ B₁ ≡ Quot A₂ B₂ ⇔
    (Γ ⊩⟨ ℓ ⟩ Quot A₁ B₁ ×
     Γ ⊩⟨ ℓ ⟩ Quot A₂ B₂ ×
     Γ ⊢ Quot A₁ B₁ ≅ Quot A₂ B₂ ×
     (∀ {κ′ m} {Δ : Cons κ′ m} {ρ : Wk m n} →
      Δ ⊢ʷᵏʳ ρ ∷ Γ →
      Δ ⊩⟨ ℓ ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
      (∀ {t u} →
       Δ ⊩⟨ ℓ ⟩ t ∷ wk ρ A₁ →
       Δ ⊩⟨ ℓ ⟩ u ∷ wk ρ A₁ →
       Δ ⊩⟨ ℓ ⟩ wk (liftn ρ 2) B₁ [ t , u ]₁₀ ≡
         wk (liftn ρ 2) B₂ [ t , u ]₁₀)))
  ⊩Quot≡Quot⇔ {Γ} {ℓ} {A₁} {B₁} {A₂} {B₂} =
    (λ Q≡Q →
       case ⊩Quot≡⇔ .proj₁ Q≡Q of λ
         (⊩Q₁ , ⊩Q₂ , _ , _ , Q⇒*Q , rest) →
       case whnfRed* Q⇒*Q Quot of λ {
         PE.refl →
       ⊩Q₁ , ⊩Q₂ , rest }) ,
    (λ (⊩Q₁ , ⊩Q₂ , rest) →
       ⊩Quot≡⇔ .proj₂
         (⊩Q₁ , ⊩Q₂ , _ , _ , id (escape-⊩ ⊩Q₂) , rest))

opaque
  unfolding Quot-rel-Con

  -- A variant of ⊩Quot≡Quot⇔.

  ⊩Quot≡Quot→ :
    Γ ⊩⟨ ℓ ⟩ Quot A₁ B₁ ≡ Quot A₂ B₂ →
    Quot-allowed ×
    Γ ⊩⟨ ℓ ⟩ A₁ ≡ A₂ ×
    (⦃ inc : Var-included ⦄ → Quot-rel-Cons Γ A₁ ⊩⟨ ℓ ⟩ B₁ ≡ B₂)
  ⊩Quot≡Quot→ Quot≡Quot =
    let _ , _ , Q≅Q , rest = ⊩Quot≡Quot⇔ .proj₁ Quot≡Quot
        ⊢Q₁ , _            = wf-⊢ (≅-eq Q≅Q)
        ok , _ , ⊢B₁       = inversion-Quot ⊢Q₁
    in
    ok ,
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wk-id _) (wk-id _)
      (rest (⊢ʷᵏʳid (wf ⊢Q₁)) .proj₁) ,
    let wk₁-A₁≡wk₁-A₂ ,
          wk-lift²-step²-id-B₁[]₁₀≡wk-lift²-step²-id-B₂[]₁₀ =
          rest (includedʳ (⊢ʷᵏdrop (wf ⊢B₁)))
        ⊩wk2-A₁ =
          PE.subst (_⊩⟨_⟩_ _ _) (PE.sym wk[]≡wk[]′) $
          wf-⊩≡ wk₁-A₁≡wk₁-A₂ .proj₁
    in
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _) lemma lemma $
    wk-lift²-step²-id-B₁[]₁₀≡wk-lift²-step²-id-B₂[]₁₀
      (PE.subst (_⊩⟨_⟩_∷_ _ _ _) wk[]≡wk[]′ $
       ⊩var (there here) ⊩wk2-A₁)
      (PE.subst (_⊩⟨_⟩_∷_ _ _ _) wk[]≡wk[]′ $
       ⊩var here ⊩wk2-A₁)
    where
    lemma : wk (liftn (stepn id 2) 2) t [ var x1 , var x0 ]₁₀ PE.≡ t
    lemma {t} =
      wk (liftn (stepn id 2) 2) t [ var x1 , var x0 ]₁₀  ≡⟨ subst-wk t ⟩

      t [ consSubst (sgSubst (var x1)) (var x0) ₛ•
          liftn (stepn id 2) 2 ]                         ≡⟨ (flip substVar-to-subst t λ where
                                                               x0        → PE.refl
                                                               (x0 +1)   → PE.refl
                                                               (_ +1 +1) → PE.refl) ⟩

      t [ idSubst ]                                      ≡⟨ subst-id _ ⟩

      t                                                  ∎

opaque

  -- A variant of ⊩Quot⇔.

  ⊩Quot→ :
    Γ ⊩⟨ ℓ ⟩ Quot A B →
    Quot-allowed ×
    Γ ⊩⟨ ℓ ⟩ A ×
    (⦃ inc : Var-included ⦄ → Quot-rel-Cons Γ A ⊩⟨ ℓ ⟩ B)
  ⊩Quot→ ⊩Quot =
    let ok , A≡A , B≡B = ⊩Quot≡Quot→ (refl-⊩≡ ⊩Quot) in
    ok , wf-⊩≡ A≡A .proj₁ , wf-⊩≡ B≡B .proj₁

-- A variant of Quot-view.

data Quot-viewʰ
       (Γ : Cons m n) (ℓ : Universe-level) (A : Term n)
         (B : Term (2+ n)) : (_ _ : Term n) → Set a where
  equal :
    (t≡u : Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A) →
    Quot-viewʰ Γ ℓ A B (class t) (class u)
  related :
    (ok : Equality-reflection)
    (rel :
       Symmetric-transitive-closure
         (λ t u →
            Γ ⊩⟨ ℓ ⟩ t ∷ A ×
            Γ ⊩⟨ ℓ ⟩ u ∷ A ×
            ∃ λ v → Γ ⊩⟨ ℓ ⟩ v ∷ B [ t , u ]₁₀)
         t u) →
    Quot-viewʰ Γ ℓ A B (class t) (class u)
  ne :
    (t-n : Neutralᵃₗ (Γ .defs) t)
    (u-n : Neutralᵃₗ (Γ .defs) u)
    (t~u : Γ ⊢ t ~ u ∷ Quot A B) →
    Quot-viewʰ Γ ℓ A B t u

opaque

  -- If Quot-viewʰ Γ ℓ A B t u holds, then Quotientᵃₗ (Γ .defs) t and
  -- Quotientᵃₗ (Γ .defs) u both hold.

  Quot-viewʰ→Quotientᵃ :
    Quot-viewʰ Γ ℓ A B t u →
    Quotientᵃₗ (Γ .defs) t × Quotientᵃₗ (Γ .defs) u
  Quot-viewʰ→Quotientᵃ (equal _)      = class , class
  Quot-viewʰ→Quotientᵃ (related _ _)  = class , class
  Quot-viewʰ→Quotientᵃ (ne t-n u-n _) = ne t-n , ne u-n

opaque

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷Quot⇔ :
    Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ Quot A B ⇔
    (Γ ⊩⟨ ℓ ⟩ Quot A B ×
     ∃₂ λ t′ u′ →
     Γ ⊢ t ⇒* t′ ∷ Quot A B ×
     Γ ⊢ u ⇒* u′ ∷ Quot A B ×
     Quot-viewʰ Γ ℓ A B t′ u′)
  ⊩≡∷Quot⇔ {B} =
    (λ t≡u →
       let ⊩t , ⊩u = wf-⊩≡∷ t≡u in
       case wf-⊩∷ ⊩t of λ
         ⊩Q →
       case S.Quot-view ⊩Q of λ {
         (S.Quot ⊩Q@record{}) →
       case ⊩≡∷→⊩≡∷/ (Quot ⊩Q) t≡u of λ
         t≡u →
       let open _⊩ₗQuot_ ⊩Q
           t′ , u′ , t⇒*t′ , u⇒*u′ , _ = t≡u
           ⊩wk-A = ⊩Data (⊢ʷᵏʳid (wf (subset* ⇒*Quot)))
       in
       case whnfRed* ⇒*Quot Quot of λ {
         PE.refl →
       Quot ⊩Q , t′ , u′ , t⇒*t′ , u⇒*u′ ,
       (case Quot-view-inhabited ⊩Q t≡u of λ where
          (equal t≡u) →
            equal $
            PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-id _) $
            ⊩≡∷-intro ⊩wk-A t≡u
          (related ok rel) →
            related ok
              (Symmetric-transitive-closure-map
                 (λ (⊩t , ⊩u , _ , ⊩v) →
                    PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk-id _)
                      (⊩∷-intro ⊩wk-A ⊩t) ,
                    PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk-id _)
                      (⊩∷-intro ⊩wk-A ⊩u) ,
                    _ ,
                    PE.subst (_⊩⟨_⟩_∷_ _ _ _)
                      (PE.cong _[ _ , _ ]₁₀ (wk-liftn-id 2 B))
                      (⊩∷-intro (⊩Rel _ ⊩t ⊩u) ⊩v))
                 rel)
          (ne t-n u-n t~u) →
            ne t-n u-n t~u) }}) ,
    (λ (⊩Q , t′ , u′ , t⇒*t′ , u⇒*u′ , rest) →
       case S.Quot-view ⊩Q of λ {
         (S.Quot ⊩Q@record{}) →
       let open _⊩ₗQuot_ ⊩Q in
       case whnfRed* ⇒*Quot Quot of λ {
         PE.refl →
       let ⊢id = ⊢ʷᵏʳid (wf (subset* ⇒*Quot))
           ⊩A  = ⊩Data ⊢id
       in
       ⊩≡∷-intro (Quot ⊩Q)
         (t′ , u′ , t⇒*t′ , u⇒*u′ ,
          (case rest of λ where
             (equal t≡u) →
               class , class ,
               inj₁
                 (⊩≡∷→⊩≡∷/ ⊩A $
                  PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym (wk-id _)) t≡u)
             (related ok rel) →
               class , class ,
               inj₂
                 (ok ,
                  Symmetric-transitive-closure-map
                    (λ (⊩t , ⊩u , _ , ⊩v) →
                       ⊩∷→⊩∷/ ⊩A
                         (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym (wk-id _))
                            ⊩t) ,
                       ⊩∷→⊩∷/ ⊩A
                         (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym (wk-id _))
                            ⊩u) ,
                       _ ,
                       ⊩∷→⊩∷/ (⊩Rel ⊢id _ _)
                         (PE.subst (_⊩⟨_⟩_∷_ _ _ _)
                            (PE.cong _[ _ , _ ]₁₀
                               (PE.sym (wk-liftn-id 2 B)))
                            ⊩v))
                    rel)
             (ne t-n u-n t~u) →
               ne t-n , ne u-n , t~u)) }})

opaque

  -- A variant of ⊩≡∷Id⇔.

  Quotientᵃ→⊩≡∷Quot⇔ :
    Quotientᵃₗ (Γ .defs) t → Quotientᵃₗ (Γ .defs) u →
    Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ Quot A B ⇔
    (Γ ⊩⟨ ℓ ⟩ Quot A B × Quot-viewʰ Γ ℓ A B t u)
  Quotientᵃ→⊩≡∷Quot⇔ t-q u-q =
    (λ t≡u →
       case ⊩≡∷Quot⇔ .proj₁ t≡u of λ
         (⊩Q , _ , _ , t⇒*t′ , u⇒*u′ , rest) →
       case whnfRed*Term t⇒*t′ (Quotientᵃ→Whnf t-q) of λ {
         PE.refl →
       case whnfRed*Term u⇒*u′ (Quotientᵃ→Whnf u-q) of λ {
         PE.refl →
       ⊩Q , rest }}) ,
    (λ (⊩Q , rest) →
       let ⊢Q      = escape-⊩ ⊩Q
           ⊢t , ⊢u = case rest of λ where
             (equal t≡u) →
               let _ , ⊢t , ⊢u = wf-⊢ (≅ₜ-eq (escape-⊩≡∷ t≡u)) in
               class ⊢Q ⊢t , class ⊢Q ⊢u
             (related _ rel) →
               Symmetric-transitive-closure-elim-×
                 (λ (⊩t , ⊩u , _) →
                    class ⊢Q (escape-⊩∷ ⊩t) ,
                    class ⊢Q (escape-⊩∷ ⊩u))
                 rel
             (ne _ _ t~u) →
               wf-⊢ (~-eq t~u) .proj₂
       in
       ⊩≡∷Quot⇔ .proj₂
         (⊩Q , _ , _ , id ⊢t , id ⊢u , rest))

-- A variant of Quot-view₁.

data Quot-view₁ʰ
       (Γ : Cons m n) (ℓ : Universe-level) (A : Term n)
         (B : Term (2+ n)) : Term n → Set a where
  class :
    (⊩t : Γ ⊩⟨ ℓ ⟩ t ∷ A) →
    Quot-view₁ʰ Γ ℓ A B (class t)
  ne :
    (t-n : Neutralᵃₗ (Γ .defs) t)
    (~t : Γ ⊢~ t ∷ Quot A B) →
    Quot-view₁ʰ Γ ℓ A B t

opaque

  -- Quot-view₁ʰ is pointwise logically equivalent to the diagonal of
  -- Quot-viewʰ.

  Quot-view₁ʰ⇔Quot-viewʰ :
    Quot-view₁ʰ Γ ℓ A B t ⇔ Quot-viewʰ Γ ℓ A B t t
  Quot-view₁ʰ⇔Quot-viewʰ =
    (λ where
       (class ⊩t)  → equal (refl-⊩≡∷ ⊩t)
       (ne t-n ~t) → ne t-n t-n ~t) ,
    (λ where
       (ne t-n _ t~u)  → ne t-n t~u
       (equal t≡t)     → class (wf-⊩≡∷ t≡t .proj₁)
       (related _ rel) →
         class $ proj₁ $
         Symmetric-transitive-closure-elim-×
           (λ (⊩t , ⊩u , _) → ⊩t , ⊩u) rel)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷Quot⇔ :
    Γ ⊩⟨ ℓ ⟩ t ∷ Quot A B ⇔
    (Γ ⊩⟨ ℓ ⟩ Quot A B ×
     ∃ λ t′ →
     Γ ⊢ t ⇒* t′ ∷ Quot A B ×
     Quot-view₁ʰ Γ ℓ A B t′)
  ⊩∷Quot⇔ =
    (id⇔ ×-cong-⇔
       ((λ (_ , _ , t⇒*t′ , t⇒*t″ , rest) →
           let t′-q , t″-q = Quot-viewʰ→Quotientᵃ rest in
           case whrDet*Term (t⇒*t′ , Quotientᵃ→Whnf t′-q)
                  (t⇒*t″ , Quotientᵃ→Whnf t″-q) of λ {
             PE.refl →
           _ , t⇒*t′ , Quot-view₁ʰ⇔Quot-viewʰ .proj₂ rest }) ,
        (λ (_ , t⇒*t′ , rest) →
           _ , _ , t⇒*t′ , t⇒*t′ ,
           Quot-view₁ʰ⇔Quot-viewʰ .proj₁ rest))) ∘⇔
    ⊩≡∷Quot⇔ ∘⇔ ⊩∷⇔⊩≡∷

opaque

  -- A variant of ⊩∷Quot⇔.

  Quotientᵃ→⊩∷Quot⇔ :
    Quotientᵃₗ (Γ .defs) t →
    Γ ⊩⟨ ℓ ⟩ t ∷ Quot A B ⇔
    (Γ ⊩⟨ ℓ ⟩ Quot A B × Quot-view₁ʰ Γ ℓ A B t)
  Quotientᵃ→⊩∷Quot⇔ t-q =
    (id⇔ ×-cong-⇔ sym⇔ Quot-view₁ʰ⇔Quot-viewʰ) ∘⇔
    Quotientᵃ→⊩≡∷Quot⇔ t-q t-q ∘⇔ ⊩∷⇔⊩≡∷

------------------------------------------------------------------------
-- A substitution lemma

opaque

  -- A substitution lemma for _⊩⟨_⟩_≡_.

  ⊩Quot≡Quot→⊩≡∷→⊩≡∷→⊩[]₁₀≡[]₁₀ :
    Γ ⊩⟨ ℓ₁ ⟩ Quot A₁ B₁ ≡ Quot A₂ B₂ →
    Γ ⊩⟨ ℓ₂ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩⟨ ℓ₃ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩⟨ ℓ₁ ⟩ B₁ [ t₁ , u₁ ]₁₀ ≡ B₂ [ t₂ , u₂ ]₁₀
  ⊩Quot≡Quot→⊩≡∷→⊩≡∷→⊩[]₁₀≡[]₁₀
    {B₁} {B₂} {t₁} {t₂} {u₁} {u₂} Quot≡Quot t₁≡t₂ u₁≡u₂ =
    let ⊩Q₁ , _ , _ , rest = ⊩Quot≡Quot⇔ .proj₁ Quot≡Quot
        _ , ⊩A₁ , _        = ⊩Quot→ ⊩Q₁
        ⊢≅Q , rest₁        = ⊩Quot⇔ .proj₁ ⊩Q₁
        ⊢Γ                 = wf (wf-⊢ (≅-eq ⊢≅Q) .proj₁)
    in
    B₁ [ t₁ , u₁ ]₁₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                           (PE.cong _[ _ , _ ]₁₀ (wk-liftn-id 2 B₁))
                           (PE.cong _[ _ , _ ]₁₀ (wk-liftn-id 2 B₁)) $
                         rest₁ (⊢ʷᵏʳid ⊢Γ) .proj₂
                           (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                              (PE.sym $ wk-id _) $
                            level-⊩≡∷ ⊩A₁ t₁≡t₂)
                           (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                              (PE.sym $ wk-id _) $
                            level-⊩≡∷ ⊩A₁ u₁≡u₂) ⟩⊩
    B₁ [ t₂ , u₂ ]₁₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                           (PE.cong _[ _ , _ ]₁₀ (wk-liftn-id 2 B₁))
                           (PE.cong _[ _ , _ ]₁₀ (wk-liftn-id 2 B₂)) $
                         rest (⊢ʷᵏʳid ⊢Γ) .proj₂
                           (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk-id _) $
                            level-⊩∷ ⊩A₁ $ wf-⊩≡∷ t₁≡t₂ .proj₂)
                           (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk-id _) $
                            level-⊩∷ ⊩A₁ $ wf-⊩≡∷ u₁≡u₂ .proj₂) ⟩⊩∎
    B₂ [ t₂ , u₂ ]₁₀  ∎

------------------------------------------------------------------------
-- The type former Quot

opaque
  unfolding Quot-rel-Con

  -- Validity for Quot-rel-Cons.

  Quot-rel-Consᵛ :
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ A →
    ⊩ᵛ Quot-rel-Cons Γ A
  Quot-rel-Consᵛ ⊩A = ⊩ᵛ-∙-intro (wk1-⊩ᵛ ⊩A ⊩A)

opaque
  unfolding Quot-rel-Con

  -- An introduction lemma for Quot.

  ⊩Quot :
    Quot-allowed →
    Γ ⊩ᵛ⟨ ℓ ⟩ A →
    Quot-rel-Cons Γ A ⊢ B →
    Quot-rel-Cons Γ A ⊩ᵛ⟨ ℓ ⟩ B →
    ⦃ inc : Var-included or-empty Δ ⦄ →
    Γ .defs » Δ ⊩ˢ σ ∷ Γ .vars →
    Γ .defs » Δ ⊩⟨ ℓ ⟩ Quot A B [ σ ]
  ⊩Quot {Γ} {A} {B} ok ⊩A ⊢B ⊩B ⊩σ =
    let _ , ⊢σ = escape-⊩ˢ∷ ⊩σ in
    ⊩Quot⇔ .proj₂
      (≅-Quot-cong ok (escape-⊩≡ (refl-⊩≡ (R.⊩→ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ))))
         (PE.subst₃ _⊢_≅_
            (Quot-rel-Con-[] (Γ .vars) A) PE.refl PE.refl $
          with-inc-⊢≅ (refl (subst-⊢-⇑ ⊢B ⊢σ)) $
          escape-⊩≡ $
          refl-⊩≡ (R.⊩→ ⦃ inc = included ⦄ (⊩ᵛ→⊩ˢ∷→⊩[⇑[]] ⊩B ⊩σ))) ,
       λ ⊢ρ →
         wk-⊩ ⊢ρ (R.⊩→ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ)) ,
         λ t₁≡t₂ u₁≡u₂ →
           let instance
                 inc    = wk-Var-included-or-empty← ⊢ρ
               Δ⊇Γ , ⊢ρ = ⊢ʷᵏ⇔ .proj₁ (⊢ʷᵏʳ→⊢ʷᵏ ⊢ρ)
               ⊩A       = defn-wk-⊩ᵛ Δ⊇Γ ⊩A
               ⊩B       = defn-wk-⊩ᵛ Δ⊇Γ ⊩B
               ⊩σ       = defn-wk-⊩ˢ∷ Δ⊇Γ ⊩σ
           in
           PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
             (PE.sym (doubleSubstWkComp B))
             (PE.sym (doubleSubstWkComp B)) $
           R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] (refl-⊩ᵛ≡ ⊩B) $
           ⊩ˢ≡∷∙⇔ .proj₂
             ((( _ , wk1-⊩ᵛ ⊩A ⊩A
               , (R.→⊩≡∷ $
                  PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                    (PE.trans (wk-subst A) (PE.sym (wk1-tail A))) u₁≡u₂)
               )) ,
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ( _ , ⊩A
                  , (R.→⊩≡∷ $
                     PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A) t₁≡t₂)
                  )
                , refl-⊩ˢ≡∷ (⊩ˢ∷-•ₛ ⊢ρ ⊩σ)
                )))

opaque
  unfolding Quot-rel-Con

  -- A congruence lemma for Quot.

  ⊩Quot≡Quot :
    Quot-allowed →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ ℓ ⟩ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ ⟩ B₁ ≡ B₂ →
    ⦃ inc : Var-included or-empty Δ ⦄ →
    Γ .defs » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars →
    Γ .defs » Δ ⊩⟨ ℓ ⟩ Quot A₁ B₁ [ σ₁ ] ≡ Quot A₂ B₂ [ σ₂ ]
  ⊩Quot≡Quot
    {Γ} {A₁} {A₂} {B₁} {B₂} ok ⊢A₁≡A₂ A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ σ₁≡σ₂ =
    let ⊩A₁ , ⊩A₂ = wf-⊩ᵛ≡ A₁≡A₂
        ⊢B₁ , ⊢B₂ = wf-⊢ ⊢B₁≡B₂
        ⊩B₁ , ⊩B₂ = wf-⊩ᵛ≡ B₁≡B₂
        ⊩σ₁ , ⊩σ₂ = wf-⊩ˢ≡∷ σ₁≡σ₂
    in
    ⊩Quot≡Quot⇔ .proj₂
      ( ⊩Quot ok ⊩A₁ ⊢B₁ ⊩B₁ ⊩σ₁
      , ⊩Quot ok ⊩A₂
          (stability (Quot-rel-Con-cong (reflConEq (wf ⊢A₁≡A₂)) ⊢A₁≡A₂)
             ⊢B₂)
          (conv-∙∙-⊩ᵛ A₁≡A₂ (wk1-⊩ᵛ≡ ⊩A₁ A₁≡A₂) ⊩B₂) ⊩σ₂
      , ≅-Quot-cong ok (R.escape-⊩≡ (⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ σ₁≡σ₂))
          (PE.subst₃ _⊢_≅_
             (Quot-rel-Con-[] (Γ .vars) A₁) PE.refl PE.refl $
           with-inc-⊢≅ (subst-⊢≡-⇑ ⊢B₁≡B₂ (escape-⊩ˢ≡∷ σ₁≡σ₂ .proj₂)) $
           R.escape-⊩≡ ⦃ inc = included ⦄ $
           ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑[]]≡[⇑[]] B₁≡B₂ σ₁≡σ₂)
      , λ ⊢ρ →
          let instance
                inc   = wk-Var-included-or-empty← ⊢ρ
              ∇⊇ , ⊢ρ = ⊢ʷᵏ⇔ .proj₁ (⊢ʷᵏʳ→⊢ʷᵏ ⊢ρ)
              ⊩A₁     = defn-wk-⊩ᵛ ∇⊇ ⊩A₁
              A₁≡A₂   = defn-wk-⊩ᵛ≡ ∇⊇ A₁≡A₂
              B₁≡B₂   = defn-wk-⊩ᵛ≡ ∇⊇ B₁≡B₂
              σ₁≡σ₂   = defn-wk-⊩ˢ≡∷ ∇⊇ σ₁≡σ₂
          in
           PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
             (PE.sym $ wk-subst A₁) (PE.sym $ wk-subst A₂)
             (R.⊩≡→ (⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ (⊩ˢ≡∷-•ₛ ⊢ρ σ₁≡σ₂))) ,
           λ ⊩t ⊩u →
             PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
               (PE.sym $ doubleSubstWkComp B₁)
               (PE.sym $ doubleSubstWkComp B₂) $
             R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] B₁≡B₂ $
             ⊩ˢ≡∷∙⇔ .proj₂
               ((( _ , wk1-⊩ᵛ ⊩A₁ ⊩A₁
                 , (R.refl-⊩≡∷ $ R.→⊩∷ $
                    PE.subst (_⊩⟨_⟩_∷_ _ _ _)
                      (PE.trans (wk-subst A₁) (PE.sym (wk1-tail A₁)))
                      ⊩u)
                 )) ,
                ⊩ˢ≡∷∙⇔ .proj₂
                  ( ( _ , ⊩A₁
                    , (R.refl-⊩≡∷ $ R.→⊩∷ $
                       PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk-subst A₁) ⊩t)
                    )
                  , ⊩ˢ≡∷-•ₛ ⊢ρ σ₁≡σ₂
                  ))
      )

opaque

  -- Validity congruence for Quot, seen as a type former.

  Quot-congᵛ :
    Quot-allowed →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ ℓ ⟩ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ ℓ ⟩ Quot A₁ B₁ ≡ Quot A₂ B₂
  Quot-congᵛ ok ⊢A₁≡A₂ A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ =
    let ⊩A₁ , _ = wf-⊩ᵛ≡ A₁≡A₂ in
    ⊩ᵛ≡⇔ʰ .proj₂
      ( wf-⊩ᵛ ⊩A₁
      , λ ∇⊇ →
          ⊩Quot≡Quot ok (defn-wk ∇⊇ ⊢A₁≡A₂) (defn-wk-⊩ᵛ≡ ∇⊇ A₁≡A₂)
            (defn-wk ∇⊇ ⊢B₁≡B₂) (defn-wk-⊩ᵛ≡ ∇⊇ B₁≡B₂)
      )

opaque

  -- A variant of Quot-congᵛ.

  Quot-congᵛ′ :
    Quot-allowed →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ₂ ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ Quot A₁ B₁ ≡ Quot A₂ B₂
  Quot-congᵛ′ ok ⊢A₁≡A₂ A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ =
    Quot-congᵛ ok ⊢A₁≡A₂ (emb-⊩ᵛ≡ ≤ᵘωᵘ·2 A₁≡A₂) ⊢B₁≡B₂
      (emb-⊩ᵛ≡ ≤ᵘωᵘ·2 B₁≡B₂)

opaque
  unfolding Quot-rel-Con

  -- Validity for Quot, seen as a type former.

  Quotᵛ :
    Quot-allowed →
    Γ ⊩ᵛ⟨ ℓ ⟩ A →
    Quot-rel-Cons Γ A ⊢ B →
    Quot-rel-Cons Γ A ⊩ᵛ⟨ ℓ ⟩ B →
    Γ ⊩ᵛ⟨ ℓ ⟩ Quot A B
  Quotᵛ ok ⊩A ⊢B ⊩B =
    let _ , (⊢A , _) , _ = ∙∙⊢→⊢-<ˢ ⊢B in
    wf-⊩ᵛ≡
      (Quot-congᵛ ok (refl ⊢A) (refl-⊩ᵛ≡ ⊩A) (refl ⊢B) (refl-⊩ᵛ≡ ⊩B))
      .proj₁

opaque
  unfolding Quot-rel-Con

  -- A variant of Quotᵛ.

  Quotᵛ′ :
    Quot-allowed →
    Quot-rel-Cons Γ A ⊢ B →
    Quot-rel-Cons Γ A ⊩ᵛ⟨ ℓ₂ ⟩ B →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ Quot A B
  Quotᵛ′ ok ⊢B ⊩B =
    let _ , ⊩wk1-A = wf-⊩ᵛ-∙ (wf-⊩ᵛ ⊩B)
        _ , ⊩A     = wf-⊩ᵛ-∙ (wf-⊩ᵛ ⊩wk1-A)
    in
    Quotᵛ ok (emb-⊩ᵛ ≤ᵘωᵘ·2 ⊩A) ⊢B (emb-⊩ᵛ ≤ᵘωᵘ·2 ⊩B)

opaque
  unfolding Quot-rel-Con

  -- A kind of inversion lemma for quotient types.

  ⊩ᵛQuot→ :
    Γ ⊩ᵛ⟨ ℓ ⟩ Quot A B →
    (⦃ inc : Var-included or-empty (Γ .vars) ⦄ → Quot-allowed) ×
    Γ ⊩ᵛ⟨ ℓ ⟩ A × Quot-rel-Cons Γ A ⊩ᵛ⟨ ℓ ⟩ B
  ⊩ᵛQuot→ {A} {B} ⊩Q =
    let ⊩Γ , Q≡Q = ⊩ᵛ⇔ʰ .proj₁ ⊩Q
        ⊩A       =
          ⊩ᵛ⇔ʰ .proj₂
            (⊩Γ , λ ∇⊇ → proj₁ ∘→ proj₂ ∘→ ⊩Quot≡Quot→ ∘→ Q≡Q ∇⊇)
    in
    inversion-Quot (escape-⊩ᵛ ⊩Q) .proj₁ ,
    ⊩A ,
    ⊩ᵛ⇔ʰ .proj₂
      ( ⊩ᵛ-∙-intro (wk1-⊩ᵛ ⊩A ⊩A)
      , λ ∇⊇ {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          let (_ , _ , σ₁₀≡σ₂₀)   , σ₁₊≡σ₂₊   = ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂
              (_ , _ , σ₁₊₀≡σ₂₊₀) , σ₁₊₊≡σ₂₊₊ = ⊩ˢ≡∷∙⇔ .proj₁ σ₁₊≡σ₂₊
          in
          B [ σ₁ ]                                                   ≡˘⟨ (flip substVar-to-subst B λ x →
                                                                          PE.trans (consSubst-cong PE.refl consSubst-η x) $
                                                                          consSubst-η {σ = σ₁} x) ⟩⊩≡
          B [ consSubst (consSubst (tail[ 2 ] σ₁) (head (tail σ₁)))
                (head σ₁) ]                                          ≡˘⟨ doubleSubstComp B _ _ _ ⟩⊩≡

          B [ tail[ 2 ] σ₁ ⇑[ 2 ] ] [ head (tail σ₁) , head σ₁ ]₁₀   ≡⟨ ⊩Quot≡Quot→⊩≡∷→⊩≡∷→⊩[]₁₀≡[]₁₀
                                                                          (Q≡Q ∇⊇ σ₁₊₊≡σ₂₊₊) (R.⊩≡∷→ σ₁₊₀≡σ₂₊₀)
                                                                          (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk1-tail A) $
                                                                           R.⊩≡∷→ σ₁₀≡σ₂₀) ⟩⊩∎≡

          B [ tail[ 2 ] σ₂ ⇑[ 2 ] ] [ head (tail σ₂) , head σ₂ ]₁₀   ≡⟨ doubleSubstComp B _ _ _ ⟩

          B [ consSubst (consSubst (tail[ 2 ] σ₂) (head (tail σ₂)))
                (head σ₂) ]                                          ≡⟨ (flip substVar-to-subst B λ x →
                                                                          PE.trans (consSubst-cong PE.refl consSubst-η x) $
                                                                          consSubst-η {σ = σ₂} x) ⟩
          B [ σ₂ ]                                                   ∎
      )

------------------------------------------------------------------------
-- The term former Quot

opaque
  unfolding Quot-rel-Con

  -- An introduction lemma for Quot.

  ⊩Quot∷U :
    Quot-allowed →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ l ∷Level →
    Γ ⊩ᵛ⟨ ℓ₂ ⟩ A ∷ U l →
    Quot-rel-Cons Γ A ⊢ B ∷ U (wk[ 2 ]′ l) →
    Quot-rel-Cons Γ A ⊩ᵛ⟨ ℓ₃ ⟩ B ∷ U (wk[ 2 ]′ l) →
    ⦃ inc : Var-included or-empty Δ ⦄ →
    Γ .defs » Δ ⊩ˢ σ ∷ Γ .vars →
    Γ .defs » Δ ⊩⟨ ωᵘ·2 ⟩ Quot A B [ σ ] ∷ U (l [ σ ])
  ⊩Quot∷U {Γ} {l} {A} {B} ok ⊩l ⊩A ⊢B ⊩B ⊩σ =
    let _ , ⊢σ = escape-⊩ˢ∷ ⊩σ
        ⊢≅Q    = ≅ₜ-Quot-cong ok
                   (escape-⊩≡∷ $
                    refl-⊩≡∷ (R.⊩∷→ (⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩A ⊩σ))) $
                 PE.subst₄ _⊢_≅_∷_ (Quot-rel-Con-[] (Γ .vars) A)
                   PE.refl PE.refl (wk[]′-[⇑] (U l)) $
                 with-inc-⊢≅∷ (refl (subst-⊢-⇑ ⊢B ⊢σ)) $
                 R.escape-⊩≡∷ ⦃ inc = included ⦄ $ R.refl-⊩≡∷ $
                 ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩B $
                 ⊩ˢ∷-⇑[] (Quot-rel-Consᵛ (⊩ᵛ∷U→⊩ᵛ ⊩A)) ⊩σ
    in
    Type→⊩∷U⇔ Quot .proj₂
      ( ⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L ⊩l ⊩σ
      , ↑ᵘ<ᵘωᵘ·2
      , ⊩Quot⇔ .proj₂
          ( ≅-univ ⊢≅Q
          , λ ⊢ρ →
              let instance
                    inc           = wk-Var-included-or-empty← ⊢ρ
                  ∇⊇ , ⊢ρ         = ⊢ʷᵏ⇔ .proj₁ (⊢ʷᵏʳ→⊢ʷᵏ ⊢ρ)
                  ⊩A              = defn-wk-⊩ᵛ∷ ∇⊇ ⊩A
                  ⊩σ              = defn-wk-⊩ˢ∷ ∇⊇ ⊩σ
                  _ , _ , ⊩A′ , _ =
                    ⊩∷U⇔ .proj₁ $ R.⊩∷→ $
                    ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩A (⊩ˢ∷-•ₛ ⊢ρ ⊩σ)
              in
              PE.subst₂ (_⊩⟨_⟩_ _)
                (↑ᵘ-irrelevance-»∷ʷ⊇-»⊇ ∇⊇ ⊢ρ (wk-subst l))
                (PE.sym (wk-subst A)) ⊩A′ ,
              λ t₁≡t₂ u₁≡u₂ →
                let _ , _ , B≡B , _ =
                      ⊩≡∷U⇔ .proj₁ $ R.⊩≡∷→ $
                      ⊩ᵛ∷⇔ .proj₁ ⊩B .proj₂ ∇⊇ $
                      ⊩ˢ≡∷∙⇔ {σ₁ = consSubst (consSubst _ _) _}
                        {σ₂ = consSubst (consSubst _ _) _} .proj₂
                        ( ( ωᵘ·2
                          , emb-⊩ᵛ ≤ᵘωᵘ·2
                              (wk1-⊩ᵛ (⊩ᵛ∷U→⊩ᵛ ⊩A) (⊩ᵛ∷U→⊩ᵛ ⊩A))
                          , (R.→⊩≡∷ $ emb-⊩≡∷ ≤ᵘωᵘ·2 $
                             PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                               (PE.trans (wk-subst A) $
                                PE.sym (wk1-tail A))
                               u₁≡u₂)
                          )
                        , ⊩ˢ≡∷∙⇔ .proj₂
                            ( ( ωᵘ·2
                              , emb-⊩ᵛ ≤ᵘωᵘ·2 (⊩ᵛ∷U→⊩ᵛ ⊩A)
                              , (R.→⊩≡∷ $ emb-⊩≡∷ ≤ᵘωᵘ·2 $
                                 PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                                   (wk-subst A) t₁≡t₂)
                              )
                            , refl-⊩ˢ≡∷ (⊩ˢ∷-•ₛ ⊢ρ ⊩σ)
                            )
                        )
                in
                PE.subst₃ (_⊩⟨_⟩_≡_ _)
                  (↑ᵘ-irrelevance-»∷ʷ⊇-»⊇ ∇⊇ ⊢ρ $
                   PE.trans (wk-subst l) (PE.sym (wk[]′-tail l)))
                  (PE.sym $ doubleSubstWkComp B)
                  (PE.sym $ doubleSubstWkComp B)
                  B≡B
          )
      , ⊢≅Q
      )

opaque
  unfolding Quot-rel-Con

  -- A congruence lemma for Quot.

  ⊩Quot≡Quot∷U :
    Quot-allowed →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ l ∷Level →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ ℓ₂ ⟩ A₁ ≡ A₂ ∷ U l →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk[ 2 ]′ l) →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ₃ ⟩ B₁ ≡ B₂ ∷ U (wk[ 2 ]′ l) →
    ⦃ inc : Var-included or-empty Δ ⦄ →
    Γ .defs » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars →
    Γ .defs » Δ ⊩⟨ ωᵘ·2 ⟩ Quot A₁ B₁ [ σ₁ ] ≡ Quot A₂ B₂ [ σ₂ ] ∷
      U (l [ σ₁ ])
  ⊩Quot≡Quot∷U
    {Γ} {l} {A₁} {A₂} {B₁} {B₂} ok ⊩l ⊢A₁≡A₂ A₁≡A₂∷U ⊢B₁≡B₂∷U B₁≡B₂∷U σ₁≡σ₂ =
    let _ , ⊢σ₁≡σ₂        = escape-⊩ˢ≡∷ σ₁≡σ₂
        ⊩σ₁ , ⊩σ₂         = wf-⊩ˢ≡∷ σ₁≡σ₂
        ⊩A₁∷U , ⊩A₂∷U     = wf-⊩ᵛ≡∷ A₁≡A₂∷U
        A₁≡A₂             = ⊩ᵛ≡∷U→⊩ᵛ≡ A₁≡A₂∷U
        ⊩A₁ , _           = wf-⊩ᵛ≡ A₁≡A₂
        _ , ⊢B₁∷U , ⊢B₂∷U = wf-⊢ ⊢B₁≡B₂∷U
        (⊢Γ , _) , _      = ∙∙⊢→⊢-<ˢ ⊢B₁∷U
        ⊢B₂∷U             = stability
                              (Quot-rel-Con-cong (reflConEq ⊢Γ) ⊢A₁≡A₂)
                              ⊢B₂∷U
        ⊩B₁∷U , ⊩B₂∷U     = wf-⊩ᵛ≡∷ B₁≡B₂∷U
        Q≅Q               =
          ≅ₜ-Quot-cong ok
            (R.escape-⊩≡∷ (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ A₁≡A₂∷U σ₁≡σ₂)) $
          PE.subst₄ _⊢_≅_∷_ (Quot-rel-Con-[] (Γ .vars) A₁)
            PE.refl PE.refl (wk[]′-[⇑] (U l)) $
          with-inc-⊢≅∷ (subst-⊢≡-⇑ ⊢B₁≡B₂∷U ⊢σ₁≡σ₂)
          (R.escape-⊩≡∷ ⦃ inc = included ⦄ $
          ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ B₁≡B₂∷U $
          ⊩ˢ≡∷-⇑[] (Quot-rel-Consᵛ ⊩A₁) σ₁≡σ₂)
        _ , _ , ⊩Q₁ , _ =
          Type→⊩∷U⇔ Quot .proj₁ $
          ⊩Quot∷U ok ⊩l ⊩A₁∷U ⊢B₁∷U ⊩B₁∷U ⊩σ₁
        _ , _ , ⊩Q₂ , _ =
          Type→⊩∷U⇔ Quot .proj₁ $
          ⊩Quot∷U ok ⊩l ⊩A₂∷U ⊢B₂∷U
            (conv-∙∙-⊩ᵛ∷ A₁≡A₂ (wk1-⊩ᵛ≡ ⊩A₁ A₁≡A₂) ⊩B₂∷U) ⊩σ₂
    in
    Type→⊩≡∷U⇔ Quot Quot .proj₂
      ( ⊩ᵛ∷L→⊩ˢ∷→⊩[]∷L ⊩l ⊩σ₁
      , ↑ᵘ<ᵘωᵘ·2
      , ⊩Quot≡Quot⇔ .proj₂
          ( PE.subst (flip (_⊩⟨_⟩_ _) _) ↑ᵘ-irrelevance ⊩Q₁
          , PE.subst (flip (_⊩⟨_⟩_ _) _)
              (PE.sym $ ↑ᵘ-cong $
               ⊩ᵛ≡∷L→⊩ˢ≡∷→⊩[]≡[]∷L (⊩ᵛ∷L⇔⊩ᵛ≡∷L .proj₁ ⊩l) σ₁≡σ₂)
              ⊩Q₂
          , ≅-univ Q≅Q
          , λ ⊢ρ →
              let instance
                    inc               = wk-Var-included-or-empty← ⊢ρ
                  ∇⊇ , ⊢ρ             = ⊢ʷᵏ⇔ .proj₁ (⊢ʷᵏʳ→⊢ʷᵏ ⊢ρ)
                  ⊩A₁                 = defn-wk-⊩ᵛ ∇⊇ ⊩A₁
                  A₁≡A₂∷U             = defn-wk-⊩ᵛ≡∷ ∇⊇ A₁≡A₂∷U
                  σ₁≡σ₂               = defn-wk-⊩ˢ≡∷ ∇⊇ σ₁≡σ₂
                  _ , _ , A₁≡A₂∷U , _ =
                    ⊩≡∷U⇔ .proj₁ $ R.⊩≡∷→ $
                    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ A₁≡A₂∷U (⊩ˢ≡∷-•ₛ ⊢ρ σ₁≡σ₂)
              in
              PE.subst₃ (_⊩⟨_⟩_≡_ _)
                (↑ᵘ-irrelevance-»∷ʷ⊇-»⊇ ∇⊇ ⊢ρ (wk-subst l))
                (PE.sym (wk-subst A₁)) (PE.sym (wk-subst A₂)) A₁≡A₂∷U ,
              λ ⊩t ⊩u →
                let _ , _ , B₁≡B₂∷U , _ =
                      ⊩≡∷U⇔ .proj₁ $ R.⊩≡∷→ $
                      ⊩ᵛ≡∷⇔ .proj₁ B₁≡B₂∷U .proj₂ ∇⊇ $
                      ⊩ˢ≡∷∙⇔ {σ₁ = consSubst (consSubst _ _) _}
                        {σ₂ = consSubst (consSubst _ _) _} .proj₂
                        ( ( ωᵘ·2
                          , emb-⊩ᵛ ≤ᵘωᵘ·2 (wk1-⊩ᵛ ⊩A₁ ⊩A₁)
                          , (R.→⊩≡∷ $ emb-⊩≡∷ ≤ᵘωᵘ·2 $ refl-⊩≡∷ $
                             PE.subst (_⊩⟨_⟩_∷_ _ _ _)
                               (PE.trans (wk-subst A₁) $
                                PE.sym (wk1-tail A₁))
                               ⊩u)
                          )
                        , ⊩ˢ≡∷∙⇔ .proj₂
                            ( ( ωᵘ·2
                              , emb-⊩ᵛ ≤ᵘωᵘ·2 ⊩A₁
                              , (R.→⊩≡∷ $ emb-⊩≡∷ ≤ᵘωᵘ·2 $ refl-⊩≡∷ $
                                 PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk-subst A₁)
                                   ⊩t)
                              )
                            , ⊩ˢ≡∷-•ₛ ⊢ρ σ₁≡σ₂
                            )
                        )
                in
                PE.subst₃ (_⊩⟨_⟩_≡_ _)
                  (↑ᵘ-irrelevance-»∷ʷ⊇-»⊇ ∇⊇ ⊢ρ $
                   PE.trans (wk-subst l) (PE.sym (wk[]′-tail l)))
                  (PE.sym $ doubleSubstWkComp B₁)
                  (PE.sym $ doubleSubstWkComp B₂)
                  B₁≡B₂∷U
          )
      , Q≅Q
      )

opaque

  -- Validity congruence for Quot, seen as a term former.

  Quot-congᵗᵛ :
    Quot-allowed →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ l ∷Level →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ ℓ₂ ⟩ A₁ ≡ A₂ ∷ U l →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ ∷ U (wk[ 2 ]′ l) →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ₃ ⟩ B₁ ≡ B₂ ∷ U (wk[ 2 ]′ l) →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ Quot A₁ B₁ ≡ Quot A₂ B₂ ∷ U l
  Quot-congᵗᵛ ok ⊩l ⊢A₁≡A₂ A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ =
    let ⊩A₁ , _ = wf-⊩ᵛ≡∷ A₁≡A₂ in
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛU ⊩l
      , λ ∇⊇ →
          ⊩Quot≡Quot∷U ok (defn-wk-⊩ᵛ∷L ∇⊇ ⊩l) (defn-wk ∇⊇ ⊢A₁≡A₂)
            (defn-wk-⊩ᵛ≡∷ ∇⊇ A₁≡A₂) (defn-wk ∇⊇ ⊢B₁≡B₂)
            (defn-wk-⊩ᵛ≡∷ ∇⊇ B₁≡B₂)
      )

opaque

  -- Validity for Quot, seen as a term former.

  Quotᵗᵛ :
    Quot-allowed →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ l ∷Level →
    Γ ⊢ A →
    Γ ⊩ᵛ⟨ ℓ₂ ⟩ A ∷ U l →
    Quot-rel-Cons Γ A ⊢ B ∷ U (wk[ 2 ]′ l) →
    Quot-rel-Cons Γ A ⊩ᵛ⟨ ℓ₃ ⟩ B ∷ U (wk[ 2 ]′ l) →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ Quot A B ∷ U l
  Quotᵗᵛ ok ⊩l ⊢A ⊩A ⊢B ⊩B =
    wf-⊩ᵛ≡∷
      (Quot-congᵗᵛ ok ⊩l (refl ⊢A) (refl-⊩ᵛ≡∷ ⊩A) (refl ⊢B)
         (refl-⊩ᵛ≡∷ ⊩B))
      .proj₁

------------------------------------------------------------------------
-- Validity for class

opaque

  -- A congruence lemma for class.

  ⊩class≡class :
    Γ ⊩⟨ ℓ ⟩ Quot A B →
    Γ ⊩⟨ ℓ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ ℓ ⟩ class t ≡ class u ∷ Quot A B
  ⊩class≡class ⊩Q t≡u =
    Quotientᵃ→⊩≡∷Quot⇔ class class .proj₂ (⊩Q , equal t≡u)

opaque

  -- An introduction lemma for class.

  ⊩class :
    Γ ⊩⟨ ℓ ⟩ Quot A B →
    Γ ⊩⟨ ℓ ⟩ t ∷ A →
    Γ ⊩⟨ ℓ ⟩ class t ∷ Quot A B
  ⊩class ⊩Q = proj₁ ∘→ wf-⊩≡∷ ∘→ ⊩class≡class ⊩Q ∘→ refl-⊩≡∷

opaque

  -- Validity for class-cong.

  class-congᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ Quot A B →
    Γ ⊩ᵛ⟨ ℓ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ ℓ ⟩ class t ≡ class u ∷ Quot A B
  class-congᵛ ⊩Q t≡u =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩Q
      , λ ∇′⊇ σ₁≡σ₂ →
          ⊩class≡class
            (wf-⊩≡ (⊩ᵛ⇔ʰ .proj₁ ⊩Q .proj₂ ∇′⊇ σ₁≡σ₂) .proj₁)
            (⊩ᵛ≡∷⇔ʰ .proj₁ t≡u .proj₂ ∇′⊇ σ₁≡σ₂)
      )

opaque

  -- A variant of class-congᵛ.

  class-congᵛ′ :
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₂ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ class t ≡ class u ∷ Quot A B
  class-congᵛ′ ⊩Q t≡u =
    class-congᵛ (emb-⊩ᵛ ≤ᵘωᵘ·2 ⊩Q) (emb-⊩ᵛ≡∷ ≤ᵘωᵘ·2 t≡u)

opaque

  -- Validity for class.

  classᵛ :
    Γ ⊩ᵛ⟨ ℓ ⟩ Quot A B →
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ ℓ ⟩ class t ∷ Quot A B
  classᵛ ⊩Q = ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ ∘→ class-congᵛ ⊩Q ∘→ refl-⊩ᵛ≡∷

opaque

  -- A variant of classᵛ.

  classᵛ′ :
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₂ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ class t ∷ Quot A B
  classᵛ′ ⊩Q ⊩t = classᵛ (emb-⊩ᵛ ≤ᵘωᵘ·2 ⊩Q) (emb-⊩ᵛ∷ ≤ᵘωᵘ·2 ⊩t)

------------------------------------------------------------------------
-- Validity for resp

opaque
  unfolding Quot-rel-Con

  -- A congruence lemma for resp.

  ⊩resp≡resp :
    Quot-allowed →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ ℓ ⟩ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ ⟩ B₁ ≡ B₂ →
    ⦃ inc : Var-included or-empty Δ ⦄ →
    Γ .defs » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars →
    Γ .defs » Δ ⊩⟨ ℓ ⟩ t₁ ≡ t₂ ∷ A₁ [ σ₁ ] →
    Γ .defs » Δ ⊩⟨ ℓ ⟩ u₁ ≡ u₂ ∷ A₁ [ σ₁ ] →
    Γ .defs » Δ ⊩⟨ ℓ ⟩ v₁ ≡ v₂ ∷ B₁ [ σ₁ ⇑[ 2 ] ] [ t₁ , u₁ ]₁₀ →
    Γ .defs » Δ ⊩⟨ ℓ ⟩ resp (A₁ [ σ₁ ]) (B₁ [ σ₁ ⇑[ 2 ] ]) t₁ u₁ v₁ ≡
      resp (A₂ [ σ₂ ]) (B₂ [ σ₂ ⇑[ 2 ] ]) t₂ u₂ v₂ ∷
      Id (Quot A₁ B₁ [ σ₁ ]) (class t₁) (class u₁)
  ⊩resp≡resp
    {Γ} {A₁} ok ⊢A₁≡A₂ A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ σ₁≡σ₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    let _ , ⊢σ₁≡σ₂          = escape-⊩ˢ≡∷ σ₁≡σ₂
        Q₁[σ₁]≡Q₂[σ₂]       = R.⊩≡→ $
                              ⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[]
                                (Quot-congᵛ ok ⊢A₁≡A₂ A₁≡A₂ ⊢B₁≡B₂
                                   B₁≡B₂)
                                σ₁≡σ₂
        ⊩Q₁[σ₁] , _         = wf-⊩≡ Q₁[σ₁]≡Q₂[σ₂]
        ⊢Q₁[σ₁] , ⊢Q₂[σ₂]   = wf-⊢ (≅-eq (escape-⊩≡ Q₁[σ₁]≡Q₂[σ₂]))
        A₁[σ₁]≅A₂[σ₂]       = escape-⊩≡ $
                              R.⊩≡→ (⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ σ₁≡σ₂)
        ⊢A₁[σ₁]≡A₂[σ₂]      = ≅-eq A₁[σ₁]≅A₂[σ₂]
        B₁[σ₁⇑²]≅B₂[σ₂⇑²]   = PE.subst₃ _⊢_≅_
                                (Quot-rel-Con-[] (Γ .vars) A₁)
                                PE.refl PE.refl $
                              with-inc-⊢≅ (subst-⊢≡-⇑ ⊢B₁≡B₂ ⊢σ₁≡σ₂) $
                              escape-⊩≡ $ R.⊩≡→ ⦃ inc = included ⦄ $
                              ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑[]]≡[⇑[]] B₁≡B₂ σ₁≡σ₂
        ⊢B₁[σ₁⇑²]≡B₂[σ₂⇑²]  = ≅-eq B₁[σ₁⇑²]≅B₂[σ₂⇑²]
        ⊩t₁ , _             = wf-⊩≡∷ t₁≡t₂
        t₁≅t₂               = escape-⊩≡∷ t₁≡t₂
        ⊢t₁≡t₂              = ≅ₜ-eq t₁≅t₂
        _ , ⊢t₁ , ⊢t₂       = wf-⊢ ⊢t₁≡t₂
        ⊢t₂                 = conv ⊢t₂ ⊢A₁[σ₁]≡A₂[σ₂]
        ⊩u₁ , _             = wf-⊩≡∷ u₁≡u₂
        u₁≅u₂               = escape-⊩≡∷ u₁≡u₂
        ⊢u₁≡u₂              = ≅ₜ-eq u₁≅u₂
        _ , ⊢u₁ , ⊢u₂       = wf-⊢ ⊢u₁≡u₂
        ⊢u₂                 = conv ⊢u₂ ⊢A₁[σ₁]≡A₂[σ₂]
        ⊩v₁ , _             = wf-⊩≡∷ v₁≡v₂
        v₁≅v₂               = escape-⊩≡∷ v₁≡v₂
        ⊢v₁≡v₂              = ≅ₜ-eq v₁≅v₂
        _ , ⊢v₁ , ⊢v₂       = wf-⊢ ⊢v₁≡v₂
        ⊢v₂                 = conv ⊢v₂
                                (subst-⊢≡₁₀ ⊢B₁[σ₁⇑²]≡B₂[σ₂⇑²] ⊢t₁≡t₂
                                   (PE.subst (_⊢_≡_∷_ _ _ _)
                                      (PE.sym (wk1-sgSubst _ _))
                                      ⊢u₁≡u₂))
        ⊢resp₁≡resp₂        = resp-cong ok ⊢A₁[σ₁]≡A₂[σ₂]
                                ⊢B₁[σ₁⇑²]≡B₂[σ₂⇑²] ⊢t₁≡t₂ ⊢u₁≡u₂ ⊢v₁≡v₂
        _ , ⊢resp₁ , ⊢resp₂ = wf-⊢ ⊢resp₁≡resp₂
    in
    case Equality-reflection? of λ where
      (no not-ok) →
        let n = Higher-quotient-constructors-neutral⇔ .proj₂
                  (ok , not-ok)
        in
        Identityᵃ→⊩≡∷Id⇔ (ne (respᵃ n)) (ne (respᵃ n)) .proj₂
          (⊢resp₁ , ⊢resp₂ ,
           ⊩class ⊩Q₁[σ₁] ⊩t₁ , ⊩class ⊩Q₁[σ₁] ⊩u₁ ,
           ne (respᵃ n) (respᵃ n)
             (~-resp-cong ok A₁[σ₁]≅A₂[σ₂] B₁[σ₁⇑²]≅B₂[σ₂⇑²] t₁≅t₂ u₁≅u₂
                v₁≅v₂))
      (yes refl-ok) →
        ⊩≡∷Id⇔ .proj₂
          (rfl , rfl ,
           redMany (resp-η refl-ok ⊢Q₁[σ₁] ⊢t₁ ⊢u₁ ⊢v₁) ,
           redMany
             (conv
                (resp-η refl-ok ⊢Q₂[σ₂] ⊢t₂ ⊢u₂ ⊢v₂)
                (_⊢_≡_.sym $
                 Id-cong
                   (Quot-cong ok ⊢A₁[σ₁]≡A₂[σ₂] ⊢B₁[σ₁⇑²]≡B₂[σ₂⇑²])
                   (class-cong ⊢Q₁[σ₁] ⊢t₁≡t₂)
                   (class-cong ⊢Q₁[σ₁] ⊢u₁≡u₂))) ,
           ⊩class ⊩Q₁[σ₁] ⊩t₁ , ⊩class ⊩Q₁[σ₁] ⊩u₁ ,
           rfl₌
             (Quotientᵃ→⊩≡∷Quot⇔ class class .proj₂
                (⊩Q₁[σ₁] ,
                 related refl-ok (injˢᵗ (⊩t₁ , ⊩u₁ , _ , ⊩v₁)))))

opaque
  unfolding Quot-rel-Con

  -- An introduction lemma for resp.

  ⊩resp :
    Quot-allowed →
    Γ ⊩ᵛ⟨ ℓ ⟩ A →
    Quot-rel-Cons Γ A ⊢ B →
    Quot-rel-Cons Γ A ⊩ᵛ⟨ ℓ ⟩ B →
    ⦃ inc : Var-included or-empty Δ ⦄ →
    Γ .defs » Δ ⊩ˢ σ ∷ Γ .vars →
    Γ .defs » Δ ⊩⟨ ℓ ⟩ t ∷ A [ σ ] →
    Γ .defs » Δ ⊩⟨ ℓ ⟩ u ∷ A [ σ ] →
    Γ .defs » Δ ⊩⟨ ℓ ⟩ v ∷ B [ σ ⇑[ 2 ] ] [ t , u ]₁₀ →
    Γ .defs » Δ ⊩⟨ ℓ ⟩ resp (A [ σ ]) (B [ σ ⇑[ 2 ] ]) t u v ∷
      Id (Quot A B [ σ ]) (class t) (class u)
  ⊩resp ok ⊩A ⊢B ⊩B ⊩σ ⊩t ⊩u ⊩v =
    let _ , (⊢A , _) , _ = ∙∙⊢→⊢-<ˢ ⊢B in
    wf-⊩≡∷
      (⊩resp≡resp ok (refl ⊢A) (refl-⊩ᵛ≡ ⊩A) (refl ⊢B) (refl-⊩ᵛ≡ ⊩B)
         (refl-⊩ˢ≡∷ ⊩σ) (refl-⊩≡∷ ⊩t) (refl-⊩≡∷ ⊩u) (refl-⊩≡∷ ⊩v))
      .proj₁

opaque

  -- Validity for resp-cong.

  resp-congᵛ :
    Quot-allowed →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ ℓ ⟩ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ ℓ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ ℓ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ ℓ ⟩ v₁ ≡ v₂ ∷ B₁ [ t₁ , u₁ ]₁₀ →
    Γ ⊩ᵛ⟨ ℓ ⟩ resp A₁ B₁ t₁ u₁ v₁ ≡ resp A₂ B₂ t₂ u₂ v₂ ∷
      Id (Quot A₁ B₁) (class t₁) (class u₁)
  resp-congᵛ {B₁} ok ⊢A₁≡A₂ A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    let ⊩A₁ , _ = wf-⊩ᵛ≡ A₁≡A₂
        ⊢B₁ , _ = wf-⊢ ⊢B₁≡B₂
        ⊩B₁ , _ = wf-⊩ᵛ≡ B₁≡B₂
        ⊩t₁ , _ = wf-⊩ᵛ≡∷ t₁≡t₂
        ⊩u₁ , _ = wf-⊩ᵛ≡∷ u₁≡u₂
        ⊩Q      = Quotᵛ ok ⊩A₁ ⊢B₁ ⊩B₁
    in
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( Idᵛ (classᵛ ⊩Q ⊩t₁) (classᵛ ⊩Q ⊩u₁)
      , λ ∇′⊇ σ₁≡σ₂ →
          ⊩resp≡resp ok (defn-wk ∇′⊇ ⊢A₁≡A₂) (defn-wk-⊩ᵛ≡ ∇′⊇ A₁≡A₂)
            (defn-wk ∇′⊇ ⊢B₁≡B₂) (defn-wk-⊩ᵛ≡ ∇′⊇ B₁≡B₂) σ₁≡σ₂
            (R.⊩≡∷→ (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇ t₁≡t₂) σ₁≡σ₂))
            (R.⊩≡∷→ (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇ u₁≡u₂) σ₁≡σ₂))
            (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) ([,]-[]-commute B₁) $
             R.⊩≡∷→ (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ (defn-wk-⊩ᵛ≡∷ ∇′⊇ v₁≡v₂) σ₁≡σ₂))
      )

opaque

  -- A variant of resp-congᵛ.

  resp-congᵛ′ :
    Quot-allowed →
    Γ ⊢ A₁ ≡ A₂ →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ₂ ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ ℓ₄ ⟩ u₁ ≡ u₂ ∷ A₁ →
    Γ ⊩ᵛ⟨ ℓ₅ ⟩ v₁ ≡ v₂ ∷ B₁ [ t₁ , u₁ ]₁₀ →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ resp A₁ B₁ t₁ u₁ v₁ ≡ resp A₂ B₂ t₂ u₂ v₂ ∷
      Id (Quot A₁ B₁) (class t₁) (class u₁)
  resp-congᵛ′ ok ⊢A₁≡A₂ A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    resp-congᵛ ok ⊢A₁≡A₂ (emb-⊩ᵛ≡ ≤ᵘωᵘ·2 A₁≡A₂) ⊢B₁≡B₂
      (emb-⊩ᵛ≡ ≤ᵘωᵘ·2 B₁≡B₂) (emb-⊩ᵛ≡∷ ≤ᵘωᵘ·2 t₁≡t₂)
      (emb-⊩ᵛ≡∷ ≤ᵘωᵘ·2 u₁≡u₂) (emb-⊩ᵛ≡∷ ≤ᵘωᵘ·2 v₁≡v₂)

opaque
  unfolding Quot-rel-Con

  -- Validity for resp.

  respᵛ :
    Γ ⊢ Quot A B →
    Γ ⊩ᵛ⟨ ℓ ⟩ Quot A B →
    Γ ⊩ᵛ⟨ ℓ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ ℓ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ ℓ ⟩ v ∷ B [ t , u ]₁₀ →
    Γ ⊩ᵛ⟨ ℓ ⟩ resp A B t u v ∷ Id (Quot A B) (class t) (class u)
  respᵛ ⊢Q ⊩Q ⊩t ⊩u ⊩v =
    let ok , ⊢A , ⊢B = inversion-Quot ⊢Q
        _ , ⊩A , ⊩B  = ⊩ᵛQuot→ ⊩Q
    in
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂
      (resp-congᵛ ok (refl ⊢A) (refl-⊩ᵛ≡ ⊩A) (refl ⊢B) (refl-⊩ᵛ≡ ⊩B)
         (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ᵛ≡∷ ⊩u) (refl-⊩ᵛ≡∷ ⊩v))

opaque

  -- A variant of respᵛ.

  respᵛ′ :
    Γ ⊢ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₂ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ ℓ₄ ⟩ v ∷ B [ t , u ]₁₀ →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ resp A B t u v ∷ Id (Quot A B) (class t) (class u)
  respᵛ′ ⊢Q ⊩Q ⊩t ⊩u ⊩v =
    respᵛ ⊢Q (emb-⊩ᵛ ≤ᵘωᵘ·2 ⊩Q) (emb-⊩ᵛ∷ ≤ᵘωᵘ·2 ⊩t) (emb-⊩ᵛ∷ ≤ᵘωᵘ·2 ⊩u)
      (emb-⊩ᵛ∷ ≤ᵘωᵘ·2 ⊩v)

opaque

  -- A simplification lemma for Resp-type.

  Equality-reflection→Resp-type-[]₂₁₀≡ :
    Equality-reflection →
    Γ ⊩ᵛ⟨ ℓ′ ⟩ A →
    Quot-rel-Cons Γ A ⊩ᵛ⟨ ℓ′ ⟩ B →
    Γ »∙ Quot A B ⊢ C →
    Γ »∙ Quot A B ⊩ᵛ⟨ ℓ ⟩ C →
    Γ »∙ A ⊩ᵛ⟨ ℓ ⟩ t ∷ C [ class (var x0) ]↑ →
    Γ .defs » ε ⊩ˢ σ ∷ Γ .vars →
    Γ .defs » ε ⊩⟨ ℓ′ ⟩ u ∷ A [ σ ] →
    Γ .defs » ε ⊩⟨ ℓ′ ⟩ v ∷ A [ σ ] →
    Γ .defs » ε ⊩⟨ ℓ′ ⟩ w ∷ B [ σ ⇑[ 2 ] ] [ u , v ]₁₀ →
    Γ .defs » ε ⊩⟨ ℓ ⟩
      Resp-type A B C t [ σ ⇑[ 3 ] ] [ u , v , w ]₂₁₀ ≡
      Id (C [ σ ⇑ ] [ class u ]₀) (t [ σ ⇑ ] [ u ]₀) (t [ σ ⇑ ] [ v ]₀)
  Equality-reflection→Resp-type-[]₂₁₀≡
    {A} {B} {C} {t} {σ} {u} {v} {w} ok ⊩A ⊩B ⊢C ⊩C ⊩t ⊩σ ⊩u ⊩v ⊩w =
    let q-ok , _ , ⊢B     = inversion-Quot (⊢∙→⊢ (wf ⊢C))
        _ , ⊢σ            = escape-⊩ˢ∷ ⦃ inc = ε ⦄ ⊩σ
        ⊢C[σ⇑]            = subst-⊢-⇑ ⊢C ⊢σ
        u≡v               = Equality-reflection→⊩∷Id⇔ ok .proj₁
                              (_ ,
                               ⊩resp q-ok ⊩A ⊢B ⊩B ⦃ inc = ε ⦄ ⊩σ ⊩u ⊩v
                                 ⊩w)
        C[σ⇑][u]≡C[σ⇑][v] = R.⊩≡→ ⦃ inc = ε ⦄ $
                            ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩C)
                              (refl-⊩ˢ≡∷ ⊩σ) (R.→⊩≡∷ u≡v)
        ⊩t[σ⇑][u]         = PE.subst (_⊩⟨_⟩_∷_ _ _ _)
                              ([class-0]↑[⇑][]₀≡ C) $
                            R.⊩∷→ ⦃ inc = ε ⦄ $
                            ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[⇑][]₀∷ ⊩t ⊩σ (R.→⊩∷ ⊩u)
        ⊢t[σ⇑][u]         = escape-⊩∷ ⊩t[σ⇑][u]
    in
    PE.subst (flip (_⊩⟨_⟩_≡_ _ _) _)
      (PE.sym $
       PE.trans (PE.cong _[ _ , _ , _ ]₂₁₀ Resp-type-[])
       Resp-type-[]₂₁₀) $
    ⊩Id≡Id⇔ .proj₂
      ( sym-⊩≡ C[σ⇑][u]≡C[σ⇑][v]
      , ⊩∷-⇐*
          (subst ω (Quot A B [ σ ]) (C [ σ ⇑ ]) (class u) (class v)
             (resp (A [ σ ]) (B [ σ ⇑[ 2 ] ]) u v w)
             (t [ σ ⇑ ] [ u ]₀) ∷ C [ σ ⇑ ] [ class v ]₀             ⇒⟨ subst-subst ⊢C[σ⇑]
                                                                          (resp-η ok (⊢∙→⊢ (wf ⊢C[σ⇑])) (escape-⊩∷ ⊩u) (escape-⊩∷ ⊩v)
                                                                             (escape-⊩∷ ⊩w))
                                                                          ⊢t[σ⇑][u] ⟩∷
                                                                     ˘⟨ ≅-eq (escape-⊩≡ C[σ⇑][u]≡C[σ⇑][v]) ⟩⇒
           subst ω (Quot A B [ σ ]) (C [ σ ⇑ ]) (class u) (class v)
             rfl (t [ σ ⇑ ] [ u ]₀) ∷ C [ σ ⇑ ] [ class u ]₀         ⇒⟨ subst-⇒′ ⊢C[σ⇑] (≅ₜ-eq (escape-⊩≡∷ u≡v)) ⊢t[σ⇑][u] ⟩∎∷

           t [ σ ⇑ ] [ u ]₀                                          ∎)
          (conv-⊩∷ C[σ⇑][u]≡C[σ⇑][v] ⊩t[σ⇑][u])
      , refl-⊩≡∷
          (PE.subst (_⊩⟨_⟩_∷_ _ _ _) ([class-0]↑[⇑][]₀≡ C) $
           R.⊩∷→ ⦃ inc = ε ⦄ (⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[⇑][]₀∷ ⊩t ⊩σ (R.→⊩∷ ⊩v)))
      )

------------------------------------------------------------------------
-- Validity for set

opaque
  unfolding Quot-rel-Con

  -- A congruence lemma for set.

  ⊩set≡set :
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ₂ ⟩ B₁ ≡ B₂ →
    ⦃ inc : Var-included or-empty Δ ⦄ →
    Γ .defs » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars →
    Γ .defs » Δ ⊩⟨ ℓ₃ ⟩ t₁ ≡ t₂ ∷ Quot A₁ B₁ [ σ₁ ] →
    Γ .defs » Δ ⊩⟨ ℓ₄ ⟩ u₁ ≡ u₂ ∷ Quot A₁ B₁ [ σ₁ ] →
    Γ .defs » Δ ⊩⟨ ℓ₅ ⟩ v₁ ≡ v₂ ∷ Id (Quot A₁ B₁ [ σ₁ ]) t₁ u₁ →
    Γ .defs » Δ ⊩⟨ ℓ₅ ⟩ w₁ ≡ w₂ ∷ Id (Quot A₁ B₁ [ σ₁ ]) t₁ u₁ →
    Γ .defs » Δ ⊩⟨ ℓ₅ ⟩ set (A₁ [ σ₁ ]) (B₁ [ σ₁ ⇑[ 2 ] ]) t₁ u₁ v₁ w₁ ≡
      set (A₂ [ σ₂ ]) (B₂ [ σ₂ ⇑[ 2 ] ]) t₂ u₂ v₂ w₂ ∷
      Id (Id (Quot A₁ B₁ [ σ₁ ]) t₁ u₁) v₁ w₁
  ⊩set≡set
    {Γ} {A₁} {v₁} {w₁}
    A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ σ₁≡σ₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
    let _ , ⊢σ₁≡σ₂          = escape-⊩ˢ≡∷ σ₁≡σ₂
        A₁[σ₁]≅A₂[σ₂]       = escape-⊩≡ $
                              R.⊩≡→ (⊩ᵛ≡→⊩ˢ≡∷→⊩[]≡[] A₁≡A₂ σ₁≡σ₂)
        ⊢A₁[σ₁]≡A₂[σ₂]      = ≅-eq A₁[σ₁]≅A₂[σ₂]
        B₁[σ₁⇑²]≅B₂[σ₂⇑²]   = PE.subst₃ _⊢_≅_
                                (Quot-rel-Con-[] (Γ .vars) A₁)
                                PE.refl PE.refl $
                              with-inc-⊢≅ (subst-⊢≡-⇑ ⊢B₁≡B₂ ⊢σ₁≡σ₂) $
                              escape-⊩≡ $ R.⊩≡→ ⦃ inc = included ⦄ $
                              ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑[]]≡[⇑[]] B₁≡B₂ σ₁≡σ₂
        ⊢B₁[σ₁⇑²]≡B₂[σ₂⇑²]  = ≅-eq B₁[σ₁⇑²]≅B₂[σ₂⇑²]
        t₁≅t₂               = escape-⊩≡∷ t₁≡t₂
        t₁≡t₂′              = ≅ₜ-eq t₁≅t₂
        u₁≅u₂               = escape-⊩≡∷ u₁≡u₂
        u₁≡u₂′              = ≅ₜ-eq u₁≅u₂
        v₁≅v₂               = escape-⊩≡∷ v₁≡v₂
        v₁≡v₂′              = ≅ₜ-eq v₁≅v₂
        w₁≅w₂               = escape-⊩≡∷ w₁≡w₂
        w₁≡w₂′              = ≅ₜ-eq w₁≅w₂
        ⊢Q , ⊢t₁ , ⊢t₂      = wf-⊢ t₁≡t₂′
        ok , _              = inversion-Quot ⊢Q
        Q≡Q                 = Quot-cong ok ⊢A₁[σ₁]≡A₂[σ₂]
                                ⊢B₁[σ₁⇑²]≡B₂[σ₂⇑²]
        Id≡Id               = Id-cong Q≡Q t₁≡t₂′ u₁≡u₂′
        ⊢t₂                 = conv ⊢t₂ Q≡Q
        _ , ⊢u₁ , ⊢u₂       = wf-⊢ u₁≡u₂′
        ⊢u₂                 = conv ⊢u₂ Q≡Q
        _ , ⊢v₁ , ⊢v₂       = wf-⊢ v₁≡v₂′
        ⊢v₂                 = conv ⊢v₂ Id≡Id
        _ , ⊢w₁ , ⊢w₂       = wf-⊢ w₁≡w₂′
        ⊢w₂                 = conv ⊢w₂ Id≡Id
        ⊩v₁ , _             = wf-⊩≡∷ v₁≡v₂
        ⊩w₁ , _             = wf-⊩≡∷ w₁≡w₂
        ⊢Q                  = wf-⊢ ⊢t₁
        ok , _              = inversion-Quot ⊢Q
        »Γ                  = defn-wf (wf ⊢Q)
        _ , ⊢set₁ , ⊢set₂   = wf-⊢ $
                              set-cong ⊢A₁[σ₁]≡A₂[σ₂] ⊢B₁[σ₁⇑²]≡B₂[σ₂⇑²]
                                t₁≡t₂′ u₁≡u₂′ v₁≡v₂′ w₁≡w₂′
    in
    case Equality-reflection? of λ where
      (no not-ok) →
        let n = Higher-quotient-constructors-neutral⇔ .proj₂
                  (ok , not-ok)
        in
        Identityᵃ→⊩≡∷Id⇔ (ne (setᵃ n)) (ne (setᵃ n)) .proj₂
          (⊢set₁ , ⊢set₂ , ⊩v₁ , ⊩w₁ ,
           ne (setᵃ n) (setᵃ n)
             (~-set-cong A₁[σ₁]≅A₂[σ₂] B₁[σ₁⇑²]≅B₂[σ₂⇑²] t₁≅t₂ u₁≅u₂
                v₁≅v₂ w₁≅w₂))
      (yes ok) →
        case Equality-reflection→Empty-con ok of λ {
          ε →
        case ⊩∷Id⇔ .proj₁ ⊩v₁ of λ {
          (_ , _ , _ , _ , ne n _) →
            ⊥-elim $
            Equality-reflection→¬Neutral-Var-included »Γ ok (ne⁻ n)
        ; (_ , v₁⇒*rfl , _ , _ , rflᵣ t₁≡u₁) →
        case ⊩∷Id⇔ .proj₁ ⊩w₁ of λ {
          (_ , _ , _ , _ , ne n _) →
            ⊥-elim $
            Equality-reflection→¬Neutral-Var-included »Γ ok (ne⁻ n)
        ; (_ , w₁⇒*rfl , _ , _ , rflᵣ _) →
            ⊩≡∷Id⇔ .proj₂
              (rfl , rfl ,
               redMany (set-η ok ⊢t₁ ⊢u₁ ⊢v₁ ⊢w₁) ,
               redMany
                 (conv (set-η ok ⊢t₂ ⊢u₂ ⊢v₂ ⊢w₂)
                    (sym (Id-cong Id≡Id v₁≡v₂′ w₁≡w₂′))) ,
               ⊩v₁ , ⊩w₁ ,
               rfl₌
                 (v₁   ⇒*⟨ v₁⇒*rfl ⟩⊩∷
                  rfl  ≡⟨ ⊩rfl≡rfl t₁≡u₁ ⟩⊩∷⇐*
                  rfl  ⇐*⟨ w₁⇒*rfl ⟩∎
                  w₁   ∎)) }}}

opaque

  -- Validity for set-cong.

  set-congᵛ :
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ₂ ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ t₁ ≡ t₂ ∷ Quot A₁ B₁ →
    Γ ⊩ᵛ⟨ ℓ₄ ⟩ u₁ ≡ u₂ ∷ Quot A₁ B₁ →
    Γ ⊩ᵛ⟨ ℓ₅ ⟩ v₁ ≡ v₂ ∷ Id (Quot A₁ B₁) t₁ u₁ →
    Γ ⊩ᵛ⟨ ℓ₅ ⟩ w₁ ≡ w₂ ∷ Id (Quot A₁ B₁) t₁ u₁ →
    Γ ⊩ᵛ⟨ ℓ₅ ⟩ set A₁ B₁ t₁ u₁ v₁ w₁ ≡ set A₂ B₂ t₂ u₂ v₂ w₂ ∷
      Id (Id (Quot A₁ B₁) t₁ u₁) v₁ w₁
  set-congᵛ A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
    let ⊩v₁ , _ = wf-⊩ᵛ≡∷ v₁≡v₂
        ⊩w₁ , _ = wf-⊩ᵛ≡∷ w₁≡w₂
    in
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( Idᵛ ⊩v₁ ⊩w₁
      , λ ∇⊇ σ₁≡σ₂ →
          ⊩set≡set (defn-wk-⊩ᵛ≡ ∇⊇ A₁≡A₂) (defn-wk ∇⊇ ⊢B₁≡B₂)
            (defn-wk-⊩ᵛ≡ ∇⊇ B₁≡B₂) σ₁≡σ₂
            (⊩ᵛ≡∷⇔ʰ .proj₁ t₁≡t₂ .proj₂ ∇⊇ σ₁≡σ₂)
            (⊩ᵛ≡∷⇔ʰ .proj₁ u₁≡u₂ .proj₂ ∇⊇ σ₁≡σ₂)
            (⊩ᵛ≡∷⇔ʰ .proj₁ v₁≡v₂ .proj₂ ∇⊇ σ₁≡σ₂)
            (⊩ᵛ≡∷⇔ʰ .proj₁ w₁≡w₂ .proj₂ ∇⊇ σ₁≡σ₂)
      )

opaque

  -- A variant of set-congᵛ.

  set-congᵛ′ :
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ A₁ ≡ A₂ →
    Quot-rel-Cons Γ A₁ ⊢ B₁ ≡ B₂ →
    Quot-rel-Cons Γ A₁ ⊩ᵛ⟨ ℓ₂ ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ t₁ ≡ t₂ ∷ Quot A₁ B₁ →
    Γ ⊩ᵛ⟨ ℓ₄ ⟩ u₁ ≡ u₂ ∷ Quot A₁ B₁ →
    Γ ⊩ᵛ⟨ ℓ₅ ⟩ v₁ ≡ v₂ ∷ Id (Quot A₁ B₁) t₁ u₁ →
    Γ ⊩ᵛ⟨ ℓ₆ ⟩ w₁ ≡ w₂ ∷ Id (Quot A₁ B₁) t₁ u₁ →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ set A₁ B₁ t₁ u₁ v₁ w₁ ≡ set A₂ B₂ t₂ u₂ v₂ w₂ ∷
      Id (Id (Quot A₁ B₁) t₁ u₁) v₁ w₁
  set-congᵛ′ A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ w₁≡w₂ =
    set-congᵛ A₁≡A₂ ⊢B₁≡B₂ B₁≡B₂ t₁≡t₂ u₁≡u₂ (emb-⊩ᵛ≡∷ ≤ᵘωᵘ·2 v₁≡v₂)
      (emb-⊩ᵛ≡∷ ≤ᵘωᵘ·2 w₁≡w₂)

opaque

  -- Validity for set.

  setᵛ :
    Γ ⊢ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₂ ⟩ t ∷ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ u ∷ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₄ ⟩ v ∷ Id (Quot A B) t u →
    Γ ⊩ᵛ⟨ ℓ₄ ⟩ w ∷ Id (Quot A B) t u →
    Γ ⊩ᵛ⟨ ℓ₄ ⟩ set A B t u v w ∷ Id (Id (Quot A B) t u) v w
  setᵛ ⊢Q ⊩Q ⊩t ⊩u ⊩v ⊩w =
    let _ , _ , ⊢B  = inversion-Quot ⊢Q
        _ , ⊩A , ⊩B = ⊩ᵛQuot→ ⊩Q
    in
    wf-⊩ᵛ≡∷
      (set-congᵛ (refl-⊩ᵛ≡ ⊩A) (refl ⊢B) (refl-⊩ᵛ≡ ⊩B) (refl-⊩ᵛ≡∷ ⊩t)
         (refl-⊩ᵛ≡∷ ⊩u) (refl-⊩ᵛ≡∷ ⊩v) (refl-⊩ᵛ≡∷ ⊩w))
      .proj₁

opaque

  -- A variant of setᵛ.

  setᵛ′ :
    Γ ⊢ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₂ ⟩ t ∷ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ u ∷ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₄ ⟩ v ∷ Id (Quot A B) t u →
    Γ ⊩ᵛ⟨ ℓ₅ ⟩ w ∷ Id (Quot A B) t u →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ set A B t u v w ∷ Id (Id (Quot A B) t u) v w
  setᵛ′ ⊢Q ⊩Q ⊩t ⊩u ⊩v ⊩w =
    setᵛ ⊢Q ⊩Q ⊩t ⊩u (emb-⊩ᵛ∷ ≤ᵘωᵘ·2 ⊩v) (emb-⊩ᵛ∷ ≤ᵘωᵘ·2 ⊩w)

------------------------------------------------------------------------
-- Validity for qrec

opaque
  unfolding Is-set-Con Quot-rel-Con Resp-Con

  -- A congruence lemma for qrec.

  ⊩qrec≡qrec :
    {σ₁ σ₂ : Subst m n} →
    Γ »∙ Quot A B ⊢ C₁ ≡ C₂ →
    Γ »∙ Quot A B ⊩ᵛ⟨ ℓ₁ ⟩ C₁ ≡ C₂ →
    Γ »∙ A ⊢ t₁ ≡ t₂ ∷ C₁ [ class (var x0) ]↑ →
    Γ »∙ A ⊩ᵛ⟨ ℓ₁ ⟩ t₁ ≡ t₂ ∷ C₁ [ class (var x0) ]↑ →
    Resp-Cons Γ A B ⊢ u₁ ≡ u₂ ∷ Resp-type A B C₁ t₁ →
    Resp-Cons Γ A B ⊩ᵛ⟨ ℓ₁ ⟩ u₁ ≡ u₂ ∷ Resp-type A B C₁ t₁ →
    Is-set-Cons Γ A B C₁ ⊢ v₁ ≡ v₂ ∷ Is-set-type C₁ →
    Is-set-Cons Γ A B C₁ ⊩ᵛ⟨ ℓ₂ ⟩ v₁ ≡ v₂ ∷ Is-set-type C₁ →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ w₁ ≡ w₂ ∷ Quot A B →
    ⦃ inc : Var-included or-empty Δ ⦄ →
    Γ .defs » Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ .vars →
    Γ .defs » Δ ⊩⟨ ℓ₁ ⟩ qrec C₁ t₁ u₁ v₁ w₁ [ σ₁ ] ≡
      qrec C₂ t₂ u₂ v₂ w₂ [ σ₂ ] ∷ C₁ [ w₁ ]₀ [ σ₁ ]
  ⊩qrec≡qrec
    {m} {Γ} {A} {B} {C₁} {C₂} {ℓ₁} {t₁} {t₂} {u₁} {u₂} {v₁} {v₂} {ℓ₃}
    {w₁} {w₂} {Δ} {σ₁} {σ₂}
    ⊢C₁≡C₂ C₁≡C₂ ⊢t₁≡t₂ t₁≡t₂ ⊢u₁≡u₂ u₁≡u₂ ⊢v₁≡v₂ v₁≡v₂ w₁≡w₂ ⦃ inc ⦄
    σ₁≡σ₂ =
    let w₁[σ₁]≡w₂[σ₂] = R.⊩≡∷→ (⊩ᵛ≡∷→⊩ˢ≡∷→⊩[]≡[]∷ w₁≡w₂ σ₁≡σ₂)
        ⊩w₁[σ₁] , _   = wf-⊩≡∷ w₁[σ₁]≡w₂[σ₂]
    in
    case ⊩≡∷Quot⇔ .proj₁ w₁[σ₁]≡w₂[σ₂] of λ
      (⊩Q , w₁′ , w₂′ , w₁[σ₁]⇒*w₁′ , w₂[σ₂]⇒*w₂′ , rest) →
    let q-ok , _      = inversion-Quot (⊢∙→⊢ (wf ⊢C₁≡C₂))
        _ , ⊩A , ⊩B   = ⊩ᵛQuot→ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ w₁≡w₂ .proj₁))
        ⊩σ₁ , _       = wf-⊩ˢ≡∷ σ₁≡σ₂
        _ , ⊢σ₁≡σ₂    = escape-⊩ˢ≡∷ σ₁≡σ₂
        _ , ⊢σ₁ , ⊢σ₂ = wf-⊢ˢʷ≡∷ ⊢σ₁≡σ₂
        ⊢Q            = ⊢∙→⊢ (wf ⊢C₁≡C₂)
        ⊢Q[σ₁]        = subst-⊢ ⊢Q ⊢σ₁
        _ , ⊢A , ⊢B   = inversion-Quot ⊢Q
        ⊩C₁ , _       = wf-⊩ᵛ≡ C₁≡C₂
        ⊢C₁ , ⊢C₂     = wf-⊢ ⊢C₁≡C₂
        ⊢C₁[σ₁⇑]      = subst-⊢-⇑ ⊢C₁ ⊢σ₁
        ⊢C₂[σ₂⇑]      = subst-⊢-⇑ ⊢C₂ ⊢σ₂
        ⊩t₁ , _       = wf-⊩ᵛ≡∷ t₁≡t₂
        _ , ⊢t₁ , ⊢t₂ = wf-⊢ ⊢t₁≡t₂
        ⊢t₁[σ₁⇑]      = PE.subst (_⊢_∷_ _ _) ([][]↑-commutes C₁) $
                        subst-⊢-⇑ ⊢t₁ ⊢σ₁
        ⊢t₂           = conv ⊢t₂ $ subst-⊢≡ ⊢C₁≡C₂ $ refl-⊢ˢʷ≡∷ $
                        ⊢ˢʷ∷-[][]↑ (class (W.wk₁ ⊢A ⊢Q) (var₀ ⊢A))
        ⊢t₂[σ₂⇑]      = PE.subst (_⊢_∷_ _ _) ([][]↑-commutes C₂) $
                        subst-⊢-⇑ ⊢t₂ ⊢σ₂
        ⊩u₁ , _       = wf-⊩ᵛ≡∷ u₁≡u₂
        _ , ⊢u₁ , ⊢u₂ = wf-⊢ ⊢u₁≡u₂
        ⊢u₁[σ₁⇑³]     = PE.subst₃ _⊢_∷_ (Resp-Con-[] (Γ .vars) A B)
                          PE.refl Resp-type-[] $
                        subst-⊢-⇑ ⊢u₁ ⊢σ₁
        ⊢u₂           = conv ⊢u₂ $
                        Resp-type-cong (refl ⊢A) (refl ⊢B) ⊢C₁≡C₂ ⊢t₁≡t₂
        ⊢u₂[σ₂⇑³]     = PE.subst₃ _⊢_∷_ (Resp-Con-[] (Γ .vars) A B)
                          PE.refl Resp-type-[] $
                        subst-⊢-⇑ ⊢u₂ ⊢σ₂
        _ , ⊢v₁ , ⊢v₂ = wf-⊢ ⊢v₁≡v₂
        ⊢v₁[σ₁⇑⁵]     = PE.subst₃ _⊢_∷_ (Is-set-Con-[] (Γ .vars) A B C₁)
                          PE.refl Is-set-type-[] $
                        subst-⊢-⇑ ⊢v₁ ⊢σ₁
        ⊢v₂           = stability
                          (Is-set-Con-cong (reflConEq (wf ⊢A)) (refl ⊢A)
                             (refl ⊢B) ⊢C₁≡C₂)
                          (conv ⊢v₂ (Is-set-type-cong ⊢C₁≡C₂))
        ⊢v₂[σ₂⇑⁵]     = PE.subst₃ _⊢_∷_ (Is-set-Con-[] (Γ .vars) A B C₂)
                          PE.refl Is-set-type-[] $
                        subst-⊢-⇑ ⊢v₂ ⊢σ₂
        w₁[σ₁]≡w₁′    = ⊩∷-⇒* w₁[σ₁]⇒*w₁′ ⊩w₁[σ₁]
        _ , ⊩w₁′      = wf-⊩≡∷ w₁[σ₁]≡w₁′

        lemma₃ :
          Γ .defs » Δ ⊢ w₁″ ∷ A [ σ₁ ] →
          Γ .defs » Δ ⊢ w₂″ ∷ A [ σ₁ ] →
          Γ .defs » Δ ⊢ class w₁″ ≡ class w₂″ ∷ Quot A B [ σ₁ ] →
          Γ .defs » Δ ⊩⟨ ℓ₁ ⟩ t₁ [ σ₁ ⇑ ] [ w₁″ ]₀ ≡
            t₂ [ σ₂ ⇑ ] [ w₂″ ]₀ ∷ C₁ [ σ₁ ⇑ ] [ class w₁″ ]₀ →
          Γ .defs » Δ ⊩⟨ ℓ₁ ⟩
            qrec (C₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ⇑ ]) (u₁ [ σ₁ ⇑[ 3 ] ])
              (v₁ [ σ₁ ⇑[ 5 ] ]) (class w₁″) ≡
            qrec (C₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ⇑ ]) (u₂ [ σ₂ ⇑[ 3 ] ])
              (v₂ [ σ₂ ⇑[ 5 ] ]) (class w₂″) ∷
            C₁ [ σ₁ ⇑ ] [ class w₁″ ]₀ ×
          Γ .defs » Δ ⊢ class w₁″ ≡ class w₂″ ∷ Quot A B [ σ₁ ]
        lemma₃
          {w₁″} {w₂″}
          ⊢w₁″ ⊢w₂″ class-w₁″≡class-w₂″ t₁[σ₁⇑][w₁″]≡t₂[σ₂⇑][w₂″] =
          let ⊢w₂″ = conv ⊢w₂″ (subst-⊢≡ ⊢A ⊢σ₁≡σ₂) in
          (qrec (C₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ⇑ ]) (u₁ [ σ₁ ⇑[ 3 ] ])
             (v₁ [ σ₁ ⇑[ 5 ] ]) (class w₁″)                     ⇒⟨ qrec-β ⊢C₁[σ₁⇑] ⊢t₁[σ₁⇑] ⊢u₁[σ₁⇑³] ⊢v₁[σ₁⇑⁵] ⊢w₁″ ⟩⊩∷

           t₁ [ σ₁ ⇑ ] [ w₁″ ]₀ ∷ C₁ [ σ₁ ⇑ ] [ class w₁″ ]₀    ≡⟨ t₁[σ₁⇑][w₁″]≡t₂[σ₂⇑][w₂″] ⟩⊩∷∷⇐*
                                                                 ⟨ subst-⊢≡₀ (subst-⊢≡-⇑ ⊢C₁≡C₂ ⊢σ₁≡σ₂) class-w₁″≡class-w₂″ ⟩⇒

           t₂ [ σ₂ ⇑ ] [ w₂″ ]₀ ∷ C₂ [ σ₂ ⇑ ] [ class w₂″ ]₀    ⇐⟨ qrec-β ⊢C₂[σ₂⇑] ⊢t₂[σ₂⇑] ⊢u₂[σ₂⇑³] ⊢v₂[σ₂⇑⁵] ⊢w₂″ ⟩∎∷

           qrec (C₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ⇑ ]) (u₂ [ σ₂ ⇑[ 3 ] ])
             (v₂ [ σ₂ ⇑[ 5 ] ]) (class w₂″)                     ∎) ,
          class-w₁″≡class-w₂″

        Lemma₂-domain : Term m → Term m → Set a
        Lemma₂-domain w₁″ w₂″ =
          Γ .defs » Δ ⊩⟨ ℓ₃ ⟩ w₁″ ∷ A [ σ₁ ] ×
          Γ .defs » Δ ⊩⟨ ℓ₃ ⟩ w₂″ ∷ A [ σ₁ ] ×
          Γ .defs » Δ ⊩⟨ ℓ₃ ⟩ class w₁″ ≡ class w₂″ ∷ Quot A B [ σ₁ ] ×
          Γ .defs » Δ ⊩⟨ ℓ₁ ⟩ t₁ [ σ₁ ⇑ ] [ w₁″ ]₀ ≡
            t₂ [ σ₂ ⇑ ] [ w₂″ ]₀ ∷ C₁ [ σ₁ ⇑ ] [ class w₁″ ]₀

        lemma₂ :
          Lemma₂-domain w₁″ w₂″ →
          Γ .defs » Δ ⊩⟨ ℓ₁ ⟩
            qrec (C₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ⇑ ]) (u₁ [ σ₁ ⇑[ 3 ] ])
              (v₁ [ σ₁ ⇑[ 5 ] ]) (class w₁″) ≡
            qrec (C₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ⇑ ]) (u₂ [ σ₂ ⇑[ 3 ] ])
              (v₂ [ σ₂ ⇑[ 5 ] ]) (class w₂″) ∷
            C₁ [ σ₁ ⇑ ] [ class w₁″ ]₀ ×
          Γ .defs » Δ ⊢ class w₁″ ≡ class w₂″ ∷ Quot A B [ σ₁ ]
        lemma₂
          (⊩w₁″ , ⊩w₂″ , class-w₁″≡class-w₂″ ,
           t₁[σ₁⇑][w₁″]≡t₂[σ₂⇑][w₂″]) =
          lemma₃ (escape-⊩∷ ⊩w₁″) (escape-⊩∷ ⊩w₂″)
            (≅ₜ-eq (escape-⊩≡∷ class-w₁″≡class-w₂″))
            t₁[σ₁⇑][w₁″]≡t₂[σ₂⇑][w₂″]

        lemma₁ :
          Γ .defs » Δ ⊩⟨ ℓ₁ ⟩
            qrec (C₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ⇑ ]) (u₁ [ σ₁ ⇑[ 3 ] ])
              (v₁ [ σ₁ ⇑[ 5 ] ]) w₁′ ≡
            qrec (C₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ⇑ ]) (u₂ [ σ₂ ⇑[ 3 ] ])
              (v₂ [ σ₂ ⇑[ 5 ] ]) w₂′ ∷
            C₁ [ σ₁ ⇑ ] [ w₁′ ]₀ ×
          Γ .defs » Δ ⊢ w₁′ ≡ w₂′ ∷ Quot A B [ σ₁ ]
        lemma₁ = case rest of λ where
          (ne w₁′-n w₂′-n w₁′~w₂′) →
            neutral-⊩≡∷ (R.⊩→ (⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ ⊩C₁ ⊩σ₁ (R.→⊩∷ ⊩w₁′)))
              (qrecᵃ w₁′-n) (qrecᵃ w₂′-n)
              (with-inc-⊢~∷
                 (qrec-cong (subst-⊢≡-⇑ ⊢C₁≡C₂ ⊢σ₁≡σ₂)
                    (PE.subst (_⊢_≡_∷_ _ _ _) ([][]↑-commutes C₁) $
                     subst-⊢≡-⇑ ⊢t₁≡t₂ ⊢σ₁≡σ₂)
                    (PE.subst₄ _⊢_≡_∷_
                       (Resp-Con-[] (Γ .vars) A B) PE.refl PE.refl
                       Resp-type-[] $
                     subst-⊢≡-⇑ ⊢u₁≡u₂ ⊢σ₁≡σ₂)
                    (PE.subst₄ _⊢_≡_∷_
                       (Is-set-Con-[] (Γ .vars) A B C₁) PE.refl PE.refl
                       Is-set-type-[] $
                     subst-⊢≡-⇑ ⊢v₁≡v₂ ⊢σ₁≡σ₂)
                    (~-eq w₁′~w₂′)) $
               ~-qrec-cong
                 (escape-⊩≡ $ R.⊩≡→ ⦃ inc = included ⦄ $
                  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] C₁≡C₂ σ₁≡σ₂)
                 (PE.subst (_⊢_≅_∷_ _ _ _) ([][]↑-commutes C₁) $
                  escape-⊩≡∷ $ R.⊩≡∷→ ⦃ inc = included ⦄ $
                  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ t₁≡t₂ σ₁≡σ₂)
                 (PE.subst₄ _⊢_≅_∷_
                    (Resp-Con-[] (Γ .vars) A B) PE.refl PE.refl
                    Resp-type-[] $
                  escape-⊩≡∷ $ R.⊩≡∷→ ⦃ inc = included ⦄ $
                  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑[]]≡[⇑[]]∷ u₁≡u₂ σ₁≡σ₂)
                 (PE.subst₄ _⊢_≅_∷_
                    (Is-set-Con-[] (Γ .vars) A B C₁) PE.refl PE.refl
                    Is-set-type-[] $
                  escape-⊩≡∷ $ R.⊩≡∷→ ⦃ inc = included ⦄ $
                  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑[]]≡[⇑[]]∷ v₁≡v₂ σ₁≡σ₂)
                 w₁′~w₂′) ,
            ~-eq w₁′~w₂′
          (equal w₁″≡w₂″) →
            let ⊢w₁″≡w₂″            = ≅ₜ-eq (escape-⊩≡∷ w₁″≡w₂″)
                _ , ⊢w₁″ , ⊢w₂″     = wf-⊢ ⊢w₁″≡w₂″
                class-w₁″≡class-w₂″ = class-cong ⊢Q[σ₁] ⊢w₁″≡w₂″
            in
            lemma₃ ⊢w₁″ ⊢w₂″ class-w₁″≡class-w₂″ $
            PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
              (PE.trans (PE.cong _[ _ ]₀ ([][]↑-commutes C₁)) $
               [][]↑-[₀⇑] 0 (C₁ [ _ ]))
              (R.⊩≡∷→ $
               ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ t₁≡t₂ σ₁≡σ₂
                 (R.→⊩≡∷ w₁″≡w₂″))
          (related ok rel) →
            case Equality-reflection→Empty-con ok of λ {
              ε →
            lemma₂ $
            Symmetric-transitive-closure-elim
              {R₂ = Lemma₂-domain}
              (λ {w₁″ w₂″} (⊩w₁″ , ⊩w₂″ , eq₁ , eq₂) →
                 ⊩w₂″ , ⊩w₁″ , sym-⊩≡∷ eq₁ ,
                 (t₁ [ σ₁ ⇑ ] [ w₂″ ]₀ ∷ C₁ [ σ₁ ⇑ ] [ class w₂″ ]₀  ≡⟨ PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) ([class-0]↑[⇑][]₀≡ C₁) $ R.⊩≡∷→ $
                                                                        ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ t₁≡t₂ σ₁≡σ₂ (R.→⊩≡∷ (refl-⊩≡∷ ⊩w₂″)) ⟩⊩∷∷
                                                                     ˘⟨ R.⊩≡→ $
                                                                        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩C₁) (refl-⊩ˢ≡∷ ⊩σ₁) (R.→⊩≡∷ eq₁) ⟩⊩∷
                  t₂ [ σ₂ ⇑ ] [ w₂″ ]₀ ∷ C₁ [ σ₁ ⇑ ] [ class w₁″ ]₀  ≡˘⟨ eq₂ ⟩⊩∷∷
                  t₁ [ σ₁ ⇑ ] [ w₁″ ]₀                               ≡⟨ PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) ([class-0]↑[⇑][]₀≡ C₁) $ R.⊩≡∷→ $
                                                                        ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ t₁≡t₂ σ₁≡σ₂ (R.→⊩≡∷ (refl-⊩≡∷ ⊩w₁″)) ⟩⊩∷∎
                  t₂ [ σ₂ ⇑ ] [ w₁″ ]₀                               ∎))
              (λ {w₁″ w₂″ w₃″}
                 (⊩w₁″ , ⊩w₂″ , eq₁ , eq₂) (_ , ⊩w₃″ , eq₃ , eq₄) →
                 ⊩w₁″ , ⊩w₃″ , trans-⊩≡∷ eq₁ eq₃ ,
                 (t₁ [ σ₁ ⇑ ] [ w₁″ ]₀ ∷ C₁ [ σ₁ ⇑ ] [ class w₁″ ]₀  ≡⟨ eq₂ ⟩⊩∷∷
                                                                      ⟨ R.⊩≡→ $
                                                                        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩C₁) (refl-⊩ˢ≡∷ ⊩σ₁) (R.→⊩≡∷ eq₁) ⟩⊩∷
                  t₂ [ σ₂ ⇑ ] [ w₂″ ]₀ ∷ C₁ [ σ₁ ⇑ ] [ class w₂″ ]₀  ≡˘⟨ PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) ([class-0]↑[⇑][]₀≡ C₁) $ R.⊩≡∷→ $
                                                                         ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ t₁≡t₂ σ₁≡σ₂ (R.→⊩≡∷ (refl-⊩≡∷ ⊩w₂″)) ⟩⊩∷∷
                  t₁ [ σ₁ ⇑ ] [ w₂″ ]₀                               ≡⟨ eq₄ ⟩⊩∷∎
                  t₂ [ σ₂ ⇑ ] [ w₃″ ]₀                               ∎))
              (λ {w₁″ w₂″} (⊩w₁″ , ⊩w₂″ , prf , ⊩prf) →
                 let ⊢w₁″                = escape-⊩∷ ⊩w₁″
                     ⊢w₂″                = escape-⊩∷ ⊩w₂″
                     class-w₁″≡class-w₂″ =
                       Equality-reflection→⊩∷Id⇔ ok .proj₁
                         (_ , ⊩resp q-ok ⊩A ⊢B ⊩B ⊩σ₁ ⊩w₁″ ⊩w₂″ ⊩prf)
                     ⊢class-w₁″≡class-w₂″ =
                       ≅ₜ-eq (escape-⊩≡∷ class-w₁″≡class-w₂″)
                 in
                 ⊩w₁″ , ⊩w₂″ , class-w₁″≡class-w₂″ ,
                 Equality-reflection→⊩∷Id⇔ ok .proj₁
                   ( u₁ [ σ₁ ⇑[ 3 ] ] [ w₁″ , w₂″ , prf ]₂₁₀
                   , conv-⊩∷
                       (Resp-type A B C₁ t₁
                          [ σ₁ ⇑[ 3 ] ] [ w₁″ , w₂″ , prf ]₂₁₀                ≡⟨ Equality-reflection→Resp-type-[]₂₁₀≡
                                                                                   ok ⊩A ⊩B ⊢C₁ ⊩C₁ ⊩t₁ ⊩σ₁ ⊩w₁″ ⊩w₂″ ⊩prf ⟩⊩
                        Id (C₁ [ σ₁ ⇑ ] [ class w₁″ ]₀)
                          (t₁ [ σ₁ ⇑ ] [ w₁″ ]₀) (t₁ [ σ₁ ⇑ ] [ w₂″ ]₀)       ≡⟨ ⊩Id≡Id⇔ .proj₂
                                                                                   ( refl-⊩≡
                                                                                       (R.⊩→ (⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ ⊩C₁ ⊩σ₁ (R.→⊩∷ (⊩class ⊩Q ⊩w₁″))))
                                                                                   , refl-⊩≡∷
                                                                                       (PE.subst (_⊩⟨_⟩_∷_ _ _ _) ([class-0]↑[⇑][]₀≡ C₁) $
                                                                                        R.⊩∷→ (⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[⇑][]₀∷ ⊩t₁ ⊩σ₁ (R.→⊩∷ ⊩w₁″)))
                                                                                   , conv-⊩≡∷
                                                                                       (R.⊩≡→ $
                                                                                        ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩C₁)
                                                                                          (refl-⊩ˢ≡∷ ⊩σ₁) (R.→⊩≡∷ (sym-⊩≡∷ class-w₁″≡class-w₂″)))
                                                                                       (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) ([class-0]↑[⇑][]₀≡ C₁)
                                                                                          (R.⊩≡∷→ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ t₁≡t₂ σ₁≡σ₂ $
                                                                                           R.→⊩≡∷ (refl-⊩≡∷ ⊩w₂″)))
                                                                                   ) ⟩⊩∎
                        Id (C₁ [ σ₁ ⇑ ] [ class w₁″ ]₀)
                          (t₁ [ σ₁ ⇑ ] [ w₁″ ]₀) (t₂ [ σ₂ ⇑ ] [ w₂″ ]₀)       ∎)
                       (R.⊩∷→ $
                        ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩∷→⊩∷→⊩[⇑³][]₂₁₀∷ ⊩u₁ ⊩σ₁ (R.→⊩∷ ⊩w₁″)
                          (R.→⊩∷ $
                           PE.subst (_⊩⟨_⟩_∷_ _ _ _)
                             (PE.sym $
                              PE.trans (PE.cong _[ _ ]₀ (wk1-liftSubst A)) $
                              wk1-sgSubst _ _)
                             ⊩w₂″)
                          (R.→⊩∷ ⊩prf))
                   ))
              rel }
    in
                               ∷ C₁ [ w₁ ]₀ [ σ₁ ]             ⟨ singleSubstLift C₁ _ ⟩⊩∷∷≡

    qrec C₁ t₁ u₁ v₁ w₁ [ σ₁ ] ∷ C₁ [ σ₁ ⇑ ] [ w₁ [ σ₁ ] ]₀  ⇒*⟨ qrec-subst* ⊢C₁[σ₁⇑] ⊢t₁[σ₁⇑] ⊢u₁[σ₁⇑³] ⊢v₁[σ₁⇑⁵] w₁[σ₁]⇒*w₁′ ⟩⊩∷∷
                                                               ⟨ R.⊩≡→ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩C₁) (refl-⊩ˢ≡∷ ⊩σ₁) $
                                                                 R.→⊩≡∷ w₁[σ₁]≡w₁′ ⟩⊩∷
    qrec (C₁ [ σ₁ ⇑ ]) (t₁ [ σ₁ ⇑ ]) (u₁ [ σ₁ ⇑[ 3 ] ])
      (v₁ [ σ₁ ⇑[ 5 ] ]) w₁′ ∷ C₁ [ σ₁ ⇑ ] [ w₁′ ]₀          ≡⟨ lemma₁ .proj₁ ⟩⊩∷∷⇐*
                                                              ⟨ subst-⊢≡₀ (subst-⊢≡-⇑ ⊢C₁≡C₂ ⊢σ₁≡σ₂)
                                                                  (trans (lemma₁ .proj₂) (sym′ (subset*Term w₂[σ₂]⇒*w₂′))) ⟩⇒
    qrec (C₂ [ σ₂ ⇑ ]) (t₂ [ σ₂ ⇑ ]) (u₂ [ σ₂ ⇑[ 3 ] ])
      (v₂ [ σ₂ ⇑[ 5 ] ]) w₂′ ∷ C₂ [ σ₂ ⇑ ] [ w₂ [ σ₂ ] ]₀    ⇐*⟨ qrec-subst* ⊢C₂[σ₂⇑] ⊢t₂[σ₂⇑] ⊢u₂[σ₂⇑³] ⊢v₂[σ₂⇑⁵]
                                                                   (conv* w₂[σ₂]⇒*w₂′ (subst-⊢≡ ⊢Q ⊢σ₁≡σ₂)) ⟩∎∷
    qrec C₂ t₂ u₂ v₂ w₂ [ σ₂ ]                               ∎

opaque

  -- Validity for qrec-cong.

  qrec-congᵛ :
    Γ »∙ Quot A B ⊢ C₁ ≡ C₂ →
    Γ »∙ Quot A B ⊩ᵛ⟨ ℓ₁ ⟩ C₁ ≡ C₂ →
    Γ »∙ A ⊢ t₁ ≡ t₂ ∷ C₁ [ class (var x0) ]↑ →
    Γ »∙ A ⊩ᵛ⟨ ℓ₁ ⟩ t₁ ≡ t₂ ∷ C₁ [ class (var x0) ]↑ →
    Resp-Cons Γ A B ⊢ u₁ ≡ u₂ ∷ Resp-type A B C₁ t₁ →
    Resp-Cons Γ A B ⊩ᵛ⟨ ℓ₁ ⟩ u₁ ≡ u₂ ∷ Resp-type A B C₁ t₁ →
    Is-set-Cons Γ A B C₁ ⊢ v₁ ≡ v₂ ∷ Is-set-type C₁ →
    Is-set-Cons Γ A B C₁ ⊩ᵛ⟨ ℓ₂ ⟩ v₁ ≡ v₂ ∷ Is-set-type C₁ →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ w₁ ≡ w₂ ∷ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ qrec C₁ t₁ u₁ v₁ w₁ ≡ qrec C₂ t₂ u₂ v₂ w₂ ∷ C₁ [ w₁ ]₀
  qrec-congᵛ ⊢C₁≡C₂ C₁≡C₂ ⊢t₁≡t₂ t₁≡t₂ ⊢u₁≡u₂ u₁≡u₂ ⊢v₁≡v₂ v₁≡v₂ w₁≡w₂ =
    ⊩ᵛ≡∷⇔ʰ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ (wf-⊩ᵛ≡ C₁≡C₂ .proj₁) (wf-⊩ᵛ≡∷ w₁≡w₂ .proj₁)
      , λ ∇′⊇ σ₁≡σ₂ →
          ⊩qrec≡qrec
            (defn-wk      ∇′⊇ ⊢C₁≡C₂)
            (defn-wk-⊩ᵛ≡  ∇′⊇ C₁≡C₂)
            (defn-wk      ∇′⊇ ⊢t₁≡t₂)
            (defn-wk-⊩ᵛ≡∷ ∇′⊇ t₁≡t₂)
            (defn-wk      ∇′⊇ ⊢u₁≡u₂)
            (defn-wk-⊩ᵛ≡∷ ∇′⊇ u₁≡u₂)
            (defn-wk      ∇′⊇ ⊢v₁≡v₂)
            (defn-wk-⊩ᵛ≡∷ ∇′⊇ v₁≡v₂)
            (defn-wk-⊩ᵛ≡∷ ∇′⊇ w₁≡w₂)
            σ₁≡σ₂
      )

opaque

  -- A variant of qrec-congᵛ.

  qrec-congᵛ′ :
    Γ »∙ Quot A B ⊢ C₁ ≡ C₂ →
    Γ »∙ Quot A B ⊩ᵛ⟨ ℓ₁ ⟩ C₁ ≡ C₂ →
    Γ »∙ A ⊢ t₁ ≡ t₂ ∷ C₁ [ class (var x0) ]↑ →
    Γ »∙ A ⊩ᵛ⟨ ℓ₂ ⟩ t₁ ≡ t₂ ∷ C₁ [ class (var x0) ]↑ →
    Resp-Cons Γ A B ⊢ u₁ ≡ u₂ ∷ Resp-type A B C₁ t₁ →
    Resp-Cons Γ A B ⊩ᵛ⟨ ℓ₃ ⟩ u₁ ≡ u₂ ∷ Resp-type A B C₁ t₁ →
    Is-set-Cons Γ A B C₁ ⊢ v₁ ≡ v₂ ∷ Is-set-type C₁ →
    Is-set-Cons Γ A B C₁ ⊩ᵛ⟨ ℓ₄ ⟩ v₁ ≡ v₂ ∷ Is-set-type C₁ →
    Γ ⊩ᵛ⟨ ℓ₅ ⟩ w₁ ≡ w₂ ∷ Quot A B →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ qrec C₁ t₁ u₁ v₁ w₁ ≡ qrec C₂ t₂ u₂ v₂ w₂ ∷ C₁ [ w₁ ]₀
  qrec-congᵛ′
    ⊢C₁≡C₂ C₁≡C₂ ⊢t₁≡t₂ t₁≡t₂ ⊢u₁≡u₂ u₁≡u₂ ⊢v₁≡v₂ v₁≡v₂ w₁≡w₂ =
    qrec-congᵛ ⊢C₁≡C₂ (emb-⊩ᵛ≡ ≤ᵘωᵘ·2 C₁≡C₂) ⊢t₁≡t₂
      (emb-⊩ᵛ≡∷ ≤ᵘωᵘ·2 t₁≡t₂) ⊢u₁≡u₂ (emb-⊩ᵛ≡∷ ≤ᵘωᵘ·2 u₁≡u₂) ⊢v₁≡v₂
      (emb-⊩ᵛ≡∷ ≤ᵘωᵘ·2 v₁≡v₂) (emb-⊩ᵛ≡∷ ≤ᵘωᵘ·2 w₁≡w₂)

opaque

  -- Validity for qrec.

  qrecᵛ :
    Γ »∙ Quot A B ⊢ C →
    Γ »∙ Quot A B ⊩ᵛ⟨ ℓ₁ ⟩ C →
    Γ »∙ A ⊢ t ∷ C [ class (var x0) ]↑ →
    Γ »∙ A ⊩ᵛ⟨ ℓ₁ ⟩ t ∷ C [ class (var x0) ]↑ →
    Resp-Cons Γ A B ⊢ u ∷ Resp-type A B C t →
    Resp-Cons Γ A B ⊩ᵛ⟨ ℓ₁ ⟩ u ∷ Resp-type A B C t →
    Is-set-Cons Γ A B C ⊢ v ∷ Is-set-type C →
    Is-set-Cons Γ A B C ⊩ᵛ⟨ ℓ₂ ⟩ v ∷ Is-set-type C →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ w ∷ Quot A B →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ qrec C t u v w ∷ C [ w ]₀
  qrecᵛ ⊢C ⊩C ⊢t ⊩t ⊢u ⊩u ⊢v ⊩v ⊩w =
    ⊩ᵛ∷⇔⊩ᵛ≡∷ .proj₂ $
    qrec-congᵛ (refl ⊢C) (refl-⊩ᵛ≡ ⊩C) (refl ⊢t) (refl-⊩ᵛ≡∷ ⊩t)
      (refl ⊢u) (refl-⊩ᵛ≡∷ ⊩u) (refl ⊢v) (refl-⊩ᵛ≡∷ ⊩v) (refl-⊩ᵛ≡∷ ⊩w)

opaque

  -- A variant of qrecᵛ.

  qrecᵛ′ :
    Γ »∙ Quot A B ⊢ C →
    Γ »∙ Quot A B ⊩ᵛ⟨ ℓ₁ ⟩ C →
    Γ »∙ A ⊢ t ∷ C [ class (var x0) ]↑ →
    Γ »∙ A ⊩ᵛ⟨ ℓ₂ ⟩ t ∷ C [ class (var x0) ]↑ →
    Resp-Cons Γ A B ⊢ u ∷ Resp-type A B C t →
    Resp-Cons Γ A B ⊩ᵛ⟨ ℓ₃ ⟩ u ∷ Resp-type A B C t →
    Is-set-Cons Γ A B C ⊢ v ∷ Is-set-type C →
    Is-set-Cons Γ A B C ⊩ᵛ⟨ ℓ₄ ⟩ v ∷ Is-set-type C →
    Γ ⊩ᵛ⟨ ℓ₅ ⟩ w ∷ Quot A B →
    Γ ⊩ᵛ⟨ ωᵘ·2 ⟩ qrec C t u v w ∷ C [ w ]₀
  qrecᵛ′ ⊢C ⊩C ⊢t ⊩t ⊢u ⊩u ⊢v ⊩v ⊩w =
    qrecᵛ ⊢C (emb-⊩ᵛ ≤ᵘωᵘ·2 ⊩C) ⊢t (emb-⊩ᵛ∷ ≤ᵘωᵘ·2 ⊩t) ⊢u
      (emb-⊩ᵛ∷ ≤ᵘωᵘ·2 ⊩u) ⊢v (emb-⊩ᵛ∷ ≤ᵘωᵘ·2 ⊩v) (emb-⊩ᵛ∷ ≤ᵘωᵘ·2 ⊩w)

opaque
  unfolding Is-set-Con Quot-rel-Con Resp-Con

  -- Validity for qrec-β.

  qrec-βᵛ :
    Γ »∙ Quot A B ⊢ C →
    Γ »∙ A ⊢ t ∷ C [ class (var x0) ]↑ →
    Γ »∙ A ⊩ᵛ⟨ ℓ₁ ⟩ t ∷ C [ class (var x0) ]↑ →
    Resp-Cons Γ A B ⊢ u ∷ Resp-type A B C t →
    Is-set-Cons Γ A B C ⊢ v ∷ Is-set-type C →
    Γ ⊢ w ∷ A →
    Γ ⊩ᵛ⟨ ℓ₃ ⟩ w ∷ A →
    Γ ⊩ᵛ⟨ ℓ₁ ⟩ qrec C t u v (class w) ≡ t [ w ]₀ ∷ C [ class w ]₀
  qrec-βᵛ {Γ} {A} {B} {C} {t} ⊢C ⊢t ⊩t ⊢u ⊢v ⊢w ⊩w =
    ⊩ᵛ∷-⇐
      (λ ∇′⊇ ⊩σ →
         let _ , ⊢σ = escape-⊩ˢ∷ ⊩σ in
         PE.subst₄ _⊢_⇒_∷_ PE.refl PE.refl
           (PE.sym (singleSubstLift t _))
           (PE.sym (singleSubstLift C _)) $
         qrec-β (subst-⊢-⇑ (defn-wk ∇′⊇ ⊢C) ⊢σ)
           (PE.subst (_⊢_∷_ _ _) ([][]↑-commutes C) $
            subst-⊢-⇑ (defn-wk ∇′⊇ ⊢t) ⊢σ)
           (PE.subst₃ _⊢_∷_
              (Resp-Con-[] (Γ .vars) A B) PE.refl Resp-type-[] $
            subst-⊢-⇑ (defn-wk ∇′⊇ ⊢u) ⊢σ)
           (PE.subst₃ _⊢_∷_
              (Is-set-Con-[] (Γ .vars) A B C) PE.refl Is-set-type-[] $
            subst-⊢-⇑ (defn-wk ∇′⊇ ⊢v) ⊢σ)
           (subst-⊢ (defn-wk ∇′⊇ ⊢w) ⊢σ))
      (PE.subst (_⊩ᵛ⟨_⟩_∷_ _ _ _) ([][]↑-[] 1 C) $
       ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ ⊩t ⊩w)
