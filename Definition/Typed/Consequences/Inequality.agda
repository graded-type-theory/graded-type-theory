------------------------------------------------------------------------
-- Inequality lemmata.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Consequences.Inequality
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant as UN
  using (Neutral)
open import Definition.Untyped.Whnf M type-variant as UW
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Function
open import Tools.Nat as Nat using (Nat)
open import Tools.Product
open import Tools.Relation
open import Tools.Empty
import Tools.PropositionalEquality as PE
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    m n : Nat
    ∇ : DCon (Term 0) _
    Γ : Cons _ _
    A B C D t u v : Term _
    V : Set a
    p p′ q q′ : M
    b : BinderMode
    s : Strength
    l l₁ l₂ : Universe-level

opaque
  unfolding _⊩⟨_⟩_≡_

  A≢B :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄
    (_⊩′⟨_⟩A_ _⊩′⟨_⟩B_ : Cons m n → Universe-level → Term n → Set a)
    (A-intr : ∀ {l} → Γ ⊩′⟨ l ⟩A A → Γ ⊩⟨ l ⟩ A)
    (B-intr : ∀ {l} → Γ ⊩′⟨ l ⟩B B → Γ ⊩⟨ l ⟩ B) →
    (∀ {l} → Γ ⊩⟨ l ⟩ A → Γ ⊩′⟨ l ⟩A A) →
    (∀ {l} → Γ ⊩⟨ l ⟩ B → Γ ⊩′⟨ l ⟩B B) →
    (∀ {l₁ l₂} {⊩A : Γ ⊩′⟨ l₁ ⟩A A} {⊩B : Γ ⊩′⟨ l₂ ⟩B B} →
     ¬ ShapeView Γ l₁ l₂ A B (A-intr ⊩A) (B-intr ⊩B)) →
    ¬ Γ ⊢ A ≡ B
  A≢B _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B =
    let _ , ⊩A , ⊩B , A≡B = reducible-⊩≡ A≡B
        ⊩A′               = A-elim ⊩A
        ⊩B′               = B-elim ⊩B
        A≡B′              = irrelevanceEq ⊩A (A-intr ⊩A′) A≡B
    in
    A≢B′ (goodCases (A-intr ⊩A′) (B-intr ⊩B′) A≡B′)

opaque

  -- Applications of U are not definitionally equal to ℕ (given a
  -- certain assumption).

  U≢ℕ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ U l ≡ ℕ
  U≢ℕ =
    A≢B _⊩′⟨_⟩U_ (λ Γ _ A → Γ ⊩ℕ A) Uᵣ ℕᵣ
      U-elim ℕ-elim (λ ())

opaque

  -- Applications of U are not definitionally equal to Empty (given a
  -- certain assumption).

  U≢Emptyⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ U l ≡ Empty
  U≢Emptyⱼ =
    A≢B _⊩′⟨_⟩U_ (λ Γ _ A → Γ ⊩Empty A) Uᵣ Emptyᵣ
      U-elim Empty-elim (λ ())

opaque

  -- Applications of U are not definitionally equal to applications of
  -- Unit (given a certain assumption).

  U≢Unitⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ U l₁ ≡ Unit s l₂
  U≢Unitⱼ {s} =
    A≢B _⊩′⟨_⟩U_ _⊩Unit⟨_, s ⟩_ Uᵣ Unitᵣ
      U-elim Unit-elim (λ ())

opaque

  -- ℕ and Empty are not definitionally equal (given a certain
  -- assumption).

  ℕ≢Emptyⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ ℕ ≡ Empty
  ℕ≢Emptyⱼ =
    A≢B (λ Γ _ A → Γ ⊩ℕ A) (λ Γ _ A → Γ ⊩Empty A) ℕᵣ Emptyᵣ
      ℕ-elim Empty-elim (λ ())

opaque

  -- If equality reflection is allowed, then there is a context for
  -- which ℕ is judgementally equal to Empty.
  --
  -- Similar counterexamples could presumably be constructed for some
  -- of the other lemmas in this module.

  ℕ≡Empty :
    Equality-reflection →
    » ∇ →
    ∃ λ (Γ : Con Term 1) → ∇ » Γ ⊢ ℕ ≡ Empty
  ℕ≡Empty ok »∇ =
    ε ∙ Id (U 0) ℕ Empty ,
    univ
      (equality-reflection′ ok $
       var₀ (Idⱼ′ (ℕⱼ (ε »∇)) (Emptyⱼ (ε »∇))))

opaque

  -- ℕ is not definitionally equal to applications of Unit (given a
  -- certain assumption).

  ℕ≢Unitⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ ℕ ≡ Unit s l
  ℕ≢Unitⱼ {s} =
    A≢B (λ Γ _ A → Γ ⊩ℕ A) _⊩Unit⟨_, s ⟩_ ℕᵣ Unitᵣ
      ℕ-elim Unit-elim (λ ())

opaque

  -- Empty is not definitionally equal to applications of Unit (given
  -- a certain assumption).

  Empty≢Unitⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Empty ≡ Unit s l
  Empty≢Unitⱼ {s} =
    A≢B (λ Γ _ A → Γ ⊩Empty A) _⊩Unit⟨_, s ⟩_ Emptyᵣ Unitᵣ
      Empty-elim Unit-elim (λ ())

opaque

  -- Applications of U are not definitionally equal to applications of
  -- ΠΣ⟨_⟩_,_▷_▹_ (given a certain assumption).

  U≢ΠΣⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ U l ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  U≢ΠΣⱼ =
    let b = _ in
    A≢B _⊩′⟨_⟩U_ _⊩′⟨_⟩B⟨ b ⟩_ Uᵣ (Bᵣ _)
      U-elim B-elim (λ ())

opaque

  -- Applications of U are not definitionally equal to neutral terms
  -- (given a certain assumption).

  U≢ne :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Neutral V (Γ .defs) A → ¬ Γ ⊢ U l ≡ A
  U≢ne A-ne =
    A≢B _⊩′⟨_⟩U_ (λ Γ _ A → Γ ⊩ne A) Uᵣ ne
      U-elim (ne-elim A-ne) (λ ())

opaque

  -- ℕ is not definitionally equal to applications of ΠΣ⟨_⟩_,_▷_▹_
  -- (given a certain assumption).

  ℕ≢ΠΣⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ ℕ ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  ℕ≢ΠΣⱼ =
    let b = _ in
    A≢B (λ Γ _ A → Γ ⊩ℕ A) _⊩′⟨_⟩B⟨ b ⟩_ ℕᵣ (Bᵣ _)
      ℕ-elim B-elim (λ ())

opaque

  -- Empty is not definitionally equal to applications of ΠΣ⟨_⟩_,_▷_▹_
  -- (given a certain assumption).

  Empty≢ΠΣⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Empty ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  Empty≢ΠΣⱼ =
    let b = _ in
    A≢B (λ Γ _ A → Γ ⊩Empty A) _⊩′⟨_⟩B⟨ b ⟩_ Emptyᵣ (Bᵣ _)
      Empty-elim B-elim (λ ())

opaque

  -- Applications of Unit are not definitionally equal to applications
  -- of ΠΣ⟨_⟩_,_▷_▹_ (given a certain assumption).

  Unit≢ΠΣⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Unit s l ≡ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C
  Unit≢ΠΣⱼ {s} =
    let b = _ in
    A≢B _⊩Unit⟨_, s ⟩_ _⊩′⟨_⟩B⟨ b ⟩_ Unitᵣ (Bᵣ _)
      Unit-elim B-elim (λ ())

opaque

  -- ℕ is not definitionally equal to neutral terms (given a certain
  -- assumption).

  ℕ≢ne :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Neutral V (Γ .defs) A → ¬ Γ ⊢ ℕ ≡ A
  ℕ≢ne A-ne =
    A≢B (λ Γ _ A → Γ ⊩ℕ A) (λ Γ _ A → Γ ⊩ne A) ℕᵣ ne
      ℕ-elim (ne-elim A-ne) (λ ())

opaque

  -- Empty is not definitionally equal to neutral terms (given a
  -- certain assumption).

  Empty≢neⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Neutral V (Γ .defs) A → ¬ Γ ⊢ Empty ≡ A
  Empty≢neⱼ A-ne =
    A≢B (λ Γ _ A → Γ ⊩Empty A) (λ Γ _ A → Γ ⊩ne A) Emptyᵣ ne
      Empty-elim (ne-elim A-ne) (λ ())

opaque

  -- Applications of Unit are not definitionally equal to neutral
  -- terms (given a certain assumption).

  Unit≢neⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Neutral V (Γ .defs) A → ¬ Γ ⊢ Unit s l ≡ A
  Unit≢neⱼ {s} A-ne =
    A≢B _⊩Unit⟨_, s ⟩_ (λ Γ _ A → Γ ⊩ne A) Unitᵣ ne
      Unit-elim (ne-elim A-ne) (λ ())

opaque

  -- Applications of ΠΣ⟨_⟩_,_▷_▹_ are not definitionally equal to
  -- neutral terms (given a certain assumption).

  ΠΣ≢ne :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Neutral V (Γ .defs) C → ¬ Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C
  ΠΣ≢ne C-ne =
    let b = _ in
    A≢B _⊩′⟨_⟩B⟨ b ⟩_ (λ Γ _ A → Γ ⊩ne A) (Bᵣ _) ne
      B-elim (ne-elim C-ne) (λ ())

opaque

  -- Applications of Π_,_▷_▹_ are not definitionally equal to
  -- applications of Σ⟨_⟩_,_▷_▹_ (given a certain assumption).

  Π≢Σⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Π p , q ▷ A ▹ B ≡ Σ⟨ s ⟩ p′ , q′ ▷ C ▹ D
  Π≢Σⱼ =
    let b₁ = _
        b₂ = _
    in
    A≢B _⊩′⟨_⟩B⟨ b₁ ⟩_ _⊩′⟨_⟩B⟨ b₂ ⟩_ (Bᵣ _) (Bᵣ _)
      B-elim B-elim (λ ())

opaque

  -- Applications of Σˢ_,_▷_▹_ are not definitionally equal to
  -- applications of Σʷ_,_▷_▹_ (given a certain assumption).

  Σˢ≢Σʷⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Σˢ p , q ▷ A ▹ B ≡ Σʷ p′ , q′ ▷ C ▹ D
  Σˢ≢Σʷⱼ =
    let b₁ = _
        b₂ = _
    in
    A≢B _⊩′⟨_⟩B⟨ b₁ ⟩_ _⊩′⟨_⟩B⟨ b₂ ⟩_ (Bᵣ _) (Bᵣ _)
      B-elim B-elim (λ ())

opaque

  -- Applications of Unitʷ are not definitionally equal to
  -- applications of Unitˢ (given a certain assumption).

  Unitʷ≢Unitˢ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Unitʷ l₁ ≡ Unitˢ l₂
  Unitʷ≢Unitˢ =
    A≢B _⊩Unit⟨_, 𝕨 ⟩_ _⊩Unit⟨_, 𝕤 ⟩_ Unitᵣ Unitᵣ
      Unit-elim Unit-elim (λ ())

opaque

  -- Applications of Id are not definitionally equal to neutral types
  -- (given a certain assumption).

  Id≢ne :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Neutral V (Γ .defs) B → ¬ Γ ⊢ Id A t u ≡ B
  Id≢ne B-ne =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩ne A) Idᵣ ne
      Id-elim (ne-elim B-ne) (λ ())

opaque

  -- Applications of Id are not definitionally equal to applications
  -- of U (given a certain assumption).

  Id≢U :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Id A t u ≡ U l
  Id≢U =
    A≢B _⊩′⟨_⟩Id_ _⊩′⟨_⟩U_ Idᵣ Uᵣ
      Id-elim U-elim (λ ())

opaque

  -- Applications of Id are not definitionally equal to ℕ (given a
  -- certain assumption).

  Id≢ℕ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Id A t u ≡ ℕ
  Id≢ℕ =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩ℕ A) Idᵣ ℕᵣ
      Id-elim ℕ-elim (λ ())

opaque

  -- Applications of Id are not definitionally equal to applications
  -- of Unit (given a certain assumption).

  Id≢Unit :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Id A t u ≡ Unit s l
  Id≢Unit {s} =
    A≢B _⊩′⟨_⟩Id_ _⊩Unit⟨_, s ⟩_ Idᵣ Unitᵣ
      Id-elim Unit-elim (λ ())

opaque

  -- Applications of Id are not definitionally equal to Empty (given a
  -- certain assumption).

  Id≢Empty :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Id A t u ≡ Empty
  Id≢Empty =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩Empty A) Idᵣ Emptyᵣ
      Id-elim Empty-elim (λ ())

opaque

  -- Applications of Id are not definitionally equal to applications
  -- of ΠΣ⟨_⟩_,_▷_▹_ (given a certain assumption).

  Id≢ΠΣ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Id A t u ≡ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C
  Id≢ΠΣ =
    let b = _ in
    A≢B _⊩′⟨_⟩Id_ _⊩′⟨_⟩B⟨ b ⟩_ Idᵣ (Bᵣ _)
      Id-elim B-elim (λ ())

-- If No-η-equality A holds, then A is not a Π-type (given a certain
-- assumption).

No-η-equality→≢Π :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  No-η-equality (Γ .defs) A → Γ ⊢ A ≡ Π p , q ▷ B ▹ C → ⊥
No-η-equality→≢Π = λ where
  Uₙ         U≡Π     → U≢ΠΣⱼ U≡Π
  Σʷₙ        Σʷ≡Π    → Π≢Σⱼ (sym Σʷ≡Π)
  Emptyₙ     Empty≡Π → Empty≢ΠΣⱼ Empty≡Π
  ℕₙ         ℕ≡Π     → ℕ≢ΠΣⱼ ℕ≡Π
  Idₙ        Id≡Π    → Id≢ΠΣ Id≡Π
  (Unitʷₙ _) Unit≡Π  → Unit≢ΠΣⱼ Unit≡Π
  (neₙ A-ne) A≡Π     → ΠΣ≢ne A-ne (sym A≡Π)

-- If No-η-equality A holds, then A is not a Σ-type with η-equality
-- (given a certain assumption).

No-η-equality→≢Σˢ :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  No-η-equality (Γ .defs) A → Γ ⊢ A ≡ Σˢ p , q ▷ B ▹ C → ⊥
No-η-equality→≢Σˢ = λ where
  Uₙ         U≡Σ     → U≢ΠΣⱼ U≡Σ
  Σʷₙ        Σʷ≡Σ    → Σˢ≢Σʷⱼ (sym Σʷ≡Σ)
  Emptyₙ     Empty≡Σ → Empty≢ΠΣⱼ Empty≡Σ
  ℕₙ         ℕ≡Σ     → ℕ≢ΠΣⱼ ℕ≡Σ
  Idₙ        Id≡Σ    → Id≢ΠΣ Id≡Σ
  (Unitʷₙ _) Unit≡Σ  → Unit≢ΠΣⱼ Unit≡Σ
  (neₙ A-ne) A≡Σ     → ΠΣ≢ne A-ne (sym A≡Σ)

-- If No-η-equality A holds, then A is not a unit type with η-equality
-- (given a certain assumption).

No-η-equality→≢Unit :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  No-η-equality (Γ .defs) A → Γ ⊢ A ≡ Unit s l → ¬ Unit-with-η s
No-η-equality→≢Unit = λ where
  Uₙ            U≡Unit      _              → U≢Unitⱼ U≡Unit
  Σʷₙ           Σʷ≡Unit     _              → Unit≢ΠΣⱼ (sym Σʷ≡Unit)
  Emptyₙ        Empty≡Unit  _              → Empty≢Unitⱼ Empty≡Unit
  ℕₙ            ℕ≡Unit      _              → ℕ≢Unitⱼ ℕ≡Unit
  Idₙ           Id≡Unit     _              → Id≢Unit Id≡Unit
  (Unitʷₙ _)    Unitʷ≡Unitˢ (inj₁ PE.refl) → Unitʷ≢Unitˢ Unitʷ≡Unitˢ
  (Unitʷₙ no-η) _           (inj₂ η)       → no-η η
  (neₙ A-ne)    A≡Unit      _              → Unit≢neⱼ A-ne
                                                 (sym A≡Unit)

-- If A is a type without η-equality, then a non-neutral WHNF is not
-- definitionally equal at type A to any neutral term (given a certain
-- assumption).

whnf≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  (No-equality-reflection → V) →
  No-η-equality (Γ .defs) A → Whnf (Γ .defs) t →
  ¬ Neutral V (Γ .defs) t → Neutral V (Γ .defs) u →
  ¬ Γ ⊢ t ≡ u ∷ A
whnf≢ne {Γ} {V} {A} {t} {u} →V ¬-A-η t-whnf ¬-t-ne u-ne t≡u =
  case reducible-⊩≡∷ t≡u of λ
    (_ , t≡u) →
  case wf-⊩∷ $ wf-⊩≡∷ t≡u .proj₁ of λ
    ⊩A →
  lemma ⊩A (⊩≡∷→⊩≡∷/ ⊩A t≡u)
  where
  A⇒*no-η : Γ ⊢ A ⇒* B → No-η-equality (Γ .defs) B
  A⇒*no-η A⇒*B =
    case whnfRed* A⇒*B (No-η-equality→Whnf ¬-A-η) of λ {
      PE.refl →
    ¬-A-η }

  ¬t⇒*ne : Γ ⊢ t ⇒* v ∷ B → ¬ Neutralₗ (Γ .defs) v
  ¬t⇒*ne t⇒*v v-ne =
    case whnfRed*Term t⇒*v t-whnf of λ {
      PE.refl →
    ¬-t-ne (UN.ne→ →V v-ne) }

  u⇒*ne : Γ ⊢ u ⇒* v ∷ B → Neutral V (Γ .defs) v
  u⇒*ne u⇒*v =
    case whnfRed*Term u⇒*v (ne-whnf u-ne) of λ {
      PE.refl →
    u-ne }

  lemma : ([A] : Γ ⊩⟨ l ⟩ A) → ¬ Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
  lemma = λ where
    (ℕᵣ _) (ℕₜ₌ _ _ _ u⇒*zero _ zeroᵣ) →
      UN.zero≢ne (u⇒*ne u⇒*zero) PE.refl
    (ℕᵣ _) (ℕₜ₌ _ _ _ u⇒*suc _ (sucᵣ _)) →
      UN.suc≢ne (u⇒*ne u⇒*suc) PE.refl
    (ℕᵣ _) (ℕₜ₌ _ _ t⇒*v _ _ (ne (neNfₜ₌ v-ne _ _))) →
      ¬t⇒*ne t⇒*v v-ne
    (Emptyᵣ _) (Emptyₜ₌ _ _ t⇒*v _ _ (ne (neNfₜ₌ v-ne _ _))) →
      ¬t⇒*ne t⇒*v v-ne
    (Unitᵣ′ _ _ A⇒*Unit _) (Unitₜ₌ _ _ (d , _) (d′ , _) prop) →
      case A⇒*no-η A⇒*Unit of λ where
        (UW.neₙ ())
        (UW.Unitʷₙ no-η) → case prop of λ where
          (Unitₜ₌ʷ starᵣ _) →
            UN.star≢ne (u⇒*ne d′) PE.refl
          (Unitₜ₌ʷ (ne (neNfₜ₌ neK _ _)) _) →
            ¬t⇒*ne d neK
          (Unitₜ₌ˢ η) →
            no-η (Unit-with-η-𝕨→Unitʷ-η η)
    (ne _) (neₜ₌ _ _ t⇒*v _ (neNfₜ₌ v-ne _ _)) →
      ¬t⇒*ne t⇒*v v-ne
    (Bᵣ BΠ! (Bᵣ _ _ A⇒*Π _ _ _ _ _)) _ →
      case A⇒*no-η A⇒*Π of λ where
        (neₙ ())
    (Bᵣ BΣˢ (Bᵣ _ _ A⇒*Σ _ _ _ _ _)) _ →
      case A⇒*no-η A⇒*Σ of λ where
        (UW.neₙ ())
    (Bᵣ BΣʷ record{}) (_ , _ , _ , u⇒*w , _ , _ , UW.prodₙ , _) →
      UN.prod≢ne (u⇒*ne u⇒*w) PE.refl
    (Bᵣ BΣʷ record{}) (_ , _ , t⇒*v , _ , _ , UW.ne v-ne , _) →
      ¬t⇒*ne t⇒*v v-ne
    (Bᵣ BΣʷ record{}) (_ , _ , _ , _ , _ , UW.prodₙ , UW.ne _  , ())
    (Idᵣ ⊩Id) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) →
      case ⊩Id≡∷-view-inhabited ⊩Id t≡u of λ where
        (ne t′-ne _ _) → ¬t⇒*ne t⇒*t′ t′-ne
        (rfl₌ _)       → UN.rfl≢ne (u⇒*ne u⇒*u′) PE.refl
    (Uᵣ _) (Uₜ₌ _ _ t⇒*A u⇒*B A-type B-type A≡B _ _ _) →
      case B-type of λ where
        UW.Uₙ        → UN.U≢ne     (u⇒*ne u⇒*B) PE.refl
        UW.ΠΣₙ       → UN.ΠΣ≢ne _  (u⇒*ne u⇒*B) PE.refl
        UW.ℕₙ        → UN.ℕ≢ne     (u⇒*ne u⇒*B) PE.refl
        UW.Emptyₙ    → UN.Empty≢ne (u⇒*ne u⇒*B) PE.refl
        UW.Unitₙ     → UN.Unit≢ne  (u⇒*ne u⇒*B) PE.refl
        UW.Idₙ       → UN.Id≢ne    (u⇒*ne u⇒*B) PE.refl
        (UW.ne B-ne) → case A-type of λ where
          (UW.ne A-ne) → ⊥-elim (¬t⇒*ne t⇒*A A-ne)
          UW.Uₙ        → U≢ne      B-ne (univ A≡B)
          UW.ΠΣₙ       → ΠΣ≢ne     B-ne (univ A≡B)
          UW.ℕₙ        → ℕ≢ne      B-ne (univ A≡B)
          UW.Emptyₙ    → Empty≢neⱼ B-ne (univ A≡B)
          UW.Unitₙ     → Unit≢neⱼ  B-ne (univ A≡B)
          UW.Idₙ       → Id≢ne     B-ne (univ A≡B)

-- The term zero is not definitionally equal (at type ℕ) to any
-- neutral term (given a certain assumption).

zero≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  (No-equality-reflection → V) → Neutral V (Γ .defs) t →
  ¬ Γ ⊢ zero ≡ t ∷ ℕ
zero≢ne →V = whnf≢ne →V ℕₙ zeroₙ (λ ())

-- The term suc t is not definitionally equal (at type ℕ) to any
-- neutral term (given a certain assumption).

suc≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  (No-equality-reflection → V) → Neutral V (Γ .defs) u →
  ¬ Γ ⊢ suc t ≡ u ∷ ℕ
suc≢ne →V = whnf≢ne →V ℕₙ sucₙ (λ ())

-- The term starʷ l is not definitionally equal (at type Unitʷ l) to
-- any neutral term (given certain assumptions).

starʷ≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  ¬ Unitʷ-η → (No-equality-reflection → V) → Neutral V (Γ .defs) t →
  ¬ Γ ⊢ starʷ l ≡ t ∷ Unitʷ l
starʷ≢ne no-η →V = whnf≢ne →V (UW.Unitʷₙ no-η) UW.starₙ (λ ())

-- The term prodʷ p t u is not definitionally equal (at type
-- Σʷ p , q ▷ A ▹ B) to any neutral term (given a certain assumption).

prodʷ≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  (No-equality-reflection → V) → Neutral V (Γ .defs) v →
  ¬ Γ ⊢ prodʷ p t u ≡ v ∷ Σʷ p , q ▷ A ▹ B
prodʷ≢ne →V = whnf≢ne →V Σʷₙ prodₙ (λ ())

-- The term rfl is not definitionally equal (at type Id A t u) to any
-- neutral term (given a certain assumption).

rfl≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  (No-equality-reflection → V) → Neutral V (Γ .defs) v →
  ¬ Γ ⊢ rfl ≡ v ∷ Id A t u
rfl≢ne →V = whnf≢ne →V Idₙ rflₙ (λ ())
