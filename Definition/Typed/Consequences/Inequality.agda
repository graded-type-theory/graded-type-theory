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
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Neutral M type-variant as U
  using (Neutral)
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties.Primitive R
open import Definition.LogicalRelation.Properties.Whnf R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Substitution.Introductions.Level R

open import Tools.Fin
open import Tools.Function
import Tools.Level as L
open import Tools.Nat as Nat using (Nat; 1+; 1+n≢n)
open import Tools.Product
open import Tools.Relation
open import Tools.Empty
open import Tools.PropositionalEquality as PE using (_≢_)
open import Tools.Reasoning.PropositionalEquality
open import Tools.Sum using (inj₁; inj₂)
open import Tools.Unit

private
  variable
    m n : Nat
    ∇ : DCon (Term 0) _
    Γ : Cons _ _
    A B C D t u v : Term _
    l l₁ l₂ : Lvl _
    V : Set a
    p p′ q q′ : M
    b : BinderMode
    s : Strength

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

  -- Applications of U are not definitionally equal to Level (given a
  -- certain assumption).

  U≢Level :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ U l ≡ Level
  U≢Level =
    A≢B _⊩′⟨_⟩U_ (λ Γ _ A → Γ ⊩Level A) Uᵣ Levelᵣ
      U-elim Level-elim (λ ())

opaque

  -- Neutral types are atomic neutral (given a certain assumption).

  Neutral→Neutralᵃ-⊢ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Γ ⊢ A → Neutral V (Γ .defs) A → Neutralᵃ V (Γ .defs) A
  Neutral→Neutralᵃ-⊢ ⊢A A-ne =
    ne A-ne λ where
      is-supᵘ →
        case ⊢A of λ {
          (univ ⊢A) →
        let _ , _ , U≡Level = inversion-supᵘ ⊢A in
        U≢Level U≡Level }

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
    ¬ Γ ⊢ U l ≡ Unit s
  U≢Unitⱼ {s} =
    A≢B _⊩′⟨_⟩U_ (λ Γ _ A → Γ ⊩Unit⟨ s ⟩ A) Uᵣ Unitᵣ
      U-elim Unit-elim (λ ())

opaque

  -- Applications of U are not definitionally equal to applications of
  -- Unit (given a certain assumption).

  U≢Liftⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ U l₁ ≡ Lift l₂ A
  U≢Liftⱼ =
    A≢B _⊩′⟨_⟩U_ _⊩′⟨_⟩Lift_ Uᵣ Liftᵣ
      U-elim Lift-elim (λ ())

opaque

  -- Applications of Lift are not definitionally equal to Level (given a
  -- certain assumption).

  Lift≢Level :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Lift l A ≡ Level
  Lift≢Level =
    A≢B _⊩′⟨_⟩Lift_ (λ Γ _ A → Γ ⊩Level A) Liftᵣ Levelᵣ
      Lift-elim Level-elim (λ ())

opaque

  -- Applications of Lift are not definitionally equal to ℕ (given a
  -- certain assumption).

  Lift≢ℕ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Lift l A ≡ ℕ
  Lift≢ℕ =
    A≢B _⊩′⟨_⟩Lift_ (λ Γ _ A → Γ ⊩ℕ A) Liftᵣ ℕᵣ
      Lift-elim ℕ-elim (λ ())

opaque

  -- Applications of Lift are not definitionally equal to Empty (given a
  -- certain assumption).

  Lift≢Emptyⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Lift l A ≡ Empty
  Lift≢Emptyⱼ =
    A≢B _⊩′⟨_⟩Lift_ (λ Γ _ A → Γ ⊩Empty A) Liftᵣ Emptyᵣ
      Lift-elim Empty-elim (λ ())

opaque

  -- Applications of Lift are not definitionally equal to applications of
  -- Unit (given a certain assumption).

  Lift≢Unitⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Lift l A ≡ Unit s
  Lift≢Unitⱼ {s} =
    A≢B _⊩′⟨_⟩Lift_ (λ Γ _ A → Γ ⊩Unit⟨ s ⟩ A) Liftᵣ Unitᵣ
      Lift-elim Unit-elim (λ ())

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
    ε ∙ Id U₀ ℕ Empty ,
    univ
      (equality-reflection′ ok $
       var₀ (Idⱼ′ (ℕⱼ (ε »∇)) (Emptyⱼ (ε »∇))))

opaque

  -- ℕ is not definitionally equal to applications of Unit (given a
  -- certain assumption).

  ℕ≢Unitⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ ℕ ≡ Unit s
  ℕ≢Unitⱼ {s} =
    A≢B (λ Γ _ A → Γ ⊩ℕ A) (λ Γ _ A → Γ ⊩Unit⟨ s ⟩ A) ℕᵣ Unitᵣ
      ℕ-elim Unit-elim (λ ())

opaque

  -- Empty is not definitionally equal to applications of Unit (given
  -- a certain assumption).

  Empty≢Unitⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Empty ≡ Unit s
  Empty≢Unitⱼ {s} =
    A≢B (λ Γ _ A → Γ ⊩Empty A) (λ Γ _ A → Γ ⊩Unit⟨ s ⟩ A) Emptyᵣ Unitᵣ
      Empty-elim Unit-elim (λ ())

opaque

  -- Level is not definitionally equal to neutral terms (given a certain
  -- assumption).

  Level≢ne :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Neutral V (Γ .defs) A → ¬ Γ ⊢ Level ≡ A
  Level≢ne A-ne =
    A≢B (λ Γ _ A → Γ ⊩Level A) (λ Γ _ A → Γ ⊩ne A) Levelᵣ ne
      Level-elim (ne-elim A-ne) (λ ())

opaque

  -- Level is not definitionally equal to Empty (given a certain
  -- assumption).

  Level≢Empty :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Level ≡ Empty
  Level≢Empty =
    A≢B (λ Γ _ A → Γ ⊩Level A) (λ Γ _ A → Γ ⊩Empty A) Levelᵣ Emptyᵣ
      Level-elim Empty-elim (λ ())

opaque

  -- Level is not definitionally equal to applications of Unit (given
  -- a certain assumption).

  Level≢Unitⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Level ≡ Unit s
  Level≢Unitⱼ {s} =
    A≢B (λ Γ _ A → Γ ⊩Level A) (λ Γ _ A → Γ ⊩Unit⟨ s ⟩ A) Levelᵣ Unitᵣ
      Level-elim Unit-elim (λ ())

opaque

  -- Level is not definitionally equal to applications of ΠΣ⟨_⟩_,_▷_▹_
  -- (given a certain assumption).

  Level≢ΠΣⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Level ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  Level≢ΠΣⱼ =
    let b = _ in
    A≢B (λ Γ _ A → Γ ⊩Level A) _⊩′⟨_⟩B⟨ b ⟩_ Levelᵣ (Bᵣ _)
      Level-elim B-elim (λ ())

opaque

  -- Level is not definitionally equal to ℕ (given a certain
  -- assumption).

  Level≢ℕ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Level ≡ ℕ
  Level≢ℕ =
    A≢B (λ Γ _ A → Γ ⊩Level A) (λ Γ _ A → Γ ⊩ℕ A) Levelᵣ ℕᵣ
      Level-elim ℕ-elim (λ ())

opaque

  -- Level is not definitionally equal to applications of Id (given a
  -- certain assumption).

  Level≢Id :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Level ≡ Id A t u
  Level≢Id =
    A≢B (λ Γ _ A → Γ ⊩Level A) _⊩′⟨_⟩Id_ Levelᵣ Idᵣ
      Level-elim Id-elim (λ ())

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

  -- Applications of Lift are not definitionally equal to applications of
  -- ΠΣ⟨_⟩_,_▷_▹_ (given a certain assumption).

  Lift≢ΠΣⱼ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Lift l C ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  Lift≢ΠΣⱼ =
    let b = _ in
    A≢B _⊩′⟨_⟩Lift_ _⊩′⟨_⟩B⟨ b ⟩_ Liftᵣ (Bᵣ _)
      Lift-elim B-elim (λ ())

opaque

  -- Applications of Lift are not definitionally equal to neutral terms
  -- (given a certain assumption).

  Lift≢ne :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    Neutral V (Γ .defs) A → ¬ Γ ⊢ Lift l C ≡ A
  Lift≢ne A-ne =
    A≢B _⊩′⟨_⟩Lift_ (λ Γ _ A → Γ ⊩ne A) Liftᵣ ne
      Lift-elim (ne-elim A-ne) (λ ())

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
    ¬ Γ ⊢ Unit s ≡ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C
  Unit≢ΠΣⱼ {s} =
    let b = _ in
    A≢B (λ Γ _ A → Γ ⊩Unit⟨ s ⟩ A) _⊩′⟨_⟩B⟨ b ⟩_ Unitᵣ (Bᵣ _)
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
    Neutral V (Γ .defs) A → ¬ Γ ⊢ Unit s ≡ A
  Unit≢neⱼ {s} A-ne =
    A≢B (λ Γ _ A → Γ ⊩Unit⟨ s ⟩ A) (λ Γ _ A → Γ ⊩ne A) Unitᵣ ne
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
    ¬ Γ ⊢ Unitʷ ≡ Unitˢ
  Unitʷ≢Unitˢ =
    A≢B (λ Γ _ A → Γ ⊩Unit⟨ 𝕨 ⟩ A) (λ Γ _ A → Γ ⊩Unit⟨ 𝕤 ⟩ A) Unitᵣ Unitᵣ
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

  -- Applications of Id are not definitionally equal to Level (given a
  -- certain assumption).

  Id≢Level :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Id A t u ≡ Level
  Id≢Level =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩Level A) Idᵣ Levelᵣ
      Id-elim Level-elim (λ ())

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

  -- Applications of Id are not definitionally equal to applications
  -- of Lift (given a certain assumption).

  Id≢Lift :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ Id A t u ≡ Lift l B
  Id≢Lift =
    A≢B _⊩′⟨_⟩Id_ _⊩′⟨_⟩Lift_ Idᵣ Liftᵣ
      Id-elim Lift-elim (λ ())

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
    ¬ Γ ⊢ Id A t u ≡ Unit s
  Id≢Unit {s} =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩Unit⟨ s ⟩ A) Idᵣ Unitᵣ
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
  Levelₙ     Level≡Π → Level≢ΠΣⱼ Level≡Π
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
  Levelₙ     Level≡Σ → Level≢ΠΣⱼ Level≡Σ
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
  No-η-equality (Γ .defs) A → Γ ⊢ A ≡ Unit s → ¬ Unit-with-η s
No-η-equality→≢Unit = λ where
  Levelₙ        Level≡Unit  _              → Level≢Unitⱼ Level≡Unit
  Uₙ            U≡Unit      _              → U≢Unitⱼ U≡Unit
  Σʷₙ           Σʷ≡Unit     _              → Unit≢ΠΣⱼ (sym Σʷ≡Unit)
  Emptyₙ        Empty≡Unit  _              → Empty≢Unitⱼ Empty≡Unit
  ℕₙ            ℕ≡Unit      _              → ℕ≢Unitⱼ ℕ≡Unit
  Idₙ           Id≡Unit     _              → Id≢Unit Id≡Unit
  (Unitʷₙ _)    Unitʷ≡Unitˢ (inj₁ PE.refl) → Unitʷ≢Unitˢ Unitʷ≡Unitˢ
  (Unitʷₙ no-η) _           (inj₂ η)       → no-η η
  (neₙ A-ne)    A≡Unit      _              → Unit≢neⱼ A-ne (sym A≡Unit)

-- If No-η-equality A holds, then A is not a lifted type (given a
-- certain assumption).

No-η-equality→≢Lift :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  No-η-equality (Γ .defs) A → ¬ Γ ⊢ A ≡ Lift l B
No-η-equality→≢Lift = λ where
  Levelₙ        Level≡Lift → Lift≢Level (sym Level≡Lift)
  Uₙ            U≡Lift     → U≢Liftⱼ U≡Lift
  Σʷₙ           Σʷ≡Lift    → Lift≢ΠΣⱼ (sym Σʷ≡Lift)
  Emptyₙ        Empty≡Lift → Lift≢Emptyⱼ (sym Empty≡Lift)
  ℕₙ            ℕ≡Lift     → Lift≢ℕ (sym ℕ≡Lift)
  Idₙ           Id≡Lift    → Id≢Lift Id≡Lift
  (Unitʷₙ _)    Unit≡Lift  → Lift≢Unitⱼ (sym Unit≡Lift)
  (neₙ A-ne)    A≡Lift     → Lift≢ne A-ne (sym A≡Lift)

-- If No-η-equality (Γ .defs) A holds, for some A distinct from Level,
-- then a WHNF that is not neutral is not definitionally equal at type
-- A to any neutral term (given certain assumptions).

whnf≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  (No-equality-reflection → V) →
  No-η-equality (Γ .defs) A → A ≢ Level →
  Whnf (Γ .defs) t → ¬ Neutral V (Γ .defs) t → Neutral V (Γ .defs) u →
  ¬ Γ ⊢ t ≡ u ∷ A
whnf≢ne {Γ} {V} {A} {t} {u} →V ¬-A-η A≢Level t-whnf ¬-t-ne u-ne t≡u =
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
    ¬-t-ne (U.ne→ →V v-ne) }

  u⇒*ne : Γ ⊢ u ⇒* v ∷ B → Neutral V (Γ .defs) v
  u⇒*ne u⇒*v =
    case whnfRed*Term u⇒*v (ne-whnf u-ne) of λ {
      PE.refl →
    u-ne }

  lemma : ∀ {l} → ([A] : Γ ⊩⟨ l ⟩ A) → ¬ Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
  lemma = λ where
    (Levelᵣ A⇒*Level) _ →
      A≢Level (whnfRed* A⇒*Level (No-η-equality→Whnf ¬-A-η))
    (Liftᵣ′ A⇒*Lift _ _) _ →
      case A⇒*no-η A⇒*Lift of λ where
        (neₙ ())
    (ℕᵣ _) (ℕₜ₌ _ _ _ u⇒*zero _ zeroᵣ) →
      U.zero≢ne (u⇒*ne u⇒*zero) PE.refl
    (ℕᵣ _) (ℕₜ₌ _ _ _ u⇒*suc _ (sucᵣ _)) →
      U.suc≢ne (u⇒*ne u⇒*suc) PE.refl
    (ℕᵣ _) (ℕₜ₌ _ _ t⇒*v _ _ (ne (neNfₜ₌ v-ne _ _))) →
      ¬t⇒*ne t⇒*v (ne⁻ v-ne)
    (Emptyᵣ _) (Emptyₜ₌ _ _ t⇒*v _ _ (ne (neNfₜ₌ v-ne _ _))) →
      ¬t⇒*ne t⇒*v (ne⁻ v-ne)
    (Unitᵣ′ A⇒*Unit _) (Unitₜ₌ _ _ (d , _) (d′ , _) prop) →
      case A⇒*no-η A⇒*Unit of λ where
        (neₙ ())
        (Unitʷₙ no-η) → case prop of λ where
          (Unitₜ₌ʷ starᵣ _) →
            U.star≢ne (u⇒*ne d′) PE.refl
          (Unitₜ₌ʷ (ne (neNfₜ₌ neK _ _)) _) →
            ¬t⇒*ne d (ne⁻ neK)
          (Unitₜ₌ˢ η) →
            no-η (Unit-with-η-𝕨→Unitʷ-η η)
    (ne _) (neₜ₌ _ _ t⇒*v _ (neNfₜ₌ v-ne _ _)) →
      ¬t⇒*ne t⇒*v (ne⁻ v-ne)
    (Bᵣ BΠ! (Bᵣ _ _ A⇒*Π _ _ _ _ _)) _ →
      case A⇒*no-η A⇒*Π of λ where
        (neₙ ())
    (Bᵣ BΣˢ (Bᵣ _ _ A⇒*Σ _ _ _ _ _)) _ →
      case A⇒*no-η A⇒*Σ of λ where
        (neₙ ())
    (Bᵣ BΣʷ record{}) (_ , _ , _ , u⇒*w , _ , _ , prodₙ , _) →
      U.prod≢ne (u⇒*ne u⇒*w) PE.refl
    (Bᵣ BΣʷ record{}) (_ , _ , t⇒*v , _ , _ , ne v-ne , _) →
      ¬t⇒*ne t⇒*v (ne⁻ v-ne)
    (Bᵣ BΣʷ record{}) (_ , _ , _ , _ , _ , prodₙ , ne _  , ())
    (Idᵣ ⊩Id) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) →
      case ⊩Id≡∷-view-inhabited ⊩Id t≡u of λ where
        (ne t′-ne _ _) → ¬t⇒*ne t⇒*t′ (ne⁻ t′-ne)
        (rfl₌ _)       → U.rfl≢ne (u⇒*ne u⇒*u′) PE.refl
    (Uᵣ _) (Uₜ₌ _ _ t⇒*A u⇒*B A-type B-type A≡B _ _ _) →
      case B-type of λ where
        Levelₙ    → U.Level≢ne (u⇒*ne u⇒*B) PE.refl
        Uₙ        → U.U≢ne     (u⇒*ne u⇒*B) PE.refl
        Liftₙ     → case u⇒*ne u⇒*B of λ ()
        ΠΣₙ       → U.ΠΣ≢ne _  (u⇒*ne u⇒*B) PE.refl
        ℕₙ        → U.ℕ≢ne     (u⇒*ne u⇒*B) PE.refl
        Emptyₙ    → U.Empty≢ne (u⇒*ne u⇒*B) PE.refl
        Unitₙ     → U.Unit≢ne  (u⇒*ne u⇒*B) PE.refl
        Idₙ       → U.Id≢ne    (u⇒*ne u⇒*B) PE.refl
        (ne B-ne) → case A-type of λ where
          (ne A-ne) → ⊥-elim (¬t⇒*ne t⇒*A A-ne)
          Levelₙ    → Level≢ne  B-ne (univ A≡B)
          Uₙ        → U≢ne      B-ne (univ A≡B)
          Liftₙ     → Lift≢ne   B-ne (univ A≡B)
          ΠΣₙ       → ΠΣ≢ne     B-ne (univ A≡B)
          ℕₙ        → ℕ≢ne      B-ne (univ A≡B)
          Emptyₙ    → Empty≢neⱼ B-ne (univ A≡B)
          Unitₙ     → Unit≢neⱼ  B-ne (univ A≡B)
          Idₙ       → Id≢ne     B-ne (univ A≡B)

opaque

  -- If Level is allowed, then there is a counterexample to whnf≢ne
  -- (without the argument called ok) if the assumption of type
  -- A ≢ Level is removed.

  counterexample-to-whnf≢ne :
    Level-allowed →
    let V = L.Lift a ⊤
        Γ = ε » ε ∙ Level
        A = Level
        t = sucᵘ (var x0)
        u = var x0 supᵘ sucᵘ (var x0)
    in
    (No-equality-reflection → V) ×
    No-η-equality (Γ .defs) A ×
    Whnf (Γ .defs) t × ¬ Neutral V (Γ .defs) t × Neutral V (Γ .defs) u ×
    Γ ⊢ t ≡ u ∷ A
  counterexample-to-whnf≢ne ok =
    _ ,
    Levelₙ ,
    sucᵘₙ ,
    (λ ()) ,
    U.supᵘˡₙ (U.var _ _) ,
    sym′ (supᵘ-sub (var₀ (Levelⱼ′ ok εε)))

-- The term zero is not definitionally equal (at type ℕ) to any
-- neutral term (given a certain assumption).

zero≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  (No-equality-reflection → V) → Neutral V (Γ .defs) t →
  ¬ Γ ⊢ zero ≡ t ∷ ℕ
zero≢ne →V = whnf≢ne →V ℕₙ (λ ()) zeroₙ (λ ())

-- The term suc t is not definitionally equal (at type ℕ) to any
-- neutral term (given a certain assumption).

suc≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  (No-equality-reflection → V) → Neutral V (Γ .defs) u →
  ¬ Γ ⊢ suc t ≡ u ∷ ℕ
suc≢ne →V = whnf≢ne →V ℕₙ (λ ()) sucₙ (λ ())

opaque

  -- The term sucⁿ n is not definitionally equal (at type ℕ) to any
  -- neutral term (given a certain assumption).

  sucⁿ≢ne :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    (No-equality-reflection → V) → Neutral V (Γ .defs) t →
    ¬ Γ ⊢ sucⁿ n ≡ t ∷ ℕ
  sucⁿ≢ne {n = 0}    = zero≢ne
  sucⁿ≢ne {n = 1+ _} = suc≢ne

-- The term starʷ l is not definitionally equal (at type Unitʷ l) to
-- any neutral term (given certain assumptions).

starʷ≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  ¬ Unitʷ-η → (No-equality-reflection → V) → Neutral V (Γ .defs) t →
  ¬ Γ ⊢ starʷ ≡ t ∷ Unitʷ
starʷ≢ne no-η →V =
  whnf≢ne →V (Unitʷₙ no-η) (λ ()) starₙ (λ ())

-- The term prodʷ p t u is not definitionally equal (at type
-- Σʷ p , q ▷ A ▹ B) to any neutral term (given a certain assumption).

prodʷ≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  (No-equality-reflection → V) → Neutral V (Γ .defs) v →
  ¬ Γ ⊢ prodʷ p t u ≡ v ∷ Σʷ p , q ▷ A ▹ B
prodʷ≢ne →V = whnf≢ne →V Σʷₙ (λ ()) prodₙ (λ ())

-- The term rfl is not definitionally equal (at type Id A t u) to any
-- neutral term (given a certain assumption).

rfl≢ne :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  (No-equality-reflection → V) → Neutral V (Γ .defs) v →
  ¬ Γ ⊢ rfl ≡ v ∷ Id A t u
rfl≢ne →V = whnf≢ne →V Idₙ (λ ()) rflₙ (λ ())

opaque
  unfolding ⊩1ᵘ+ ↑ⁿ

  -- The level l is not equal to 1ᵘ+ l (given a certain assumption).

  ≢1ᵘ+ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ l ≡ 1ᵘ+ l ∷Level
  ≢1ᵘ+ (term okᴸ t≡sucᵘt) =
    let _ , ⊩t≡sucᵘt = reducible-⊩≡∷ t≡sucᵘt
        _ , ⊩t≡sucᵘt = ⊩≡∷Level⇔ .proj₁ ⊩t≡sucᵘt
    in
    case wf-Level-eq ⊩t≡sucᵘt of λ where
      (⊩t@(term _ _) , _) →
        1+n≢n (PE.sym (↑ⁿ-cong {ok₁ = okᴸ} ⊩t (⊩1ᵘ+ ⊩t) ⊩t≡sucᵘt))
      (literal ok _ , _) →
        Level-allowed→Allowed-literal→ okᴸ ok
  ≢1ᵘ+ {l = ωᵘ+ _} ()

opaque

  -- The level zeroᵘₗ is not equal to 1ᵘ+ l (given a certain
  -- assumption).

  zeroᵘ≢1ᵘ+ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ zeroᵘₗ ≡ 1ᵘ+ l ∷Level
  zeroᵘ≢1ᵘ+ {l = level _} (term ok 0≡1+) =
    let _ , 0≡1+  = ⊩≡∷Level⇔ .proj₁ (reducible-⊩≡∷ 0≡1+ .proj₂)
        ⊩0 , ⊩1+l = wf-Level-eq 0≡1+
        ⊩l        = ⊩1ᵘ+⇔ .proj₁ ⊩1+l
    in
    case
      0                ≡˘⟨ ↑ⁿ-zeroᵘ ⊩0 ⟩
      ↑ⁿ ok ⊩0         ≡⟨ ↑ⁿ-cong ⊩0 (⊩1ᵘ+ ⊩l) 0≡1+ ⟩
      ↑ⁿ ok (⊩1ᵘ+ ⊩l)  ≡⟨ ↑ⁿ-sucᵘ ⊩l (⊩1ᵘ+ ⊩l) ⟩
      1+ (↑ⁿ ok ⊩l)    ∎
    of λ ()
    where
    open Tools.Reasoning.PropositionalEquality
  zeroᵘ≢1ᵘ+ {l = ωᵘ+ _} ()

opaque

  -- ℕ does not have type U (1ᵘ+ l) (given a certain assumption).

  ¬ℕ∷U-sucᵘ :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ¬ Γ ⊢ ℕ ∷ U (1ᵘ+ l)
  ¬ℕ∷U-sucᵘ = zeroᵘ≢1ᵘ+ ∘→ sym-⊢≡∷L ∘→ U-injectivity ∘→ inversion-ℕ
