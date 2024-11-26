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
open import Definition.Untyped.Neutral M type-variant as U
  using (Neutral; No-η-equality; Whnf)
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Properties R
open import Definition.Typed.Syntactic R
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
    n : Nat
    Γ : Con Term n
    A B C D t u v : Term n
    p p′ q q′ : M
    b : BinderMode
    s : Strength
    l l₁ l₂ : Universe-level

opaque
  unfolding _⊩⟨_⟩_≡_

  A≢B :
    (_⊩′⟨_⟩A_ _⊩′⟨_⟩B_ : Con Term n → Universe-level → Term n → Set a)
    (A-intr : ∀ {l} → Γ ⊩′⟨ l ⟩A A → Γ ⊩⟨ l ⟩ A)
    (B-intr : ∀ {l} → Γ ⊩′⟨ l ⟩B B → Γ ⊩⟨ l ⟩ B) →
    (∀ {l} → Γ ⊩⟨ l ⟩ A → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩A A) →
    (∀ {l} → Γ ⊩⟨ l ⟩ B → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩B B) →
    (∀ {l₁ l₂} {⊩A : Γ ⊩′⟨ l₁ ⟩A A} {⊩B : Γ ⊩′⟨ l₂ ⟩B B} →
     ¬ ShapeView Γ l₁ l₂ A B (A-intr ⊩A) (B-intr ⊩B)) →
    ¬ Γ ⊢ A ≡ B
  A≢B _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B =
    let _ , ⊩A , ⊩B , A≡B = reducible-⊩≡ A≡B
        _ , ⊩A′           = A-elim ⊩A
        _ , ⊩B′           = B-elim ⊩B
        A≡B′              = irrelevanceEq ⊩A (A-intr ⊩A′) A≡B
    in
    A≢B′ (goodCases (A-intr ⊩A′) (B-intr ⊩B′) A≡B′)

opaque

  -- Applications of U are not definitionally equal to ℕ.

  U≢ℕ : ¬ Γ ⊢ U l ≡ ℕ
  U≢ℕ =
    A≢B _⊩′⟨_⟩U_ (λ Γ _ A → Γ ⊩ℕ A) Uᵣ ℕᵣ
      (extractMaybeEmb ∘→ U-elim)
      (extractMaybeEmb ∘→ ℕ-elim)
      (λ ())

opaque

  -- Applications of U are not definitionally equal to Empty.

  U≢Emptyⱼ : ¬ Γ ⊢ U l ≡ Empty
  U≢Emptyⱼ =
    A≢B _⊩′⟨_⟩U_ (λ Γ _ A → Γ ⊩Empty A) Uᵣ Emptyᵣ
      (extractMaybeEmb ∘→ U-elim)
      (extractMaybeEmb ∘→ Empty-elim)
      (λ ())

opaque

  -- Applications of U are not definitionally equal to applications of
  -- Unit.

  U≢Unitⱼ : ¬ Γ ⊢ U l₁ ≡ Unit s l₂
  U≢Unitⱼ {s} =
    A≢B _⊩′⟨_⟩U_ _⊩Unit⟨_, s ⟩_ Uᵣ Unitᵣ
      (extractMaybeEmb ∘→ U-elim)
      (extractMaybeEmb ∘→ Unit-elim)
      (λ ())

opaque

  -- ℕ and Empty are not definitionally equal.

  ℕ≢Emptyⱼ : ¬ Γ ⊢ ℕ ≡ Empty
  ℕ≢Emptyⱼ =
    A≢B (λ Γ _ A → Γ ⊩ℕ A) (λ Γ _ A → Γ ⊩Empty A) ℕᵣ Emptyᵣ
      (extractMaybeEmb ∘→ ℕ-elim)
      (extractMaybeEmb ∘→ Empty-elim)
      (λ ())

opaque

  -- ℕ is not definitionally equal to applications of Unit.

  ℕ≢Unitⱼ : ¬ Γ ⊢ ℕ ≡ Unit s l
  ℕ≢Unitⱼ {s} =
    A≢B (λ Γ _ A → Γ ⊩ℕ A) _⊩Unit⟨_, s ⟩_ ℕᵣ Unitᵣ
      (extractMaybeEmb ∘→ ℕ-elim)
      (extractMaybeEmb ∘→ Unit-elim)
      (λ ())

opaque

  -- Empty is not definitionally equal to applications of Unit.

  Empty≢Unitⱼ : ¬ Γ ⊢ Empty ≡ Unit s l
  Empty≢Unitⱼ {s} =
    A≢B (λ Γ _ A → Γ ⊩Empty A) _⊩Unit⟨_, s ⟩_ Emptyᵣ Unitᵣ
      (extractMaybeEmb ∘→ Empty-elim)
      (extractMaybeEmb ∘→ Unit-elim)
      (λ ())

opaque

  -- Applications of U are not definitionally equal to applications of
  -- ΠΣ⟨_⟩_,_▷_▹_.

  U≢ΠΣⱼ : ¬ Γ ⊢ U l ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  U≢ΠΣⱼ =
    let b = _ in
    A≢B _⊩′⟨_⟩U_ _⊩′⟨_⟩B⟨ b ⟩_ Uᵣ (Bᵣ _)
      (extractMaybeEmb ∘→ U-elim)
      (extractMaybeEmb ∘→ B-elim _)
      (λ ())

opaque

  -- Applications of U are not definitionally equal to neutral terms.

  U≢ne : Neutral A → ¬ Γ ⊢ U l ≡ A
  U≢ne A-ne =
    A≢B _⊩′⟨_⟩U_ (λ Γ _ A → Γ ⊩ne A) Uᵣ ne
      (extractMaybeEmb ∘→ U-elim)
      (extractMaybeEmb ∘→ ne-elim A-ne)
      (λ ())

opaque

  -- ℕ is not definitionally equal to applications of ΠΣ⟨_⟩_,_▷_▹_.

  ℕ≢ΠΣⱼ : ¬ Γ ⊢ ℕ ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  ℕ≢ΠΣⱼ =
    let b = _ in
    A≢B (λ Γ _ A → Γ ⊩ℕ A) _⊩′⟨_⟩B⟨ b ⟩_ ℕᵣ (Bᵣ _)
      (extractMaybeEmb ∘→ ℕ-elim)
      (extractMaybeEmb ∘→ B-elim _)
      (λ ())

opaque

  -- Empty is not definitionally equal to applications of
  -- ΠΣ⟨_⟩_,_▷_▹_.

  Empty≢ΠΣⱼ : ¬ Γ ⊢ Empty ≡ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  Empty≢ΠΣⱼ =
    let b = _ in
    A≢B (λ Γ _ A → Γ ⊩Empty A) _⊩′⟨_⟩B⟨ b ⟩_ Emptyᵣ (Bᵣ _)
      (extractMaybeEmb ∘→ Empty-elim)
      (extractMaybeEmb ∘→ B-elim _)
      (λ ())

opaque

  -- Applications of Unit are not definitionally equal to applications
  -- of ΠΣ⟨_⟩_,_▷_▹_.

  Unit≢ΠΣⱼ : ¬ Γ ⊢ Unit s l ≡ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C
  Unit≢ΠΣⱼ {s} =
    let b = _ in
    A≢B _⊩Unit⟨_, s ⟩_ _⊩′⟨_⟩B⟨ b ⟩_ Unitᵣ (Bᵣ _)
      (extractMaybeEmb ∘→ Unit-elim)
      (extractMaybeEmb ∘→ B-elim _)
      (λ ())

opaque

  -- ℕ is not definitionally equal to neutral terms.

  ℕ≢ne : Neutral A → ¬ Γ ⊢ ℕ ≡ A
  ℕ≢ne A-ne =
    A≢B (λ Γ _ A → Γ ⊩ℕ A) (λ Γ _ A → Γ ⊩ne A) ℕᵣ ne
      (extractMaybeEmb ∘→ ℕ-elim)
      (extractMaybeEmb ∘→ ne-elim A-ne)
      (λ ())

opaque

  -- Empty is not definitionally equal to neutral terms.

  Empty≢neⱼ : Neutral A → ¬ Γ ⊢ Empty ≡ A
  Empty≢neⱼ A-ne =
    A≢B (λ Γ _ A → Γ ⊩Empty A) (λ Γ _ A → Γ ⊩ne A) Emptyᵣ ne
      (extractMaybeEmb ∘→ Empty-elim)
      (extractMaybeEmb ∘→ ne-elim A-ne)
      (λ ())

opaque

  -- Applications of Unit are not definitionally equal to neutral
  -- terms.

  Unit≢neⱼ : Neutral A → ¬ Γ ⊢ Unit s l ≡ A
  Unit≢neⱼ {s} A-ne =
    A≢B _⊩Unit⟨_, s ⟩_ (λ Γ _ A → Γ ⊩ne A) Unitᵣ ne
      (extractMaybeEmb ∘→ Unit-elim)
      (extractMaybeEmb ∘→ ne-elim A-ne)
      (λ ())

opaque

  -- Applications of ΠΣ⟨_⟩_,_▷_▹_ are not definitionally equal to
  -- neutral terms.

  ΠΣ≢ne : Neutral C → ¬ Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ≡ C
  ΠΣ≢ne C-ne =
    let b = _ in
    A≢B _⊩′⟨_⟩B⟨ b ⟩_ (λ Γ _ A → Γ ⊩ne A) (Bᵣ _) ne
      (extractMaybeEmb ∘→ B-elim _)
      (extractMaybeEmb ∘→ ne-elim C-ne)
      (λ ())

opaque

  -- Applications of Π_,_▷_▹_ are not definitionally equal to
  -- applications of Σ⟨_⟩_,_▷_▹_.

  Π≢Σⱼ : ¬ Γ ⊢ Π p , q ▷ A ▹ B ≡ Σ⟨ s ⟩ p′ , q′ ▷ C ▹ D
  Π≢Σⱼ =
    let b₁ = _
        b₂ = _
    in
    A≢B _⊩′⟨_⟩B⟨ b₁ ⟩_ _⊩′⟨_⟩B⟨ b₂ ⟩_ (Bᵣ _) (Bᵣ _)
      (extractMaybeEmb ∘→ B-elim _)
      (extractMaybeEmb ∘→ B-elim _)
      (λ ())

opaque

  -- Applications of Σˢ_,_▷_▹_ are not definitionally equal to
  -- applications of Σʷ_,_▷_▹_.

  Σˢ≢Σʷⱼ : ¬ Γ ⊢ Σˢ p , q ▷ A ▹ B ≡ Σʷ p′ , q′ ▷ C ▹ D
  Σˢ≢Σʷⱼ =
    let b₁ = _
        b₂ = _
    in
    A≢B _⊩′⟨_⟩B⟨ b₁ ⟩_ _⊩′⟨_⟩B⟨ b₂ ⟩_ (Bᵣ _) (Bᵣ _)
      (extractMaybeEmb ∘→ B-elim _)
      (extractMaybeEmb ∘→ B-elim _)
      (λ ())

opaque

  -- Applications of Unitʷ are not definitionally equal to
  -- applications of Unitˢ.

  Unitʷ≢Unitˢ : ¬ Γ ⊢ Unitʷ l₁ ≡ Unitˢ l₂
  Unitʷ≢Unitˢ =
    A≢B _⊩Unit⟨_, 𝕨 ⟩_ _⊩Unit⟨_, 𝕤 ⟩_ Unitᵣ Unitᵣ
      (extractMaybeEmb ∘→ Unit-elim)
      (extractMaybeEmb ∘→ Unit-elim)
      (λ ())

opaque

  -- Applications of Id are not definitionally equal to neutral types.

  Id≢ne : Neutral B → ¬ Γ ⊢ Id A t u ≡ B
  Id≢ne B-ne =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩ne A) Idᵣ ne
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ ne-elim B-ne)
      (λ ())

opaque

  -- Applications of Id are not definitionally equal to applications
  -- of U.

  Id≢U : ¬ Γ ⊢ Id A t u ≡ U l
  Id≢U =
    A≢B _⊩′⟨_⟩Id_ _⊩′⟨_⟩U_ Idᵣ Uᵣ
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ U-elim)
      (λ ())

opaque

  -- Applications of Id are not definitionally equal to ℕ.

  Id≢ℕ : ¬ Γ ⊢ Id A t u ≡ ℕ
  Id≢ℕ =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩ℕ A) Idᵣ ℕᵣ
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ ℕ-elim)
      (λ ())

opaque

  -- Applications of Id are not definitionally equal to applications
  -- of Unit.

  Id≢Unit : ¬ Γ ⊢ Id A t u ≡ Unit s l
  Id≢Unit {s} =
    A≢B _⊩′⟨_⟩Id_ _⊩Unit⟨_, s ⟩_ Idᵣ Unitᵣ
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ Unit-elim)
      (λ ())

opaque

  -- Applications of Id are not definitionally equal to Empty.

  Id≢Empty : ¬ Γ ⊢ Id A t u ≡ Empty
  Id≢Empty =
    A≢B _⊩′⟨_⟩Id_ (λ Γ _ A → Γ ⊩Empty A) Idᵣ Emptyᵣ
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ Empty-elim)
      (λ ())

opaque

  -- Applications of Id are not definitionally equal to applications
  -- of ΠΣ⟨_⟩_,_▷_▹_.

  Id≢ΠΣ : ¬ Γ ⊢ Id A t u ≡ ΠΣ⟨ b ⟩ p , q ▷ B ▹ C
  Id≢ΠΣ =
    let b = _ in
    A≢B _⊩′⟨_⟩Id_ _⊩′⟨_⟩B⟨ b ⟩_ Idᵣ (Bᵣ _)
      (extractMaybeEmb ∘→ Id-elim)
      (extractMaybeEmb ∘→ B-elim _)
      (λ ())

-- If No-η-equality A holds, then A is not a Π-type.

No-η-equality→≢Π : No-η-equality A → Γ ⊢ A ≡ Π p , q ▷ B ▹ C → ⊥
No-η-equality→≢Π = λ where
  U.Uₙ         U≡Π     → U≢ΠΣⱼ U≡Π
  U.Σʷₙ        Σʷ≡Π    → Π≢Σⱼ (sym Σʷ≡Π)
  U.Emptyₙ     Empty≡Π → Empty≢ΠΣⱼ Empty≡Π
  U.ℕₙ         ℕ≡Π     → ℕ≢ΠΣⱼ ℕ≡Π
  U.Idₙ        Id≡Π    → Id≢ΠΣ Id≡Π
  (U.Unitʷₙ _) Unit≡Π  → Unit≢ΠΣⱼ Unit≡Π
  (U.neₙ A-ne) A≡Π     → ΠΣ≢ne A-ne (sym A≡Π)

-- If No-η-equality A holds, then A is not a Σ-type with η-equality.

No-η-equality→≢Σˢ : No-η-equality A → Γ ⊢ A ≡ Σˢ p , q ▷ B ▹ C → ⊥
No-η-equality→≢Σˢ = λ where
  U.Uₙ         U≡Σ     → U≢ΠΣⱼ U≡Σ
  U.Σʷₙ        Σʷ≡Σ    → Σˢ≢Σʷⱼ (sym Σʷ≡Σ)
  U.Emptyₙ     Empty≡Σ → Empty≢ΠΣⱼ Empty≡Σ
  U.ℕₙ         ℕ≡Σ     → ℕ≢ΠΣⱼ ℕ≡Σ
  U.Idₙ        Id≡Σ    → Id≢ΠΣ Id≡Σ
  (U.Unitʷₙ _) Unit≡Σ  → Unit≢ΠΣⱼ Unit≡Σ
  (U.neₙ A-ne) A≡Σ     → ΠΣ≢ne A-ne (sym A≡Σ)

-- If No-η-equality A holds, then A is not a unit type with
-- η-equality.

No-η-equality→≢Unit :
  No-η-equality A → Γ ⊢ A ≡ Unit s l → ¬ Unit-with-η s
No-η-equality→≢Unit = λ where
  U.Uₙ            U≡Unit      _              → U≢Unitⱼ U≡Unit
  U.Σʷₙ           Σʷ≡Unit     _              → Unit≢ΠΣⱼ (sym Σʷ≡Unit)
  U.Emptyₙ        Empty≡Unit  _              → Empty≢Unitⱼ Empty≡Unit
  U.ℕₙ            ℕ≡Unit      _              → ℕ≢Unitⱼ ℕ≡Unit
  U.Idₙ           Id≡Unit     _              → Id≢Unit Id≡Unit
  (U.Unitʷₙ _)    Unitʷ≡Unitˢ (inj₁ PE.refl) → Unitʷ≢Unitˢ Unitʷ≡Unitˢ
  (U.Unitʷₙ no-η) _           (inj₂ η)       → no-η η
  (U.neₙ A-ne)    A≡Unit      _              → Unit≢neⱼ A-ne
                                                 (sym A≡Unit)

-- If A is a type without η-equality, then a non-neutral WHNF is not
-- definitionally equal at type A to any neutral term.

whnf≢ne :
  No-η-equality A → Whnf t → ¬ Neutral t → Neutral u →
  ¬ Γ ⊢ t ≡ u ∷ A
whnf≢ne {A} {t} {u} ¬-A-η t-whnf ¬-t-ne u-ne t≡u =
  case reducible-⊩≡∷ t≡u of λ
    (_ , t≡u) →
  case wf-⊩∷ $ wf-⊩≡∷ t≡u .proj₁ of λ
    ⊩A →
  lemma ⊩A (⊩≡∷→⊩≡∷/ ⊩A t≡u)
  where
  A⇒*no-η : Γ ⊢ A ⇒* B → No-η-equality B
  A⇒*no-η A⇒*B =
    case whnfRed* A⇒*B (U.No-η-equality→Whnf ¬-A-η) of λ {
      PE.refl →
    ¬-A-η }

  ¬t⇒*ne : Γ ⊢ t ⇒* v ∷ B → ¬ Neutral v
  ¬t⇒*ne t⇒*v v-ne =
    case whnfRed*Term t⇒*v t-whnf of λ {
      PE.refl →
    ¬-t-ne v-ne }

  u⇒*ne : Γ ⊢ u ⇒* v ∷ B → Neutral v
  u⇒*ne u⇒*v =
    case whnfRed*Term u⇒*v (U.ne u-ne) of λ {
      PE.refl →
    u-ne }

  lemma : ([A] : Γ ⊩⟨ l ⟩ A) → ¬ Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
  lemma = λ where
    (ℕᵣ _) (ℕₜ₌ _ _ _ u⇒*zero _ zeroᵣ) →
      U.zero≢ne (u⇒*ne u⇒*zero) PE.refl
    (ℕᵣ _) (ℕₜ₌ _ _ _ u⇒*suc _ (sucᵣ _)) →
      U.suc≢ne (u⇒*ne u⇒*suc) PE.refl
    (ℕᵣ _) (ℕₜ₌ _ _ t⇒*v _ _ (ne (neNfₜ₌ _ v-ne _ _))) →
      ¬t⇒*ne t⇒*v v-ne
    (Emptyᵣ _) (Emptyₜ₌ _ _ t⇒*v _ _ (ne (neNfₜ₌ _ v-ne _ _))) →
      ¬t⇒*ne t⇒*v v-ne
    (Unitᵣ (Unitₜ A⇒*Unit _)) [t≡u] →
      case A⇒*no-η A⇒*Unit of λ where
        (U.neₙ ())
        (U.Unitʷₙ not-ok) → case [t≡u] of λ where
          (Unitₜ₌ʷ _ _ _ d′ _ starᵣ _) →
            U.star≢ne (u⇒*ne d′) PE.refl
          (Unitₜ₌ʷ _ _ d _ _ (ne (neNfₜ₌ _ neK _ _)) _) →
            ¬t⇒*ne d neK
          (Unitₜ₌ˢ _ _ (inj₂ ok)) →
            not-ok ok
    (ne _) (neₜ₌ _ _ t⇒*v _ (neNfₜ₌ _ v-ne _ _)) →
      ¬t⇒*ne t⇒*v v-ne
    (Bᵣ BΠ! (Bᵣ _ _ A⇒*Π _ _ _ _ _)) _ →
      case A⇒*no-η A⇒*Π of λ where
        (U.neₙ ())
    (Bᵣ BΣˢ (Bᵣ _ _ A⇒*Σ _ _ _ _ _)) _ →
      case A⇒*no-η A⇒*Σ of λ where
        (U.neₙ ())
    (Bᵣ BΣʷ record{}) (_ , _ , _ , u⇒*w , _ , _ , _ , _ , U.prodₙ , _) →
      U.prod≢ne (u⇒*ne u⇒*w) PE.refl
    (Bᵣ BΣʷ record{}) (_ , _ , t⇒*v , _ , _ , _ , _ , U.ne v-ne , _) →
      ¬t⇒*ne t⇒*v v-ne
    (Bᵣ BΣʷ record{})
      (_ , _ , _ , _ , _ , _ , _ , U.prodₙ , U.ne _  , ())
    (Idᵣ ⊩Id) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) →
      case ⊩Id≡∷-view-inhabited ⊩Id t≡u of λ where
        (ne _ t′-ne _ _) → ¬t⇒*ne t⇒*t′ t′-ne
        (rfl₌ _)         → U.rfl≢ne (u⇒*ne u⇒*u′) PE.refl
    (Uᵣ _) (Uₜ₌ _ _ t⇒*A u⇒*B A-type B-type A≡B _ _ _) →
      case B-type of λ where
        U.Uₙ        → U.U≢ne     (u⇒*ne u⇒*B) PE.refl
        U.ΠΣₙ       → U.ΠΣ≢ne _  (u⇒*ne u⇒*B) PE.refl
        U.ℕₙ        → U.ℕ≢ne     (u⇒*ne u⇒*B) PE.refl
        U.Emptyₙ    → U.Empty≢ne (u⇒*ne u⇒*B) PE.refl
        U.Unitₙ     → U.Unit≢ne  (u⇒*ne u⇒*B) PE.refl
        U.Idₙ       → U.Id≢ne    (u⇒*ne u⇒*B) PE.refl
        (U.ne B-ne) → case A-type of λ where
          (U.ne A-ne) → ⊥-elim (¬t⇒*ne t⇒*A A-ne)
          U.Uₙ        → U≢ne      B-ne (univ A≡B)
          U.ΠΣₙ       → ΠΣ≢ne     B-ne (univ A≡B)
          U.ℕₙ        → ℕ≢ne      B-ne (univ A≡B)
          U.Emptyₙ    → Empty≢neⱼ B-ne (univ A≡B)
          U.Unitₙ     → Unit≢neⱼ  B-ne (univ A≡B)
          U.Idₙ       → Id≢ne     B-ne (univ A≡B)
    (emb ≤ᵘ-refl     [A]) → lemma [A]
    (emb (≤ᵘ-step p) [A]) → lemma (emb p [A])

-- The term zero is not definitionally equal (at type ℕ) to any
-- neutral term.

zero≢ne :
  Neutral t →
  ¬ Γ ⊢ zero ≡ t ∷ ℕ
zero≢ne = whnf≢ne U.ℕₙ U.zeroₙ (λ ())

-- The term suc t is not definitionally equal (at type ℕ) to any
-- neutral term.

suc≢ne :
  Neutral u →
  ¬ Γ ⊢ suc t ≡ u ∷ ℕ
suc≢ne = whnf≢ne U.ℕₙ U.sucₙ (λ ())

-- The term prodʷ p t u is not definitionally equal (at type
-- Σʷ p , q ▷ A ▹ B) to any neutral term.

prodʷ≢ne :
  Neutral v →
  ¬ Γ ⊢ prodʷ p t u ≡ v ∷ Σʷ p , q ▷ A ▹ B
prodʷ≢ne = whnf≢ne U.Σʷₙ U.prodₙ (λ ())

-- The term rfl is not definitionally equal (at type Id A t u) to any
-- neutral term.

rfl≢ne :
  Neutral v →
  ¬ Γ ⊢ rfl ≡ v ∷ Id A t u
rfl≢ne = whnf≢ne U.Idₙ U.rflₙ (λ ())
