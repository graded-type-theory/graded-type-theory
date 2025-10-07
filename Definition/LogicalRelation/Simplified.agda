------------------------------------------------------------------------
-- A variant of the logical relation for reducibility with fewer
-- assumptions.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Simplified
  {a} {Mod : Set a}
  {𝕄 : Modality Mod}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped Mod
open import Definition.Untyped.Neutral Mod type-variant
open import Definition.Untyped.Properties Mod
open import Definition.Untyped.Whnf Mod type-variant
open import Definition.Typed R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Properties R
open import Definition.Typed.Inversion R
open import Definition.Typed.Substitution R
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Weakening.Definition R
open import Definition.LogicalRelation R
  hiding (Uᵣ′; Unitᵣ′; ne′; Bᵣ′)
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Weakening.Restricted R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ : Cons _ _
  m n : Nat
  s : Strength
  t u A A′ B : Term _
  p q : Mod
  b : BinderMode

------------------------------------------------------------------------
-- The logical relation and some auxilliary definitions

-- Universe type

infix 4 _⊨U_

record _⊨U_ (Γ : Cons m n) (A : Term n) : Set a where
  no-eta-equality
  pattern
  constructor Uᵣ
  field
    l  : Universe-level
    ⇒*U : Γ ⊢ A ⇒* U l

-- Unit type

infix 4 _⊨Unit⟨_⟩_

record _⊨Unit⟨_⟩_
  (Γ : Cons m n) (s : Strength) (A : Term n) :
  Set a where
  no-eta-equality
  pattern
  constructor Unitᵣ
  field
    l      : Universe-level
    ⇒*-Unit : Γ ⊢ A ⇒* Unit s l

-- Neutral type

infix 4 _⊨ne_

record _⊨ne_ (Γ : Cons m n) (A : Term n) : Set a where
  no-eta-equality
  pattern
  constructor ne
  field
    N                 : Term n
    D                 : Γ ⊢ A ⇒* N
    neN               : Neutralₗ (Γ .defs) N

mutual

  -- ΠΣ-type

  infix 4 _⊨ΠΣ⟨_,_,_⟩_

  record _⊨ΠΣ⟨_,_,_⟩_ (Γ : Cons m n) (b : BinderMode)
                      (p q : Mod) (A : Term n) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor Bᵣ
    field
      F : Term n
      G : Term (1+ n)
      D : Γ ⊢ A ⇒* ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
      [F] : Γ ⊨ F
      [G] : Γ ⊢ t ∷ F → Γ ⊨ G [ t ]₀

  -- Identity types.

  infix 4 _⊨Id_

  record _⊨Id_ (Γ : Cons m n) (A : Term n) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor Idᵣ
    field
      Ty lhs rhs : Term n
      ⇒*Id       : Γ ⊢ A ⇒* Id Ty lhs rhs
      ⊨Ty        : Γ ⊨ Ty
      ⊨lhs       : Γ ⊢ lhs ∷ Ty
      ⊨rhs       : Γ ⊢ rhs ∷ Ty

  -- The logical relation

  infix 4 _⊨_

  data _⊨_ (Γ : Cons m n) (A : Term n) : Set a where
    Uᵣ     : Γ ⊨U A           → Γ ⊨ A
    ℕᵣ     : Γ ⊢ A ⇒* ℕ       → Γ ⊨ A
    Emptyᵣ : Γ ⊢ A ⇒* Empty   → Γ ⊨ A
    Unitᵣ  : Γ ⊨Unit⟨ s ⟩ A    → Γ ⊨ A
    ne     : Γ ⊨ne A          → Γ ⊨ A
    Bᵣ     : ∀ b p q → Γ ⊨ΠΣ⟨ b , p , q ⟩ A → Γ ⊨ A
    Idᵣ    : Γ ⊨Id A          → Γ ⊨ A

pattern Uᵣ′ a b = Uᵣ (Uᵣ a b)
pattern Unitᵣ′ a b = Unitᵣ (Unitᵣ a b)
pattern ne′ a b c = ne (ne a b c)
pattern Bᵣ′ a b c d e f g h = Bᵣ a b c (Bᵣ d e f g h)
pattern Idᵣ′ a b c d e f g = Idᵣ (Idᵣ a b c d e f g)

private variable
  l : Universe-level

opaque

  -- Types in the relation are well-formed types.

  ⊨→⊢ : Γ ⊨ A → Γ ⊢ A
  ⊨→⊢ (Uᵣ′ _ ⇒*U) = redFirst* ⇒*U
  ⊨→⊢ (ℕᵣ x) = redFirst* x
  ⊨→⊢ (Emptyᵣ x) = redFirst* x
  ⊨→⊢ (Unitᵣ′ _ ⇒*-Unit) = redFirst* ⇒*-Unit
  ⊨→⊢ (ne′ _ D _) = redFirst* D
  ⊨→⊢ (Bᵣ′ _ _ _ _ _ D _ _) = redFirst* D
  ⊨→⊢ (Idᵣ′ _ _ _ ⇒*Id _ _ _) = redFirst* ⇒*Id

opaque

  -- Types in the reducibility logical relation are in the relation.

  ⊩→⊨ : ⦃ inc : Var-included or-empty (Γ .vars) ⦄ → Γ ⊩⟨ l ⟩ A → Γ ⊨ A
  ⊩→⊨ (Uᵣ (Uᵣ l′ _ ⇒*U)) = Uᵣ′ l′ ⇒*U
  ⊩→⊨ (ℕᵣ x) = ℕᵣ x
  ⊩→⊨ (Emptyᵣ x) = Emptyᵣ x
  ⊩→⊨ (Unitᵣ (Unitᵣ l′ _ ⇒*-Unit ok)) = Unitᵣ (Unitᵣ l′ ⇒*-Unit)
  ⊩→⊨ (ne (ne N D neN _)) = ne′ N D neN
  ⊩→⊨ (Bᵣ (BM b p q) (Bᵣ F G D A≡A [F] [G] G-ext ok)) =
    let ⊢Γ = wf (redFirst* D)
        [F]′ = [F] id⊇ (id ⊢Γ)
    in  Bᵣ′ b p q F G D
         (PE.subst (_ ⊨_) (wk-id F) (⊩→⊨ [F]′))
         (λ ⊢t →
           let ⊢t′ = PE.subst (_ ⊢ _ ∷_) (PE.sym (wk-id F)) ⊢t
               _ , [t] = reducible-⊩∷ ⊢t′
               [t]′ = ⊩∷→⊩∷/ [F]′ [t]
           in  PE.subst (_ ⊨_) (PE.cong (_[ _ ]₀) (wk-lift-id G))
                 (⊩→⊨ ([G] id⊇ (id ⊢Γ) [t]′)))
  ⊩→⊨ (Idᵣ (Idᵣ Ty lhs rhs ⇒*Id ⊩Ty ⊩lhs ⊩rhs)) =
    Idᵣ′ Ty lhs rhs ⇒*Id (⊩→⊨ ⊩Ty)
      (escapeTerm ⊩Ty ⊩lhs) (escapeTerm ⊩Ty ⊩rhs)

opaque

  -- Well-formed types are in the relation

  ⊢→⊨ : ⦃ inc : Var-included or-empty (Γ .vars) ⦄ → Γ ⊢ A → Γ ⊨ A
  ⊢→⊨ ⊢A = ⊩→⊨ (reducible-⊩ ⊢A .proj₂)

------------------------------------------------------------------------
-- A ShapeView for the logical relation.

data ShapeView (Γ : Cons m n) : ∀ A A′ → Γ ⊨ A → Γ ⊨ A′ → Set a where
  Uᵥ : ∀ UA UA′ → ShapeView Γ A A′ (Uᵣ UA) (Uᵣ UA′)
  ℕᵥ : ∀ ℕA ℕA′ → ShapeView Γ A A′ (ℕᵣ ℕA) (ℕᵣ ℕA′)
  Emptyᵥ : ∀ EmptyA EmptyA′ → ShapeView Γ A A′ (Emptyᵣ EmptyA) (Emptyᵣ EmptyA′)
  Unitᵥ : ∀ UnitA UnitA′ → ShapeView Γ A A′ (Unitᵣ {s = s} UnitA) (Unitᵣ {s = s} UnitA′)
  ne : ∀ neA neA′ → ShapeView Γ A A′ (ne neA) (ne neA′)
  Bᵥ : ∀ b p q BA BA′ → ShapeView Γ A A′ (Bᵣ b p q BA) (Bᵣ b p q BA′)
  Idᵥ : ∀ IdA IdA′ → ShapeView Γ A A′ (Idᵣ IdA) (Idᵣ IdA′)

opaque

  -- Definitionally equal types are in the ShapeView.

  goodCases : ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄
            → ([A] : Γ ⊨ A) ([B] : Γ ⊨ B)
            → Γ ⊢ A ≡ B → ShapeView Γ A B [A] [B]
  goodCases (Uᵣ x) (Uᵣ x₁) A≡B = Uᵥ x x₁
  goodCases (ℕᵣ x) (ℕᵣ x₁) A≡B = ℕᵥ x x₁
  goodCases (Emptyᵣ x) (Emptyᵣ x₁) A≡B = Emptyᵥ x x₁
  goodCases (Unitᵣ {(𝕤)} x) (Unitᵣ {(𝕤)} x₁) A≡B = Unitᵥ x x₁
  goodCases (Unitᵣ {(𝕨)} x) (Unitᵣ {(𝕨)} x₁) A≡B = Unitᵥ x x₁
  goodCases (ne x) (ne x₁) A≡B = ne x x₁
  goodCases (Bᵣ BMΠ _ _ [Π]@(Bᵣ _ _ D _ _))
            (Bᵣ BMΠ _ _ [Π]′@(Bᵣ _ _ D′ _ _)) A≡B =
    case ΠΣ-injectivity (trans (trans (sym (subset* D)) A≡B) (subset* D′)) of λ where
      (_ , _ , PE.refl , PE.refl , _) →
        Bᵥ _ _ _ [Π] [Π]′
  goodCases (Bᵣ (BMΣ 𝕤) _ _ [Σ]@(Bᵣ _ _ D _ _))
            (Bᵣ (BMΣ 𝕤) _ _ [Σ]′@(Bᵣ _ _ D′ _ _)) A≡B =
    case ΠΣ-injectivity (trans (trans (sym (subset* D)) A≡B) (subset* D′)) of λ where
      (_ , _ , PE.refl , PE.refl , _) →
        Bᵥ _ _ _ [Σ] [Σ]′
  goodCases (Bᵣ (BMΣ 𝕨) _ _ [Σ]@(Bᵣ _ _ D _ _))
            (Bᵣ (BMΣ 𝕨) _ _ [Σ]′@(Bᵣ _ _ D′ _ _)) A≡B =
    case ΠΣ-injectivity (trans (trans (sym (subset* D)) A≡B) (subset* D′)) of λ where
      (_ , _ , PE.refl , PE.refl , _) →
        Bᵥ _ _ _ [Σ] [Σ]′
  goodCases (Idᵣ x) (Idᵣ x₁) A≡B = Idᵥ x x₁

  goodCases (Unitᵣ {(𝕤)} x) (Unitᵣ {(𝕨)} x₁) A≡B =
    ⊥-elim (Unitʷ≢Unitˢ (trans (trans (sym (subset* (x₁ ._⊨Unit⟨_⟩_.⇒*-Unit))) (sym A≡B)) (subset* (x ._⊨Unit⟨_⟩_.⇒*-Unit))))
  goodCases (Unitᵣ {(𝕨)} x) (Unitᵣ {(𝕤)} x₁) A≡B =
    ⊥-elim (Unitʷ≢Unitˢ (trans (trans (sym (subset* (x ._⊨Unit⟨_⟩_.⇒*-Unit))) A≡B) (subset* (x₁ ._⊨Unit⟨_⟩_.⇒*-Unit))))
  goodCases (Bᵣ BMΠ _ _ x) (Bᵣ (BMΣ s) _ _ x₁) A≡B =
    ⊥-elim (Π≢Σⱼ (trans (trans (sym (subset* (x ._⊨ΠΣ⟨_,_,_⟩_.D))) A≡B) (subset* (x₁ ._⊨ΠΣ⟨_,_,_⟩_.D))))
  goodCases (Bᵣ (BMΣ s) _ _ x) (Bᵣ BMΠ _ _ x₁) A≡B =
    ⊥-elim (Π≢Σⱼ (trans (trans (sym (subset* (x₁ ._⊨ΠΣ⟨_,_,_⟩_.D))) (sym A≡B)) (subset* (x ._⊨ΠΣ⟨_,_,_⟩_.D))))
  goodCases (Bᵣ (BMΣ 𝕤) _ _ x) (Bᵣ (BMΣ 𝕨) _ _ x₁) A≡B =
    ⊥-elim (Σˢ≢Σʷⱼ (trans (trans (sym (subset* (x ._⊨ΠΣ⟨_,_,_⟩_.D))) A≡B) (subset* (x₁ ._⊨ΠΣ⟨_,_,_⟩_.D))))
  goodCases (Bᵣ (BMΣ 𝕨) _ _ x) (Bᵣ (BMΣ 𝕤) _ _ x₁) A≡B =
    ⊥-elim (Σˢ≢Σʷⱼ (trans (trans (sym (subset* (x₁ ._⊨ΠΣ⟨_,_,_⟩_.D))) (sym A≡B)) (subset* (x ._⊨ΠΣ⟨_,_,_⟩_.D))))

  goodCases (Uᵣ x) (ℕᵣ x₁) A≡B =
    ⊥-elim (U≢ℕ (trans (trans (sym (subset* (_⊨U_.⇒*U x))) A≡B) (subset* x₁)))
  goodCases (Uᵣ x) (Emptyᵣ x₁) A≡B =
    ⊥-elim (U≢Emptyⱼ (trans (trans (sym (subset* (_⊨U_.⇒*U x))) A≡B) (subset* x₁)))
  goodCases (Uᵣ x) (Unitᵣ x₁) A≡B =
    ⊥-elim (U≢Unitⱼ (trans (trans (sym (subset* (_⊨U_.⇒*U x))) A≡B) (subset* (_⊨Unit⟨_⟩_.⇒*-Unit x₁))))
  goodCases (Uᵣ x) (ne′ x₁ x₂ x₃) A≡B =
    ⊥-elim (I.U≢ne x₃ (trans (trans (sym (subset* (_⊨U_.⇒*U x))) A≡B) (subset* x₂)))
  goodCases (Uᵣ x) (Bᵣ _ _ _ x₁) A≡B =
    ⊥-elim (U≢ΠΣⱼ (trans (trans (sym (subset* (_⊨U_.⇒*U x))) A≡B) (subset* (_⊨ΠΣ⟨_,_,_⟩_.D x₁))))
  goodCases (Uᵣ x) (Idᵣ x₁) A≡B =
    ⊥-elim (Id≢U (trans (trans (sym (subset* (x₁ ._⊨Id_.⇒*Id))) (sym A≡B)) (subset* (x ._⊨U_.⇒*U))))
  goodCases (ℕᵣ x) (Uᵣ x₁) A≡B =
    ⊥-elim (U≢ℕ (trans (trans (sym (subset* (x₁ ._⊨U_.⇒*U))) (sym A≡B)) (subset* x)))
  goodCases (ℕᵣ x) (Emptyᵣ x₁) A≡B =
    ⊥-elim (ℕ≢Emptyⱼ (trans (trans (sym (subset* x)) A≡B) (subset* x₁)))
  goodCases (ℕᵣ x) (Unitᵣ x₁) A≡B =
    ⊥-elim (ℕ≢Unitⱼ (trans (trans (sym (subset* x)) A≡B) (subset* (x₁ ._⊨Unit⟨_⟩_.⇒*-Unit))))
  goodCases (ℕᵣ x) (ne′ x₁ x₂ x₃) A≡B =
    ⊥-elim (I.ℕ≢ne x₃ (trans (trans (sym (subset* x)) A≡B) (subset* x₂)))
  goodCases (ℕᵣ x) (Bᵣ _ _ _ x₁) A≡B =
    ⊥-elim (ℕ≢ΠΣⱼ (trans (trans (sym (subset* x)) A≡B) (subset* (_⊨ΠΣ⟨_,_,_⟩_.D x₁))))
  goodCases (ℕᵣ x) (Idᵣ x₁) A≡B =
    ⊥-elim (Id≢ℕ (trans (trans (sym (subset* (x₁ ._⊨Id_.⇒*Id))) (sym A≡B)) (subset* x)))
  goodCases (Emptyᵣ x) (Uᵣ x₁) A≡B =
    ⊥-elim (U≢Emptyⱼ (trans (trans (sym (subset* (x₁ ._⊨U_.⇒*U))) (sym A≡B)) (subset* x)))
  goodCases (Emptyᵣ x) (ℕᵣ x₁) A≡B =
    ⊥-elim (ℕ≢Emptyⱼ (trans (trans (sym (subset* x₁)) (sym A≡B)) (subset* x)))
  goodCases (Emptyᵣ x) (Unitᵣ x₁) A≡B =
    ⊥-elim (Empty≢Unitⱼ (trans (trans (sym (subset* x)) A≡B) (subset* (x₁ ._⊨Unit⟨_⟩_.⇒*-Unit))))
  goodCases (Emptyᵣ x) (ne′ x₁ x₂ x₃) A≡B =
    ⊥-elim (Empty≢neⱼ x₃ (trans (trans (sym (subset* x)) A≡B) (subset* x₂)))
  goodCases (Emptyᵣ x) (Bᵣ _ _ _ x₁) A≡B =
    ⊥-elim (Empty≢ΠΣⱼ (trans (trans (sym (subset* x)) A≡B) (subset* (x₁ ._⊨ΠΣ⟨_,_,_⟩_.D))))
  goodCases (Emptyᵣ x) (Idᵣ x₁) A≡B =
    ⊥-elim (Id≢Empty (trans (trans (sym (subset* (x₁ ._⊨Id_.⇒*Id))) (sym A≡B)) (subset* x)))
  goodCases (Unitᵣ x) (Uᵣ x₁) A≡B =
    ⊥-elim (U≢Unitⱼ (trans (trans (sym (subset* (x₁ ._⊨U_.⇒*U))) (sym A≡B)) (subset* (x ._⊨Unit⟨_⟩_.⇒*-Unit))))
  goodCases (Unitᵣ x) (ℕᵣ x₁) A≡B =
    ⊥-elim (ℕ≢Unitⱼ (trans (trans (sym (subset* x₁)) (sym A≡B)) (subset* (x ._⊨Unit⟨_⟩_.⇒*-Unit))))
  goodCases (Unitᵣ x) (Emptyᵣ x₁) A≡B =
    ⊥-elim (Empty≢Unitⱼ (trans (trans (sym (subset* x₁)) (sym A≡B)) (subset* (x ._⊨Unit⟨_⟩_.⇒*-Unit))))
  goodCases (Unitᵣ x) (ne′ x₁ x₂ x₃) A≡B =
    ⊥-elim (Unit≢neⱼ x₃ (trans (trans (sym (subset* (x ._⊨Unit⟨_⟩_.⇒*-Unit))) A≡B) (subset* x₂)))
  goodCases (Unitᵣ x) (Bᵣ _ _ _ x₁) A≡B =
    ⊥-elim (Unit≢ΠΣⱼ (trans (trans (sym (subset* (x ._⊨Unit⟨_⟩_.⇒*-Unit))) A≡B) (subset* (x₁ ._⊨ΠΣ⟨_,_,_⟩_.D))))
  goodCases (Unitᵣ x) (Idᵣ x₁) A≡B =
    ⊥-elim (Id≢Unit (trans (trans (sym (subset* (x₁ ._⊨Id_.⇒*Id))) (sym A≡B)) (subset* (x ._⊨Unit⟨_⟩_.⇒*-Unit))))
  goodCases (ne′ x x₁ x₂) (Uᵣ x₃) A≡B =
    ⊥-elim (I.U≢ne x₂ (trans (trans (sym (subset* (x₃ ._⊨U_.⇒*U))) (sym A≡B)) (subset* x₁)))
  goodCases (ne′ x x₁ x₂) (ℕᵣ x₃) A≡B =
    ⊥-elim (I.ℕ≢ne x₂ (trans (trans (sym (subset* x₃)) (sym A≡B)) (subset* x₁)))
  goodCases (ne′ x x₁ x₂) (Emptyᵣ x₃) A≡B =
    ⊥-elim (Empty≢neⱼ x₂ (trans (trans (sym (subset* x₃)) (sym A≡B)) (subset* x₁)))
  goodCases (ne′ x x₁ x₂) (Unitᵣ x₃) A≡B =
    ⊥-elim (Unit≢neⱼ x₂ (trans (trans (sym (subset* (x₃ ._⊨Unit⟨_⟩_.⇒*-Unit))) (sym A≡B)) (subset* x₁)))
  goodCases (ne′ x x₁ x₂) (Bᵣ _ _ _ x₃) A≡B =
    ⊥-elim (I.ΠΣ≢ne x₂ (trans (trans (sym (subset* (x₃ ._⊨ΠΣ⟨_,_,_⟩_.D))) (sym A≡B)) (subset* x₁)))
  goodCases (ne′ x x₁ x₂) (Idᵣ x₃) A≡B =
    ⊥-elim (I.Id≢ne x₂ (trans (trans (sym (subset* (x₃ ._⊨Id_.⇒*Id))) (sym A≡B)) (subset* x₁)))
  goodCases (Bᵣ _ _ _ x) (Uᵣ x₁) A≡B =
    ⊥-elim (U≢ΠΣⱼ (trans (trans (sym (subset* (x₁ ._⊨U_.⇒*U))) (sym A≡B)) (subset* (x ._⊨ΠΣ⟨_,_,_⟩_.D))))
  goodCases (Bᵣ _ _ _ x) (ℕᵣ x₁) A≡B =
    ⊥-elim (ℕ≢ΠΣⱼ (trans (trans (sym (subset* x₁)) (sym A≡B)) (subset* (x ._⊨ΠΣ⟨_,_,_⟩_.D))))
  goodCases (Bᵣ _ _ _ x) (Emptyᵣ x₁) A≡B =
    ⊥-elim (Empty≢ΠΣⱼ (trans (trans (sym (subset* x₁)) (sym A≡B)) (subset* (x ._⊨ΠΣ⟨_,_,_⟩_.D))))
  goodCases (Bᵣ _ _ _ x) (Unitᵣ x₁) A≡B =
    ⊥-elim (Unit≢ΠΣⱼ (trans (trans (sym (subset* (x₁ ._⊨Unit⟨_⟩_.⇒*-Unit))) (sym A≡B)) (subset* (x ._⊨ΠΣ⟨_,_,_⟩_.D))))
  goodCases (Bᵣ _ _ _ x) (ne′ x₁ x₂ x₃) A≡B =
    ⊥-elim (I.ΠΣ≢ne x₃ (trans (trans (sym (subset* (x ._⊨ΠΣ⟨_,_,_⟩_.D))) A≡B) (subset* x₂)))
  goodCases (Bᵣ _ _ _ x) (Idᵣ x₁) A≡B =
    ⊥-elim (I.Id≢ΠΣ (trans (trans (sym (subset* (x₁ ._⊨Id_.⇒*Id))) (sym A≡B)) (subset* (x ._⊨ΠΣ⟨_,_,_⟩_.D))))
  goodCases (Idᵣ x) (Uᵣ x₁) A≡B =
    ⊥-elim (Id≢U (trans (trans (sym (subset* (x ._⊨Id_.⇒*Id))) A≡B) (subset* (x₁ ._⊨U_.⇒*U))))
  goodCases (Idᵣ x) (ℕᵣ x₁) A≡B =
    ⊥-elim (Id≢ℕ (trans (trans (sym (subset* (x ._⊨Id_.⇒*Id))) A≡B) (subset* x₁)))
  goodCases (Idᵣ x) (Emptyᵣ x₁) A≡B =
    ⊥-elim (Id≢Empty (trans (trans (sym (subset* (x ._⊨Id_.⇒*Id))) A≡B) (subset* x₁)))
  goodCases (Idᵣ x) (Unitᵣ x₁) A≡B =
    ⊥-elim (Id≢Unit (trans (trans (sym (subset* (x ._⊨Id_.⇒*Id))) A≡B) (subset* (x₁ ._⊨Unit⟨_⟩_.⇒*-Unit))))
  goodCases (Idᵣ x) (ne′ x₁ x₂ x₃) A≡B =
    ⊥-elim (I.Id≢ne x₃ (trans (trans (sym (subset* (x ._⊨Id_.⇒*Id))) A≡B) (subset* x₂)))
  goodCases (Idᵣ x) (Bᵣ _ _ _ x₁) A≡B =
    ⊥-elim (I.Id≢ΠΣ (trans (trans (sym (subset* (x ._⊨Id_.⇒*Id))) A≡B) (subset* (x₁ ._⊨ΠΣ⟨_,_,_⟩_.D))))

opaque

  -- Two proofs that a type is in the relation are in the ShapeView.

  goodCasesRefl :
    ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
    ([A] [A]′ : Γ ⊨ A) → ShapeView Γ A A [A] [A]′
  goodCasesRefl [A] [A]′ = goodCases [A] [A]′ (refl (⊨→⊢ [A]))

------------------------------------------------------------------------
-- Introduction and Elimination lemmas for the logical relation.
-- Note that the introduction lemmas are deliberately not made opaque.

opaque

  -- An elimination lemma for ΠΣ

  ΠΣ-elim :
    Γ ⊨ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊨ A × (∀ {t} → Γ ⊢ t ∷ A → Γ ⊨ B [ t ]₀)
  ΠΣ-elim (Uᵣ x) =
    case whnfRed* (x ._⊨U_.⇒*U) ΠΣₙ of λ ()
  ΠΣ-elim (ℕᵣ x) =
    case whnfRed* x ΠΣₙ of λ ()
  ΠΣ-elim (Emptyᵣ x) =
    case whnfRed* x ΠΣₙ of λ ()
  ΠΣ-elim (Unitᵣ x) =
    case whnfRed* (x ._⊨Unit⟨_⟩_.⇒*-Unit) ΠΣₙ of λ ()
  ΠΣ-elim (ne′ N D neN) =
    case whnfRed* D ΠΣₙ of λ {PE.refl → case neN of λ ()}
  ΠΣ-elim (Bᵣ′ b p q F G D [F] [G]) =
    case whnfRed* D ΠΣₙ of λ {PE.refl →
      [F] , (λ {t} ⊢t → [G] {t = t} ⊢t)}
  ΠΣ-elim (Idᵣ x) =
    case whnfRed* (x ._⊨Id_.⇒*Id) ΠΣₙ of λ ()

-- An introduction lemma for U l.

U-intro : ⊢ Γ → Γ ⊨ U l
U-intro ⊢Γ = Uᵣ′ _ (id (Uⱼ ⊢Γ))

-- An introduction lemma for ℕ.

ℕ-intro : ⊢ Γ → Γ ⊨ ℕ
ℕ-intro ⊢Γ = ℕᵣ (id (ℕⱼ ⊢Γ))

-- An introduction lemma for Empty.

Empty-intro : ⊢ Γ → Γ ⊨ Empty
Empty-intro ⊢Γ = Emptyᵣ (id (Emptyⱼ ⊢Γ))

-- An introduction lemma for Unit s l.

Unit-intro : ⊢ Γ → Unit-allowed s → Γ ⊨ Unit s l
Unit-intro ⊢Γ ok = Unitᵣ′ _ (id (Unitⱼ ⊢Γ ok))

-- An introduction lemma for Id.

Id-intro :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  Γ ⊢ A → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊨ Id A t u
Id-intro ⊢A ⊢t ⊢u = Idᵣ′ _ _ _ (id (Idⱼ ⊢A ⊢t ⊢u)) (⊢→⊨ ⊢A) ⊢t ⊢u

-- An introduction lemma for ΠΣ.

ΠΣ-intro′ :
  Γ ⊨ A →
  (∀ {t} → Γ ⊢ t ∷ A → Γ ⊨ B [ t ]₀) →
  Γ »∙ A ⊢ B →
  ΠΣ-allowed b p q →
  Γ ⊨ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
ΠΣ-intro′ ⊨A ⊨B ⊢B ok = Bᵣ′ _ _ _ _ _ (id (ΠΣⱼ ⊢B ok)) ⊨A ⊨B

-- Another introduction lemma for ΠΣ.

ΠΣ-intro :
  ⦃ ok : No-equality-reflection or-empty (Γ .vars) ⦄ →
  Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  Γ ⊨ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
ΠΣ-intro ⊢Π =
  let ⊢A , ⊢B , ok = inversion-ΠΣ ⊢Π
  in  ΠΣ-intro′ (⊢→⊨ ⊢A) (λ ⊢t → ⊢→⊨ (substType ⊢B ⊢t)) ⊢B ok
