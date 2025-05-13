------------------------------------------------------------------------
-- Irrelevance lemmata for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality


module Definition.LogicalRelation.Irrelevance
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (Wk; K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Escape R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Kit R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Primitive R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Reflexivity R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Whnf R ⦃ eqrel ⦄
open import Definition.LogicalRelation.ShapeView R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Level hiding (_⊔_)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    n : Nat
    Γ Γ′ : Con Term n
    A A′ B B′ C C′ t u : Term _
    l l′ : Universe-level

-- Irrelevance for level reflection.

opaque
  unfolding ↑ᵘ′_

  mutual
    ↑ᵘ′-irrelevance
      : ∀ {t} ([t] : Γ ⊩Level t ∷Level) ([t]′ : Γ ⊩Level t ∷Level)
      → ↑ᵘ′ [t] PE.≡ ↑ᵘ′ [t]′
    ↑ᵘ′-irrelevance (Levelₜ _ t⇒ [t]) (Levelₜ _ t⇒′ [t]′) =
      case whrDet*Term (t⇒ , level [t]) (t⇒′ , level [t]′) of λ {
        PE.refl →
      ↑ᵘ′-prop-irrelevance [t] [t]′ }

    ↑ᵘ′-prop-irrelevance
      : ∀ {t} ([t] : Level-prop Γ t) ([t]′ : Level-prop Γ t)
      → ↑ᵘ′-prop [t] PE.≡ ↑ᵘ′-prop [t]′
    ↑ᵘ′-prop-irrelevance zeroᵘᵣ zeroᵘᵣ = PE.refl
    ↑ᵘ′-prop-irrelevance (sucᵘᵣ x) (sucᵘᵣ y) = PE.cong 1+ (↑ᵘ′-irrelevance x y)
    ↑ᵘ′-prop-irrelevance (neLvl x) (neLvl y) = ↑ᵘ′-neprop-irrelevance x y
    ↑ᵘ′-prop-irrelevance zeroᵘᵣ (neLvl (ne (neNfₜ₌ _ () neM k≡m)))
    ↑ᵘ′-prop-irrelevance (sucᵘᵣ x) (neLvl (ne (neNfₜ₌ _ () neM k≡m)))
    ↑ᵘ′-prop-irrelevance (neLvl (ne (neNfₜ₌ _ () neM k≡m))) zeroᵘᵣ
    ↑ᵘ′-prop-irrelevance (neLvl (ne (neNfₜ₌ _ () neM k≡m))) (sucᵘᵣ x₁)

    ↑ᵘ′-neprop-irrelevance
      : ∀ {t} ([t] : neLevel-prop Γ t) ([t]′ : neLevel-prop Γ t)
      → ↑ᵘ′-neprop [t] PE.≡ ↑ᵘ′-neprop [t]′
    ↑ᵘ′-neprop-irrelevance (maxᵘˡᵣ x x₁) (maxᵘˡᵣ y x₂) =
      PE.cong₂ _⊔_ (↑ᵘ′-neprop-irrelevance x y) (↑ᵘ′-irrelevance x₁ x₂)
    ↑ᵘ′-neprop-irrelevance (maxᵘʳᵣ x x₁) (maxᵘʳᵣ x₂ y) =
      PE.cong₂ _⊔_ (PE.cong 1+ (↑ᵘ′-irrelevance x x₂)) (↑ᵘ′-neprop-irrelevance x₁ y)
    ↑ᵘ′-neprop-irrelevance (ne x) (ne x₁) = PE.refl
    ↑ᵘ′-neprop-irrelevance (maxᵘˡᵣ x x₁) (maxᵘʳᵣ x₂ y) = case nelevel x of λ { (ne ()) }
    ↑ᵘ′-neprop-irrelevance (maxᵘˡᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m))
    ↑ᵘ′-neprop-irrelevance (maxᵘʳᵣ x x₁) (maxᵘˡᵣ y x₂) = case nelevel y of λ { (ne ()) }
    ↑ᵘ′-neprop-irrelevance (maxᵘʳᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m))
    ↑ᵘ′-neprop-irrelevance (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘˡᵣ y x₁)
    ↑ᵘ′-neprop-irrelevance (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘʳᵣ x₁ y)

↑ᵘ-irrelevance
  : ∀ {t} {[t] : Γ ⊩Level t ∷Level} {[t]′ : Γ ⊩Level t ∷Level}
  → ↑ᵘ [t] PE.≡ ↑ᵘ [t]′
↑ᵘ-irrelevance {[t]} {[t]′} = PE.cong 0ᵘ+_ (↑ᵘ′-irrelevance [t] [t]′)

↑ᵘ′-refl
  : ([t] : Γ ⊩Level t ∷Level)
  → ↑ᵘ′ wf-Level-eq (reflLevel [t]) .proj₁ PE.≡ ↑ᵘ′ [t]
↑ᵘ′-refl [t] = ↑ᵘ′-irrelevance (wf-Level-eq (reflLevel [t]) .proj₁) [t]

opaque
  unfolding ↑ᵘ′_ ⊩maxᵘ

  -- Level reflection sends maxᵘ to ⊔ᵘ.

  ↑ᵘ′-maxᵘ :
    ([t] : Γ ⊩Level t ∷Level) →
    ([u] : Γ ⊩Level u ∷Level) →
    ↑ᵘ′ ⊩maxᵘ [t] [u] PE.≡ ↑ᵘ′ [t] ⊔ ↑ᵘ′ [u]
  ↑ᵘ′-maxᵘ [t]@(Levelₜ t′ t⇒ zeroᵘᵣ) [u]@(Levelₜ u′ u⇒ propu) = PE.refl
  ↑ᵘ′-maxᵘ [t]@(Levelₜ t′ t⇒ (sucᵘᵣ x)) [u]@(Levelₜ u′ u⇒ zeroᵘᵣ) = PE.refl
  ↑ᵘ′-maxᵘ [t]@(Levelₜ t′ t⇒ (sucᵘᵣ x)) [u]@(Levelₜ u′ u⇒ (sucᵘᵣ x₁)) = PE.cong 1+ (↑ᵘ′-maxᵘ x x₁)
  ↑ᵘ′-maxᵘ [t]@(Levelₜ t′ t⇒ (sucᵘᵣ x)) [u]@(Levelₜ u′ u⇒ (neLvl x₁)) = PE.refl
  ↑ᵘ′-maxᵘ [t]@(Levelₜ t′ t⇒ (neLvl x)) [u]@(Levelₜ u′ u⇒ propu) = PE.refl

  ↑ᵘ-maxᵘ :
    ([t] : Γ ⊩Level t ∷Level) →
    ([u] : Γ ⊩Level u ∷Level) →
    ↑ᵘ ⊩maxᵘ [t] [u] PE.≡ ↑ᵘ [t] ⊔ᵘ ↑ᵘ [u]
  ↑ᵘ-maxᵘ [t] [u] = PE.cong 0ᵘ+_ (↑ᵘ′-maxᵘ [t] [u])

opaque
  unfolding ↑ᵘ′_ ⊩sucᵘ

  ↑ᵘ′-prop-zeroᵘ : ([0] : Level-prop Γ zeroᵘ) → ↑ᵘ′-prop [0] PE.≡ 0
  ↑ᵘ′-prop-zeroᵘ zeroᵘᵣ = PE.refl
  ↑ᵘ′-prop-zeroᵘ (neLvl n) = case nelevel n of λ { (ne ()) }

  ↑ᵘ′-zeroᵘ : ([0] : Γ ⊩Level zeroᵘ ∷Level) → ↑ᵘ′ [0] PE.≡ 0
  ↑ᵘ′-zeroᵘ (Levelₜ _ 0⇒ prop) with whnfRed*Term 0⇒ zeroᵘₙ
  ... | PE.refl = ↑ᵘ′-prop-zeroᵘ prop

  ↑ᵘ′-prop-sucᵘ
    : ∀ {t} ([t+1] : Level-prop Γ (sucᵘ t))
    → ∃ λ ([t] : Γ ⊩Level t ∷Level) → ↑ᵘ′-prop [t+1] PE.≡ 1+ (↑ᵘ′ [t])
  ↑ᵘ′-prop-sucᵘ (sucᵘᵣ x) = x , PE.refl
  ↑ᵘ′-prop-sucᵘ (neLvl n) = case nelevel n of λ { (ne ()) }

  mutual
    ↑ᵘ′-cong
      : ∀ {t u} ([t] : Γ ⊩Level t ∷Level) ([u] : Γ ⊩Level u ∷Level)
      → Γ ⊩Level t ≡ u ∷Level
      → ↑ᵘ′ [t] PE.≡ ↑ᵘ′ [u]
    ↑ᵘ′-cong (Levelₜ _ t⇒ [t]) (Levelₜ _ u⇒ [u]) (Levelₜ₌ _ _ t⇒′ u⇒′ t≡u) =
      case whrDet*Term (t⇒ , level [t]) (t⇒′ , lsplit t≡u .proj₁) of λ {
        PE.refl →
      case whrDet*Term (u⇒ , level [u]) (u⇒′ , lsplit t≡u .proj₂) of λ {
        PE.refl →
      ↑ᵘ′-prop-cong [t] [u] t≡u }}

    ↑ᵘ′-prop-cong
      : ∀ {t u} ([t] : Level-prop Γ t) ([u] : Level-prop Γ u)
      → [Level]-prop Γ t u
      → ↑ᵘ′-prop [t] PE.≡ ↑ᵘ′-prop [u]
    ↑ᵘ′-prop-cong x y zeroᵘᵣ = PE.trans (↑ᵘ′-prop-zeroᵘ x) (PE.sym (↑ᵘ′-prop-zeroᵘ y))
    ↑ᵘ′-prop-cong x y (sucᵘᵣ z) =
      let x′ , x≡ = ↑ᵘ′-prop-sucᵘ x
          y′ , y≡ = ↑ᵘ′-prop-sucᵘ y
      in PE.trans x≡ (PE.trans (PE.cong 1+ (↑ᵘ′-cong x′ y′ z)) (PE.sym y≡))
    ↑ᵘ′-prop-cong (neLvl x) (neLvl y) (neLvl z) = ↑ᵘ′-neprop-cong x y z
    ↑ᵘ′-prop-cong zeroᵘᵣ y (neLvl n) = case nelsplit n .proj₁ of λ { (ne ()) }
    ↑ᵘ′-prop-cong (sucᵘᵣ x) y (neLvl n) = case nelsplit n .proj₁ of λ { (ne ()) }
    ↑ᵘ′-prop-cong (neLvl _) zeroᵘᵣ (neLvl n) = case nelsplit n .proj₂ of λ { (ne ())}
    ↑ᵘ′-prop-cong (neLvl _) (sucᵘᵣ _) (neLvl n) = case nelsplit n .proj₂ of λ { (ne ()) }

    ↑ᵘ′-neprop-cong
      : ∀ {t u} ([t] : neLevel-prop Γ t) ([u] : neLevel-prop Γ u)
      → [neLevel]-prop Γ t u
      → ↑ᵘ′-neprop [t] PE.≡ ↑ᵘ′-neprop [u]
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x₄ x₅) (maxᵘˡᵣ y x₇) (maxᵘˡᵣ z x₃) =
      PE.cong₂ _⊔_ (↑ᵘ′-neprop-cong x₄ y z) (↑ᵘ′-cong x₅ x₇ x₃)
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x x₁) (maxᵘʳᵣ x₂ y) (maxᵘʳᵣ x₃ z) =
      PE.cong₂ _⊔_ (PE.cong 1+ (↑ᵘ′-cong x x₂ x₃)) (↑ᵘ′-neprop-cong x₁ y z)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x x₁) y (maxᵘ-zeroʳˡᵣ x₂) =
      let p = ↑ᵘ′-neprop-cong x y x₂
      in PE.trans (PE.cong₂ _⊔_ p (↑ᵘ′-zeroᵘ x₁)) (⊔-identityʳ _)
    ↑ᵘ′-neprop-cong (ne x) (ne x₂) (ne x₁) = PE.refl
    ↑ᵘ′-neprop-cong x y (sym z) = PE.sym (↑ᵘ′-neprop-cong y x z)
    ↑ᵘ′-neprop-cong x y (trans z z₁) =
      let _ , [k′] = wf-[neLevel]-prop z
      in PE.trans (↑ᵘ′-neprop-cong x [k′] z) (↑ᵘ′-neprop-cong [k′] y z₁)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (maxᵘˡᵣ x x₅) x₃) (maxᵘˡᵣ y x₄) (maxᵘ-assoc¹ᵣ z x₁ x₂) =
      PE.trans
        (⊔-assoc (↑ᵘ′-neprop x) (↑ᵘ′ x₅) (↑ᵘ′ x₃))
        (PE.cong₂ _⊔_ (↑ᵘ′-neprop-irrelevance x y) (PE.trans
          (PE.sym (↑ᵘ′-maxᵘ x₅ x₃))
          (↑ᵘ′-irrelevance (⊩maxᵘ x₅ x₃) x₄)))
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₄) x₃) (maxᵘʳᵣ x₅ (maxᵘˡᵣ y x₆)) (maxᵘ-assoc²ᵣ x₁ z x₂) =
      PE.trans
        (⊔-assoc (1+ (↑ᵘ′ x)) (↑ᵘ′-neprop x₄) (↑ᵘ′ x₃))
        (PE.cong₂ _⊔_ (PE.cong 1+ (↑ᵘ′-irrelevance x x₅))
          (PE.cong₂ _⊔_ (↑ᵘ′-neprop-irrelevance x₄ y)
            (↑ᵘ′-irrelevance x₃ x₆)))
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x x₃) (maxᵘʳᵣ x₄ (maxᵘʳᵣ x₅ y)) (maxᵘ-assoc³ᵣ x₁ x₂ z) =
      PE.trans
        (PE.cong₂ _⊔_
          (PE.cong 1+ (PE.trans (↑ᵘ′-irrelevance x (⊩maxᵘ x₄ x₅)) (↑ᵘ′-maxᵘ x₄ x₅)))
          (↑ᵘ′-neprop-irrelevance x₃ y))
        (⊔-assoc (1+ (↑ᵘ′ x₄)) (1+ (↑ᵘ′ x₅)) (↑ᵘ′-neprop y))
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x x₁) (maxᵘˡᵣ y x₂) (maxᵘ-comm¹ᵣ z d w d′) =
      PE.trans
        (⊔-comm (↑ᵘ′-neprop x) (↑ᵘ′ x₁))
        (PE.cong₂ _⊔_ (↑ᵘ′-cong x₁ (⊩neLvl y) d′) (↑ᵘ′-cong (⊩neLvl x) x₂ d))
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x@record{} x₁) (maxᵘˡᵣ y x₂) (maxᵘ-comm²ᵣ z d w) =
      PE.trans
        (⊔-comm (1+ (↑ᵘ′ x)) (↑ᵘ′-neprop x₁))
        (PE.cong₂ _⊔_ (↑ᵘ′-neprop-cong x₁ y w) (↑ᵘ′-cong (⊩sucᵘ x) x₂ d))
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x x₁) y (maxᵘ-idem z w) = PE.trans
      (PE.cong₂ _⊔_
        (↑ᵘ′-neprop-irrelevance x y)
        (PE.sym (↑ᵘ′-cong (⊩neLvl y) x₁ w)))
      (⊔-idem (↑ᵘ′-neprop y))
    -- Absurd cases
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ _ _) (maxᵘʳᵣ _ _) (maxᵘˡᵣ z _) = case nelsplit z .proj₂ of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ _ _) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘˡᵣ z x₃)
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ _ _) _ (maxᵘˡᵣ z _) = case nelsplit z .proj₁ of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) _ (maxᵘˡᵣ _ _)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x _) _ (maxᵘʳᵣ _ _) = case nelevel x of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ _ _) (maxᵘˡᵣ y _) (maxᵘʳᵣ _ _) = case nelevel y of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ _ _) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘʳᵣ _ _)
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) _ (maxᵘʳᵣ _ _)
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ _ _) y (maxᵘ-zeroʳˡᵣ _) = case nelevel y of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) _ (maxᵘ-zeroʳˡᵣ _)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ _ _) _ (ne (neNfₜ₌ _ () neM k≡m))
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ _ _) _ (ne (neNfₜ₌ _ () neM k≡m))
    ↑ᵘ′-neprop-cong (ne _) (maxᵘˡᵣ _ _) (ne (neNfₜ₌ _ neK () k≡m))
    ↑ᵘ′-neprop-cong (ne _) (maxᵘʳᵣ _ _) (ne (neNfₜ₌ _ neK () k≡m))
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₅) x₃) (maxᵘˡᵣ y x₄) (maxᵘ-assoc¹ᵣ z x₁ x₂) = case nelevel y of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (ne (neNfₜ₌ _ () neM k≡m)) x₃) (maxᵘˡᵣ y x₄) (maxᵘ-assoc¹ᵣ z x₁ x₂)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x x₃) (maxᵘʳᵣ x₄ y) (maxᵘ-assoc¹ᵣ z x₁ x₂) = case nelsplit z .proj₁ of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x x₃) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘ-assoc¹ᵣ z x₁ x₂)
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-assoc¹ᵣ z x₁ x₂)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (maxᵘˡᵣ x x₄) x₃) y (maxᵘ-assoc²ᵣ x₁ z x₂) = case nelevel x of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₄) x₃) (maxᵘˡᵣ y x₅) (maxᵘ-assoc²ᵣ x₁ z x₂) = case nelevel y of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₄) x₃) (maxᵘʳᵣ x₅ (maxᵘʳᵣ x₆ y)) (maxᵘ-assoc²ᵣ x₁ z x₂) = case nelevel x₄ of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₄) x₃) (maxᵘʳᵣ x₅ (ne (neNfₜ₌ _ () neM k≡m))) (maxᵘ-assoc²ᵣ x₁ z x₂)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (maxᵘʳᵣ x x₄) x₃) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘ-assoc²ᵣ x₁ z x₂)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ (ne (neNfₜ₌ _ () neM k≡m)) x₃) y (maxᵘ-assoc²ᵣ x₁ z x₂)
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-assoc²ᵣ x₁ z x₂)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x x₃) y (maxᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel x of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x x₃) (maxᵘˡᵣ y x₄) (maxᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel y of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x x₃) (maxᵘʳᵣ x₄ (maxᵘˡᵣ y x₅)) (maxᵘ-assoc³ᵣ x₁ x₂ z) = case nelevel y of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x x₃) (maxᵘʳᵣ x₄ (ne (neNfₜ₌ _ () neM k≡m))) (maxᵘ-assoc³ᵣ x₁ x₂ z)
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x x₃) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘ-assoc³ᵣ x₁ x₂ z)
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-assoc³ᵣ x₁ x₂ z)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x x₁) (maxᵘʳᵣ x₂ y) (maxᵘ-comm¹ᵣ z d w d′) = case nelsplit w .proj₁ of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘ-comm¹ᵣ z d w d′)
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x x₁) y (maxᵘ-comm¹ᵣ z d w d′) = case nelsplit z .proj₁ of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-comm¹ᵣ z d w d′)
    ↑ᵘ′-neprop-cong (maxᵘˡᵣ x x₁) y (maxᵘ-comm²ᵣ z d w) = case nelevel x of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x x₁) (maxᵘʳᵣ x₂ y) (maxᵘ-comm²ᵣ z d w) = case nelevel x₁ of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x x₁) (ne (neNfₜ₌ _ () neM k≡m)) (maxᵘ-comm²ᵣ z d w)
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-comm²ᵣ z d w)
    ↑ᵘ′-neprop-cong (maxᵘʳᵣ x x₁) y (maxᵘ-idem z w) = case nelevel y of λ { (ne ()) }
    ↑ᵘ′-neprop-cong (ne (neNfₜ₌ _ () neM k≡m)) y (maxᵘ-idem z w)

↑ᵘ-cong
  : ∀ {t u} {[t] : Γ ⊩Level t ∷Level} {[u] : Γ ⊩Level u ∷Level}
  → Γ ⊩Level t ≡ u ∷Level → ↑ᵘ [t] PE.≡ ↑ᵘ [u]
↑ᵘ-cong {[t]} {[u]} t≡u = PE.cong 0ᵘ+_ (↑ᵘ′-cong [t] [u] t≡u)

-- Irrelevance for propositionally equal types
irrelevance′ : ∀ {A A′ l}
             → A PE.≡ A′
             → Γ ⊩⟨ l ⟩ A
             → Γ ⊩⟨ l ⟩ A′
irrelevance′ PE.refl [A] = [A]

-- Irrelevance for propositionally equal types and contexts
irrelevanceΓ′ : ∀ {l A A′}
              → Γ PE.≡ Γ′
              → A PE.≡ A′
              → Γ  ⊩⟨ l ⟩ A
              → Γ′ ⊩⟨ l ⟩ A′
irrelevanceΓ′ PE.refl PE.refl [A] = [A]

mutual
  -- Irrelevance for type equality
  irrelevanceEq : ∀ {A B l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEq p q A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B

  -- Irrelevance for type equality with propositionally equal first types
  irrelevanceEq′ : ∀ {A A′ B l l′} (eq : A PE.≡ A′)
                   (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                 → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B / q
  irrelevanceEq′ PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal types
  irrelevanceEq″ : ∀ {A A′ B B′ l l′} (eqA : A PE.≡ A′) (eqB : B PE.≡ B′)
                    (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                  → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B′ / q
  irrelevanceEq″ PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal second types
  irrelevanceEqR′ : ∀ {A B B′ l} (eqB : B PE.≡ B′) (p : Γ ⊩⟨ l ⟩ A)
                  → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l ⟩ A ≡ B′ / p
  irrelevanceEqR′ PE.refl p A≡B = A≡B

  -- Irrelevance for type equality with propositionally equal types
  -- and contexts.
  irrelevanceEq‴ :
    A PE.≡ A′ → B PE.≡ B′ → Γ PE.≡ Γ′ →
    (⊩A : Γ ⊩⟨ l ⟩ A) (⊩A′ : Γ′ ⊩⟨ l′ ⟩ A′) →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A → Γ′ ⊩⟨ l′ ⟩ A′ ≡ B′ / ⊩A′
  irrelevanceEq‴ PE.refl PE.refl PE.refl = irrelevanceEq

  -- Helper for irrelevance of type equality using shape view
  irrelevanceEqT : ∀ {A B l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                       → ShapeView Γ l l′ A A p q
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEqT (Levelᵥ D D′) A≡B = A≡B
  irrelevanceEqT (ℕᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Unitᵥ (Unitᵣ _ _ _ A⇒*Unit₁ _) (Unitᵣ _ _ _ A⇒*Unit₂ _)) (Unit₌ k′ D k≡k′) =
    case Unit-PE-injectivity $
         whrDet* (A⇒*Unit₁ , Unitₙ) (A⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    Unit₌ k′ D k≡k′ }
  irrelevanceEqT
    (ne (ne _ _ D neK _) (ne _ K₁ D₁ neK₁ K≡K₁)) (ne₌ inc M D′ neM K≡M)
    rewrite whrDet* (D , ne! neK) (D₁ , ne! neK₁) =
    ne₌ inc M D′ neM K≡M
  irrelevanceEqT
    {Γ = Γ}
    (Bᵥ W (Bᵣ F G D A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠFG≡ΠF₁G₁       = whrDet* (D , ⟦ W ⟧ₙ) (D₁ , ⟦ W ⟧ₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity W W ΠFG≡ΠF₁G₁
    in  B₌ F′ G′ D′
           (PE.subst (λ x → Γ ⊢ x ≅ ⟦ W ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B)
           (λ {_} {ρ} [ρ] → irrelevanceEq′ (PE.cong (wk ρ) F≡F₁)
                              ([F] [ρ]) ([F]₁ [ρ]) ([F≡F′] [ρ]))
           (λ {_} {ρ} [ρ] [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                         ([F]₁ [ρ]) ([F] [ρ]) [a]₁
              in  irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
                    ([G] [ρ] [a]) ([G]₁ [ρ] [a]₁) ([G≡G′] [ρ] [a]))
  irrelevanceEqT (Uᵥ (Uᵣ _ _ _ D1) (Uᵣ _ _ _ D2)) A≡B
    = case whrDet* (D1 , Uₙ) (D2 , Uₙ) of λ { PE.refl →
        U₌ k′ ⇒*U′ k≡k′ }
    where
    open _⊩₁U≡_/_ A≡B
  irrelevanceEqT (Idᵥ ⊩A@record{} ⊩A′) A≡B =
    case whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_⊩ₗId_.⇒*Id ⊩A′ , Idₙ) of λ {
      PE.refl →
    record
      { ⇒*Id′    = ⇒*Id′
      ; Ty≡Ty′   = irrelevanceEq (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) Ty≡Ty′
      ; lhs≡lhs′ =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) lhs≡lhs′
      ; rhs≡rhs′ =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) rhs≡rhs′
      ; lhs≡rhs→lhs′≡rhs′ =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) ∘→
          lhs≡rhs→lhs′≡rhs′ ∘→
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A′) (_⊩ₗId_.⊩Ty ⊩A)
      ; lhs′≡rhs′→lhs≡rhs =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) ∘→
          lhs′≡rhs′→lhs≡rhs ∘→
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A′) (_⊩ₗId_.⊩Ty ⊩A)
      } }
    where
    open _⊩ₗId_≡_/_ A≡B

--------------------------------------------------------------------------------

  -- Irrelevance for terms
  irrelevanceTerm : ∀ {A t l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                  → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A / q
  irrelevanceTerm p q t = irrelevanceEqTerm p q t

  -- Irrelevance for terms with propositionally equal types
  irrelevanceTerm′ : ∀ {A A′ t l l′} (eq : A PE.≡ A′)
                     (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                   → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A′ / q
  irrelevanceTerm′ PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types and terms
  irrelevanceTerm″ : ∀ {A A′ t t′ l l′}
                      (eqA : A PE.≡ A′) (eqt : t PE.≡ t′)
                      (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                    → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t′ ∷ A′ / q
  irrelevanceTerm″ PE.refl PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types, terms and contexts
  irrelevanceTermΓ″ : ∀ {l l′ A A′ t t′}
                     → Γ PE.≡ Γ′
                     → A PE.≡ A′
                     → t PE.≡ t′
                     → ([A]  : Γ  ⊩⟨ l  ⟩ A)
                       ([A′] : Γ′ ⊩⟨ l′ ⟩ A′)
                     → Γ  ⊩⟨ l  ⟩ t ∷ A  / [A]
                     → Γ′ ⊩⟨ l′ ⟩ t′ ∷ A′ / [A′]
  irrelevanceTermΓ″ PE.refl PE.refl PE.refl [A] [A′] [t] = irrelevanceTerm [A] [A′] [t]

--------------------------------------------------------------------------------

  -- Irrelevance for term equality
  irrelevanceEqTerm : ∀ {A t u l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                    → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTerm p q t≡u = irrelevanceEqTermT (goodCasesRefl p q) t≡u

  -- Irrelevance for term equality with propositionally equal types
  irrelevanceEqTerm′ : ∀ {A A′ t u l l′} (eq : A PE.≡ A′)
                       (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                     → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A′ / q
  irrelevanceEqTerm′ PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Irrelevance for term equality with propositionally equal types and terms
  irrelevanceEqTerm″ : ∀ {A A′ t t′ u u′ l l′}
                        (eqt : t PE.≡ t′) (equ : u PE.≡ u′) (eqA : A PE.≡ A′)
                        (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                      → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t′ ≡ u′ ∷ A′ / q
  irrelevanceEqTerm″ PE.refl PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Helper for irrelevance of term equality using shape view
  irrelevanceEqTermT : ∀ {A t u} {l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                           → ShapeView Γ l l′ A A p q
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTermT (Levelᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (ℕᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Emptyᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Unitᵥ (Unitᵣ _ _ _ A⇒*Unit₁ _) (Unitᵣ _ _ _ A⇒*Unit₂ _)) t≡u =
    case Unit-PE-injectivity $
         whrDet* (A⇒*Unit₁ , Unitₙ) (A⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    t≡u }
  irrelevanceEqTermT
    (ne (ne _ _ D neK K≡K) (ne _ K₁ D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
    with whrDet* (D₁ , ne! neK₁) (D , ne! neK)
  … | PE.refl = neₜ₌ k m d d′ nf
  irrelevanceEqTermT
    {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΠ! x@(Bᵣ F G D A≡A [F] [G] G-ext _)
       x₁@(Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (Πₜ₌ f g d d′ funcF funcG f≡g [f≡g]) =
    case B-PE-injectivity BΠ! BΠ!
           (whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)) of λ where
      (PE.refl , PE.refl , _) →
        Πₜ₌ f g d d′ funcF funcG f≡g
        λ [ρ] ⊩v ⊩w v≡w →
          let ⊩v′ = irrelevanceTerm ([F]₁ [ρ]) ([F] [ρ]) ⊩v in
          irrelevanceEqTerm ([G] [ρ] ⊩v′) ([G]₁ [ρ] ⊩v) $
          [f≡g] [ρ] ⊩v′ (irrelevanceTerm ([F]₁ [ρ]) ([F] [ρ]) ⊩w)
            (irrelevanceEqTerm ([F]₁ [ρ]) ([F] [ρ]) v≡w)
  irrelevanceEqTermT
    {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΣˢ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ pProd rProd p≅r ([fstp] , [fstr] , [fst≡] , [snd≡])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [fstp]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _) ([F]₁ _) [fstp]
        [fstr]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _) ([F]₁ _) [fstr]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _) ([F]₁ _) [fst≡]
        [snd≡]′ = irrelevanceEqTerm′
                    (PE.cong (λ x → wk (lift id) x [ fst _ p ]₀) G≡G₁)
                    ([G] _ [fstp]) ([G]₁ _ [fstp]′) [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) pProd rProd
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            ([fstp]′ , [fstr]′ , [fst≡]′ ,  [snd≡]′)
  irrelevanceEqTermT
    {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΣʷ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ prodₙ prodₙ p≅r
       (PE.refl , PE.refl , PE.refl , PE.refl ,
        [p₁] , [r₁] , [fst≡] , [snd≡])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [p₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                  ([F] _) ([F]₁ _) [p₁]
        [r₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                  ([F] _) ([F]₁ _) [r₁]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _) ([F]₁ _) [fst≡]
        [snd≡]′ = irrelevanceEqTerm′ (PE.cong (λ x → wk (lift id) x [ _ ]₀) G≡G₁)
                    ([G] _ [p₁]) ([G]₁ _ [p₁]′) [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) prodₙ prodₙ
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (PE.refl , PE.refl , PE.refl , PE.refl ,
             [p₁]′ , [r₁]′ , [fst≡]′ ,  [snd≡]′)
  irrelevanceEqTermT
    {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΣʷ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ (ne x) (ne y) p≅r (inc , p~r)) =
    let ΣFG≡ΣF₁G₁ = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        p~r′ = PE.subst (λ x → Γ ⊢ p ~ r ∷ x) ΣFG≡ΣF₁G₁ p~r
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) (ne x) (ne y)
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (inc , p~r′)
  irrelevanceEqTermT
    (Bᵥ BΣʷ record{} _) (Σₜ₌ _ _ _ _ prodₙ (ne _) _ (lift ()))
  irrelevanceEqTermT
    (Bᵥ BΣʷ record{} _) (Σₜ₌ _ _ _ _ (ne _) prodₙ _ (lift ()))
  irrelevanceEqTermT (Uᵥ (Uᵣ k [k] k< ⇒*U1) (Uᵣ k′ [k′] k′< ⇒*U2))
    (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u])
    with whrDet* (⇒*U1 , Uₙ) (⇒*U2 ,  Uₙ)
  ... | PE.refl = Uₜ₌ A B d d′ typeA typeB A≡B _
    (irrelevance-⊩< ↑ᵘ-irrelevance k< k′< [u])
    (irrelevance-⊩<≡ ↑ᵘ-irrelevance k< k′< [t≡u])
  irrelevanceEqTermT
    (Idᵥ ⊩A@record{} ⊩A′) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
    case whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_⊩ₗId_.⇒*Id ⊩A′ , Idₙ) of λ {
      PE.refl →
      _ , _ , t⇒*t′ , u⇒*u′
    , (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
         (ne inc t′-n u′-n t′~u′) →
           ne t′-n , ne u′-n , inc , t′~u′
         (rfl₌ lhs≡rhs) →
             rflₙ , rflₙ
           , irrelevanceEqTerm
               (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) lhs≡rhs) }
