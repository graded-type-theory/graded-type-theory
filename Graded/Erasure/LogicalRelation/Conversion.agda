------------------------------------------------------------------------
-- Type conversion lemmata for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation.Conversion
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as
open Modality 𝕄
open Type-restrictions R

open import Graded.Erasure.LogicalRelation as
import Graded.Erasure.Target as T

open import Definition.LogicalRelation.Simplified R
open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Type R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    n : Nat
    Γ : Con Term n
    A B t : Term n
    v : T.Term n
    p : M

private opaque

  -- Conversion of logical relation for erasure using ShapeView

  convTermʳ′ : {[A] : ts » Δ ⊨ A}
               {[B] : ts » Δ ⊨ B}
             → ts » Δ ⊢ A ≡ B
             → ShapeView (ts » Δ) A B [A] [B]
             → t ® v ∷ A / [A]
             → t ® v ∷ B / [B]
  convTermʳ′ _ (Levelᵥ _ _) t®v = t®v
  convTermʳ′ A≡B (Uᵥ UA UB) t®v = t®v
  convTermʳ′
    {A} {B} A≡B
    (Liftᵥ (Liftᵣ {level = l₁} {Ty = A′} A⇒*Lift ⊩A′)
       (Liftᵣ {level = l₂} {Ty = B′} B⇒*Lift ⊩B′))
    t®v =
    let _ , A′≡B′ =
          Lift-injectivity
            (Lift l₁ A′  ≡˘⟨ subset* A⇒*Lift ⟩⊢
             A           ≡⟨ A≡B ⟩⊢
             B           ≡⟨ subset* B⇒*Lift ⟩⊢∎
             Lift l₂ B′  ∎)
    in
    convTermʳ′ A′≡B′ (goodCases ⊩A′ ⊩B′ (A′≡B′)) t®v
  convTermʳ′ A≡B (ℕᵥ ℕA ℕB) t®v = t®v
  convTermʳ′ _ (Unitᵥ _ _) t®v = t®v
  convTermʳ′
    A≡B
    (Bᵥ BMΠ p q (Bᵣ F G A⇒Π [F] [G])
       (Bᵣ F₁ G₁ B⇒Π₁ [F]₁ [G]₁))
    t®v
       with is-𝟘? p
  ... | yes PE.refl = t®v .proj₁ , λ ⊢a₁ →
    let Π≡Π₁ = reduction′ A⇒Π B⇒Π₁ A≡B
        F≡F₁ , G≡G₁ , _ , _ = ΠΣ-injectivity Π≡Π₁
        ⊢a = conv ⊢a₁ (sym F≡F₁)
        G[a]≡G₁[a] = G≡G₁ (refl ⊢a)
    in  convTermʳ′ G[a]≡G₁[a]
          (goodCases ([G] ⊢a) ([G]₁ ⊢a₁) G[a]≡G₁[a])
          (t®v .proj₂ ⊢a)
  ... | no p≢𝟘 = t®v .proj₁ , λ ⊢a₁ a®w′ →
    let Π≡Π₁ = reduction′ A⇒Π B⇒Π₁ A≡B
        F≡F₁ , G≡G₁ , _ , _ = ΠΣ-injectivity Π≡Π₁
        ⊢a = conv ⊢a₁ (sym F≡F₁)
        G[a]≡G₁[a] = G≡G₁ (refl ⊢a)
        a®w = convTermʳ′ (sym F≡F₁)
                (goodCases [F]₁ [F] (sym F≡F₁)) a®w′
    in  convTermʳ′ G[a]≡G₁[a]
          (goodCases ([G] ⊢a) ([G]₁ ⊢a₁) G[a]≡G₁[a])
          (t®v .proj₂ ⊢a a®w)
  convTermʳ′ {v = v}
    A≡B
    (Bᵥ (BMΣ _) p _ (Bᵣ F G A⇒Σ [F] [G])
       (Bᵣ F₁ G₁ B⇒Σ₁ [F]₁ [G]₁))
    (t₁ , t₂ , t⇒t′ , ⊢t₁ , v₂ , t₂®v₂ , extra) =
    let Σ≡Σ₁ = reduction′ A⇒Σ B⇒Σ₁ A≡B
        F≡F₁ , G≡G₁ , _ = ΠΣ-injectivity Σ≡Σ₁
        ⊢t₁′ = conv ⊢t₁ F≡F₁
        G[t₁]≡G₁[t₁] = G≡G₁ (refl ⊢t₁)
        t₂®v₂′ = convTermʳ′ G[t₁]≡G₁[t₁] (goodCases ([G] ⊢t₁) ([G]₁ ⊢t₁′) G[t₁]≡G₁[t₁]) t₂®v₂
        extra′ =
          Σ-®-elim (λ _ → Σ-® _ [F]₁ t₁ v v₂ p) extra
                   Σ-®-intro-𝟘
                   λ v₁ v⇒p t₁®v₁ →
                     let t₁®v₁′ = convTermʳ′ F≡F₁ (goodCases [F] [F]₁ F≡F₁) t₁®v₁
                     in  Σ-®-intro-ω v₁ v⇒p t₁®v₁′
    in  t₁ , t₂ , conv-⇛ t⇒t′ Σ≡Σ₁ , ⊢t₁′ , v₂
           , t₂®v₂′ , extra′
  convTermʳ′ {A} {B} A≡B (Idᵥ ⊩A ⊩B) (rflᵣ t⇒*rfl ⇒*↯) =
    rflᵣ
      (conv-⇛ t⇒*rfl
         (Id (_⊨Id_.Ty ⊩A) (_⊨Id_.lhs ⊩A) (_⊨Id_.rhs ⊩A)  ≡˘⟨ subset* (_⊨Id_.⇒*Id ⊩A) ⟩⊢
          A                                                  ≡⟨ A≡B ⟩⊢
          B                                                  ≡⟨ subset* (_⊨Id_.⇒*Id ⊩B) ⟩⊢∎
          Id (_⊨Id_.Ty ⊩B) (_⊨Id_.lhs ⊩B) (_⊨Id_.rhs ⊩B)  ∎))
      ⇒*↯
  -- Impossible cases
  convTermʳ′ _ (Emptyᵥ _ _) ()
  convTermʳ′ _ (ne record{} _) ()

opaque

  -- Conversion of logical relation for erasure

  convTermʳ : ∀ {A B t v}
            → ([A] : ts » Δ ⊨ A)
              ([B] : ts » Δ ⊨ B)
            → ts » Δ ⊢ A ≡ B
            → t ® v ∷ A / [A]
            → t ® v ∷ B / [B]
  convTermʳ [A] [B] A≡B t®v =
    convTermʳ′ A≡B (goodCases [A] [B] A≡B) t®v
