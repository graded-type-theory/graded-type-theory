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

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Properties.Conversion R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Weakening.Restricted R
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Properties R
open import Definition.Typed.Reasoning.Type R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R hiding (wk)

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Unit

private
  variable
    n : Nat
    Γ : Con Term n
    A B t : Term n
    v : T.Term n
    p : M

-- Conversion of logical relation for erasure using ShapeView
-- If t ® v ∷ A and Δ ⊩ A ≡ B then t ® v ∷ B

convTermʳ′ : ∀ {l l′}
           → ([A] : Δ ⊩⟨ l ⟩ A)
             ([B] : Δ ⊩⟨ l′ ⟩ B)
           → Δ ⊢ A ≡ B
           → ShapeView Δ l l′ A B [A] [B]
           → t ®⟨ l ⟩ v ∷ A / [A]
           → t ®⟨ l′ ⟩ v ∷ B / [B]
convTermʳ′ _ _ A≡B (Uᵥ UA UB) t®v = t®v
convTermʳ′ _ _ A≡B (ℕᵥ ℕA ℕB) t®v = t®v
convTermʳ′
  {A} {B} {l} {l′}
  _ _ A≡B (Unitᵥ {s} (Unitₜ A⇒*Unit _) (Unitₜ B⇒*Unit _)) t®v =
  case Unit-injectivity
         (Unit s l  ≡˘⟨ subset* A⇒*Unit ⟩⊢
          A         ≡⟨ A≡B ⟩⊢
          B         ≡⟨ subset* B⇒*Unit ⟩⊢∎
          Unit s l′ ∎) of λ {
    (_ , PE.refl) →
  t®v }
convTermʳ′
  [A] [B] A≡B
  (Bᵥ (BΠ p q) (Bᵣ F G A⇒Π A≡A [F] [G] G-ext _)
     (Bᵣ F₁ G₁ B⇒Π₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
  t®v
     with is-𝟘? p
... | yes PE.refl = t®v .proj₁ , λ [a]′ →
  let Π≡Π₁ = reduction′ A⇒Π B⇒Π₁ A≡B
      F≡F₁ , G≡G₁ , _ , _ = ΠΣ-injectivity Π≡Π₁
      [F₁≡F] = ⊩≡→⊩≡/ ([F]₁ _) $
               PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (PE.sym $ wk-id _)
                 (PE.sym $ wk-id _) $
               reducible-⊩≡ (sym F≡F₁) .proj₂
      [a] = convTerm₁ ([F]₁ (id ⊢Δ)) ([F] (id ⊢Δ)) [F₁≡F] [a]′
      G[a]≡G₁[a] =
        PE.subst₂ (_⊢_≡_ _)
          (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id G)
          (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id G₁) $
        G≡G₁ $ _⊢_≡_∷_.refl $
        PE.subst (_⊢_∷_ _ _) (wk-id _) $
        escapeTerm ([F] (id ⊢Δ)) [a]
      [Ga≡G₁a] = ⊩≡→⊩≡/ ([G] _ _) (reducible-⊩≡ G[a]≡G₁[a] .proj₂)
      t®v′ = t®v .proj₂ [a]
      SV = goodCases ([G] (id ⊢Δ) [a]) ([G]₁ (id ⊢Δ) [a]′) [Ga≡G₁a]
  in  convTermʳ′ ([G] (id ⊢Δ) [a]) ([G]₁ (id ⊢Δ) [a]′) G[a]≡G₁[a] SV t®v′
... | no p≢𝟘 = t®v .proj₁ , λ [a]′ a®w′ →
  let Π≡Π₁ = reduction′ A⇒Π B⇒Π₁ A≡B
      F≡F₁ , G≡G₁ , _ , _ = ΠΣ-injectivity Π≡Π₁
      [F₁≡F] = ⊩≡→⊩≡/ ([F]₁ _) $
               PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (PE.sym $ wk-id _)
                 (PE.sym $ wk-id _) $
               reducible-⊩≡ (sym F≡F₁) .proj₂
      [a] = convTerm₁ ([F]₁ (id ⊢Δ)) ([F] (id ⊢Δ)) [F₁≡F] [a]′
      G[a]≡G₁[a] =
        PE.subst₂ (_⊢_≡_ _)
          (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id G)
          (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id G₁) $
        G≡G₁ $ _⊢_≡_∷_.refl $
        PE.subst (_⊢_∷_ _ _) (wk-id _) $
        escapeTerm ([F] (id ⊢Δ)) [a]
      [Ga≡G₁a] = ⊩≡→⊩≡/ ([G] _ _) (reducible-⊩≡ G[a]≡G₁[a] .proj₂)
      SV = goodCases ([F]₁ (id ⊢Δ)) ([F] (id ⊢Δ)) [F₁≡F]
      F₁≡F = PE.subst₂ (Δ ⊢_≡_) (PE.sym (wk-id F₁)) (PE.sym (wk-id F)) (sym F≡F₁)
      a®w = convTermʳ′ ([F]₁ (id ⊢Δ)) ([F] (id ⊢Δ)) F₁≡F SV a®w′
      t®v′ = t®v .proj₂ [a] a®w
      SV′ = goodCases ([G] (id ⊢Δ) [a]) ([G]₁ (id ⊢Δ) [a]′) [Ga≡G₁a]
  in  convTermʳ′ ([G] (id ⊢Δ) [a]) ([G]₁ (id ⊢Δ) [a]′) G[a]≡G₁[a] SV′ t®v′
convTermʳ′ {v = v}
  [A] [B] A≡B
  (Bᵥ (BΣ _ p _) (Bᵣ F G A⇒Σ A≡A [F] [G] G-ext _)
     (Bᵣ F₁ G₁ B⇒Σ₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
  (t₁ , t₂ , t⇒t′ , [t₁] , v₂ , t₂®v₂ , extra) =
  let Σ≡Σ₁ = reduction′ A⇒Σ B⇒Σ₁ A≡B
      F≡F₁ , G≡G₁ , _ = ΠΣ-injectivity Σ≡Σ₁
      [F]′ = [F] (id ⊢Δ)
      [F]₁′ = [F]₁ (id ⊢Δ)
      [F≡F₁] = ⊩≡→⊩≡/ [F]′ $
               PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (PE.sym $ wk-id _)
                 (PE.sym $ wk-id _) $
               reducible-⊩≡ F≡F₁ .proj₂
      F≡F₁′ = PE.subst₂ (Δ ⊢_≡_) (PE.sym (wk-id F)) (PE.sym (wk-id F₁)) F≡F₁
      [t₁]′ = convTerm₁ [F]′ [F]₁′ [F≡F₁] [t₁]
      G[t₁]≡G₁[t₁] =
        PE.subst₂ (_⊢_≡_ _)
          (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id G)
          (PE.sym $ PE.cong _[ _ ]₀ $ wk-lift-id G₁) $
        G≡G₁ $ _⊢_≡_∷_.refl $
        PE.subst (_⊢_∷_ _ _) (wk-id _) $
        escapeTerm [F]′ [t₁]
      [Gt₁] = [G] (id ⊢Δ) [t₁]
      [Gt₁]₁ = [G]₁ (id ⊢Δ) [t₁]′
      [Gt₁≡G₁t₁] = ⊩≡→⊩≡/ [Gt₁] (reducible-⊩≡ G[t₁]≡G₁[t₁] .proj₂)
      t⇒t″ = conv* t⇒t′ Σ≡Σ₁
      SV₂ = goodCases [Gt₁] [Gt₁]₁ [Gt₁≡G₁t₁]
      t₂®v₂′ = convTermʳ′ [Gt₁] [Gt₁]₁ G[t₁]≡G₁[t₁] SV₂ t₂®v₂
      SV₁ = goodCases [F]′ [F]₁′ [F≡F₁]
      extra′ =
        Σ-®-elim (λ _ → Σ-® _ _ [F]₁′ t₁ v v₂ p) extra
                 Σ-®-intro-𝟘
                 λ v₁ v⇒p t₁®v₁ →
                   let t₁®v₁′ = convTermʳ′ [F]′ [F]₁′ F≡F₁′ SV₁ t₁®v₁
                   in  Σ-®-intro-ω v₁ v⇒p t₁®v₁′
  in  t₁ , t₂ , t⇒t″ , [t₁]′ , v₂ , t₂®v₂′ , extra′
convTermʳ′ {A} {B} _ _ A≡B (Idᵥ ⊩A ⊩B) (rflᵣ t⇒*rfl ⇒*↯) =
  rflᵣ
    (conv* t⇒*rfl
       (Id (_⊩ₗId_.Ty ⊩A) (_⊩ₗId_.lhs ⊩A) (_⊩ₗId_.rhs ⊩A)  ≡˘⟨ subset* (_⊩ₗId_.⇒*Id ⊩A) ⟩⊢
        A                                                  ≡⟨ A≡B ⟩⊢
        B                                                  ≡⟨ subset* (_⊩ₗId_.⇒*Id ⊩B) ⟩⊢∎
        Id (_⊩ₗId_.Ty ⊩B) (_⊩ₗId_.lhs ⊩B) (_⊩ₗId_.rhs ⊩B)  ∎))
    ⇒*↯
convTermʳ′ _ _ A≡B (embᵥ₁ ≤ᵘ-refl A≡B′) =
  convTermʳ′ _ _ A≡B A≡B′
convTermʳ′ _ _ A≡B (embᵥ₁ (≤ᵘ-step p) A≡B′) =
  convTermʳ′ _ _ A≡B (embᵥ₁ p A≡B′)
convTermʳ′ _ _ A≡B (embᵥ₂ ≤ᵘ-refl A≡B′) =
  convTermʳ′ _ _ A≡B A≡B′
convTermʳ′ _ _ A≡B (embᵥ₂ (≤ᵘ-step p) A≡B′) =
  convTermʳ′ _ _ A≡B (embᵥ₂ p A≡B′)
-- Impossible cases
convTermʳ′ _ _ _ (Emptyᵥ _ _) ()
convTermʳ′ _ _ _ (ne record{} _) ()

-- Conversion of logical relation for erasure
-- If t ® v ∷ A and Δ ⊢ A ≡ B then t ® v ∷ B

convTermʳ : ∀ {l l′ A B t v}
          → ([A] : Δ ⊩⟨ l ⟩ A)
            ([B] : Δ ⊩⟨ l′ ⟩ B)
          → Δ ⊢ A ≡ B
          → t ®⟨ l ⟩ v ∷ A / [A]
          → t ®⟨ l′ ⟩ v ∷ B / [B]
convTermʳ [A] [B] A≡B t®v =
  let [A≡B] = ⊩≡→⊩≡/ [A] (reducible-⊩≡ A≡B .proj₂)
  in convTermʳ′ [A] [B] A≡B (goodCases [A] [B] [A≡B]) t®v
