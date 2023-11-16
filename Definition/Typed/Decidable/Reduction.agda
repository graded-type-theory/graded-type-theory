------------------------------------------------------------------------
-- Decidability of reducing to Π and Σ-types.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
import Tools.PropositionalEquality as PE
open import Tools.Relation

module Definition.Typed.Decidable.Reduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  (_≟_ : Decidable (PE._≡_ {A = M}))
  where

open import Definition.Untyped M
  hiding (_∷_; U≢B; ℕ≢B; B≢ne; Id≢⟦⟧▷; Id≢ne)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Inequality R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental.Reducibility R
open import Definition.LogicalRelation.Properties R

open import Tools.Function
open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n
    A : Term n
    l : TypeLevel

-- Decidability of being (reducing to) a binding type

isB′ : ∀ {l} → Γ ⊩⟨ l ⟩ A → Dec (∃₃ λ F G W → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (⟦ W ⟧ F ▹ G))
isB′ (Uᵣ′ l′ l< ⊢Γ) = no (λ {(F , G , W , ⊢F , ⊢G , U⇒W) → U≢B W (subset* U⇒W)})
isB′ (ℕᵣ x) = no (λ {(F , G , W , ⊢F , ⊢G , A⇒W) → ℕ≢B W (trans (sym (subset* (red x))) (subset* A⇒W))})
isB′ (Emptyᵣ x) = no (λ {(F , G , W , ⊢F , ⊢G , A⇒W) → Empty≢Bⱼ W (trans (sym (subset* (red x))) (subset* A⇒W))})
isB′ (Unitᵣ (Unitₜ x _)) =
  no (λ { (_ , _ , W , _ , _ , A⇒W) →
          Unit≢Bⱼ W (trans (sym (subset* (red x))) (subset* A⇒W)) })
isB′ (ne′ H D neH H≡H) = no (λ {(F , G , W , ⊢F , ⊢G , A⇒W) → B≢ne W neH (trans (sym (subset* A⇒W)) (subset* (red D)))})
isB′ (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
  yes (F , G , W , ⊢F , ⊢G , red D)
isB′ (Idᵣ ⊩A) =
  no λ (_ , _ , _ , _ , _ , A⇒*Id) →
    Id≢⟦⟧▷
      (trans (sym (subset* (red (_⊩ₗId_.⇒*Id ⊩A)))) (subset* A⇒*Id ))
isB′ (emb 0<1 [A]) = isB′ [A]

isB : Γ ⊢ A → Dec (∃₃ λ F G W → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (⟦ W ⟧ F ▹ G))
isB ⊢A = isB′ (reducible ⊢A)

-- Decidability of being (reducing to) a Π-type

isΠ : Γ ⊢ A → Dec (∃₄ λ F G p q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Π p , q ▷ F ▹ G))
isΠ ⊢A with isB ⊢A
... | yes (F , G , BΠ p q , ⊢F , ⊢G , A⇒Π) = yes (F , G , p , q , ⊢F , ⊢G , A⇒Π)
... | yes (F , G , BΣ p q x , ⊢F , ⊢G , A⇒Σ) = no (λ {(F′ , G′ , p′ , q′ , ⊢F , ⊢G , A⇒Π) → Π≢Σⱼ (trans (sym (subset* A⇒Π)) (subset* A⇒Σ))})
... | no ¬isB = no (λ {(F′ , G′ , p′ , q′ , ⊢F , ⊢G , A⇒Π) → ¬isB (F′ , G′ , BΠ p′ q′ , ⊢F , ⊢G , A⇒Π)})

-- Decidability of being (reducing to) a Σ-type

isΣ : Γ ⊢ A → Dec (∃₄ λ F G m p → ∃ λ q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Σ⟨ m ⟩ p , q ▷ F ▹ G))
isΣ ⊢A with isB ⊢A
... | yes (F , G , BΣ m p q , ⊢F , ⊢G , A⇒Σ) = yes (F , G , m , p , q , ⊢F , ⊢G , A⇒Σ)
... | yes (F , G , BΠ p q , ⊢F , ⊢G , A⇒Π) = no (λ {(F′ , G′ , m′ , p′ , q′ , ⊢F , ⊢G , A⇒Σ) → Π≢Σⱼ (trans (sym (subset* A⇒Π)) (subset* A⇒Σ))})
... | no ¬isB = no (λ {(F′ , G′ , m , p′ , q′ , ⊢F , ⊢G , A⇒Π) → ¬isB (F′ , G′ , BΣ m p′ q′ , ⊢F , ⊢G , A⇒Π)})

isΣˢ : Γ ⊢ A → Dec (∃₄ λ F G p q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Σˢ p , q ▷ F ▹ G))
isΣˢ ⊢A with isΣ ⊢A
... | yes (F , G , 𝕤 , p , q , ⊢F , ⊢G , A⇒Σ) = yes (F , G , p , q , ⊢F , ⊢G , A⇒Σ)
... | yes (F , G , 𝕨 , p , q , ⊢F , ⊢G , A⇒Σ) = no (λ {(F′ , G′ , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → Σˢ≢Σʷⱼ (trans (sym (subset* A⇒Σ′)) (subset* A⇒Σ))})
... | no ¬isΣ = no (λ {(F′ , G′ , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → ¬isΣ (F′ , G′ , 𝕤 , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′)})

isΣʷ : Γ ⊢ A → Dec (∃₄ λ F G p q → (Γ ⊢ F) × (Γ ∙ F ⊢ G) × Γ ⊢ A ⇒* (Σʷ p , q ▷ F ▹ G))
isΣʷ ⊢A with isΣ ⊢A
... | yes (F , G , 𝕤 , p , q , ⊢F , ⊢G , A⇒Σ) = no (λ {(F′ , G′ , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → Σˢ≢Σʷⱼ (trans (sym (subset* A⇒Σ)) (subset* A⇒Σ′))})
... | yes (F , G , 𝕨 , p , q , ⊢F , ⊢G , A⇒Σ) = yes (F , G , p , q , ⊢F , ⊢G , A⇒Σ)
... | no ¬isΣ = no (λ {(F′ , G′ , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′) → ¬isΣ (F′ , G′ , 𝕨 , p′ , q′ , ⊢F′ , ⊢G′ , A⇒Σ′)})

opaque

  -- It is decidable whether a well-formed type reduces to an identity
  -- type.

  is-Id :
    Γ ⊢ A →
    Dec (∃₃ λ B t u →
         (Γ ⊢ B) × Γ ⊢ t ∷ B × Γ ⊢ u ∷ B × Γ ⊢ A ⇒* Id B t u)
  is-Id = helper ∘→ reducible
    where
    helper :
      Γ ⊩⟨ l ⟩ A →
      Dec (∃₃ λ B t u →
           (Γ ⊢ B) × Γ ⊢ t ∷ B × Γ ⊢ u ∷ B × Γ ⊢ A ⇒* Id B t u)
    helper (Uᵣ _) =
      no λ (_ , _ , _ , _ , _ , _ , U⇒*Id) →
        Id≢U (sym (subset* U⇒*Id))
    helper (ℕᵣ A⇒*ℕ) =
      no λ (_ , _ , _ , _ , _ , _ , A⇒*Id) →
        Id≢ℕ (trans (sym (subset* A⇒*Id)) (subset* (red A⇒*ℕ)))
    helper (Emptyᵣ A⇒*Empty) =
      no λ (_ , _ , _ , _ , _ , _ , A⇒*Id) →
        Id≢Empty (trans (sym (subset* A⇒*Id)) (subset* (red A⇒*Empty)))
    helper (Unitᵣ ⊩Unit) =
      no λ (_ , _ , _ , _ , _ , _ , A⇒*Id) →
        Id≢Unit $
        trans (sym (subset* A⇒*Id))
          (subset* (red (_⊩Unit⟨_⟩_.⇒*-Unit ⊩Unit)))
    helper (ne ⊩A) =
      no λ (_ , _ , _ , _ , _ , _ , A⇒*Id) →
        Id≢ne neK $ trans (sym (subset* A⇒*Id)) (subset* (red D))
      where
      open _⊩ne_ ⊩A
    helper (Bᵣ _ ⊩A) =
      no λ (_ , _ , _ , _ , _ , _ , A⇒*Id) →
        Id≢⟦⟧▷ $
        trans (sym (subset* A⇒*Id)) (subset* (red (_⊩ₗB⟨_⟩_.D ⊩A)))
    helper (Idᵣ ⊩A) = yes
        ( _ , _ , _
        , escape ⊩Ty , escapeTerm ⊩Ty ⊩lhs , escapeTerm ⊩Ty ⊩rhs
        , red ⇒*Id
        )
      where
      open _⊩ₗId_ ⊩A
    helper (emb 0<1 ⊩A) =
      helper ⊩A
