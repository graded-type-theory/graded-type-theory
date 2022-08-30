{-# OPTIONS --safe --without-K #-}

open import Tools.Relation

module Definition.Typechecking {a ℓ} (M′ : Setoid a ℓ) where

open Setoid M′ renaming (Carrier to M)

open import Definition.Untyped M
open import Definition.Typed M′

open import Tools.Fin
open import Tools.Level
open import Tools.Nat

private
  variable
    n : Nat
    Γ : Con Term n
    t u A B F G : Term n
    p q r p′ : M


mutual

  data _⊢_⇇Type (Γ : Con Term n) : (A : Term n) → Set (a ⊔ ℓ) where
    Uᵢ : Γ ⊢ U ⇇Type
    ℕᵢ : Γ ⊢ ℕ ⇇Type
    Unitᵢ : Γ ⊢ Unit ⇇Type
    Emptyᵢ : Γ ⊢ Empty ⇇Type
    Πᵢ : Γ ⊢ F ⇇Type
       → Γ ∙ F ⊢ G ⇇Type
       → Γ ⊢ Π p , q ▷ F ▹ G ⇇Type
    Σᵢ : ∀ {m}
       → Γ ⊢ F ⇇Type
       → Γ ∙ F ⊢ G ⇇Type
       → Γ ⊢ Σ⟨ m ⟩ q ▷ F ▹ G ⇇Type
    univᵢ : Γ ⊢ A ⇇ U
          → Γ ⊢ A ⇇Type

  data _⊢_⇉_ (Γ : Con Term n) : (t A : Term n) → Set (a ⊔ ℓ) where
    Πᵢ : Γ ⊢ F ⇇ U
       → Γ ∙ F ⊢ G ⇇ U
       → Γ ⊢ Π p , q ▷ F ▹ G ⇉ U
    Σᵢ : ∀ {m}
       → Γ ⊢ F ⇇ U
       → Γ ∙ F ⊢ G ⇇ U
       → Γ ⊢ Σ⟨ m ⟩ q ▷ F ▹ G ⇉ U
    varᵢ : ∀ {x}
         → x ∷ A ∈ Γ
         → Γ ⊢ var x ⇉ A
    appᵢ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ↘ Π p , q ▷ F ▹ G
         → Γ ⊢ u ⇇ F
         → p ≈ p′
         → Γ ⊢ t ∘ p′ ▷ u ⇉ G [ u ]
    fstᵢ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ↘ Σₚ q ▷ F ▹ G
         → Γ ⊢ fst t ⇉ F
    sndᵢ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ↘ Σₚ q ▷ F ▹ G
         → Γ ⊢ snd t ⇉ G [ fst t ]
    prodrecᵢ : Γ ∙ (Σᵣ q ▷ F ▹ G) ⊢ A ⇇Type
             → Γ ⊢ t ⇉ B
             → Γ ⊢ B ↘ Σᵣ q ▷ F ▹ G
             → Γ ∙ F ∙ G ⊢ u ⇇ (A [ prod (var (x0 +1)) (var x0) ]↑²)
             → Γ ⊢ prodrec p A t u ⇉ A [ t ]
    ℕᵢ : Γ ⊢ ℕ ⇉ U
    zeroᵢ : Γ ⊢ zero ⇉ ℕ
    sucᵢ : Γ ⊢ t ⇇ ℕ
         → Γ ⊢ suc t ⇉ ℕ
    natrecᵢ : ∀ {z s n}
            → Γ ∙ ℕ ⊢ A ⇇Type
            → Γ ⊢ z ⇇ A [ zero ]
            → Γ ∙ ℕ ∙ A ⊢ s ⇇ wk1 (A [ suc (var x0) ]↑)
            → Γ ⊢ n ⇇ ℕ
            → Γ ⊢ natrec p r A z s n ⇉ A [ n ]
    Unitᵢ : Γ ⊢ Unit ⇉ U
    starᵢ : Γ ⊢ star ⇉ Unit
    Emptyᵢ : Γ ⊢ Empty ⇉ U
    Emptyrecᵢ : Γ ⊢ A ⇇Type
              → Γ ⊢ t ⇇ Empty
              → Γ ⊢ Emptyrec p A t ⇉ A

  data _⊢_⇇_ (Γ : Con Term n) : (t A : Term n) → Set (a ⊔ ℓ) where
    lamᶜ : Γ ⊢ A ↘ Π p , q ▷ F ▹ G
         → Γ ∙ F ⊢ t ⇇ G
         → p ≈ p′
         → Γ ⊢ lam p′ t ⇇ A
    prodᶜ : ∀ {m}
          → Γ ⊢ A ↘ Σ⟨ m ⟩ q ▷ F ▹ G
          → Γ ⊢ t ⇇ F
          → Γ ⊢ u ⇇ G [ t ]
          → Γ ⊢ prod t u ⇇ A
    infᶜ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ≡ B
         → Γ ⊢ t ⇇ B
