{-# OPTIONS --without-K #-}

module Definition.Typed.EqualityRelation where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_)

open import Tools.Nat
open import Tools.Product

record EqRelSet : Set₁ where
  constructor eqRel
  field
    _⊢_≅_   : Con Term → (A B : Term)   → Set
    _⊢_≅_∷_ : Con Term → (t u A : Term) → Set
    _⊢_~_∷_ : Con Term → (t u A : Term) → Set

    ~-var : ∀ {x A Γ} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A
    ~-app : ∀ {a b f g F G Γ}
          → Γ ⊢ f ~ g ∷ Πₑ F ▹ G
          → Γ ⊢ a ≅ b ∷ F
          → Γ ⊢ f ∘ₑ a ~ g ∘ₑ b ∷ G [ a ]
    ~-natrec : ∀ {z z' s s' n n' F F' Γ}
             → Γ ∙ ℕₑ ⊢ F ≅ F'
             → Γ     ⊢ z ≅ z' ∷ F [ zeroₑ ]
             → Γ     ⊢ s ≅ s' ∷ Πₑ ℕₑ ▹ (F ▹▹ F [ sucₑ (var zero) ]↑)
             → Γ     ⊢ n ~ n' ∷ ℕₑ
             → Γ     ⊢ natrecₑ F z s n ~ natrecₑ F' z' s' n' ∷ F [ n ]

    ~-sym   : ∀ {k l A Γ}
            → Γ ⊢ k ~ l ∷ A
            → Γ ⊢ l ~ k ∷ A
    ~-trans : ∀ {k l m A Γ}
            → Γ ⊢ k ~ l ∷ A
            → Γ ⊢ l ~ m ∷ A
            → Γ ⊢ k ~ m ∷ A
    ~-conv  : ∀ {k l A B Γ}
            → Γ ⊢ k ~ l ∷ A
            → Γ ⊢ A ≡ B
            → Γ ⊢ k ~ l ∷ B
    ~-wk    : ∀ {k l A ρ Γ Δ}
            → ρ ∷ Δ ⊆ Γ
            → ⊢ Δ
            → Γ ⊢ k ~ l ∷ A
            → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A

    ~-to-≅ₜ : ∀ {k l A Γ}
            → Γ ⊢ k ~ l ∷ A
            → Γ ⊢ k ≅ l ∷ A

    ≅-Urefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ Uₑ ≅ Uₑ
    ≅-ℕrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕₑ ≅ ℕₑ
    ≅ₜ-ℕrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕₑ ≅ ℕₑ ∷ Uₑ

    ≅ₜ-zerorefl : ∀ {Γ} → ⊢ Γ → Γ ⊢ zeroₑ ≅ zeroₑ ∷ ℕₑ

    ≅-sym  : ∀ {A B Γ}   → Γ ⊢ A ≅ B     → Γ ⊢ B ≅ A
    ≅ₜ-sym : ∀ {t u A Γ} → Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ t ∷ A

    ≅-trans  : ∀ {A B C Γ}   → Γ ⊢ A ≅ B     → Γ ⊢ B ≅ C     → Γ ⊢ A ≅ C
    ≅ₜ-trans : ∀ {t u v A Γ} → Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ v ∷ A → Γ ⊢ t ≅ v ∷ A

    ≅-red : ∀ {A A' B B' Γ}
          → Γ ⊢ A ⇒* A'
          → Γ ⊢ B ⇒* B'
          → Whnf A'
          → Whnf B'
          → Γ ⊢ A' ≅ B'
          → Γ ⊢ A  ≅ B

    ≅ₜ-red : ∀ {a a' b b' A B Γ}
           → Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a' ∷ B
           → Γ ⊢ b ⇒* b' ∷ B
           → Whnf B
           → Whnf a'
           → Whnf b'
           → Γ ⊢ a' ≅ b' ∷ B
           → Γ ⊢ a  ≅ b  ∷ A

    ≅-wk  : ∀ {A B ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ A ≅ B
          → Δ ⊢ wk ρ A ≅ wk ρ B
    ≅ₜ-wk : ∀ {t u A ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ t ≅ u ∷ A
          → Δ ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A

    ≅-eq  : ∀ {A B Γ}
          → Γ ⊢ A ≅ B
          → Γ ⊢ A ≡ B
    ≅ₜ-eq : ∀ {t u A Γ}
          → Γ ⊢ t ≅ u ∷ A
          → Γ ⊢ t ≡ u ∷ A

    ≅-conv : ∀ {t u A B Γ}
           → Γ ⊢ t ≅ u ∷ A
           → Γ ⊢ A ≡ B
           → Γ ⊢ t ≅ u ∷ B

    ≅-univ : ∀ {A B Γ}
           → Γ ⊢ A ≅ B ∷ Uₑ
           → Γ ⊢ A ≅ B

    ≅-suc-cong : ∀ {m n Γ}
               → Γ ⊢ m ≅ n ∷ ℕₑ
               → Γ ⊢ sucₑ m ≅ sucₑ n ∷ ℕₑ

    ≅-Π-cong  : ∀ {F G H E Γ}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H
              → Γ ∙ F ⊢ G ≅ E
              → Γ ⊢ Πₑ F ▹ G ≅ Πₑ H ▹ E

    ≅ₜ-Π-cong : ∀ {F G H E Γ}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H ∷ Uₑ
              → Γ ∙ F ⊢ G ≅ E ∷ Uₑ
              → Γ ⊢ Πₑ F ▹ G ≅ Πₑ H ▹ E ∷ Uₑ

    ≅-fun-ext : ∀ {f g F G Γ}
              → Γ ⊢ F
              → Γ ⊢ f ∷ Πₑ F ▹ G
              → Γ ⊢ g ∷ Πₑ F ▹ G
              → Whnf f
              → Whnf g
              → Γ ∙ F ⊢ wk1 f ∘ₑ var zero ≅ wk1 g ∘ₑ var zero ∷ G
              → Γ ⊢ f ≅ g ∷ Πₑ F ▹ G

  ~-to-≅ : ∀ {k l Γ} → Γ ⊢ k ~ l ∷ Uₑ → Γ ⊢ k ≅ l
  ~-to-≅ k~l = ≅-univ (~-to-≅ₜ k~l)
