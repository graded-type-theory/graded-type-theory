{-# OPTIONS --without-K #-}

module Definition.Typed.Consequences.Inversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Nat
open import Tools.Product


inversion-ℕ : ∀ {Γ C} → Γ ⊢ ℕₑ ∷ C → Γ ⊢ C ≡ Uₑ
inversion-ℕ (ℕ x) = refl (U x)
inversion-ℕ (conv x x₁) = trans (sym x₁) (inversion-ℕ x)

inversion-Π : ∀ {F G Γ C}
            → Γ ⊢ Πₑ F ▹ G ∷ C → Γ ⊢ F ∷ Uₑ × Γ ∙ F ⊢ G ∷ Uₑ × Γ ⊢ C ≡ Uₑ
inversion-Π (Π x ▹ x₁) = x , x₁ , refl (U (wfTerm x))
inversion-Π (conv x x₁) = let a , b , c = inversion-Π x
                          in  a , b , trans (sym x₁) c

inversion-zero : ∀ {Γ C} → Γ ⊢ zeroₑ ∷ C → Γ ⊢ C ≡ ℕₑ
inversion-zero (zero x) = refl (ℕ x)
inversion-zero (conv x x₁) = trans (sym x₁) (inversion-zero x)

inversion-suc : ∀ {Γ t C} → Γ ⊢ sucₑ t ∷ C → Γ ⊢ t ∷ ℕₑ × Γ ⊢ C ≡ ℕₑ
inversion-suc (suc x) = x , refl (ℕ (wfTerm x))
inversion-suc (conv x x₁) =
  let a , b = inversion-suc x
  in  a , trans (sym x₁) b

inversion-natrec : ∀ {Γ c g n A C} → Γ ⊢ natrecₑ C c g n ∷ A
  → (Γ ∙ ℕₑ ⊢ C)
  × Γ ⊢ c ∷ C [ zeroₑ ]
  × Γ ⊢ g ∷ Πₑ ℕₑ ▹ (C ▹▹ C [ sucₑ (var zero) ]↑)
  × Γ ⊢ n ∷ ℕₑ
  × Γ ⊢ A ≡ C [ n ]
inversion-natrec (natrec x d d₁ n) = x , d , d₁ , n , refl (substType x n)
inversion-natrec (conv d x) = let a , b , c , d , e = inversion-natrec d
                              in  a , b , c , d , trans (sym x) e

inversion-app :  ∀ {Γ f a A} → Γ ⊢ (f ∘ₑ a) ∷ A →
  ∃₂ λ F G → Γ ⊢ f ∷ Πₑ F ▹ G × Γ ⊢ a ∷ F × Γ ⊢ A ≡ G [ a ]
inversion-app (d ∘ d₁) = _ , _ , d , d₁ , refl (substTypeΠ (syntacticTerm d) d₁)
inversion-app (conv d x) = let a , b , c , d , e = inversion-app d
                           in  a , b , c , d , trans (sym x) e

inversion-lam : ∀ {t A Γ} → Γ ⊢ lamₑ t ∷ A →
  ∃₂ λ F G → Γ ⊢ F × (Γ ∙ F ⊢ t ∷ G × Γ ⊢ A ≡ Πₑ F ▹ G)
inversion-lam (lam x x₁) = _ , _ , x , x₁ , refl (Π x ▹ (syntacticTerm x₁))
inversion-lam (conv x x₁) = let a , b , c , d , e = inversion-lam x
                            in  a , b , c , d , trans (sym x₁) e
