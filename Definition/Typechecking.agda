module Definition.Typechecking {a} (M : Set a) where

open import Definition.Untyped M
open import Definition.Typed M

open import Tools.Fin
open import Tools.Nat

private
  variable
    n : Nat
    Γ : Con Term n
    t u A B F G : Term n
    p q r p′ q′ : M
    b : BinderMode

-- Bi-directional typechecking relations

mutual

  data _⊢_⇇Type (Γ : Con Term n) : (A : Term n) → Set a where
    Uᶜ : Γ ⊢ U ⇇Type
    ℕᶜ : Γ ⊢ ℕ ⇇Type
    Unitᶜ : Γ ⊢ Unit ⇇Type
    Emptyᶜ : Γ ⊢ Empty ⇇Type
    ΠΣᶜ : Γ ⊢ F ⇇Type
       → Γ ∙ F ⊢ G ⇇Type
       → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ⇇Type
    univᶜ : Γ ⊢ A ⇇ U
          → Γ ⊢ A ⇇Type

  data _⊢_⇉_ (Γ : Con Term n) : (t A : Term n) → Set a where
    ΠΣᵢ : Γ ⊢ F ⇇ U
       → Γ ∙ F ⊢ G ⇇ U
       → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ⇉ U
    varᵢ : ∀ {x}
         → x ∷ A ∈ Γ
         → Γ ⊢ var x ⇉ A
    appᵢ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ↘ Π p , q ▷ F ▹ G
         → Γ ⊢ u ⇇ F
         → Γ ⊢ t ∘⟨ p ⟩ u ⇉ G [ u ]
    fstᵢ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ↘ Σₚ p , q ▷ F ▹ G
         → Γ ⊢ fst p t ⇉ F
    sndᵢ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ↘ Σₚ p , q ▷ F ▹ G
         → Γ ⊢ snd p t ⇉ G [ fst p t ]
    prodrecᵢ : Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ A ⇇Type
             → Γ ⊢ t ⇉ B
             → Γ ⊢ B ↘ Σᵣ p , q ▷ F ▹ G
             → Γ ∙ F ∙ G ⊢ u ⇇ (A [ prodᵣ p (var (x0 +1)) (var x0) ]↑²)
             → Γ ⊢ prodrec r p q′ A t u ⇉ A [ t ]
    ℕᵢ : Γ ⊢ ℕ ⇉ U
    zeroᵢ : Γ ⊢ zero ⇉ ℕ
    sucᵢ : Γ ⊢ t ⇇ ℕ
         → Γ ⊢ suc t ⇉ ℕ
    natrecᵢ : ∀ {z s n}
            → Γ ∙ ℕ ⊢ A ⇇Type
            → Γ ⊢ z ⇇ A [ zero ]
            → Γ ∙ ℕ ∙ A ⊢ s ⇇ wk1 (A [ suc (var x0) ]↑)
            → Γ ⊢ n ⇇ ℕ
            → Γ ⊢ natrec p q r A z s n ⇉ A [ n ]
    Unitᵢ : Γ ⊢ Unit ⇉ U
    starᵢ : Γ ⊢ star ⇉ Unit
    Emptyᵢ : Γ ⊢ Empty ⇉ U
    Emptyrecᵢ : Γ ⊢ A ⇇Type
              → Γ ⊢ t ⇇ Empty
              → Γ ⊢ Emptyrec p A t ⇉ A

  data _⊢_⇇_ (Γ : Con Term n) : (t A : Term n) → Set a where
    lamᶜ : Γ ⊢ A ↘ Π p , q ▷ F ▹ G
         → Γ ∙ F ⊢ t ⇇ G
         → Γ ⊢ lam p t ⇇ A
    prodᶜ : ∀ {m}
          → Γ ⊢ A ↘ Σ⟨ m ⟩ p , q ▷ F ▹ G
          → Γ ⊢ t ⇇ F
          → Γ ⊢ u ⇇ G [ t ]
          → Γ ⊢ prod m p t u ⇇ A
    infᶜ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ≡ B
         → Γ ⊢ t ⇇ B

-- Inferable and checkable terms
-- Checkable terms are essentially normal form terms

mutual

  data Inferable {n : Nat} : (Term n) → Set a where
    Uᵢ : Inferable U
    ΠΣᵢ : Checkable F → Checkable G → Inferable (ΠΣ⟨ b ⟩ p , q ▷ F ▹ G)
    varᵢ : ∀ {x} → Inferable (var x)
    ∘ᵢ : Inferable t → Checkable u → Inferable (t ∘⟨ p ⟩ u)
    fstᵢ : Inferable t → Inferable (fst p t)
    sndᵢ : Inferable t → Inferable (snd p t)
    prodrecᵢ : Checkable A → Inferable t → Checkable u → Inferable (prodrec p q r A t u)
    ℕᵢ : Inferable ℕ
    zeroᵢ : Inferable zero
    sucᵢ : Checkable t → Inferable (suc t)
    natrecᵢ : ∀ {z s n} → Checkable A → Checkable z → Checkable s → Checkable n → Inferable (natrec p q r A z s n)
    Unitᵢ : Inferable Unit
    starᵢ : Inferable star
    Emptyᵢ : Inferable Empty
    Emptyrecᵢ : Checkable A → Checkable t → Inferable (Emptyrec p A t)


  data Checkable : (Term n) → Set a where
    lamᶜ : Checkable t → Checkable (lam p t)
    prodᶜ : ∀ {m} → Checkable t → Checkable u → Checkable (prod m p t u)
    infᶜ : Inferable t → Checkable t

-- The bi-directional type checking relations imply the syntactic notion of Inferable and Checkable

mutual

  Checkable⇇Type : Γ ⊢ A ⇇Type → Checkable A
  Checkable⇇Type Uᶜ = infᶜ Uᵢ
  Checkable⇇Type ℕᶜ = infᶜ ℕᵢ
  Checkable⇇Type Unitᶜ = infᶜ Unitᵢ
  Checkable⇇Type Emptyᶜ = infᶜ Emptyᵢ
  Checkable⇇Type (ΠΣᶜ F⇇Type G⇇Type) =
    infᶜ (ΠΣᵢ (Checkable⇇Type F⇇Type) (Checkable⇇Type G⇇Type))
  Checkable⇇Type (univᶜ x) = Checkable⇇ x

  Checkable⇇ : Γ ⊢ t ⇇ A → Checkable t
  Checkable⇇ (lamᶜ x t⇇A) = lamᶜ (Checkable⇇ t⇇A)
  Checkable⇇ (prodᶜ x t⇇A t⇇A₁) = prodᶜ (Checkable⇇ t⇇A) (Checkable⇇ t⇇A₁)
  Checkable⇇ (infᶜ x x₁) = infᶜ (Inferable⇉ x)

  Inferable⇉ : Γ ⊢ t ⇉ A → Inferable t
  Inferable⇉ (ΠΣᵢ x x₁) = ΠΣᵢ (Checkable⇇ x) (Checkable⇇ x₁)
  Inferable⇉ (varᵢ x) = varᵢ
  Inferable⇉ (appᵢ t⇉A x x₁) = ∘ᵢ (Inferable⇉ t⇉A) (Checkable⇇ x₁)
  Inferable⇉ (fstᵢ t⇉A x) = fstᵢ (Inferable⇉ t⇉A)
  Inferable⇉ (sndᵢ t⇉A x) = sndᵢ (Inferable⇉ t⇉A)
  Inferable⇉ (prodrecᵢ x t⇉A x₁ x₂) = prodrecᵢ (Checkable⇇Type x) (Inferable⇉ t⇉A) (Checkable⇇ x₂)
  Inferable⇉ ℕᵢ = ℕᵢ
  Inferable⇉ zeroᵢ = zeroᵢ
  Inferable⇉ (sucᵢ x) = sucᵢ (Checkable⇇ x)
  Inferable⇉ (natrecᵢ x x₁ x₂ x₃) = natrecᵢ (Checkable⇇Type x) (Checkable⇇ x₁) (Checkable⇇ x₂) (Checkable⇇ x₃)
  Inferable⇉ Unitᵢ = Unitᵢ
  Inferable⇉ starᵢ = starᵢ
  Inferable⇉ Emptyᵢ = Emptyᵢ
  Inferable⇉ (Emptyrecᵢ x x₁) = Emptyrecᵢ (Checkable⇇Type x) (Checkable⇇ x₁)
