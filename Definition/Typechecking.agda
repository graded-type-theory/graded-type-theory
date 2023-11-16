------------------------------------------------------------------------
-- Bi-directional typechecking
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typechecking
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
  hiding (_∷_) renaming (_[_,_] to _[_,_]₁₀)
open import Definition.Typed R

import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Fin
open import Tools.Nat

private
  variable
    n : Nat
    Γ : Con Term n
    t u v w A B F G : Term n
    p q r p′ q′ : M
    b : BinderMode
    s : Strength

-- Bi-directional typechecking relations

mutual

  data _⊢_⇇Type (Γ : Con Term n) : (A : Term n) → Set a where
    Uᶜ : Γ ⊢ U ⇇Type
    ℕᶜ : Γ ⊢ ℕ ⇇Type
    Unitᶜ : Unit-allowed s
          → Γ ⊢ Unit s ⇇Type
    Emptyᶜ : Γ ⊢ Empty ⇇Type
    ΠΣᶜ : Γ ⊢ F ⇇Type
       → Γ ∙ F ⊢ G ⇇Type
       → ΠΣ-allowed b p q
       → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ⇇Type
    Idᶜ : Γ ⊢ A ⇇Type
        → Γ ⊢ t ⇇ A
        → Γ ⊢ u ⇇ A
        → Γ ⊢ Id A t u ⇇Type
    univᶜ : Γ ⊢ A ⇇ U
          → Γ ⊢ A ⇇Type

  data _⊢_⇉_ (Γ : Con Term n) : (t A : Term n) → Set a where
    ΠΣᵢ : Γ ⊢ F ⇇ U
       → Γ ∙ F ⊢ G ⇇ U
       → ΠΣ-allowed b p q
       → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ⇉ U
    varᵢ : ∀ {x}
         → x ∷ A ∈ Γ
         → Γ ⊢ var x ⇉ A
    appᵢ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ↘ Π p , q ▷ F ▹ G
         → Γ ⊢ u ⇇ F
         → Γ ⊢ t ∘⟨ p ⟩ u ⇉ G [ u ]₀
    fstᵢ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ↘ Σˢ p , q ▷ F ▹ G
         → Γ ⊢ fst p t ⇉ F
    sndᵢ : Γ ⊢ t ⇉ A
         → Γ ⊢ A ↘ Σˢ p , q ▷ F ▹ G
         → Γ ⊢ snd p t ⇉ G [ fst p t ]₀
    prodrecᵢ : Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊢ A ⇇Type
             → Γ ⊢ t ⇉ B
             → Γ ⊢ B ↘ Σʷ p , q ▷ F ▹ G
             → Γ ∙ F ∙ G ⊢ u ⇇ (A [ prodʷ p (var x1) (var x0) ]↑²)
             → Γ ⊢ prodrec r p q′ A t u ⇉ A [ t ]₀
    ℕᵢ : Γ ⊢ ℕ ⇉ U
    zeroᵢ : Γ ⊢ zero ⇉ ℕ
    sucᵢ : Γ ⊢ t ⇇ ℕ
         → Γ ⊢ suc t ⇉ ℕ
    natrecᵢ : ∀ {z s n}
            → Γ ∙ ℕ ⊢ A ⇇Type
            → Γ ⊢ z ⇇ A [ zero ]₀
            → Γ ∙ ℕ ∙ A ⊢ s ⇇ A [ suc (var x1) ]↑²
            → Γ ⊢ n ⇇ ℕ
            → Γ ⊢ natrec p q r A z s n ⇉ A [ n ]₀
    Unitᵢ : Unit-allowed s
          → Γ ⊢ Unit s ⇉ U
    starᵢ : Unit-allowed s
          → Γ ⊢ star s ⇉ Unit s
    unitrecᵢ : Γ ∙ Unitʷ ⊢ A ⇇Type
             → Γ ⊢ t ⇇ Unitʷ
             → Γ ⊢ u ⇇ A [ starʷ ]₀
             → Γ ⊢ unitrec p q A t u ⇉ A [ t ]₀
    Emptyᵢ : Γ ⊢ Empty ⇉ U
    emptyrecᵢ : Γ ⊢ A ⇇Type
              → Γ ⊢ t ⇇ Empty
              → Γ ⊢ emptyrec p A t ⇉ A
    Idᵢ : Γ ⊢ A ⇇ U
        → Γ ⊢ t ⇇ A
        → Γ ⊢ u ⇇ A
        → Γ ⊢ Id A t u ⇉ U
    Jᵢ : Γ ⊢ A ⇇Type
       → Γ ⊢ t ⇇ A
       → Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B ⇇Type
       → Γ ⊢ u ⇇ B [ t , rfl ]₁₀
       → Γ ⊢ v ⇇ A
       → Γ ⊢ w ⇇ Id A t v
       → Γ ⊢ J p q A t B u v w ⇉ B [ v , w ]₁₀
    Kᵢ : Γ ⊢ A ⇇Type
       → Γ ⊢ t ⇇ A
       → Γ ∙ Id A t t ⊢ B ⇇Type
       → Γ ⊢ u ⇇ B [ rfl ]₀
       → Γ ⊢ v ⇇ Id A t t
       → K-allowed
       → Γ ⊢ K p A t B u v ⇉ B [ v ]₀
    []-congᵢ : Γ ⊢ A ⇇Type
             → Γ ⊢ t ⇇ A
             → Γ ⊢ u ⇇ A
             → Γ ⊢ v ⇇ Id A t u
             → []-cong-allowed s
             → let open Erased s in
               Γ ⊢ []-cong s A t u v ⇉
                 Id (Erased A) ([ t ]) ([ u ])

  data _⊢_⇇_ (Γ : Con Term n) : (t A : Term n) → Set a where
    lamᶜ : Γ ⊢ A ↘ Π p , q ▷ F ▹ G
         → Γ ∙ F ⊢ t ⇇ G
         → Γ ⊢ lam p t ⇇ A
    prodᶜ : ∀ {m}
          → Γ ⊢ A ↘ Σ⟨ m ⟩ p , q ▷ F ▹ G
          → Γ ⊢ t ⇇ F
          → Γ ⊢ u ⇇ G [ t ]₀
          → Γ ⊢ prod m p t u ⇇ A
    rflᶜ : Γ ⊢ A ↘ Id B t u
         → Γ ⊢ t ≡ u ∷ B
         → Γ ⊢ rfl ⇇ A
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
    Unitᵢ : Inferable (Unit s)
    starᵢ : Inferable (star s)
    unitrecᵢ : Checkable A → Checkable t → Checkable u → Inferable (unitrec p q A t u)
    Emptyᵢ : Inferable Empty
    emptyrecᵢ : Checkable A → Checkable t → Inferable (emptyrec p A t)
    Idᵢ : Checkable A → Checkable t → Checkable u → Inferable (Id A t u)
    Jᵢ : Checkable A → Checkable t → Checkable B → Checkable u →
         Checkable v → Checkable w → Inferable (J p q A t B u v w)
    Kᵢ : Checkable A → Checkable t → Checkable B → Checkable u →
         Checkable v → Inferable (K p A t B u v)
    []-congᵢ : Checkable A → Checkable t → Checkable u → Checkable v →
               Inferable ([]-cong s A t u v)

  data Checkable : (Term n) → Set a where
    lamᶜ : Checkable t → Checkable (lam p t)
    prodᶜ : ∀ {m} → Checkable t → Checkable u → Checkable (prod m p t u)
    rflᶜ : Checkable {n = n} rfl
    infᶜ : Inferable t → Checkable t

-- CheckableCon Γ means that the types in Γ are checkable.

data CheckableCon : (Γ : Con Term n) → Set a where
  ε   : CheckableCon ε
  _∙_ : CheckableCon Γ → Checkable A → CheckableCon (Γ ∙ A)

-- The bi-directional type checking relations imply the syntactic notion of Inferable and Checkable

mutual

  Checkable⇇Type : Γ ⊢ A ⇇Type → Checkable A
  Checkable⇇Type Uᶜ = infᶜ Uᵢ
  Checkable⇇Type ℕᶜ = infᶜ ℕᵢ
  Checkable⇇Type (Unitᶜ _) = infᶜ Unitᵢ
  Checkable⇇Type Emptyᶜ = infᶜ Emptyᵢ
  Checkable⇇Type (ΠΣᶜ F⇇Type G⇇Type _) =
    infᶜ (ΠΣᵢ (Checkable⇇Type F⇇Type) (Checkable⇇Type G⇇Type))
  Checkable⇇Type (Idᶜ A t u) =
    infᶜ (Idᵢ (Checkable⇇Type A) (Checkable⇇ t) (Checkable⇇ u))
  Checkable⇇Type (univᶜ x) = Checkable⇇ x

  Checkable⇇ : Γ ⊢ t ⇇ A → Checkable t
  Checkable⇇ (lamᶜ x t⇇A) = lamᶜ (Checkable⇇ t⇇A)
  Checkable⇇ (prodᶜ x t⇇A t⇇A₁) = prodᶜ (Checkable⇇ t⇇A) (Checkable⇇ t⇇A₁)
  Checkable⇇ (rflᶜ _ _) = rflᶜ
  Checkable⇇ (infᶜ x x₁) = infᶜ (Inferable⇉ x)

  Inferable⇉ : Γ ⊢ t ⇉ A → Inferable t
  Inferable⇉ (ΠΣᵢ x x₁ _) = ΠΣᵢ (Checkable⇇ x) (Checkable⇇ x₁)
  Inferable⇉ (varᵢ x) = varᵢ
  Inferable⇉ (appᵢ t⇉A x x₁) = ∘ᵢ (Inferable⇉ t⇉A) (Checkable⇇ x₁)
  Inferable⇉ (fstᵢ t⇉A x) = fstᵢ (Inferable⇉ t⇉A)
  Inferable⇉ (sndᵢ t⇉A x) = sndᵢ (Inferable⇉ t⇉A)
  Inferable⇉ (prodrecᵢ x t⇉A x₁ x₂) =
    prodrecᵢ (Checkable⇇Type x) (Inferable⇉ t⇉A) (Checkable⇇ x₂)
  Inferable⇉ ℕᵢ = ℕᵢ
  Inferable⇉ zeroᵢ = zeroᵢ
  Inferable⇉ (sucᵢ x) = sucᵢ (Checkable⇇ x)
  Inferable⇉ (natrecᵢ x x₁ x₂ x₃) = natrecᵢ (Checkable⇇Type x) (Checkable⇇ x₁) (Checkable⇇ x₂) (Checkable⇇ x₃)
  Inferable⇉ (Unitᵢ _) = Unitᵢ
  Inferable⇉ (starᵢ _) = starᵢ
  Inferable⇉ (unitrecᵢ x x₁ x₂) = unitrecᵢ (Checkable⇇Type x) (Checkable⇇ x₁) (Checkable⇇ x₂)
  Inferable⇉ Emptyᵢ = Emptyᵢ
  Inferable⇉ (emptyrecᵢ x x₁) = emptyrecᵢ (Checkable⇇Type x) (Checkable⇇ x₁)
  Inferable⇉ (Idᵢ A t u) =
    Idᵢ (Checkable⇇ A) (Checkable⇇ t) (Checkable⇇ u)
  Inferable⇉ (Jᵢ A t B u v w) =
    Jᵢ (Checkable⇇Type A) (Checkable⇇ t) (Checkable⇇Type B)
      (Checkable⇇ u) (Checkable⇇ v) (Checkable⇇ w)
  Inferable⇉ (Kᵢ A t B u v _) =
    Kᵢ (Checkable⇇Type A) (Checkable⇇ t) (Checkable⇇Type B)
      (Checkable⇇ u) (Checkable⇇ v)
  Inferable⇉ ([]-congᵢ A t u v _) =
    []-congᵢ (Checkable⇇Type A) (Checkable⇇ t) (Checkable⇇ u)
      (Checkable⇇ v)
