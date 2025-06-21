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
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Typed R

open import Tools.Fin
open import Tools.Nat

private
  variable
    n : Nat
    Γ : Con Term n
    l l₁ l₂ t u v w A B C C₁ C₂ F G : Term n
    p q r p′ q′ : M
    b : BinderMode
    s : Strength

-- Bi-directional typechecking relations

mutual

  data _⊢_⇇Type (Γ : Con Term n) : (A : Term n) → Set a where
    Levelᶜ : Γ ⊢ Level ⇇Type
    Uᶜ : Γ ⊢ l ⇇ Level → Γ ⊢ U l ⇇Type
    Liftᶜ : Γ ⊢ l ⇇ Level
          → Γ ⊢ A ⇇Type
          → Γ ⊢ Lift l A ⇇Type
    ℕᶜ : Γ ⊢ ℕ ⇇Type
    Unitᶜ : Γ ⊢ l ⇇ Level
          → Unit-allowed s
          → Γ ⊢ Unit s l ⇇Type
    Emptyᶜ : Γ ⊢ Empty ⇇Type
    ΠΣᶜ : Γ ⊢ F ⇇Type
        → Γ ∙ F ⊢ G ⇇Type
        → ΠΣ-allowed b p q
        → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ⇇Type
    Idᶜ : Γ ⊢ A ⇇Type
        → Γ ⊢ t ⇇ A
        → Γ ⊢ u ⇇ A
        → Γ ⊢ Id A t u ⇇Type
    univᶜ : Γ ⊢ A ⇇ U l
          → Γ ⊢ A ⇇Type

  data _⊢_⇉_ (Γ : Con Term n) : (t A : Term n) → Set a where
    Levelᵢ : Γ ⊢ Level ⇉ U zeroᵘ
    zeroᵘᵢ : Γ ⊢ zeroᵘ ⇉ Level
    sucᵘᵢ : Γ ⊢ t ⇇ Level
          → Γ ⊢ sucᵘ t ⇉ Level
    maxᵘᵢ : Γ ⊢ t ⇇ Level
          → Γ ⊢ u ⇇ Level
          → Γ ⊢ t maxᵘ u ⇉ Level
    Uᵢ : Γ ⊢ l ⇇ Level → Γ ⊢ U l ⇉ U (sucᵘ l)
    Liftᵢ : Γ ⊢ l₂ ⇇ Level
          → Γ ⊢ A ⇉ C
          → Γ ⊢ C ↘ U l₁
          → Γ ⊢ Lift l₂ A ⇉ U (l₁ maxᵘ l₂)
    liftᵢ : Γ ⊢ l ⇇ Level
          → Γ ⊢ t ⇉ B
          → Γ ⊢ lift l t ⇉ Lift l B
    ΠΣᵢ : Γ ⊢ A ⇉ C₁
        → Γ ⊢ C₁ ↘ U l
        → Γ ∙ A ⊢ B ⇇ U (wk1 l)
        → ΠΣ-allowed b p q
        → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇉ U l
    varᵢ : ∀ {x}
         → x ∷ A ∈ Γ
         → Γ ⊢ var x ⇉ A
    lowerᵢ : Γ ⊢ t ⇉ A
           → Γ ⊢ A ↘ Lift l B
           → Γ ⊢ lower t ⇉ B
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
    ℕᵢ : Γ ⊢ ℕ ⇉ U zeroᵘ
    zeroᵢ : Γ ⊢ zero ⇉ ℕ
    sucᵢ : Γ ⊢ t ⇇ ℕ
         → Γ ⊢ suc t ⇉ ℕ
    natrecᵢ : ∀ {z s n}
            → Γ ∙ ℕ ⊢ A ⇇Type
            → Γ ⊢ z ⇇ A [ zero ]₀
            → Γ ∙ ℕ ∙ A ⊢ s ⇇ A [ suc (var x1) ]↑²
            → Γ ⊢ n ⇇ ℕ
            → Γ ⊢ natrec p q r A z s n ⇉ A [ n ]₀
    Unitᵢ : Γ ⊢ l ⇇ Level
          → Unit-allowed s
          → Γ ⊢ Unit s l ⇉ U l
    starᵢ : Γ ⊢ l ⇇ Level
          → Unit-allowed s
          → Γ ⊢ star s l ⇉ Unit s l
    unitrecᵢ : Γ ⊢ l ⇇ Level
             → Γ ∙ Unitʷ l ⊢ A ⇇Type
             → Γ ⊢ t ⇇ Unitʷ l
             → Γ ⊢ u ⇇ A [ starʷ l ]₀
             → Γ ⊢ unitrec p q l A t u ⇉ A [ t ]₀
    Emptyᵢ : Γ ⊢ Empty ⇉ U zeroᵘ
    emptyrecᵢ : Γ ⊢ A ⇇Type
              → Γ ⊢ t ⇇ Empty
              → Γ ⊢ emptyrec p A t ⇉ A
    Idᵢ : Γ ⊢ A ⇉ B
        → Γ ⊢ B ↘ U l
        → Γ ⊢ t ⇇ A
        → Γ ⊢ u ⇇ A
        → Γ ⊢ Id A t u ⇉ U l
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

mutual

  -- Checkable types.

  data Checkable-type {n : Nat} : Term n → Set a where
    Liftᶜ  : Checkable l →
             Checkable-type A →
             Checkable-type (Lift l A)
    ΠΣᶜ    : Checkable-type A → Checkable-type B →
             Checkable-type (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
    Idᶜ    : Checkable-type A → Checkable t → Checkable u →
             Checkable-type (Id A t u)
    checkᶜ : Checkable A → Checkable-type A

  -- Inferable terms.

  data Inferable {n : Nat} : (Term n) → Set a where
    Levelᵢ : Inferable Level
    zeroᵘᵢ : Inferable zeroᵘ
    sucᵘᵢ : Checkable t → Inferable (sucᵘ t)
    maxᵘᵢ : Checkable t → Checkable u → Inferable (t maxᵘ u)
    Uᵢ : Checkable l → Inferable (U l)
    Liftᵢ : Checkable l → Inferable A → Inferable (Lift l A)
    liftᵢ : Checkable l → Inferable t → Inferable (lift l t)
    ΠΣᵢ : Inferable A → Checkable B → Inferable (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
    varᵢ : ∀ {x} → Inferable (var x)
    lowerᵢ : Inferable t → Inferable (lower t)
    ∘ᵢ : Inferable t → Checkable u → Inferable (t ∘⟨ p ⟩ u)
    fstᵢ : Inferable t → Inferable (fst p t)
    sndᵢ : Inferable t → Inferable (snd p t)
    prodrecᵢ : Checkable-type A → Inferable t → Checkable u →
               Inferable (prodrec p q r A t u)
    ℕᵢ : Inferable ℕ
    zeroᵢ : Inferable zero
    sucᵢ : Checkable t → Inferable (suc t)
    natrecᵢ : Checkable-type A → Checkable t → Checkable u → Checkable v →
              Inferable (natrec p q r A t u v)
    Unitᵢ : Checkable l → Inferable (Unit s l)
    starᵢ : Checkable l → Inferable (star s l)
    unitrecᵢ : Checkable l → Checkable-type A → Checkable t → Checkable u →
               Inferable (unitrec p q l A t u)
    Emptyᵢ : Inferable Empty
    emptyrecᵢ : Checkable-type A → Checkable t →
                Inferable (emptyrec p A t)
    Idᵢ : Inferable A → Checkable t → Checkable u → Inferable (Id A t u)
    Jᵢ : Checkable-type A → Checkable t → Checkable-type B →
         Checkable u → Checkable v → Checkable w →
         Inferable (J p q A t B u v w)
    Kᵢ : Checkable-type A → Checkable t → Checkable-type B →
         Checkable u → Checkable v → Inferable (K p A t B u v)
    []-congᵢ : Checkable-type A → Checkable t → Checkable u →
               Checkable v → Inferable ([]-cong s A t u v)

  -- Checkable terms.

  data Checkable : (Term n) → Set a where
    lamᶜ : Checkable t → Checkable (lam p t)
    prodᶜ : ∀ {m} → Checkable t → Checkable u → Checkable (prod m p t u)
    rflᶜ : Checkable {n = n} rfl
    infᶜ : Inferable t → Checkable t

-- CheckableCon Γ means that the types in Γ are checkable.

data CheckableCon : (Γ : Con Term n) → Set a where
  ε   : CheckableCon ε
  _∙_ : CheckableCon Γ → Checkable-type A → CheckableCon (Γ ∙ A)

mutual

  -- Γ ⊢ A ⇇Type implies that A is a checkable type.

  Checkable⇇Type : Γ ⊢ A ⇇Type → Checkable-type A
  Checkable⇇Type Levelᶜ      = checkᶜ (infᶜ Levelᵢ)
  Checkable⇇Type (Liftᶜ l A) = Liftᶜ (Checkable⇇ l) (Checkable⇇Type A)
  Checkable⇇Type (Uᶜ l)      = checkᶜ (infᶜ (Uᵢ (Checkable⇇ l)))
  Checkable⇇Type ℕᶜ          = checkᶜ (infᶜ ℕᵢ)
  Checkable⇇Type (Unitᶜ l _) = checkᶜ (infᶜ (Unitᵢ (Checkable⇇ l)))
  Checkable⇇Type Emptyᶜ      = checkᶜ (infᶜ Emptyᵢ)
  Checkable⇇Type (ΠΣᶜ A B _) = ΠΣᶜ (Checkable⇇Type A) (Checkable⇇Type B)
  Checkable⇇Type (Idᶜ A t u) = Idᶜ (Checkable⇇Type A) (Checkable⇇ t)
                                 (Checkable⇇ u)
  Checkable⇇Type (univᶜ A) = checkᶜ (Checkable⇇ A)

  -- Γ ⊢ t ⇇ A implies that t is a checkable term.

  Checkable⇇ : Γ ⊢ t ⇇ A → Checkable t
  Checkable⇇ (lamᶜ x t⇇A) = lamᶜ (Checkable⇇ t⇇A)
  Checkable⇇ (prodᶜ x t⇇A t⇇A₁) = prodᶜ (Checkable⇇ t⇇A) (Checkable⇇ t⇇A₁)
  Checkable⇇ (rflᶜ _ _) = rflᶜ
  Checkable⇇ (infᶜ x x₁) = infᶜ (Inferable⇉ x)

  -- Γ ⊢ t ⇉ A implies that t is an inferable term.

  Inferable⇉ : Γ ⊢ t ⇉ A → Inferable t
  Inferable⇉ Levelᵢ = Levelᵢ
  Inferable⇉ zeroᵘᵢ = zeroᵘᵢ
  Inferable⇉ (sucᵘᵢ x) = sucᵘᵢ (Checkable⇇ x)
  Inferable⇉ (maxᵘᵢ x x₁) = maxᵘᵢ (Checkable⇇ x) (Checkable⇇ x₁)
  Inferable⇉ (Uᵢ l) = Uᵢ (Checkable⇇ l)
  Inferable⇉ (Liftᵢ l A ↘U) = Liftᵢ (Checkable⇇ l) (Inferable⇉ A)
  Inferable⇉ (liftᵢ l t) = liftᵢ (Checkable⇇ l) (Inferable⇉ t)
  Inferable⇉ (lowerᵢ x y) = lowerᵢ (Inferable⇉ x)
  Inferable⇉ (ΠΣᵢ A _ B _) = ΠΣᵢ (Inferable⇉ A) (Checkable⇇ B)
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
  Inferable⇉ (Unitᵢ l _) = Unitᵢ (Checkable⇇ l)
  Inferable⇉ (starᵢ l _) = starᵢ (Checkable⇇ l)
  Inferable⇉ (unitrecᵢ l x x₁ x₂) = unitrecᵢ (Checkable⇇ l) (Checkable⇇Type x) (Checkable⇇ x₁) (Checkable⇇ x₂)
  Inferable⇉ Emptyᵢ = Emptyᵢ
  Inferable⇉ (emptyrecᵢ x x₁) = emptyrecᵢ (Checkable⇇Type x) (Checkable⇇ x₁)
  Inferable⇉ (Idᵢ A _ t u) =
    Idᵢ (Inferable⇉ A) (Checkable⇇ t) (Checkable⇇ u)
  Inferable⇉ (Jᵢ A t B u v w) =
    Jᵢ (Checkable⇇Type A) (Checkable⇇ t) (Checkable⇇Type B)
      (Checkable⇇ u) (Checkable⇇ v) (Checkable⇇ w)
  Inferable⇉ (Kᵢ A t B u v _) =
    Kᵢ (Checkable⇇Type A) (Checkable⇇ t) (Checkable⇇Type B)
      (Checkable⇇ u) (Checkable⇇ v)
  Inferable⇉ ([]-congᵢ A t u v _) =
    []-congᵢ (Checkable⇇Type A) (Checkable⇇ t) (Checkable⇇ u)
      (Checkable⇇ v)
