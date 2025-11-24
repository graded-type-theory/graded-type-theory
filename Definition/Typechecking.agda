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

open Modality 𝕄
open Type-restrictions R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant

open import Definition.Typed R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Reduction R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Relation

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
    Levelᶜ : Level-allowed
           → Γ ⊢ Level ⇇Type
    Uᶜ : Γ ⊢ l ⇇Level → Γ ⊢ U l ⇇Type
    Liftᶜ : Γ ⊢ l ⇇Level
          → Γ ⊢ A ⇇Type
          → Γ ⊢ Lift l A ⇇Type
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
    univᶜ : Γ ⊢ A ⇉ B
          → Γ ⊢ B ↘ U l
          → Γ ⊢ A ⇇Type

  data _⊢_⇉_ (Γ : Con Term n) : (t A : Term n) → Set a where
    Levelᵢ : Level-is-small → Γ ⊢ Level ⇉ U zeroᵘ
    zeroᵘᵢ : Level-allowed
           → Γ ⊢ zeroᵘ ⇉ Level
    sucᵘᵢ : Γ ⊢ t ⇇ Level
          → Γ ⊢ sucᵘ t ⇉ Level
    supᵘᵢ : Γ ⊢ t ⇇ Level
          → Γ ⊢ u ⇇ Level
          → Γ ⊢ t supᵘ u ⇉ Level
    Uᵢ : Γ ⊢ l ⇇Level → Γ ⊢ U l ⇉ U (sucᵘ l)
    Liftᵢ : Γ ⊢ l₂ ⇇Level
          → Γ ⊢ A ⇉ C
          → Γ ⊢ C ↘ U l₁
          → Γ ⊢ Lift l₂ A ⇉ U (l₁ supᵘₗ l₂)
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
    Unitᵢ : Unit-allowed s
          → Γ ⊢ Unit s ⇉ U zeroᵘ
    starᵢ : Unit-allowed s
          → Γ ⊢ star s ⇉ Unit s
    unitrecᵢ : Γ ∙ Unitʷ ⊢ A ⇇Type
             → Γ ⊢ t ⇇ Unitʷ
             → Γ ⊢ u ⇇ A [ starʷ ]₀
             → Γ ⊢ unitrec p q A t u ⇉ A [ t ]₀
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
    []-congᵢ : Γ ⊢ l ⇇Level
             → Γ ⊢ A ⇇Type
             → Γ ⊢ t ⇇ A
             → Γ ⊢ u ⇇ A
             → Γ ⊢ v ⇇ Id A t u
             → []-cong-allowed s
             → let open Erased s in
               Γ ⊢ []-cong s l A t u v ⇉
                 Id (Erased l A) [ t ] ([ u ])

  data _⊢_⇇_ (Γ : Con Term n) : (t A : Term n) → Set a where
    liftᶜ : Γ ⊢ A ↘ Lift l B
          → Γ ⊢ t ⇇ B
          → Γ ⊢ lift t ⇇ A
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

  data _⊢_⇇Level (Γ : Con Term n) (l : Term n) : Set a where
    term    : Level-allowed
            → Γ ⊢ l ⇇ Level
            → Γ ⊢ l ⇇Level
    literal : ¬ Level-allowed
            → Level-literal l
            → Γ ⊢ l ⇇Level

opaque

  -- A variant of univᶜ.

  ⊢⇇U→⊢⇇Type :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ A ⇇ U l → Γ ⊢ A ⇇Type
  ⊢⇇U→⊢⇇Type (liftᶜ U↘Lift _) =
    case whnfRed* (U↘Lift .proj₁) Uₙ of λ ()
  ⊢⇇U→⊢⇇Type (lamᶜ U↘Π _) =
    case whnfRed* (U↘Π .proj₁) Uₙ of λ ()
  ⊢⇇U→⊢⇇Type (prodᶜ U↘Σ _ _) =
    case whnfRed* (U↘Σ .proj₁) Uₙ of λ ()
  ⊢⇇U→⊢⇇Type (rflᶜ U↘Id _) =
    case whnfRed* (U↘Id .proj₁) Uₙ of λ ()
  ⊢⇇U→⊢⇇Type (infᶜ A⇉ ≡U) =
    univᶜ A⇉ (U-norm ≡U .proj₂ , Uₙ)

mutual

  -- Checkable types.

  data Checkable-type {n : Nat} : Term n → Set a where
    Liftᶜ  : Checkable-level l →
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
    supᵘᵢ : Checkable t → Checkable u → Inferable (t supᵘ u)
    Uᵢ : Checkable-level l → Inferable (U l)
    Liftᵢ : Checkable-level l → Inferable A → Inferable (Lift l A)
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
    Unitᵢ : Inferable (Unit s)
    starᵢ : Inferable (star s)
    unitrecᵢ : Checkable-type A → Checkable t → Checkable u →
               Inferable (unitrec p q A t u)
    Emptyᵢ : Inferable Empty
    emptyrecᵢ : Checkable-type A → Checkable t →
                Inferable (emptyrec p A t)
    Idᵢ : Inferable A → Checkable t → Checkable u → Inferable (Id A t u)
    Jᵢ : Checkable-type A → Checkable t → Checkable-type B →
         Checkable u → Checkable v → Checkable w →
         Inferable (J p q A t B u v w)
    Kᵢ : Checkable-type A → Checkable t → Checkable-type B →
         Checkable u → Checkable v → Inferable (K p A t B u v)
    []-congᵢ : Checkable-level l → Checkable-type A → Checkable t →
               Checkable u → Checkable v →
               Inferable ([]-cong s l A t u v)

  -- Checkable terms.

  data Checkable : (Term n) → Set a where
    liftᶜ : Checkable t → Checkable (lift t)
    lamᶜ : Checkable t → Checkable (lam p t)
    prodᶜ : ∀ {m} → Checkable t → Checkable u → Checkable (prod m p t u)
    rflᶜ : Checkable {n = n} rfl
    infᶜ : Inferable t → Checkable t

  -- Checkable levels.

  data Checkable-level (l : Term n) : Set a where
    term    : Level-allowed → Checkable l → Checkable-level l
    literal : ¬ Level-allowed → Checkable-level l

-- CheckableCon Γ means that the types in Γ are checkable.

data CheckableCon : (Γ : Con Term n) → Set a where
  ε   : CheckableCon ε
  _∙_ : CheckableCon Γ → Checkable-type A → CheckableCon (Γ ∙ A)

opaque

  -- There is a well-typed term that is checkable but not inferable.

  Checkable×¬Inferable :
    let t : Term 0
        t = lift zero
    in
    ε ⊢ t ∷ Lift zeroᵘ ℕ × Checkable t × ¬ Inferable t
  Checkable×¬Inferable =
    liftⱼ′ (⊢zeroᵘ ε) (zeroⱼ ε) ,
    liftᶜ (infᶜ zeroᵢ) ,
    (λ { () })

opaque

  -- The term A = Π p , q ▷ lam r (var x0) ▹ var x0 is a checkable
  -- type but not checkable. If Γ is empty or equality reflection is
  -- not allowed, then Γ ⊢ A does not hold.

  Checkable-type×¬Checkable :
    let A : Term 0
        A = Π p , q ▷ lam r (var x0) ▹ var x0
    in
    Checkable-type A × ¬ Checkable A ×
    (∀ {Γ} → ⦃ No-equality-reflection or-empty Γ ⦄ → ¬ Γ ⊢ A)
  Checkable-type×¬Checkable =
    ΠΣᶜ (checkᶜ (lamᶜ (infᶜ varᵢ))) (checkᶜ (infᶜ varᵢ)) ,
    (λ { (infᶜ (ΠΣᵢ () _)) }) ,
    (λ ⊢A →
       let ⊢lam , _ = inversion-ΠΣ ⊢A in
       case ⊢lam of λ {
         (univ ⊢lam) →
       let _ , _ , _ , _ , _ , U≡Π , _ = inversion-lam ⊢lam in
       U≢ΠΣⱼ U≡Π })

opaque

  -- Every well-formed type that is checkable is inferable (if the
  -- context is empty or equality reflection is disallowed).

  ⊢→Checkable→Inferable :
    ⦃ ok : No-equality-reflection or-empty Γ ⦄ →
    Γ ⊢ A → Checkable A → Inferable A
  ⊢→Checkable→Inferable ⊢A = λ where
    (liftᶜ _) →
      case ⊢A of λ {
        (univ ⊢lift) →
      let _ , _ , _ , U≡Lift = inversion-lift ⊢lift in
      ⊥-elim (U≢Liftⱼ U≡Lift) }
    (lamᶜ _) →
      case ⊢A of λ {
        (univ ⊢lam) →
      let _ , _ , _ , _ , _ , U≡Π , _ = inversion-lam ⊢lam in
      ⊥-elim (U≢ΠΣⱼ U≡Π) }
    (prodᶜ _ _) →
      case ⊢A of λ {
        (univ ⊢prod) →
      let _ , _ , _ , _ , _ , _ , _ , U≡Σ , _ = inversion-prod ⊢prod in
      ⊥-elim (U≢ΠΣⱼ U≡Σ) }
    rflᶜ →
      case ⊢A of λ {
        (univ ⊢rfl) →
      let _ , _ , _ , _ , U≡Id = inversion-rfl ⊢rfl in
      ⊥-elim (Id≢U (sym U≡Id)) }
    (infᶜ A) →
      A

opaque

  -- Every well-formed type that is a checkable type is inferable (if
  -- equality reflection is disallowed).

  ⊢→Checkable-type→Inferable :
    ⦃ ok : No-equality-reflection ⦄ →
    Γ ⊢ A → Checkable-type A → Inferable A
  ⊢→Checkable-type→Inferable ⊢A = λ where
    (Liftᶜ l B) →
      let _ , ⊢B = inversion-Lift ⊢A in
      Liftᵢ l (⊢→Checkable-type→Inferable ⊢B B)
    (ΠΣᶜ B C) →
      let ⊢B , ⊢C , _ = inversion-ΠΣ ⊢A in
      ΠΣᵢ (⊢→Checkable-type→Inferable ⊢B B)
        (infᶜ (⊢→Checkable-type→Inferable ⊢C C))
    (Idᶜ B t u) →
      let ⊢B , _ = inversion-Id ⊢A in
      Idᵢ (⊢→Checkable-type→Inferable ⊢B B) t u
    (checkᶜ A) →
      ⊢→Checkable→Inferable ⦃ ok = possibly-nonempty ⦄ ⊢A A

opaque

  -- If Level is allowed, then Checkable-level l is logically
  -- equivalent to Checkable l.

  Checkable-level⇔ :
    Level-allowed →
    Checkable-level l ⇔ Checkable l
  Checkable-level⇔ ok =
    (λ where
       (term _ l)       → l
       (literal not-ok) → ⊥-elim (not-ok ok)) ,
    term ok

opaque

  -- If Level is allowed, then Γ ⊢ l ⇇Level is logically
  -- equivalent to Γ ⊢ l ⇇ Level.

  ⊢⇇Level⇔ :
    Level-allowed →
    Γ ⊢ l ⇇Level ⇔ Γ ⊢ l ⇇ Level
  ⊢⇇Level⇔ ok =
    (λ where
       (term _ ⊢l)        → ⊢l
       (literal not-ok _) → ⊥-elim (not-ok ok)) ,
    term ok

mutual

  -- Γ ⊢ A ⇇Type implies that A is a checkable type.

  Checkable⇇Type : Γ ⊢ A ⇇Type → Checkable-type A
  Checkable⇇Type (Levelᶜ _)  = checkᶜ (infᶜ Levelᵢ)
  Checkable⇇Type (Liftᶜ l A) = Liftᶜ (Checkable⇇Level l)
                                 (Checkable⇇Type A)
  Checkable⇇Type (Uᶜ l)      = checkᶜ (infᶜ (Uᵢ (Checkable⇇Level l)))
  Checkable⇇Type ℕᶜ          = checkᶜ (infᶜ ℕᵢ)
  Checkable⇇Type (Unitᶜ _) = checkᶜ (infᶜ Unitᵢ)
  Checkable⇇Type Emptyᶜ      = checkᶜ (infᶜ Emptyᵢ)
  Checkable⇇Type (ΠΣᶜ A B _) = ΠΣᶜ (Checkable⇇Type A) (Checkable⇇Type B)
  Checkable⇇Type (Idᶜ A t u) = Idᶜ (Checkable⇇Type A) (Checkable⇇ t)
                                 (Checkable⇇ u)
  Checkable⇇Type (univᶜ A _) = checkᶜ (infᶜ (Inferable⇉ A))

  -- Γ ⊢ t ⇇ A implies that t is a checkable term.

  Checkable⇇ : Γ ⊢ t ⇇ A → Checkable t
  Checkable⇇ (liftᶜ x t⇇) = liftᶜ (Checkable⇇ t⇇)
  Checkable⇇ (lamᶜ x t⇇A) = lamᶜ (Checkable⇇ t⇇A)
  Checkable⇇ (prodᶜ x t⇇A t⇇A₁) = prodᶜ (Checkable⇇ t⇇A) (Checkable⇇ t⇇A₁)
  Checkable⇇ (rflᶜ _ _) = rflᶜ
  Checkable⇇ (infᶜ x x₁) = infᶜ (Inferable⇉ x)

  -- Γ ⊢ t ⇉ A implies that t is an inferable term.

  Inferable⇉ : Γ ⊢ t ⇉ A → Inferable t
  Inferable⇉ (Levelᵢ ok) = Levelᵢ
  Inferable⇉ (zeroᵘᵢ _) = zeroᵘᵢ
  Inferable⇉ (sucᵘᵢ x) = sucᵘᵢ (Checkable⇇ x)
  Inferable⇉ (supᵘᵢ x x₁) = supᵘᵢ (Checkable⇇ x) (Checkable⇇ x₁)
  Inferable⇉ (Uᵢ l) = Uᵢ (Checkable⇇Level l)
  Inferable⇉ (Liftᵢ l A ↘U) = Liftᵢ (Checkable⇇Level l) (Inferable⇉ A)
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
  Inferable⇉ (Unitᵢ _) = Unitᵢ
  Inferable⇉ (starᵢ _) = starᵢ
  Inferable⇉ (unitrecᵢ x x₁ x₂) = unitrecᵢ (Checkable⇇Type x) (Checkable⇇ x₁) (Checkable⇇ x₂)
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
  Inferable⇉ ([]-congᵢ l A t u v _) =
    []-congᵢ (Checkable⇇Level l) (Checkable⇇Type A) (Checkable⇇ t)
      (Checkable⇇ u) (Checkable⇇ v)

  -- Γ ⊢ t ⇇Level implies that t is a checkable level.

  Checkable⇇Level : Γ ⊢ l ⇇Level → Checkable-level l
  Checkable⇇Level (term ok l) =
    term ok (Checkable⇇ l)
  Checkable⇇Level (literal not-ok _) =
    literal not-ok
