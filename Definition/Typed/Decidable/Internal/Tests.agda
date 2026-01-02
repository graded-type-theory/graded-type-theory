------------------------------------------------------------------------
-- Various tests used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal.Tests
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open import Definition.Typed.Decidable.Internal.Equality TR
open import Definition.Typed.Decidable.Internal.Monad TR as M
  hiding (_<$>_; _⊛_)
open import Definition.Typed.Decidable.Internal.Term TR
open import Definition.Typed.Decidable.Internal.Substitution TR

open import Definition.Untyped M using (Wk)

open import Tools.Fin
open import Tools.Function using (case_of_; _∘→_)
open import Tools.Maybe
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum
import Tools.Vec as Vec

private variable
  m n n₁ n₂ n′ n′₁ n′₂ : Nat
  x₁ x₂                : Fin _
  c                    : Constants
  Δ                    : Con _ _
  s                    : Termˢ _
  b                    : Termᵇᵐ _ _
  p q r                : Termᵍ _

------------------------------------------------------------------------
-- A simple test involving the Constants

-- Checks that the meta-variable context is empty.

check-meta-con-empty : Check c (c .ms PE.≡ 0)
check-meta-con-empty {c} = do
  [ dec⇒maybe (c .ms N.≟ 0) ]with-message
    "Expected an empty meta-variable context."

------------------------------------------------------------------------
-- A simple test involving binder modes

-- The binder mode is a literal binder mode (BMΠ or BMΣ s; s does not
-- have to be a literal).

data Is-literal-binder-mode {m n} : Termᵇᵐ m n → Set a where
  BMΠ : Is-literal-binder-mode BMΠ
  BMΣ : ∀ s → Is-literal-binder-mode (BMΣ s)

-- Is the binder mode a literal binder mode?

is-literal-binder-mode? :
  (b : Termᵇᵐ m n) → Maybe (Is-literal-binder-mode b)
is-literal-binder-mode? BMΠ     = just BMΠ
is-literal-binder-mode? (BMΣ _) = just (BMΣ _)
is-literal-binder-mode? _       = nothing

------------------------------------------------------------------------
-- Checkable and inferable terms

-- The term's outermost constructor indicates that its type should be
-- checked rather than inferred.

data Checkable {c : Constants} {n} : Term c n → Set a where
  lift : ∀ t → Checkable (lift nothing t)
  lam  : ∀ p t → Checkable (lam p nothing t)
  prod : ∀ s p t₁ t₂ → Checkable (prod s p nothing t₁ t₂)
  rfl  : Checkable (rfl nothing)

-- Does the term's outermost constructor indicate that its type should
-- be checked rather than inferred?

checkable? : (t : Term c n) → Maybe (Checkable t)
checkable? (lift nothing _)       = just (lift _)
checkable? (lam _ nothing _)      = just (lam _ _)
checkable? (prod _ _ nothing _ _) = just (prod _ _ _ _)
checkable? (rfl nothing)          = just rfl
checkable? _                      = nothing

-- The term's outermost constructor indicates that its type might be
-- inferable.

infixr 30 _supᵘₗ_

data Inferable {c : Constants} {n} : Term c n → Set a where
  meta-var : ∀ x (σ : Subst c n n′) → Inferable (meta-var x σ)
  var      : ∀ x → Inferable (var x)
  defn     : ∀ α → Inferable (defn α)
  Level    : Inferable Level
  zeroᵘ    : Inferable zeroᵘ
  sucᵘ     : ∀ l → Inferable (sucᵘ l)
  _supᵘₗ_  : ∀ l₁ l₂ → Inferable (l₁ supᵘₗ l₂)
  U        : ∀ l → Inferable (U l)
  Lift     : ∀ l A → Inferable (Lift l A)
  lift     : ∀ l t → Inferable (lift (just l) t)
  lower    : ∀ t → Inferable (lower t)
  Unit     : ∀ s → Inferable (Unit s)
  star     : ∀ s → Inferable (star s)
  unitrec  : ∀ A t₁ t₂ → Inferable (unitrec p q A t₁ t₂)
  Empty    : Inferable Empty
  emptyrec : ∀ A t → Inferable (emptyrec p A t)
  ΠΣ       : ∀ b p q A₁ A₂ → Inferable (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
  lam      : ∀ p q A t → Inferable (lam p (just (q , A)) t)
  app      : ∀ t₁ p t₂ → Inferable (t₁ ∘⟨ p ⟩ t₂)
  prod     : ∀ s p q A₂ t₁ t₂ →
             Inferable (prod s p (just (q , A₂)) t₁ t₂)
  fst      : ∀ p t → Inferable (fst p t)
  snd      : ∀ p t → Inferable (snd p t)
  prodrec  : ∀ p A t₁ t₂ → Inferable (prodrec r p q A t₁ t₂)
  ℕ        : Inferable ℕ
  zero     : Inferable zero
  suc      : ∀ t → Inferable (suc t)
  natrec   : ∀ A t₁ t₂ t₃ → Inferable (natrec p q r A t₁ t₂ t₃)
  Id       : ∀ A t₁ t₂ → Inferable (Id A t₁ t₂)
  rfl      : ∀ t → Inferable (rfl (just t))
  J        : ∀ A₁ t₁ A₂ t₂ t₃ t₄ →
             Inferable (J p q A₁ t₁ A₂ t₂ t₃ t₄)
  K        : ∀ A₁ t₁ A₂ t₂ t₃ → Inferable (K p A₁ t₁ A₂ t₂ t₃)
  []-cong  : ∀ s l A t₁ t₂ t₃ → Inferable ([]-cong s l A t₁ t₂ t₃)

-- A procedure that checks that the term's outermost constructor
-- indicates that its type might be inferable.

inferable : (t : Term c n) → Check c (Inferable t)
inferable (meta-var _ _)          = return (meta-var _ _)
inferable (var _)                 = return (var _)
inferable (defn _)                = return (defn _)
inferable Level                   = return Level
inferable zeroᵘ                   = return zeroᵘ
inferable (sucᵘ _)                = return (sucᵘ _)
inferable (_ supᵘₗ _)             = return (_ supᵘₗ _)
inferable (U _)                   = return (U _)
inferable (Lift _ _)              = return (Lift _ _)
inferable (lift (just _) _)       = return (lift _ _)
inferable (lower _)               = return (lower _)
inferable (Unit _)                = return (Unit _)
inferable (star _)                = return (star _)
inferable (unitrec _ _ _ _ _)     = return (unitrec _ _ _)
inferable Empty                   = return Empty
inferable (emptyrec _ _ _)        = return (emptyrec _ _)
inferable (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) = return (ΠΣ _ _ _ _ _)
inferable (lam _ (just _) _)      = return (lam _ _ _ _)
inferable (_ ∘⟨ _ ⟩ _)            = return (app _ _ _)
inferable (prod _ _ (just _) _ _) = return (prod _ _ _ _ _ _)
inferable (fst _ _)               = return (fst _ _)
inferable (snd _ _)               = return (snd _ _)
inferable (prodrec _ _ _ _ _ _)   = return (prodrec _ _ _ _)
inferable ℕ                       = return ℕ
inferable zero                    = return zero
inferable (suc _)                 = return (suc _)
inferable (natrec _ _ _ _ _ _ _)  = return (natrec _ _ _ _)
inferable (Id _ _ _)              = return (Id _ _ _)
inferable (rfl (just _))          = return (rfl _)
inferable (J _ _ _ _ _ _ _ _)     = return (J _ _ _ _ _ _)
inferable (K _ _ _ _ _ _)         = return (K _ _ _ _ _)
inferable ([]-cong _ _ _ _ _ _)   = return ([]-cong _ _ _ _ _ _)
inferable _                       = fail "Expected an inferable term."

------------------------------------------------------------------------
-- Eliminators

-- The two terms are applications of equal eliminators (or equal
-- variables, or equal names).

data Are-equal-eliminators (t : Term c n) : Term c n → Set a where
  meta-var : ∀ x₁ (σ₁ : Subst c n n′₁) x₂ (σ₂ : Subst c n n′₂) →
             t PE.≡ meta-var x₁ σ₁ →
             Are-equal-eliminators t (meta-var x₂ σ₂)
  var      : ∀ x → t PE.≡ var x →
             Are-equal-eliminators t (var x)
  defn     : ∀ α → t PE.≡ defn α →
             Are-equal-eliminators t (defn α)
  sup      : ∀ l₁₁ l₂₁ l₁₂ l₂₂ → t PE.≡ l₁₁ supᵘₗ l₂₁ →
             Are-equal-eliminators t (l₁₂ supᵘₗ l₂₂)
  lower    : ∀ t₁ t₂ → t PE.≡ lower t₁ →
             Are-equal-eliminators t (lower t₂)
  emptyrec : ∀ A₁ t₁ A₂ t₂ → t PE.≡ emptyrec p A₁ t₁ →
             Are-equal-eliminators t (emptyrec p A₂ t₂)
  unitrec  : ∀ A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ → t PE.≡ unitrec p q A₁ t₁₁ t₁₂ →
             Are-equal-eliminators t (unitrec p q A₂ t₂₁ t₂₂)
  app      : ∀ p t₁₁ t₁₂ t₂₁ t₂₂ → t PE.≡ t₁₁ ∘⟨ p ⟩ t₁₂ →
             Are-equal-eliminators t (t₂₁ ∘⟨ p ⟩ t₂₂)
  fst      : ∀ p t₁ t₂ → t PE.≡ fst p t₁ →
             Are-equal-eliminators t (fst p t₂)
  snd      : ∀ p t₁ t₂ → t PE.≡ snd p t₁ →
             Are-equal-eliminators t (snd p t₂)
  prodrec  : ∀ p A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ →
             t PE.≡ prodrec r p q A₁ t₁₁ t₁₂ →
             Are-equal-eliminators t (prodrec r p q A₂ t₂₁ t₂₂)
  natrec   : ∀ A₁ t₁₁ t₁₂ t₁₃ A₂ t₂₁ t₂₂ t₂₃ →
             t PE.≡ natrec p q r A₁ t₁₁ t₁₂ t₁₃ →
             Are-equal-eliminators t (natrec p q r A₂ t₂₁ t₂₂ t₂₃)
  J        : ∀ A₁₁ t₁₁ A₁₂ t₁₂ t₁₃ t₁₄ A₂₁ t₂₁ A₂₂ t₂₂ t₂₃ t₂₄ →
             t PE.≡ J p q A₁₁ t₁₁ A₁₂ t₁₂ t₁₃ t₁₄ →
             Are-equal-eliminators t (J p q A₂₁ t₂₁ A₂₂ t₂₂ t₂₃ t₂₄)
  K        : ∀ A₁₁ t₁₁ A₁₂ t₁₂ t₁₃ A₂₁ t₂₁ A₂₂ t₂₂ t₂₃ →
             t PE.≡ K p A₁₁ t₁₁ A₁₂ t₁₂ t₁₃ →
             Are-equal-eliminators t (K p A₂₁ t₂₁ A₂₂ t₂₂ t₂₃)
  []-cong  : ∀ s l₁ A₁ t₁₁ t₁₂ t₁₃ l₂ A₂ t₂₁ t₂₂ t₂₃ →
             t PE.≡ []-cong s l₁ A₁ t₁₁ t₁₂ t₁₃ →
             Are-equal-eliminators t ([]-cong s l₂ A₂ t₂₁ t₂₂ t₂₃)

-- A procedure that checks that the two terms are applications of
-- equal eliminators (or equal meta-variables, equal variables, or
-- equal names).

are-equal-eliminators :
  (t₁ t₂ : Term c n) → Check c (Are-equal-eliminators t₁ t₂)
are-equal-eliminators t₁ t₂ =
  [ are-equal-eliminators? t₁ t₂ ]with-message
    "Expected applications of equal eliminators."
  where
  are-equal-eliminators? :
    (t₁ t₂ : Term c n) → Maybe (Are-equal-eliminators t₁ t₂)
  are-equal-eliminators? (meta-var _ _) (meta-var _ _) =
    just (meta-var _ _ _ _ PE.refl)
  are-equal-eliminators? (var x₁) (var x₂) =
    (λ eq → var _ (PE.cong var eq)) <$>
    dec⇒maybe (x₁ ≟ⱽ x₂)
  are-equal-eliminators? (defn α₁) (defn α₂) =
    (λ eq → defn _ (PE.cong defn eq)) <$>
    dec⇒maybe (α₁ N.≟ α₂)
  are-equal-eliminators? (_ supᵘₗ _) (_ supᵘₗ _) =
    just (sup _ _ _ _ PE.refl)
  are-equal-eliminators? (lower _) (lower _) =
    just (lower _ _ PE.refl)
  are-equal-eliminators? (emptyrec p₁ _ _) (emptyrec p₂ _ _) =
    (λ eq → emptyrec _ _ _ _ (PE.cong (λ p → emptyrec p _ _) eq)) <$>
    p₁ ≟ᵍ p₂
  are-equal-eliminators? (unitrec p₁ q₁ _ _ _) (unitrec p₂ q₂ _ _ _) =
    (λ eq₁ eq₂ →
       unitrec _ _ _ _ _ _
         (PE.cong₂ (λ p q → unitrec p q _ _ _) eq₁ eq₂)) <$>
    p₁ ≟ᵍ p₂ ⊛ q₁ ≟ᵍ q₂
  are-equal-eliminators? (_ ∘⟨ p₁ ⟩ _) (_ ∘⟨ p₂ ⟩ _) =
    (λ eq → app _ _ _ _ _ (PE.cong (λ p → _ ∘⟨ p ⟩ _) eq)) <$>
    p₁ ≟ᵍ p₂
  are-equal-eliminators? (fst p₁ _) (fst p₂ _) =
    (λ eq → fst _ _ _ (PE.cong (λ p → fst p _) eq)) <$>
    p₁ ≟ᵍ p₂
  are-equal-eliminators? (snd p₁ _) (snd p₂ _) =
    (λ eq → snd _ _ _ (PE.cong (λ p → snd p _) eq)) <$>
    p₁ ≟ᵍ p₂
  are-equal-eliminators?
    (prodrec r₁ p₁ q₁ _ _ _) (prodrec r₂ p₂ q₂ _ _ _) =
    (λ eq₁ eq₂ eq₃ →
       prodrec _ _ _ _ _ _ _
         (PE.cong₃ (λ r p q → prodrec r p q _ _ _) eq₁ eq₂ eq₃)) <$>
    r₁ ≟ᵍ r₂ ⊛ p₁ ≟ᵍ p₂ ⊛ q₁ ≟ᵍ q₂
  are-equal-eliminators?
    (natrec p₁ q₁ r₁ _ _ _ _) (natrec p₂ q₂ r₂ _ _ _ _) =
    (λ eq₁ eq₂ eq₃ →
       natrec _ _ _ _ _ _ _ _
         (PE.cong₃ (λ p q r → natrec p q r _ _ _ _) eq₁ eq₂ eq₃)) <$>
    p₁ ≟ᵍ p₂ ⊛ q₁ ≟ᵍ q₂ ⊛ r₁ ≟ᵍ r₂
  are-equal-eliminators? (J p₁ q₁ _ _ _ _ _ _) (J p₂ q₂ _ _ _ _ _ _) =
    (λ eq₁ eq₂ →
       J _ _ _ _ _ _ _ _ _ _ _ _
         (PE.cong₂ (λ p q → J p q _ _ _ _ _ _) eq₁ eq₂)) <$>
    p₁ ≟ᵍ p₂ ⊛ q₁ ≟ᵍ q₂
  are-equal-eliminators? (K p₁ _ _ _ _ _) (K p₂ _ _ _ _ _) =
    (λ eq →
       K _ _ _ _ _ _ _ _ _ _ (PE.cong (λ p → K p _ _ _ _ _) eq)) <$>
    p₁ ≟ᵍ p₂
  are-equal-eliminators? ([]-cong s₁ _ _ _ _ _) ([]-cong s₂ _ _ _ _ _) =
    (λ eq →
       []-cong _ _ _ _ _ _ _ _ _ _ _
         (PE.cong (λ s → []-cong s _ _ _ _ _) eq)) <$>
    s₁ ≟ˢ s₂
  are-equal-eliminators? _ _ =
    nothing

------------------------------------------------------------------------
-- Type constructors

-- The term is a type constructor application (or a meta-variable).

data Is-type-constructor {c : Constants} {n} : Term c n → Set a where
  meta-var : ∀ x (σ : Subst c n n′) →
             Is-type-constructor (meta-var x σ)
  Level    : Is-type-constructor Level
  U        : ∀ l → Is-type-constructor (U l)
  Lift     : ∀ l A → Is-type-constructor (Lift l A)
  Empty    : Is-type-constructor Empty
  Unit     : ∀ s → Is-type-constructor (Unit s)
  ΠΣ       : ∀ b p q A₁ A₂ →
             Is-type-constructor (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
  ℕ        : Is-type-constructor ℕ
  Id       : ∀ A t₁ t₂ → Is-type-constructor (Id A t₁ t₂)

-- Is the term a type constructor application (or a meta-variable)?

is-type-constructor? : (A : Term c n) → Maybe (Is-type-constructor A)
is-type-constructor? (meta-var _ _) =
  just (meta-var _ _)
is-type-constructor? Level =
  just Level
is-type-constructor? (U _) =
  just (U _)
is-type-constructor? (Lift _ _) =
  just (Lift _ _)
is-type-constructor? Empty =
  just Empty
is-type-constructor? (Unit _) =
  just (Unit _)
is-type-constructor? ℕ =
  just ℕ
is-type-constructor? (ΠΣ⟨ b ⟩ _ , _ ▷ _ ▹ _) =
  just (ΠΣ _ _ _ _ _)
is-type-constructor? (Id _ _ _) =
  just (Id _ _ _)
is-type-constructor? _ =
  nothing

-- A variant of Is-type-constructor that only holds for
-- ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂ if b is a literal.

data Is-type-constructorˡ {c : Constants} {n} : Term c n → Set a where
  meta-var : ∀ x (σ : Subst c n n′) →
             Is-type-constructorˡ (meta-var x σ)
  Level    : Is-type-constructorˡ Level
  U        : ∀ l → Is-type-constructorˡ (U l)
  Lift     : ∀ l A → Is-type-constructorˡ (Lift l A)
  Empty    : Is-type-constructorˡ Empty
  Unit     : ∀ s → Is-type-constructorˡ (Unit s)
  ΠΣ       : Is-literal-binder-mode b →
             ∀ p q A₁ A₂ →
             Is-type-constructorˡ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
  ℕ        : Is-type-constructorˡ ℕ
  Id       : ∀ A t₁ t₂ → Is-type-constructorˡ (Id A t₁ t₂)

-- Does Is-type-constructorˡ hold for the given term?

is-type-constructorˡ? : (A : Term c n) → Maybe (Is-type-constructorˡ A)
is-type-constructorˡ? (meta-var _ _) =
  just (meta-var _ _)
is-type-constructorˡ? Level =
  just Level
is-type-constructorˡ? (U _) =
  just (U _)
is-type-constructorˡ? (Lift _ _) =
  just (Lift _ _)
is-type-constructorˡ? Empty =
  just Empty
is-type-constructorˡ? (Unit _) =
  just (Unit _)
is-type-constructorˡ? ℕ =
  just ℕ
is-type-constructorˡ? (ΠΣ⟨ b ⟩ _ , _ ▷ _ ▹ _) =
  (λ b → ΠΣ b _ _ _ _) <$> is-literal-binder-mode? b
is-type-constructorˡ? (Id _ _ _) =
  just (Id _ _ _)
is-type-constructorˡ? _ =
  nothing

-- The two terms are applications of equal type constructors (or both
-- meta-variables).

data Are-equal-type-constructors (A : Term c n) :
       Term c n → Set a where
  meta-var : ∀ x₁ (σ₁ : Subst c n n′₁) x₂ (σ₂ : Subst c n n′₂) →
             A PE.≡ meta-var x₁ σ₁ →
             Are-equal-type-constructors A (meta-var x₂ σ₂)
  Level    : A PE.≡ Level → Are-equal-type-constructors A Level
  U        : ∀ l₁ l₂ → A PE.≡ U l₁ →
             Are-equal-type-constructors A (U l₂)
  Lift     : ∀ l₁ A₁ l₂ A₂ → A PE.≡ Lift l₁ A₁ →
             Are-equal-type-constructors A (Lift l₂ A₂)
  Empty    : A PE.≡ Empty → Are-equal-type-constructors A Empty
  Unit     : A PE.≡ Unit s → Are-equal-type-constructors A (Unit s)
  ΠΣ       : ∀ B₁₁ B₁₂ B₂₁ B₂₂ → A PE.≡ ΠΣ⟨ b ⟩ p , q ▷ B₁₁ ▹ B₁₂ →
             Are-equal-type-constructors A (ΠΣ⟨ b ⟩ p , q ▷ B₂₁ ▹ B₂₂)
  ℕ        : A PE.≡ ℕ → Are-equal-type-constructors A ℕ
  Id       : ∀ B₁ t₁₁ t₁₂ B₂ t₂₁ t₂₂ → A PE.≡ Id B₁ t₁₁ t₁₂ →
             Are-equal-type-constructors A (Id B₂ t₂₁ t₂₂)

-- Are the terms applications of equal type constructors?
--
-- Note that this function matches on reflexivity "before" returning
-- the meta-var constructor.

are-equal-type-constructors? :
  (A₁ A₂ : Term c n) → Maybe (Are-equal-type-constructors A₁ A₂)
are-equal-type-constructors? (meta-var _ _) (meta-var _ _) =
  just (meta-var _ _ _ _ PE.refl)
are-equal-type-constructors? Level Level =
  just (Level PE.refl)
are-equal-type-constructors? (U _) (U _) =
  just (U _ _ PE.refl)
are-equal-type-constructors? (Lift _ _) (Lift _ _) =
  just (Lift _ _ _ _ PE.refl)
are-equal-type-constructors? Empty Empty =
  just (Empty PE.refl)
are-equal-type-constructors? (Unit s₁) (Unit s₂) =
  (λ eq → Unit (PE.cong Unit eq)) <$>
  s₁ ≟ˢ s₂
are-equal-type-constructors?
  (ΠΣ⟨ b₁ ⟩ p₁ , q₁ ▷ A₁₁ ▹ A₁₂) (ΠΣ⟨ b₂ ⟩ p₂ , q₂ ▷ A₂₁ ▹ A₂₂) =
  (λ eq₁ eq₂ eq₃ →
     ΠΣ _ _ _ _
       (PE.cong₃ (λ b p q → ΠΣ⟨ b ⟩ p , q ▷ _ ▹ _) eq₁ eq₂ eq₃)) <$>
  b₁ ≟ᵇᵐ b₂ ⊛ p₁ ≟ᵍ p₂ ⊛ q₁ ≟ᵍ q₂
are-equal-type-constructors? ℕ ℕ =
  just (ℕ PE.refl)
are-equal-type-constructors? (Id A₁ t₁₁ t₁₂) (Id A₂ t₂₁ t₂₂) =
  just (Id _ _ _ _ _ _ PE.refl)
are-equal-type-constructors? _ _ =
  nothing

------------------------------------------------------------------------
-- Some simple tests involving terms

-- The term is an application of weaken or subst.

data Is-weaken-subst {c : Constants} {n} :
       Term c n → Set a where
  weaken : ∀ (ρ : Wk n n′) t → Is-weaken-subst (weaken ρ t)
  subst  : ∀ t (σ : Subst c n n′) → Is-weaken-subst (subst t σ)

-- Is the term an application of weaken or subst?

is-weaken-subst? : (t : Term c n) → Maybe (Is-weaken-subst t)
is-weaken-subst? (weaken _ _) = just (weaken _ _)
is-weaken-subst? (subst _ _)  = just (subst _ _)
is-weaken-subst? _            = nothing

-- Are the two terms both applications of meta-variables?

are-meta-variables? :
  (l₁ l₂ : Term c n) →
  Maybe
    (∃₆ λ m₁ (x₁ : Meta-var c m₁) σ₁ m₂ (x₂ : Meta-var c m₂) σ₂ →
     l₁ PE.≡ meta-var x₁ σ₁ × l₂ PE.≡ meta-var x₂ σ₂)
are-meta-variables? (meta-var _ _) (meta-var _ _) =
  just (_ , _ , _ , _ , _ , _ , PE.refl , PE.refl)
are-meta-variables? _ _ =
  nothing

opaque

  -- A lemma related to equality of meta-variables.

  var-cong :
    {eq₁ : Vec.lookup (c .meta-con-size) x₁ PE.≡ n}
    {eq₂ : Vec.lookup (c .meta-con-size) x₂ PE.≡ n} →
    x₁ PE.≡ x₂ →
    Meta-var.var {c = c} x₁ eq₁ PE.≡ var x₂ eq₂
  var-cong PE.refl = PE.cong (var _) N.Nat-set

-- Are the two meta-variables equal?

infix 4 _≟ᵐᵛ_

_≟ᵐᵛ_ : (x₁ x₂ : Meta-var c n) → Maybe (x₁ PE.≡ x₂)
var x₁ _ ≟ᵐᵛ var x₂ _ = var-cong <$> dec⇒maybe (x₁ ≟ⱽ x₂)

-- A procedure that checks that the term is the type Level.

is-Level : (A : Term c n) → Check c (A PE.≡ Level)
is-Level Level = return PE.refl
is-Level _     = fail "Expected Level."

-- A procedure that checks that the term is the level zeroᵘ.

is-zeroᵘ : (l : Term c n) → Check c (l PE.≡ zeroᵘ)
is-zeroᵘ zeroᵘ = return PE.refl
is-zeroᵘ _     = fail "Expected the level zeroᵘ."

-- The term is a level constructor.

data Level-con {c n} : Term c n → Set a where
  zeroᵘ : Level-con zeroᵘ
  sucᵘ  : ∀ l → Level-con (sucᵘ l)

-- Is the term a level constructor?

level-con? : (l : Term c n) → Maybe (Level-con l)
level-con? zeroᵘ    = just zeroᵘ
level-con? (sucᵘ _) = just (sucᵘ _)
level-con? _        = nothing

-- The terms are applications of equal level constructors.

data Equal-level-cons {c n} : Term c n → Term c n → Set a where
  zeroᵘ : Equal-level-cons zeroᵘ zeroᵘ
  sucᵘ  : ∀ l₁ l₂ → Equal-level-cons (sucᵘ l₁) (sucᵘ l₂)

-- Are the terms applications of equal level constructors?

equal-level-cons? : (l₁ l₂ : Term c n) → Maybe (Equal-level-cons l₁ l₂)
equal-level-cons? zeroᵘ    zeroᵘ    = just zeroᵘ
equal-level-cons? (sucᵘ _) (sucᵘ _) = just (sucᵘ _ _)
equal-level-cons? _        _        = nothing

-- The top-level constructor of the term indicates that it is
-- something that could possibly be a level, even if Level is not
-- allowed. Weakenings and substitutions are assumed to have been
-- removed.

data Is-perhaps-level {c n} : Term c n → Set a where
  meta-var : ∀ (x : Meta-var c m) σ → Is-perhaps-level (meta-var x σ)
  zeroᵘ    : Is-perhaps-level zeroᵘ
  sucᵘ     : ∀ l → Is-perhaps-level (sucᵘ l)
  _supᵘₗ_  : ∀ l₁ l₂ → Is-perhaps-level (l₁ supᵘₗ l₂)

-- Does the top-level constructor of the term indicate that it is
-- something that could possibly be a level, even if Level is not
-- allowed?

is-perhaps-level? : (l : Term c n) → Maybe (Is-perhaps-level l)
is-perhaps-level? (meta-var _ _) = just (meta-var _ _)
is-perhaps-level? zeroᵘ          = just zeroᵘ
is-perhaps-level? (sucᵘ _)       = just (sucᵘ _)
is-perhaps-level? (_ supᵘₗ _)    = just (_ supᵘₗ _)
is-perhaps-level? _              = nothing

-- A procedure that checks that the term is an application of U.

is-U : (A : Term c n) → Check c (∃ λ l → A PE.≡ U l)
is-U (U _) = return (_ , PE.refl)
is-U _     = fail "Expected an application of U."

-- A procedure that checks that the term is an application of Lift.

is-Lift : (t : Term c n) → Check c (∃₂ λ l A → t PE.≡ Lift l A)
is-Lift (Lift l A) = return (_ , _ , PE.refl)
is-Lift _          = fail "Expected an application of Lift."

-- Is the term an application of lift?

is-lift? : (t : Term c n) → Maybe (∃₂ λ l u → t PE.≡ lift l u)
is-lift? (lift l t) = just (_ , _ , PE.refl)
is-lift? _          = nothing

-- Is the term equal to star s?

is-star? : ∀ s (t : Term c n) → Maybe (t PE.≡ star s)
is-star? s (star s′) = PE.cong star <$> s′ ≟ˢ s
is-star? _ _         = nothing

-- Are the terms both equal to star s?

are-star? :
  ∀ s (t₁ t₂ : Term c n) → Maybe (t₁ PE.≡ star s × t₂ PE.≡ star s)
are-star? s (star s₁) (star s₂) =
  (λ eq₁ eq₂ → PE.cong star eq₁ , PE.cong star eq₂) <$>
  s₁ ≟ˢ s ⊛ s₂ ≟ˢ s
are-star? _ _ _ =
  nothing

-- A procedure that checks that the term is an application of
-- ΠΣ⟨ b ⟩ p ,_▷_▹_.

is-ΠΣ :
  ∀ b p (A : Term c n) →
  Check c (∃₃ λ q A₁ A₂ → A PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
is-ΠΣ b p A =
  [ is-ΠΣ? b p A ]with-message
    "Expected a certain kind of Π- or Σ-type."
  where
  is-ΠΣ? :
    ∀ b p (A : Term c n) →
    Maybe (∃₃ λ q A₁ A₂ → A PE.≡ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
  is-ΠΣ? b p (ΠΣ⟨ b′ ⟩ p′ , _ ▷ _ ▹ _) =
    (λ eq₁ eq₂ →
       _ , _ , _ , PE.cong₂ (λ b p → ΠΣ⟨ b ⟩ p , _ ▷ _ ▹ _) eq₁ eq₂) <$>
    b′ ≟ᵇᵐ b ⊛ p′ ≟ᵍ p
  is-ΠΣ? _ _ _ =
    nothing

-- Is the term equal to an application of lam p?

is-lam? : ∀ p (t : Term c n) → Maybe (∃₂ λ qA u → t PE.≡ lam p qA u)
is-lam? p (lam p′ _ _) =
  (λ eq → _ , _ , PE.cong (λ p → lam p _ _) eq) <$>
  p′ ≟ᵍ p
is-lam? _ _ =
  nothing

-- Is the term equal to an application of prod s p?

is-prod? :
  ∀ s p (t : Term c n) →
  Maybe (∃₃ λ qA₂ t₁ t₂ → t PE.≡ prod s p qA₂ t₁ t₂)
is-prod? s p (prod s′ p′ _ _ _) =
  (λ eq₁ eq₂ →
     _ , _ , _ , PE.cong₂ (λ s p → prod s p _ _ _) eq₁ eq₂) <$>
  s′ ≟ˢ s ⊛ p′ ≟ᵍ p
is-prod? _ _ _ =
  nothing

-- Are the terms both applications of prod s p?

are-prod? :
  ∀ s p (t₁ t₂ : Term c n) →
  Maybe
    (∃₆ λ qA₂₁ t₁₁ t₂₁ qA₂₂ t₁₂ t₂₂ →
     t₁ PE.≡ prod s p qA₂₁ t₁₁ t₂₁ × t₂ PE.≡ prod s p qA₂₂ t₁₂ t₂₂)
are-prod? s p (prod s₁ p₁ _ _ _) (prod s₂ p₂ _ _ _) =
  (λ eq₁ eq₂ eq₃ eq₄ →
     _ , _ , _ , _ , _ , _ ,
     (case eq₁ of λ {
        PE.refl →
      case eq₂ of λ {
        PE.refl →
      case eq₃ of λ {
        PE.refl →
      case eq₄ of λ {
        PE.refl →
      PE.refl , PE.refl }}}})) <$>
  s ≟ˢ s₁ ⊛ s ≟ˢ s₂ ⊛ p ≟ᵍ p₁ ⊛ p ≟ᵍ p₂
are-prod? _ _ _ _ =
  nothing

-- Is the term equal to zero or an application of suc?

is-zero-or-suc? :
  (t : Term c n) → Maybe (t PE.≡ zero ⊎ ∃ λ u → t PE.≡ suc u)
is-zero-or-suc? zero    = just (inj₁ PE.refl)
is-zero-or-suc? (suc _) = just (inj₂ (_ , PE.refl))
is-zero-or-suc? _       = nothing

-- Are both terms equal to zero or both terms applications of suc?

are-zero-or-suc? :
  (t₁ t₂ : Term c n) →
  Maybe (t₁ PE.≡ zero × t₂ PE.≡ zero ⊎
         ∃₂ λ u₁ u₂ → t₁ PE.≡ suc u₁ × t₂ PE.≡ suc u₂)
are-zero-or-suc? zero zero =
  just (inj₁ (PE.refl , PE.refl))
are-zero-or-suc? (suc _) (suc _) =
  just (inj₂ (_ , _ , PE.refl , PE.refl))
are-zero-or-suc? _ _ =
  nothing

-- A procedure that checks that the term is an application of Id.

is-Id : (A : Term c n) → Check c (∃₃ λ B t₁ t₂ → A PE.≡ Id B t₁ t₂)
is-Id (Id _ _ _) = return (_ , _ , _ , PE.refl)
is-Id -          = fail "Expected an identity type."

-- Is the term an application of rfl?

is-rfl? : (t : Term c n) → Maybe (∃ λ u → t PE.≡ rfl u)
is-rfl? (rfl _) = just (_ , PE.refl)
is-rfl? _       = nothing

-- Are both terms equal to applications of rfl?

are-rfl? :
  (t₁ t₂ : Term c n) →
  Maybe (∃₂ λ u₁ u₂ → t₁ PE.≡ rfl u₁ × t₂ PE.≡ rfl u₂)
are-rfl? (rfl _) (rfl _) = just (_ , _ , PE.refl , PE.refl)
are-rfl? _       _       = nothing

------------------------------------------------------------------------
-- Some simple tests involving contexts

-- A procedure that checks that the context is an application of _∙_.

is-∙ : (Γ : Con c (1+ n)) → Check c (∃₂ λ Δ A → Γ PE.≡ Δ ∙ A)
is-∙ (Γ ∙ A) = return (_ , _ , PE.refl)
is-∙ _       = fail "Expected a non-empty context."

-- A procedure that checks that the context is an application of base.

is-base :
  (Γ : Con c (c .base-con-size)) →
  Check c (∃ λ b → Γ PE.≡ base {b = b})
is-base {c} Γ = is-base′ Γ PE.refl
  where
  is-base′ :
    (Γ : Con c n) (eq : n PE.≡ c .base-con-size) →
    Check c (∃ λ b → PE.subst (Con c) eq Γ PE.≡ base {b = b})
  is-base′ (base {b}) _ =
    return
      (b ,
       PE.subst
         (λ eq → PE.subst (Con c) eq (base {b = b}) PE.≡ base {b = b})
         N.Nat-set PE.refl)
  is-base′ _ _ =
    fail "Expected the base context."

-- The two contexts have equal outermost constructors.

data Equal-con-constructors {c : Constants} :
       Con c n₁ → Con c n₂ → Set a where
  base : {b₁ b₂ : Base-con-allowed c} →
         Equal-con-constructors (base {b = b₁}) (base {b = b₂})
  ε    : Equal-con-constructors ε ε
  ext  : ∀ (Δ₁ : Con c n₁) A₁ (Δ₂ : Con c n₂) A₂ →
         Equal-con-constructors (Δ₁ ∙ A₁) (Δ₂ ∙ A₂)

-- A procedure that checks that the two contexts have equal outermost
-- constructors.

equal-con-constructors :
  (Δ₁ : Con c n₁) (Δ₂ : Con c n₂) →
  Check c (Equal-con-constructors Δ₁ Δ₂)
equal-con-constructors base     base     = return base
equal-con-constructors ε        ε        = return ε
equal-con-constructors (_ ∙ _)  (_ ∙ _)  = return (ext _ _ _ _)
equal-con-constructors _        _        =
  fail "Expected two contexts with equal outermost constructors."

-- The two contexts have equal outermost constructors.
--
-- This variant of Equal-con-constructors is restricted to contexts
-- that have equal lengths.

data Equal-con-constructors⁼ {c : Constants} :
       Con c n → Con c n → Set a where
  base : {b₁ b₂ : Base-con-allowed c} →
         Δ PE.≡ base {b = b₂} →
         Equal-con-constructors⁼ (base {b = b₁}) Δ
  ε    : Equal-con-constructors⁼ ε ε
  ext  : ∀ (Δ₁ : Con c n) A₁ Δ₂ A₂ →
         Equal-con-constructors⁼ (Δ₁ ∙ A₁) (Δ₂ ∙ A₂)

-- A procedure that checks that the two contexts have equal outermost
-- constructors.

equal-con-constructors⁼ :
  (Δ₁ Δ₂ : Con c n) → Check c (Equal-con-constructors⁼ Δ₁ Δ₂)
equal-con-constructors⁼ base Δ₂ =
  base ∘→ proj₂ M.<$> is-base Δ₂
equal-con-constructors⁼ ε ε =
  return ε
equal-con-constructors⁼ (_ ∙ _) (_ ∙ _) =
  return (ext _ _ _ _)
equal-con-constructors⁼ _ _ =
  fail "Expected two contexts with equal outermost constructors."

------------------------------------------------------------------------
-- Some simple tests involving substitutions

-- Is the substitution equal to id?
--
-- Note that this variant of is-id? is (only) defined for
-- substitutions with equal natural number indices.

is-id?⁼ : (σ : Subst c n n) → Maybe (σ PE.≡ id)
is-id?⁼ σ = is-id?⁼′ σ PE.refl
  where
  is-id?⁼′ :
    (σ : Subst c n₂ n₁) (eq : n₁ PE.≡ n₂) →
    Maybe (PE.subst (Subst c n₂) eq σ PE.≡ id)
  is-id?⁼′ {c} {n₂} id _ =
    just
      (PE.subst (λ eq → PE.subst (Subst c n₂) eq id PE.≡ id) N.Nat-set
         PE.refl)
  is-id?⁼′ _ _ =
    nothing

-- The two substitutions are equal applications of wk1, zero or more
-- times, to id, and the context is equal to a corresponding number of
-- applications of _∙_.

data Both-wk1-id {c : Constants} {n₁} :
       (_ _ : Subst c n₂ n₁) → Set a where
  both :
    ∀ k {σ₂} → σ₂ PE.≡ wkSubst k id →
    Both-wk1-id (wkSubst k id) σ₂

-- A procedure that checks that the two substitutions are equal
-- applications of wk1, zero or more times, to id.

both-wk1-id : (σ₁ σ₂ : Subst c n₂ n₁) → Check c (Both-wk1-id σ₁ σ₂)
both-wk1-id σ₁ σ₂ =
  [ both-wk1-id? σ₁ σ₂ ]with-message
    "Expected equal iterated applications of wk1 to id."
  where
  both-wk1-id? : (σ₁ σ₂ : Subst c n₂ n₁) → Maybe (Both-wk1-id σ₁ σ₂)
  both-wk1-id? id σ₂ =
    both _ <$> is-id?⁼ σ₂
  both-wk1-id? (wk1 σ₁) (wk1 σ₂) =
    (λ { (both _ eq) → both _ (PE.cong wk1 eq) }) <$>
    both-wk1-id? σ₁ σ₂
  both-wk1-id? _ _ =
    nothing
