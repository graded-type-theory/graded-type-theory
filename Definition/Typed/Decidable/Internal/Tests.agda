------------------------------------------------------------------------
-- Various tests used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Typed.Decidable.Internal.Tests
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open import Definition.Typed.Decidable.Internal.Monad 𝕄 as M
  hiding (_<$>_; _⊛_)
open import Definition.Typed.Decidable.Internal.Term 𝕄
open import Definition.Typed.Decidable.Internal.Substitution 𝕄

open import Definition.Untyped M as U using (Universe-level; Wk)
open import Definition.Untyped.Properties M

open import Tools.Bool as B using (T)
open import Tools.Fin as Fin
open import Tools.Function using (case_of_; flip; idᶠ; _∘→_)
open import Tools.List as List
open import Tools.Maybe
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Sum
import Tools.Vec as Vec

private variable
  m n n₁ n₂ n′ n′₁ n′₂ : Nat
  x₁ x₂                : Fin _
  c                    : Constants
  Δ                    : Con _ _
  l l₁ l₂              : Termˡ _
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
-- Syntactic term equality for various kinds of terms.

-- Are the two grade terms syntactically equal?

infix 4 _≟ᵍ_

_≟ᵍ_ : (t₁ t₂ : Termᵍ n) → Maybe (t₁ PE.≡ t₂)
var x ≟ᵍ var y =
  PE.cong var <$> dec⇒maybe (x ≟ⱽ y)
𝟘 ≟ᵍ 𝟘 =
  just PE.refl
𝟙 ≟ᵍ 𝟙 =
  just PE.refl
ω ≟ᵍ ω =
  just PE.refl
t₁₁ + t₁₂ ≟ᵍ t₂₁ + t₂₂ =
  PE.cong₂ _+_ <$> t₁₁ ≟ᵍ t₂₁ ⊛ t₁₂ ≟ᵍ t₂₂
t₁₁ · t₁₂ ≟ᵍ t₂₁ · t₂₂ =
  PE.cong₂ _·_ <$> t₁₁ ≟ᵍ t₂₁ ⊛ t₁₂ ≟ᵍ t₂₂
t₁₁ ∧ t₁₂ ≟ᵍ t₂₁ ∧ t₂₂ =
  PE.cong₂ _∧_ <$> t₁₁ ≟ᵍ t₂₁ ⊛ t₁₂ ≟ᵍ t₂₂
_ ≟ᵍ _ =
  nothing

-- Semantic equality of universe level terms.

[_]_≡ˡ_ : ∀ c → (_ _ : Termˡ (c .ls)) → Set a
[ c ] t₁ ≡ˡ t₂ = (γ : Contexts c) → ⟦ t₁ ⟧ˡ γ PE.≡ ⟦ t₂ ⟧ˡ γ

-- Are the two universe level terms semantically equal?
--
-- The implementation could presumably be more efficient, but the
-- terms are expected to be small.

infix 4 _≟ˡ_

_≟ˡ_ : (t₁ t₂ : Termˡ (c .ls)) → Maybe ([ c ] t₁ ≡ˡ t₂)
t₁ ≟ˡ t₂ =
  soundness t₁ t₂ <$> normalise t₁ ≟ˡⁿ normalise t₂
  where
  -- Normal forms.
  --
  -- Invariant: There is at most one list element for each variable,
  -- and later variables are larger.

  Termˡⁿ′ : Nat → Set
  Termˡⁿ′ n = List (Nat × Fin n)

  Termˡⁿ : Nat → Set
  Termˡⁿ n = Termˡⁿ′ n × Nat

  -- Semantics of normal forms.

  ⟦_⟧ˡⁿ″ : Nat × Fin (c .ls) → Contexts c → Universe-level
  ⟦ n , x ⟧ˡⁿ″ γ = n N.+ Vec.lookup (γ .levels) x

  ⟦_⟧ˡⁿ′ : Termˡⁿ′ (c .ls) → Contexts c → Universe-level
  ⟦ ns ⟧ˡⁿ′ γ = List.foldr U._⊔ᵘ_ 0 (List.map (flip ⟦_⟧ˡⁿ″ γ) ns)

  ⟦_⟧ˡⁿ : Termˡⁿ (c .ls) → Contexts c → Universe-level
  ⟦ ns , n ⟧ˡⁿ γ = ⟦ ns ⟧ˡⁿ′ γ U.⊔ᵘ n

  -- An equality test for normal forms.

  infix 4 _≟ˡⁿ_

  _≟ˡⁿ_ : (n₁ n₂ : Termˡⁿ n) → Maybe (n₁ PE.≡ n₂)
  n₁ ≟ˡⁿ n₂ =
    dec⇒maybe (Σ.≡-dec (List.≡-dec (Σ.≡-dec N._≟_ _≟ⱽ_)) N._≟_ n₁ n₂)

  -- Normal form operations.

  sucⁿ′ : Termˡⁿ′ n → Termˡⁿ′ n
  sucⁿ′ = List.map (Σ.map 1+ idᶠ)

  sucⁿ : Termˡⁿ n → Termˡⁿ n
  sucⁿ = Σ.map sucⁿ′ 1+

  mergeⁿ : (_ _ : List (Nat × Fin n)) → List (Nat × Fin n)
  mergeⁿ []                     ns                     = ns
  mergeⁿ ns                     []                     = ns
  mergeⁿ ns₁@((n₁ , x₁) ∷ ns₁′) ns₂@((n₂ , x₂) ∷ ns₂′)
    with mergeⁿ ns₁′ ns₂ | mergeⁿ ns₁′ ns₂′ | mergeⁿ ns₁  ns₂′
       | Fin.compare x₁ x₂
  … | ns | _  | _  | less _ _    = (n₁         , x₁) ∷ ns
  … | _  | ns | _  | equal _     = (n₁ U.⊔ᵘ n₂ , x₁) ∷ ns
  … | _  | _  | ns | greater _ _ = (n₂         , x₂) ∷ ns

  maxⁿ : Termˡⁿ n → Termˡⁿ n → Termˡⁿ n
  maxⁿ (ns₁ , n₁) (ns₂ , n₂) = mergeⁿ ns₁ ns₂ , n₁ U.⊔ᵘ n₂

  opaque

    -- The normal form operations have the intended semantics.

    sucⁿ-correct :
      (n : Termˡⁿ (c .ls)) (γ : Contexts c) →
      ⟦ sucⁿ n ⟧ˡⁿ γ PE.≡ 1+ (⟦ n ⟧ˡⁿ γ)
    sucⁿ-correct ([] , n) γ =
      1+ n           ≡˘⟨ PE.cong 1+ (N.⊔-identityʳ _) ⟩
      1+ (0 U.⊔ᵘ n)  ∎
    sucⁿ-correct ((n₁ , x) ∷ ns , n₂) γ =
      (⟦ 1+ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ sucⁿ′ ns ⟧ˡⁿ′ γ) U.⊔ᵘ 1+ n₂  ≡˘⟨ N.⊔-assoc (1+ _) (⟦ sucⁿ′ ns ⟧ˡⁿ′ γ) _ ⟩
      ⟦ 1+ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ sucⁿ (ns , n₂) ⟧ˡⁿ γ          ≡⟨ PE.cong (_ U.⊔ᵘ_) (sucⁿ-correct (ns , n₂) γ) ⟩
      ⟦ 1+ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ 1+ (⟦ ns , n₂ ⟧ˡⁿ γ)            ≡⟨ N.⊔-assoc (1+ _) (1+ (⟦ ns ⟧ˡⁿ′ γ)) (⟦ 1+ n₁ , _ ⟧ˡⁿ″ γ) ⟩
      (⟦ 1+ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ 1+ (⟦ ns ⟧ˡⁿ′ γ)) U.⊔ᵘ 1+ n₂   ∎

    mergeⁿ-correct :
      (ns₁ ns₂ : Termˡⁿ′ (c .ls)) (γ : Contexts c) →
      ⟦ mergeⁿ ns₁ ns₂ ⟧ˡⁿ′ γ PE.≡ ⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ
    mergeⁿ-correct [] ns₂ γ =
      ⟦ ns₂ ⟧ˡⁿ′ γ         ≡˘⟨ N.⊔-identityʳ _ ⟩
      0 U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ  ∎
    mergeⁿ-correct (_ ∷ _) [] γ =
      PE.refl
    mergeⁿ-correct ns₁@((n₁ , x₁) ∷ ns₁′) ns₂@((n₂ , x₂) ∷ ns₂′) γ
      with mergeⁿ ns₁′ ns₂  | mergeⁿ-correct ns₁′ ns₂  γ
         | mergeⁿ ns₁′ ns₂′ | mergeⁿ-correct ns₁′ ns₂′ γ
         | mergeⁿ ns₁  ns₂′ | mergeⁿ-correct ns₁  ns₂′ γ
         | Fin.compare x₁ x₂
    … | ns | eq | _ | _ | _ | _ | less _ _ =
      ⟦ n₁ , _ ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns ⟧ˡⁿ′ γ                        ≡⟨ PE.cong (_ U.⊔ᵘ_) eq ⟩
      ⟦ n₁ , _ ⟧ˡⁿ″ γ U.⊔ᵘ (⟦ ns₁′ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ)  ≡⟨ N.⊔-assoc (⟦ ns₂ ⟧ˡⁿ′ γ) _ _ ⟩
      ⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ                          ∎
    … | _ | _ | ns | eq | _ | _ | equal x =
      ⟦ n₁ U.⊔ᵘ n₂ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns ⟧ˡⁿ′ γ                         ≡⟨ PE.cong (_ U.⊔ᵘ_) eq ⟩

      ⟦ n₁ U.⊔ᵘ n₂ , x ⟧ˡⁿ″ γ U.⊔ᵘ (⟦ ns₁′ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ)  ≡⟨ PE.cong (U._⊔ᵘ (_ U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ)) (N.+-distribʳ-⊔ _ n₂ _) ⟩

      (⟦ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ n₂ , x ⟧ˡⁿ″ γ) U.⊔ᵘ
      (⟦ ns₁′ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ)                               ≡⟨ N.⊔-swap (⟦ ns₂′ ⟧ˡⁿ′ γ) ⟩

      (⟦ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns₁′ ⟧ˡⁿ′ γ) U.⊔ᵘ
      (⟦ n₂ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ)                             ∎
    … | _ | _ | _ | _ | ns | eq | greater _ _ =
      ⟦ n₂ , _ ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns ⟧ˡⁿ′ γ                        ≡⟨ PE.cong (_ U.⊔ᵘ_) eq ⟩
      ⟦ n₂ , _ ⟧ˡⁿ″ γ U.⊔ᵘ (⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ)  ≡⟨ N.⊔-assoc (⟦ ns₂′ ⟧ˡⁿ′ γ) _ _ ⟩
      (⟦ n₂ , _ ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns₁ ⟧ˡⁿ′ γ) U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ  ≡⟨ PE.cong (U._⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ) (N.⊔-comm (⟦ ns₁ ⟧ˡⁿ′ γ) _) ⟩
      (⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ n₂ , _ ⟧ˡⁿ″ γ) U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ  ≡˘⟨ N.⊔-assoc (⟦ ns₂′ ⟧ˡⁿ′ γ) _ _ ⟩
      ⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ                          ∎

    maxⁿ-correct :
      (n₁ n₂ : Termˡⁿ (c .ls)) (γ : Contexts c) →
      ⟦ maxⁿ n₁ n₂ ⟧ˡⁿ γ PE.≡ ⟦ n₁ ⟧ˡⁿ γ U.⊔ᵘ ⟦ n₂ ⟧ˡⁿ γ
    maxⁿ-correct (ns₁ , n₁) (ns₂ , n₂) γ =
      ⟦ mergeⁿ ns₁ ns₂ ⟧ˡⁿ′ γ U.⊔ᵘ (n₁ U.⊔ᵘ n₂)           ≡⟨ PE.cong (U._⊔ᵘ _) (mergeⁿ-correct ns₁ ns₂ γ) ⟩
      (⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ) U.⊔ᵘ (n₁ U.⊔ᵘ n₂)  ≡⟨ N.⊔-swap n₂ ⟩
      (⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ n₁) U.⊔ᵘ (⟦ ns₂ ⟧ˡⁿ′ γ U.⊔ᵘ n₂)  ∎

  -- Normalisation.

  normalise : Termˡ n → Termˡⁿ n
  normalise (var x)    = (0 , x) ∷ [] , 0
  normalise zero       = [] , 0
  normalise (suc t)    = sucⁿ (normalise t)
  normalise (t₁ ⊔ᵘ t₂) = maxⁿ (normalise t₁) (normalise t₂)

  opaque

    -- Normalisation produces terms with the same semantics.

    normalise-correct :
      (t : Termˡ (c .ls)) (γ : Contexts c) →
      ⟦ normalise t ⟧ˡⁿ γ PE.≡ ⟦ t ⟧ˡ γ
    normalise-correct (var _) _ =
      PE.refl
    normalise-correct zero _ =
      PE.refl
    normalise-correct (suc t) γ =
      ⟦ sucⁿ (normalise t) ⟧ˡⁿ γ  ≡⟨ sucⁿ-correct (normalise t) γ ⟩
      1+ (⟦ normalise t ⟧ˡⁿ γ)    ≡⟨ PE.cong 1+ (normalise-correct t _) ⟩
      1+ (⟦ t ⟧ˡ γ)               ∎
    normalise-correct (t₁ ⊔ᵘ t₂) γ =
      ⟦ maxⁿ (normalise t₁) (normalise t₂) ⟧ˡⁿ γ      ≡⟨ maxⁿ-correct (normalise t₁) (normalise t₂) γ ⟩
      ⟦ normalise t₁ ⟧ˡⁿ γ U.⊔ᵘ ⟦ normalise t₂ ⟧ˡⁿ γ  ≡⟨ PE.cong₂ U._⊔ᵘ_ (normalise-correct t₁ _) (normalise-correct t₂ _) ⟩
      ⟦ t₁ ⟧ˡ γ U.⊔ᵘ ⟦ t₂ ⟧ˡ γ                        ∎

  opaque

    -- Equal normal forms have the same semantics.

    soundness :
      (t₁ t₂ : Termˡ (c .ls)) →
      normalise t₁ PE.≡ normalise t₂ →
      [ c ] t₁ ≡ˡ t₂
    soundness t₁ t₂ eq γ =
      ⟦ t₁ ⟧ˡ γ             ≡˘⟨ normalise-correct t₁ γ ⟩
      ⟦ normalise t₁ ⟧ˡⁿ γ  ≡⟨ PE.cong (flip ⟦_⟧ˡⁿ γ) eq ⟩
      ⟦ normalise t₂ ⟧ˡⁿ γ  ≡⟨ normalise-correct t₂ γ ⟩
      ⟦ t₂ ⟧ˡ γ             ∎

-- Are the two strength terms syntactically equal?

infix 4 _≟ˢ_

_≟ˢ_ : (t₁ t₂ : Termˢ n) → Maybe (t₁ PE.≡ t₂)
var x ≟ˢ var y =
  PE.cong var <$> dec⇒maybe (x ≟ⱽ y)
𝕤 ≟ˢ 𝕤 =
  just PE.refl
𝕨 ≟ˢ 𝕨 =
  just PE.refl
_ ≟ˢ _ =
  nothing

-- Are the two binder mode terms syntactically equal?

infix 4 _≟ᵇᵐ_

_≟ᵇᵐ_ : (t₁ t₂ : Termᵇᵐ m n) → Maybe (t₁ PE.≡ t₂)
var x ≟ᵇᵐ var y =
  PE.cong var <$> dec⇒maybe (x ≟ⱽ y)
BMΠ ≟ᵇᵐ BMΠ =
  just PE.refl
BMΣ s₁ ≟ᵇᵐ BMΣ s₂ =
  PE.cong BMΣ <$> s₁ ≟ˢ s₂
_ ≟ᵇᵐ _ =
  nothing

------------------------------------------------------------------------
-- A simple test involving binder modes

-- The binder mode is a literal binder mode (BMΠ, BMΣ 𝕤 or BMΣ 𝕨).

data Is-literal-binder-mode {m n} : Termᵇᵐ m n → Set a where
  BMΠ   : Is-literal-binder-mode BMΠ
  BMΣ-𝕤 : Is-literal-binder-mode (BMΣ 𝕤)
  BMΣ-𝕨 : Is-literal-binder-mode (BMΣ 𝕨)

-- Is the binder mode a literal binder mode?

is-literal-binder-mode? :
  (b : Termᵇᵐ m n) → Maybe (Is-literal-binder-mode b)
is-literal-binder-mode? BMΠ     = just BMΠ
is-literal-binder-mode? (BMΣ 𝕤) = just BMΣ-𝕤
is-literal-binder-mode? (BMΣ 𝕨) = just BMΣ-𝕨
is-literal-binder-mode? _       = nothing

------------------------------------------------------------------------
-- Checkable and inferable terms

-- The term's outermost constructor indicates that its type should be
-- checked rather than inferred.

data Checkable {c : Constants} {n} : Term c n → Set a where
  lam  : ∀ p t → Checkable (lam p nothing t)
  prod : ∀ s p t₁ t₂ → Checkable (prod s p nothing t₁ t₂)
  rfl  : Checkable (rfl nothing)

-- Does the term's outermost constructor indicate that its type should
-- be checked rather than inferred?

checkable? : (t : Term c n) → Maybe (Checkable t)
checkable? (lam _ nothing _)      = just (lam _ _)
checkable? (prod _ _ nothing _ _) = just (prod _ _ _ _)
checkable? (rfl nothing)          = just rfl
checkable? _                      = nothing

-- The term's outermost constructor indicates that its type might be
-- inferable.

data Inferable {c : Constants} {n} : Term c n → Set a where
  meta-var : ∀ x (σ : Subst c n n′) → Inferable (meta-var x σ)
  var      : ∀ x → Inferable (var x)
  defn     : ∀ α → Inferable (defn α)
  U        : ∀ l → Inferable (U l)
  Unit     : ∀ s l → Inferable (Unit s l)
  star     : ∀ s l → Inferable (star s l)
  unitrec  : ∀ l A t₁ t₂ → Inferable (unitrec l p q A t₁ t₂)
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
  []-cong  : ∀ s A t₁ t₂ t₃ → Inferable ([]-cong s A t₁ t₂ t₃)

-- A procedure that checks that the term's outermost constructor
-- indicates that its type might be inferable.

inferable : (t : Term c n) → Check c (Inferable t)
inferable (meta-var _ _)          = return (meta-var _ _)
inferable (var _)                 = return (var _)
inferable (defn _)                = return (defn _)
inferable (U _)                   = return (U _)
inferable (Unit _ _)              = return (Unit _ _)
inferable (star _ _)              = return (star _ _)
inferable (unitrec _ _ _ _ _ _)   = return (unitrec _ _ _ _)
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
inferable ([]-cong _ _ _ _ _)     = return ([]-cong _ _ _ _ _)
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
  emptyrec : ∀ A₁ t₁ A₂ t₂ → t PE.≡ emptyrec p A₁ t₁ →
             Are-equal-eliminators t (emptyrec p A₂ t₂)
  unitrec  : ∀ l₁ A₁ t₁₁ t₁₂ A₂ t₂₁ t₂₂ → [ c ] l₁ ≡ˡ l₂ →
             t PE.≡ unitrec l₁ p q A₁ t₁₁ t₁₂ →
             Are-equal-eliminators t (unitrec l₂ p q A₂ t₂₁ t₂₂)
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
  []-cong  : ∀ s A₁ t₁₁ t₁₂ t₁₃ A₂ t₂₁ t₂₂ t₂₃ →
             t PE.≡ []-cong s A₁ t₁₁ t₁₂ t₁₃ →
             Are-equal-eliminators t ([]-cong s A₂ t₂₁ t₂₂ t₂₃)

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
  are-equal-eliminators? (emptyrec p₁ _ _) (emptyrec p₂ _ _) =
    (λ eq → emptyrec _ _ _ _ (PE.cong (λ p → emptyrec p _ _) eq)) <$>
    p₁ ≟ᵍ p₂
  are-equal-eliminators?
    (unitrec l₁ p₁ q₁ _ _ _) (unitrec l₂ p₂ q₂ _ _ _) =
    (λ eq₁ eq₂ eq₃ →
       unitrec _ _ _ _ _ _ _ eq₁
         (PE.cong₂ (λ p q → unitrec _ p q _ _ _) eq₂ eq₃)) <$>
    l₁ ≟ˡ l₂ ⊛ p₁ ≟ᵍ p₂ ⊛ q₁ ≟ᵍ q₂
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
  are-equal-eliminators? ([]-cong s₁ _ _ _ _) ([]-cong s₂ _ _ _ _) =
    (λ eq →
       []-cong _ _ _ _ _ _ _ _ _
         (PE.cong (λ s → []-cong s _ _ _ _) eq)) <$>
    s₁ ≟ˢ s₂
  are-equal-eliminators? _ _ =
    nothing

------------------------------------------------------------------------
-- Type constructors

-- The term is a type constructor application (or a meta-variable).

data Is-type-constructor {c : Constants} {n} : Term c n → Set a where
  meta-var : ∀ x (σ : Subst c n n′) →
             Is-type-constructor (meta-var x σ)
  U        : ∀ l → Is-type-constructor (U l)
  Empty    : Is-type-constructor Empty
  Unit     : ∀ s l → Is-type-constructor (Unit s l)
  ΠΣ       : ∀ b p q A₁ A₂ →
             Is-type-constructor (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
  ℕ        : Is-type-constructor ℕ
  Id       : ∀ A t₁ t₂ → Is-type-constructor (Id A t₁ t₂)

-- Is the term a type constructor application (or a meta-variable)?

is-type-constructor? : (A : Term c n) → Maybe (Is-type-constructor A)
is-type-constructor? (meta-var _ _) =
  just (meta-var _ _)
is-type-constructor? (U _) =
  just (U _)
is-type-constructor? Empty =
  just Empty
is-type-constructor? (Unit _ _) =
  just (Unit _ _)
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
  U        : ∀ l → Is-type-constructorˡ (U l)
  Empty    : Is-type-constructorˡ Empty
  Unit     : ∀ s l → Is-type-constructorˡ (Unit s l)
  ΠΣ       : Is-literal-binder-mode b →
             ∀ p q A₁ A₂ →
             Is-type-constructorˡ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ A₂)
  ℕ        : Is-type-constructorˡ ℕ
  Id       : ∀ A t₁ t₂ → Is-type-constructorˡ (Id A t₁ t₂)

-- Does Is-type-constructorˡ hold for the given term?

is-type-constructorˡ? : (A : Term c n) → Maybe (Is-type-constructorˡ A)
is-type-constructorˡ? (meta-var _ _) =
  just (meta-var _ _)
is-type-constructorˡ? (U _) =
  just (U _)
is-type-constructorˡ? Empty =
  just Empty
is-type-constructorˡ? (Unit _ _) =
  just (Unit _ _)
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
  U        : [ c ] l₁ ≡ˡ l₂ → A PE.≡ U l₁ →
             Are-equal-type-constructors A (U l₂)
  Empty    : A PE.≡ Empty → Are-equal-type-constructors A Empty
  Unit     : [ c ] l₁ ≡ˡ l₂ → A PE.≡ Unit s l₁ →
             Are-equal-type-constructors A (Unit s l₂)
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
are-equal-type-constructors? (U l₁) (U l₂) =
  (λ eq → U eq PE.refl) <$> l₁ ≟ˡ l₂
are-equal-type-constructors? Empty Empty =
  just (Empty PE.refl)
are-equal-type-constructors? (Unit s₁ l₁) (Unit s₂ l₂) =
  (λ eq₁ eq₂ → Unit eq₂ (PE.cong (λ s → Unit s _) eq₁)) <$>
  s₁ ≟ˢ s₂ ⊛ l₁ ≟ˡ l₂
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

-- A procedure that checks that the two meta-variables are equal.

are-equal-meta-vars : (x₁ x₂ : Meta-var c n) → Check c (x₁ PE.≡ x₂)
are-equal-meta-vars (var x₁ eq₁) (var x₂ eq₂) =
  (λ { PE.refl → PE.cong (var _) N.Nat-set }) M.<$>
  [ dec⇒maybe (x₁ ≟ⱽ x₂) ]with-message "Expected equal meta-variables."

-- A procedure that checks that the level is the level zero.

is-zero : (l : Termˡ n) → Check c (l PE.≡ zero)
is-zero zero = return PE.refl
is-zero _    = fail "Expected the level zero."

-- A procedure that checks that the term is an application of U.

is-U : (A : Term c n) → Check c (∃ λ l → A PE.≡ U l)
is-U (U _) = return (_ , PE.refl)
is-U _     = fail "Expected an instance of U."

-- A procedure that checks that the term is U l.

is-U[_] :
  (l : Termˡ (c .ls)) (A : Term c n) →
  Check c (∃ λ l′ → [ c ] l ≡ˡ l′ × A PE.≡ U l′)
is-U[_] {c} l A =
  [ is-U′ A ]with-message "Expected a given instance of U."
  where
  is-U′ : (A : Term c n) → Maybe (∃ λ l′ → [ c ] l ≡ˡ l′ × A PE.≡ U l′)
  is-U′ (U l′) = (λ eq → _ , eq , PE.refl) <$> l ≟ˡ l′
  is-U′ _      = nothing

-- Is the term equal to star s l?

is-star? :
  ∀ s l (t : Term c n) →
  Maybe (∃ λ l′ → [ c ] l ≡ˡ l′ × t PE.≡ star s l′)
is-star? s l (star s′ l′) =
  (λ eq₁ eq₂ → _ , eq₂ , PE.cong (λ s → star s _) eq₁) <$>
  s′ ≟ˢ s ⊛ l ≟ˡ l′
is-star? _ _ _ = nothing

-- Are the terms both equal to star s l?

are-star? :
  ∀ s l (t₁ t₂ : Term c n) →
  Maybe
    (∃₂ λ l₁ l₂ → [ c ] l ≡ˡ l₁ × [ c ] l ≡ˡ l₂ ×
     t₁ PE.≡ star s l₁ × t₂ PE.≡ star s l₂)
are-star? s l (star s₁ l₁) (star s₂ l₂) =
  (λ eq₁ eq₂ eq₃ eq₄ →
     _ , _ , eq₃ , eq₄ ,
     PE.cong (λ s → star s _) eq₁ , PE.cong (λ s → star s _) eq₂) <$>
  s₁ ≟ˢ s ⊛ s₂ ≟ˢ s ⊛ l ≟ˡ l₁ ⊛ l ≟ˡ l₂
are-star? _ _ _ _ =
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

-- Are the terms both applications of prod 𝕨 p?

are-prodʷ? :
  ∀ p (t₁ t₂ : Term c n) →
  Maybe
    (∃₆ λ qA₂₁ t₁₁ t₂₁ qA₂₂ t₁₂ t₂₂ →
     t₁ PE.≡ prod 𝕨 p qA₂₁ t₁₁ t₂₁ × t₂ PE.≡ prod 𝕨 p qA₂₂ t₁₂ t₂₂)
are-prodʷ? p (prod 𝕨 p₁ _ _ _) (prod 𝕨 p₂ _ _ _) =
  (λ eq₁ eq₂ →
     _ , _ , _ , _ , _ , _ ,
     (case eq₁ of λ {
        PE.refl →
      case eq₂ of λ {
        PE.refl →
      PE.refl , PE.refl }})) <$>
  p ≟ᵍ p₁ ⊛ p ≟ᵍ p₂
are-prodʷ? _ _ _ =
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
