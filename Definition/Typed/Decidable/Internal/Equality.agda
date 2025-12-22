------------------------------------------------------------------------
-- Term equality tests used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Graded.Modality

module Definition.Typed.Decidable.Internal.Equality
  {a} {M : Set a}
  (𝕄 : Modality M)
  where

open import Definition.Typed.Decidable.Internal.Term 𝕄

open import Definition.Untyped M as U using (Universe-level)

open import Tools.Fin as Fin
open import Tools.Function
open import Tools.List as List
open import Tools.Maybe
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality
import Tools.Vec as Vec

private variable
  m n : Nat
  c   : Constants

-- Are the two grade terms syntactically equal?

infix 4 _≟ᵍ_

_≟ᵍ_ : (t₁ t₂ : Termᵍ n) → Maybe (t₁ ≡ t₂)
var x ≟ᵍ var y =
  cong var <$> dec⇒maybe (x ≟ⱽ y)
𝟘 ≟ᵍ 𝟘 =
  just refl
𝟙 ≟ᵍ 𝟙 =
  just refl
ω ≟ᵍ ω =
  just refl
t₁₁ + t₁₂ ≟ᵍ t₂₁ + t₂₂ =
  cong₂ _+_ <$> t₁₁ ≟ᵍ t₂₁ ⊛ t₁₂ ≟ᵍ t₂₂
t₁₁ · t₁₂ ≟ᵍ t₂₁ · t₂₂ =
  cong₂ _·_ <$> t₁₁ ≟ᵍ t₂₁ ⊛ t₁₂ ≟ᵍ t₂₂
t₁₁ ∧ t₁₂ ≟ᵍ t₂₁ ∧ t₂₂ =
  cong₂ _∧_ <$> t₁₁ ≟ᵍ t₂₁ ⊛ t₁₂ ≟ᵍ t₂₂
⌜⌞ t₁ ⌟⌝ ≟ᵍ ⌜⌞ t₂ ⌟⌝ =
  cong ⌜⌞_⌟⌝ <$> t₁ ≟ᵍ t₂
_ ≟ᵍ _ =
  nothing

-- Semantic equality of universe level terms.

[_]_≡ˡ_ : ∀ c → (_ _ : Termˡ (c .ls)) → Set a
[ c ] t₁ ≡ˡ t₂ = (γ : Contexts c) → ⟦ t₁ ⟧ˡ γ ≡ ⟦ t₂ ⟧ˡ γ

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

  _≟ˡⁿ_ : (n₁ n₂ : Termˡⁿ n) → Maybe (n₁ ≡ n₂)
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
      ⟦ sucⁿ n ⟧ˡⁿ γ ≡ 1+ (⟦ n ⟧ˡⁿ γ)
    sucⁿ-correct ([] , n) γ =
      1+ n           ≡˘⟨ cong 1+ (N.⊔-identityʳ _) ⟩
      1+ (0 U.⊔ᵘ n)  ∎
    sucⁿ-correct ((n₁ , x) ∷ ns , n₂) γ =
      (⟦ 1+ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ sucⁿ′ ns ⟧ˡⁿ′ γ) U.⊔ᵘ 1+ n₂  ≡˘⟨ N.⊔-assoc (1+ _) (⟦ sucⁿ′ ns ⟧ˡⁿ′ γ) _ ⟩
      ⟦ 1+ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ sucⁿ (ns , n₂) ⟧ˡⁿ γ          ≡⟨ cong (_ U.⊔ᵘ_) (sucⁿ-correct (ns , n₂) γ) ⟩
      ⟦ 1+ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ 1+ (⟦ ns , n₂ ⟧ˡⁿ γ)            ≡⟨ N.⊔-assoc (1+ _) (1+ (⟦ ns ⟧ˡⁿ′ γ)) (⟦ 1+ n₁ , _ ⟧ˡⁿ″ γ) ⟩
      (⟦ 1+ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ 1+ (⟦ ns ⟧ˡⁿ′ γ)) U.⊔ᵘ 1+ n₂   ∎

    mergeⁿ-correct :
      (ns₁ ns₂ : Termˡⁿ′ (c .ls)) (γ : Contexts c) →
      ⟦ mergeⁿ ns₁ ns₂ ⟧ˡⁿ′ γ ≡ ⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ
    mergeⁿ-correct [] ns₂ γ =
      ⟦ ns₂ ⟧ˡⁿ′ γ         ≡˘⟨ N.⊔-identityʳ _ ⟩
      0 U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ  ∎
    mergeⁿ-correct (_ ∷ _) [] γ =
      refl
    mergeⁿ-correct ns₁@((n₁ , x₁) ∷ ns₁′) ns₂@((n₂ , x₂) ∷ ns₂′) γ
      with mergeⁿ ns₁′ ns₂  | mergeⁿ-correct ns₁′ ns₂  γ
         | mergeⁿ ns₁′ ns₂′ | mergeⁿ-correct ns₁′ ns₂′ γ
         | mergeⁿ ns₁  ns₂′ | mergeⁿ-correct ns₁  ns₂′ γ
         | Fin.compare x₁ x₂
    … | ns | eq | _ | _ | _ | _ | less _ _ =
      ⟦ n₁ , _ ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns ⟧ˡⁿ′ γ                        ≡⟨ cong (_ U.⊔ᵘ_) eq ⟩
      ⟦ n₁ , _ ⟧ˡⁿ″ γ U.⊔ᵘ (⟦ ns₁′ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ)  ≡⟨ N.⊔-assoc (⟦ ns₂ ⟧ˡⁿ′ γ) _ _ ⟩
      ⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ                          ∎
    … | _ | _ | ns | eq | _ | _ | equal x =
      ⟦ n₁ U.⊔ᵘ n₂ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns ⟧ˡⁿ′ γ                         ≡⟨ cong (_ U.⊔ᵘ_) eq ⟩

      ⟦ n₁ U.⊔ᵘ n₂ , x ⟧ˡⁿ″ γ U.⊔ᵘ (⟦ ns₁′ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ)  ≡⟨ cong (U._⊔ᵘ (_ U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ)) (N.+-distribʳ-⊔ _ n₂ _) ⟩

      (⟦ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ n₂ , x ⟧ˡⁿ″ γ) U.⊔ᵘ
      (⟦ ns₁′ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ)                               ≡⟨ N.⊔-swap (⟦ ns₂′ ⟧ˡⁿ′ γ) ⟩

      (⟦ n₁ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns₁′ ⟧ˡⁿ′ γ) U.⊔ᵘ
      (⟦ n₂ , x ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ)                             ∎
    … | _ | _ | _ | _ | ns | eq | greater _ _ =
      ⟦ n₂ , _ ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns ⟧ˡⁿ′ γ                        ≡⟨ cong (_ U.⊔ᵘ_) eq ⟩
      ⟦ n₂ , _ ⟧ˡⁿ″ γ U.⊔ᵘ (⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ)  ≡⟨ N.⊔-assoc (⟦ ns₂′ ⟧ˡⁿ′ γ) _ _ ⟩
      (⟦ n₂ , _ ⟧ˡⁿ″ γ U.⊔ᵘ ⟦ ns₁ ⟧ˡⁿ′ γ) U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ  ≡⟨ cong (U._⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ) (N.⊔-comm (⟦ ns₁ ⟧ˡⁿ′ γ) _) ⟩
      (⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ n₂ , _ ⟧ˡⁿ″ γ) U.⊔ᵘ ⟦ ns₂′ ⟧ˡⁿ′ γ  ≡˘⟨ N.⊔-assoc (⟦ ns₂′ ⟧ˡⁿ′ γ) _ _ ⟩
      ⟦ ns₁ ⟧ˡⁿ′ γ U.⊔ᵘ ⟦ ns₂ ⟧ˡⁿ′ γ                          ∎

    maxⁿ-correct :
      (n₁ n₂ : Termˡⁿ (c .ls)) (γ : Contexts c) →
      ⟦ maxⁿ n₁ n₂ ⟧ˡⁿ γ ≡ ⟦ n₁ ⟧ˡⁿ γ U.⊔ᵘ ⟦ n₂ ⟧ˡⁿ γ
    maxⁿ-correct (ns₁ , n₁) (ns₂ , n₂) γ =
      ⟦ mergeⁿ ns₁ ns₂ ⟧ˡⁿ′ γ U.⊔ᵘ (n₁ U.⊔ᵘ n₂)           ≡⟨ cong (U._⊔ᵘ _) (mergeⁿ-correct ns₁ ns₂ γ) ⟩
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
      ⟦ normalise t ⟧ˡⁿ γ ≡ ⟦ t ⟧ˡ γ
    normalise-correct (var _) _ =
      refl
    normalise-correct zero _ =
      refl
    normalise-correct (suc t) γ =
      ⟦ sucⁿ (normalise t) ⟧ˡⁿ γ  ≡⟨ sucⁿ-correct (normalise t) γ ⟩
      1+ (⟦ normalise t ⟧ˡⁿ γ)    ≡⟨ cong 1+ (normalise-correct t _) ⟩
      1+ (⟦ t ⟧ˡ γ)               ∎
    normalise-correct (t₁ ⊔ᵘ t₂) γ =
      ⟦ maxⁿ (normalise t₁) (normalise t₂) ⟧ˡⁿ γ      ≡⟨ maxⁿ-correct (normalise t₁) (normalise t₂) γ ⟩
      ⟦ normalise t₁ ⟧ˡⁿ γ U.⊔ᵘ ⟦ normalise t₂ ⟧ˡⁿ γ  ≡⟨ cong₂ U._⊔ᵘ_ (normalise-correct t₁ _) (normalise-correct t₂ _) ⟩
      ⟦ t₁ ⟧ˡ γ U.⊔ᵘ ⟦ t₂ ⟧ˡ γ                        ∎

  opaque

    -- Equal normal forms have the same semantics.

    soundness :
      (t₁ t₂ : Termˡ (c .ls)) →
      normalise t₁ ≡ normalise t₂ →
      [ c ] t₁ ≡ˡ t₂
    soundness t₁ t₂ eq γ =
      ⟦ t₁ ⟧ˡ γ             ≡˘⟨ normalise-correct t₁ γ ⟩
      ⟦ normalise t₁ ⟧ˡⁿ γ  ≡⟨ cong (flip ⟦_⟧ˡⁿ γ) eq ⟩
      ⟦ normalise t₂ ⟧ˡⁿ γ  ≡⟨ normalise-correct t₂ γ ⟩
      ⟦ t₂ ⟧ˡ γ             ∎

-- Are the two strength terms syntactically equal?

infix 4 _≟ˢ_

_≟ˢ_ : (t₁ t₂ : Termˢ n) → Maybe (t₁ ≡ t₂)
var x ≟ˢ var y =
  cong var <$> dec⇒maybe (x ≟ⱽ y)
𝕤 ≟ˢ 𝕤 =
  just refl
𝕨 ≟ˢ 𝕨 =
  just refl
_ ≟ˢ _ =
  nothing

-- Are the two binder mode terms syntactically equal?

infix 4 _≟ᵇᵐ_

_≟ᵇᵐ_ : (t₁ t₂ : Termᵇᵐ m n) → Maybe (t₁ ≡ t₂)
var x ≟ᵇᵐ var y =
  cong var <$> dec⇒maybe (x ≟ⱽ y)
BMΠ ≟ᵇᵐ BMΠ =
  just refl
BMΣ s₁ ≟ᵇᵐ BMΣ s₂ =
  cong BMΣ <$> s₁ ≟ˢ s₂
_ ≟ᵇᵐ _ =
  nothing
