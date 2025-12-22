------------------------------------------------------------------------
-- Constraints used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal.Constraint
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR

open import Definition.Typed.Decidable.Internal.Equality 𝕄
open import Definition.Typed.Decidable.Internal.Term 𝕄
open import Definition.Typed.Variant

open import Tools.Function
open import Tools.Level
open import Tools.List
open import Tools.Maybe
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Sum
open import Tools.Unit

private variable
  A          : Set _
  Cs Cs₁ Cs₂ : A
  c          : Constants
  γ          : Contexts _

------------------------------------------------------------------------
-- Single constraints

-- Constraints that can be returned by the type-checker and other
-- functions.

data Constraint (c : Constants) : Set a where
  k-allowed opacity-allowed unfolding-mode-transitive :
    Constraint c
  box-cong-allowed unit-allowed unit-with-η :
    (s : Termˢ (c .ss)) → Constraint c
  πσ-allowed :
    (b : Termᵇᵐ (c .ss) (c .bms)) (p q : Termᵍ (c .gs)) → Constraint c

private variable
  C C′ : Constraint _

-- The semantics of a single constraint.

⟦_⟧₁ : Constraint c → Contexts c → Set a
⟦ k-allowed                 ⟧₁ _ = K-allowed
⟦ opacity-allowed           ⟧₁ _ = Opacity-allowed
⟦ unfolding-mode-transitive ⟧₁ _ = Lift _ (unfolding-mode ≡ transitive)
⟦ box-cong-allowed s        ⟧₁ γ = []-cong-allowed (⟦ s ⟧ˢ γ)
⟦ unit-allowed s            ⟧₁ γ = Unit-allowed (⟦ s ⟧ˢ γ)
⟦ unit-with-η s             ⟧₁ γ = Lift _ (Unit-with-η (⟦ s ⟧ˢ γ))
⟦ πσ-allowed b p q          ⟧₁ γ =
  ΠΣ-allowed (⟦ b ⟧ᵇᵐ γ) (⟦ p ⟧ᵍ γ) (⟦ q ⟧ᵍ γ)

-- An equality test for constraints.

infix 4 _≟ᶜ_

_≟ᶜ_ : (C₁ C₂ : Constraint c) → Maybe (C₁ ≡ C₂)
k-allowed ≟ᶜ k-allowed =
  just refl
opacity-allowed ≟ᶜ opacity-allowed =
  just refl
unfolding-mode-transitive ≟ᶜ unfolding-mode-transitive =
  just refl
box-cong-allowed s₁ ≟ᶜ box-cong-allowed s₂ =
  cong box-cong-allowed <$> s₁ ≟ˢ s₂
unit-allowed s₁ ≟ᶜ unit-allowed s₂ =
  cong unit-allowed <$> s₁ ≟ˢ s₂
unit-with-η s₁ ≟ᶜ unit-with-η s₂ =
  cong unit-with-η <$> s₁ ≟ˢ s₂
πσ-allowed b₁ p₁ q₁ ≟ᶜ πσ-allowed b₂ p₂ q₂ =
  cong₃ πσ-allowed <$> b₁ ≟ᵇᵐ b₂ ⊛ p₁ ≟ᵍ p₂ ⊛ q₁ ≟ᵍ q₂
_ ≟ᶜ _ =
  nothing

------------------------------------------------------------------------
-- Collections of constraints

-- Collections of constraints.

infixr 5 _∪_

data Constraints (c : Constants) : Set a where
  none : Constraints c
  con  : Constraint c → Constraints c
  _∪_  : (Cs₁ Cs₂ : Constraints c) → Constraints c

-- A semantics of a collection of constraints.

⟦_⟧′ : Constraints c → Contexts c → Set a
⟦ none      ⟧′ _ = Lift _ ⊤
⟦ con C     ⟧′ γ = ⟦ C ⟧₁ γ
⟦ Cs₁ ∪ Cs₂ ⟧′ γ = ⟦ Cs₁ ⟧′ γ × ⟦ Cs₂ ⟧′ γ

-- A smart constructor.

infixr 5 _∪′_

_∪′_ : Constraints c → Constraints c → Constraints c
Cs   ∪′ none = Cs
none ∪′ Cs   = Cs
Cs₁  ∪′ Cs₂  = Cs₁ ∪ Cs₂

-- Membership in a collection of constraints.

infix 4 _∈ᶜ_

data _∈ᶜ_ : Constraint c → Constraints c → Set a where
  here  : C ∈ᶜ con C
  left  : C ∈ᶜ Cs₁ → C ∈ᶜ Cs₁ ∪ Cs₂
  right : C ∈ᶜ Cs₂ → C ∈ᶜ Cs₁ ∪ Cs₂

opaque

  -- A characterisation of ⟦_⟧′.

  ⟦⟧′⇔ : ⟦ Cs ⟧′ γ ⇔ (∀ C → C ∈ᶜ Cs → ⟦ C ⟧₁ γ)
  ⟦⟧′⇔ {Cs = none} {γ} =
    Lift _ ⊤                      ⇔⟨ (λ _ _ ()) , _ ⟩
    (∀ C → C ∈ᶜ none → ⟦ C ⟧₁ γ)  □⇔
  ⟦⟧′⇔ {Cs = con C} {γ} =
    ⟦ C ⟧₁ γ                          ⇔⟨ (λ { c _ here → c })
                                       , (λ hyp → hyp _ here)
                                       ⟩
    (∀ C′ → C′ ∈ᶜ con C → ⟦ C′ ⟧₁ γ)  □⇔
  ⟦⟧′⇔ {Cs = Cs₁ ∪ Cs₂} {γ} =
    ⟦ Cs₁ ⟧′ γ × ⟦ Cs₂ ⟧′ γ                                    ⇔⟨ ⟦⟧′⇔ ×-cong-⇔ ⟦⟧′⇔ ⟩
    (∀ C → C ∈ᶜ Cs₁ → ⟦ C ⟧₁ γ) × (∀ C → C ∈ᶜ Cs₂ → ⟦ C ⟧₁ γ)  ⇔⟨ (λ { (hyp , _)   _ (left  C′∈) → hyp _ C′∈
                                                                     ; (_   , hyp) _ (right C′∈) → hyp _ C′∈
                                                                     })
                                                                , (λ hyp → (λ _ C∈ → hyp _ (left C∈)) , (λ _ C∈ → hyp _ (right C∈)))
                                                                ⟩
    (∀ C′ → C′ ∈ᶜ Cs₁ ∪ Cs₂ → ⟦ C′ ⟧₁ γ)                       □⇔

------------------------------------------------------------------------
-- An alternative semantics for collections of constraints

-- A semantics of a list of constraints.

⟦_⟧ₗ : List (Constraint c) → Contexts c → Set a
⟦ []     ⟧ₗ _ = Lift _ ⊤
⟦ C ∷ [] ⟧ₗ γ = ⟦ C ⟧₁ γ
⟦ C ∷ Cs ⟧ₗ γ = ⟦ C ⟧₁ γ × ⟦ Cs ⟧ₗ γ

opaque

  -- A characterisation of ⟦_⟧ₗ.

  ⟦⟧ₗ⇔ : ⟦ Cs ⟧ₗ γ ⇔ (∀ C → C ∈ Cs → ⟦ C ⟧₁ γ)
  ⟦⟧ₗ⇔ {Cs = []} {γ} =
    Lift _ ⊤                   ⇔⟨ (λ _ _ ()) , _ ⟩
    (∀ C → C ∈ [] → ⟦ C ⟧₁ γ)  □⇔
  ⟦⟧ₗ⇔ {Cs = C ∷ []} {γ} =
    ⟦ C ⟧₁ γ                          ⇔⟨ (λ { c _ (here refl) → c; _ _ (there ()) })
                                       , (λ hyp → hyp _ (here refl))
                                       ⟩
    (∀ C′ → C′ ∈ C ∷ [] → ⟦ C′ ⟧₁ γ)  □⇔
  ⟦⟧ₗ⇔ {Cs = C ∷ Cs@(_ ∷ _)} {γ} =
    ⟦ C ⟧₁ γ × ⟦ Cs ⟧ₗ γ                     ⇔⟨ id⇔ ×-cong-⇔ ⟦⟧ₗ⇔ ⟩
    ⟦ C ⟧₁ γ × (∀ C′ → C′ ∈ Cs → ⟦ C′ ⟧₁ γ)  ⇔⟨ (λ { (c , _) _ (here refl) → c
                                                   ; (_ , hyp) _ (there C′∈) → hyp _ C′∈
                                                   })
                                              , (λ hyp → hyp _ (here refl) , (λ _ → hyp _ ∘→ there))
                                              ⟩
    (∀ C′ → C′ ∈ C ∷ Cs → ⟦ C′ ⟧₁ γ)         □⇔

opaque

  -- The function ⟦_⟧ₗ respects set equivalence.

  ⟦⟧ₗ-respects-set-equivalence :
    (∀ C → C ∈ Cs₁ ⇔ C ∈ Cs₂) →
    ⟦ Cs₁ ⟧ₗ γ ⇔ ⟦ Cs₂ ⟧ₗ γ
  ⟦⟧ₗ-respects-set-equivalence {Cs₁} {Cs₂} {γ} Cs₁∼Cs₂ =
    ⟦ Cs₁ ⟧ₗ γ                  ⇔⟨ ⟦⟧ₗ⇔ ⟩
    (∀ C → C ∈ Cs₁ → ⟦ C ⟧₁ γ)  ⇔⟨ (Π-cong-⇔ λ _ → Cs₁∼Cs₂ _ →-cong-⇔ id⇔) ⟩
    (∀ C → C ∈ Cs₂ → ⟦ C ⟧₁ γ)  ⇔˘⟨ ⟦⟧ₗ⇔ ⟩
    ⟦ Cs₂ ⟧ₗ γ                  □⇔

private

  -- Turns collections of constraints into lists of constraints.

  to-list′ : Constraints c → List (Constraint c) → List (Constraint c)
  to-list′ none        Cs  = Cs
  to-list′ (con C)     Cs  = C ∷ Cs
  to-list′ (Cs₁ ∪ Cs₂) Cs₃ = to-list′ Cs₁ (to-list′ Cs₂ Cs₃)

  opaque

    -- The function to-list′ does not add or remove any constraints.

    to-list′-correct : C ∈ to-list′ Cs₁ Cs₂ ⇔ (C ∈ᶜ Cs₁ ⊎ C ∈ Cs₂)
    to-list′-correct {C} {Cs₁ = none} {Cs₂} =
      C ∈ Cs₂              ⇔⟨ inj₂ , (λ { (inj₁ ()); (inj₂ C∈) → C∈ }) ⟩
      C ∈ᶜ none ⊎ C ∈ Cs₂  □⇔
    to-list′-correct {C} {Cs₁ = con C′} {Cs₂} =
      C ∈ C′ ∷ Cs₂           ⇔⟨ ∈∷⇔ ⟩
      C ≡ C′ ⊎ C ∈ Cs₂       ⇔⟨ ((λ { refl → here }) , (λ { here → refl })) ⊎-cong-⇔ id⇔ ⟩
      C ∈ᶜ con C′ ⊎ C ∈ Cs₂  □⇔
    to-list′-correct {C} {Cs₁ = Cs₁₁ ∪ Cs₁₂} {Cs₂} =
      C ∈ to-list′ Cs₁₁ (to-list′ Cs₁₂ Cs₂)  ⇔⟨ to-list′-correct ⟩
      C ∈ᶜ Cs₁₁ ⊎ C ∈ to-list′ Cs₁₂ Cs₂      ⇔⟨ id⇔ ⊎-cong-⇔ to-list′-correct ⟩
      C ∈ᶜ Cs₁₁ ⊎ (C ∈ᶜ Cs₁₂ ⊎ C ∈ Cs₂)      ⇔˘⟨ ⊎-assoc-⇔ ⟩
      (C ∈ᶜ Cs₁₁ ⊎ C ∈ᶜ Cs₁₂) ⊎ C ∈ Cs₂      ⇔⟨ ( (λ { (inj₁ C∈) → left C∈; (inj₂ C∈) → right C∈ })
                                                , (λ { (left C∈) → inj₁ C∈; (right C∈) → inj₂ C∈ })
                                                )
                                                  ⊎-cong-⇔
                                                id⇔ ⟩
      C ∈ᶜ Cs₁₁ ∪ Cs₁₂ ⊎ C ∈ Cs₂             □⇔

-- Turns collections of constraints into lists of constraints.

to-list : Constraints c → List (Constraint c)
to-list Cs = to-list′ Cs []

opaque

  -- The function to-list does not add or remove any constraints.

  to-list-correct : C ∈ to-list Cs ⇔ C ∈ᶜ Cs
  to-list-correct {C} {Cs} =
    C ∈ to-list Cs      ⇔⟨ id⇔ ⟩
    C ∈ to-list′ Cs []  ⇔⟨ to-list′-correct ⟩
    C ∈ᶜ Cs ⊎ C ∈ []    ⇔⟨ (λ { (inj₁ C∈) → C∈; (inj₂ ()) })
                         , inj₁
                         ⟩
    C ∈ᶜ Cs             □⇔

-- A list membership test for constraints.

member :
  (C : Constraint c) (Cs : List (Constraint c)) → Maybe (C ∈ Cs)
member _  []        = nothing
member C₁ (C₂ ∷ Cs) with C₁ ≟ᶜ C₂
… | just eq = just (here eq)
… | nothing = there <$> member C₁ Cs

-- Prepends the constraint to the list if it is not already a
-- member.

cons-if-not-member :
  Constraint c → List (Constraint c) → List (Constraint c)
cons-if-not-member C Cs with member C Cs
… | just _  = Cs
… | nothing = C ∷ Cs

opaque

  -- The function cons-if-not-member C does not add or remove any
  -- constraints, with the possible exception that C might be added.

  cons-if-not-member-correct :
    C′ ∈ cons-if-not-member C Cs ⇔ (C′ ≡ C ⊎ C′ ∈ Cs)
  cons-if-not-member-correct {C′} {C} {Cs} with member C Cs
  … | just C∈Cs =
    C′ ∈ Cs           ⇔⟨ inj₂ , (λ { (inj₁ refl) → C∈Cs; (inj₂ C′∈) → C′∈ }) ⟩
    C′ ≡ C ⊎ C′ ∈ Cs  □⇔
  … | nothing =
    C′ ∈ C ∷ Cs       ⇔⟨ ∈∷⇔ ⟩
    C′ ≡ C ⊎ C′ ∈ Cs  □⇔

-- Removes duplicates.
--
-- This implementation could be slow, but the number of distinct
-- constraints is expected to be low, in which case the time
-- complexity should be OK.
--
-- However, the current approach of first generating a possibly large
-- number of constraints and then letting the user show that they are
-- satisfied does not work very well in practice for even slightly
-- larger examples.
--
-- An attempted implementation of
-- Definition.Typed.Properties.Admissible.Vec.⊢⇒*∷-vecrec-β-cons using
-- the type-checker failed (on one setup) due to lack of memory. The
-- type-checker generated 4483 constraints, but most were duplicates:
-- there were three distinct constraints. A tree with 4483 elements
-- "ought" to be easy to handle, but presumably there is some kind of
-- space leak.
--
-- There is also the problem that if the constraint argument is left
-- as a goal to be solved using the auto command, then, when the file
-- is loaded, Agda prints the non-normalised goal type, which can be
-- rather large.

nub : List (Constraint c) → List (Constraint c)
nub []       = []
nub (C ∷ Cs) = cons-if-not-member C (nub Cs)

opaque

  -- The function nub returns a list that is set equivalent to its
  -- input.

  nub-correct : C ∈ nub Cs ⇔ C ∈ Cs
  nub-correct {Cs = []} =
    id⇔
  nub-correct {C} {Cs = C′ ∷ Cs} =
    C ∈ cons-if-not-member C′ (nub Cs)  ⇔⟨ cons-if-not-member-correct ⟩
    C ≡ C′ ⊎ C ∈ nub Cs                 ⇔⟨ id⇔ ⊎-cong-⇔ nub-correct ⟩
    C ≡ C′ ⊎ C ∈ Cs                     ⇔˘⟨ ∈∷⇔ ⟩
    C ∈ C′ ∷ Cs                         □⇔

-- A semantics of a collection of constraints.

⟦_⟧ : Constraints c → Contexts c → Set a
⟦ Cs ⟧ γ = ⟦ nub (to-list Cs) ⟧ₗ γ

opaque

  -- ⟦ Cs ⟧ γ is logically equivalent to ⟦ Cs ⟧′ γ.

  ⟦⟧⇔⟦⟧′ : ∀ Cs → ⟦ Cs ⟧ γ ⇔ ⟦ Cs ⟧′ γ
  ⟦⟧⇔⟦⟧′ {γ} Cs =
    ⟦ nub (to-list Cs) ⟧ₗ γ            ⇔⟨ ⟦⟧ₗ-respects-set-equivalence (λ _ → nub-correct {Cs = to-list Cs}) ⟩
    ⟦ to-list Cs ⟧ₗ γ                  ⇔⟨ ⟦⟧ₗ⇔ ⟩
    (∀ C → C ∈ to-list Cs → ⟦ C ⟧₁ γ)  ⇔⟨ (Π-cong-⇔ λ _ → to-list-correct →-cong-⇔ id⇔) ⟩
    (∀ C → C ∈ᶜ Cs        → ⟦ C ⟧₁ γ)  ⇔˘⟨ ⟦⟧′⇔ ⟩
    ⟦ Cs ⟧′ γ                          □⇔

opaque

  -- ⟦ Cs₁ ∪ Cs₂ ⟧ γ is logically equivalent to ⟦ Cs₁ ⟧ γ × ⟦ Cs₂ ⟧ γ.

  ⟦∪⟧⇔⟦⟧×⟦⟧ : ∀ Cs₁ Cs₂ → ⟦ Cs₁ ∪ Cs₂ ⟧ γ ⇔ (⟦ Cs₁ ⟧ γ × ⟦ Cs₂ ⟧ γ)
  ⟦∪⟧⇔⟦⟧×⟦⟧ {γ} Cs₁ Cs₂ =
    ⟦ Cs₁ ∪ Cs₂ ⟧ γ          ⇔⟨ ⟦⟧⇔⟦⟧′ (Cs₁ ∪ Cs₂) ⟩
    ⟦ Cs₁ ∪ Cs₂ ⟧′ γ         ⇔⟨ id⇔ ⟩
    ⟦ Cs₁ ⟧′ γ × ⟦ Cs₂ ⟧′ γ  ⇔˘⟨ ⟦⟧⇔⟦⟧′ Cs₁ ×-cong-⇔ ⟦⟧⇔⟦⟧′ Cs₂ ⟩
    ⟦ Cs₁ ⟧ γ × ⟦ Cs₂ ⟧ γ    □⇔

opaque

  -- ⟦ Cs₁ ∪ Cs₂ ⟧′ γ is logically equivalent to ⟦ Cs₁ ∪′ Cs₂ ⟧′ γ.

  ⟦∪⟧′⇔⟦∪′⟧′ : ∀ Cs₁ Cs₂ → ⟦ Cs₁ ∪ Cs₂ ⟧′ γ ⇔ ⟦ Cs₁ ∪′ Cs₂ ⟧′ γ
  ⟦∪⟧′⇔⟦∪′⟧′ _       none    = proj₁ , (_, _)
  ⟦∪⟧′⇔⟦∪′⟧′ none    (con _) = proj₂ , (_ ,_)
  ⟦∪⟧′⇔⟦∪′⟧′ (con _) (con _) = id⇔
  ⟦∪⟧′⇔⟦∪′⟧′ (_ ∪ _) (con _) = id⇔
  ⟦∪⟧′⇔⟦∪′⟧′ none    (_ ∪ _) = proj₂ , (_ ,_)
  ⟦∪⟧′⇔⟦∪′⟧′ (con _) (_ ∪ _) = id⇔
  ⟦∪⟧′⇔⟦∪′⟧′ (_ ∪ _) (_ ∪ _) = id⇔
