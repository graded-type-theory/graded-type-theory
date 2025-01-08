------------------------------------------------------------------------
-- A resource aware heap semantics. Some basic definitions.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Variant
open import Graded.Usage.Restrictions.Natrec

module Graded.Heap.Untyped
  {a} {M : Set a}
  {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  (open Usage-restrictions UR)
  -- If the usage rules use an nr function it must be factoring
  (factoring-nr :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr M (Natrec-mode-Has-nr 𝕄 has-nr))
  where

open Modality 𝕄
open Type-variant type-variant

open import Tools.Fin
open import Tools.Function
open import Tools.Nat hiding (_≤_)
open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

open import Definition.Untyped M hiding (head)
open import Graded.Modality.Nr-instances
open import Graded.Mode
open import Graded.Modality.Properties.Subtraction semiring-with-meet
open import Graded.Usage.Erased-matches

private variable
  n n′ m m′ m″ n″ k : Nat
  Γ : Con Term _
  t t′ t₁ t₂ u v A B : Term _
  x : Fin _
  p q r q′ q″ : M
  s : Strength
  b : BinderMode
  l : Universe-level
  ρ ρ′ : Wk _ _

opaque instance
  factoring-nr′ :
    ⦃ has-nr : Nr-available ⦄ →
    Is-factoring-nr _ (Natrec-mode-Has-nr 𝕄 has-nr)
  factoring-nr′ ⦃ has-nr ⦄ = factoring-nr ⦃ has-nr ⦄

------------------------------------------------------------------------
-- Pointers, closures and environments

-- Pointers as de Bruijn indices

Ptr : Nat → Set
Ptr = Fin

pattern y0 = x0

-- Heap entries, containing a term and a weakening, translating variable
-- indices to pointer indices.
-- Indexed by the size of the heap and the number of free variables of
-- the term

Entry : (m n : Nat) → Set a
Entry m n = Term n × Wk m n

-- Entires with a grade

Entryₘ : (m n : Nat) → Set a
Entryₘ m n = M × Entry m n

-- Weakening of entries

wkᵉⁿ : Wk m′ m → Entry m n → Entry m′ n
wkᵉⁿ ρ (t , E) = t , ρ • E

wk1ᵉⁿ : Entry m n → Entry (1+ m) n
wk1ᵉⁿ = wkᵉⁿ (step id)

------------------------------------------------------------------------
-- Eliminators and Evaluation stacks

-- Eliminators, indexed by the size of the heap.
-- The successor contructor is also treated as en eliminator when
-- evaluating under it.

data Elim (m : Nat) : Set a where
  ∘ₑ        : (p : M) (u : Term n) (ρ : Wk m n) → Elim m
  fstₑ      : M → Elim m
  sndₑ      : M → Elim m
  prodrecₑ  : (r p q : M) (A : Term (1+ n)) (u : Term (2+ n))
              (ρ : Wk m n) → Elim m
  natrecₑ   : (p q r q′ : M) (A : Term (1+ n)) (z : Term n)
              (s : Term (2+ n)) (ρ : Wk m n) → Elim m
  unitrecₑ  : (l : Universe-level) (p q : M) (A : Term (1+ n))
              (u : Term n) (ρ : Wk m n) → Elim m
  emptyrecₑ : (p : M) (A : Term n) (ρ : Wk m n) → Elim m
  Jₑ        : (p q : M) (A t : Term n) (B : Term (2+ n))
              (u v : Term n) (ρ : Wk m n) → Elim m
  Kₑ        : (p : M) (A t : Term n) (B : Term (1+ n))
              (u : Term n) (ρ : Wk m n) → Elim m
  []-congₑ  : (s : Strength) (A t u : Term n) (ρ : Wk m n) → Elim m
  sucₑ      : Elim m

private variable
  e e′ : Elim _

-- A predicate on grades indicating whether the grades on
-- natrecₑ are "compatible" for the chosen natrec-mode.

data Ok-natrec-multiplicity (q p r : M) : Set a where
  has-nr :
    ⦃ has-nr : Nr-available ⦄ →
    q ≡ nr₂ p r → Ok-natrec-multiplicity q p r
  no-nr :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    Greatest-lower-bound q (nrᵢ r 𝟙 p) →
    Ok-natrec-multiplicity q p r

-- Weakening of eliminators

wkᵉ : Wk m′ m → Elim m → Elim m′
wkᵉ ρ (∘ₑ p u ρ′) = ∘ₑ p u (ρ • ρ′)
wkᵉ ρ (fstₑ p) = fstₑ p
wkᵉ ρ (sndₑ p) = sndₑ p
wkᵉ ρ (natrecₑ p q r x A z s ρ′) = natrecₑ p q r x A z s (ρ • ρ′)
wkᵉ ρ (prodrecₑ r p q A u ρ′) = prodrecₑ r p q A u (ρ • ρ′)
wkᵉ ρ (unitrecₑ l p q A u ρ′) = unitrecₑ l p q A u (ρ • ρ′)
wkᵉ ρ (emptyrecₑ p A ρ′) = emptyrecₑ p A (ρ • ρ′)
wkᵉ ρ (Jₑ p q A t B u v ρ′) = Jₑ p q A t B u v (ρ • ρ′)
wkᵉ ρ (Kₑ p A t B u ρ′) = Kₑ p A t B u (ρ • ρ′)
wkᵉ ρ ([]-congₑ s A t u ρ′) = []-congₑ s A t u (ρ • ρ′)
wkᵉ ρ sucₑ = sucₑ

wk1ᵉ : Elim m → Elim (1+ m)
wk1ᵉ = wkᵉ (step id)

wk2ᵉ : Elim m → Elim (2+ m)
wk2ᵉ = wkᵉ (step (step id))

-- The multiplicity of the Jₑ eliminator, depending on which
-- erased matches are used.

∣∣ᵉ-J : Erased-matches → (p q : M) → M
∣∣ᵉ-J none _ _ = ω
∣∣ᵉ-J all  _ _ = 𝟘
∣∣ᵉ-J some p q =
  case is-𝟘? p of λ where
    (no _) → ω
    (yes _) → case is-𝟘? q of λ where
      (no _) → ω
      (yes _) → 𝟘

-- The multiplicity of the Kₑ eliminator, depending on which
-- erased matches are used.

∣∣ᵉ-K : Erased-matches → (p : M) → M
∣∣ᵉ-K none _ = ω
∣∣ᵉ-K all  _ = 𝟘
∣∣ᵉ-K some p =
  case is-𝟘? p of λ where
    (no _) → ω
    (yes _) → 𝟘

-- Multiplicity of an eliminator, representing how many copies need to
-- be evaluated.

∣_∣ᵉ : Elim m → M
∣ ∘ₑ _ _ _ ∣ᵉ = 𝟙
∣ fstₑ _ ∣ᵉ = 𝟙
∣ sndₑ _ ∣ᵉ = 𝟙
∣ prodrecₑ r _ _ _ _ _ ∣ᵉ = r
∣ natrecₑ _ _ _ q′ _ _ _ _ ∣ᵉ = q′
∣ unitrecₑ _ p _ _ _ _ ∣ᵉ = p
∣ emptyrecₑ p _ _ ∣ᵉ = p
∣ Jₑ p q _ _ _ _ _ _ ∣ᵉ = ∣∣ᵉ-J (erased-matches-for-J 𝟙ᵐ) p q
∣ Kₑ p _ _ _ _ _ ∣ᵉ = ∣∣ᵉ-K (erased-matches-for-K 𝟙ᵐ) p
∣ []-congₑ _ _ _ _ _ ∣ᵉ = 𝟘
∣ sucₑ ∣ᵉ = 𝟙

-- An equality relation for eliminators.
-- Eliminators are equal if they are (syntactically) the same up to
-- the multiplicity of natrec, i.e. if they are representations of the
-- same syntactic term.

infix 5 _~ᵉ_

data _~ᵉ_ {m} : (e e′ : Elim m) → Set a where
  ~ᵉ-refl : e ~ᵉ e
  ~ᵉ-natrec : natrecₑ p q r q′ A t u ρ ~ᵉ natrecₑ p q r q″ A t u ρ

-- Evaluation stacks, indexed by the size of the heap

data Stack (m : Nat) : Set a where
  ε : Stack m
  _∙_ : (e : Elim m) → (S : Stack m) → Stack m

-- Multiplicity of a stack, representing how many copies are currently
-- being evaluated.

∣_∣ : Stack m → M
∣ ε ∣ = 𝟙
∣ e ∙ S ∣ = ∣ S ∣ · ∣ e ∣ᵉ

private variable
  S S′ : Stack _

-- Weakening of stacks

wkˢ : Wk m′ m → Stack m → Stack m′
wkˢ ρ ε = ε
wkˢ ρ (e ∙ S) = wkᵉ ρ e ∙ wkˢ ρ S

wk1ˢ : Stack m → Stack (1+ m)
wk1ˢ = wkˢ (step id)

wk2ˢ : Stack m → Stack (2+ m)
wk2ˢ = wkˢ (step (step id))

-- Concatenation of stacks

_++_ : (S S′ : Stack m) → Stack m
ε ++ S′ = S′
(e ∙ S) ++ S′ = e ∙ (S ++ S′)

-- A stack consisting only of successor eliminators

sucₛ : Nat → Stack m
sucₛ 0 = ε
sucₛ (1+ n) = sucₑ ∙ sucₛ n

-- A utility predicate: stacks containing erased emptyrec

data emptyrec₀∈_ : (S : Stack m) → Set a where
  here : emptyrec₀∈ (emptyrecₑ 𝟘 A ρ ∙ S)
  there : emptyrec₀∈ S → emptyrec₀∈ (e ∙ S)

-- An equality relation for stacks.
-- Stacks are equal if all eliminators are pairwise equal up to the
-- multiplicity of natrec i.e. if they are representations of the same
-- syntactic term.

infix 5 _~ˢ_

data _~ˢ_ {m} : (S S′ : Stack m) → Set a where
  ε : ε ~ˢ ε
  _∙_ : e ~ᵉ e′ → S ~ˢ S′ → e ∙ S ~ˢ e′ ∙ S′

------------------------------------------------------------------------
-- Heaps

infixl 24 _∙_
infixl 24 _∙●

-- Heaps are lists of entries or "dummy" entries, representing something
-- erased.
-- Indexed by the number of dummy entries and total entries.

data Heap : (k m : Nat) → Set a where
  ε   : Heap 0 0
  _∙_ : (H : Heap k m) → (c : Entryₘ m n) → Heap k (1+ m)
  _∙● : (H : Heap k m) → Heap (1+ k) (1+ m)

-- A heap where all entries are erased

erasedHeap : (k : Nat) → Heap k k
erasedHeap 0 = ε
erasedHeap (1+ k) = erasedHeap k ∙●

private variable
  H H′ : Heap _ _
  c : Entry _ _
  c′ : Entryₘ _ _
  y : Ptr _

infix 20 _⊢_↦[_]_⨾_

-- Heap lookup (with grade update)
-- Note that lookup fails when trying to look up more copies than are
-- available. For instance, looking up any non-zero number when there
-- are zero copies available.

data _⊢_↦[_]_⨾_ : (H : Heap k m) (y : Ptr m) (q : M)
                  (c : Entry m n) (H′ : Heap k m) → Set a where
  here : p - q ≡ r
       → H ∙ (p , c) ⊢ y0 ↦[ q ] wk1ᵉⁿ c ⨾ H ∙ (r , c)
  there : H ⊢ y ↦[ q ] c ⨾ H′
        → H ∙ c′ ⊢ y +1 ↦[ q ] wk1ᵉⁿ c ⨾ H′ ∙ c′
  there● : H ⊢ y ↦[ q ] c ⨾ H′
         → H ∙● ⊢ y +1 ↦[ q ] wk1ᵉⁿ c ⨾ H′ ∙●

infix 20 _⊢_↦_

-- Heap lookup (without grade update)

data _⊢_↦_ : (H : Heap k m) (y : Ptr m) (c : Entry m n) → Set a where
  here : H ∙ (p , c) ⊢ y0 ↦ wk1ᵉⁿ c
  there : H ⊢ y ↦ c
        → H ∙ c′ ⊢ y +1 ↦ wk1ᵉⁿ c
  there● : H ⊢ y ↦ c
         → H ∙● ⊢ y +1 ↦ wk1ᵉⁿ c

infix 20 _⊢_↦●

-- Heap lookup to a dummy entry

data _⊢_↦● : (H : Heap k m) (y : Ptr m) → Set a where
  here : H ∙● ⊢ y0 ↦●
  there : H ⊢ y ↦● → H ∙ c′ ⊢ y +1 ↦●
  there● : H ⊢ y ↦● → H ∙● ⊢ y +1 ↦●

infix 5 _~ʰ_

-- Equality of heaps up to grades

data _~ʰ_ : (H H′ : Heap k m) → Set a where
  ε : ε ~ʰ ε
  _∙_ : H ~ʰ H′ → (c : Entry m n) → H ∙ (p , c) ~ʰ H′ ∙ (q , c)
  _∙● : H ~ʰ H′ → H ∙● ~ʰ H′ ∙●

-- Weakening of heaps

data _∷_⊇ʰ_ : (ρ : Wk m n) (H : Heap k m) (H′ : Heap k n) → Set a where
  id : id ∷ H ⊇ʰ H
  step : ρ ∷ H ⊇ʰ H′ → step ρ ∷ H ∙ c′ ⊇ʰ H′
  lift : ρ ∷ H ⊇ʰ H′ → lift ρ ∷ H ∙ (p , wkᵉⁿ ρ c) ⊇ʰ H′ ∙ (p , c)

-- Heaps as substitutions

toSubstₕ : Heap k m → Subst k m
toSubstₕ ε = idSubst
toSubstₕ (H ∙ (_ , t , ρ)) =
  let σ = toSubstₕ H
  in  consSubst σ (wk ρ t [ σ ])
toSubstₕ (H ∙●) = liftSubst (toSubstₕ H)

infix 25 _[_]ₕ
infix 25 _[_]⇑ₕ
infix 25 _[_]⇑²ₕ

_[_]ₕ : Term m → Heap k m → Term k
t [ H ]ₕ = t [ toSubstₕ H ]

_[_]⇑ₕ : Term (1+ m) → Heap k m → Term (1+ k)
t [ H ]⇑ₕ = t [ liftSubst (toSubstₕ H) ]

_[_]⇑²ₕ : Term (2+ m) → Heap k m → Term (2+ k)
t [ H ]⇑²ₕ = t [ liftSubstn (toSubstₕ H) 2 ]

-- A weakening that acts as an "inverse" to a heap substitution
-- See Graded.Heap.Untyped.Properties.toWkₕ-toSubstₕ

toWkₕ : Heap k m → Wk m k
toWkₕ ε = id
toWkₕ (H ∙ c) = step (toWkₕ H)
toWkₕ (H ∙●) = lift (toWkₕ H)

------------------------------------------------------------------------
-- Evaluation states

-- States consist of a heap, a head term, an environment/weakening
-- mapping variable indices to pointer indices and a stack.
-- Indexed by the number of dummy entries in the heap, the size
-- of the heap and the number of free variables in the head term.

infix 2 ⟨_,_,_,_⟩

record State (k m n : Nat) : Set a where
  no-eta-equality
  pattern
  constructor ⟨_,_,_,_⟩
  field
    heap : Heap k m
    head : Term n
    env : Wk m n
    stack : Stack m

-- Converting eliminators back to terms

infixr 29 ⦅_⦆ᵉ_

⦅_⦆ᵉ_ : Elim m → (Term m → Term m)
⦅ ∘ₑ p u ρ ⦆ᵉ t = t ∘⟨ p ⟩ wk ρ u
⦅ fstₑ p ⦆ᵉ t = fst p t
⦅ sndₑ p ⦆ᵉ t = snd p t
⦅ prodrecₑ r p q A u ρ ⦆ᵉ t =
  prodrec r p q (wk (lift ρ) A) t (wk (liftn ρ 2) u)
⦅ natrecₑ p q r _ A z s ρ ⦆ᵉ t =
  natrec p q r (wk (lift ρ) A) (wk ρ z) (wk (liftn ρ 2) s) t
⦅ unitrecₑ l p q A u ρ ⦆ᵉ t =
  unitrec l p q (wk (lift ρ) A) t (wk ρ u)
⦅ emptyrecₑ p A ρ ⦆ᵉ t =
  emptyrec p (wk ρ A) t
⦅ Jₑ p q A t B u v ρ ⦆ᵉ w =
  J p q (wk ρ A) (wk ρ t) (wk (liftn ρ 2) B) (wk ρ u) (wk ρ v) w
⦅ Kₑ p A t B u ρ ⦆ᵉ v =
  K p (wk ρ A) (wk ρ t) (wk (lift ρ) B) (wk ρ u) v
⦅ []-congₑ s A t u ρ ⦆ᵉ v =
  []-cong s (wk ρ A ) (wk ρ t) (wk ρ u) v
⦅ sucₑ ⦆ᵉ t = suc t

-- Converting stacks back to terms

infixr 28 ⦅_⦆ˢ_

⦅_⦆ˢ_ : Stack m → (Term m → Term m)
⦅ ε ⦆ˢ t = t
⦅ e ∙ S ⦆ˢ t = ⦅ S ⦆ˢ ⦅ e ⦆ᵉ t

-- Converting states back to terms

infix 28 ⦅_⦆

⦅_⦆ : (s : State k m n) → Term k
⦅ ⟨ H , t , ρ , S ⟩ ⦆ = ⦅ S ⦆ˢ (wk ρ t) [ H ]ₕ

-- The initial state consisting of a heap with only dummy bindings and
-- an empty stack.

initial : Term k → State k k k
initial {k} t = ⟨ erasedHeap k , t , id , ε ⟩

------------------------------------------------------------------------
-- Values and normal form head terms

-- Values are those terms that do not evaluate further

data Value {n : Nat} : (t : Term n) → Set a where
  lamᵥ : Value (lam p t)
  zeroᵥ : Value zero
  sucᵥ : Value (suc t)
  starᵥ : Value (star s l)
  prodᵥ : Value (prod s p u t)
  rflᵥ : Value rfl
  Uᵥ : Value (U l)
  ΠΣᵥ : Value (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ℕᵥ : Value ℕ
  Unitᵥ : Value (Unit s l)
  Emptyᵥ : Value Empty
  Idᵥ : Value (Id A t u)
  unitrec-ηᵥ : Unitʷ-η → Value (unitrec l p q A t u)

-- States in normal form are either values, or variables without
-- entries in the heap.
-- I.e. states which do not reduce with _⇒ₙ_

data Normal : (State k m n) → Set a where
  val : Value t → Normal ⟨ H , t , ρ , S ⟩
  var : H ⊢ wkVar ρ x ↦● → Normal ⟨ H , var x , ρ , S ⟩

------------------------------------------------------------------------
-- Matching terms and eliminators

-- "Matching" terms and stacks. A term and an eliminator are considered
-- to match if a state with the term in head position and the eliminator
-- on top of the stack would reduce using _⇒ᵥ_, see ⇒ᵥ→Matching and
-- Matching→⇒ᵥ in Graded.Heap.Reduction.Properties.
--
-- Note that when the weak unit type has eta-equality, unitrec is
-- considered a value and matches any stack.

data Matching {m n} : Term n → Stack m → Set a where
  ∘ₑ : Matching (lam p t) (∘ₑ p u ρ ∙ S)
  fstₑ : Matching (prodˢ p t u) (fstₑ p ∙ S)
  sndₑ : Matching (prodˢ p t u) (sndₑ p ∙ S)
  prodrecₑ : Matching (prodʷ p t u) (prodrecₑ r p q A v ρ ∙ S)
  natrecₑ₀ : Matching zero (natrecₑ p q r q′ A t u ρ ∙ S)
  natrecₑ₊ : Matching (suc v) (natrecₑ p q r q′ A t u ρ ∙ S)
  unitrecₑ : Matching (starʷ l) (unitrecₑ l p q A u ρ ∙ S)
  unitrec-η : Unitʷ-η → Matching (unitrec l p q A t u) S
  Jₑ : Matching rfl (Jₑ p q A t B u v ρ ∙ S)
  Kₑ : Matching rfl (Kₑ p A t B u ρ ∙ S)
  []-congₑ : Matching rfl ([]-congₑ s A t u ρ ∙ S)
