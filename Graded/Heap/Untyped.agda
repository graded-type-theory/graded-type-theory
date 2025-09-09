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
  -- If the usage rules use an nr function is assumed to be factoring
  -- This is used to get the quantity representing the uses of the
  -- natural number argument, i.e. how many copies of it that should
  -- be placed on the heap.
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
open import Definition.Untyped.Names-below M

open import Graded.Modality.Nr-instances
open import Graded.Mode
open import Graded.Modality.Properties.Subtraction semiring-with-meet
open import Graded.Usage.Erased-matches

private variable
  n n′ m m′ m″ n″ k : Nat
  Γ : Con Term _
  t t₁ t₂ u v A B C : Term _
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

wkᵉ : Wk m′ m → Entry m n → Entry m′ n
wkᵉ ρ (t , E) = t , ρ • E

wk1ᵉ : Entry m n → Entry (1+ m) n
wk1ᵉ = wkᵉ (step id)

------------------------------------------------------------------------
-- Continuations and Evaluation stacks

-- Contiuations, indexed by the size of the heap.
-- These are essentially continuations but the successor contructor is
-- also treated as a continuation when evaluating under it.

data Cont (m : Nat) : Set a where
  ∘ₑ        : (p : M) (u : Term n) (ρ : Wk m n) → Cont m
  fstₑ      : M → Cont m
  sndₑ      : M → Cont m
  prodrecₑ  : (r p q : M) (A : Term (1+ n)) (u : Term (2+ n))
              (ρ : Wk m n) → Cont m
  natrecₑ   : (p q r : M) (A : Term (1+ n)) (z : Term n)
              (s : Term (2+ n)) (ρ : Wk m n) → Cont m
  unitrecₑ  : (l : Universe-level) (p q : M) (A : Term (1+ n))
              (u : Term n) (ρ : Wk m n) → Cont m
  emptyrecₑ : (p : M) (A : Term n) (ρ : Wk m n) → Cont m
  Jₑ        : (p q : M) (A t : Term n) (B : Term (2+ n))
              (u v : Term n) (ρ : Wk m n) → Cont m
  Kₑ        : (p : M) (A t : Term n) (B : Term (1+ n))
              (u : Term n) (ρ : Wk m n) → Cont m
  []-congₑ  : (s : Strength) (A t u : Term n) (ρ : Wk m n) → Cont m
  sucₑ      : Cont m

private variable
  c c′ : Cont _

-- Weakening of continuations

wkᶜ : Wk m′ m → Cont m → Cont m′
wkᶜ ρ (∘ₑ p u ρ′) = ∘ₑ p u (ρ • ρ′)
wkᶜ ρ (fstₑ p) = fstₑ p
wkᶜ ρ (sndₑ p) = sndₑ p
wkᶜ ρ (natrecₑ p q r A z s ρ′) = natrecₑ p q r A z s (ρ • ρ′)
wkᶜ ρ (prodrecₑ r p q A u ρ′) = prodrecₑ r p q A u (ρ • ρ′)
wkᶜ ρ (unitrecₑ l p q A u ρ′) = unitrecₑ l p q A u (ρ • ρ′)
wkᶜ ρ (emptyrecₑ p A ρ′) = emptyrecₑ p A (ρ • ρ′)
wkᶜ ρ (Jₑ p q A t B u v ρ′) = Jₑ p q A t B u v (ρ • ρ′)
wkᶜ ρ (Kₑ p A t B u ρ′) = Kₑ p A t B u (ρ • ρ′)
wkᶜ ρ ([]-congₑ s A t u ρ′) = []-congₑ s A t u (ρ • ρ′)
wkᶜ ρ sucₑ = sucₑ

wk1ᶜ : Cont m → Cont (1+ m)
wk1ᶜ = wkᶜ (step id)

wk2ᶜ : Cont m → Cont (2+ m)
wk2ᶜ = wkᶜ (step (step id))

-- The multiplicity of the natrecₑ continuation

data ∣natrec_,_∣≡_ : M → M → M → Set a where
  has-nrₑ :
    ⦃ has-nr : Nr-available ⦄ →
     ∣natrec p , r ∣≡ nr₂ p r
  no-nrₑ :
    ⦃ no-nr : Nr-not-available-GLB ⦄ →
    Greatest-lower-bound q (nrᵢ r 𝟙 p) →
    ∣natrec p , r ∣≡ q

-- The multiplicity of the Jₑ continuation, depending on which
-- erased matches are used.

data ∣J_,_,_∣≡_ : Erased-matches → M → M → M → Set a where
  J-all   : ∣J all  , p , q ∣≡ 𝟘
  J-some₀ : p ≡ 𝟘 → q ≡ 𝟘 →
            ∣J some , p , q ∣≡ 𝟘
  J-some  : ¬ (p ≡ 𝟘 × q ≡ 𝟘) →
            ∣J some , p , q ∣≡ ω
  J-none  : ∣J none , p , q ∣≡ ω

-- The multiplicity of the Kₑ continuation, depending on which
-- erased matches are used.

data ∣K_,_∣≡_ : Erased-matches → M → M → Set a where
  K-all   : ∣K all  , p ∣≡ 𝟘
  K-some₀ : p ≡ 𝟘 →
            ∣K some , p ∣≡ 𝟘
  K-some  : p ≢ 𝟘 →
            ∣K some , p ∣≡ ω
  K-none  : ∣K none , p ∣≡ ω

-- Multiplicity of an continuation, representing how many copies need to
-- be evaluated.

data ∣_∣ᶜ≡_ {m} : Cont m → M → Set a where
  ∘ₑ : ∣ ∘ₑ p u ρ ∣ᶜ≡ 𝟙
  fstₑ : ∣ fstₑ p ∣ᶜ≡ 𝟙
  sndₑ : ∣ sndₑ p ∣ᶜ≡ 𝟙
  prodrecₑ : ∣ prodrecₑ r p q A u ρ ∣ᶜ≡ r
  natrecₑ :
    ∣natrec p , r ∣≡ q′ →
    ∣ natrecₑ p q r A u v ρ ∣ᶜ≡ q′
  unitrecₑ : ∣ unitrecₑ l p q A u ρ ∣ᶜ≡ p
  emptyrecₑ : ∣ emptyrecₑ p A ρ ∣ᶜ≡ p
  Jₑ :
    ∣J erased-matches-for-J 𝟙ᵐ , p , q ∣≡ r →
    ∣ Jₑ p q A t B u v ρ ∣ᶜ≡ r
  Kₑ :
    ∣K erased-matches-for-K 𝟙ᵐ , p ∣≡ r →
    ∣ Kₑ p A t B u ρ ∣ᶜ≡ r
  []-congₑ : ∣ []-congₑ s A t u ρ ∣ᶜ≡ 𝟘
  sucₑ : ∣ sucₑ ∣ᶜ≡ 𝟙

-- Evaluation stacks, indexed by the size of the heap

data Stack (m : Nat) : Set a where
  ε : Stack m
  _∙_ : (c : Cont m) → (S : Stack m) → Stack m

private variable
  S S′ : Stack _

-- Multiplicity of a stack, representing how many copies are currently
-- being evaluated.

data ∣_∣≡_ {m} : Stack m → M → Set a where
  ε   : ∣ ε ∣≡ 𝟙
  _∙_ : ∣ c ∣ᶜ≡ q → ∣ S ∣≡ p → ∣ c ∙ S ∣≡ p · q

-- Weakening of stacks

wkˢ : Wk m′ m → Stack m → Stack m′
wkˢ ρ ε = ε
wkˢ ρ (c ∙ S) = wkᶜ ρ c ∙ wkˢ ρ S

wk1ˢ : Stack m → Stack (1+ m)
wk1ˢ = wkˢ (step id)

wk2ˢ : Stack m → Stack (2+ m)
wk2ˢ = wkˢ (step (step id))

-- Concatenation of stacks

_++_ : (S S′ : Stack m) → Stack m
ε ++ S′ = S′
(c ∙ S) ++ S′ = c ∙ (S ++ S′)

-- A stack consisting only of successor continuations

sucₛ : Nat → Stack m
sucₛ 0 = ε
sucₛ (1+ n) = sucₑ ∙ sucₛ n

-- A predicate for stacks containing natrec (with given grades)

data prodrec_,_∈ {m} (r p : M) : (S : Stack m) → Set a where
  here  : prodrec r , p ∈ (prodrecₑ r p q A u ρ ∙ S)
  there : prodrec r , p ∈ S → prodrec r , p ∈ (c ∙ S)

-- A predicate for stacks containing natrec (with given grades)

data natrec_,_∈ {m} (p r : M) : (S : Stack m) → Set a where
  here  : natrec p , r ∈ (natrecₑ p q r A u v ρ ∙ S)
  there : natrec p , r ∈ S → natrec p , r ∈ (c ∙ S)

-- A predicate for stacks containing unitrecₑ (with a given grade)

data unitrec_∈_ {m} (p : M) : (S : Stack m) → Set a where
  here  : unitrec p ∈ (unitrecₑ n p q A u ρ ∙ S)
  there : unitrec p ∈ S → unitrec p ∈ (c ∙ S)

-- A predicate for stacks containing emptyrecₑ (with a given grade)

data emptyrec_∈_ {m} (p : M) : (S : Stack m) → Set a where
  here : emptyrec p ∈ (emptyrecₑ p A ρ ∙ S)
  there : emptyrec p ∈ S → emptyrec p ∈ (c ∙ S)

-- A predicate for stacks containing Jₑ (with given grades)

data J_,_∈_ {m} (p q : M) : (S : Stack m) → Set a where
  here : J p , q ∈ (Jₑ p q A t B u v ρ ∙ S)
  there : J p , q ∈ S → J p , q ∈ (c ∙ S)

-- A predicate for stacks containing Kₑ (with a given grade)

data K_∈_ {m} (p : M) : (S : Stack m) → Set a where
  here : K p ∈ (Kₑ p A t B u ρ ∙ S)
  there : K p ∈ S → K p ∈ (c ∙ S)

-- A predicate for stacks containing []-congₑ

data []-cong∈_ {m} : (S : Stack m) → Set a where
  here : []-cong∈ ([]-congₑ s A t u ρ ∙ S)
  there : []-cong∈ S → []-cong∈ (c ∙ S)

-- A predicate for stacks containing []-congₑ

data suc∈_ {m} : (S : Stack m) → Set a where
  here : suc∈ (sucₑ ∙ S)
  there : suc∈ S → suc∈ (c ∙ S)

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
  e : Entry _ _
  e′ : Entryₘ _ _
  y : Ptr _

infix 20 _⊢_↦[_]_⨾_

-- Heap lookup (with grade update)
-- Note that lookup fails when trying to look up more copies than are
-- available. For instance, looking up any non-zero number when there
-- are zero copies available.

data _⊢_↦[_]_⨾_ : (H : Heap k m) (y : Ptr m) (q : M)
                  (e : Entry m n) (H′ : Heap k m) → Set a where
  here : p - q ≡ r
       → H ∙ (p , e) ⊢ y0 ↦[ q ] wk1ᵉ e ⨾ H ∙ (r , e)
  there : H ⊢ y ↦[ q ] e ⨾ H′
        → H ∙ e′ ⊢ y +1 ↦[ q ] wk1ᵉ e ⨾ H′ ∙ e′
  there● : H ⊢ y ↦[ q ] e ⨾ H′
         → H ∙● ⊢ y +1 ↦[ q ] wk1ᵉ e ⨾ H′ ∙●

infix 20 _⊢_↦_

-- Heap lookup (without grade update)

data _⊢_↦_ : (H : Heap k m) (y : Ptr m) (e : Entry m n) → Set a where
  here : H ∙ (p , e) ⊢ y0 ↦ wk1ᵉ e
  there : H ⊢ y ↦ e
        → H ∙ e′ ⊢ y +1 ↦ wk1ᵉ e
  there● : H ⊢ y ↦ e
         → H ∙● ⊢ y +1 ↦ wk1ᵉ e

infix 20 _⊢_↦●

-- Heap lookup to a dummy entry

data _⊢_↦● : (H : Heap k m) (y : Ptr m) → Set a where
  here : H ∙● ⊢ y0 ↦●
  there : H ⊢ y ↦● → H ∙ e′ ⊢ y +1 ↦●
  there● : H ⊢ y ↦● → H ∙● ⊢ y +1 ↦●

infix 5 _~ʰ_

-- Equality of heaps up to grades

data _~ʰ_ : (H H′ : Heap k m) → Set a where
  ε : ε ~ʰ ε
  _∙_ : H ~ʰ H′ → (e : Entry m n) → H ∙ (p , e) ~ʰ H′ ∙ (q , e)
  _∙● : H ~ʰ H′ → H ∙● ~ʰ H′ ∙●

-- Weakening of heaps

data _∷_⊇ʰ_ : (ρ : Wk m n) (H : Heap k m) (H′ : Heap k n) → Set a where
  id : id ∷ H ⊇ʰ H
  step : ρ ∷ H ⊇ʰ H′ → step ρ ∷ H ∙ e′ ⊇ʰ H′
  lift : ρ ∷ H ⊇ʰ H′ → lift ρ ∷ H ∙ (p , wkᵉ ρ e) ⊇ʰ H′ ∙ (p , e)

-- Lookup the grade of the entry of a given pointer

_⟨_⟩ʰ : Heap k m → Ptr m → M
ε ⟨ () ⟩ʰ
(H ∙ (p , _)) ⟨ y0 ⟩ʰ = p
(H ∙ _) ⟨ y +1 ⟩ʰ = H ⟨ y ⟩ʰ
(H ∙●) ⟨ y0 ⟩ʰ = 𝟘
(H ∙●) ⟨ y +1 ⟩ʰ = H ⟨ y ⟩ʰ

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
toWkₕ (H ∙ e) = step (toWkₕ H)
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

-- Converting continuations back to terms

infixr 29 ⦅_⦆ᶜ_

⦅_⦆ᶜ_ : Cont m → (Term m → Term m)
⦅ ∘ₑ p u ρ ⦆ᶜ t = t ∘⟨ p ⟩ wk ρ u
⦅ fstₑ p ⦆ᶜ t = fst p t
⦅ sndₑ p ⦆ᶜ t = snd p t
⦅ prodrecₑ r p q A u ρ ⦆ᶜ t =
  prodrec r p q (wk (lift ρ) A) t (wk (liftn ρ 2) u)
⦅ natrecₑ p q r A z s ρ ⦆ᶜ t =
  natrec p q r (wk (lift ρ) A) (wk ρ z) (wk (liftn ρ 2) s) t
⦅ unitrecₑ l p q A u ρ ⦆ᶜ t =
  unitrec l p q (wk (lift ρ) A) t (wk ρ u)
⦅ emptyrecₑ p A ρ ⦆ᶜ t =
  emptyrec p (wk ρ A) t
⦅ Jₑ p q A t B u v ρ ⦆ᶜ w =
  J p q (wk ρ A) (wk ρ t) (wk (liftn ρ 2) B) (wk ρ u) (wk ρ v) w
⦅ Kₑ p A t B u ρ ⦆ᶜ v =
  K p (wk ρ A) (wk ρ t) (wk (lift ρ) B) (wk ρ u) v
⦅ []-congₑ s A t u ρ ⦆ᶜ v =
  []-cong s (wk ρ A ) (wk ρ t) (wk ρ u) v
⦅ sucₑ ⦆ᶜ t = suc t

-- Converting stacks back to terms

infixr 28 ⦅_⦆ˢ_

⦅_⦆ˢ_ : Stack m → (Term m → Term m)
⦅ ε ⦆ˢ t = t
⦅ c ∙ S ⦆ˢ t = ⦅ S ⦆ˢ ⦅ c ⦆ᶜ t

-- Converting states back to terms

infix 28 ⦅_⦆

⦅_⦆ : (s : State k m n) → Term k
⦅ ⟨ H , t , ρ , S ⟩ ⦆ = ⦅ S ⦆ˢ (wk ρ t) [ H ]ₕ

-- The initial state consisting of a heap with only dummy bindings and
-- an empty stack.

initial : Term k → State k k k
initial {k} t = ⟨ erasedHeap k , t , id , ε ⟩

------------------------------------------------------------------------
-- Variants of No-names

-- No-namesʰ holds for a heap if it does not contain any names.

data No-namesʰ : Heap k m → Set a where
  ε   : No-namesʰ ε
  _∙_ : No-namesʰ H → No-names t → No-namesʰ (H ∙ (p , t , ρ))
  _∙● : No-namesʰ H → No-namesʰ (H ∙●)

-- No-namesᶜ holds for a continuation if it does not contain any
-- names.

data No-namesᶜ : Cont m → Set a where
  emptyrecₑ : No-names A → No-namesᶜ (emptyrecₑ p A ρ)
  unitrecₑ  : No-names A → No-names u → No-namesᶜ (unitrecₑ l p q A u ρ)
  ∘ₑ        : No-names u → No-namesᶜ (∘ₑ p u ρ)
  fstₑ      : No-namesᶜ {m = m} (fstₑ p)
  sndₑ      : No-namesᶜ {m = m} (sndₑ p)
  prodrecₑ  : No-names C → No-names u → No-namesᶜ (prodrecₑ r p q C u ρ)
  sucₑ      : No-namesᶜ {m = m} sucₑ
  natrecₑ   : No-names A → No-names t → No-names u →
              No-namesᶜ (natrecₑ p q r A t u ρ)
  Jₑ        : No-names A → No-names t → No-names B → No-names u →
              No-names v → No-namesᶜ (Jₑ p q A t B u v ρ)
  Kₑ        : No-names A → No-names t → No-names B → No-names u →
              No-namesᶜ (Kₑ p A t B u ρ)
  []-congₑ  : No-names A → No-names t → No-names u →
              No-namesᶜ ([]-congₑ s A t u ρ)

-- No-namesˢ holds for a stack if it does not contain any names.

data No-namesˢ : Stack m → Set a where
  ε   : No-namesˢ {m = m} ε
  _∙_ : No-namesᶜ c → No-namesˢ S → No-namesˢ (c ∙ S)

-- No-namesₛ′ holds for a state if there are no names in its heap or
-- head term.

No-namesₛ′ : State k m n → Set a
No-namesₛ′ ⟨ H , t , _ , _ ⟩ = No-namesʰ H × No-names t

-- No-namesₛ holds for a state if there are no names in its heap, head
-- term or stack.

No-namesₛ : State k m n → Set a
No-namesₛ s@(⟨ _ , _ , _ , S ⟩) = No-namesₛ′ s × No-namesˢ S

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
-- Matching terms and continuations

-- "Matching" terms and stacks. A term and a continuation are considered
-- to match if a state with the term in head position and the continuation
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
  natrecₑ₀ : Matching zero (natrecₑ p q r A t u ρ ∙ S)
  natrecₑ₊ : Matching (suc v) (natrecₑ p q r A t u ρ ∙ S)
  unitrecₑ : Matching (starʷ l) (unitrecₑ l p q A u ρ ∙ S)
  unitrec-η : Unitʷ-η → Matching (unitrec l p q A t u) S
  Jₑ : Matching rfl (Jₑ p q A t B u v ρ ∙ S)
  Kₑ : Matching rfl (Kₑ p A t B u ρ ∙ S)
  []-congₑ : Matching rfl ([]-congₑ s A t u ρ ∙ S)
