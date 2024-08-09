------------------------------------------------------------------------
-- A resource aware heap semantics. Some basic definitions.
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Tools.Bool
open import Definition.Typed.Variant

module Heap.Untyped
  {a} {M : Set a}
  {𝕄 : Modality M}
  (type-variant : Type-variant)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄 hiding (_+_)
open Type-variant type-variant
open Usage-restrictions UR

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat hiding (_≤_)
open import Tools.PropositionalEquality
open import Tools.Product
open import Tools.Relation

open import Definition.Untyped M hiding (head)
open import Graded.Mode
open import Graded.Modality.Properties.Subtraction semiring-with-meet
open import Graded.Modality.Nr-instances
open import Graded.Usage.Erased-matches

private variable
  n n′ m m′ m″ n″ k : Nat
  Γ : Con Term _
  t t₁ t₂ u v A B : Term _
  x : Fin _
  p q r : M
  s : Strength
  b : BinderMode
  ρ : Wk _ _

infixl 20 _⊢_↦[_]_⨾_
infix   2 ⟨_,_,_,_⟩

------------------------------------------------------------------------
-- Pointers, closures and environments

-- Pointers as de Bruijn indices

Ptr : Nat → Set
Ptr = Fin

pattern y0 = x0

-- An enivronment is a weakening,
-- mapping variables (de Bruijn indices) to pointers (de Bruijn indices).

Env : (m n : Nat) → Set
Env = Wk

-- Closures, indexed by the size of the heap and the number of
-- free variables of the term

Closure : (m n : Nat) → Set a
Closure m n = Term n × Env m n

-- Closures with a grade

Closureₘ : (m n : Nat) → Set a
Closureₘ m n = M × Closure m n

private
  -- Weakening of closures

  wkᶜ : Wk m′ m → Closure m n → Closure m′ n
  wkᶜ ρ (t , E) = t , ρ • E

wk1ᶜ : Closure m n → Closure (1+ m) n
wk1ᶜ = wkᶜ (step id)

------------------------------------------------------------------------
-- Eliminators and Evaluation stacks

-- Eliminators, indexed by the size of the heap

data Elim (m : Nat) : Set a where
  ∘ₑ        : (p : M) (u : Term n) (E : Env m n) → Elim m
  fstₑ      : M → Elim m
  sndₑ      : M → Elim m
  prodrecₑ  : (r p q : M) (A : Term (1+ n)) (u : Term (2+ n)) (E : Env m n) → Elim m
  natrecₑ   : (p q r : M) (A : Term (1+ n)) (z : Term n)
              (s : Term (2+ n)) (E : Env m n) → Elim m
  unitrecₑ  : (p q : M) (A : Term (1+ n)) (u : Term n) (E : Env m n) → Elim m
  Jₑ        : (p q : M) (A t : Term n) (B : Term (2+ n))
              (u v : Term n) (E : Env m n) → Elim m
  Kₑ        : (p : M) (A t : Term n) (B : Term (1+ n))
              (u : Term n) (E : Env m n) → Elim m
  []-congₑ  : (s : Strength) (A t u : Term n) (E : Env m n) → Elim m
  sucₑ      : Elim m

-- Weakening of eliminators

wkᵉ : Wk m′ m → Elim m → Elim m′
wkᵉ ρ (∘ₑ p u E) = ∘ₑ p u (ρ • E)
wkᵉ ρ (fstₑ p) = fstₑ p
wkᵉ ρ (sndₑ p) = sndₑ p
wkᵉ ρ (natrecₑ p q r A z s E) = natrecₑ p q r A z s (ρ • E)
wkᵉ ρ (prodrecₑ r p q A u E) = prodrecₑ r p q A u (ρ • E)
wkᵉ ρ (unitrecₑ p q A u E) = unitrecₑ p q A u (ρ • E)
wkᵉ ρ (Jₑ p q A t B u v E) = Jₑ p q A t B u v (ρ • E)
wkᵉ ρ (Kₑ p A t B u E) = Kₑ p A t B u (ρ • E)
wkᵉ ρ ([]-congₑ s A t u E) = []-congₑ s A t u (ρ • E)
wkᵉ ρ sucₑ = sucₑ

wk1ᵉ : Elim m → Elim (1+ m)
wk1ᵉ = wkᵉ (step id)

wk2ᵉ : Elim m → Elim (2+ m)
wk2ᵉ = wkᵉ (step (step id))

-- The multiplicity of the Jₑ eliminator

∣∣ᵉ-J : Erased-matches → (p q : M) → M
∣∣ᵉ-J none _ _ = ω
∣∣ᵉ-J all  _ _ = 𝟘
∣∣ᵉ-J some p q =
  case is-𝟘? p of λ where
    (no _) → ω
    (yes _) → case is-𝟘? q of λ where
      (no _) → ω
      (yes _) → 𝟘

-- The multiplicity of the Kₑ eliminator

∣∣ᵉ-K : Erased-matches → (p : M) → M
∣∣ᵉ-K none _ = ω
∣∣ᵉ-K all  _ = 𝟘
∣∣ᵉ-K some p =
  case is-𝟘? p of λ where
    (no _) → ω
    (yes _) → 𝟘

-- Multiplicity of an eliminator, representing how many copies need to be evaluated

∣_∣ᵉ : ⦃ _ : Has-nr M semiring-with-meet ⦄
     → ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
     → Elim m → M
∣ ∘ₑ _ _ _ ∣ᵉ = 𝟙
∣ fstₑ _ ∣ᵉ = 𝟙
∣ sndₑ _ ∣ᵉ = 𝟙
∣ prodrecₑ r _ _ _ _ _ ∣ᵉ = r
∣ natrecₑ p _ r _ _ _ _ ∣ᵉ = nr₂ p r
∣ unitrecₑ p _ _ _ _ ∣ᵉ = p
∣ Jₑ p q _ _ _ _ _ _ ∣ᵉ = ∣∣ᵉ-J (erased-matches-for-J 𝟙ᵐ) p q
∣ Kₑ p _ _ _ _ _ ∣ᵉ = ∣∣ᵉ-K (erased-matches-for-K 𝟙ᵐ) p
∣ []-congₑ _ _ _ _ _ ∣ᵉ = 𝟘
∣ sucₑ ∣ᵉ = 𝟙

-- Evaluation stacks, indexed by the size of the heap

data Stack (m : Nat) : Set a where
  ε : Stack m
  _∙_ : (e : Elim m) → (S : Stack m) → Stack m

-- Multiplicity of a stack, representing how many copies are currently being evaluated

∣_∣ : ⦃ _ : Has-nr M semiring-with-meet ⦄
    → ⦃ _ : Has-factoring-nr M semiring-with-meet ⦄
    →  Stack m → M
∣ ε ∣ = 𝟙
∣ e ∙ S ∣ = ∣ S ∣ · ∣ e ∣ᵉ

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

sucₛ : Nat → Stack m
sucₛ 0 = ε
sucₛ (1+ n) = sucₑ ∙ sucₛ n

------------------------------------------------------------------------
-- Heaps

-- Heaps are collections of bindings.

infixl 24 _∙_
infixl 24 _∙●

data Heap : (k m : Nat) → Set a where
  ε   : Heap 0 0
  _∙_ : (H : Heap k m) → (c : Closureₘ m n) → Heap k (1+ m)
  _∙● : (H : Heap k m) → Heap (1+ k) (1+ m)

-- A heap where all entries are erased

erasedHeap : (k : Nat) → Heap k k
erasedHeap 0 = ε
erasedHeap (1+ k) = erasedHeap k ∙●

private variable
  H H′ : Heap _ _
  c : Closure _ _
  c′ : Closureₘ _ _
  E E′ : Env _ _
  S : Stack _
  y : Ptr _

-- Heap lookup (with grade update)
-- Note that lookup fails e.g. when the grade is 𝟘.

data _⊢_↦[_]_⨾_ : (H : Heap k m) (y : Ptr m) (q : M)
                  (c : Closure m n) (H′ : Heap k m) → Set a where
  here : p - q ≡ r
       → H ∙ (p , c) ⊢ y0 ↦[ q ] wk1ᶜ c ⨾ H ∙ (r , c)
  there : H ⊢ y ↦[ q ] c ⨾ H′
        → H ∙ c′ ⊢ y +1 ↦[ q ] wk1ᶜ c ⨾ H′ ∙ c′
  there● : H ⊢ y ↦[ q ] c ⨾ H′
         → H ∙● ⊢ y +1 ↦[ q ] wk1ᶜ c ⨾ H′ ∙●


-- Heap lookup (without grade update)

data _⊢_↦_ : (H : Heap k m) (y : Ptr m) (c : Closure m n) → Set a where
  here : H ∙ (p , c) ⊢ y0 ↦ wk1ᶜ c
  there : H ⊢ y ↦ c
        → H ∙ c′ ⊢ y +1 ↦ wk1ᶜ c
  there● : H ⊢ y ↦ c
         → H ∙● ⊢ y +1 ↦ wk1ᶜ c


-- Equality of heaps up to grades

infix 5 _~ʰ_

data _~ʰ_ : (H H′ : Heap k m) → Set a where
  ε : ε ~ʰ ε
  _∙_ : H ~ʰ H′ → (c : Closure m n) → H ∙ (p , c) ~ʰ H′ ∙ (q , c)
  _∙● : H ~ʰ H′ → H ∙● ~ʰ H′ ∙●

-- Weakening of heaps

data _∷_⊇ʰ_ : (ρ : Wk m n) (H : Heap k m) (H′ : Heap k n) → Set a where
  id : id ∷ H ⊇ʰ H
  step : ρ ∷ H ⊇ʰ H′ → step ρ ∷ H ∙ c′ ⊇ʰ H′
  -- lift : ρ ∷ H ⊇ʰ H′ → lift ρ ∷ H ∙ (p , wkᶜ ρ c) ⊇ʰ H′ ∙ (p , c)

-- Heaps as substitutions

toSubstₕ : Heap k m → Subst k m
toSubstₕ ε = idSubst
toSubstₕ (H ∙ (_ , t , E)) =
  let σ = toSubstₕ H
  in  consSubst σ (wk E t [ σ ])
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
-- See Heap.Untyped.Properties.toWkₕ-toSubstₕ

toWkₕ : Heap k m → Wk m k
toWkₕ ε = id
toWkₕ (H ∙ c) = step (toWkₕ H)
toWkₕ (H ∙●) = lift (toWkₕ H)

------------------------------------------------------------------------
-- Evaluation states

-- States, indexed by the size of the heap and the number of free
-- variables in the head.

record State (k m n : Nat) : Set a where
  constructor ⟨_,_,_,_⟩
  field
    heap : Heap k m
    head : Term n
    env : Env m n
    stack : Stack m

-- Converting states back to terms

⦅_⦆ᵉ : Elim m → (Term m → Term m)
⦅ ∘ₑ p u E ⦆ᵉ = _∘⟨ p ⟩ wk E u
⦅ fstₑ p ⦆ᵉ = fst p
⦅ sndₑ p ⦆ᵉ = snd p
⦅ prodrecₑ r p q A u E ⦆ᵉ t =
  prodrec r p q (wk (lift E) A) t (wk (liftn E 2) u)
⦅ natrecₑ p q r A z s E ⦆ᵉ t =
  natrec p q r (wk (lift E) A) (wk E z) (wk (liftn E 2) s) t
⦅ unitrecₑ p q A u E ⦆ᵉ t =
  unitrec p q (wk (lift E) A) t (wk E u)
⦅ Jₑ p q A t B u v E ⦆ᵉ w =
  J p q (wk E A) (wk E t) (wk (liftn E 2) B) (wk E u) (wk E v) w
⦅ Kₑ p A t B u E ⦆ᵉ v =
  K p (wk E A) (wk E t) (wk (lift E) B) (wk E u) v
⦅ []-congₑ s A t u E ⦆ᵉ v =
  []-cong s (wk E A ) (wk E t) (wk E u) v
⦅ sucₑ ⦆ᵉ = suc

⦅_⦆ˢ : Stack m → (Term m → Term m)
⦅ ε ⦆ˢ = idᶠ
⦅ e ∙ S ⦆ˢ = ⦅ S ⦆ˢ ∘ᶠ ⦅ e ⦆ᵉ

⦅_⦆ : (s : State k m n) → Term k
⦅ ⟨ H , t , E , S ⟩ ⦆ = ⦅ S ⦆ˢ (wk E t) [ H ]ₕ

-- The initial state

initial : Term k → State k k k
initial {k} t = ⟨ erasedHeap k , t , id , ε ⟩

------------------------------------------------------------------------
-- Values and normal form head terms

-- Values are those terms that do not evaluate further

data Value {n : Nat} : (t : Term n) → Set a where
  lamᵥ : Value (lam p t)
  zeroᵥ : Value zero
  sucᵥ : Value (suc t)
  starᵥ : Value (star s)
  prodᵥ : Value (prod s p u t)
  rflᵥ : Value rfl
  Uᵥ : Value U
  ΠΣᵥ : Value (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ℕᵥ : Value ℕ
  Unitᵥ : Value (Unit s)
  Emptyᵥ : Value Empty
  Idᵥ : Value (Id A t u)

-- States in normal form

data Normal : (State k m n) → Set a where
  val : Value t → Normal ⟨ H , t , E , S ⟩
  var : (∀ {n} {c : Closure _ n} → H ⊢ wkVar E x ↦ c → ⊥) → Normal ⟨ H , var x , E , S ⟩
  emptyrecₙ : Normal ⟨ H , emptyrec p A t , E , S ⟩
  unitrec-ηₙ : Unitʷ-η → Normal ⟨ H , unitrec p q A t u , E , S ⟩
