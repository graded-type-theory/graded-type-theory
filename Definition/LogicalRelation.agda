------------------------------------------------------------------------
-- The logical relation for reducibility
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation
  {a} {Mod : Set a}
  {𝕄 : Modality Mod}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped Mod as U hiding (_∷_; K)
open import Definition.Typed.Properties R
open import Definition.Typed R
open import Definition.Typed.Weakening R

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Unit

private
  variable
    p q : Mod
    ℓ : Nat
    Γ Δ : Con Term ℓ
    t t′ u u′ : Term _
    ρ : Wk _ _

-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reducibility of Neutrals:

-- Neutral type
record _⊩ne_ {ℓ : Nat} (Γ : Con Term ℓ) (A : Term ℓ) : Set a where
  constructor ne
  field
    K   : Term ℓ
    D   : Γ ⊢ A :⇒*: K
    neK : Neutral K
    K≡K : Γ ⊢ K ≅ K

-- Neutral type equality
record _⊩ne_≡_/_ (Γ : Con Term ℓ) (A B : Term ℓ) ([A] : Γ ⊩ne A) : Set a where
  constructor ne₌
  open _⊩ne_ [A]
  field
    M   : Term ℓ
    D′  : Γ ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ ⊢ K ≅ M

-- Neutral term in WHNF
record _⊩neNf_∷_ (Γ : Con Term ℓ) (k A : Term ℓ) : Set a where
  inductive
  constructor neNfₜ
  field
    neK  : Neutral k
    ⊢k   : Γ ⊢ k ∷ A
    k≡k  : Γ ⊢ k ~ k ∷ A

-- Neutral term
record _⊩ne_∷_/_ (Γ : Con Term ℓ) (t A : Term ℓ) ([A] : Γ ⊩ne A) : Set a where
  inductive
  constructor neₜ
  open _⊩ne_ [A]
  field
    k   : Term ℓ
    d   : Γ ⊢ t :⇒*: k ∷ K
    nf  : Γ ⊩neNf k ∷ K

-- Neutral term equality in WHNF
record _⊩neNf_≡_∷_ (Γ : Con Term ℓ) (k m A : Term ℓ) : Set a where
  inductive
  constructor neNfₜ₌
  field
    neK  : Neutral k
    neM  : Neutral m
    k≡m  : Γ ⊢ k ~ m ∷ A

-- Neutral term equality
record _⊩ne_≡_∷_/_ (Γ : Con Term ℓ) (t u A : Term ℓ) ([A] : Γ ⊩ne A) : Set a where
  constructor neₜ₌
  open _⊩ne_ [A]
  field
    k m : Term ℓ
    d   : Γ ⊢ t :⇒*: k ∷ K
    d′  : Γ ⊢ u :⇒*: m ∷ K
    nf  : Γ ⊩neNf k ≡ m ∷ K

-- Reducibility of natural numbers:

-- Natural number type
_⊩ℕ_ : (Γ : Con Term ℓ) (A : Term ℓ) → Set a
Γ ⊩ℕ A = Γ ⊢ A :⇒*: ℕ

-- Natural number type equality
_⊩ℕ_≡_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Set a
Γ ⊩ℕ A ≡ B = Γ ⊢ B ⇒* ℕ

mutual
  -- Natural number term
  record _⊩ℕ_∷ℕ (Γ : Con Term ℓ) (t : Term ℓ) : Set a where
    inductive
    constructor ℕₜ
    field
      n : Term ℓ
      d : Γ ⊢ t :⇒*: n ∷ ℕ
      n≡n : Γ ⊢ n ≅ n ∷ ℕ
      prop : Natural-prop Γ n

  -- WHNF property of natural number terms
  data Natural-prop (Γ : Con Term ℓ) : (n : Term ℓ) → Set a where
    sucᵣ  : ∀ {n} → Γ ⊩ℕ n ∷ℕ → Natural-prop Γ (suc n)
    zeroᵣ : Natural-prop Γ zero
    ne    : ∀ {n} → Γ ⊩neNf n ∷ ℕ → Natural-prop Γ n

mutual
  -- Natural number term equality
  record _⊩ℕ_≡_∷ℕ (Γ : Con Term ℓ) (t u : Term ℓ) : Set a where
    inductive
    constructor ℕₜ₌
    field
      k k′ : Term ℓ
      d : Γ ⊢ t :⇒*: k  ∷ ℕ
      d′ : Γ ⊢ u :⇒*: k′ ∷ ℕ
      k≡k′ : Γ ⊢ k ≅ k′ ∷ ℕ
      prop : [Natural]-prop Γ k k′

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term ℓ) : (n n′ : Term ℓ) → Set a where
    sucᵣ  : ∀ {n n′} → Γ ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ (suc n) (suc n′)
    zeroᵣ : [Natural]-prop Γ zero zero
    ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ ℕ → [Natural]-prop Γ n n′

-- Natural extraction from term WHNF property
natural : ∀ {n} → Natural-prop Γ n → Natural n
natural (sucᵣ x) = sucₙ
natural zeroᵣ = zeroₙ
natural (ne (neNfₜ neK ⊢k k≡k)) = ne neK

-- Natural extraction from term equality WHNF property
split : ∀ {a b} → [Natural]-prop Γ a b → Natural a × Natural b
split (sucᵣ x) = sucₙ , sucₙ
split zeroᵣ = zeroₙ , zeroₙ
split (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM

-- Reducibility of Empty

-- Empty type
_⊩Empty_ : (Γ : Con Term ℓ) (A : Term ℓ) → Set a
Γ ⊩Empty A = Γ ⊢ A :⇒*: Empty

-- Empty type equality
_⊩Empty_≡_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Set a
Γ ⊩Empty A ≡ B = Γ ⊢ B ⇒* Empty

-- WHNF property of absurd terms
data Empty-prop (Γ : Con Term ℓ) : (n : Term ℓ) → Set a where
  ne    : ∀ {n} → Γ ⊩neNf n ∷ Empty → Empty-prop Γ n

-- Empty term
record _⊩Empty_∷Empty (Γ : Con Term ℓ) (t : Term ℓ) : Set a where
  inductive
  constructor Emptyₜ
  field
    n : Term ℓ
    d : Γ ⊢ t :⇒*: n ∷ Empty
    n≡n : Γ ⊢ n ≅ n ∷ Empty
    prop : Empty-prop Γ n

data [Empty]-prop (Γ : Con Term ℓ) : (n n′ : Term ℓ) → Set a where
  ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ Empty → [Empty]-prop Γ n n′

-- Empty term equality
record _⊩Empty_≡_∷Empty (Γ : Con Term ℓ) (t u : Term ℓ) : Set a where
  inductive
  constructor Emptyₜ₌
  field
    k k′ : Term ℓ
    d : Γ ⊢ t :⇒*: k  ∷ Empty
    d′ : Γ ⊢ u :⇒*: k′ ∷ Empty
    k≡k′ : Γ ⊢ k ≅ k′ ∷ Empty
    prop : [Empty]-prop Γ k k′

empty : ∀ {n} → Empty-prop Γ n → Neutral n
empty (ne (neNfₜ neK _ _)) = neK

esplit : ∀ {a b} → [Empty]-prop Γ a b → Neutral a × Neutral b
esplit (ne (neNfₜ₌ neK neM k≡m)) = neK , neM

-- Reducibility of Unit

-- Unit type
record _⊩Unit⟨_⟩_ (Γ : Con Term ℓ) (s : Strength) (A : Term ℓ) : Set a where
  no-eta-equality
  pattern
  constructor Unitₜ
  field
    ⇒*-Unit : Γ ⊢ A :⇒*: Unit s
    ok      : Unit-allowed s

-- Unit type equality
_⊩Unit⟨_⟩_≡_ : (Γ : Con Term ℓ) (s : Strength) (A B : Term ℓ) → Set a
Γ ⊩Unit⟨ s ⟩ A ≡ B = Γ ⊢ B ⇒* Unit s

data Unit-prop (Γ : Con Term ℓ) (s : Strength) : (t : Term ℓ) → Set a where
  starᵣ : Unit-prop Γ s (star s)
  ne : ∀ {n} → Γ ⊩neNf n ∷ Unit s → Unit-prop Γ s n

record _⊩Unit⟨_⟩_∷Unit (Γ : Con Term ℓ) (s : Strength) (t : Term ℓ) : Set a where
  inductive
  constructor Unitₜ
  field
    n : Term ℓ
    d : Γ ⊢ t :⇒*: n ∷ Unit s
    n≡n : Γ ⊢ n ≅ n ∷ Unit s
    prop : Unit-prop Γ s n

-- Unit term equality

record _⊩Unitˢ_≡_∷Unit (Γ : Con Term ℓ) (t u : Term ℓ) : Set a where
  inductive
  constructor Unitₜ₌
  field
    ⊢t : Γ ⊢ t ∷ Unitˢ
    ⊢u : Γ ⊢ u ∷ Unitˢ

data [Unitʷ]-prop (Γ : Con Term ℓ) : (t u : Term ℓ) → Set a where
  starᵣ : [Unitʷ]-prop Γ starʷ starʷ
  ne : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ Unitʷ → [Unitʷ]-prop Γ n n′

unit : ∀ {s a} → Unit-prop Γ s a → Whnf a
unit starᵣ = starₙ
unit (ne (neNfₜ neK ⊢k k≡k)) = ne neK

usplit : ∀ {a b} → [Unitʷ]-prop Γ a b → Whnf a × Whnf b
usplit starᵣ = starₙ , starₙ
usplit (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM

record _⊩Unitʷ_≡_∷Unit (Γ : Con Term ℓ) (t u : Term ℓ) : Set a where
  inductive
  constructor Unitₜ₌
  field
    k k′ : Term ℓ
    d : Γ ⊢ t :⇒*: k  ∷ Unitʷ
    d′ : Γ ⊢ u :⇒*: k′ ∷ Unitʷ
    k≡k′ : Γ ⊢ k ≅ k′ ∷ Unitʷ
    prop : [Unitʷ]-prop Γ k k′

_⊩Unit⟨_⟩_≡_∷Unit : (Γ : Con Term ℓ) (s : Strength) (t u : Term ℓ) → Set a
Γ ⊩Unit⟨ 𝕤 ⟩ t ≡ u ∷Unit = Γ ⊩Unitˢ t ≡ u ∷Unit
Γ ⊩Unit⟨ 𝕨 ⟩ t ≡ u ∷Unit = Γ ⊩Unitʷ t ≡ u ∷Unit

-- Type levels

data TypeLevel : Set where
  ⁰  : TypeLevel
  ¹′ : (ℓ : TypeLevel) → ℓ PE.≡ ⁰ → TypeLevel

pattern ¹ = ¹′ ⁰ PE.refl

private variable
  l : TypeLevel

data _<_ : (i j : TypeLevel) → Set where
  0<1 : ⁰ < ¹

-- Ordering of type levels.

data _≤_ (l : TypeLevel) : TypeLevel → Set where
  refl : l ≤ l
  emb  : ∀ {l′} → l < l′ → l ≤ l′

-- Logical relation
-- Exported interface
record LogRelKit : Set (lsuc a) where
  constructor Kit
  field
    _⊩U : (Γ : Con Term ℓ) → Set a
    _⊩B⟨_⟩_ : (Γ : Con Term ℓ) (W : BindingType) → Term ℓ → Set a
    _⊩Id_ : Con Term ℓ → Term ℓ → Set a

    _⊩_ : (Γ : Con Term ℓ) → Term ℓ → Set a
    _⊩_≡_/_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Γ ⊩ A → Set a
    _⊩_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ A → Set a
    _⊩_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ A → Set a

module LogRel (l : TypeLevel) (rec : ∀ {l′} → l′ < l → LogRelKit) where

  -- Reducibility of Universe:

  -- Universe type
  record _⊩₁U (Γ : Con Term ℓ) : Set a where
    constructor Uᵣ
    field
      l′ : TypeLevel
      l< : l′ < l
      ⊢Γ : ⊢ Γ

  -- Universe type equality
  _⊩₁U≡_ : (Γ : Con Term ℓ) (B : Term ℓ) → Set a
  Γ ⊩₁U≡ B = B PE.≡ U -- Note lack of reduction

  -- Universe term
  record _⊩₁U_∷U/_ {l′} (Γ : Con Term ℓ) (t : Term ℓ) (l< : l′ < l) : Set a where
    constructor Uₜ
    open LogRelKit (rec l<)
    field
      A     : Term ℓ
      d     : Γ ⊢ t :⇒*: A ∷ U
      typeA : Type A
      A≡A   : Γ ⊢ A ≅ A ∷ U
      [t]   : Γ ⊩ t

  -- Universe term equality
  record _⊩₁U_≡_∷U/_ {l′} (Γ : Con Term ℓ) (t u : Term ℓ) (l< : l′ < l) : Set a where
    constructor Uₜ₌
    open LogRelKit (rec l<)
    field
      A B   : Term ℓ
      d     : Γ ⊢ t :⇒*: A ∷ U
      d′    : Γ ⊢ u :⇒*: B ∷ U
      typeA : Type A
      typeB : Type B
      A≡B   : Γ ⊢ A ≅ B ∷ U
      [t]   : Γ ⊩ t
      [u]   : Γ ⊩ u
      [t≡u] : Γ ⊩ t ≡ u / [t]

  mutual

    -- Reducibility of Binding types (Π, Σ):

    -- B-type
    record _⊩ₗB⟨_⟩_ (Γ : Con Term ℓ) (W : BindingType) (A : Term ℓ) : Set a where
      inductive
      constructor Bᵣ
      eta-equality
      field
        F : Term ℓ
        G : Term (1+ ℓ)
        D : Γ ⊢ A :⇒*: ⟦ W ⟧ F ▹ G
        ⊢F : Γ ⊢ F
        ⊢G : Γ ∙ F ⊢ G
        A≡A : Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F ▹ G
        [F] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} → ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊩ₗ U.wk ρ F
        [G] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a : Term m}
            → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ
            → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀
        G-ext : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩ₗ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩ₗ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ
              → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀ ≡ U.wk (lift ρ) G [ b ]₀ / [G] [ρ] ⊢Δ [a]
        ok : BindingType-allowed W

    -- B-type equality
    record _⊩ₗB⟨_⟩_≡_/_ (Γ : Con Term ℓ) (W : BindingType) (A B : Term ℓ) ([A] : Γ ⊩ₗB⟨ W ⟩ A) : Set a where
      inductive
      constructor B₌
      eta-equality
      open _⊩ₗB⟨_⟩_ [A]
      field
        F′     : Term ℓ
        G′     : Term (1+ ℓ)
        D′     : Γ ⊢ B ⇒* ⟦ W ⟧ F′ ▹ G′
        A≡B    : Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F′ ▹ G′
        [F≡F′] : {m : Nat} {ρ : Wk m ℓ} {Δ : Con Term m}
               → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩ₗ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a}
               → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
               → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀ ≡ U.wk (lift ρ) G′ [ a ]₀ / [G] [ρ] ⊢Δ [a]

    -- Term reducibility of Π-type
    _⊩ₗΠ_∷_/_ : {ℓ : Nat} {p q : Mod} (Γ : Con Term ℓ) (t A : Term ℓ) ([A] : Γ ⊩ₗB⟨ BΠ p q ⟩ A) → Set a
    _⊩ₗΠ_∷_/_ {ℓ} {p} {q} Γ t A (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π p , q ▷ F ▹ G
            × Function f
            × Γ ⊢ f ≅ f ∷ Π p , q ▷ F ▹ G
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
              ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([b] : Δ ⊩ₗ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([a≡b] : Δ ⊩ₗ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩ₗ U.wk ρ f ∘⟨ p ⟩ a ≡ U.wk ρ f ∘⟨ p ⟩ b ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩ₗ U.wk ρ f ∘⟨ p ⟩ a ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
              {- NOTE(WN): Last 2 fields could be refactored to a single forall.
                           But touching this definition is painful, so only do it
                           if you have to change it anyway. -}
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- Term equality of Π-type
    _⊩ₗΠ_≡_∷_/_ : {ℓ : Nat} {p q : Mod} (Γ : Con Term ℓ) (t u A : Term ℓ) ([A] : Γ ⊩ₗB⟨ BΠ p q ⟩ A) → Set a
    _⊩ₗΠ_≡_∷_/_
      {ℓ} {p} {q} Γ t u A [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃₂ λ f g → Γ ⊢ t :⇒*: f ∷ Π p , q ▷ F ▹ G
               × Γ ⊢ u :⇒*: g ∷ Π p , q ▷ F ▹ G
               × Function f
               × Function g
               × Γ ⊢ f ≅ g ∷ Π p , q ▷ F ▹ G
               × Γ ⊩ₗΠ t ∷ A / [A]
               × Γ ⊩ₗΠ u ∷ A / [A]
               × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
                 ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
                 → Δ ⊩ₗ U.wk ρ f ∘⟨ p ⟩ a ≡ U.wk ρ g ∘⟨ p ⟩ a ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.


    -- Term reducibility of Σ-type
    _⊩ₗΣ_∷_/_ :
      {p q : Mod} {m : Strength} (Γ : Con Term ℓ) (t A : Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Set a
    _⊩ₗΣ_∷_/_
      {p = p} {q = q} {m = m} Γ t A
      [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃ λ u → Γ ⊢ t :⇒*: u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
            × Γ ⊢ u ≅ u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
            × Σ (Product u) λ pProd
            → Σ-prop m u Γ [A] pProd

    Σ-prop : ∀ {A p q} (m : Strength) (t : Term ℓ) → (Γ : Con Term ℓ)
           → ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → (Product t) → Set a
    Σ-prop {p = p} 𝕤 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) _ =
      Σ (Γ ⊩ₗ fst p t ∷ U.wk id F / [F] id (wf ⊢F)) λ [fst] →
      Γ ⊩ₗ snd p t ∷ U.wk (lift id) G [ fst p t ]₀ /
        [G] id (wf ⊢F) [fst]
    Σ-prop
      {p = p} 𝕨 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {p = p′} {t = p₁} {u = p₂} {m = m}) =
           p PE.≡ p′ ×
           Σ (Γ ⊩ₗ p₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [p₁]
           → Γ ⊩ₗ p₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁]
           × m PE.≡ 𝕨
    Σ-prop
      {p = p} {q = q}
      𝕨 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) (ne x) =
      Γ ⊢ t ~ t ∷ Σʷ p , q ▷ F ▹ G

    -- Term equality of Σ-type
    _⊩ₗΣ_≡_∷_/_ :
      {p q : Mod} {m : Strength} (Γ : Con Term ℓ) (t u A : Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Set a
    _⊩ₗΣ_≡_∷_/_
      {p = p} {q = q} {m} Γ t u A
      [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃₂ λ t′ u′ → Γ ⊢ t :⇒*: t′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊢ u :⇒*: u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊢ t′ ≅ u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊩ₗΣ t ∷ A / [A]
                 × Γ ⊩ₗΣ u ∷ A / [A]
                 × Σ (Product t′) λ pProd
                 → Σ (Product u′) λ rProd
                 → [Σ]-prop m t′ u′ Γ [A] pProd rProd

    [Σ]-prop :
      ∀ {A p q} (m : Strength) (t r : Term ℓ) (Γ : Con Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Product t → Product r → Set a
    [Σ]-prop {p = p} 𝕤 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) _ _ =
      Σ (Γ ⊩ₗ fst p t ∷ U.wk id F / [F] id (wf ⊢F)) λ [fstp]
      → Γ ⊩ₗ fst p r ∷ U.wk id F / [F] id (wf ⊢F)
      × Γ ⊩ₗ fst p t ≡ fst p r ∷ U.wk id F / [F] id (wf ⊢F)
      × Γ ⊩ₗ snd p t ≡ snd p r ∷ U.wk (lift id) G [ fst p t ]₀
        / [G] id (wf ⊢F) [fstp]
    [Σ]-prop
      {p = p} 𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {p = p′} {t = p₁} {u = p₂})
      (prodₙ {p = p″} {t = r₁} {u = r₂}) =
             p PE.≡ p′ × p PE.≡ p″ ×
             Σ (Γ ⊩ₗ p₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [p₁] →
             Σ (Γ ⊩ₗ r₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [r₁]
             → (Γ ⊩ₗ p₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁])
             × (Γ ⊩ₗ r₂ ∷ U.wk (lift id) G [ r₁ ]₀ / [G] id (wf ⊢F) [r₁])
             × (Γ ⊩ₗ p₁ ≡ r₁ ∷ U.wk id F / [F] id (wf ⊢F))
             × (Γ ⊩ₗ p₂ ≡ r₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁])
    [Σ]-prop
      𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {t = p₁} {u = p₂}) (ne y) =
      Lift a ⊥
    [Σ]-prop
      𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
      (ne x) (prodₙ {t = r₁} {u = r₂}) =
      Lift a ⊥
    [Σ]-prop
      {p = p} {q = q} 𝕨 t r Γ
      (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) (ne x) (ne y) =
        Γ ⊢ t ~ r ∷ Σʷ p , q ▷ F ▹ G

    -- Reducibility for identity types.

    -- Well-formed identity types.
    record _⊩ₗId_ (Γ : Con Term ℓ) (A : Term ℓ) : Set a where
      inductive
      constructor Idᵣ
      eta-equality
      field
        Ty lhs rhs : Term ℓ
        ⇒*Id       : Γ ⊢ A :⇒*: Id Ty lhs rhs
        ⊩Ty        : Γ ⊩ₗ Ty
        ⊩lhs       : Γ ⊩ₗ lhs ∷ Ty / ⊩Ty
        ⊩rhs       : Γ ⊩ₗ rhs ∷ Ty / ⊩Ty

    -- Well-formed identity type equality.
    record _⊩ₗId_≡_/_
      (Γ : Con Term ℓ) (A B : Term ℓ) (⊩A : Γ ⊩ₗId A) : Set a where
      inductive
      constructor Id₌
      eta-equality

      open _⊩ₗId_ ⊩A

      field
        Ty′ lhs′ rhs′ : Term ℓ
        ⇒*Id′         : Γ ⊢ B :⇒*: Id Ty′ lhs′ rhs′
        Ty≡Ty′        : Γ ⊩ₗ Ty ≡ Ty′ / ⊩Ty
        lhs≡lhs′      : Γ ⊩ₗ lhs ≡ lhs′ ∷ Ty / ⊩Ty
        rhs≡rhs′      : Γ ⊩ₗ rhs ≡ rhs′ ∷ Ty / ⊩Ty

        -- The fact that the types of the following two fields are
        -- inhabited follows from symmetry, transitivity and the
        -- previous two fields, see
        -- Definition.LogicalRelation.Properties.Transitivity.Id₌′.
        -- The fields are used in
        -- Definition.LogicalRelation.Properties.Conversion, which is
        -- imported from
        -- Definition.LogicalRelation.Properties.Transitivity.
        lhs≡rhs→lhs′≡rhs′ : Γ ⊩ₗ lhs  ≡ rhs  ∷ Ty / ⊩Ty →
                            Γ ⊩ₗ lhs′ ≡ rhs′ ∷ Ty / ⊩Ty
        lhs′≡rhs′→lhs≡rhs : Γ ⊩ₗ lhs′ ≡ rhs′ ∷ Ty / ⊩Ty →
                            Γ ⊩ₗ lhs  ≡ rhs  ∷ Ty / ⊩Ty

    -- Well-formed identity terms.
    _⊩ₗId_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ₗId A → Set a
    Γ ⊩ₗId t ∷ A / ⊩A =
      ∃ λ u →
      Γ ⊢ t :⇒*: u ∷ Id Ty lhs rhs ×
      ∃ λ (u-id : Identity u) →
      case u-id of λ where
        (ne _) → Γ ⊢ u ~ u ∷ Id Ty lhs rhs
        rflₙ   → Γ ⊩ₗ lhs ≡ rhs ∷ Ty / ⊩Ty
      where
      open _⊩ₗId_ ⊩A

    -- Well-formed identity term equality.
    _⊩ₗId_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ₗId A → Set a
    Γ ⊩ₗId t ≡ u ∷ A / ⊩A =
      ∃₂ λ t′ u′ →
      Γ ⊢ t :⇒*: t′ ∷ Id Ty lhs rhs ×
      Γ ⊢ u :⇒*: u′ ∷ Id Ty lhs rhs ×
      ∃ λ (t′-id : Identity t′) →
      ∃ λ (u′-id : Identity u′) →
      Identity-rec t′-id
        (Identity-rec u′-id
           (Γ ⊩ₗ lhs ≡ rhs ∷ Ty / ⊩Ty)
           (Lift _ ⊥))
        (Identity-rec u′-id
           (Lift _ ⊥)
           (Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs))
      where
      open _⊩ₗId_ ⊩A

    -- Logical relation definition
    data _⊩ₗ_ (Γ : Con Term ℓ) : Term ℓ → Set a where
      Uᵣ  : Γ ⊩₁U → Γ ⊩ₗ U
      ℕᵣ  : ∀ {A} → Γ ⊩ℕ A → Γ ⊩ₗ A
      Emptyᵣ : ∀ {A} → Γ ⊩Empty A → Γ ⊩ₗ A
      Unitᵣ : ∀ {A} {s : Strength} → Γ ⊩Unit⟨ s ⟩ A → Γ ⊩ₗ A
      ne  : ∀ {A} → Γ ⊩ne A → Γ ⊩ₗ A
      Bᵣ  : ∀ {A} W → Γ ⊩ₗB⟨ W ⟩ A → Γ ⊩ₗ A
      Idᵣ : ∀ {A} → Γ ⊩ₗId A → Γ ⊩ₗ A
      emb : ∀ {A l′} (l< : l′ < l) (let open LogRelKit (rec l<))
            ([A] : Γ ⊩ A) → Γ ⊩ₗ A

    _⊩ₗ_≡_/_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ A ≡ B / Uᵣ UA = Γ ⊩₁U≡ B
    Γ ⊩ₗ A ≡ B / ℕᵣ D = Γ ⊩ℕ A ≡ B
    Γ ⊩ₗ A ≡ B / Emptyᵣ D = Γ ⊩Empty A ≡ B
    Γ ⊩ₗ A ≡ B / Unitᵣ {s = s} D = Γ ⊩Unit⟨ s ⟩ A ≡ B
    Γ ⊩ₗ A ≡ B / ne neA = Γ ⊩ne A ≡ B / neA
    Γ ⊩ₗ A ≡ B / Bᵣ W BA = Γ ⊩ₗB⟨ W ⟩ A ≡ B / BA
    Γ ⊩ₗ A ≡ B / Idᵣ ⊩A = Γ ⊩ₗId A ≡ B / ⊩A
    Γ ⊩ₗ A ≡ B / emb l< [A] = Γ ⊩ A ≡ B / [A]
      where open LogRelKit (rec l<)

    _⊩ₗ_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ t ∷ .U / Uᵣ (Uᵣ l′ l< ⊢Γ) = Γ ⊩₁U t ∷U/ l<
    Γ ⊩ₗ t ∷ A / ℕᵣ D = Γ ⊩ℕ t ∷ℕ
    Γ ⊩ₗ t ∷ A / Emptyᵣ D = Γ ⊩Empty t ∷Empty
    Γ ⊩ₗ t ∷ A / Unitᵣ {s = s} D = Γ ⊩Unit⟨ s ⟩ t ∷Unit
    Γ ⊩ₗ t ∷ A / ne neA = Γ ⊩ne t ∷ A / neA
    Γ ⊩ₗ t ∷ A / Bᵣ BΠ! ΠA  = Γ ⊩ₗΠ t ∷ A / ΠA
    Γ ⊩ₗ t ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩ₗΣ t ∷ A / ΣA
    Γ ⊩ₗ t ∷ A / Idᵣ ⊩A = Γ ⊩ₗId t ∷ A / ⊩A
    Γ ⊩ₗ t ∷ A / emb l< [A] = Γ ⊩ t ∷ A / [A]
      where open LogRelKit (rec l<)

    _⊩ₗ_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ t ≡ u ∷ .U / Uᵣ (Uᵣ l′ l< ⊢Γ) = Γ ⊩₁U t ≡ u ∷U/ l<
    Γ ⊩ₗ t ≡ u ∷ A / ℕᵣ D = Γ ⊩ℕ t ≡ u ∷ℕ
    Γ ⊩ₗ t ≡ u ∷ A / Emptyᵣ D = Γ ⊩Empty t ≡ u ∷Empty
    Γ ⊩ₗ t ≡ u ∷ A / Unitᵣ {s = s} D = Γ ⊩Unit⟨ s ⟩ t ≡ u ∷Unit
    Γ ⊩ₗ t ≡ u ∷ A / ne neA = Γ ⊩ne t ≡ u ∷ A / neA
    Γ ⊩ₗ t ≡ u ∷ A / Bᵣ BΠ! ΠA = Γ ⊩ₗΠ t ≡ u ∷ A / ΠA
    Γ ⊩ₗ t ≡ u ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩ₗΣ t ≡ u ∷ A / ΣA
    Γ ⊩ₗ t ≡ u ∷ A / Idᵣ ⊩A = Γ ⊩ₗId t ≡ u ∷ A / ⊩A
    Γ ⊩ₗ t ≡ u ∷ A / emb l< [A] = Γ ⊩ t ≡ u ∷ A / [A]
      where open LogRelKit (rec l<)

    kit : LogRelKit
    kit = Kit _⊩₁U _⊩ₗB⟨_⟩_ _⊩ₗId_
              _⊩ₗ_ _⊩ₗ_≡_/_ _⊩ₗ_∷_/_ _⊩ₗ_≡_∷_/_

open LogRel public
  using
    (Uᵣ; ℕᵣ; Emptyᵣ; Unitᵣ; ne; Bᵣ; B₌; Idᵣ; Id₌; emb; Uₜ; Uₜ₌;
     module _⊩₁U; module _⊩₁U_∷U/_; module _⊩₁U_≡_∷U/_;
     module _⊩ₗB⟨_⟩_; module _⊩ₗB⟨_⟩_≡_/_;
     module _⊩ₗId_; module _⊩ₗId_≡_/_)

-- Patterns for the non-records of Π
pattern Πₜ f d funcF f≡f [f] [f]₁ = f , d , funcF , f≡f , [f] , [f]₁
pattern Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g] = f , g , d , d′ , funcF , funcG , f≡g , [f] , [g] , [f≡g]
pattern Σₜ p d p≡p pProd prop =  p , d , p≡p , pProd , prop
pattern Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] prop = p , r , d , d′ , p≅r , [t] , [u] , pProd , rProd , prop

pattern Uᵣ′ a b c = Uᵣ (Uᵣ a b c)
pattern ne′ a b c d = ne (ne a b c d)
pattern Bᵣ′ W a b c d e f g h i j = Bᵣ W (Bᵣ a b c d e f g h i j)
pattern Πᵣ′ a b c d e f g h i j = Bᵣ′ BΠ! a b c d e f g h i j
pattern 𝕨′ a b c d e f g h i j = Bᵣ′ BΣ! a b c d e f g h i j

kit : TypeLevel → LogRelKit
kit ℓ = LogRel.kit ℓ (λ { 0<1 → kit ⁰ })

_⊩′⟨_⟩U : (Γ : Con Term ℓ) (l : TypeLevel) → Set a
Γ ⊩′⟨ l ⟩U = Γ ⊩U where open LogRelKit (kit l)

_⊩′⟨_⟩B⟨_⟩_ : (Γ : Con Term ℓ) (l : TypeLevel) (W : BindingType) → Term ℓ → Set a
Γ ⊩′⟨ l ⟩B⟨ W ⟩ A = Γ ⊩B⟨ W ⟩ A where open LogRelKit (kit l)

_⊩′⟨_⟩Id_ : Con Term ℓ → TypeLevel → Term ℓ → Set a
Γ ⊩′⟨ l ⟩Id A = Γ ⊩Id A
  where
  open LogRelKit (kit l)

-- Reducibility of types

_⊩⟨_⟩_ : (Γ : Con Term ℓ) (l : TypeLevel) → Term ℓ → Set a
Γ ⊩⟨ l ⟩ A = Γ ⊩ A where open LogRelKit (kit l)

-- Equality of reducibile types

_⊩⟨_⟩_≡_/_ : (Γ : Con Term ℓ) (l : TypeLevel) (A B : Term ℓ) → Γ ⊩⟨ l ⟩ A → Set a
Γ ⊩⟨ l ⟩ A ≡ B / [A] = Γ ⊩ A ≡ B / [A] where open LogRelKit (kit l)

-- Reducibility of terms

_⊩⟨_⟩_∷_/_ : (Γ : Con Term ℓ) (l : TypeLevel) (t A : Term ℓ) → Γ ⊩⟨ l ⟩ A → Set a
Γ ⊩⟨ l ⟩ t ∷ A / [A] = Γ ⊩ t ∷ A / [A] where open LogRelKit (kit l)

-- Equality of reducibile terms

_⊩⟨_⟩_≡_∷_/_ : (Γ : Con Term ℓ) (l : TypeLevel) (t u A : Term ℓ) → Γ ⊩⟨ l ⟩ A → Set a
Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] = Γ ⊩ t ≡ u ∷ A / [A] where open LogRelKit (kit l)

------------------------------------------------------------------------
-- Some definitions related to the identity type

-- A view of parts of _⊩ₗId_∷_/_.

data ⊩Id∷-view
  {A : Term ℓ} (⊩A : Γ ⊩′⟨ l ⟩Id A) :
  ∀ t → Identity t → Set a where
  rflᵣ : let open _⊩ₗId_ ⊩A in
         Γ ⊩⟨ l ⟩ lhs ≡ rhs ∷ Ty / ⊩Ty →
         ⊩Id∷-view ⊩A rfl rflₙ
  ne   : let open _⊩ₗId_ ⊩A in
         (u-n : Neutral u) →
         Γ ⊢ u ~ u ∷ Id Ty lhs rhs →
         ⊩Id∷-view ⊩A u (ne u-n)

-- The view is inhabited for well-formed identity terms.

⊩Id∷-view-inhabited :
  ∀ {A} {⊩A : Γ ⊩′⟨ l ⟩Id A}
  ((u , _ , u-id , _) : Γ ⊩⟨ l ⟩ t ∷ A / Idᵣ ⊩A) →
  ⊩Id∷-view ⊩A u u-id
⊩Id∷-view-inhabited = λ where
  (_ , _ , rflₙ , lhs≡rhs) → rflᵣ lhs≡rhs
  (_ , _ , ne u-n , u~u)   → ne u-n u~u

-- A view of parts of _⊩ₗId_≡_∷_/_.

data ⊩Id≡∷-view
  {Γ : Con Term ℓ} (lhs rhs {Ty} : Term ℓ) (⊩Ty : Γ ⊩⟨ l ⟩ Ty) :
  ∀ t → Identity t → ∀ u → Identity u → Set a where
  rfl₌ : (lhs≡rhs : Γ ⊩⟨ l ⟩ lhs ≡ rhs ∷ Ty / ⊩Ty) →
         ⊩Id≡∷-view lhs rhs ⊩Ty rfl rflₙ rfl rflₙ
  ne   : (t′-n : Neutral t′) (u′-n : Neutral u′) →
         Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs →
         ⊩Id≡∷-view lhs rhs ⊩Ty t′ (ne t′-n) u′ (ne u′-n)

-- The view is inhabited for instances of "well-formed identity term
-- equality".

⊩Id≡∷-view-inhabited :
  ∀ {A} {Γ : Con Term ℓ}
  (⊩A : Γ ⊩′⟨ l ⟩Id A) →
  let open _⊩ₗId_ ⊩A in
  ((t′ , u′ , _ , _ , t′-id , u′-id , _) :
   Γ ⊩⟨ l ⟩ t ≡ u ∷ A / Idᵣ ⊩A) →
  ⊩Id≡∷-view lhs rhs ⊩Ty t′ t′-id u′ u′-id
⊩Id≡∷-view-inhabited _ = λ where
  (_ , _ , _ , _ , rflₙ , rflₙ , lhs≡rhs) →
    rfl₌ lhs≡rhs
  (_ , _ , _ , _ , ne t′-n , ne u′-n , t′~u′) →
    ne t′-n u′-n t′~u′
  (_ , _ , _ , _ , rflₙ , ne _ , ())
  (_ , _ , _ , _ , ne _ , rflₙ , ())

-- A kind of constructor for _⊩ₗId_≡_∷_/_.

⊩Id≡∷ :
  ∀ {A} {Γ : Con Term ℓ} {⊩A : Γ ⊩′⟨ l ⟩Id A} →
  let open _⊩ₗId_ ⊩A in
  ((t′ , _ , t′-id , _) : Γ ⊩⟨ l ⟩ t ∷ A / Idᵣ ⊩A)
  ((u′ , _ , u′-id , _) : Γ ⊩⟨ l ⟩ u ∷ A / Idᵣ ⊩A) →
  Identity-rec t′-id
    (Identity-rec u′-id
       (Lift _ ⊤)
       (Lift _ ⊥))
    (Identity-rec u′-id
       (Lift _ ⊥)
       (Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs)) →
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A / Idᵣ ⊩A
⊩Id≡∷ ⊩t@(t′ , t⇒*t′ , t′-id , _) ⊩u@(u′ , u⇒*u′ , u′-id , _) rest =
    t′ , u′ , t⇒*t′ , u⇒*u′ , t′-id , u′-id
  , (case ⊩Id∷-view-inhabited ⊩t of λ where
       (rflᵣ lhs≡rhs) → case ⊩Id∷-view-inhabited ⊩u of λ where
         (rflᵣ _) → lhs≡rhs
         (ne _ _) → case rest of λ ()
       (ne _ _) → case ⊩Id∷-view-inhabited ⊩u of λ where
         (rflᵣ _) → case rest of λ ()
         (ne _ _) → rest)

-- A kind of inverse of ⊩Id≡∷.

⊩Id≡∷⁻¹ :
  ∀ {A} {Γ : Con Term ℓ}
  (⊩A : Γ ⊩′⟨ l ⟩Id A) →
  let open _⊩ₗId_ ⊩A in
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A / Idᵣ ⊩A →
  ∃ λ (⊩t@(t′ , _ , t′-id , _) : Γ ⊩⟨ l ⟩ t ∷ A / Idᵣ ⊩A) →
  ∃ λ (⊩u@(u′ , _ , u′-id , _) : Γ ⊩⟨ l ⟩ u ∷ A / Idᵣ ⊩A) →
  Identity-rec t′-id
    (Identity-rec u′-id
       (Lift _ ⊤)
       (Lift _ ⊥))
    (Identity-rec u′-id
       (Lift _ ⊥)
       (Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs))
⊩Id≡∷⁻¹ ⊩A t≡u@(t′ , u′ , t⇒*t′ , u⇒*u′ , t′-id , u′-id , rest) =
  case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
    (rfl₌ lhs≡rhs) →
        (t′ , t⇒*t′ , t′-id , lhs≡rhs)
      , (u′ , u⇒*u′ , u′-id , lhs≡rhs)
      , _
    (ne _ _ t′~u′) →
        (t′ , t⇒*t′ , t′-id , ~-trans t′~u′ (~-sym t′~u′))
      , (u′ , u⇒*u′ , u′-id , ~-trans (~-sym t′~u′) t′~u′)
      , t′~u′
