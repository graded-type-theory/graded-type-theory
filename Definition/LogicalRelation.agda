------------------------------------------------------------------------
-- The logical relation for reducibility
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions

module Definition.LogicalRelation
  {a} {Mod : Set a}
  (R : Type-restrictions Mod)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped Mod as U hiding (_∷_)
open import Definition.Typed.Properties R
open import Definition.Typed R
open import Definition.Typed.Weakening R

open import Tools.Level
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≈_)

private
  variable
    p q : Mod
    ℓ : Nat
    Γ : Con Term ℓ

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
    K≡K : Γ ⊢ K ~ K ∷ U

-- Neutral type equality
record _⊩ne_≡_/_ (Γ : Con Term ℓ) (A B : Term ℓ) ([A] : Γ ⊩ne A) : Set a where
  constructor ne₌
  open _⊩ne_ [A]
  field
    M   : Term ℓ
    D′  : Γ ⊢ B :⇒*: M
    neM : Neutral M
    K≡M : Γ ⊢ K ~ M ∷ U

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
record _⊩Unit_ (Γ : Con Term ℓ) (A : Term ℓ) : Set a where
  no-eta-equality
  pattern
  constructor Unitₜ
  field
    ⇒*-Unit : Γ ⊢ A :⇒*: Unit
    ok      : Unit-allowed

-- Unit type equality
_⊩Unit_≡_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Set a
Γ ⊩Unit A ≡ B = Γ ⊢ B ⇒* Unit

record _⊩Unit_∷Unit (Γ : Con Term ℓ) (t : Term ℓ) : Set a where
  inductive
  constructor Unitₜ
  field
    n : Term ℓ
    d : Γ ⊢ t :⇒*: n ∷ Unit
    prop : Whnf n

-- Unit term equality
record _⊩Unit_≡_∷Unit (Γ : Con Term ℓ) (t u : Term ℓ) : Set a where
  constructor Unitₜ₌
  field
    ⊢t : Γ ⊢ t ∷ Unit
    ⊢u : Γ ⊢ u ∷ Unit

-- Type levels

data TypeLevel : Set where
  ⁰ : TypeLevel
  ¹ : TypeLevel

data _<_ : (i j : TypeLevel) → Set where
  0<1 : ⁰ < ¹

-- Logical relation
-- Exported interface
record LogRelKit : Set (lsuc a) where
  constructor Kit
  field
    _⊩U : (Γ : Con Term ℓ) → Set a
    _⊩B⟨_⟩_ : (Γ : Con Term ℓ) (W : BindingType) → Term ℓ → Set a

    _⊩_ : (Γ : Con Term ℓ) → Term ℓ → Set a
    _⊩_≡_/_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Γ ⊩ A → Set a
    _⊩_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ A → Set a
    _⊩_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ A → Set a

module LogRel (l : TypeLevel) (rec : ∀ {l′} → l′ < l → LogRelKit) where

  -- Reducibility of Universe:

  -- Universe type
  record _⊩¹U (Γ : Con Term ℓ) : Set a where
    constructor Uᵣ
    field
      l′ : TypeLevel
      l< : l′ < l
      ⊢Γ : ⊢ Γ

  -- Universe type equality
  _⊩¹U≡_ : (Γ : Con Term ℓ) (B : Term ℓ) → Set a
  Γ ⊩¹U≡ B = B PE.≡ U -- Note lack of reduction

  -- Universe term
  record _⊩¹U_∷U/_ {l′} (Γ : Con Term ℓ) (t : Term ℓ) (l< : l′ < l) : Set a where
    constructor Uₜ
    open LogRelKit (rec l<)
    field
      A     : Term ℓ
      d     : Γ ⊢ t :⇒*: A ∷ U
      typeA : Type A
      A≡A   : Γ ⊢ A ≅ A ∷ U
      [t]   : Γ ⊩ t

  -- Universe term equality
  record _⊩¹U_≡_∷U/_ {l′} (Γ : Con Term ℓ) (t u : Term ℓ) (l< : l′ < l) : Set a where
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
    record _⊩¹B⟨_⟩_ (Γ : Con Term ℓ) (W : BindingType) (A : Term ℓ) : Set a where
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
        [F] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} → ρ ∷ Δ ⊆ Γ → ⊢ Δ → Δ ⊩¹ U.wk ρ F
        [G] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a : Term m}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ
            → Δ ⊩¹ U.wk (lift ρ) G [ a ]₀
        G-ext : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩¹ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ
              → Δ ⊩¹ U.wk (lift ρ) G [ a ]₀ ≡ U.wk (lift ρ) G [ b ]₀ / [G] [ρ] ⊢Δ [a]
        ok : BindingType-allowed W

    -- B-type equality
    record _⊩¹B⟨_⟩_≡_/_ (Γ : Con Term ℓ) (W : BindingType) (A B : Term ℓ) ([A] : Γ ⊩¹B⟨ W ⟩ A) : Set a where
      inductive
      constructor B₌
      eta-equality
      open _⊩¹B⟨_⟩_ [A]
      field
        F′     : Term ℓ
        G′     : Term (1+ ℓ)
        D′     : Γ ⊢ B ⇒* ⟦ W ⟧ F′ ▹ G′
        A≡B    : Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F′ ▹ G′
        [F≡F′] : {m : Nat} {ρ : Wk m ℓ} {Δ : Con Term m}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩¹ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
               → Δ ⊩¹ U.wk (lift ρ) G [ a ]₀ ≡ U.wk (lift ρ) G′ [ a ]₀ / [G] [ρ] ⊢Δ [a]

    -- Term reducibility of Π-type
    _⊩¹Π_∷_/_ : {ℓ : Nat} {p q : Mod} (Γ : Con Term ℓ) (t A : Term ℓ) ([A] : Γ ⊩¹B⟨ BΠ p q ⟩ A) → Set a
    _⊩¹Π_∷_/_ {ℓ} {p} {q} Γ t A (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π p , q ▷ F ▹ G
            × Function f
            × Γ ⊢ f ≅ f ∷ Π p , q ▷ F ▹ G
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([b] : Δ ⊩¹ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([a≡b] : Δ ⊩¹ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘⟨ p ⟩ a ≡ U.wk ρ f ∘⟨ p ⟩ b ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘⟨ p ⟩ a ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
              {- NOTE(WN): Last 2 fields could be refactored to a single forall.
                           But touching this definition is painful, so only do it
                           if you have to change it anyway. -}
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- Term equality of Π-type
    _⊩¹Π_≡_∷_/_ : {ℓ : Nat} {p q : Mod} (Γ : Con Term ℓ) (t u A : Term ℓ) ([A] : Γ ⊩¹B⟨ BΠ p q ⟩ A) → Set a
    _⊩¹Π_≡_∷_/_
      {ℓ} {p} {q} Γ t u A [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃₂ λ f g → Γ ⊢ t :⇒*: f ∷ Π p , q ▷ F ▹ G
               × Γ ⊢ u :⇒*: g ∷ Π p , q ▷ F ▹ G
               × Function f
               × Function g
               × Γ ⊢ f ≅ g ∷ Π p , q ▷ F ▹ G
               × Γ ⊩¹Π t ∷ A / [A]
               × Γ ⊩¹Π u ∷ A / [A]
               × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                 ([a] : Δ ⊩¹ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
                 → Δ ⊩¹ U.wk ρ f ∘⟨ p ⟩ a ≡ U.wk ρ g ∘⟨ p ⟩ a ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.


    -- Term reducibility of Σ-type
    _⊩¹Σ_∷_/_ :
      {p q : Mod} {m : SigmaMode} (Γ : Con Term ℓ) (t A : Term ℓ)
      ([A] : Γ ⊩¹B⟨ BΣ m p q ⟩ A) → Set a
    _⊩¹Σ_∷_/_
      {p = p} {q = q} {m = m} Γ t A
      [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃ λ u → Γ ⊢ t :⇒*: u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
            × Γ ⊢ u ≅ u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
            × Σ (Product u) λ pProd
            → Σ-prop m u Γ [A] pProd

    Σ-prop : ∀ {A p q} (m : SigmaMode) (t : Term ℓ) → (Γ : Con Term ℓ)
           → ([A] : Γ ⊩¹B⟨ BΣ m p q ⟩ A) → (Product t) → Set a
    Σ-prop {p = p} Σₚ t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) _ =
      Σ (Γ ⊩¹ fst p t ∷ U.wk id F / [F] id (wf ⊢F)) λ [fst] →
      Γ ⊩¹ snd p t ∷ U.wk (lift id) G [ fst p t ]₀ /
        [G] id (wf ⊢F) [fst]
    Σ-prop
      {p = p} Σᵣ t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {p = p′} {t = p₁} {u = p₂} {m = m}) =
           p ≈ p′ ×
           Σ (Γ ⊩¹ p₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [p₁]
           → Γ ⊩¹ p₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁]
           × m PE.≡ Σᵣ
    Σ-prop
      {p = p} {q = q}
      Σᵣ t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) (ne x) =
      Γ ⊢ t ~ t ∷ Σᵣ p , q ▷ F ▹ G

    -- Term equality of Σ-type
    _⊩¹Σ_≡_∷_/_ :
      {p q : Mod} {m : SigmaMode} (Γ : Con Term ℓ) (t u A : Term ℓ)
      ([A] : Γ ⊩¹B⟨ BΣ m p q ⟩ A) → Set a
    _⊩¹Σ_≡_∷_/_
      {p = p} {q = q} {m} Γ t u A
      [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃₂ λ t′ u′ → Γ ⊢ t :⇒*: t′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊢ u :⇒*: u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊢ t′ ≅ u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊩¹Σ t ∷ A / [A]
                 × Γ ⊩¹Σ u ∷ A / [A]
                 × Σ (Product t′) λ pProd
                 → Σ (Product u′) λ rProd
                 → [Σ]-prop m t′ u′ Γ [A] pProd rProd

    [Σ]-prop :
      ∀ {A p q} (m : SigmaMode) (t r : Term ℓ) (Γ : Con Term ℓ)
      ([A] : Γ ⊩¹B⟨ BΣ m p q ⟩ A) → Product t → Product r → Set a
    [Σ]-prop {p = p} Σₚ t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) _ _ =
      Σ (Γ ⊩¹ fst p t ∷ U.wk id F / [F] id (wf ⊢F)) λ [fstp]
      → Γ ⊩¹ fst p r ∷ U.wk id F / [F] id (wf ⊢F)
      × Γ ⊩¹ fst p t ≡ fst p r ∷ U.wk id F / [F] id (wf ⊢F)
      × Γ ⊩¹ snd p t ≡ snd p r ∷ U.wk (lift id) G [ fst p t ]₀
        / [G] id (wf ⊢F) [fstp]
    [Σ]-prop
      {p = p} Σᵣ t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {p = p′} {t = p₁} {u = p₂})
      (prodₙ {p = p″} {t = r₁} {u = r₂}) =
             p ≈ p′ × p ≈ p″ ×
             Σ (Γ ⊩¹ p₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [p₁] →
             Σ (Γ ⊩¹ r₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [r₁]
             → (Γ ⊩¹ p₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁])
             × (Γ ⊩¹ r₂ ∷ U.wk (lift id) G [ r₁ ]₀ / [G] id (wf ⊢F) [r₁])
             × (Γ ⊩¹ p₁ ≡ r₁ ∷ U.wk id F / [F] id (wf ⊢F))
             × (Γ ⊩¹ p₂ ≡ r₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁])
    [Σ]-prop
      Σᵣ t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {t = p₁} {u = p₂}) (ne y) =
      Lift a PE.⊥
    [Σ]-prop
      Σᵣ t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
      (ne x) (prodₙ {t = r₁} {u = r₂}) =
      Lift a PE.⊥
    [Σ]-prop
      {p = p} {q = q} Σᵣ t r Γ
      (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) (ne x) (ne y) =
        Γ ⊢ t ~ r ∷ Σᵣ p , q ▷ F ▹ G

    -- Logical relation definition
    data _⊩¹_ (Γ : Con Term ℓ) : Term ℓ → Set a where
      Uᵣ  : Γ ⊩¹U → Γ ⊩¹ U
      ℕᵣ  : ∀ {A} → Γ ⊩ℕ A → Γ ⊩¹ A
      Emptyᵣ : ∀ {A} → Γ ⊩Empty A → Γ ⊩¹ A
      Unitᵣ : ∀ {A} → Γ ⊩Unit A → Γ ⊩¹ A
      ne  : ∀ {A} → Γ ⊩ne A → Γ ⊩¹ A
      Bᵣ  : ∀ {A} W → Γ ⊩¹B⟨ W ⟩ A → Γ ⊩¹ A
      emb : ∀ {A l′} (l< : l′ < l) (let open LogRelKit (rec l<))
            ([A] : Γ ⊩ A) → Γ ⊩¹ A

    _⊩¹_≡_/_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Γ ⊩¹ A → Set a
    Γ ⊩¹ A ≡ B / Uᵣ UA = Γ ⊩¹U≡ B
    Γ ⊩¹ A ≡ B / ℕᵣ D = Γ ⊩ℕ A ≡ B
    Γ ⊩¹ A ≡ B / Emptyᵣ D = Γ ⊩Empty A ≡ B
    Γ ⊩¹ A ≡ B / Unitᵣ D = Γ ⊩Unit A ≡ B
    Γ ⊩¹ A ≡ B / ne neA = Γ ⊩ne A ≡ B / neA
    Γ ⊩¹ A ≡ B / Bᵣ W BA = Γ ⊩¹B⟨ W ⟩ A ≡ B / BA
    Γ ⊩¹ A ≡ B / emb l< [A] = Γ ⊩ A ≡ B / [A]
      where open LogRelKit (rec l<)

    _⊩¹_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩¹ A → Set a
    Γ ⊩¹ t ∷ .U / Uᵣ (Uᵣ l′ l< ⊢Γ) = Γ ⊩¹U t ∷U/ l<
    Γ ⊩¹ t ∷ A / ℕᵣ D = Γ ⊩ℕ t ∷ℕ
    Γ ⊩¹ t ∷ A / Emptyᵣ D = Γ ⊩Empty t ∷Empty
    Γ ⊩¹ t ∷ A / Unitᵣ D = Γ ⊩Unit t ∷Unit
    Γ ⊩¹ t ∷ A / ne neA = Γ ⊩ne t ∷ A / neA
    Γ ⊩¹ t ∷ A / Bᵣ BΠ! ΠA  = Γ ⊩¹Π t ∷ A / ΠA
    Γ ⊩¹ t ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩¹Σ t ∷ A / ΣA
    Γ ⊩¹ t ∷ A / emb l< [A] = Γ ⊩ t ∷ A / [A]
      where open LogRelKit (rec l<)

    _⊩¹_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩¹ A → Set a
    Γ ⊩¹ t ≡ u ∷ .U / Uᵣ (Uᵣ l′ l< ⊢Γ) = Γ ⊩¹U t ≡ u ∷U/ l<
    Γ ⊩¹ t ≡ u ∷ A / ℕᵣ D = Γ ⊩ℕ t ≡ u ∷ℕ
    Γ ⊩¹ t ≡ u ∷ A / Emptyᵣ D = Γ ⊩Empty t ≡ u ∷Empty
    Γ ⊩¹ t ≡ u ∷ A / Unitᵣ D = Γ ⊩Unit t ≡ u ∷Unit
    Γ ⊩¹ t ≡ u ∷ A / ne neA = Γ ⊩ne t ≡ u ∷ A / neA
    Γ ⊩¹ t ≡ u ∷ A / Bᵣ BΠ! ΠA = Γ ⊩¹Π t ≡ u ∷ A / ΠA
    Γ ⊩¹ t ≡ u ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩¹Σ t ≡ u ∷ A / ΣA
    Γ ⊩¹ t ≡ u ∷ A / emb l< [A] = Γ ⊩ t ≡ u ∷ A / [A]
      where open LogRelKit (rec l<)

    kit : LogRelKit
    kit = Kit _⊩¹U _⊩¹B⟨_⟩_
              _⊩¹_ _⊩¹_≡_/_ _⊩¹_∷_/_ _⊩¹_≡_∷_/_

open LogRel public using (Uᵣ; ℕᵣ; Emptyᵣ; Unitᵣ; ne; Bᵣ; B₌; emb; Uₜ; Uₜ₌)

-- Patterns for the non-records of Π
pattern Πₜ f d funcF f≡f [f] [f]₁ = f , d , funcF , f≡f , [f] , [f]₁
pattern Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g] = f , g , d , d′ , funcF , funcG , f≡g , [f] , [g] , [f≡g]
pattern Σₜ p d p≡p pProd prop =  p , d , p≡p , pProd , prop
pattern Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] prop = p , r , d , d′ , p≅r , [t] , [u] , pProd , rProd , prop

pattern Uᵣ′ a b c = Uᵣ (Uᵣ a b c)
pattern ne′ a b c d = ne (ne a b c d)
pattern Bᵣ′ W a b c d e f g h i j = Bᵣ W (Bᵣ a b c d e f g h i j)
pattern Πᵣ′ a b c d e f g h i j = Bᵣ′ BΠ! a b c d e f g h i j
pattern Σᵣ′ a b c d e f g h i j = Bᵣ′ BΣ! a b c d e f g h i j

logRelRec : ∀ l {l′} → l′ < l → LogRelKit
logRelRec ⁰ = λ ()
logRelRec ¹ 0<1 = LogRel.kit ⁰ (λ ())

kit : ∀ (i : TypeLevel) → LogRelKit
kit l = LogRel.kit l (logRelRec l)
-- a bit of repetition in "kit ¹" definition, would work better with Fin 2 for
-- TypeLevel because you could recurse.

_⊩′⟨_⟩U : (Γ : Con Term ℓ) (l : TypeLevel) → Set a
Γ ⊩′⟨ l ⟩U = Γ ⊩U where open LogRelKit (kit l)

_⊩′⟨_⟩B⟨_⟩_ : (Γ : Con Term ℓ) (l : TypeLevel) (W : BindingType) → Term ℓ → Set a
Γ ⊩′⟨ l ⟩B⟨ W ⟩ A = Γ ⊩B⟨ W ⟩ A where open LogRelKit (kit l)

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
