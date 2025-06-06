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

open import Definition.LogicalRelation.Weakening.Restricted R
open import Definition.Untyped Mod as U hiding (K)
open import Definition.Untyped.Neutral Mod type-variant
open import Definition.Typed.Properties R
open import Definition.Typed R
-- The imported operator _,_ is not "supposed" to be used below, but
-- "," is used in some pattern synonyms, and if this import statement
-- is removed, then some code in
-- Definition.LogicalRelation.Properties.Reduction fails to type-check
-- (at the time of writing).
open import Definition.Typed.Substitution R using (_,_)

open import Tools.Empty
open import Tools.Function
open import Tools.Level hiding (_⊔_)
open import Tools.Nat hiding (_<_; _≤_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Unit

private
  variable
    p q : Mod
    ℓ l : Nat
    Γ Δ : Con Term ℓ
    t t′ u u′ : Term _
    ρ : Wk _ _
    s : Strength

-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reducibility of Neutrals:

-- Neutral type
record _⊩ne_ {ℓ : Nat} (Γ : Con Term ℓ) (A : Term ℓ) : Set a where
  no-eta-equality
  pattern
  constructor ne
  field
    neutrals-included : Neutrals-included
    K                 : Term ℓ
    D                 : Γ ⊢ A ⇒* K
    neK               : Neutral K
    K≡K               : Γ ⊢≅ K

-- Neutral type equality
record _⊩ne_≡_/_ (Γ : Con Term ℓ) (A B : Term ℓ) ([A] : Γ ⊩ne A) : Set a where
  no-eta-equality
  pattern
  constructor ne₌
  open _⊩ne_ [A]
  field
    neutrals-included : Neutrals-included
    M                 : Term ℓ
    D′                : Γ ⊢ B ⇒* M
    neM               : Neutral M
    K≡M               : Γ ⊢ K ≅ M

-- Neutral term equality in WHNF
record _⊩neNf_≡_∷_ (Γ : Con Term ℓ) (k m A : Term ℓ) : Set a where
  inductive
  no-eta-equality
  pattern
  constructor neNfₜ₌
  field
    neutrals-included : Neutrals-included
    neK               : Neutral k
    neM               : Neutral m
    k≡m               : Γ ⊢ k ~ m ∷ A

-- Neutral term equality
record _⊩ne_≡_∷_/_ (Γ : Con Term ℓ) (t u A : Term ℓ) ([A] : Γ ⊩ne A) : Set a where
  no-eta-equality
  pattern
  constructor neₜ₌
  open _⊩ne_ [A]
  field
    k m : Term ℓ
    d   : Γ ⊢ t ⇒* k ∷ K
    d′  : Γ ⊢ u ⇒* m ∷ K
    nf  : Γ ⊩neNf k ≡ m ∷ K

-- Reducibility of natural numbers:

-- Natural number type
_⊩ℕ_ : (Γ : Con Term ℓ) (A : Term ℓ) → Set a
Γ ⊩ℕ A = Γ ⊢ A ⇒* ℕ

-- Natural number type equality
_⊩ℕ_≡_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Set a
Γ ⊩ℕ A ≡ B = Γ ⊢ B ⇒* ℕ

mutual
  -- Natural number term equality
  record _⊩ℕ_≡_∷ℕ (Γ : Con Term ℓ) (t u : Term ℓ) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor ℕₜ₌
    field
      k k′ : Term ℓ
      d : Γ ⊢ t ⇒* k  ∷ ℕ
      d′ : Γ ⊢ u ⇒* k′ ∷ ℕ
      k≡k′ : Γ ⊢ k ≅ k′ ∷ ℕ
      prop : [Natural]-prop Γ k k′

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term ℓ) : (n n′ : Term ℓ) → Set a where
    sucᵣ  : ∀ {n n′} → Γ ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ (suc n) (suc n′)
    zeroᵣ : [Natural]-prop Γ zero zero
    ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ ℕ → [Natural]-prop Γ n n′

-- Reducibility of Empty

-- Empty type
_⊩Empty_ : (Γ : Con Term ℓ) (A : Term ℓ) → Set a
Γ ⊩Empty A = Γ ⊢ A ⇒* Empty

-- Empty type equality
_⊩Empty_≡_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Set a
Γ ⊩Empty A ≡ B = Γ ⊢ B ⇒* Empty

data [Empty]-prop (Γ : Con Term ℓ) : (n n′ : Term ℓ) → Set a where
  ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ Empty → [Empty]-prop Γ n n′

-- Empty term equality
record _⊩Empty_≡_∷Empty (Γ : Con Term ℓ) (t u : Term ℓ) : Set a where
  inductive
  no-eta-equality
  pattern
  constructor Emptyₜ₌
  field
    k k′ : Term ℓ
    d : Γ ⊢ t ⇒* k  ∷ Empty
    d′ : Γ ⊢ u ⇒* k′ ∷ Empty
    k≡k′ : Γ ⊢ k ≅ k′ ∷ Empty
    prop : [Empty]-prop Γ k k′

-- Reducibility of Unit

-- Unit type
record _⊩Unit⟨_,_⟩_
  (Γ : Con Term ℓ) (l : Universe-level) (s : Strength) (A : Term ℓ) :
  Set a where
  no-eta-equality
  pattern
  constructor Unitᵣ
  field
    l′      : Universe-level
    l′≤     : l′ ≤ᵘ l
    ⇒*-Unit : Γ ⊢ A ⇒* Unit s l′
    ok      : Unit-allowed s

-- Unit type equality
_⊩Unit⟨_⟩_≡_/_ :
  Con Term ℓ → Strength → (_ _ : Term ℓ) → Universe-level → Set a
Γ ⊩Unit⟨ s ⟩ A ≡ B / l′ = Γ ⊢ B ⇒* Unit s l′

-- Unit term equality

data [Unitʷ]-prop
       (Γ : Con Term ℓ) (l′ : Universe-level) :
       Term ℓ → Term ℓ → Set a where
  starᵣ : [Unitʷ]-prop Γ l′ (starʷ l′) (starʷ l′)
  ne    : Γ ⊩neNf t ≡ u ∷ Unitʷ l′ → [Unitʷ]-prop Γ l′ t u

data [Unit]-prop
       (Γ : Con Term ℓ) (l′ : Universe-level) :
       Strength → Term ℓ → Term ℓ → Set a where
  Unitₜ₌ʷ : [Unitʷ]-prop Γ l′ t u → ¬ Unitʷ-η → [Unit]-prop Γ l′ 𝕨 t u
  Unitₜ₌ˢ : Unit-with-η s → [Unit]-prop Γ l′ s t u

record _⊩Unit⟨_⟩_≡_∷Unit/_
         (Γ : Con Term ℓ) (s : Strength)
         (t₁ t₂ : Term ℓ) (l′ : Universe-level) :
         Set a where
  inductive
  no-eta-equality
  pattern
  constructor Unitₜ₌
  field
    u₁ u₂ : Term ℓ
    ↘u₁   : Γ ⊢ t₁ ↘ u₁ ∷ Unit s l′
    ↘u₂   : Γ ⊢ t₂ ↘ u₂ ∷ Unit s l′
    prop  : [Unit]-prop Γ l′ s u₁ u₂


-- Logical relation
-- Exported interface
record LogRelKit : Set (lsuc a) where
  no-eta-equality
  pattern
  constructor Kit
  field
    _⊩U_ : Con Term ℓ → Term ℓ → Set a
    _⊩B⟨_⟩_ : (Γ : Con Term ℓ) (W : BindingType) → Term ℓ → Set a
    _⊩Id_ : Con Term ℓ → Term ℓ → Set a

    _⊩_ : (Γ : Con Term ℓ) → Term ℓ → Set a
    _⊩_≡_/_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Γ ⊩ A → Set a
    _⊩_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ A → Set a

  -- Unary reducibility for terms is defined in terms of binary
  -- reducibility for terms.

  _⊩_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ A → Set a
  Γ ⊩ t ∷ A / ⊩A = Γ ⊩ t ≡ t ∷ A / ⊩A

module LogRel
  (l : Universe-level) (rec : ∀ {l′} → l′ <ᵘ l → LogRelKit)
  where

  -- Reducibility of Universe:

  -- Universe type
  record _⊩₁U_ (Γ : Con Term ℓ) (A : Term ℓ) : Set a where
    no-eta-equality
    pattern
    constructor Uᵣ
    field
      l′  : Universe-level
      l′< : l′ <ᵘ l
      ⇒*U : Γ ⊢ A ⇒* U l′

  -- Universe type equality
  _⊩₁U≡_/_ : Con Term ℓ → Term ℓ → Universe-level → Set a
  Γ ⊩₁U≡ B / l′ = Γ ⊢ B ⇒* U l′

  -- Universe term equality
  record _⊩₁U_≡_∷U/_
           {l′} (Γ : Con Term ℓ) (t u : Term ℓ) (l< : l′ <ᵘ l) :
           Set a where
    no-eta-equality
    pattern
    constructor Uₜ₌
    open LogRelKit (rec l<)
    field
      A B   : Term ℓ
      d     : Γ ⊢ t ⇒* A ∷ U l′
      d′    : Γ ⊢ u ⇒* B ∷ U l′
      typeA : Type A
      typeB : Type B
      A≡B   : Γ ⊢ A ≅ B ∷ U l′
      [t]   : Γ ⊩ t
      [u]   : Γ ⊩ u
      [t≡u] : Γ ⊩ t ≡ u / [t]



  mutual

    -- Reducibility of Binding types (Π, Σ):

    -- B-type
    record _⊩ₗB⟨_⟩_ (Γ : Con Term ℓ) (W : BindingType) (A : Term ℓ) : Set a where
      inductive
      no-eta-equality
      pattern
      constructor Bᵣ
      field
        F : Term ℓ
        G : Term (1+ ℓ)
        D : Γ ⊢ A ⇒* ⟦ W ⟧ F ▹ G
        A≡A : Γ ⊢≅ ⟦ W ⟧ F ▹ G
        [F] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} →
              ρ ∷ʷʳ Δ ⊇ Γ → Δ ⊩ₗ U.wk ρ F
        [G] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a : Term m}
            → ([ρ] : ρ ∷ʷʳ Δ ⊇ Γ)
            → Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ]
            → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀
        G-ext : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              → ([ρ] : ρ ∷ʷʳ Δ ⊇ Γ)
              → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ])
              → ([b] : Δ ⊩ₗ b ∷ U.wk ρ F / [F] [ρ])
              → Δ ⊩ₗ a ≡ b ∷ U.wk ρ F / [F] [ρ]
              → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀ ≡ U.wk (lift ρ) G [ b ]₀ /
                  [G] [ρ] [a]
        ok : BindingType-allowed W

    -- B-type equality
    record _⊩ₗB⟨_⟩_≡_/_ (Γ : Con Term ℓ) (W : BindingType) (A B : Term ℓ) ([A] : Γ ⊩ₗB⟨ W ⟩ A) : Set a where
      inductive
      no-eta-equality
      pattern
      constructor B₌
      open _⊩ₗB⟨_⟩_ [A]
      field
        F′     : Term ℓ
        G′     : Term (1+ ℓ)
        D′     : Γ ⊢ B ⇒* ⟦ W ⟧ F′ ▹ G′
        A≡B    : Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F′ ▹ G′
        [F≡F′] : {m : Nat} {ρ : Wk m ℓ} {Δ : Con Term m}
               → ([ρ] : ρ ∷ʷʳ Δ ⊇ Γ)
               → Δ ⊩ₗ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ]
        [G≡G′] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a}
               → ([ρ] : ρ ∷ʷʳ Δ ⊇ Γ)
               → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ])
               → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀ ≡ U.wk (lift ρ) G′ [ a ]₀ /
                   [G] [ρ] [a]

    -- Term equality of Π-type
    _⊩ₗΠ_≡_∷_/_ : {ℓ : Nat} {p q : Mod} (Γ : Con Term ℓ) (t u A : Term ℓ) ([A] : Γ ⊩ₗB⟨ BΠ p q ⟩ A) → Set a
    _⊩ₗΠ_≡_∷_/_
      {ℓ} {p} {q} Γ t u A [A]@(Bᵣ F G D A≡A [F] [G] G-ext _) =
      ∃₂ λ f g → Γ ⊢ t ⇒* f ∷ Π p , q ▷ F ▹ G
               × Γ ⊢ u ⇒* g ∷ Π p , q ▷ F ▹ G
               × Function f
               × Function g
               × Γ ⊢ f ≅ g ∷ Π p , q ▷ F ▹ G
               × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {v w}
                  ([ρ] : ρ ∷ʷʳ Δ ⊇ Γ)
                  (⊩v : Δ ⊩ₗ v ∷ U.wk ρ F / [F] [ρ]) →
                  Δ ⊩ₗ w ∷ U.wk ρ F / [F] [ρ] →
                  Δ ⊩ₗ v ≡ w ∷ U.wk ρ F / [F] [ρ] →
                  Δ ⊩ₗ U.wk ρ f ∘⟨ p ⟩ v ≡ U.wk ρ g ∘⟨ p ⟩ w ∷
                    U.wk (lift ρ) G [ v ]₀ / [G] [ρ] ⊩v)
    -- This type is not defined as a record type, because then Agda's
    -- positivity checker would complain.

    -- Term equality of Σ-type
    _⊩ₗΣ_≡_∷_/_ :
      {p q : Mod} {m : Strength} (Γ : Con Term ℓ) (t u A : Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Set a
    _⊩ₗΣ_≡_∷_/_
      {p = p} {q = q} {m} Γ t u A
      [A]@(Bᵣ F G D A≡A [F] [G] G-ext _) =
      ∃₂ λ t′ u′ → Γ ⊢ t ⇒* t′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊢ u ⇒* u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊢ t′ ≅ u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Σ (Product t′) λ pProd
                 → Σ (Product u′) λ rProd
                 → [Σ]-prop m t′ u′ Γ [A] pProd rProd

    [Σ]-prop :
      ∀ {A p q} (m : Strength) (t r : Term ℓ) (Γ : Con Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Product t → Product r → Set a
    [Σ]-prop {p = p} 𝕤 t r Γ (Bᵣ F G D A≡A [F] [G] G-ext _) _ _ =
      let id-Γ = id (wfEq (≅-eq A≡A)) in
      Σ (Γ ⊩ₗ fst p t ∷ U.wk id F / [F] id-Γ) λ [fstp]
      → Γ ⊩ₗ fst p r ∷ U.wk id F / [F] id-Γ
      × Γ ⊩ₗ fst p t ≡ fst p r ∷ U.wk id F / [F] id-Γ
      × Γ ⊩ₗ snd p t ≡ snd p r ∷ U.wk (lift id) G [ fst p t ]₀
        / [G] id-Γ [fstp]
    [Σ]-prop
      {p = p} 𝕨 t r Γ (Bᵣ F G D A≡A [F] [G] G-ext _)
      (prodₙ {p = p′} {t = p₁} {u = p₂} {m = m′})
      (prodₙ {p = p″} {t = r₁} {u = r₂} {m = m″}) =
             let id-Γ = id (wfEq (≅-eq A≡A)) in
             m′ PE.≡ 𝕨 × m″ PE.≡ 𝕨 ×
             p PE.≡ p′ × p PE.≡ p″ ×
             Σ (Γ ⊩ₗ p₁ ∷ U.wk id F / [F] id-Γ) λ [p₁] →
             Σ (Γ ⊩ₗ r₁ ∷ U.wk id F / [F] id-Γ) λ [r₁]
             → (Γ ⊩ₗ p₁ ≡ r₁ ∷ U.wk id F / [F] id-Γ)
             × (Γ ⊩ₗ p₂ ≡ r₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id-Γ [p₁])
    [Σ]-prop
      𝕨 t r Γ (Bᵣ F G D A≡A [F] [G] G-ext _)
      (prodₙ {t = p₁} {u = p₂}) (ne y) =
      Lift a ⊥
    [Σ]-prop
      𝕨 t r Γ (Bᵣ F G D A≡A [F] [G] G-ext ok)
      (ne x) (prodₙ {t = r₁} {u = r₂}) =
      Lift a ⊥
    [Σ]-prop
      {p = p} {q = q} 𝕨 t r Γ
      (Bᵣ F G D A≡A [F] [G] G-ext _) (ne x) (ne y) =
        Neutrals-included ×
        Γ ⊢ t ~ r ∷ Σʷ p , q ▷ F ▹ G

    -- Reducibility for identity types.

    -- Well-formed identity types.
    record _⊩ₗId_ (Γ : Con Term ℓ) (A : Term ℓ) : Set a where
      inductive
      no-eta-equality
      pattern
      constructor Idᵣ
      field
        Ty lhs rhs : Term ℓ
        ⇒*Id       : Γ ⊢ A ⇒* Id Ty lhs rhs
        ⊩Ty        : Γ ⊩ₗ Ty
        ⊩lhs       : Γ ⊩ₗ lhs ∷ Ty / ⊩Ty
        ⊩rhs       : Γ ⊩ₗ rhs ∷ Ty / ⊩Ty

    -- Well-formed identity type equality.
    record _⊩ₗId_≡_/_
      (Γ : Con Term ℓ) (A B : Term ℓ) (⊩A : Γ ⊩ₗId A) : Set a where
      inductive
      no-eta-equality
      pattern
      constructor Id₌

      open _⊩ₗId_ ⊩A

      field
        Ty′ lhs′ rhs′ : Term ℓ
        ⇒*Id′         : Γ ⊢ B ⇒* Id Ty′ lhs′ rhs′
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

    -- Well-formed identity term equality.
    _⊩ₗId_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ₗId A → Set a
    Γ ⊩ₗId t ≡ u ∷ A / ⊩A =
      ∃₂ λ t′ u′ →
      Γ ⊢ t ⇒* t′ ∷ Id Ty lhs rhs ×
      Γ ⊢ u ⇒* u′ ∷ Id Ty lhs rhs ×
      ∃ λ (t′-id : Identity t′) →
      ∃ λ (u′-id : Identity u′) →
      Identity-rec t′-id
        (Identity-rec u′-id
           (Γ ⊩ₗ lhs ≡ rhs ∷ Ty / ⊩Ty)
           (Lift _ ⊥))
        (Identity-rec u′-id
           (Lift _ ⊥)
           (Neutrals-included ×
            Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs))
      where
      open _⊩ₗId_ ⊩A

    -- Logical relation definition
    data _⊩ₗ_ (Γ : Con Term ℓ) : Term ℓ → Set a where
      Uᵣ  : ∀ {A} → Γ ⊩₁U A → Γ ⊩ₗ A
      ℕᵣ  : ∀ {A} → Γ ⊩ℕ A → Γ ⊩ₗ A
      Emptyᵣ : ∀ {A} → Γ ⊩Empty A → Γ ⊩ₗ A
      Unitᵣ : ∀ {A} {s : Strength} → Γ ⊩Unit⟨ l , s ⟩ A → Γ ⊩ₗ A
      ne  : ∀ {A} → Γ ⊩ne A → Γ ⊩ₗ A
      Bᵣ  : ∀ {A} W → Γ ⊩ₗB⟨ W ⟩ A → Γ ⊩ₗ A
      Idᵣ : ∀ {A} → Γ ⊩ₗId A → Γ ⊩ₗ A

    _⊩ₗ_≡_/_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ A ≡ B / Uᵣ ⊩A = Γ ⊩₁U≡ B / _⊩₁U_.l′ ⊩A
    Γ ⊩ₗ A ≡ B / ℕᵣ D = Γ ⊩ℕ A ≡ B
    Γ ⊩ₗ A ≡ B / Emptyᵣ D = Γ ⊩Empty A ≡ B
    Γ ⊩ₗ A ≡ B / Unitᵣ {s = s} ⊩A = Γ ⊩Unit⟨ s ⟩ A ≡ B / ⊩A ._⊩Unit⟨_,_⟩_.l′
    Γ ⊩ₗ A ≡ B / ne neA = Γ ⊩ne A ≡ B / neA
    Γ ⊩ₗ A ≡ B / Bᵣ W BA = Γ ⊩ₗB⟨ W ⟩ A ≡ B / BA
    Γ ⊩ₗ A ≡ B / Idᵣ ⊩A = Γ ⊩ₗId A ≡ B / ⊩A

    _⊩ₗ_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ t ∷ A / ⊩A = Γ ⊩ₗ t ≡ t ∷ A / ⊩A

    _⊩ₗ_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ t ≡ u ∷ A / Uᵣ ⊩A = Γ ⊩₁U t ≡ u ∷U/ _⊩₁U_.l′< ⊩A
    Γ ⊩ₗ t ≡ u ∷ A / ℕᵣ D = Γ ⊩ℕ t ≡ u ∷ℕ
    Γ ⊩ₗ t ≡ u ∷ A / Emptyᵣ D = Γ ⊩Empty t ≡ u ∷Empty
    Γ ⊩ₗ t ≡ u ∷ A / Unitᵣ {s = s} ⊩A = Γ ⊩Unit⟨ s ⟩ t ≡ u ∷Unit/ ⊩A ._⊩Unit⟨_,_⟩_.l′
    Γ ⊩ₗ t ≡ u ∷ A / ne neA = Γ ⊩ne t ≡ u ∷ A / neA
    Γ ⊩ₗ t ≡ u ∷ A / Bᵣ BΠ! ΠA = Γ ⊩ₗΠ t ≡ u ∷ A / ΠA
    Γ ⊩ₗ t ≡ u ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩ₗΣ t ≡ u ∷ A / ΣA
    Γ ⊩ₗ t ≡ u ∷ A / Idᵣ ⊩A = Γ ⊩ₗId t ≡ u ∷ A / ⊩A

    kit : LogRelKit
    kit = Kit _⊩₁U_ _⊩ₗB⟨_⟩_ _⊩ₗId_
              _⊩ₗ_ _⊩ₗ_≡_/_ _⊩ₗ_≡_∷_/_

open LogRel public
  using
    (Uᵣ; ℕᵣ; Emptyᵣ; Unitᵣ; ne; Bᵣ; B₌; Idᵣ; Id₌; Uₜ₌;
     module _⊩₁U_; module _⊩₁U_≡_∷U/_;
     module _⊩ₗB⟨_⟩_; module _⊩ₗB⟨_⟩_≡_/_;
     module _⊩ₗId_; module _⊩ₗId_≡_/_)

-- Patterns for the non-records of Π
pattern Πₜ₌ f g d d′ funcF funcG f≡g [f≡g] = f , g , d , d′ , funcF , funcG , f≡g , [f≡g]
pattern Σₜ₌ p r d d′ pProd rProd p≅r prop = p , r , d , d′ , p≅r , pProd , rProd , prop

pattern Unitᵣ′ a b c d = Unitᵣ (Unitᵣ a b c d)
pattern Uᵣ′ a b c = Uᵣ (Uᵣ a b c)
pattern ne′ a b c d e = ne (ne a b c d e)
pattern Bᵣ′ W a b c d e f g h = Bᵣ W (Bᵣ a b c d e f g h)
pattern Πᵣ′ a b c d e f g h = Bᵣ′ BΠ! a b c d e f g h
pattern Σᵣ′ a b c d e f g h = Bᵣ′ BΣ! a b c d e f g h

mutual

  -- A LogRelKit for the given Universe-level.

  kit : Universe-level → LogRelKit
  kit ℓ = LogRel.kit ℓ kit′

  -- A LogRelKit for m.

  kit′ : {n m : Universe-level} → m <ᵘ n → LogRelKit
  kit′ {m = m} ≤ᵘ-refl = kit m
  kit′ (≤ᵘ-step p) = kit′ p

_⊩′⟨_⟩U_ : Con Term ℓ → Universe-level → Term ℓ → Set a
Γ ⊩′⟨ l ⟩U A = Γ ⊩U A where open LogRelKit (kit l)

_⊩′⟨_⟩B⟨_⟩_ : Con Term ℓ → Universe-level → BindingType → Term ℓ → Set a
Γ ⊩′⟨ l ⟩B⟨ W ⟩ A = Γ ⊩B⟨ W ⟩ A where open LogRelKit (kit l)

_⊩′⟨_⟩Id_ : Con Term ℓ → Universe-level → Term ℓ → Set a
Γ ⊩′⟨ l ⟩Id A = Γ ⊩Id A
  where
  open LogRelKit (kit l)

-- Reducibility of types

_⊩⟨_⟩_ : Con Term ℓ → Universe-level → Term ℓ → Set a
Γ ⊩⟨ l ⟩ A = Γ ⊩ A where open LogRelKit (kit l)

-- Equality of reducibile types

_⊩⟨_⟩_≡_/_ :
  (Γ : Con Term ℓ) (l : Universe-level) (A _ : Term ℓ) → Γ ⊩⟨ l ⟩ A →
  Set a
Γ ⊩⟨ l ⟩ A ≡ B / [A] = Γ ⊩ A ≡ B / [A] where open LogRelKit (kit l)

-- Reducibility of terms

_⊩⟨_⟩_∷_/_ :
  (Γ : Con Term ℓ) (l : Universe-level) (_ A : Term ℓ) → Γ ⊩⟨ l ⟩ A →
  Set a
Γ ⊩⟨ l ⟩ t ∷ A / [A] = Γ ⊩ t ∷ A / [A] where open LogRelKit (kit l)

-- Equality of reducibile terms

_⊩⟨_⟩_≡_∷_/_ :
  (Γ : Con Term ℓ) (l : Universe-level) (_ _ A : Term ℓ) → Γ ⊩⟨ l ⟩ A →
  Set a
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
         Neutrals-included →
         (u-n : Neutral u) →
         Γ ⊢~ u ∷ Id Ty lhs rhs →
         ⊩Id∷-view ⊩A u (ne u-n)

-- The view is inhabited for well-formed identity terms.

⊩Id∷-view-inhabited :
  ∀ {A} (⊩A : Γ ⊩′⟨ l ⟩Id A)
  ((u , _ , _ , _ , u-id , _) : Γ ⊩⟨ l ⟩ t ∷ A / Idᵣ ⊩A) →
  ⊩Id∷-view ⊩A u u-id
⊩Id∷-view-inhabited _ = λ where
  (_ , _ , _ , _ , rflₙ , rflₙ , lhs≡rhs)     → rflᵣ lhs≡rhs
  (_ , _ , _ , _ , ne u-n , ne _ , inc , u~v) →
    ne inc u-n (~-trans u~v (~-sym u~v))
  (_ , _ , _ , _ , rflₙ , ne _ , ())
  (_ , _ , _ , _ , ne _ , rflₙ , ())

-- A view of parts of _⊩ₗId_≡_∷_/_.

data ⊩Id≡∷-view
  {Γ : Con Term ℓ} (lhs rhs {Ty} : Term ℓ) (⊩Ty : Γ ⊩⟨ l ⟩ Ty) :
  ∀ t → Identity t → ∀ u → Identity u → Set a where
  rfl₌ : (lhs≡rhs : Γ ⊩⟨ l ⟩ lhs ≡ rhs ∷ Ty / ⊩Ty) →
         ⊩Id≡∷-view lhs rhs ⊩Ty rfl rflₙ rfl rflₙ
  ne   : Neutrals-included →
         (t′-n : Neutral t′) (u′-n : Neutral u′) →
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
  (_ , _ , _ , _ , ne t′-n , ne u′-n , inc , t′~u′) →
    ne inc t′-n u′-n t′~u′
  (_ , _ , _ , _ , rflₙ , ne _ , ())
  (_ , _ , _ , _ , ne _ , rflₙ , ())

-- A kind of constructor for _⊩ₗId_≡_∷_/_.

⊩Id≡∷ :
  ∀ {A} {Γ : Con Term ℓ} (⊩A : Γ ⊩′⟨ l ⟩Id A) →
  let open _⊩ₗId_ ⊩A in
  ((t′ , _ , _ , _ , t′-id , _) : Γ ⊩⟨ l ⟩ t ∷ A / Idᵣ ⊩A)
  ((u′ , _ , _ , _ , u′-id , _) : Γ ⊩⟨ l ⟩ u ∷ A / Idᵣ ⊩A) →
  Identity-rec t′-id
    (Identity-rec u′-id
       (Lift _ ⊤)
       (Lift _ ⊥))
    (Identity-rec u′-id
       (Lift _ ⊥)
       (Neutrals-included ×
        Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs)) →
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A / Idᵣ ⊩A
⊩Id≡∷ ⊩A ⊩t@(t′ , _ , t⇒*t′ , _ , t′-id , _)
  ⊩u@(u′ , _ , u⇒*u′ , _ , u′-id , _) rest =
    t′ , u′ , t⇒*t′ , u⇒*u′ , t′-id , u′-id
  , (case ⊩Id∷-view-inhabited ⊩A ⊩t of λ where
       (rflᵣ lhs≡rhs) → case ⊩Id∷-view-inhabited ⊩A ⊩u of λ where
         (rflᵣ _)   → lhs≡rhs
         (ne _ _ _) → case rest of λ ()
       (ne _ _ _) → case ⊩Id∷-view-inhabited ⊩A ⊩u of λ where
         (rflᵣ _)   → case rest of λ ()
         (ne _ _ _) → rest)

-- A kind of inverse of ⊩Id≡∷.

⊩Id≡∷⁻¹ :
  ∀ {A} {Γ : Con Term ℓ}
  (⊩A : Γ ⊩′⟨ l ⟩Id A) →
  let open _⊩ₗId_ ⊩A in
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A / Idᵣ ⊩A →
  ∃ λ (⊩t@(t′ , _ , _ , _ , t′-id , _) : Γ ⊩⟨ l ⟩ t ∷ A / Idᵣ ⊩A) →
  ∃ λ (⊩u@(u′ , _ , _ , _ , u′-id , _) : Γ ⊩⟨ l ⟩ u ∷ A / Idᵣ ⊩A) →
  Identity-rec t′-id
    (Identity-rec u′-id
       (Lift _ ⊤)
       (Lift _ ⊥))
    (Identity-rec u′-id
       (Lift _ ⊥)
       (Neutrals-included ×
        Γ ⊢ t′ ~ u′ ∷ Id Ty lhs rhs))
⊩Id≡∷⁻¹ ⊩A t≡u@(t′ , u′ , t⇒*t′ , u⇒*u′ , t′-id , u′-id , rest) =
  case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
    (rfl₌ lhs≡rhs) →
        (t′ , t′ , t⇒*t′ , t⇒*t′ , t′-id , t′-id , lhs≡rhs)
      , (u′ , u′ , u⇒*u′ , u⇒*u′ , u′-id , u′-id , lhs≡rhs)
      , _
    (ne inc _ _ t′~u′) →
      let ~t′ , ~u′ = wf-⊢~∷ t′~u′ in
        (t′ , t′ , t⇒*t′ , t⇒*t′ , t′-id , t′-id , inc , ~t′)
      , (u′ , u′ , u⇒*u′ , u⇒*u′ , u′-id , u′-id , inc , ~u′)
      , inc , t′~u′
