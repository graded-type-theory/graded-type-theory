------------------------------------------------------------------------
-- An abstract set of equality relations over which the logical relation
-- is parameterized.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.EqualityRelation
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Well-formed R
open import Definition.Typed.Weakening R as W using (_∷ʷ_⊇_)

open import Tools.Fin
open import Tools.Function
open import Tools.Level hiding (Level; _⊔_; Lift)
open import Tools.Nat
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    p q q′ r : M
    n n′ : Nat
    Γ : Con Term n
    Δ : Con Term n′
    ρ : Wk n′ n
    A A₁ A₂ A′ B B₁ B₂ B′ C : Term n
    a a′ b b′ e e′ : Term n
    k l l₁ l₂ l′ m t t₁ t₂ u u₁ u₂ v v₁ v₂ w₁ w₂ : Term n
    s : Strength
    bm : BinderMode

-- If Equality-relations _⊢_≅_ _⊢_≅_∷_ _⊢_~_∷_ holds, then one can
-- instantiate the logical relation in Definition.LogicalRelation with
-- these relations and prove the fundamental lemma.

record Equality-relations
  -- Equality of types.
  (_⊢_≅_ : ∀ {n} → Con Term n → (_ _ : Term n) → Set ℓ)
  -- Equality of terms.
  (_⊢_≅_∷_ : ∀ {n} → Con Term n → (_ _ _ : Term n) → Set ℓ)
  -- Equality of levels.
  (_⊢_≅_∷Level : ∀ {n} → Con Term n → (_ _ : Term n) → Set ℓ)
  -- Equality of atomic neutral terms.
  (_⊢_~_∷_ : ∀ {n} → Con Term n → (t u A : Term n) → Set ℓ)
  -- Are neutral cases included in the logical relation?
  (Neutrals-included : Set ℓ) :
  Set ℓ where
  no-eta-equality

  -- A variant of _⊢_≅_.

  _⊢≅_ : Con Term n → Term n → Set ℓ
  Γ ⊢≅ A = Γ ⊢ A ≅ A

  -- A variant of _⊢_≅_∷_.

  _⊢≅_∷_ : Con Term n → Term n → Term n → Set ℓ
  Γ ⊢≅ t ∷ A = Γ ⊢ t ≅ t ∷ A

  -- A variant of _⊢_~_∷_.

  _⊢~_∷_ : Con Term n → Term n → Term n → Set ℓ
  Γ ⊢~ t ∷ A = Γ ⊢ t ~ t ∷ A

  field
    -- Neutrals-included is decided.
    Neutrals-included? : Dec Neutrals-included

    -- If Equality-reflection-allowed holds, then Neutrals-included
    -- does not hold.
    Equality-reflection-allowed→¬Neutrals-included :
      Equality-reflection → ¬ Neutrals-included

    -- If Neutrals-included does not hold, then definitional equality
    -- for types and terms is contained in _⊢_≅_ and _⊢_≅_∷_,
    -- respectively.
    ⊢≡→⊢≅ :
      ¬ Neutrals-included →
      Γ ⊢ A ≡ B → Γ ⊢ A ≅ B
    ⊢≡∷→⊢≅∷ :
      ¬ Neutrals-included →
      Γ ⊢ t ≡ u ∷ A → Γ ⊢ t ≅ u ∷ A

    -- Generic equality compatibility
    ~-to-≅ₜ  : Γ ⊢ t ~ u ∷ A
             → Γ ⊢ t ≅ u ∷ A
    ⊢≅∷→⊢≅∷L : Γ ⊢ l₁ ≅ l₂ ∷ Level
             → Γ ⊢ l₁ ≅ l₂ ∷Level

    -- Judgmental conversion compatibility
    ≅-eq      : Γ ⊢ A ≅ B
              → Γ ⊢ A ≡ B
    ≅ₜ-eq     : Γ ⊢ t ≅ u ∷ A
              → Γ ⊢ t ≡ u ∷ A
    ⊢≅∷L→⊢≡∷L : Γ ⊢ l₁ ≅ l₂ ∷Level
              → Γ ⊢ l₁ ≡ l₂ ∷Level

    -- Level literals are related to themselves in well-formed
    -- contexts if Level is not allowed.
    Level-literal→⊢≅∷L : ¬ Level-allowed
                       → ⊢ Γ
                       → Level-literal l
                       → Γ ⊢ l ≅ l ∷Level

    -- If Level is allowed, then _⊢_≅_∷Level is contained in
    -- _⊢_≅_∷ Level.
    ⊢≅∷L→⊢≅∷ : Level-allowed
             → Γ ⊢ l₁ ≅ l₂ ∷Level
             → Γ ⊢ l₁ ≅ l₂ ∷ Level

    -- Universe
    ≅-univ : Γ ⊢ A ≅ B ∷ U l
           → Γ ⊢ A ≅ B

    -- Symmetry
    ≅-sym  : Γ ⊢ A ≅ B     → Γ ⊢ B ≅ A
    ≅ₜ-sym : Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ t ∷ A
    ~-sym  : Γ ⊢ t ~ u ∷ A → Γ ⊢ u ~ t ∷ A

    -- Transitivity
    ≅-trans  : Γ ⊢ A ≅ B     → Γ ⊢ B ≅ C     → Γ ⊢ A ≅ C
    ≅ₜ-trans : Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ v ∷ A → Γ ⊢ t ≅ v ∷ A
    ~-trans  : Γ ⊢ t ~ u ∷ A → Γ ⊢ u ~ v ∷ A → Γ ⊢ t ~ v ∷ A

    -- Conversion
    ≅-conv : Γ ⊢ t ≅ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ≅ u ∷ B
    ~-conv : Γ ⊢ t ~ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ~ u ∷ B

    -- Weakening
    ≅-wk    : ρ ∷ʷ Δ ⊇ Γ
            → Γ ⊢ A ≅ B
            → Δ ⊢ wk ρ A ≅ wk ρ B
    ≅ₜ-wk   : ρ ∷ʷ Δ ⊇ Γ
            → Γ ⊢ t ≅ u ∷ A
            → Δ ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A
    wk-⊢≅∷L : ρ ∷ʷ Δ ⊇ Γ
            → Γ ⊢ t ≅ u ∷Level
            → Δ ⊢ wk ρ t ≅ wk ρ u ∷Level
    ~-wk    : ρ ∷ʷ Δ ⊇ Γ
            → Γ ⊢ t ~ u ∷ A
            → Δ ⊢ wk ρ t ~ wk ρ u ∷ wk ρ A

    -- Weak head expansion
    ≅-red : Γ ⊢ A ↘ A′
          → Γ ⊢ B ↘ B′
          → Γ ⊢ A′ ≅ B′
          → Γ ⊢ A  ≅ B

    ≅ₜ-red : Γ ⊢ A ↘ B
           → Γ ⊢ a ↘ a′ ∷ B
           → Γ ⊢ b ↘ b′ ∷ B
           → Γ ⊢ a′ ≅ b′ ∷ B
           → Γ ⊢ a  ≅ b  ∷ A

    -- Level type reflexivity
    ≅ₜ-Levelrefl : ⊢ Γ → Level-is-small → Γ ⊢≅ Level ∷ U zeroᵘ

    ≅-Levelrefl : Level-allowed → ⊢ Γ → Γ ⊢≅ Level

    -- Zero level reflexivity
    ≅ₜ-zeroᵘrefl : Level-allowed → ⊢ Γ → Γ ⊢≅ zeroᵘ ∷ Level

    -- Successor level congruence
    ≅ₜ-sucᵘ-cong : Γ ⊢ t ≅ u ∷ Level → Γ ⊢ sucᵘ t ≅ sucᵘ u ∷ Level

    -- supᵘ congruence
    ≅ₜ-supᵘ-cong
      : Γ ⊢ t₁ ≅ t₂ ∷ Level
      → Γ ⊢ u₁ ≅ u₂ ∷ Level
      → Γ ⊢ t₁ supᵘ u₁ ≅ t₂ supᵘ u₂ ∷ Level

    -- supᵘ right identity
    ≅ₜ-supᵘ-zeroʳ
      : Γ ⊢≅ t ∷ Level
      → Γ ⊢ t supᵘ zeroᵘ ≅ t ∷ Level

    -- supᵘ associativity
    ≅ₜ-supᵘ-assoc
      : Γ ⊢≅ t ∷ Level
      → Γ ⊢≅ u ∷ Level
      → Γ ⊢≅ v ∷ Level
      → Γ ⊢ (t supᵘ u) supᵘ v ≅ t supᵘ (u supᵘ v) ∷ Level

    -- supᵘ commutativity
    ≅ₜ-supᵘ-comm
      : Γ ⊢≅ t ∷ Level
      → Γ ⊢≅ u ∷ Level
      → Γ ⊢ t supᵘ u ≅ u supᵘ t ∷ Level

    -- supᵘ idempotence
    ≅ₜ-supᵘ-idem
      : Γ ⊢≅ t ∷ Level
      → Γ ⊢ t supᵘ t ≅ t ∷ Level

    -- supᵘ subsumption
    ≅ₜ-supᵘ-sub
      : Γ ⊢≅ t ∷ Level
      → Γ ⊢ t supᵘ sucᵘ t ≅ sucᵘ t ∷ Level

    -- Universe congruence
    ≅ₜ-U-cong : Γ ⊢ l ≅ k ∷Level → Γ ⊢ U l ≅ U k ∷ U (sucᵘ l)

    -- Lift congruence
    ≅-Lift-cong
      : Γ ⊢ l ≅ k ∷Level
      → Γ ⊢ A ≅ B
      → Γ ⊢ Lift l A ≅ Lift k B

    ≅ₜ-Lift-cong
      : Γ ⊢ l ≅ k ∷Level
      → Γ ⊢ A ≅ B ∷ U l₁
      → Γ ⊢ Lift l A ≅ Lift k B ∷ U (l₁ supᵘₗ l)

    -- η for Lift
    ≅-Lift-η : Γ ⊢ t ∷ Lift k A
             → Γ ⊢ u ∷ Lift k A
             → Whnf t
             → Whnf u
             → Γ ⊢ lower t ≅ lower u ∷ A
             → Γ ⊢ t ≅ u ∷ Lift k A

    -- Natural number type reflexivity
    ≅ₜ-ℕrefl : ⊢ Γ → Γ ⊢≅ ℕ ∷ U zeroᵘ

    -- Empty type reflexivity
    ≅ₜ-Emptyrefl : ⊢ Γ → Γ ⊢≅ Empty ∷ U zeroᵘ

    -- Unit type congruence
    ≅ₜ-Unit-refl : ⊢ Γ → Unit-allowed s → Γ ⊢≅ Unit s ∷ U zeroᵘ

    -- Unit η-equality
    ≅ₜ-η-unit : Γ ⊢ e ∷ Unit s
              → Γ ⊢ e′ ∷ Unit s
              → Unit-allowed s
              → Unit-with-η s
              → Γ ⊢ e ≅ e′ ∷ Unit s

    -- Π- and Σ-congruence

    ≅-ΠΣ-cong : ∀ {F G H E}
              → Γ ⊢ F ≅ H
              → Γ ∙ F ⊢ G ≅ E
              → ΠΣ-allowed bm p q
              → Γ ⊢ ΠΣ⟨ bm ⟩ p , q ▷ F ▹ G ≅ ΠΣ⟨ bm ⟩ p , q ▷ H ▹ E

    ≅ₜ-ΠΣ-cong
              : ∀ {F G H E}
              → Γ ⊢ l ∷Level
              → Γ ⊢ F ≅ H ∷ U l
              → Γ ∙ F ⊢ G ≅ E ∷ U (wk1 l)
              → ΠΣ-allowed bm p q
              → Γ ⊢ ΠΣ⟨ bm ⟩ p , q ▷ F ▹ G ≅ ΠΣ⟨ bm ⟩ p , q ▷ H ▹ E ∷
                  U l

    -- Zero reflexivity
    ≅ₜ-zerorefl : ⊢ Γ → Γ ⊢≅ zero ∷ ℕ

    -- Successor congruence
    ≅-suc-cong : ∀ {m n} → Γ ⊢ m ≅ n ∷ ℕ → Γ ⊢ suc m ≅ suc n ∷ ℕ

    -- Product congruence
    ≅-prod-cong : ∀ {F G t t′ u u′}
                → Γ ∙ F ⊢ G
                → Γ ⊢ t ≅ t′ ∷ F
                → Γ ⊢ u ≅ u′ ∷ G [ t ]₀
                → Σʷ-allowed p q
                → Γ ⊢ prodʷ p t u ≅ prodʷ p t′ u′ ∷ Σʷ p , q ▷ F ▹ G

    -- η-equality
    ≅-η-eq : ∀ {f g F G}
           → Γ ⊢ f ∷ Π p , q ▷ F ▹ G
           → Γ ⊢ g ∷ Π p , q ▷ F ▹ G
           → Function f
           → Function g
           → Γ ∙ F ⊢ wk1 f ∘⟨ p ⟩ var x0 ≅ wk1 g ∘⟨ p ⟩ var x0 ∷ G
           → Γ ⊢ f ≅ g ∷ Π p , q ▷ F ▹ G

    -- η for product types
    ≅-Σ-η : ∀ {r s F G}
          → Γ ⊢ r ∷ Σˢ p , q ▷ F ▹ G
          → Γ ⊢ s ∷ Σˢ p , q ▷ F ▹ G
          → Product r
          → Product s
          → Γ ⊢ fst p r ≅ fst p s ∷ F
          → Γ ⊢ snd p r ≅ snd p s ∷ G [ fst p r ]₀
          → Γ ⊢ r ≅ s ∷ Σˢ p , q ▷ F ▹ G

    -- Variable reflexivity
    ~-var : ∀ {x A} → Γ ⊢ var x ∷ A → Γ ⊢~ var x ∷ A

    -- lower congruence
    ~-lower
      : Γ ⊢ t ~ u ∷ Lift l₂ A
      → Γ ⊢ lower t ~ lower u ∷ A

    -- Application congruence
    ~-app : ∀ {a b f g F G}
          → Γ ⊢ f ~ g ∷ Π p , q ▷ F ▹ G
          → Γ ⊢ a ≅ b ∷ F
          → Γ ⊢ f ∘⟨ p ⟩ a ~ g ∘⟨ p ⟩ b ∷ G [ a ]₀

    -- Product projections congruence
    ~-fst : ∀ {r s F G}
          → Γ ∙ F ⊢ G
          → Γ ⊢ r ~ s ∷ Σˢ p , q ▷ F ▹ G
          → Γ ⊢ fst p r ~ fst p s ∷ F

    ~-snd : ∀ {r s F G}
          → Γ ∙ F ⊢ G
          → Γ ⊢ r ~ s ∷ Σˢ p , q ▷ F ▹ G
          → Γ ⊢ snd p r ~ snd p s ∷ G [ fst p r ]₀

    -- Natural recursion congruence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′}
             → Γ ∙ ℕ     ⊢ F ≅ F′
             → Γ         ⊢ z ≅ z′ ∷ F [ zero ]₀
             → Γ ∙ ℕ ∙ F ⊢ s ≅ s′ ∷ F [ suc (var x1) ]↑²
             → Γ         ⊢ n ~ n′ ∷ ℕ
             → Γ         ⊢ natrec p q r F z s n ~ natrec p q r F′ z′ s′ n′ ∷ F [ n ]₀

    -- Product recursion congruence
    ~-prodrec : ∀ {F G A A′ t t′ u u′}
             → Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊢ A ≅ A′
             → Γ                      ⊢ t ~ t′ ∷ Σʷ p , q ▷ F ▹ G
             → Γ ∙ F ∙ G              ⊢ u ≅ u′ ∷ A [ prodʷ p (var x1) (var x0) ]↑²
             → Σʷ-allowed p q
             → Γ                      ⊢ prodrec r p q′ A t u ~ prodrec r p q′ A′ t′ u′ ∷ A [ t ]₀

    -- Empty recursion congruence
    ~-emptyrec : ∀ {n n′ F F′}
               → Γ ⊢ F ≅ F′
               → Γ ⊢ n ~ n′ ∷ Empty
               → Γ ⊢ emptyrec p F n ~ emptyrec p F′ n′ ∷ F

    -- Weak unit type recursion congruence
    ~-unitrec : ∀ {A A′ t t′ u u′}
              → Γ ∙ Unitʷ ⊢ A ≅ A′
              → Γ ⊢ t ~ t′ ∷ Unitʷ
              → Γ ⊢ u ≅ u′ ∷ A [ starʷ ]₀
              → Unitʷ-allowed
              → ¬ Unitʷ-η
              → Γ ⊢ unitrec p q A t u ~ unitrec p q A′ t′ u′ ∷
                  A [ t ]₀

    -- Star congruence
    ≅ₜ-star-refl
      : ⊢ Γ
      → Unit-allowed s
      → Γ ⊢≅ star s ∷ Unit s

    -- Id preserves "equality".
    ≅-Id-cong
      : Γ ⊢ A₁ ≅ A₂
      → Γ ⊢ t₁ ≅ t₂ ∷ A₁
      → Γ ⊢ u₁ ≅ u₂ ∷ A₁
      → Γ ⊢ Id A₁ t₁ u₁ ≅ Id A₂ t₂ u₂
    ≅ₜ-Id-cong
      : Γ ⊢ A₁ ≅ A₂ ∷ U l
      → Γ ⊢ t₁ ≅ t₂ ∷ A₁
      → Γ ⊢ u₁ ≅ u₂ ∷ A₁
      → Γ ⊢ Id A₁ t₁ u₁ ≅ Id A₂ t₂ u₂ ∷ U l

    -- Reflexivity for rfl.
    ≅ₜ-rflrefl : Γ ⊢ t ∷ A → Γ ⊢≅ rfl ∷ Id A t t

    -- J preserves the _⊢_~_ relation (in a certain way).
    ~-J
      : Γ ⊢ A₁ ≅ A₂
      → Γ ⊢ t₁ ∷ A₁
      → Γ ⊢ t₁ ≅ t₂ ∷ A₁
      → Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≅ B₂
      → Γ ⊢ u₁ ≅ u₂ ∷ B₁ [ t₁ , rfl ]₁₀
      → Γ ⊢ v₁ ≅ v₂ ∷ A₁
      → Γ ⊢ w₁ ~ w₂ ∷ Id A₁ t₁ v₁
      → Γ ⊢ J p q A₁ t₁ B₁ u₁ v₁ w₁ ~ J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
          B₁ [ v₁ , w₁ ]₁₀

    -- K preserves the _⊢_~_ relation (in a certain way).
    ~-K
      : Γ ⊢ A₁ ≅ A₂
      → Γ ⊢ t₁ ≅ t₂ ∷ A₁
      → Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ ≅ B₂
      → Γ ⊢ u₁ ≅ u₂ ∷ B₁ [ rfl ]₀
      → Γ ⊢ v₁ ~ v₂ ∷ Id A₁ t₁ t₁
      → K-allowed
      → Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ~ K p A₂ t₂ B₂ u₂ v₂ ∷ B₁ [ v₁ ]₀

    -- If []-cong is allowed, then []-cong preserves the _⊢_~_
    -- relation (in a certain way).
    ~-[]-cong
      : Γ ⊢ l₁ ≅ l₂ ∷Level
      → Γ ⊢ A₁ ≅ A₂
      → Γ ⊢ t₁ ≅ t₂ ∷ A₁
      → Γ ⊢ u₁ ≅ u₂ ∷ A₁
      → Γ ⊢ v₁ ~ v₂ ∷ Id A₁ t₁ u₁
      → []-cong-allowed s
      → let open Erased s in
        Γ ⊢ []-cong s l₁ A₁ t₁ u₁ v₁ ~ []-cong s l₂ A₂ t₂ u₂ v₂ ∷
          Id (Erased l₁ A₁) ([ t₁ ]) ([ u₁ ])


  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k l l′} → Γ ⊢ k ~ l ∷ U l′ → Γ ⊢ k ≅ l
  ~-to-≅ k~l = ≅-univ (~-to-≅ₜ k~l)

  opaque

    -- A variant of ≅ₜ-ℕrefl.

    ≅-ℕrefl : ⊢ Γ → Γ ⊢≅ ℕ
    ≅-ℕrefl = ≅-univ ∘→ ≅ₜ-ℕrefl

  opaque

    -- A variant of ≅ₜ-Emptyrefl.

    ≅-Emptyrefl : ⊢ Γ → Γ ⊢≅ Empty
    ≅-Emptyrefl = ≅-univ ∘→ ≅ₜ-Emptyrefl

  opaque

    -- A variant of ≅ₜ-U-cong.

    ≅-U-cong : Γ ⊢ l ≅ k ∷Level → Γ ⊢ U l ≅ U k
    ≅-U-cong l≡k = ≅-univ (≅ₜ-U-cong l≡k)

  opaque

    -- A variant of ≅ₜ-Unit-cong.

    ≅-Unit-refl : ⊢ Γ → Unit-allowed s → Γ ⊢≅ Unit s
    ≅-Unit-refl ⊢Γ ok = ≅-univ (≅ₜ-Unit-refl ⊢Γ ok)

  opaque

    -- A well-formedness lemma for _⊢_≅_.

    wf-⊢≅ : Γ ⊢ A ≅ B → Γ ⊢≅ A × Γ ⊢≅ B
    wf-⊢≅ A≅B =
      ≅-trans A≅B (≅-sym A≅B) ,
      ≅-trans (≅-sym A≅B) A≅B

  opaque

    -- A well-formedness lemma for _⊢_≅_∷_.

    wf-⊢≅∷ : Γ ⊢ t ≅ u ∷ A → Γ ⊢≅ t ∷ A × Γ ⊢≅ u ∷ A
    wf-⊢≅∷ t≅u =
      ≅ₜ-trans t≅u (≅ₜ-sym t≅u) ,
      ≅ₜ-trans (≅ₜ-sym t≅u) t≅u

  opaque

    -- A well-formedness lemma for _⊢_~_∷_.

    wf-⊢~∷ : Γ ⊢ t ~ u ∷ A → Γ ⊢~ t ∷ A × Γ ⊢~ u ∷ A
    wf-⊢~∷ t~u =
      ~-trans t~u (~-sym t~u) ,
      ~-trans (~-sym t~u) t~u

  opaque

    -- A variant of possibly-nonempty.

    included :
      ⦃ inc : Neutrals-included ⦄ → Neutrals-included or-empty Γ
    included ⦃ inc ⦄ = possibly-nonempty ⦃ ok = inc ⦄

  opaque

    -- If Γ ⊢ A ≡ B holds, then one can assume Neutrals-included when
    -- proving Γ ⊢ A ≅ B.

    with-inc-⊢≅ :
      Γ ⊢ A ≡ B →
      (⦃ inc : Neutrals-included ⦄ → Γ ⊢ A ≅ B) →
      Γ ⊢ A ≅ B
    with-inc-⊢≅ A≡B A≅B =
      case Neutrals-included? of λ where
        (yes inc) → A≅B ⦃ inc = inc ⦄
        (no ni)   → ⊢≡→⊢≅ ni A≡B

  opaque

    -- If Γ ⊢ t ≡ u ∷ A holds, then one can assume Neutrals-included
    -- when proving Γ ⊢ t ≅ u ∷ A.

    with-inc-⊢≅∷ :
      Γ ⊢ t ≡ u ∷ A →
      (⦃ inc : Neutrals-included ⦄ → Γ ⊢ t ≅ u ∷ A) →
      Γ ⊢ t ≅ u ∷ A
    with-inc-⊢≅∷ t≡u t≅u =
      case Neutrals-included? of λ where
        (yes inc) → t≅u ⦃ inc = inc ⦄
        (no ni)   → ⊢≡∷→⊢≅∷ ni t≡u

  opaque

    -- supᵘ distributes over sucᵘ

    ≅ₜ-supᵘ-sucᵘ
      : Γ ⊢≅ t ∷ Level
      → Γ ⊢≅ u ∷ Level
      → Γ ⊢ sucᵘ t supᵘ sucᵘ u ≅ sucᵘ (t supᵘ u) ∷ Level
    ≅ₜ-supᵘ-sucᵘ ⊢≅t ⊢≅u =
      let ⊢Level , ⊢t , _ = wf-⊢≡∷ (≅ₜ-eq ⊢≅t)
          _ , ⊢u , _ = wf-⊢≡∷ (≅ₜ-eq ⊢≅u)
      in ≅ₜ-red
        (id ⊢Level , Levelₙ)
        (redMany (supᵘ-sucᵘ ⊢t ⊢u) , sucᵘₙ)
        (id (sucᵘⱼ (supᵘⱼ ⊢t ⊢u)) , sucᵘₙ)
        (≅ₜ-sucᵘ-cong (≅ₜ-supᵘ-cong ⊢≅t ⊢≅u))

  opaque

    -- A variant of ≅ₜ-supᵘ-sub.

    ≅ₜ-supᵘ-sub′
      : Γ ⊢≅ t ∷ Level
      → Γ ⊢ t supᵘ u ≅ u ∷ Level
      → Γ ⊢ t supᵘ sucᵘ u ≅ sucᵘ u ∷ Level
    ≅ₜ-supᵘ-sub′ ⊢≅t t⊔u≡u =
      let _ , ⊢t , _ = wf-⊢≡∷ (≅ₜ-eq ⊢≅t)
          _ , ⊢t⊔u , ⊢u = wf-⊢≡∷ (≅ₜ-eq t⊔u≡u)
          _ , ⊢≅u = wf-⊢≅∷ t⊔u≡u
      in
      -- t supᵘ sucᵘ u
        ≅ₜ-trans (≅ₜ-supᵘ-cong ⊢≅t (≅ₜ-trans
          (≅ₜ-sucᵘ-cong (≅ₜ-sym t⊔u≡u))
          (≅ₜ-sym (≅ₜ-supᵘ-sucᵘ ⊢≅t ⊢≅u))))
      -- t supᵘ (sucᵘ t supᵘ sucᵘ u)
      $ ≅ₜ-trans (≅ₜ-sym (≅ₜ-supᵘ-assoc ⊢≅t (≅ₜ-sucᵘ-cong ⊢≅t) (≅ₜ-sucᵘ-cong ⊢≅u)))
      -- (t supᵘ sucᵘ t) supᵘ sucᵘ u
      $ ≅ₜ-trans (≅ₜ-supᵘ-cong (≅ₜ-supᵘ-sub ⊢≅t) (≅ₜ-sucᵘ-cong ⊢≅u))
      -- sucᵘ t supᵘ sucᵘ u
      $ ≅ₜ-trans (≅ₜ-supᵘ-sucᵘ ⊢≅t ⊢≅u)
      -- sucᵘ (t supᵘ u)
      $ ≅ₜ-sucᵘ-cong t⊔u≡u
      -- sucᵘ u

-- Values of type EqRelSet contain three relations that the logical
-- relation in Definition.LogicalRelation can be instantiated with.
-- The assumed properties ensure that the fundamental lemma can be
-- proved.

record EqRelSet : Set (lsuc ℓ) where
  no-eta-equality
  field
    ---------------
    -- Relations --
    ---------------

    -- Equality of types
    _⊢_≅_   : Con Term n → (A B : Term n)   → Set ℓ

    -- Equality of terms
    _⊢_≅_∷_ : Con Term n → (t u A : Term n) → Set ℓ

    -- Equality of levels
    _⊢_≅_∷Level : Con Term n → (t u : Term n) → Set ℓ

    -- Equality of neutral terms
    _⊢_~_∷_ : Con Term n → (t u A : Term n) → Set ℓ

    -- Are neutral cases included in the logical relation?
    Neutrals-included : Set ℓ

    ----------------
    -- Properties --
    ----------------

    equality-relations :
      Equality-relations
        _⊢_≅_ _⊢_≅_∷_ _⊢_≅_∷Level _⊢_~_∷_ Neutrals-included

  open Equality-relations equality-relations public
