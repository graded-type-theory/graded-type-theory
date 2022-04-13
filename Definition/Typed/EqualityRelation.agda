{-# OPTIONS --without-K --safe #-}

module Definition.Typed.EqualityRelation (M : Set) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M
open import Definition.Typed.Weakening M using (_∷_⊆_)

open import Tools.Fin
open import Tools.Nat

private
  variable
    p q : M
    ℓ n : Nat
    Γ : Con Term n
    Δ : Con Term ℓ
    ρ : Wk ℓ n
    A A′ B B′ C : Term n
    a a′ b b′ e e′ : Term n
    k l m t u v : Term n
    s : SigmaMode

-- Generic equality relation used with the logical relation

record EqRelSet : Set₁ where
  constructor eqRel
  field
    ---------------
    -- Relations --
    ---------------

    -- Equality of types
    _⊢_≅_   : Con Term n → (A B : Term n)   → Set

    -- Equality of terms
    _⊢_≅_∷_ : Con Term n → (t u A : Term n) → Set

    -- Equality of neutral terms
    _⊢_~_∷_ : Con Term n → (t u A : Term n) → Set

    ----------------
    -- Properties --
    ----------------

    -- Generic equality compatibility
    ~-to-≅ₜ : Γ ⊢ k ~ l ∷ A
            → Γ ⊢ k ≅ l ∷ A

    -- Judgmental conversion compatibility
    ≅-eq  : Γ ⊢ A ≅ B
          → Γ ⊢ A ≡ B
    ≅ₜ-eq : Γ ⊢ t ≅ u ∷ A
          → Γ ⊢ t ≡ u ∷ A

    -- Universe
    ≅-univ : Γ ⊢ A ≅ B ∷ U
           → Γ ⊢ A ≅ B

    -- Symmetry
    ≅-sym  : Γ ⊢ A ≅ B     → Γ ⊢ B ≅ A
    ≅ₜ-sym : Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ t ∷ A
    ~-sym  : Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ k ∷ A

    -- Transitivity
    ≅-trans  : Γ ⊢ A ≅ B     → Γ ⊢ B ≅ C     → Γ ⊢ A ≅ C
    ≅ₜ-trans : Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ v ∷ A → Γ ⊢ t ≅ v ∷ A
    ~-trans  : Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ m ∷ A → Γ ⊢ k ~ m ∷ A

    -- Conversion
    ≅-conv : Γ ⊢ t ≅ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ≅ u ∷ B
    ~-conv : Γ ⊢ k ~ l ∷ A → Γ ⊢ A ≡ B → Γ ⊢ k ~ l ∷ B

    -- Weakening
    ≅-wk  : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ A ≅ B
          → Δ ⊢ wk ρ A ≅ wk ρ B
    ≅ₜ-wk : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ t ≅ u ∷ A
          → Δ ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A
    ~-wk  : ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ k ~ l ∷ A
          → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A

    -- Weak head expansion
    ≅-red : Γ ⊢ A ⇒* A′
          → Γ ⊢ B ⇒* B′
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A′ ≅ B′
          → Γ ⊢ A  ≅ B

    ≅ₜ-red : Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a′ ∷ B
           → Γ ⊢ b ⇒* b′ ∷ B
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≅ b′ ∷ B
           → Γ ⊢ a  ≅ b  ∷ A

    -- Universe type reflexivity
    ≅-Urefl   : ⊢ Γ → Γ ⊢ U ≅ U

    -- Natural number type reflexivity
    ≅-ℕrefl   : ⊢ Γ → Γ ⊢ ℕ ≅ ℕ
    ≅ₜ-ℕrefl  : ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ∷ U

    -- Empty type reflexivity
    ≅-Emptyrefl   : ⊢ Γ → Γ ⊢ Empty ≅ Empty
    ≅ₜ-Emptyrefl  : ⊢ Γ → Γ ⊢ Empty ≅ Empty ∷ U

    -- Unit type reflexivity
    ≅-Unitrefl   : ⊢ Γ → Γ ⊢ Unit ≅ Unit
    ≅ₜ-Unitrefl  : ⊢ Γ → Γ ⊢ Unit ≅ Unit ∷ U

    -- Unit η-equality
    ≅ₜ-η-unit : Γ ⊢ e ∷ Unit
              → Γ ⊢ e′ ∷ Unit
              → Γ ⊢ e ≅ e′ ∷ Unit

    -- Π-congruence

    ≅-Π-cong  : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H
              → Γ ∙ F ⊢ G ≅ E
              → Γ ⊢ Π p , q ▷ F ▹ G ≅ Π p , q ▷ H ▹ E

    ≅ₜ-Π-cong : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H ∷ U
              → Γ ∙ F ⊢ G ≅ E ∷ U
              → Γ ⊢ Π p , q ▷ F ▹ G ≅ Π p , q ▷ H ▹ E ∷ U

    -- Σ-congruence

    ≅-Σ-cong  : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H
              → Γ ∙ F ⊢ G ≅ E
              → Γ ⊢ Σ⟨ s ⟩ p ▷ F ▹ G ≅ Σ⟨ s ⟩ p ▷ H ▹ E

    ≅ₜ-Σ-cong : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H ∷ U
              → Γ ∙ F ⊢ G ≅ E ∷ U
              → Γ ⊢ Σ⟨ s ⟩ p ▷ F ▹ G ≅ Σ⟨ s ⟩ p ▷ H ▹ E ∷ U

    -- Zero reflexivity
    ≅ₜ-zerorefl : ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ

    -- Successor congruence
    ≅-suc-cong : ∀ {m n} → Γ ⊢ m ≅ n ∷ ℕ → Γ ⊢ suc m ≅ suc n ∷ ℕ

    -- Product congruence
    ≅-prod-cong : ∀ {F G t t′ u u′}
                → Γ ⊢ F
                → Γ ∙ F ⊢ G
                → Γ ⊢ t ≅ t′ ∷ F
                → Γ ⊢ u ≅ u′ ∷ G [ t ]
                → Γ ⊢ prod t u ≅ prod t′ u′ ∷ Σ⟨ s ⟩ q ▷ F ▹ G

    -- η-equality
    ≅-η-eq : ∀ {f g F G}
           → Γ ⊢ F
           → Γ ⊢ f ∷ Π p , q ▷ F ▹ G
           → Γ ⊢ g ∷ Π p , q ▷ F ▹ G
           → Function f
           → Function g
           → Γ ∙ F ⊢ wk1 f ∘ p ▷ var x0 ≅ wk1 g ∘ p ▷ var x0 ∷ G
           → Γ ⊢ f ≅ g ∷ Π p , q ▷ F ▹ G

    -- η for product types
    ≅-Σ-η : ∀ {p r F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ p ∷ Σ⟨ Σₚ ⟩ q ▷ F ▹ G
          → Γ ⊢ r ∷ Σ⟨ Σₚ ⟩ q ▷ F ▹ G
          → Product p
          → Product r
          → Γ ⊢ fst p ≅ fst r ∷ F
          → Γ ⊢ snd p ≅ snd r ∷ G [ fst p ]
          → Γ ⊢ p ≅ r ∷ Σ⟨ Σₚ ⟩ q ▷ F ▹ G

    -- Variable reflexivity
    ~-var : ∀ {x A} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A

    -- Application congruence
    ~-app : ∀ {a b f g F G}
          → Γ ⊢ f ~ g ∷ Π p , q ▷ F ▹ G
          → Γ ⊢ a ≅ b ∷ F
          → Γ ⊢ f ∘ p ▷ a ~ g ∘ p ▷ b ∷ G [ a ]

    -- Product projections congruence
    ~-fst : ∀ {p r F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ p ~ r ∷ Σ⟨ Σₚ ⟩ q ▷ F ▹ G
          → Γ ⊢ fst p ~ fst r ∷ F

    ~-snd : ∀ {p r F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ p ~ r ∷ Σ⟨ Σₚ ⟩ q ▷ F ▹ G
          → Γ ⊢ snd p ~ snd r ∷ G [ fst p ]

    -- Natural recursion congruence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′}
             → Γ ∙ ℕ     ⊢ F
             → Γ ∙ ℕ     ⊢ F ≅ F′
             → Γ         ⊢ z ≅ z′ ∷ F [ zero ]
             → Γ ∙ ℕ ∙ F ⊢ s ≅ s′ ∷ wk1 (F [ suc (var x0) ]↑)
             → Γ         ⊢ n ~ n′ ∷ ℕ
             → Γ         ⊢ natrec p q F z s n ~ natrec p q F′ z′ s′ n′ ∷ F [ n ]

    -- Product recursion congruence
    ~-prodrec : ∀ {F G A A′ t t′ u u′}
             → Γ                 ⊢ F
             → Γ ∙ F             ⊢ G
             → Γ ∙ (Σ⟨ Σᵣ ⟩ q ▷ F ▹ G) ⊢ A ≅ A′
             → Γ                 ⊢ t ~ t′ ∷ Σ⟨ Σᵣ ⟩ q ▷ F ▹ G
             → Γ ∙ F ∙ G         ⊢ u ≅ u′ ∷ A [ prod (var (x0 +1)) (var x0) ]↑²
             → Γ                 ⊢ prodrec p A t u ~ prodrec p A′ t′ u′ ∷ A [ t ]

    -- Empty recursion congruence
    ~-Emptyrec : ∀ {n n′ F F′}
               → Γ ⊢ F ≅ F′
               → Γ ⊢ n ~ n′ ∷ Empty
               → Γ ⊢ Emptyrec p F n ~ Emptyrec p F′ n′ ∷ F

  -- Star reflexivity
  ≅ₜ-starrefl : ⊢ Γ → Γ ⊢ star ≅ star ∷ Unit
  ≅ₜ-starrefl [Γ] = ≅ₜ-η-unit (starⱼ [Γ]) (starⱼ [Γ])

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k l} → Γ ⊢ k ~ l ∷ U → Γ ⊢ k ≅ l
  ~-to-≅ k~l = ≅-univ (~-to-≅ₜ k~l)

  ≅-W-cong : ∀ {F G H E} W
          → Γ ⊢ F
          → Γ ⊢ F ≅ H
          → Γ ∙ F ⊢ G ≅ E
          → Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E
  ≅-W-cong (BΠ p q) = ≅-Π-cong
  ≅-W-cong (BΣ q m) = ≅-Σ-cong

  ≅ₜ-W-cong : ∀ {F G H E} W
            → Γ ⊢ F
            → Γ ⊢ F ≅ H ∷ U
            → Γ ∙ F ⊢ G ≅ E ∷ U
            → Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E ∷ U
  ≅ₜ-W-cong (BΠ p q) = ≅ₜ-Π-cong
  ≅ₜ-W-cong (BΣ q m) = ≅ₜ-Σ-cong
