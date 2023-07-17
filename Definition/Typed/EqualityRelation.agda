------------------------------------------------------------------------
-- An abstract set of equality relations over which the logical relation
-- is parameterized.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.EqualityRelation
  {ℓ} {M : Set ℓ}
  (R : Type-restrictions M)
  where

open Type-restrictions R

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Weakening R using (_∷_⊇_)

open import Tools.Fin
open import Tools.Level
open import Tools.Nat

private
  variable
    p q q′ r : M
    n n′ : Nat
    Γ : Con Term n
    Δ : Con Term n′
    ρ : Wk n′ n
    A A′ B B′ C : Term n
    a a′ b b′ e e′ : Term n
    k l m t u v : Term n
    s : SigmaMode
    bm : BinderMode

-- Generic equality relation used with the logical relation

record EqRelSet : Set (lsuc ℓ) where
  constructor eqRel
  field
    ---------------
    -- Relations --
    ---------------

    -- Equality of types
    _⊢_≅_   : Con Term n → (A B : Term n)   → Set ℓ

    -- Equality of terms
    _⊢_≅_∷_ : Con Term n → (t u A : Term n) → Set ℓ

    -- Equality of neutral terms
    _⊢_~_∷_ : Con Term n → (t u A : Term n) → Set ℓ

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
    ≅-wk  : ρ ∷ Δ ⊇ Γ
          → ⊢ Δ
          → Γ ⊢ A ≅ B
          → Δ ⊢ wk ρ A ≅ wk ρ B
    ≅ₜ-wk : ρ ∷ Δ ⊇ Γ
          → ⊢ Δ
          → Γ ⊢ t ≅ u ∷ A
          → Δ ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A
    ~-wk  : ρ ∷ Δ ⊇ Γ
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
    ≅-Unitrefl   : ⊢ Γ → Unit-allowed → Γ ⊢ Unit ≅ Unit
    ≅ₜ-Unitrefl  : ⊢ Γ → Unit-allowed → Γ ⊢ Unit ≅ Unit ∷ U

    -- Unit η-equality
    ≅ₜ-η-unit : Γ ⊢ e ∷ Unit
              → Γ ⊢ e′ ∷ Unit
              → Γ ⊢ e ≅ e′ ∷ Unit

    -- Π- and Σ-congruence

    ≅-ΠΣ-cong : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H
              → Γ ∙ F ⊢ G ≅ E
              → ΠΣ-allowed bm p q
              → Γ ⊢ ΠΣ⟨ bm ⟩ p , q ▷ F ▹ G ≅ ΠΣ⟨ bm ⟩ p , q ▷ H ▹ E

    ≅ₜ-ΠΣ-cong
              : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H ∷ U
              → Γ ∙ F ⊢ G ≅ E ∷ U
              → ΠΣ-allowed bm p q
              → Γ ⊢ ΠΣ⟨ bm ⟩ p , q ▷ F ▹ G ≅ ΠΣ⟨ bm ⟩ p , q ▷ H ▹ E ∷ U

    -- Zero reflexivity
    ≅ₜ-zerorefl : ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ

    -- Successor congruence
    ≅-suc-cong : ∀ {m n} → Γ ⊢ m ≅ n ∷ ℕ → Γ ⊢ suc m ≅ suc n ∷ ℕ

    -- Product congruence
    ≅-prod-cong : ∀ {F G t t′ u u′}
                → Γ ⊢ F
                → Γ ∙ F ⊢ G
                → Γ ⊢ t ≅ t′ ∷ F
                → Γ ⊢ u ≅ u′ ∷ G [ t ]₀
                → Σᵣ-allowed p q
                → Γ ⊢ prodᵣ p t u ≅ prodᵣ p t′ u′ ∷ Σᵣ p , q ▷ F ▹ G

    -- η-equality
    ≅-η-eq : ∀ {f g F G}
           → Γ ⊢ F
           → Γ ⊢ f ∷ Π p , q ▷ F ▹ G
           → Γ ⊢ g ∷ Π p , q ▷ F ▹ G
           → Function f
           → Function g
           → Γ ∙ F ⊢ wk1 f ∘⟨ p ⟩ var x0 ≅ wk1 g ∘⟨ p ⟩ var x0 ∷ G
           → Γ ⊢ f ≅ g ∷ Π p , q ▷ F ▹ G

    -- η for product types
    ≅-Σ-η : ∀ {r s F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ r ∷ Σₚ p , q ▷ F ▹ G
          → Γ ⊢ s ∷ Σₚ p , q ▷ F ▹ G
          → Product r
          → Product s
          → Γ ⊢ fst p r ≅ fst p s ∷ F
          → Γ ⊢ snd p r ≅ snd p s ∷ G [ fst p r ]₀
          → Γ ⊢ r ≅ s ∷ Σₚ p , q ▷ F ▹ G

    -- Variable reflexivity
    ~-var : ∀ {x A} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A

    -- Application congruence
    ~-app : ∀ {a b f g F G}
          → Γ ⊢ f ~ g ∷ Π p , q ▷ F ▹ G
          → Γ ⊢ a ≅ b ∷ F
          → Γ ⊢ f ∘⟨ p ⟩ a ~ g ∘⟨ p ⟩ b ∷ G [ a ]₀

    -- Product projections congruence
    ~-fst : ∀ {r s F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ r ~ s ∷ Σₚ p , q ▷ F ▹ G
          → Γ ⊢ fst p r ~ fst p s ∷ F

    ~-snd : ∀ {r s F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ r ~ s ∷ Σₚ p , q ▷ F ▹ G
          → Γ ⊢ snd p r ~ snd p s ∷ G [ fst p r ]₀

    -- Natural recursion congruence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′}
             → Γ ∙ ℕ     ⊢ F
             → Γ ∙ ℕ     ⊢ F ≅ F′
             → Γ         ⊢ z ≅ z′ ∷ F [ zero ]₀
             → Γ ∙ ℕ ∙ F ⊢ s ≅ s′ ∷ F [ suc (var x1) ]↑²
             → Γ         ⊢ n ~ n′ ∷ ℕ
             → Γ         ⊢ natrec p q r F z s n ~ natrec p q r F′ z′ s′ n′ ∷ F [ n ]₀

    -- Product recursion congruence
    ~-prodrec : ∀ {F G A A′ t t′ u u′}
             → Γ                      ⊢ F
             → Γ ∙ F                  ⊢ G
             → Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ A ≅ A′
             → Γ                      ⊢ t ~ t′ ∷ Σᵣ p , q ▷ F ▹ G
             → Γ ∙ F ∙ G              ⊢ u ≅ u′ ∷ A [ prodᵣ p (var x1) (var x0) ]↑²
             → Σᵣ-allowed p q
             → Γ                      ⊢ prodrec r p q′ A t u ~ prodrec r p q′ A′ t′ u′ ∷ A [ t ]₀

    -- Empty recursion congruence
    ~-emptyrec : ∀ {n n′ F F′}
               → Γ ⊢ F ≅ F′
               → Γ ⊢ n ~ n′ ∷ Empty
               → Γ ⊢ emptyrec p F n ~ emptyrec p F′ n′ ∷ F

  -- Star reflexivity
  ≅ₜ-starrefl : ⊢ Γ → Unit-allowed → Γ ⊢ star ≅ star ∷ Unit
  ≅ₜ-starrefl [Γ] ok = ≅ₜ-η-unit (starⱼ [Γ] ok) (starⱼ [Γ] ok)

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k l} → Γ ⊢ k ~ l ∷ U → Γ ⊢ k ≅ l
  ~-to-≅ k~l = ≅-univ (~-to-≅ₜ k~l)

  ≅-W-cong : ∀ {F G H E} W
          → Γ ⊢ F
          → Γ ⊢ F ≅ H
          → Γ ∙ F ⊢ G ≅ E
          → BindingType-allowed W
          → Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E
  ≅-W-cong BΠ! = ≅-ΠΣ-cong
  ≅-W-cong BΣ! = ≅-ΠΣ-cong

  ≅ₜ-W-cong : ∀ {F G H E} W
            → Γ ⊢ F
            → Γ ⊢ F ≅ H ∷ U
            → Γ ∙ F ⊢ G ≅ E ∷ U
            → BindingType-allowed W
            → Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E ∷ U
  ≅ₜ-W-cong BΠ! = ≅ₜ-ΠΣ-cong
  ≅ₜ-W-cong BΣ! = ≅ₜ-ΠΣ-cong
