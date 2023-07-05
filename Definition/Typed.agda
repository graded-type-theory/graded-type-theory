------------------------------------------------------------------------
-- Typing and reduction relations
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed
  {ℓ} {M : Set ℓ}
  (R : Type-restrictions M)
  where

open Type-restrictions R

open import Definition.Untyped M hiding (_∷_)

open import Tools.Fin
open import Tools.Nat
open import Tools.Product hiding (_,_)
import Tools.PropositionalEquality as PE


infixl 24 _∙_

private
  variable
    n : Nat
    Γ : Con Term _
    A A′ B C E F F′ G H : Term _
    a f g m n′ s s′ t t′ u u′ v z z′ : Term _
    σ σ′ : Subst _ _
    x : Fin _
    p p′ q q′ r : M
    b : BinderMode
    k : SigmaMode

-- Well-typed variables
data _∷_∈_ : (x : Fin n) (A : Term n) (Γ : Con Term n) → Set ℓ where
  here  :                 x0 ∷ wk1 A ∈ Γ ∙ A
  there : x ∷ A ∈ Γ → (x +1) ∷ wk1 A ∈ Γ ∙ B


mutual
  -- Well-formed context
  data ⊢_ : Con Term n → Set ℓ where
    ε   : ⊢ ε
    _∙_ : ⊢ Γ
        → Γ ⊢ A
        → ⊢ Γ ∙ A

  -- Well-formed type
  data _⊢_ (Γ : Con Term n) : Term n → Set ℓ where
    Uⱼ     : ⊢ Γ → Γ ⊢ U
    ℕⱼ     : ⊢ Γ → Γ ⊢ ℕ
    Emptyⱼ : ⊢ Γ → Γ ⊢ Empty
    Unitⱼ  : ⊢ Γ → Unit-allowed → Γ ⊢ Unit
    ΠΣⱼ    : Γ     ⊢ F
           → Γ ∙ F ⊢ G
           → ΠΣ-allowed b p q
           → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
    univ   : Γ ⊢ A ∷ U
           → Γ ⊢ A

  -- Well-formed term of a type
  data _⊢_∷_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
    ΠΣⱼ       : Γ     ⊢ F ∷ U
              → Γ ∙ F ⊢ G ∷ U
              → ΠΣ-allowed b p q
              → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ∷ U
    ℕⱼ        : ⊢ Γ → Γ ⊢ ℕ ∷ U
    Emptyⱼ    : ⊢ Γ → Γ ⊢ Empty ∷ U
    Unitⱼ     : ⊢ Γ → Unit-allowed → Γ ⊢ Unit ∷ U

    conv      : Γ ⊢ t ∷ A
              → Γ ⊢ A ≡ B
              → Γ ⊢ t ∷ B

    var       : ⊢ Γ
              → x ∷ A ∈ Γ
              → Γ ⊢ var x ∷ A

    lamⱼ      : Γ     ⊢ F
              → Γ ∙ F ⊢ t ∷ G
              → Π-allowed p q
              → Γ     ⊢ lam p t ∷ Π p , q ▷ F ▹ G
    _∘ⱼ_      : Γ ⊢ t ∷ Π p , q ▷ F ▹ G
              → Γ ⊢ u ∷ F
              → Γ ⊢ t ∘⟨ p ⟩ u ∷ G [ u ]₀

    prodⱼ     : Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ F
              → Γ ⊢ u ∷ G [ t ]₀
              → Σ-allowed k p q
              → Γ ⊢ prod k p t u ∷ Σ⟨ k ⟩ p , q ▷ F ▹ G
    fstⱼ      : Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σₚ p , q ▷ F ▹ G
              → Γ ⊢ fst p t ∷ F
    sndⱼ      : Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t ∷ Σₚ p , q ▷ F ▹ G
              → Γ ⊢ snd p t ∷ G [ fst p t ]₀
    prodrecⱼ  : Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ∙ (Σᵣ p , q′ ▷ F ▹ G) ⊢ A
              → Γ ⊢ t ∷ Σᵣ p , q′ ▷ F ▹ G
              → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ p (var x1) (var x0) ]↑²
              → Σᵣ-allowed p q′
              → Γ ⊢ prodrec r p q A t u ∷ A [ t ]₀
    zeroⱼ     : ⊢ Γ
              → Γ ⊢ zero ∷ ℕ
    sucⱼ      : ∀ {n}
              → Γ ⊢     n ∷ ℕ
              → Γ ⊢ suc n ∷ ℕ
    natrecⱼ   : ∀ {n}
              → Γ ∙ ℕ     ⊢ A
              → Γ         ⊢ z ∷ A [ zero ]₀
              → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
              → Γ         ⊢ n ∷ ℕ
              → Γ         ⊢ natrec p q r A z s n ∷ A [ n ]₀

    emptyrecⱼ : Γ ⊢ A → Γ ⊢ t ∷ Empty → Γ ⊢ emptyrec p A t ∷ A

    starⱼ     : ⊢ Γ → Unit-allowed → Γ ⊢ star ∷ Unit

  -- Type equality
  data _⊢_≡_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
    univ   : Γ ⊢ A ≡ B ∷ U
           → Γ ⊢ A ≡ B
    refl   : Γ ⊢ A
           → Γ ⊢ A ≡ A
    sym    : Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ A
    trans  : Γ ⊢ A ≡ B
           → Γ ⊢ B ≡ C
           → Γ ⊢ A ≡ C
    ΠΣ-cong
           : Γ     ⊢ F
           → Γ     ⊢ F ≡ H
           → Γ ∙ F ⊢ G ≡ E
           → ΠΣ-allowed b p q
           → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡ ΠΣ⟨ b ⟩ p , q ▷ H ▹ E

  -- Term equality
  data _⊢_≡_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set ℓ where
    refl          : Γ ⊢ t ∷ A
                  → Γ ⊢ t ≡ t ∷ A
    sym           : Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ u ≡ t ∷ A
    trans         : Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ u ≡ v ∷ A
                  → Γ ⊢ t ≡ v ∷ A
    conv          : Γ ⊢ t ≡ u ∷ A
                  → Γ ⊢ A ≡ B
                  → Γ ⊢ t ≡ u ∷ B
    ΠΣ-cong       : Γ     ⊢ F
                  → Γ     ⊢ F ≡ H ∷ U
                  → Γ ∙ F ⊢ G ≡ E ∷ U
                  → ΠΣ-allowed b p q
                  → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G ≡
                            ΠΣ⟨ b ⟩ p , q ▷ H ▹ E ∷ U
    app-cong      : ∀ {b}
                  → Γ ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
                  → Γ ⊢ a ≡ b ∷ F
                  → Γ ⊢ f ∘⟨ p ⟩ a ≡ g ∘⟨ p ⟩ b ∷ G [ a ]₀
    β-red         : Γ     ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ F ⊢ t ∷ G
                  → Γ     ⊢ a ∷ F
                  → p PE.≡ p′
                  → -- Note that q can be chosen arbitrarily.
                    Π-allowed p q
                  → Γ     ⊢ lam p t ∘⟨ p′ ⟩ a ≡ t [ a ]₀ ∷ G [ a ]₀
    η-eq          : Γ     ⊢ F
                  → Γ     ⊢ f ∷ Π p , q ▷ F ▹ G
                  → Γ     ⊢ g ∷ Π p , q ▷ F ▹ G
                  → Γ ∙ F ⊢ wk1 f ∘⟨ p ⟩ var x0 ≡ wk1 g ∘⟨ p ⟩ var x0 ∷ G
                  → Γ     ⊢ f ≡ g ∷ Π p , q ▷ F ▹ G
    fst-cong      : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t′ ∷ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ fst p t ≡ fst p t′ ∷ F
    snd-cong      : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ u ∷ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ snd p t ≡ snd p u ∷ G [ fst p t ]₀
    Σ-β₁          : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]₀
                  → p PE.≡ p′
                  → -- Note that q can be chosen arbitrarily.
                    Σₚ-allowed p q
                  → Γ ⊢ fst p (prodₚ p′ t u) ≡ t ∷ F
    Σ-β₂          : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ u ∷ G [ t ]₀
                  → p PE.≡ p′
                  → -- Note that q can be chosen arbitrarily.
                    Σₚ-allowed p q
                  → Γ ⊢ snd p (prodₚ p′ t u) ≡ u ∷ G [ fst p (prodₚ p′ t u) ]₀
    Σ-η           : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ∷ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ u ∷ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ fst p t ≡ fst p u ∷ F
                  → Γ ⊢ snd p t ≡ snd p u ∷ G [ fst p t ]₀
                  → Γ ⊢ t ≡ u ∷ Σₚ p , q ▷ F ▹ G
    prod-cong     : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ⊢ t ≡ t′ ∷ F
                  → Γ ⊢ u ≡ u′ ∷ G [ t ]₀
                  → Σ-allowed k p q
                  → Γ ⊢ prod k p t u ≡ prod k p t′ u′ ∷ Σ⟨ k ⟩ p , q ▷ F ▹ G
    prodrec-cong  : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ (Σᵣ p , q′ ▷ F ▹ G) ⊢ A ≡ A′
                  → Γ ⊢ t ≡ t′ ∷ Σᵣ p , q′ ▷ F ▹ G
                  → Γ ∙ F ∙ G ⊢ u ≡ u′ ∷ A [ prodᵣ p (var x1) (var x0) ]↑²
                  → Σᵣ-allowed p q′
                  → Γ ⊢ prodrec r p q A t u ≡ prodrec r p q A′ t′ u′ ∷ A [ t ]₀
    prodrec-β     : Γ ⊢ F
                  → Γ ∙ F ⊢ G
                  → Γ ∙ (Σᵣ p , q′ ▷ F ▹ G) ⊢ A
                  → Γ ⊢ t ∷ F
                  → Γ ⊢ t′ ∷ G [ t ]₀
                  → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ p (var x1) (var x0) ]↑²
                  → p PE.≡ p′
                  → Σᵣ-allowed p q′
                  → Γ ⊢ prodrec r p q A (prodᵣ p′ t t′) u ≡
                        u [ t , t′ ] ∷ A [ prodᵣ p′ t t′ ]₀
    suc-cong      : ∀ {n}
                  → Γ ⊢ m ≡ n ∷ ℕ
                  → Γ ⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong   : ∀ {n}
                  → Γ ∙ ℕ     ⊢ A
                  → Γ ∙ ℕ     ⊢ A ≡ A′
                  → Γ         ⊢ z ≡ z′ ∷ A [ zero ]₀
                  → Γ ∙ ℕ ∙ A ⊢ s ≡ s′ ∷ A [ suc (var x1) ]↑²
                  → Γ         ⊢ n ≡ n′ ∷ ℕ
                  → Γ         ⊢ natrec p q r A z s n ≡
                                natrec p q r A′ z′ s′ n′ ∷
                                A [ n ]₀
    natrec-zero   : Γ ∙ ℕ     ⊢ A
                  → Γ         ⊢ z ∷ A [ zero ]₀
                  → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                  → Γ         ⊢ natrec p q r A z s zero ≡ z ∷ A [ zero ]₀
    natrec-suc    : ∀ {n}
                  → Γ ∙ ℕ     ⊢ A
                  → Γ         ⊢ z ∷ A [ zero ]₀
                  → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                  → Γ         ⊢ n ∷ ℕ
                  → Γ         ⊢ natrec p q r A z s (suc n) ≡
                                s [ n , natrec p q r A z s n ] ∷
                                A [ suc n ]₀
    emptyrec-cong : Γ ⊢ A ≡ B
                  → Γ ⊢ t ≡ u ∷ Empty
                  → Γ ⊢ emptyrec p A t ≡ emptyrec p B u ∷ A
    η-unit        : Γ ⊢ t ∷ Unit
                  → Γ ⊢ t′ ∷ Unit
                  → Γ ⊢ t ≡ t′ ∷ Unit


-- Term reduction
data _⊢_⇒_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set ℓ where
  conv           : Γ ⊢ t ⇒ u ∷ A
                 → Γ ⊢ A ≡ B
                 → Γ ⊢ t ⇒ u ∷ B
  app-subst      : Γ ⊢ t ⇒ u ∷ Π p , q ▷ F ▹ G
                 → Γ ⊢ a ∷ F
                 → Γ ⊢ t ∘⟨ p ⟩ a ⇒ u ∘⟨ p ⟩ a ∷ G [ a ]₀
  β-red          : Γ     ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ F ⊢ t ∷ G
                 → Γ     ⊢ a ∷ F
                 → p PE.≡ p′
                 → -- Note that q can be chosen arbitrarily.
                   Π-allowed p q
                 → Γ     ⊢ lam p t ∘⟨ p′ ⟩ a ⇒ t [ a ]₀ ∷ G [ a ]₀
  fst-subst      : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ u ∷ Σₚ p , q ▷ F ▹ G
                 → Γ ⊢ fst p t ⇒ fst p u ∷ F
  snd-subst      : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ⇒ u ∷ Σₚ p , q ▷ F ▹ G
                 → Γ ⊢ snd p t ⇒ snd p u ∷ G [ fst p t ]₀
  Σ-β₁           : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]₀
                 → p PE.≡ p′
                 → -- Note that q can be chosen arbitrarily.
                   Σₚ-allowed p q
                 → Γ ⊢ fst p (prodₚ p′ t u) ⇒ t ∷ F
  Σ-β₂           : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ u ∷ G [ t ]₀
                 → p PE.≡ p′
                 → -- Note that q can be chosen arbitrarily.
                   Σₚ-allowed p q
                 → Γ ⊢ snd p (prodₚ p′ t u) ⇒ u ∷ G [ fst p (prodₚ p′ t u) ]₀
  prodrec-subst  : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ (Σᵣ p , q′ ▷ F ▹ G) ⊢ A
                 → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ p (var x1) (var x0) ]↑²
                 → Γ ⊢ t ⇒ t′ ∷ Σᵣ p , q′ ▷ F ▹ G
                 → Σᵣ-allowed p q′
                 → Γ ⊢ prodrec r p q A t u ⇒ prodrec r p q A t′ u ∷ A [ t ]₀
  prodrec-β      : Γ ⊢ F
                 → Γ ∙ F ⊢ G
                 → Γ ∙ (Σᵣ p , q′ ▷ F ▹ G) ⊢ A
                 → Γ ⊢ t ∷ F
                 → Γ ⊢ t′ ∷ G [ t ]₀
                 → Γ ∙ F ∙ G ⊢ u ∷ A [ prodᵣ p (var x1) (var x0) ]↑²
                 → p PE.≡ p′
                 → Σᵣ-allowed p q′
                 → Γ ⊢ prodrec r p q A (prodᵣ p′ t t′) u ⇒
                       u [ t , t′ ] ∷ A [ prodᵣ p′ t t′ ]₀
  natrec-subst   : ∀ {n}
                 → Γ ∙ ℕ     ⊢ A
                 → Γ         ⊢ z ∷ A [ zero ]₀
                 → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                 → Γ         ⊢ n ⇒ n′ ∷ ℕ
                 → Γ         ⊢ natrec p q r A z s n ⇒
                               natrec p q r A z s n′ ∷
                               A [ n ]₀
  natrec-zero    : Γ ∙ ℕ     ⊢ A
                 → Γ         ⊢ z ∷ A [ zero ]₀
                 → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                 → Γ         ⊢ natrec p q r A z s zero ⇒ z ∷ A [ zero ]₀
  natrec-suc     : ∀ {n}
                 → Γ ∙ ℕ     ⊢ A
                 → Γ         ⊢ z ∷ A [ zero ]₀
                 → Γ ∙ ℕ ∙ A ⊢ s ∷ A [ suc (var x1) ]↑²
                 → Γ         ⊢ n ∷ ℕ
                 → Γ         ⊢ natrec p q r A z s (suc n) ⇒
                               s [ n , natrec p q r A z s n ] ∷
                               A [ suc n ]₀
  emptyrec-subst : ∀ {n}
                 → Γ ⊢ A
                 → Γ     ⊢ n ⇒ n′ ∷ Empty
                 → Γ     ⊢ emptyrec p A n ⇒ emptyrec p A n′ ∷ A

-- Type reduction
data _⊢_⇒_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
  univ : Γ ⊢ A ⇒ B ∷ U
       → Γ ⊢ A ⇒ B

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con Term n) : Term n → Term n → Term n → Set ℓ where
  id  : Γ ⊢ t ∷ A
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : Γ ⊢ t  ⇒  t′ ∷ A
      → Γ ⊢ t′ ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
  id  : Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : Γ ⊢ A  ⇒  A′
      → Γ ⊢ A′ ⇒* B
      → Γ ⊢ A  ⇒* B

-- Type reduction to whnf
_⊢_↘_ : (Γ : Con Term n) → Term n → Term n → Set ℓ
Γ ⊢ A ↘ B = Γ ⊢ A ⇒* B × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_ : (Γ : Con Term n) → Term n → Term n → Term n → Set ℓ
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf u

-- Type equality with well-formed types
_⊢_:≡:_ : (Γ : Con Term n) → Term n → Term n → Set ℓ
Γ ⊢ A :≡: B = Γ ⊢ A × Γ ⊢ B × (Γ ⊢ A ≡ B)

-- Term equality with well-formed terms
_⊢_:≡:_∷_ : (Γ : Con Term n) → Term n → Term n → Term n → Set ℓ
Γ ⊢ t :≡: u ∷ A = (Γ ⊢ t ∷ A) × (Γ ⊢ u ∷ A) × (Γ ⊢ t ≡ u ∷ A)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_ (Γ : Con Term n) (A B : Term n) : Set ℓ where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A
    ⊢B : Γ ⊢ B
    D  : Γ ⊢ A ⇒* B

open _⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_ (Γ : Con Term n) (t u A : Term n) : Set ℓ where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A
    ⊢u : Γ ⊢ u ∷ A
    d  : Γ ⊢ t ⇒* u ∷ A

open _⊢_:⇒*:_∷_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

-- Well-formed substitutions.
data _⊢ˢ_∷_ {k} (Δ : Con Term k) :
       (σ : Subst k n) (Γ : Con Term n) → Set ℓ where
  id  : Δ ⊢ˢ σ ∷ ε
  _,_ : Δ ⊢ˢ tail σ ∷ Γ
      → Δ ⊢  head σ ∷ A [ tail σ ]
      → Δ ⊢ˢ σ      ∷ Γ ∙ A

-- Conversion of well-formed substitutions.
data _⊢ˢ_≡_∷_ {k} (Δ : Con Term k) :
       (σ σ′ : Subst k n) (Γ : Con Term n) → Set ℓ where
  id  : Δ ⊢ˢ σ ≡ σ′ ∷ ε
  _,_ : Δ ⊢ˢ tail σ ≡ tail σ′ ∷ Γ
      → Δ ⊢  head σ ≡ head σ′ ∷ A [ tail σ ]
      → Δ ⊢ˢ      σ ≡ σ′      ∷ Γ ∙ A

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamental theorem for substitutions.

⟦_⟧ⱼ : (W : BindingType) → ∀ {F G}
     → Γ     ⊢ F
     → Γ ∙ F ⊢ G
     → BindingType-allowed W
     → Γ     ⊢ ⟦ W ⟧ F ▹ G
⟦ BΠ _ _   ⟧ⱼ = ΠΣⱼ
⟦ BΣ _ _ _ ⟧ⱼ = ΠΣⱼ

⟦_⟧ⱼᵤ : (W : BindingType) → ∀ {F G}
     → Γ     ⊢ F ∷ U
     → Γ ∙ F ⊢ G ∷ U
     → BindingType-allowed W
     → Γ     ⊢ ⟦ W ⟧ F ▹ G ∷ U
⟦ BΠ _ _   ⟧ⱼᵤ = ΠΣⱼ
⟦ BΣ _ _ _ ⟧ⱼᵤ = ΠΣⱼ
