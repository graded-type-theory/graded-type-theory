------------------------------------------------------------------------
-- Algorithmic equality.
------------------------------------------------------------------------

module Definition.Conversion
  {a} (M : Set a) where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed M

open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality


infix 10 _⊢_~_↑_
infix 10 _⊢_~_↓_
infix 10 _⊢_[conv↑]_
infix 10 _⊢_[conv↓]_
infix 10 _⊢_[conv↑]_∷_
infix 10 _⊢_[conv↓]_∷_

private
  variable
    n : Nat
    Γ : Con Term n
    C F H G E : Term n
    a₀ b₀ g h k l t u v : Term n
    x y : Fin n
    p p′ p″ p₁ p₂ q q′ q″ r r′ : M
    b : BinderMode

mutual
  -- Neutral equality.
  data _⊢_~_↑_ (Γ : Con Term n) : (k l A : Term n) → Set a where

    var-refl      : Γ ⊢ var x ∷ C
                  → x ≡ y
                  → Γ ⊢ var x ~ var y ↑ C

    app-cong      : Γ ⊢ k ~ l ↓ Π p , q ▷ F ▹ G
                  → Γ ⊢ t [conv↑] v ∷ F
                  → Γ ⊢ k ∘⟨ p ⟩ t ~ l ∘⟨ p ⟩ v ↑ G [ t ]

    fst-cong      : Γ ⊢ k ~ l ↓ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ fst p k ~ fst p l ↑ F

    snd-cong      : Γ ⊢ k ~ l ↓ Σₚ p , q ▷ F ▹ G
                  → Γ ⊢ snd p k ~ snd p l ↑ G [ fst p k ]

    natrec-cong   : Γ ∙ ℕ ⊢ F [conv↑] G
                  → Γ ⊢ a₀ [conv↑] b₀ ∷ F [ zero ]
                  → Γ ∙ ℕ ∙ F ⊢ h [conv↑] g ∷ wk1 (F [ suc (var x0) ]↑)
                  → Γ ⊢ k ~ l ↓ ℕ
                  → Γ ⊢ natrec p q r F a₀ h k ~ natrec p q r G b₀ g l ↑ F [ k ]

    prodrec-cong  : Γ ∙ (Σᵣ p , q ▷ F ▹ G) ⊢ C [conv↑] E
                  → Γ ⊢ g ~ h ↓ Σᵣ p , q ▷ F ▹ G
                  → Γ ∙ F ∙ G ⊢ u [conv↑] v ∷ C [ prodᵣ p (var (x0 +1)) (var x0) ]↑²
                  → Γ ⊢ prodrec r p q′ C g u ~ prodrec r p q′ E h v ↑ C [ g ]

    Emptyrec-cong : Γ ⊢ F [conv↑] H
                  → Γ ⊢ k ~ l ↓ Empty
                  → Γ ⊢ Emptyrec p F k ~ Emptyrec p H l ↑ F

  -- Neutral equality with types in WHNF.
  record _⊢_~_↓_ (Γ : Con Term n) (k l B : Term n) : Set a where
    inductive
    constructor [~]
    field
      A     : Term n
      D     : Γ ⊢ A ⇒* B
      whnfB : Whnf B
      k~l   : Γ ⊢ k ~ l ↑ A

  -- Type equality.
  record _⊢_[conv↑]_ (Γ : Con Term n) (A B : Term n) : Set a where
    inductive
    constructor [↑]
    field
      A′ B′  : Term n
      D      : Γ ⊢ A ⇒* A′
      D′     : Γ ⊢ B ⇒* B′
      whnfA′ : Whnf A′
      whnfB′ : Whnf B′
      A′<>B′ : Γ ⊢ A′ [conv↓] B′

  -- Type equality with types in WHNF.
  data _⊢_[conv↓]_ (Γ : Con Term n) : (A B : Term n) → Set a where

    U-refl     : ⊢ Γ → Γ ⊢ U [conv↓] U

    ℕ-refl     : ⊢ Γ → Γ ⊢ ℕ [conv↓] ℕ

    Empty-refl : ⊢ Γ → Γ ⊢ Empty [conv↓] Empty

    Unit-refl  : ⊢ Γ → Γ ⊢ Unit [conv↓] Unit

    ne         : ∀ {K L}
               → Γ ⊢ K ~ L ↓ U
               → Γ ⊢ K [conv↓] L

    ΠΣ-cong    : ∀ {F G H E}
               → Γ ⊢ F
               → Γ ⊢ F [conv↑] H
               → Γ ∙ F ⊢ G [conv↑] E
               → Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G [conv↓] ΠΣ⟨ b ⟩ p , q ▷ H ▹ E

  -- Term equality.
  record _⊢_[conv↑]_∷_ (Γ : Con Term n) (t u A : Term n) : Set a where
    inductive
    constructor [↑]ₜ
    field
      B t′ u′ : Term n
      D       : Γ ⊢ A ⇒* B
      d       : Γ ⊢ t ⇒* t′ ∷ B
      d′      : Γ ⊢ u ⇒* u′ ∷ B
      whnfB   : Whnf B
      whnft′  : Whnf t′
      whnfu′  : Whnf u′
      t<>u    : Γ ⊢ t′ [conv↓] u′ ∷ B

  -- Term equality with types and terms in WHNF.
  data _⊢_[conv↓]_∷_ (Γ : Con Term n) : (t u A : Term n) → Set a where

    ℕ-ins     : Γ ⊢ k ~ l ↓ ℕ
              → Γ ⊢ k [conv↓] l ∷ ℕ

    Empty-ins : Γ ⊢ k ~ l ↓ Empty
              → Γ ⊢ k [conv↓] l ∷ Empty

    Unit-ins  : Γ ⊢ k ~ l ↓ Unit
              → Γ ⊢ k [conv↓] l ∷ Unit

    Σᵣ-ins    : Γ ⊢ k ∷ Σᵣ p , q ▷ F ▹ G
              → Γ ⊢ l ∷ Σᵣ p , q ▷ F ▹ G
              → Γ ⊢ k ~ l ↓ Σᵣ p′ , q′ ▷ H ▹ E
              → Γ ⊢ k [conv↓] l ∷ Σᵣ p , q ▷ F ▹ G

    ne-ins    : ∀ {k l M N}
              → Γ ⊢ k ∷ N
              → Γ ⊢ l ∷ N
              → Neutral N
              → Γ ⊢ k ~ l ↓ M
              → Γ ⊢ k [conv↓] l ∷ N

    univ      : ∀ {A B}
              → Γ ⊢ A ∷ U
              → Γ ⊢ B ∷ U
              → Γ ⊢ A [conv↓] B
              → Γ ⊢ A [conv↓] B ∷ U

    zero-refl : ⊢ Γ → Γ ⊢ zero [conv↓] zero ∷ ℕ

    suc-cong  : ∀ {m n}
              → Γ ⊢ m [conv↑] n ∷ ℕ
              → Γ ⊢ suc m [conv↓] suc n ∷ ℕ

    prod-cong : ∀ {F G t t′ u u′}
              → Γ ⊢ F
              → Γ ∙ F ⊢ G
              → Γ ⊢ t [conv↑] t′ ∷ F
              → Γ ⊢ u [conv↑] u′ ∷ G [ t ]
              → Γ ⊢ prodᵣ p t u [conv↓] prodᵣ p t′ u′ ∷ Σᵣ p , q ▷ F ▹ G

    η-eq      : ∀ {f g F G}
              → Γ ⊢ f ∷ Π p , q ▷ F ▹ G
              → Γ ⊢ g ∷ Π p , q ▷ F ▹ G
              → Function f
              → Function g
              → Γ ∙ F ⊢ wk1 f ∘⟨ p ⟩ var x0 [conv↑] wk1 g ∘⟨ p ⟩ var x0 ∷ G
              → Γ ⊢ f [conv↓] g ∷ Π p , q ▷ F ▹ G

    Σ-η       : Γ ⊢ k ∷ Σₚ p , q ▷ F ▹ G
              → Γ ⊢ l ∷ Σₚ p , q ▷ F ▹ G
              → Product k
              → Product l
              → Γ ⊢ fst p k [conv↑] fst p l ∷ F
              → Γ ⊢ snd p k [conv↑] snd p l ∷ G [ fst p k ]
              → Γ ⊢ k [conv↓] l ∷ Σₚ p , q ▷ F ▹ G

    η-unit    : ∀ {k l}
              → Γ ⊢ k ∷ Unit
              → Γ ⊢ l ∷ Unit
              → Whnf k
              → Whnf l
              → Γ ⊢ k [conv↓] l ∷ Unit

star-refl : ⊢ Γ → Γ ⊢ star [conv↓] star ∷ Unit
star-refl ⊢Γ = η-unit (starⱼ ⊢Γ) (starⱼ ⊢Γ) starₙ starₙ

-- An inversion lemma for prod-cong.

prod-cong⁻¹ :
  ∀ {t′ u′} →
  Γ ⊢ prodᵣ p t u [conv↓] prodᵣ p′ t′ u′ ∷ Σᵣ p″ , q ▷ F ▹ G →
  p ≡ p′ ×
  p ≡ p″ ×
  Γ ⊢ F ×
  Γ ∙ F ⊢ G ×
  (Γ ⊢ t [conv↑] t′ ∷ F) ×
  (Γ ⊢ u [conv↑] u′ ∷ G [ t ])
prod-cong⁻¹ (prod-cong F G t u) = refl , refl , F , G , t , u
