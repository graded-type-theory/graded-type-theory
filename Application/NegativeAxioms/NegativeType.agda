module Application.NegativeAxioms.NegativeType
  {a} (M : Set a) where

open import Definition.Untyped M as U hiding (_∷_)

open import Definition.Typed M
open import Definition.Typed.Properties M
open import Definition.Typed.Weakening M as T
open import Definition.Typed.Consequences.Inequality M
open import Definition.Typed.Consequences.Injectivity M
open import Definition.Typed.Consequences.Substitution M

open import Tools.Empty
open import Tools.Nat
open import Tools.Product

-- Preliminaries
---------------------------------------------------------------------------

private
  Ty  = Term
  Cxt = Con Ty
  variable
    m m'  : Nat
    ρ     : Wk m m'
    σ     : Subst m m'
    Γ Δ   : Con Term m
    A B C : Term m
    t u   : Term m
    p q   : M

-- Negative types
---------------------------------------------------------------------------

-- A type is negative if all of its branches end in ⊥.
-- The prime example is negation ¬A.

data NegativeType (Γ : Cxt m) : Ty m → Set a where

  empty : NegativeType Γ Empty

  pi    : Γ ⊢ A
        → NegativeType (Γ ∙ A) B
        → NegativeType Γ (Π p , q ▷ A ▹ B)

  sigma : Γ ⊢ A
        → NegativeType Γ A
        → NegativeType (Γ ∙ A) B
        → NegativeType Γ (Σₚ p , q ▷ A ▹ B)

  conv  : NegativeType Γ A
        → Γ ⊢ A ≡ B
        → NegativeType Γ B

-- Lemma: Negative types are closed under weakening.

wkNeg : ρ ∷ Δ ⊆ Γ → ⊢ Δ → NegativeType Γ A → NegativeType Δ (U.wk ρ A)

wkNeg w ⊢Δ empty
  = empty

wkNeg w ⊢Δ (pi dA nB)
  = pi dA' (wkNeg (lift w) (⊢Δ ∙ dA') nB)
    where dA' = T.wk w ⊢Δ dA

wkNeg w ⊢Δ (sigma dA nA nB)
  = sigma dA' (wkNeg w ⊢Δ nA) (wkNeg (lift w) (⊢Δ ∙ dA') nB)
    where dA' = T.wk w ⊢Δ dA

wkNeg w ⊢Δ (conv n c)
  = conv (wkNeg w ⊢Δ n) (wkEq w ⊢Δ c)

-- Lemma: Negative types are closed under parallel substitution.

subNeg : NegativeType Γ A → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → NegativeType Δ (subst σ A)

subNeg empty _ _ = empty

subNeg (pi ⊢A n) s ⊢Δ
  = pi ⊢σA (subNeg n (liftSubst′ (wf ⊢A) ⊢Δ ⊢A s) (⊢Δ ∙ ⊢σA))
    where ⊢σA = substitution ⊢A s ⊢Δ

subNeg (sigma ⊢A nA nB) s ⊢Δ
  = sigma ⊢σA (subNeg nA s ⊢Δ) (subNeg nB (liftSubst′ (wf ⊢A) ⊢Δ ⊢A s) (⊢Δ ∙ ⊢σA))
    where ⊢σA = substitution ⊢A s ⊢Δ

subNeg (conv n c) s ⊢Δ = conv (subNeg n s ⊢Δ) (substitutionEq c (substRefl s) ⊢Δ)

-- Corollary: Negative types are closed under single substitution.

subNeg1 : NegativeType (Γ ∙ A) B → Γ ⊢ t ∷ A → NegativeType Γ (B [ t ])
subNeg1 n ⊢t = subNeg n (singleSubst ⊢t) (wfTerm ⊢t)

-- Lemma: The first component of a negative Σ-type is negative.

fstNeg :
  NegativeType Γ C →
  Γ ⊢ C ≡ Σₚ p , q ▷ A ▹ B →
  NegativeType Γ A
fstNeg empty          c = ⊥-elim (Empty≢Σⱼ c)
fstNeg (pi _ _)       c = ⊥-elim (Π≢Σⱼ c)
fstNeg (sigma _ nA _) c = conv nA (proj₁ (Σ-injectivity c))
fstNeg (conv n c)    c' = fstNeg n (trans c c')

-- Lemma: Any instance of the second component of a negative Σ-type is negative.

sndNeg :
  NegativeType Γ C →
  Γ ⊢ C ≡ Σₚ p , q ▷ A ▹ B →
  Γ ⊢ t ∷ A →
  NegativeType Γ (B [ t ])
sndNeg empty          c = ⊥-elim (Empty≢Σⱼ c)
sndNeg (pi _ _)       c = ⊥-elim (Π≢Σⱼ c)
sndNeg (sigma _ _ nB) c ⊢t = let (cA , cB , _ , _) = Σ-injectivity c in
    subNeg (conv nB cB) (singleSubst (conv ⊢t (sym cA))) (wfTerm ⊢t)
sndNeg (conv n c)    c' = sndNeg n (trans c c')

-- Lemma: Any instance of the codomain of a negative Π-type is negative.

appNeg : NegativeType Γ C → Γ ⊢ C ≡ Π p , q ▷ A ▹ B → Γ ⊢ t ∷ A → NegativeType Γ (B [ t ])
appNeg empty          c = ⊥-elim (Empty≢Πⱼ c)
appNeg (sigma _ _ _)  c = ⊥-elim (Π≢Σⱼ (sym c))
appNeg (pi _ nB) c ⊢t = let (cA , cB , _ , _) = injectivity c in
  subNeg (conv nB cB) (singleSubst (conv ⊢t (sym cA))) (wfTerm ⊢t)
appNeg (conv n c)    c' = appNeg n (trans c c')

-- Lemma: The type ℕ is not negative.

¬negℕ : NegativeType Γ C → Γ ⊢ C ≡ ℕ → ⊥
¬negℕ empty         c = ℕ≢Emptyⱼ (sym c)
¬negℕ (pi _ _)      c = ℕ≢Π (sym c)
¬negℕ (sigma _ _ _) c = ℕ≢Σ (sym c)
¬negℕ (conv n c)   c' = ¬negℕ n (trans c c')

-- Lemma: The type Σᵣ is not negative

¬negΣᵣ : NegativeType Γ C → Γ ⊢ C ≡ Σᵣ p , q ▷ A ▹ B → ⊥
¬negΣᵣ empty         c = Empty≢Bⱼ BΣ! c
¬negΣᵣ (pi _ _)      c = Π≢Σⱼ c
¬negΣᵣ (sigma _ _ _) c = Σₚ≢Σᵣⱼ c
¬negΣᵣ (conv n c)   c' = ¬negΣᵣ n (trans c c')
