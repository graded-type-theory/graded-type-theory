------------------------------------------------------------------------
-- Negative types (types for which all branches end in ⊥).
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Application.NegativeAxioms.NegativeType
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M as U

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Substitution R
open import Definition.Typed.Weakening R as T
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Consequences.Inequality R as I
open import Definition.Typed.Consequences.Injectivity R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
open import Tools.Relation

-- Preliminaries
---------------------------------------------------------------------------

private variable
  m n   : Nat
  ξ     : DExt _ _ _
  ∇ ∇′  : DCon (Term 0) _
  ρ     : Wk _ _
  σ     : Subst _ _
  Γ Δ   : Con Term _
  Η     : Cons _ _
  A B C : Term _
  t u   : Term _
  p q   : M
  s     : Strength
  l     : Universe-level

-- Negative types
---------------------------------------------------------------------------

-- A type is negative if all of its branches end in ⊥ or U l.
-- The prime example is negation ¬A.

data NegativeType (Γ : Cons m n) : Term n → Set a where

  empty : NegativeType Γ Empty

  pi    : Γ ⊢ A
        → NegativeType (Γ »∙ A) B
        → NegativeType Γ (Π p , q ▷ A ▹ B)

  sigma : Γ ⊢ A
        → NegativeType Γ A
        → NegativeType (Γ »∙ A) B
        → NegativeType Γ (Σˢ p , q ▷ A ▹ B)

  universe : NegativeType Γ (U l)

  conv  : NegativeType Γ A
        → Γ ⊢ A ≡ B
        → NegativeType Γ B

-- Lemma: Negative types are closed under weakening.

wkNeg :
  ∇ » ρ ∷ʷ Δ ⊇ Γ →
  NegativeType (∇ » Γ) A → NegativeType (∇ » Δ) (U.wk ρ A)

wkNeg w empty
  = empty

wkNeg w (pi dA nB)
  = pi dA' (wkNeg (liftʷʷ w dA') nB)
    where dA' = T.wk w dA

wkNeg w (sigma dA nA nB)
  = sigma dA' (wkNeg w nA) (wkNeg (liftʷʷ w dA') nB)
    where dA' = T.wk w dA

wkNeg _ universe = universe

wkNeg w (conv n c)
  = conv (wkNeg w n) (wkEq w c)

opaque

  -- Lemma: Negative types are closed under weakening of the
  -- definition context.

  defn-wkNeg :
    ξ » ∇′ ⊇ ∇ → NegativeType (∇ » Γ) A → NegativeType (∇′ » Γ) A
  defn-wkNeg _ empty =
    empty
  defn-wkNeg ∇′⊇∇ (pi ⊢A B-neg) =
    pi (defn-wk ∇′⊇∇ ⊢A) (defn-wkNeg ∇′⊇∇ B-neg)
  defn-wkNeg ∇′⊇∇ (sigma ⊢A A-neg B-neg) =
    sigma (defn-wk ∇′⊇∇ ⊢A) (defn-wkNeg ∇′⊇∇ A-neg)
      (defn-wkNeg ∇′⊇∇ B-neg)
  defn-wkNeg _ universe =
    universe
  defn-wkNeg ∇′⊇∇ (conv ⊢A A≡B) =
    conv (defn-wkNeg ∇′⊇∇ ⊢A) (defn-wkEq ∇′⊇∇ A≡B)

-- Lemma: Negative types are closed under parallel substitution.

subNeg :
  NegativeType (∇ » Γ) A → ∇ » Δ ⊢ˢʷ σ ∷ Γ →
  NegativeType (∇ » Δ) (A [ σ ])

subNeg empty _ = empty

subNeg (pi ⊢A n) s
  = pi (subst-⊢ ⊢A s) (subNeg n (⊢ˢʷ∷-⇑′ ⊢A s))

subNeg (sigma ⊢A nA nB) s
  = sigma (subst-⊢ ⊢A s) (subNeg nA s) (subNeg nB (⊢ˢʷ∷-⇑′ ⊢A s))

subNeg universe _ = universe

subNeg (conv n c) s = conv (subNeg n s) (subst-⊢≡ c (refl-⊢ˢʷ≡∷ s))

-- Corollary: Negative types are closed under single substitution.

subNeg1 :
  NegativeType (∇ » Γ ∙ A) B → ∇ » Γ ⊢ t ∷ A →
  NegativeType (∇ » Γ) (B [ t ]₀)
subNeg1 n ⊢t = subNeg n (⊢ˢʷ∷-sgSubst ⊢t)

-- Lemma: The first component of a negative Σ-type is negative (given
-- a certain assumption).

fstNeg :
  ⦃ ok : No-equality-reflection or-empty Η .vars ⦄ →
  NegativeType Η C →
  Η ⊢ C ≡ Σˢ p , q ▷ A ▹ B →
  NegativeType Η A
fstNeg empty          c = ⊥-elim (Empty≢ΠΣⱼ c)
fstNeg (pi _ _)       c = ⊥-elim (Π≢Σⱼ c)
fstNeg (sigma _ nA _) c = conv nA (proj₁ (ΠΣ-injectivity c))
fstNeg universe       c = ⊥-elim (U≢ΠΣⱼ c)
fstNeg (conv n c)    c' = fstNeg n (trans c c')

-- Lemma: Any instance of the second component of a negative Σ-type is
-- negative (given a certain assumption).

sndNeg :
  ⦃ ok : No-equality-reflection or-empty Η .vars ⦄ →
  NegativeType Η C →
  Η ⊢ C ≡ Σˢ p , q ▷ A ▹ B →
  Η ⊢ t ∷ A →
  NegativeType Η (B [ t ]₀)
sndNeg empty          c = ⊥-elim (Empty≢ΠΣⱼ c)
sndNeg (pi _ _)       c = ⊥-elim (Π≢Σⱼ c)
sndNeg (sigma _ _ nB) c ⊢t =
  let (cA , cB , _ , _) = ΠΣ-injectivity c
      ⊢t                = conv ⊢t (sym cA)
  in
  conv (subNeg nB (⊢ˢʷ∷-sgSubst ⊢t)) (cB (refl ⊢t))
sndNeg universe      c  = ⊥-elim (U≢ΠΣⱼ c)
sndNeg (conv n c)    c' = sndNeg n (trans c c')

-- Lemma: Any instance of the codomain of a negative Π-type is
-- negative (given a certain assumption).

appNeg :
  ⦃ ok : No-equality-reflection or-empty Η .vars ⦄ →
  NegativeType Η C → Η ⊢ C ≡ Π p , q ▷ A ▹ B → Η ⊢ t ∷ A →
  NegativeType Η (B [ t ]₀)
appNeg empty          c = ⊥-elim (Empty≢ΠΣⱼ c)
appNeg (sigma _ _ _)  c = ⊥-elim (Π≢Σⱼ (sym c))
appNeg (pi _ nB) c ⊢t =
  let (cA , cB , _ , _) = ΠΣ-injectivity c
      ⊢t                = conv ⊢t (sym cA)
  in
  conv (subNeg nB (⊢ˢʷ∷-sgSubst ⊢t)) (cB (refl ⊢t))
appNeg universe      c  = ⊥-elim (U≢ΠΣⱼ c)
appNeg (conv n c)    c' = appNeg n (trans c c')

-- Lemma: The type ℕ is not negative (given a certain assumption).

¬negℕ :
  ⦃ ok : No-equality-reflection or-empty Η .vars ⦄ →
  NegativeType Η C → Η ⊢ C ≡ ℕ → ⊥
¬negℕ empty         c = ℕ≢Emptyⱼ (sym c)
¬negℕ (pi _ _)      c = ℕ≢ΠΣⱼ (sym c)
¬negℕ (sigma _ _ _) c = ℕ≢ΠΣⱼ (sym c)
¬negℕ universe      c = U≢ℕ c
¬negℕ (conv n c)   c' = ¬negℕ n (trans c c')

-- Lemma: The type Σʷ is not negative (given a certain assumption).

¬negΣʷ :
  ⦃ ok : No-equality-reflection or-empty Η .vars ⦄ →
  NegativeType Η C → Η ⊢ C ≡ Σʷ p , q ▷ A ▹ B → ⊥
¬negΣʷ empty         c = Empty≢ΠΣⱼ c
¬negΣʷ (pi _ _)      c = Π≢Σⱼ c
¬negΣʷ (sigma _ _ _) c = Σˢ≢Σʷⱼ c
¬negΣʷ universe      c = U≢ΠΣⱼ c
¬negΣʷ (conv n c)   c' = ¬negΣʷ n (trans c c')

-- Lemma: Unit types are not negative (given a certain assumption).

¬negUnit :
  ⦃ ok : No-equality-reflection or-empty Η .vars ⦄ →
  NegativeType Η C → Η ⊢ C ≡ Unit s l → ⊥
¬negUnit empty c = Empty≢Unitⱼ c
¬negUnit (pi _ _) c = Unit≢ΠΣⱼ (sym c)
¬negUnit (sigma _ _ _) c = Unit≢ΠΣⱼ (sym c)
¬negUnit universe      c = U≢Unitⱼ c
¬negUnit (conv n c) c′ = ¬negUnit n (trans c c′)

opaque

  -- Identity types are not negative (given a certain assumption).

  ¬negId :
    ⦃ ok : No-equality-reflection or-empty Η .vars ⦄ →
    NegativeType Η A → ¬ Η ⊢ A ≡ Id B t u
  ¬negId empty         = Id≢Empty ∘→ sym
  ¬negId (pi _ _)      = I.Id≢ΠΣ ∘→ sym
  ¬negId (sigma _ _ _) = I.Id≢ΠΣ ∘→ sym
  ¬negId universe      = I.Id≢U ∘→ sym
  ¬negId (conv n B≡A)  = ¬negId n ∘→ trans B≡A
