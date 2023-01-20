-- Proof that consistent negative axioms do not jeopardize canonicity.
-- https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

{-# OPTIONS --without-K --safe #-}

module Application.NegativeAxioms.Canonicity where

open import Definition.Modality.Instances.Erasure
open import Definition.Modality.Instances.Erasure.Modality (_≤ ω)
open import Definition.Modality.Instances.Erasure.Properties (_≤ ω)
open import Definition.Modality.Context ErasureModality
open import Definition.Modality.Usage ErasureModality
open import Definition.Modality.Usage.Inversion ErasureModality

open import Definition.Untyped Erasure as U hiding (_∷_)

open import Definition.Typed Erasure′
open import Definition.Typed.Properties Erasure′
open import Definition.Typed.Weakening Erasure′ as T
open import Definition.Typed.Consequences.Inequality Erasure′
open import Definition.Typed.Consequences.Injectivity Erasure′
open import Definition.Typed.Consequences.Substitution Erasure′
open import Definition.Typed.Consequences.Syntactic Erasure′

open import Definition.Conversion.Consequences.Completeness Erasure′
open import Definition.Conversion.FullReduction Erasure′

open import Tools.Empty
open import Tools.Fin
open import Tools.Nat
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Unit

-- Preliminaries
---------------------------------------------------------------------------

private
  Ty  = Term
  Cxt = Con Ty
  variable
    m m'  : Nat
    x     : Fin m
    ρ     : Wk m m'
    σ     : Subst m m'
    Γ Δ   : Con Term m
    A B C : Term m
    t u   : Term m
    p q   : Erasure
    γ     : Conₘ m

-- Numerals

data Numeral {m : Nat} : Term m → Set where
  zeroₙ : Numeral zero
  sucₙ  : Numeral t → Numeral (suc t)

-- Negative types
---------------------------------------------------------------------------

-- A type is negative if all of its branches end in ⊥.
-- The prime example is negation ¬A.

data NegativeType (Γ : Cxt m) : Ty m → Set where

  empty : NegativeType Γ Empty

  pi    : Γ ⊢ A
        → NegativeType (Γ ∙ A) B
        → NegativeType Γ (Π p , q ▷ A ▹ B)

  sigma : Γ ⊢ A
        → NegativeType Γ A
        → NegativeType (Γ ∙ A) B
        → NegativeType Γ (Σₚ q ▷ A ▹ B)

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

fstNeg : NegativeType Γ C → Γ ⊢ C ≡ Σₚ q ▷ A ▹ B → NegativeType Γ A
fstNeg empty          c = ⊥-elim (Empty≢Σⱼ c)
fstNeg (pi _ _)       c = ⊥-elim (Π≢Σⱼ c)
fstNeg (sigma _ nA _) c = conv nA (proj₁ (Σ-injectivity c))
fstNeg (conv n c)    c' = fstNeg n (trans c c')

-- Lemma: Any instance of the second component of a negative Σ-type is negative.

sndNeg : NegativeType Γ C → Γ ⊢ C ≡ Σₚ q ▷ A ▹ B → Γ ⊢ t ∷ A → NegativeType Γ (B [ t ])
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

¬negΣᵣ : NegativeType Γ C → Γ ⊢ C ≡ Σᵣ q ▷ A ▹ B → ⊥
¬negΣᵣ empty         c = Empty≢Bⱼ BΣ! c
¬negΣᵣ (pi _ _)      c = Π≢Σⱼ c
¬negΣᵣ (sigma _ _ _) c = Σₚ≢Σᵣⱼ c
¬negΣᵣ (conv n c)   c' = ¬negΣᵣ n (trans c c')

-- Negative contexts
---------------------------------------------------------------------------

-- A context is negative if all of its type entries are negative.

data NegativeErasedContext : Con Ty m → Conₘ m → Set where
  ε   : NegativeErasedContext ε ε
  _∙_ : NegativeErasedContext Γ γ → NegativeType Γ A → NegativeErasedContext (Γ ∙ A) (γ ∙ p)
  _∙𝟘 : NegativeErasedContext Γ γ → NegativeErasedContext (Γ ∙ A) (γ ∙ 𝟘)

-- Lemma: Any entry in negative context is a negative type (needs weakening).

lookupNegative : ⊢ Γ → NegativeErasedContext Γ γ → (x ∷ A ∈ Γ) → (x ◂ ω ∈ γ) → NegativeType Γ A
lookupNegative ⊢Γ∙A            (nΓ ∙ nA) here _
  = wkNeg (step id) ⊢Γ∙A nA
lookupNegative ⊢Γ∙A@(⊢Γ ∙ Γ⊢A) (nΓ ∙ nA) (there h) (there j)
  = wkNeg (step id) ⊢Γ∙A (lookupNegative ⊢Γ nΓ h j)
lookupNegative ⊢Γ∙A (nΓγ ∙𝟘) here ()
lookupNegative ⊢Γ∙A@(⊢Γ ∙ Γ⊢A) (nΓγ ∙𝟘) (there h) (there j) =
  wkNeg (step id) ⊢Γ∙A (lookupNegative ⊢Γ nΓγ h j)

-- Main results
---------------------------------------------------------------------------

-- We assume a negative, consistent context.

module Main (nΓγ : NegativeErasedContext Γ γ) (consistent : ∀{t} → Γ ⊢ t ∷ Empty → ⊥) where

  open import Definition.Typed.Consequences.Reduction Erasure′
  open import Definition.Typed.Usage ErasureModality

  -- Lemma: A neutral has negative type in a consistent negative/erased context.

  neNeg : (d : Γ ⊢ u ∷ A) (n : Neutral u) (f : γ ▸ u) → NegativeType Γ A
  neNeg (var ⊢Γ h          ) (var _      ) γ▸u = lookupNegative ⊢Γ nΓγ h (valid-var-usage γ▸u)
  neNeg (d ∘ⱼ ⊢t           ) (∘ₙ n       ) γ▸u =
    let invUsageApp δ▸g η▸a γ≤γ′ = inv-usage-app γ▸u
    in  appNeg (neNeg d n (sub δ▸g (≤ᶜ-trans γ≤γ′ (+ᶜ-decreasingˡ _ _))))
               (refl (syntacticTerm d)) ⊢t
  neNeg (fstⱼ ⊢A A⊢B d     ) (fstₙ n     ) γ▸u =
    let invUsageProj δ▸t γ≤δ = inv-usage-fst γ▸u
    in  fstNeg (neNeg d n (sub δ▸t γ≤δ))
               (refl (Σⱼ ⊢A ▹ A⊢B))
  neNeg (sndⱼ ⊢A A⊢B d     ) (sndₙ n     ) γ▸u =
    let invUsageProj δ▸t γ≤δ = inv-usage-snd γ▸u
    in  sndNeg (neNeg d n (sub δ▸t γ≤δ))
               (refl (Σⱼ ⊢A ▹ A⊢B)) (fstⱼ ⊢A A⊢B d)
  neNeg (natrecⱼ _ _ _ d   ) (natrecₙ n  ) γ▸u =
    let invUsageNatrec _ _ δ▸n γ≤γ′ = inv-usage-natrec γ▸u
        ⊢ℕ = refl (ℕⱼ (wfTerm d))
        γ▸n = sub δ▸n (≤ᶜ-trans γ≤γ′ (≤ᶜ-trans (⊛ᶜ-ineq₂ _ _ _) (∧ᶜ-decreasingʳ _ _)))
    in  ⊥-elim (¬negℕ (neNeg d n γ▸n) ⊢ℕ)
  neNeg (prodrecⱼ ⊢A A⊢B _ d _) (prodrecₙ n ) γ▸u =
    let invUsageProdrec δ▸t η▸u p≤ω γ≤γ′ = inv-usage-prodrec γ▸u
        γ▸t = sub δ▸t (≤ᶜ-trans γ≤γ′ (≤ᶜ-trans (+ᶜ-decreasingˡ _ _)
                                (≤ᶜ-trans (·ᶜ-monotoneˡ p≤ω) (≤ᶜ-reflexive (·ᶜ-identityˡ _)))))
        ⊢Σ = refl (Σⱼ ⊢A ▹ A⊢B)
    in  ⊥-elim (¬negΣᵣ (neNeg d n γ▸t) ⊢Σ)
  neNeg (Emptyrecⱼ _ d     ) (Emptyrecₙ n) γ▸u = ⊥-elim (consistent d)
  neNeg (conv d c          ) n             γ▸u = conv (neNeg d n γ▸u) c

  thm : Γ ⊢ t ∷ ℕ → γ ▸ t → ∃ λ u → Γ ⊢ t ⇒* u ∷ ℕ × Whnf u × (Neutral u → ⊥)
  thm ⊢t γ▸t =
    let u , whnfU , d = whNormTerm ⊢t
        γ▸u = usagePres*Term γ▸t (redₜ d)
        ⊢ℕ = refl (ℕⱼ (wfTerm ⊢t))
    in  u , redₜ d , whnfU , λ x → ¬negℕ (neNeg (⊢u-redₜ d) x γ▸u) ⊢ℕ

-- Q.E.D. 2023-01-19
