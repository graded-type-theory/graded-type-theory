------------------------------------------------------------------------
-- Substitution operations used by Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Usage.Restrictions

module Definition.Typed.Decidable.Internal.Substitution
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open import Definition.Typed.Decidable.Internal.Term TR UR
open import Definition.Typed.Decidable.Internal.Weakening TR UR

open import Definition.Untyped M as U using (Wk)
open import Definition.Untyped.Properties M

open Wk

open import Tools.Function
open import Tools.Fin
open import Tools.Nat as N
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  n n₁ n₂ n₃ : Nat
  c          : Constants
  γ          : Contexts _
  ρ          : Wk _ _
  σ σ₂       : Subst _ _ _

------------------------------------------------------------------------
-- Composition

-- Composition of substitutions.

infixl 30 _ₛ•ₛ_

_ₛ•ₛ_ : Subst c n₃ n₂ → Subst c n₂ n₁ → Subst c n₃ n₁
id        ₛ•ₛ σ         = σ
wk1 σ₁    ₛ•ₛ σ₂        = wk1 (σ₁ ₛ•ₛ σ₂)
σ₁        ₛ•ₛ id        = σ₁
σ₁        ₛ•ₛ cons σ₂ t = cons (σ₁ ₛ•ₛ σ₂) (subst t σ₁)
σ₁ ⇑      ₛ•ₛ wk1 σ₂    = wk1 (σ₁ ₛ•ₛ σ₂)
σ₁ ⇑      ₛ•ₛ σ₂ ⇑      = (σ₁ ₛ•ₛ σ₂) ⇑
cons σ₁ _ ₛ•ₛ wk1 σ₂    = σ₁ ₛ•ₛ σ₂
cons σ₁ t ₛ•ₛ σ₂ ⇑      = cons (σ₁ ₛ•ₛ σ₂) t

opaque

  -- The function ⌜_⌝ˢ commutes with _ₛ•ₛ_/U._ₛ•ₛ_.

  ⌜ₛ•ₛ⌝ˢ :
    ∀ (σ₁ : Subst c n₃ n₂) x →
    ⌜ σ₁ ₛ•ₛ σ₂ ⌝ˢ γ x PE.≡ (⌜ σ₁ ⌝ˢ γ U.ₛ•ₛ ⌜ σ₂ ⌝ˢ γ) x
  ⌜ₛ•ₛ⌝ˢ {σ₂} {γ} id x =
    ⌜ σ₂ ⌝ˢ γ x                  ≡˘⟨ subst-id _ ⟩
    ⌜ σ₂ ⌝ˢ γ x U.[ U.idSubst ]  ∎
  ⌜ₛ•ₛ⌝ˢ {σ₂} {γ} (wk1 σ₁) x =
    U.wk1 (⌜ σ₁ ₛ•ₛ σ₂ ⌝ˢ γ x)                  ≡⟨ PE.cong U.wk1 (⌜ₛ•ₛ⌝ˢ σ₁ _) ⟩
    U.wk1 ((⌜ σ₁ ⌝ˢ γ U.ₛ•ₛ ⌜ σ₂ ⌝ˢ γ) x)       ≡⟨⟩
    U.wk1 (⌜ σ₂ ⌝ˢ γ x U.[ ⌜ σ₁ ⌝ˢ γ ])         ≡⟨ wk-subst (⌜ σ₂ ⌝ˢ _ _) ⟩
    ⌜ σ₂ ⌝ˢ γ x U.[ U.wk1Subst (⌜ σ₁ ⌝ˢ γ) ]    ≡⟨⟩
    (U.wk1Subst (⌜ σ₁ ⌝ˢ γ) U.ₛ•ₛ ⌜ σ₂ ⌝ˢ γ) x  ∎
  ⌜ₛ•ₛ⌝ˢ {σ₂ = id} (_ ⇑) _ =
    PE.refl
  ⌜ₛ•ₛ⌝ˢ {σ₂ = wk1 σ₂} {γ} (σ₁ ⇑) x =
    U.wk1 (⌜ σ₁ ₛ•ₛ σ₂ ⌝ˢ γ x)               ≡⟨ PE.cong U.wk1 (⌜ₛ•ₛ⌝ˢ σ₁ _) ⟩
    U.wk1 ((⌜ σ₁ ⌝ˢ γ U.ₛ•ₛ ⌜ σ₂ ⌝ˢ γ) x)    ≡⟨⟩
    U.wk1 (⌜ σ₂ ⌝ˢ γ x U.[ ⌜ σ₁ ⌝ˢ γ ])      ≡˘⟨ wk1-liftSubst (⌜ σ₂ ⌝ˢ _ _) ⟩
    U.wk1 (⌜ σ₂ ⌝ˢ γ x) U.[ ⌜ σ₁ ⌝ˢ γ U.⇑ ]  ∎
  ⌜ₛ•ₛ⌝ˢ {σ₂ = _ ⇑} (_ ⇑) x0 =
    PE.refl
  ⌜ₛ•ₛ⌝ˢ {σ₂ = σ₂ ⇑} {γ} (σ₁ ⇑) (x +1) =
    U.wk1 (⌜ σ₁ ₛ•ₛ σ₂ ⌝ˢ γ x)               ≡⟨ PE.cong U.wk1 (⌜ₛ•ₛ⌝ˢ σ₁ _) ⟩
    U.wk1 ((⌜ σ₁ ⌝ˢ γ U.ₛ•ₛ ⌜ σ₂ ⌝ˢ γ) x)    ≡⟨⟩
    U.wk1 (⌜ σ₂ ⌝ˢ γ x U.[ ⌜ σ₁ ⌝ˢ γ ])      ≡˘⟨ wk1-liftSubst (⌜ σ₂ ⌝ˢ _ _) ⟩
    U.wk1 (⌜ σ₂ ⌝ˢ γ x) U.[ ⌜ σ₁ ⌝ˢ γ U.⇑ ]  ∎
  ⌜ₛ•ₛ⌝ˢ {σ₂ = cons _ _} (_ ⇑) x0 =
    PE.refl
  ⌜ₛ•ₛ⌝ˢ {σ₂ = cons σ₂ _} {γ} σ₁@(_ ⇑) (x +1) =
    ⌜ σ₁ ₛ•ₛ σ₂ ⌝ˢ γ x           ≡⟨ ⌜ₛ•ₛ⌝ˢ {σ₂ = σ₂} σ₁ _ ⟩
    ⌜ σ₂ ⌝ˢ γ x U.[ ⌜ σ₁ ⌝ˢ γ ]  ∎
  ⌜ₛ•ₛ⌝ˢ {σ₂ = id} (cons _ _) _ =
    PE.refl
  ⌜ₛ•ₛ⌝ˢ {σ₂ = wk1 σ₂} {γ} (cons σ₁ t) x =
    ⌜ σ₁ ₛ•ₛ σ₂ ⌝ˢ γ x                                           ≡⟨ ⌜ₛ•ₛ⌝ˢ σ₁ _ ⟩
    (⌜ σ₁ ⌝ˢ γ U.ₛ•ₛ ⌜ σ₂ ⌝ˢ γ) x                                ≡⟨⟩
    ⌜ σ₂ ⌝ˢ γ x U.[ ⌜ σ₁ ⌝ˢ γ ]                                  ≡˘⟨ wk1-tail (⌜ σ₂ ⌝ˢ _ _) ⟩
    U.wk1 (⌜ σ₂ ⌝ˢ γ x) U.[ U.consSubst (⌜ σ₁ ⌝ˢ γ) (⌜ t ⌝ γ) ]  ∎
  ⌜ₛ•ₛ⌝ˢ {σ₂ = _ ⇑} (cons _ _) x0 =
    PE.refl
  ⌜ₛ•ₛ⌝ˢ {σ₂ = σ₂ ⇑} {γ} (cons σ₁ t) (x +1) =
    ⌜ σ₁ ₛ•ₛ σ₂ ⌝ˢ γ x                                           ≡⟨ ⌜ₛ•ₛ⌝ˢ σ₁ _ ⟩
    (⌜ σ₁ ⌝ˢ γ U.ₛ•ₛ ⌜ σ₂ ⌝ˢ γ) x                                ≡⟨⟩
    ⌜ σ₂ ⌝ˢ γ x U.[ ⌜ σ₁ ⌝ˢ γ ]                                  ≡˘⟨ wk1-tail (⌜ σ₂ ⌝ˢ _ _) ⟩
    U.wk1 (⌜ σ₂ ⌝ˢ γ x) U.[ U.consSubst (⌜ σ₁ ⌝ˢ γ) (⌜ t ⌝ γ) ]  ∎
  ⌜ₛ•ₛ⌝ˢ {σ₂ = cons _ _} (cons _ _) x0 =
    PE.refl
  ⌜ₛ•ₛ⌝ˢ {σ₂ = cons σ₂ _} {γ} σ₁@(cons _ _) (x +1) =
    ⌜ σ₁ ₛ•ₛ σ₂ ⌝ˢ γ x           ≡⟨ ⌜ₛ•ₛ⌝ˢ {σ₂ = σ₂} σ₁ _ ⟩
    ⌜ σ₂ ⌝ˢ γ x U.[ ⌜ σ₁ ⌝ˢ γ ]  ∎

-- Composition of substitutions and weakenings.

infixl 30 _ₛ•_

_ₛ•_ : Subst c n₃ n₂ → Wk n₂ n₁ → Subst c n₃ n₁
σ ₛ• ρ = σ ₛ•ₛ toSubst ρ

opaque

  -- The function ⌜_⌝ˢ commutes with _ₛ•_/U._ₛ•_.

  ⌜ₛ•⌝ˢ :
    ∀ (σ : Subst c n₃ n₂) x →
    ⌜ σ ₛ• ρ ⌝ˢ γ x PE.≡ (⌜ σ ⌝ˢ γ U.ₛ• ρ) x
  ⌜ₛ•⌝ˢ {ρ} {γ} σ x =
    ⌜ σ ₛ•ₛ toSubst ρ ⌝ˢ γ x             ≡⟨ ⌜ₛ•ₛ⌝ˢ σ _ ⟩
    (⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ toSubst ρ ⌝ˢ γ) x  ≡⟨ PE.cong U._[ ⌜ σ ⌝ˢ _ ] (⌜toSubst⌝ˢ x) ⟩
    (⌜ σ ⌝ˢ γ U.ₛ•ₛ U.toSubst ρ) x       ≡⟨⟩
    (⌜ σ ⌝ˢ γ U.ₛ• ρ) x                  ∎

------------------------------------------------------------------------
-- Heads and tails of substitutions

-- The "head" of a substitution.

headₛ : Subst c n₂ (1+ n₁) → Term c n₂
headₛ id         = var x0
headₛ (wk1 σ)    = weaken (step id) (headₛ σ)
headₛ (σ ⇑)      = var x0
headₛ (cons _ t) = t

opaque

  -- The function headₛ is correctly implemented.

  ⌜headₛ⌝ :
    (σ : Subst c n₂ (1+ n₁)) → ⌜ headₛ σ ⌝ γ PE.≡ U.head (⌜ σ ⌝ˢ γ)
  ⌜headₛ⌝ id         = PE.refl
  ⌜headₛ⌝ (wk1 σ)    = PE.cong U.wk1 (⌜headₛ⌝ σ)
  ⌜headₛ⌝ (_ ⇑)      = PE.refl
  ⌜headₛ⌝ (cons _ _) = PE.refl

-- The "tail" of a substitution.
--
-- In Definition.Typed.Decidable.Internal.equal-sub and equal-sub′ the
-- following comparisons can (at the time of writing) be made:
--
--   headₛ σ₁                 = headₛ σ₂
--   headₛ (tailₛ σ₁)         = headₛ (tailₛ σ₂)
--   headₛ (tailₛ (tailₛ σ₁)) = headₛ (tailₛ (tailₛ σ₂))
--                            ⋮
--
-- If σ₁ and σ₂ are both id, then one gets the following substitutions:
--
--   id
--   wk1 id
--   wk1 (wk1 id)
--   ⋮
--
-- Normalising the head of wk1ⁿ id is linear in n, so comparing the
-- identity substitution with itself is at least quadratic in the size
-- of the context. This could perhaps be addressed by having a special
-- case for id, but one would get a similar problem for, say, wk1 id.
-- Another option might be to use a different representation of
-- substitutions, for instance one with wk1 replaced by something
-- corresponding to wkSubst ∘→ 1+, implemented in such a way that
-- adjacent occurrences of that constructor are merged. However, such
-- changes might amount to premature optimisation.

tailₛ : Subst c n₂ (1+ n₁) → Subst c n₂ n₁
tailₛ id         = wk1 id
tailₛ (wk1 σ)    = wk1 (tailₛ σ)
tailₛ (σ ⇑)      = wk1 σ
tailₛ (cons σ _) = σ

opaque

  -- The function tailₛ is correctly implemented.

  ⌜tailₛ⌝ˢ :
    ∀ (σ : Subst c n₂ (1+ n₁)) x →
    ⌜ tailₛ σ ⌝ˢ γ x PE.≡ U.tail (⌜ σ ⌝ˢ γ) x
  ⌜tailₛ⌝ˢ id         _ = PE.refl
  ⌜tailₛ⌝ˢ (wk1 σ)    _ = PE.cong U.wk1 (⌜tailₛ⌝ˢ σ _)
  ⌜tailₛ⌝ˢ (_ ⇑)      _ = PE.refl
  ⌜tailₛ⌝ˢ (cons _ _) _ = PE.refl

opaque

  -- An η-rule for substitutions.

  ⌜cons-tailₛ-headₛ⌝ˢ :
    ∀ (σ : Subst c n₂ (1+ n₁)) x →
    ⌜ cons (tailₛ σ) (headₛ σ) ⌝ˢ γ x PE.≡ ⌜ σ ⌝ˢ γ x
  ⌜cons-tailₛ-headₛ⌝ˢ {γ} σ x =
    ⌜ cons (tailₛ σ) (headₛ σ) ⌝ˢ γ x                      ≡⟨⟩
    U.consSubst (⌜ tailₛ σ ⌝ˢ γ) (⌜ headₛ σ ⌝ γ) x         ≡⟨ consSubst-cong (⌜tailₛ⌝ˢ σ) x ⟩
    U.consSubst (U.tail (⌜ σ ⌝ˢ γ)) (⌜ headₛ σ ⌝ γ) x      ≡⟨ PE.cong (flip (U.consSubst _) x) (⌜headₛ⌝ σ) ⟩
    U.consSubst (U.tail (⌜ σ ⌝ˢ γ)) (U.head (⌜ σ ⌝ˢ γ)) x  ≡⟨ consSubst-η {σ = ⌜ σ ⌝ˢ _} _ ⟩
    ⌜ σ ⌝ˢ γ x                                             ∎

------------------------------------------------------------------------
-- Some derived substitution operations

-- Weakening of substitutions.

wkSubst : ∀ k → Subst c n₂ n₁ → Subst c (k N.+ n₂) n₁
wkSubst k = U.stepn id k •ₛ_

opaque

  -- The function ⌜_⌝ˢ commutes with wkSubst/U.wkSubst.

  ⌜wkSubst⌝ˢ :
    ∀ k (x : Fin n) →
    ⌜ wkSubst k σ ⌝ˢ γ x PE.≡ U.wkSubst k (⌜ σ ⌝ˢ γ) x
  ⌜wkSubst⌝ˢ         0      _ = PE.refl
  ⌜wkSubst⌝ˢ {σ} {γ} (1+ k) x =
    ⌜ wk1 (wkSubst k σ) ⌝ˢ γ x             ≡⟨⟩
    U.wk1Subst (⌜ wkSubst k σ ⌝ˢ γ) x      ≡⟨ wk1Subst-cong (⌜wkSubst⌝ˢ k) _ ⟩
    U.wk1Subst (U.wkSubst k (⌜ σ ⌝ˢ γ)) x  ∎

-- Lifting.

infix 35 _⇑[_]

_⇑[_] : Subst c n₂ n₁ → ∀ k → Subst c (k N.+ n₂) (k N.+ n₁)
σ ⇑[ 0    ] = σ
σ ⇑[ 1+ k ] = σ ⇑[ k ] ⇑

opaque

  -- The functions ⌜_⌝ˢ/⌜_⌝ commute with _⇑[_]/U._⇑[_].

  ⌜⇑[]⌝ˢ :
    ∀ k (x : Fin (k N.+ n)) →
    ⌜ σ ⇑[ k ] ⌝ˢ γ x PE.≡ (⌜ σ ⌝ˢ γ U.⇑[ k ]) x
  ⌜⇑[]⌝ˢ 0 _ =
    PE.refl
  ⌜⇑[]⌝ˢ (1+ _) x0 =
    PE.refl
  ⌜⇑[]⌝ˢ {σ} {γ} (1+ k) (x +1) =
    U.wk1 (⌜ (σ ⇑[ k ]) ⌝ˢ γ x)    ≡⟨ PE.cong U.wk1 (⌜⇑[]⌝ˢ k _) ⟩
    U.wk1 ((⌜ σ ⌝ˢ γ U.⇑[ k ]) x)  ∎

-- Singleton substitutions.

sgSubst : Term c n → Subst c n (1+ n)
sgSubst = cons id

------------------------------------------------------------------------
-- Applying substitutions to terms

-- Finds the term corresponding to a given variable.

infix 25 _[_]ᵛ

_[_]ᵛ : Fin n₁ → Subst c n₂ n₁ → Term c n₂
x      [ id       ]ᵛ = var x
x      [ wk1 σ    ]ᵛ = weaken (step id) (x [ σ ]ᵛ)
x0     [ _ ⇑      ]ᵛ = var x0
(x +1) [ σ ⇑      ]ᵛ = weaken (step id) (x [ σ ]ᵛ)
x0     [ cons _ t ]ᵛ = t
(x +1) [ cons σ _ ]ᵛ = x [ σ ]ᵛ

opaque

  -- The function _[_]ᵛ is correctly defined.

  ⌜[]ᵛ⌝ : ∀ (σ : Subst c n₂ n₁) x → ⌜ x [ σ ]ᵛ ⌝ γ PE.≡ ⌜ σ ⌝ˢ γ x
  ⌜[]ᵛ⌝ id _ =
    PE.refl
  ⌜[]ᵛ⌝ (wk1 σ) x =
    PE.cong U.wk1 (⌜[]ᵛ⌝ σ x)
  ⌜[]ᵛ⌝ (_ ⇑) x0 =
    PE.refl
  ⌜[]ᵛ⌝ (σ ⇑) (x +1) =
    PE.cong U.wk1 (⌜[]ᵛ⌝ σ x)
  ⌜[]ᵛ⌝ (cons _ _) x0 =
    PE.refl
  ⌜[]ᵛ⌝ (cons σ _) (x +1) =
    ⌜[]ᵛ⌝ σ x

-- Substitution (lazy): This operation applies the substitution by
-- pushing it just below the term's top-level constructor (unless the
-- term is a variable).

infix 25 _[_]

_[_] : Term c n₁ → Subst c n₂ n₁ → Term c n₂
t ∷[ A ]              [ σ ] = subst t σ ∷[ subst A σ ]
meta-var x σ′         [ σ ] = meta-var x (σ ₛ•ₛ σ′)
⌞ t ⌟ σ′              [ σ ] = ⌞ t ⌟ (σ ₛ•ₛ σ′)
weaken ρ t            [ σ ] = subst t (σ ₛ• ρ)
subst t σ′            [ σ ] = subst t (σ ₛ•ₛ σ′)
var x                 [ σ ] = x [ σ ]ᵛ
defn α                [ σ ] = defn α
U l                   [ σ ] = U l
Empty                 [ σ ] = Empty
emptyrec p A t        [ σ ] = emptyrec p (subst A σ) (subst t σ)
Unit s l              [ σ ] = Unit s l
star s l              [ σ ] = star s l
unitrec l p q A t u   [ σ ] = unitrec l p q (subst A (σ ⇑)) (subst t σ)
                                (subst u σ)
ΠΣ⟨ b ⟩ p , q ▷ A ▹ B [ σ ] = ΠΣ⟨ b ⟩ p , q ▷ subst A σ ▹ subst B (σ ⇑)
lam p t               [ σ ] = lam p (subst t (σ ⇑))
t ∘⟨ p ⟩ u            [ σ ] = subst t σ ∘⟨ p ⟩ subst u σ
prod s p t u          [ σ ] = prod s p (subst t σ) (subst u σ)
fst p t               [ σ ] = fst p (subst t σ)
snd p t               [ σ ] = snd p (subst t σ)
prodrec r p q A t u   [ σ ] = prodrec r p q (subst A (σ ⇑)) (subst t σ)
                                (subst u (σ ⇑[ 2 ]))
ℕ                     [ σ ] = ℕ
zero                  [ σ ] = zero
suc t                 [ σ ] = suc (subst t σ)
natrec p q r A t u v  [ σ ] = natrec p q r (subst A (σ ⇑)) (subst t σ)
                                (subst u (σ ⇑[ 2 ])) (subst v σ)
Id A t u              [ σ ] = Id (subst A σ) (subst t σ) (subst u σ)
rfl                   [ σ ] = rfl
J p q A t B u v w     [ σ ] = J p q (subst A σ) (subst t σ)
                                (subst B (σ ⇑[ 2 ])) (subst u σ)
                                (subst v σ) (subst w σ)
K p A t B u v         [ σ ] = K p (subst A σ) (subst t σ)
                                (subst B (σ ⇑)) (subst u σ) (subst v σ)
[]-cong s A t u v     [ σ ] = []-cong s (subst A σ) (subst t σ)
                                (subst u σ) (subst v σ)

opaque

  -- The function ⌜_⌝ commutes with substitution.

  ⌜[]⌝ :
    (t : Term c n) → ⌜ t [ σ ] ⌝ γ PE.≡ ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]
  ⌜[]⌝ (_ ∷[ _ ]) =
    PE.refl
  ⌜[]⌝ {σ} {γ} (meta-var x σ′) =
    ⌜ meta-var x (σ ₛ•ₛ σ′) ⌝ γ              ≡⟨ ⌜meta-var⌝ (σ ₛ•ₛ _) ⟩
    ⌜ x ⌝ᵐ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ]           ≡⟨ substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) (⌜ x ⌝ᵐ γ) ⟩
    ⌜ x ⌝ᵐ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ]  ≡˘⟨ substCompEq (⌜ x ⌝ᵐ γ) ⟩
    ⌜ x ⌝ᵐ γ U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ]  ≡˘⟨ PE.cong U._[ _ ] (⌜meta-var⌝ σ′) ⟩
    ⌜ meta-var x σ′ ⌝ γ U.[ ⌜ σ ⌝ˢ γ ]       ∎
  ⌜[]⌝ {σ} {γ} (⌞ t ⌟ σ′) =
    t U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ]           ≡⟨ substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) t ⟩
    t U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ]  ≡˘⟨ substCompEq t ⟩
    t U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ]  ∎
  ⌜[]⌝ {σ} {γ} (weaken ρ t) =
    ⌜ t ⌝ γ U.[ ⌜ σ ₛ• ρ ⌝ˢ γ ]      ≡⟨ substVar-to-subst (⌜ₛ•⌝ˢ σ) (⌜ t ⌝ _) ⟩
    ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ• ρ ]    ≡˘⟨ subst-wk (⌜ t ⌝ _) ⟩
    U.wk ρ (⌜ t ⌝ γ) U.[ ⌜ σ ⌝ˢ γ ]  ∎
  ⌜[]⌝ {σ} {γ} (subst t σ′) =
    ⌜ t ⌝ γ U.[ ⌜ σ ₛ•ₛ σ′ ⌝ˢ γ ]           ≡⟨ substVar-to-subst (⌜ₛ•ₛ⌝ˢ σ) (⌜ t ⌝ _) ⟩
    ⌜ t ⌝ γ U.[ ⌜ σ ⌝ˢ γ U.ₛ•ₛ ⌜ σ′ ⌝ˢ γ ]  ≡˘⟨ substCompEq (⌜ t ⌝ _) ⟩
    ⌜ t ⌝ γ U.[ ⌜ σ′ ⌝ˢ γ ] U.[ ⌜ σ ⌝ˢ γ ]  ∎
  ⌜[]⌝ {σ} (var _) =
    ⌜[]ᵛ⌝ σ _
  ⌜[]⌝ (defn _) =
    PE.refl
  ⌜[]⌝ (U _) =
    PE.refl
  ⌜[]⌝ Empty =
    PE.refl
  ⌜[]⌝ (emptyrec _ _ _) =
    PE.refl
  ⌜[]⌝ (Unit _ _) =
    PE.refl
  ⌜[]⌝ (star _ _) =
    PE.refl
  ⌜[]⌝ (unitrec _ _ _ _ _ _) =
    PE.refl
  ⌜[]⌝ (ΠΣ⟨ _ ⟩ _ , _ ▷ _ ▹ _) =
    PE.refl
  ⌜[]⌝ (lam _ _) =
    PE.refl
  ⌜[]⌝ (_ ∘⟨ _ ⟩ _) =
    PE.refl
  ⌜[]⌝ (prod _ _ _ _) =
    PE.refl
  ⌜[]⌝ (fst _ _) =
    PE.refl
  ⌜[]⌝ (snd _ _) =
    PE.refl
  ⌜[]⌝ (prodrec _ _ _ _ _ _) =
    PE.refl
  ⌜[]⌝ ℕ =
    PE.refl
  ⌜[]⌝ zero =
    PE.refl
  ⌜[]⌝ (suc _) =
    PE.refl
  ⌜[]⌝ (natrec _ _ _ _ _ _ _) =
    PE.refl
  ⌜[]⌝ (Id _ _ _) =
    PE.refl
  ⌜[]⌝ rfl =
    PE.refl
  ⌜[]⌝ (J _ _ _ _ _ _ _ _) =
    PE.refl
  ⌜[]⌝ (K _ _ _ _ _ _) =
    PE.refl
  ⌜[]⌝ ([]-cong _ _ _ _ _) =
    PE.refl
