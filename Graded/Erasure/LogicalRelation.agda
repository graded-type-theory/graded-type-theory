------------------------------------------------------------------------
-- The Logical relation for erasure.
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.Restrictions
open import Graded.Erasure.LogicalRelation.Assumptions
open import Graded.Modality

module Graded.Erasure.LogicalRelation
  {a} {M : Set a}
  {𝕄 : Modality M}
  {R : Type-restrictions 𝕄}
  (as : Assumptions R)
  where

open Assumptions as
open Modality 𝕄

open import Definition.Untyped M as U hiding (_∘_; K)

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Substitution R
open import Definition.Typed R
open import Graded.Context 𝕄
open import Graded.Mode 𝕄
open import Definition.Typed.Weakening R

open import Graded.Erasure.Target as T hiding (_⇒*_)
open import Graded.Erasure.Extraction 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_)
open import Tools.Relation
open import Tools.Unit


private
  variable
    m n : Nat
    A B t t₁ t′ u : U.Term n
    v v₂ v′ w : T.Term n
    p : M
    l : TypeLevel
    s : Strength

------------------------------------------------------------------------
-- The logical relation

-- In the non-strict setting terms of type U are related to all target
-- terms, and in the strict setting they are related to those terms
-- that reduce to ↯. (All types are erased by the extraction
-- function.)

data _®_∷U (t : U.Term k) (v : T.Term k) : Set a where
  Uᵣ : (str ≡ strict → v T.⇒* ↯) → t ® v ∷U

-- Terms of type ℕ are related if both reduce to zero or if both
-- reduce to the successors of related terms (in the strict setting
-- the target term's reduct has to be a numeral).

data _®_∷ℕ (t : U.Term k) (v : T.Term k) : Set a where
  zeroᵣ : Δ ⊢ t ⇒* U.zero ∷ ℕ → v T.⇒* T.zero →
          t ® v ∷ℕ
  sucᵣ  : Δ ⊢ t ⇒* U.suc t′ ∷ ℕ → v T.⇒* T.suc v′ → Numeral⟨ str ⟩ v′ →
          t′ ® v′ ∷ℕ → t ® v ∷ℕ

-- Terms of type Empty are not related to anything.
-- (There are no terms of the Empty type in a consistent context).

data _®_∷Empty (t : U.Term k) (v : T.Term k) : Set a where

-- Terms of type Unit are related if both reduce to star.

data _®_∷Unit⟨_⟩ (t : U.Term k) (v : T.Term k) (s : Strength) : Set a where
  starᵣ : Δ ⊢ t ⇒* U.star s ∷ Unit s → v T.⇒* T.star → t ® v ∷Unit⟨ s ⟩

-- Equality proofs are related in the non-strict setting if the source
-- term reduces to rfl. In the strict setting the target term should
-- additionally reduce to ↯.

data _®_∷Id⟨_⟩⟨_⟩⟨_⟩
       (t : U.Term k) (v : T.Term k) (Ty lhs rhs : U.Term k) :
       Set a where
  rflᵣ : Δ ⊢ t ⇒* U.rfl ∷ Id Ty lhs rhs → (str ≡ strict → v T.⇒* ↯) →
         t ® v ∷Id⟨ Ty ⟩⟨ lhs ⟩⟨ rhs ⟩

mutual

  -- Logical relation for erasure
  infix 19 _®⟨_⟩_∷_/_

  _®⟨_⟩_∷_/_ : (t : U.Term k) (l : TypeLevel) (v : T.Term k)
               (A : U.Term k) ([A] : Δ ⊩⟨ l ⟩ A) → Set a
  t ®⟨ l ⟩ v ∷ A / Uᵣ x     = t ® v ∷U
  t ®⟨ l ⟩ v ∷ A / ℕᵣ x     = t ® v ∷ℕ
  t ®⟨ l ⟩ v ∷ A / Emptyᵣ x = t ® v ∷Empty
  t ®⟨ l ⟩ v ∷ A / Unitᵣ {s = s} x  = t ® v ∷Unit⟨ s ⟩
  t ®⟨ l ⟩ v ∷ A / ne′ K D neK K≡K = Lift a ⊥

  -- Π:
  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ p q) F G D ⊢F ⊢G A≡A [F] [G] G-ext _ =
    (str ≡ strict → ∃ λ v′ → v T.⇒* T.lam v′) ×
    (∀ {a} → ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ⊢Δ) →
     Π-® l F G t a v ([F] id ⊢Δ) ([G] id ⊢Δ [a]) p (is-𝟘? p))

  -- Σ:
  -- t and v are related if:
  -- t reduces to a pair (t₁, t₂),
  -- t₂ is related to some v₂ and
  -- there is extra data depending on whether the first component
  -- is erased (see below).
  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΣ m p q) F G D ⊢F ⊢G A≡A [F] [G] G-ext _ =
    ∃₂ λ t₁ t₂ →
    Δ ⊢ t ⇒* U.prod m p t₁ t₂ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G ×
    Σ (Δ ⊩⟨ l ⟩ t₁ ∷ U.wk id F / [F] id ⊢Δ) λ [t₁] →
    ∃ λ v₂ →
    t₂ ®⟨ l ⟩ v₂ ∷ U.wk (lift id) G U.[ t₁ ]₀ / [G] id ⊢Δ [t₁] ×
    Σ-® l F ([F] id ⊢Δ) t₁ v v₂ p

  -- Identity types.
  t ®⟨ _ ⟩ v ∷ A / Idᵣ ⊩A = t ® v ∷Id⟨ Ty ⟩⟨ lhs ⟩⟨ rhs ⟩
    where
    open _⊩ₗId_ ⊩A

  -- Subsumption:
  t ®⟨ ¹ ⟩ v ∷ A / emb 0<1 [A] = t ®⟨ ⁰ ⟩ v ∷ A / [A]


  -- Extra data for Π-types, depending on whether the function argument
  -- is erased or not.

  Π-® : (l : TypeLevel) (F : U.Term k) (G : U.Term (1+ k))
        (t b : U.Term k) (v : T.Term k)
        ([F] : Δ ⊩⟨ l ⟩ U.wk id F)
        ([G] : Δ ⊩⟨ l ⟩ U.wk (lift id) G U.[ b ]₀)
        (p : M) (p≟𝟘 : Dec (p PE.≡ 𝟘)) → Set a
  -- Erased Π:
  -- In the strict setting t is related to v if the applications t ∘ a
  -- and v ∘ ↯ are related. In the non-strict setting t ∘ a should be
  -- related to v.
  Π-® l F G t a v [F] [Ga] p (yes p≡𝟘) =
    (t U.∘⟨ p ⟩ a) ®⟨ l ⟩ app-𝟘 str v ∷ U.wk (lift id) G U.[ a ]₀ / [Ga]
  -- Non-erased Π:
  -- Functions t and v are related if the applications
  -- t∘a and v∘w are related for all related a and w.
  Π-® l F G t a v [F] [Ga] p (no p≢𝟘) =
    ∀ {w} → a ®⟨ l ⟩ w ∷ U.wk id F / [F]
          → (t U.∘⟨ p ⟩ a) ®⟨ l ⟩ v T.∘⟨ str ⟩ w ∷
              U.wk (lift id) G U.[ a ]₀ / [Ga]

  -- Extra data for Σ-types, depending on whether the first component
  -- is erased or not.

  Σ-® :
    (l : TypeLevel) (F : U.Term k) →
    Δ ⊩⟨ l ⟩ U.wk id F →
    U.Term k → T.Term k → T.Term k → (p : M) → Set a
  Σ-® l F [F] t₁ v v₂ p = case is-𝟘? p of λ where
    -- Erased Σ:
    -- v reduces to v₂
    (yes p≡𝟘) → Lift a (v T.⇒* v₂)
    -- There is a term v₁ such that v reduces to (v₁, v₂)
    -- and t₁ is related to v₁.
    (no p≢𝟘) → ∃ λ v₁ → (v T.⇒* T.prod v₁ v₂)
                      × (t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F])

-- Logical relation for terms of quantified type
-- Under grade 𝟘, the terms need not be related.
_®⟨_⟩_∷_◂_/_ : (t : U.Term k) (l : TypeLevel) (v : T.Term k)
                 (A : U.Term k) (p : M)
                 ([A] : Δ ⊩⟨ l ⟩ A) → Set a
t ®⟨ l ⟩ v ∷ A ◂ p / [A] = case is-𝟘? p of λ where
  (yes p≡𝟘) → Lift a ⊤
  (no p≢𝟘) → t ®⟨ l ⟩ v ∷ A / [A]

-- Logical relation for substitutions
--
-- Substitutions are related if all terms are pairwise related
-- under the corresponding quantity of the grade context.

_®_∷[_]_◂_/_/_ :
  (σₜ : U.Subst k n)
  (σᵥ : T.Subst k n) (m : Mode) (Γ : Con U.Term n) (γ : Conₘ n)
  ([Γ] : ⊩ᵛ Γ) ([σ] : Δ ⊩ˢ σₜ ∷ Γ / [Γ] / ⊢Δ) → Set a
σₜ ® σᵥ ∷[ _ ] ε ◂ ε / ε / (lift tt) = Lift a ⊤
σₜ ® σᵥ ∷[ m ] Γ ∙ A ◂ γ ∙ p / _∙_ {l = l} [Γ] [A] / ([σ] , [σA]) =
  (U.tail σₜ ® T.tail σᵥ ∷[ m ] Γ ◂ γ / [Γ] / [σ]) ×
  (U.head σₜ ®⟨ l ⟩ T.head σᵥ ∷ A U.[ U.tail σₜ ] ◂ ⌜ m ⌝ · p /
     proj₁ (unwrap [A] ⊢Δ [σ]))

-- Validity of erasure
--
-- A term t is valid if t[σ] is related to (erase str t)[σ′]
-- for all related contexts σ and σ′.

_▸_⊩ʳ⟨_⟩_∷[_]_/_/_ :
  (γ : Conₘ n) (Γ : Con U.Term n) (l : TypeLevel)
  (t : U.Term n) (m : Mode) (A : U.Term n)
  ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Set a
γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A] =
  ∀ {σ σ′} →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ® σ′ ∷[ m ] Γ ◂ γ / [Γ] / [σ] →
  t U.[ σ ] ®⟨ l ⟩ erase str t T.[ σ′ ] ∷ A U.[ σ ] ◂ ⌜ m ⌝ /
    proj₁ (unwrap [A] ⊢Δ [σ])

------------------------------------------------------------------------
-- Helper functions

opaque

  -- A "reduction" rule for Π-®.

  Π-®-𝟘 :
    {⊩A : Δ ⊩⟨ l ⟩ U.wk id A}
    {⊩B[u] : Δ ⊩⟨ l ⟩ U.wk (lift id) B U.[ u ]₀}
    (d : Dec (𝟘 PE.≡ 𝟘)) →
    Π-® l A B t u v ⊩A ⊩B[u] 𝟘 d →
    (t U.∘⟨ 𝟘 ⟩ u) ®⟨ l ⟩ app-𝟘 str v ∷
      U.wk (lift id) B U.[ u ]₀ / ⊩B[u]
  Π-®-𝟘 (no 𝟘≢𝟘) = λ _ → ⊥-elim (𝟘≢𝟘 PE.refl)
  Π-®-𝟘 (yes _)  = idᶠ

opaque

  -- A "reduction" rule for Π-®.

  Π-®-ω :
    {⊩A : Δ ⊩⟨ l ⟩ U.wk id A}
    {⊩B[u] : Δ ⊩⟨ l ⟩ U.wk (lift id) B U.[ u ]₀} →
    p PE.≢ 𝟘 →
    (d : Dec (p PE.≡ 𝟘)) →
    Π-® l A B t u v ⊩A ⊩B[u] p d →
    u ®⟨ l ⟩ w ∷ U.wk id A / ⊩A →
    (t U.∘⟨ p ⟩ u) ®⟨ l ⟩ v T.∘⟨ str ⟩ w ∷
      U.wk (lift id) B U.[ u ]₀ / ⊩B[u]
  Π-®-ω p≢𝟘 (yes p≡𝟘) _   = ⊥-elim (p≢𝟘 p≡𝟘)
  Π-®-ω _   (no _)    hyp = hyp

-- Helper introduction and elimination lemmata for Σ-®

Σ-®-intro-𝟘 : ∀ {l F [F] t₁ v v₂ p}
            → v T.⇒* v₂ → p PE.≡ 𝟘
            → Σ-® l F [F] t₁ v v₂ p
Σ-®-intro-𝟘 {p = p} v⇒v₂ p≡𝟘 with is-𝟘? p
... | yes _ = lift v⇒v₂
... | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

Σ-®-intro-ω : ∀ {l F [F] t₁ v v₂ p}
            → (v₁ : T.Term k)
            → v T.⇒* T.prod v₁ v₂
            → t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F]
            → p PE.≢ 𝟘
            → Σ-® l F [F] t₁ v v₂ p
Σ-®-intro-ω {p = p} v₁ v⇒v′ t₁®v₁ p≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
... | no _ = v₁ , v⇒v′ , t₁®v₁

Σ-®-elim : ∀ {b l F [F] t₁ v v₂ p}
         → (P : (p : M) → Set b)
         → Σ-® l F [F] t₁ v v₂ p
         → (v T.⇒* v₂ → p PE.≡ 𝟘 → P p)
         → ((v₁ : T.Term k) → v T.⇒* T.prod v₁ v₂ → t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F] → p PE.≢ 𝟘 → P p)
         → P p
Σ-®-elim {p = p} P extra f g with is-𝟘? p
Σ-®-elim {p = p} P (lift v⇒v₂) f g | yes p≡𝟘 = f v⇒v₂ p≡𝟘
Σ-®-elim {p = p} P (v₁ , v⇒v₁,v₂ , t₁®v₁) f g | no p≢𝟘 = g v₁ v⇒v₁,v₂ t₁®v₁ p≢𝟘

opaque

  -- A "reduction" rule for Σ-®.

  Σ-®-𝟘 :
    {⊩A : Δ ⊩⟨ l ⟩ U.wk id A} →
    Σ-® l A ⊩A t₁ v v₂ 𝟘 →
    v T.⇒* v₂
  Σ-®-𝟘 x =
    Σ-®-elim (λ _ → _ T.⇒* _) x (λ v⇒ _ → v⇒)
      (λ _ _ _ 𝟘≢𝟘 → ⊥-elim $ 𝟘≢𝟘 PE.refl)

opaque

  -- A "reduction" rule for Σ-®.

  Σ-®-ω :
    {⊩A : Δ ⊩⟨ l ⟩ U.wk id A} →
    p PE.≢ 𝟘 →
    Σ-® l A ⊩A t₁ v v₂ p →
    ∃ λ v₁ → v T.⇒* T.prod v₁ v₂ × t₁ ®⟨ l ⟩ v₁ ∷ U.wk id A / ⊩A
  Σ-®-ω p≢𝟘 x =
    Σ-®-elim _ x (λ _ p≡𝟘 → ⊥-elim $ p≢𝟘 p≡𝟘)
      (λ _ v⇒ t₁®v₁ _ → _ , v⇒ , t₁®v₁)
