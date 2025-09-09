------------------------------------------------------------------------
-- The Logical relation for erasure.
------------------------------------------------------------------------

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

open import Definition.LogicalRelation.Simplified R
open import Definition.Typed R

open import Graded.Erasure.Target as T hiding (_⊢_⇒*_)
open import Graded.Erasure.Extraction 𝕄

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.List using (List)
open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_)
open import Tools.Relation


private
  variable
    m n : Nat
    A B t t₁ t′ u : U.Term n
    v v₂ v′ w : T.Term n
    p : M
    s : Strength

------------------------------------------------------------------------
-- The logical relation

-- In the non-strict setting terms of type U are related to all target
-- terms, and in the strict setting they are related to those terms
-- that reduce to ↯. (All types are erased by the extraction
-- function.)

data _®_∷U (t : U.Term k) (v : T.Term k) : Set a where
  Uᵣ : (str ≡ strict → vs T.⊢ v ⇒* ↯) → t ® v ∷U

-- Terms of type ℕ are related if both reduce to zero or if both
-- reduce to the successors of related terms (in the strict setting
-- the target term's reduct has to be a numeral).

data _®_∷ℕ (t : U.Term k) (v : T.Term k) : Set a where
  zeroᵣ : t ⇛ U.zero ∷ ℕ → vs T.⊢ v ⇒* T.zero →
          t ® v ∷ℕ
  sucᵣ  : t ⇛ U.suc t′ ∷ ℕ → vs T.⊢ v ⇒* T.suc v′ → Numeral⟨ str ⟩ v′ →
          t′ ® v′ ∷ℕ → t ® v ∷ℕ

-- Terms of type Empty are not related to anything.
-- (There are no terms of the Empty type in a consistent context).

data _®_∷Empty (t : U.Term k) (v : T.Term k) : Set a where

-- Terms of type Unit are related if both reduce to star.

data _®_∷Unit⟨_,_⟩
  (t : U.Term k) (v : T.Term k) (s : Strength) (l : Universe-level) :
  Set a where
  starᵣ : t ⇛ U.star s l ∷ Unit s l → vs T.⊢ v ⇒* T.star →
          t ® v ∷Unit⟨ s , l ⟩

-- Equality proofs are related in the non-strict setting if the source
-- term reduces to rfl. In the strict setting the target term should
-- additionally reduce to ↯.

data _®_∷Id⟨_⟩⟨_⟩⟨_⟩
       (t : U.Term k) (v : T.Term k) (Ty lhs rhs : U.Term k) :
       Set a where
  rflᵣ : t ⇛ U.rfl ∷ Id Ty lhs rhs → (str ≡ strict → vs T.⊢ v ⇒* ↯) →
         t ® v ∷Id⟨ Ty ⟩⟨ lhs ⟩⟨ rhs ⟩

mutual

  -- Logical relation for erasure
  infix 19 _®_∷_/_

  _®_∷_/_ : (t : U.Term k) (v : T.Term k)
            (A : U.Term k) ([A] : ts » Δ ⊨ A) → Set a
  t ® v ∷ A / Uᵣ x         = t ® v ∷U
  t ® v ∷ A / ℕᵣ x         = t ® v ∷ℕ
  t ® v ∷ A / Emptyᵣ x     = t ® v ∷Empty
  t ® v ∷ A / Unitᵣ {s} ⊨A = t ® v ∷Unit⟨ s , ⊨A ._⊨Unit⟨_⟩_.l ⟩
  t ® v ∷ A / ne _         = Lift a ⊥

  -- Π:
  t ® v ∷ A / Bᵣ′ BMΠ p q F G D [F] [G] =
    (str ≡ strict → ∃ λ v′ → vs T.⊢ v ⇒* T.lam v′) ×
    (∀ {a} → (⊢a : ts » Δ ⊢ a ∷ F) →
     Π-® F G t a v [F] ([G] ⊢a) p (is-𝟘? p))

  -- Σ:
  -- t and v are related if:
  -- t reduces to a pair (t₁, t₂),
  -- t₂ is related to some v₂ and
  -- there is extra data depending on whether the first component
  -- is erased (see below).
  t ® v ∷ A / Bᵣ′ (BMΣ m) p q F G D [F] [G] =
    ∃₂ λ t₁ t₂ →
    t ⇛ U.prod m p t₁ t₂ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G ×
    Σ (ts » Δ ⊢ t₁ ∷ F) λ ⊢t₁ →
    ∃ λ v₂ →
    t₂ ® v₂ ∷ G U.[ t₁ ]₀ / [G] ⊢t₁ ×
    Σ-® F [F] t₁ v v₂ p

  -- Identity types.
  t ® v ∷ A / Idᵣ ⊨A = t ® v ∷Id⟨ Ty ⟩⟨ lhs ⟩⟨ rhs ⟩
    where
    open _⊨Id_ ⊨A

  -- Extra data for Π-types, depending on whether the function argument
  -- is erased or not.

  Π-® : (F : U.Term k) (G : U.Term (1+ k))
        (t b : U.Term k) (v : T.Term k)
        ([F] : ts » Δ ⊨ F)
        ([G] : ts » Δ ⊨ G U.[ b ]₀)
        (p : M) (p≟𝟘 : Dec (p PE.≡ 𝟘)) → Set a
  -- Erased Π:
  -- In the strict setting t is related to v if the applications t ∘ a
  -- and v ∘ ↯ are related. In the non-strict setting t ∘ a should be
  -- related to v.
  Π-® F G t a v [F] [Ga] p (yes p≡𝟘) =
    (t U.∘⟨ p ⟩ a) ® app-𝟘 str v ∷ G U.[ a ]₀ / [Ga]
  -- Non-erased Π:
  -- Functions t and v are related if the applications
  -- t∘a and v∘w are related for all related a and w.
  Π-® F G t a v [F] [Ga] p (no p≢𝟘) =
    ∀ {w} → a ® w ∷  F / [F]
          → (t U.∘⟨ p ⟩ a) ® v T.∘⟨ str ⟩ w ∷
              G U.[ a ]₀ / [Ga]

  -- Extra data for Σ-types, depending on whether the first component
  -- is erased or not.

  Σ-® :
    (F : U.Term k) →
    ts » Δ ⊨ F →
    U.Term k → T.Term k → T.Term k → (p : M) → Set a
  Σ-® F [F] t₁ v v₂ p = case is-𝟘? p of λ where
    -- Erased Σ:
    -- v reduces to v₂
    (yes p≡𝟘) → Lift a (vs T.⊢ v ⇒* v₂)
    -- There is a term v₁ such that v reduces to (v₁, v₂)
    -- and t₁ is related to v₁.
    (no p≢𝟘) → ∃ λ v₁ → (vs T.⊢ v ⇒* T.prod v₁ v₂)
                      × (t₁ ® v₁ ∷ F / [F])

------------------------------------------------------------------------
-- Helper functions

opaque

  -- A "reduction" rule for Π-®.

  Π-®-𝟘 :
    {⊨A : ts » Δ ⊨ A}
    {⊨B[u] : ts » Δ ⊨ B U.[ u ]₀}
    (d : Dec (𝟘 PE.≡ 𝟘)) →
    Π-® A B t u v ⊨A ⊨B[u] 𝟘 d →
    (t U.∘⟨ 𝟘 ⟩ u) ® app-𝟘 str v ∷
      B U.[ u ]₀ / ⊨B[u]
  Π-®-𝟘 (no 𝟘≢𝟘) = λ _ → ⊥-elim (𝟘≢𝟘 PE.refl)
  Π-®-𝟘 (yes _)  = idᶠ

opaque

  -- A "reduction" rule for Π-®.

  Π-®-ω :
    {⊨A : ts » Δ ⊨ A}
    {⊨B[u] : ts » Δ ⊨ B U.[ u ]₀} →
    p PE.≢ 𝟘 →
    (d : Dec (p PE.≡ 𝟘)) →
    Π-® A B t u v ⊨A ⊨B[u] p d →
    u ® w ∷ A / ⊨A →
    (t U.∘⟨ p ⟩ u) ® v T.∘⟨ str ⟩ w ∷
      B U.[ u ]₀ / ⊨B[u]
  Π-®-ω p≢𝟘 (yes p≡𝟘) _   = ⊥-elim (p≢𝟘 p≡𝟘)
  Π-®-ω _   (no _)    hyp = hyp

-- Helper introduction and elimination lemmata for Σ-®

Σ-®-intro-𝟘 : ∀ {F [F] t₁ v v₂ p}
            → vs T.⊢ v ⇒* v₂ → p PE.≡ 𝟘
            → Σ-® F [F] t₁ v v₂ p
Σ-®-intro-𝟘 {p = p} v⇒v₂ p≡𝟘 with is-𝟘? p
... | yes _ = lift v⇒v₂
... | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

Σ-®-intro-ω : ∀ {F [F] t₁ v v₂ p}
            → (v₁ : T.Term k)
            → vs T.⊢ v ⇒* T.prod v₁ v₂
            → t₁ ® v₁ ∷ F / [F]
            → p PE.≢ 𝟘
            → Σ-® F [F] t₁ v v₂ p
Σ-®-intro-ω {p = p} v₁ v⇒v′ t₁®v₁ p≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
... | no _ = v₁ , v⇒v′ , t₁®v₁

Σ-®-elim : ∀ {b F [F] t₁ v v₂ p}
         → (P : (p : M) → Set b)
         → Σ-® F [F] t₁ v v₂ p
         → (vs T.⊢ v ⇒* v₂ → p PE.≡ 𝟘 → P p)
         → ((v₁ : T.Term k) → vs T.⊢ v ⇒* T.prod v₁ v₂ →
            t₁ ® v₁ ∷ F / [F] → p PE.≢ 𝟘 → P p)
         → P p
Σ-®-elim {p = p} P extra f g with is-𝟘? p
Σ-®-elim {p = p} P (lift v⇒v₂) f g | yes p≡𝟘 = f v⇒v₂ p≡𝟘
Σ-®-elim {p = p} P (v₁ , v⇒v₁,v₂ , t₁®v₁) f g | no p≢𝟘 = g v₁ v⇒v₁,v₂ t₁®v₁ p≢𝟘

opaque

  -- A "reduction" rule for Σ-®.

  Σ-®-𝟘 :
    {⊨A : ts » Δ ⊨ A} →
    Σ-® A ⊨A t₁ v v₂ 𝟘 →
    vs T.⊢ v ⇒* v₂
  Σ-®-𝟘 x =
    Σ-®-elim (λ _ → _ T.⊢ _ ⇒* _) x (λ v⇒ _ → v⇒)
      (λ _ _ _ 𝟘≢𝟘 → ⊥-elim $ 𝟘≢𝟘 PE.refl)

opaque

  -- A "reduction" rule for Σ-®.

  Σ-®-ω :
    {⊨A : ts » Δ ⊨ A} →
    p PE.≢ 𝟘 →
    Σ-® A ⊨A t₁ v v₂ p →
    ∃ λ v₁ → vs T.⊢ v ⇒* T.prod v₁ v₂ × t₁ ® v₁ ∷ A / ⊨A
  Σ-®-ω p≢𝟘 x =
    Σ-®-elim _ x (λ _ p≡𝟘 → ⊥-elim $ p≢𝟘 p≡𝟘)
      (λ _ v⇒ t₁®v₁ _ → _ , v⇒ , t₁®v₁)
