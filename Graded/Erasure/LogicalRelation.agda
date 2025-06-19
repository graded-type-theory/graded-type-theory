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

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Weakening.Restricted R
open import Definition.Typed R

open import Graded.Erasure.Target as T
open import Graded.Erasure.Extraction 𝕄

open import Tools.Empty
open import Tools.Function
import Tools.Level as L
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation


private
  variable
    m n : Nat
    A B t t₁ t′ u u′ : U.Term n
    v v₂ v′ w : T.Term n
    p : M
    l : Universe-level
    s : Strength

------------------------------------------------------------------------
-- The logical relation

-- In the non-strict setting terms of type U or Level are related to
-- all target terms, and in the strict setting they are related to
-- those terms that reduce to ↯.

data _®_∷U/Level (t : U.Term k) (v : T.Term k) : Set a where
  U/Levelᵣ : (str PE.≡ strict → v ⇒* ↯) → t ® v ∷U/Level

-- Terms of type ℕ are related if both reduce to zero or if both
-- reduce to the successors of related terms (in the strict setting
-- the target term's reduct has to be a numeral).

data _®_∷ℕ (t : U.Term k) (v : T.Term k) : Set a where
  zeroᵣ : t ⇛ U.zero ∷ ℕ → v ⇒* T.zero →
          t ® v ∷ℕ
  sucᵣ  : t ⇛ U.suc t′ ∷ ℕ → v ⇒* T.suc v′ → Numeral⟨ str ⟩ v′ →
          t′ ® v′ ∷ℕ → t ® v ∷ℕ

-- Terms of type Empty are not related to anything.
-- (There are no terms of the Empty type in a consistent context).

data _®_∷Empty (t : U.Term k) (v : T.Term k) : Set a where

-- Terms of type Unit are related if both reduce to star.

data _®_∷Unit⟨_,_⟩
  (t : U.Term k) (v : T.Term k) (s : Strength) (u : U.Term k) :
  Set a where
  starᵣ : t ⇛ U.star s u′ ∷ Unit s u′ → Δ ⊢ u ≡ u′ ∷ Level →
          v ⇒* T.star →
          t ® v ∷Unit⟨ s , u ⟩

-- Equality proofs are related in the non-strict setting if the source
-- term reduces to rfl. In the strict setting the target term should
-- additionally reduce to ↯.

data _®_∷Id⟨_⟩⟨_⟩⟨_⟩
       (t : U.Term k) (v : T.Term k) (Ty lhs rhs : U.Term k) :
       Set a where
  rflᵣ : t ⇛ U.rfl ∷ Id Ty lhs rhs → (str PE.≡ strict → v ⇒* ↯) →
         t ® v ∷Id⟨ Ty ⟩⟨ lhs ⟩⟨ rhs ⟩

mutual

  -- Logical relation for erasure
  infix 19 _®⟨_⟩_∷_/_

  _®⟨_⟩_∷_/_ : (t : U.Term k) (l : Universe-level) (v : T.Term k)
               (A : U.Term k) ([A] : Δ ⊩⟨ l ⟩ A) → Set a
  t ®⟨ l ⟩ v ∷ _ / Levelᵣ _          = t ® v ∷U/Level
  t ®⟨ l ⟩ v ∷ _ / Uᵣ _              = t ® v ∷U/Level
  t ®⟨ l ⟩ v ∷ A / ℕᵣ x              = t ® v ∷ℕ
  t ®⟨ l ⟩ v ∷ A / Emptyᵣ x          = t ® v ∷Empty
  t ®⟨ l ⟩ v ∷ A / Unitᵣ {s} ⊩A      = t ® v ∷Unit⟨ s , ⊩A ._⊩Unit⟨_,_⟩_.k ⟩
  t ®⟨ l ⟩ v ∷ A / ne′ _ _ D neK K≡K = L.Lift a ⊥

  t ®⟨ l ⟩ v ∷ _ / Liftᵣ′ {F = A} _ _ ⊩A =
    lower t ®⟨ l ⟩ v ∷ A / ⊩A

  -- Π:
  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ p q) F G D A≡A [F] [G] G-ext _ =
    (str PE.≡ strict → ∃ λ v′ → v ⇒* T.lam v′) ×
    (∀ {a} → ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk id F / [F] (id ⊢Δ)) →
     Π-® l F G t a v ([F] (id ⊢Δ)) ([G] (id ⊢Δ) [a]) p (is-𝟘? p))

  -- Σ:
  -- t and v are related if:
  -- t reduces to a pair (t₁, t₂),
  -- t₂ is related to some v₂ and
  -- there is extra data depending on whether the first component
  -- is erased (see below).
  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΣ m p q) F G D A≡A [F] [G] G-ext _ =
    ∃₂ λ t₁ t₂ →
    t ⇛ U.prod m p t₁ t₂ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G ×
    Σ (Δ ⊩⟨ l ⟩ t₁ ∷ U.wk id F / [F] (id ⊢Δ)) λ [t₁] →
    ∃ λ v₂ →
    t₂ ®⟨ l ⟩ v₂ ∷ U.wk (lift id) G U.[ t₁ ]₀ / [G] (id ⊢Δ) [t₁] ×
    Σ-® l F ([F] (id ⊢Δ)) t₁ v v₂ p

  -- Identity types.
  t ®⟨ _ ⟩ v ∷ A / Idᵣ ⊩A = t ® v ∷Id⟨ Ty ⟩⟨ lhs ⟩⟨ rhs ⟩
    where
    open _⊩ₗId_ ⊩A

  -- Extra data for Π-types, depending on whether the function argument
  -- is erased or not.

  Π-® : (l : Universe-level) (F : U.Term k) (G : U.Term (1+ k))
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
    (l : Universe-level) (F : U.Term k) →
    Δ ⊩⟨ l ⟩ U.wk id F →
    U.Term k → T.Term k → T.Term k → (p : M) → Set a
  Σ-® l F [F] t₁ v v₂ p = case is-𝟘? p of λ where
    -- Erased Σ:
    -- v reduces to v₂
    (yes p≡𝟘) → L.Lift a (v ⇒* v₂)
    -- There is a term v₁ such that v reduces to (v₁, v₂)
    -- and t₁ is related to v₁.
    (no p≢𝟘) → ∃ λ v₁ → (v ⇒* T.prod v₁ v₂)
                      × (t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F])

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
            → v ⇒* v₂ → p PE.≡ 𝟘
            → Σ-® l F [F] t₁ v v₂ p
Σ-®-intro-𝟘 {p = p} v⇒v₂ p≡𝟘 with is-𝟘? p
... | yes _ = L.lift v⇒v₂
... | no p≢𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)

Σ-®-intro-ω : ∀ {l F [F] t₁ v v₂ p}
            → (v₁ : T.Term k)
            → v ⇒* T.prod v₁ v₂
            → t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F]
            → p PE.≢ 𝟘
            → Σ-® l F [F] t₁ v v₂ p
Σ-®-intro-ω {p = p} v₁ v⇒v′ t₁®v₁ p≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = ⊥-elim (p≢𝟘 p≡𝟘)
... | no _ = v₁ , v⇒v′ , t₁®v₁

Σ-®-elim : ∀ {b l F [F] t₁ v v₂ p}
         → (P : (p : M) → Set b)
         → Σ-® l F [F] t₁ v v₂ p
         → (v ⇒* v₂ → p PE.≡ 𝟘 → P p)
         → ((v₁ : T.Term k) → v ⇒* T.prod v₁ v₂ →
            t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F] → p PE.≢ 𝟘 → P p)
         → P p
Σ-®-elim {p = p} P extra f g with is-𝟘? p
Σ-®-elim {p = p} P (L.lift v⇒v₂) f g | yes p≡𝟘 = f v⇒v₂ p≡𝟘
Σ-®-elim {p = p} P (v₁ , v⇒v₁,v₂ , t₁®v₁) f g | no p≢𝟘 = g v₁ v⇒v₁,v₂ t₁®v₁ p≢𝟘

opaque

  -- A "reduction" rule for Σ-®.

  Σ-®-𝟘 :
    {⊩A : Δ ⊩⟨ l ⟩ U.wk id A} →
    Σ-® l A ⊩A t₁ v v₂ 𝟘 →
    v ⇒* v₂
  Σ-®-𝟘 x =
    Σ-®-elim (λ _ → _ ⇒* _) x (λ v⇒ _ → v⇒)
      (λ _ _ _ 𝟘≢𝟘 → ⊥-elim $ 𝟘≢𝟘 PE.refl)

opaque

  -- A "reduction" rule for Σ-®.

  Σ-®-ω :
    {⊩A : Δ ⊩⟨ l ⟩ U.wk id A} →
    p PE.≢ 𝟘 →
    Σ-® l A ⊩A t₁ v v₂ p →
    ∃ λ v₁ → v ⇒* T.prod v₁ v₂ × t₁ ®⟨ l ⟩ v₁ ∷ U.wk id A / ⊩A
  Σ-®-ω p≢𝟘 x =
    Σ-®-elim _ x (λ _ p≡𝟘 → ⊥-elim $ p≢𝟘 p≡𝟘)
      (λ _ v⇒ t₁®v₁ _ → _ , v⇒ , t₁®v₁)
