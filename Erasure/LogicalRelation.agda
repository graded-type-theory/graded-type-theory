------------------------------------------------------------------------
-- The Logical relation for erasure.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
import Definition.Untyped as U′ using (Con; Term)
import Definition.Typed as T′
open import Definition.Modality
import Tools.PropositionalEquality as PE
open import Tools.Nullary

module Erasure.LogicalRelation
  {a k} {M : Set a} (𝕄 : Modality M)
  (open T′ M) (open Modality 𝕄)
  {Δ : U′.Con (U′.Term M) k} (⊢Δ : ⊢ Δ)
  (is-𝟘? : (p : M) → Dec (p PE.≡ 𝟘))
  {{eqrel : EqRelSet M}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M as U hiding (_∷_; _∘_)

open import Definition.LogicalRelation M
open import Definition.LogicalRelation.Substitution M
open import Definition.Modality.Context 𝕄
open import Definition.Mode 𝕄
open import Definition.Typed.Weakening M

open import Erasure.Target as T hiding (_⇒*_)
open import Erasure.Extraction 𝕄 is-𝟘?

open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
open import Tools.Unit


private
  variable
    m n : Nat
    t′ : U.Term n
    v′ : T.Term n
    p : M

-- Logical relation for erasure for base types

data _®_∷U (t : U.Term k) (v : T.Term k) : Set a where
  Uᵣ : Δ ⊢ t ∷ U → t ® v ∷U

data _®_∷ℕ (t : U.Term k) (v : T.Term k) : Set a where
  zeroᵣ : Δ ⊢ t ⇒* U.zero ∷ ℕ → v T.⇒* T.zero → t ® v ∷ℕ
  sucᵣ : Δ ⊢ t ⇒* U.suc t′ ∷ ℕ → v T.⇒* T.suc v′ → t′ ® v′ ∷ℕ → t ® v ∷ℕ

data _®_∷Empty (t : U.Term k) (v : T.Term k) : Set a where

data _®_∷Unit (t : U.Term k) (v : T.Term k) : Set a where
  starᵣ : Δ ⊢ t ∷ Unit → v T.⇒* T.star → t ® v ∷Unit

mutual

  -- Logical relation for erasure

  _®⟨_⟩_∷_/_ : (t : U.Term k) (l : TypeLevel) (v : T.Term k)
               (A : U.Term k) ([A] : Δ ⊩⟨ l ⟩ A) → Set a
  t ®⟨ l ⟩ v ∷ A / Uᵣ x     = t ® v ∷U
  t ®⟨ l ⟩ v ∷ A / ℕᵣ x     = t ® v ∷ℕ
  t ®⟨ l ⟩ v ∷ A / Emptyᵣ x = t ® v ∷Empty
  t ®⟨ l ⟩ v ∷ A / Unitᵣ x  = t ® v ∷Unit
  t ®⟨ l ⟩ v ∷ A / ne′ K D neK K≡K = Lift a PE.⊥

  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΠ p q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
    ∀ {a} → ([a] : Δ ⊩⟨ l ⟩ a ∷ U.wk id F / [F] id ⊢Δ)
          → Π-® l F G t a v ([F] id ⊢Δ) ([G] id ⊢Δ [a]) p (is-𝟘? p)

  -- Σ:
  t ®⟨ l ⟩ v ∷ A / Bᵣ′ (BΣ m p q) F G D ⊢F ⊢G A≡A [F] [G] G-ext =
    ∃₂ λ t₁ t₂ →
    Δ ⊢ t ⇒* U.prod m p t₁ t₂ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G ×
    Σ (Δ ⊩⟨ l ⟩ t₁ ∷ U.wk id F / [F] id ⊢Δ) λ [t₁] →
    ∃ λ v₂ →
    t₂ ®⟨ l ⟩ v₂ ∷ U.wk (lift id) G U.[ t₁ ] / [G] id ⊢Δ [t₁] ×
    Σ-® l F ([F] id ⊢Δ) t₁ v v₂ p

  -- Subsumption:
  t ®⟨ ¹ ⟩ v ∷ A / emb 0<1 [A] = t ®⟨ ⁰ ⟩ v ∷ A / [A]


  -- Extra data for Π-types, depending on whether the function argument
  -- is erased or not.

  Π-® : (l : TypeLevel) (F : U.Term k) (G : U.Term (1+ k))
        (t b : U.Term k) (v : T.Term k)
        ([F] : Δ ⊩⟨ l ⟩ U.wk id F)
        ([G] : Δ ⊩⟨ l ⟩ U.wk (lift id) G U.[ b ])
        (p : M) (p≟𝟘 : Dec (p PE.≡ 𝟘)) → Set a
  Π-® l F G t a v [F] [Ga] p (yes p≡𝟘) =
    (t ∘⟨ p ⟩ a) ®⟨ l ⟩ v ∘ ↯ ∷ U.wk (lift id) G U.[ a ] / [Ga]
  Π-® l F G t a v [F] [Ga] p (no p≢𝟘) =
    ∀ {w} → a ®⟨ l ⟩ w ∷ U.wk id F / [F]
          → (t ∘⟨ p ⟩ a) ®⟨ l ⟩ v ∘ w ∷ U.wk (lift id) G U.[ a ] / [Ga]

  -- Extra data for Σ-types, depending on whether the first component
  -- is erased or not.

  Σ-® :
    (l : TypeLevel) (F : U.Term k) →
    Δ ⊩⟨ l ⟩ U.wk id F →
    U.Term k → T.Term k → T.Term k → (p : M) → Set a
  Σ-® l F [F] t₁ v v₂ p = case is-𝟘? p of λ where
    (yes p≡𝟘) → Lift a (v T.⇒* v₂)
    (no p≢𝟘) → ∃ λ v₁ → (v T.⇒* T.prod v₁ v₂)
                      × (t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F])

-- Logical relation for terms of quantified type
_®⟨_⟩_∷_◂_/_ : (t : U.Term k) (l : TypeLevel) (v : T.Term k)
                 (A : U.Term k) (p : M)
                 ([A] : Δ ⊩⟨ l ⟩ A) → Set a
t ®⟨ l ⟩ v ∷ A ◂ p / [A] = case is-𝟘? p of λ where
  (yes p≡𝟘) → Lift a ⊤
  (no p≢𝟘) → t ®⟨ l ⟩ v ∷ A / [A]

-- Logical relation for substitutions

_®⟨_⟩_∷[_]_◂_/_/_ :
  (σₜ : U.Subst k n) (l : TypeLevel)
  (σᵥ : T.Subst k n) (m : Mode) (Γ : Con U.Term n) (γ : Conₘ n)
  ([Γ] : ⊩ᵛ Γ) ([σ] : Δ ⊩ˢ σₜ ∷ Γ / [Γ] / ⊢Δ) → Set a
σₜ ®⟨ l ⟩ σᵥ ∷[ _ ] ε ◂ ε / ε / (lift tt) = Lift a ⊤
σₜ ®⟨ l ⟩ σᵥ ∷[ m ] Γ ∙ A ◂ γ ∙ p / _∙_ {l = l₁} [Γ] [A] / ([σ] , [σA]) =
  ((U.tail σₜ) ®⟨ l ⟩ (T.tail σᵥ) ∷[ m ] Γ ◂ γ / [Γ] / [σ]) ×
  ((U.head σₜ) ®⟨ l₁ ⟩ (T.head σᵥ) ∷ (U.subst (U.tail σₜ) A)
  ◂ ⌜ m ⌝ · p / proj₁ (unwrap [A] ⊢Δ [σ]))

-- Validity of erasure

_▸_⊩ʳ⟨_⟩_∷[_]_/_/_ :
  (γ : Conₘ n) (Γ : Con U.Term n) (l : TypeLevel)
  (t : U.Term n) (m : Mode) (A : U.Term n)
  ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) → Set a
γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] A / [Γ] / [A] =
  ∀ {σ σ′} →
  ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  σ ®⟨ l ⟩ σ′ ∷[ m ] Γ ◂ γ / [Γ] / [σ] →
  U.subst σ t ®⟨ l ⟩ T.subst σ′ (erase t) ∷ U.subst σ A ◂ ⌜ m ⌝ /
    proj₁ (unwrap [A] ⊢Δ [σ])

Σ-®-intro-𝟘 : ∀ {l F [F] t₁ v v₂ p}
            → v T.⇒* v₂ → p PE.≡ 𝟘
            → Σ-® l F [F] t₁ v v₂ p
Σ-®-intro-𝟘 {p = p} v⇒v₂ p≡𝟘 with is-𝟘? p
... | yes _ = lift v⇒v₂
... | no p≢𝟘 = PE.⊥-elim (p≢𝟘 p≡𝟘)

Σ-®-intro-ω : ∀ {l F [F] t₁ v v₂ p}
            → (v₁ : T.Term k)
            → v T.⇒* T.prod v₁ v₂
            → t₁ ®⟨ l ⟩ v₁ ∷ U.wk id F / [F]
            → p PE.≢ 𝟘
            → Σ-® l F [F] t₁ v v₂ p
Σ-®-intro-ω {p = p} v₁ v⇒v′ t₁®v₁ p≢𝟘 with is-𝟘? p
... | yes p≡𝟘 = PE.⊥-elim (p≢𝟘 p≡𝟘)
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
