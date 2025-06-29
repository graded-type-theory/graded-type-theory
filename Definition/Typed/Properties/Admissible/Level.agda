------------------------------------------------------------------------
-- Admissible rules for Level
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Admissible.Level
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion R
import Definition.Typed.Substitution.Primitive.Primitive R as S
open import Definition.Typed.Properties.Admissible.Equality R
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Syntactic R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  Γ                                     : Con Term _
  A B B₁ B₂ l l₁ l₂ l₂′ t t₁ t₂ u u₁ u₂ : Term _

wf-⊢≤ : Γ ⊢ t ≤ u ∷Level → Γ ⊢ t ∷ Level × Γ ⊢ u ∷ Level
wf-⊢≤ t≤u =
  let _ , ⊢t⊔u , ⊢u = syntacticEqTerm t≤u
      ⊢t , _ = inversion-maxᵘ ⊢t⊔u
  in ⊢t , ⊢u

-- The order on levels is reflexive

⊢≤-refl : ∀ {t u} → Γ ⊢ t ≡ u ∷ Level → Γ ⊢ t ≤ u ∷Level
⊢≤-refl t≡u =
  let _ , _ , ⊢u = syntacticEqTerm t≡u
  in trans (maxᵘ-cong t≡u (refl ⊢u)) (maxᵘ-idem ⊢u)

-- The order on levels is transitive

⊢≤-trans
  : ∀ {t u v}
  → Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ u ≤ v ∷Level
  → Γ ⊢ t ≤ v ∷Level
⊢≤-trans {t} {u} {v} t≤u u≤v =
  let ⊢t , ⊢u = wf-⊢≤ t≤u
      _  , ⊢v = wf-⊢≤ u≤v
  in
  t maxᵘ v          ≡˘⟨ maxᵘ-cong (refl ⊢t) u≤v ⟩⊢
  t maxᵘ (u maxᵘ v) ≡˘⟨ maxᵘ-assoc ⊢t ⊢u ⊢v ⟩⊢
  (t maxᵘ u) maxᵘ v ≡⟨ maxᵘ-cong t≤u (refl ⊢v) ⟩⊢
  u maxᵘ v          ≡⟨ u≤v ⟩⊢∎
  v                 ∎

-- The order on levels is antisymmetric

⊢≤-antisymmetric
  : ∀ {t u}
  → Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ u ≤ t ∷Level
  → Γ ⊢ t ≡ u ∷ Level
⊢≤-antisymmetric {t} {u} t≤u u≤t =
  let ⊢t , ⊢u = wf-⊢≤ t≤u in
  t        ≡˘⟨ u≤t ⟩⊢
  u maxᵘ t ≡⟨ maxᵘ-comm ⊢u ⊢t ⟩⊢
  t maxᵘ u ≡⟨ t≤u ⟩⊢∎
  u        ∎

-- A typing rule for sucᵘᵏ

⊢sucᵘᵏ : ∀ {t k} → Γ ⊢ t ∷ Level → Γ ⊢ sucᵘᵏ k t ∷ Level
⊢sucᵘᵏ {k = 0} ⊢t = ⊢t
⊢sucᵘᵏ {k = 1+ k} ⊢t = sucᵘⱼ (⊢sucᵘᵏ ⊢t)

-- A variant of maxᵘ-sub.
--
-- This is also proved in EqualityRelation but we can't import that
-- without creating a dependency cycle...

maxᵘ-sub′
  : Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ t ≤ sucᵘ u ∷Level
maxᵘ-sub′ {t} {u} t≤u =
  let ⊢t , ⊢u = wf-⊢≤ t≤u in
  t maxᵘ sucᵘ u               ≡˘⟨ maxᵘ-cong (refl ⊢t) (trans (maxᵘ-sucᵘ ⊢t ⊢u) (sucᵘ-cong t≤u)) ⟩⊢
  t maxᵘ (sucᵘ t maxᵘ sucᵘ u) ≡˘⟨ maxᵘ-assoc ⊢t (sucᵘⱼ ⊢t) (sucᵘⱼ ⊢u) ⟩⊢
  (t maxᵘ sucᵘ t) maxᵘ sucᵘ u ≡⟨ maxᵘ-cong (maxᵘ-sub ⊢t) (refl (sucᵘⱼ ⊢u)) ⟩⊢
  sucᵘ t maxᵘ sucᵘ u          ≡⟨ maxᵘ-sucᵘ ⊢t ⊢u ⟩⊢
  sucᵘ (t maxᵘ u)             ≡⟨ sucᵘ-cong t≤u ⟩⊢∎
  sucᵘ u                      ∎

-- If t ≤ u, then t ≤ sucᵘᵏ k u

maxᵘ-subᵏ
  : ∀ {t u k}
  → Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ t ≤ sucᵘᵏ k u ∷Level
maxᵘ-subᵏ {k = 0} t≤u = t≤u
maxᵘ-subᵏ {k = 1+ k} t≤u = maxᵘ-sub′ (maxᵘ-subᵏ t≤u)

-- If t ≤ u, then sucᵘ t ≤ sucᵘ u

≤-sucᵘ
  : ∀ {t u}
  → Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ sucᵘ t ≤ sucᵘ u ∷Level
≤-sucᵘ t≤u =
  let ⊢t , ⊢u = wf-⊢≤ t≤u
  in trans (maxᵘ-sucᵘ ⊢t ⊢u) (sucᵘ-cong t≤u)

-- If n ≤ m and t ≤ u, then sucᵘᵏ n t ≤ sucᵘᵏ m u

≤-sucᵘᵏ
  : ∀ {t u n m}
  → n ≤ m
  → Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ sucᵘᵏ n t ≤ sucᵘᵏ m u ∷Level
≤-sucᵘᵏ z≤n t≤u = maxᵘ-subᵏ t≤u
≤-sucᵘᵏ (s≤s n≤m) t≤u = ≤-sucᵘ (≤-sucᵘᵏ n≤m t≤u)

-- A variant of maxᵘ-comm

maxᵘ-comm-assoc
  : ∀ {t u v}
  → Γ ⊢ t ∷ Level
  → Γ ⊢ u ∷ Level
  → Γ ⊢ v ∷ Level
  → Γ ⊢ t maxᵘ (u maxᵘ v) ≡ u maxᵘ (t maxᵘ v) ∷ Level
maxᵘ-comm-assoc ⊢t ⊢u ⊢v =
  trans (sym′ (maxᵘ-assoc ⊢t ⊢u ⊢v))
    (trans (maxᵘ-cong (maxᵘ-comm ⊢t ⊢u) (refl ⊢v))
      (maxᵘ-assoc ⊢u ⊢t ⊢v))
