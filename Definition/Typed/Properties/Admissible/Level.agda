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
      ⊢t , _ = inversion-supᵘ ⊢t⊔u
  in ⊢t , ⊢u

-- The order on levels is reflexive

⊢≤-refl : ∀ {t u} → Γ ⊢ t ≡ u ∷ Level → Γ ⊢ t ≤ u ∷Level
⊢≤-refl t≡u =
  let _ , _ , ⊢u = syntacticEqTerm t≡u
  in trans (supᵘ-cong t≡u (refl ⊢u)) (supᵘ-idem ⊢u)

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
  t supᵘ v          ≡˘⟨ supᵘ-cong (refl ⊢t) u≤v ⟩⊢
  t supᵘ (u supᵘ v) ≡˘⟨ supᵘ-assoc ⊢t ⊢u ⊢v ⟩⊢
  (t supᵘ u) supᵘ v ≡⟨ supᵘ-cong t≤u (refl ⊢v) ⟩⊢
  u supᵘ v          ≡⟨ u≤v ⟩⊢∎
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
  u supᵘ t ≡⟨ supᵘ-comm ⊢u ⊢t ⟩⊢
  t supᵘ u ≡⟨ t≤u ⟩⊢∎
  u        ∎

-- A typing rule for sucᵘᵏ

⊢sucᵘᵏ : ∀ {t k} → Γ ⊢ t ∷ Level → Γ ⊢ sucᵘᵏ k t ∷ Level
⊢sucᵘᵏ {k = 0} ⊢t = ⊢t
⊢sucᵘᵏ {k = 1+ k} ⊢t = sucᵘⱼ (⊢sucᵘᵏ ⊢t)

-- A variant of supᵘ-sub.
--
-- This is also proved in EqualityRelation but we can't import that
-- without creating a dependency cycle...

supᵘ-sub′
  : Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ t ≤ sucᵘ u ∷Level
supᵘ-sub′ {t} {u} t≤u =
  let ⊢t , ⊢u = wf-⊢≤ t≤u in
  t supᵘ sucᵘ u               ≡˘⟨ supᵘ-cong (refl ⊢t) (trans (supᵘ-sucᵘ ⊢t ⊢u) (sucᵘ-cong t≤u)) ⟩⊢
  t supᵘ (sucᵘ t supᵘ sucᵘ u) ≡˘⟨ supᵘ-assoc ⊢t (sucᵘⱼ ⊢t) (sucᵘⱼ ⊢u) ⟩⊢
  (t supᵘ sucᵘ t) supᵘ sucᵘ u ≡⟨ supᵘ-cong (supᵘ-sub ⊢t) (refl (sucᵘⱼ ⊢u)) ⟩⊢
  sucᵘ t supᵘ sucᵘ u          ≡⟨ supᵘ-sucᵘ ⊢t ⊢u ⟩⊢
  sucᵘ (t supᵘ u)             ≡⟨ sucᵘ-cong t≤u ⟩⊢∎
  sucᵘ u                      ∎

-- If t ≤ u, then t ≤ sucᵘᵏ k u

supᵘ-subᵏ
  : ∀ {t u k}
  → Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ t ≤ sucᵘᵏ k u ∷Level
supᵘ-subᵏ {k = 0} t≤u = t≤u
supᵘ-subᵏ {k = 1+ k} t≤u = supᵘ-sub′ (supᵘ-subᵏ t≤u)

-- If t ≤ u, then sucᵘ t ≤ sucᵘ u

≤-sucᵘ
  : ∀ {t u}
  → Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ sucᵘ t ≤ sucᵘ u ∷Level
≤-sucᵘ t≤u =
  let ⊢t , ⊢u = wf-⊢≤ t≤u
  in trans (supᵘ-sucᵘ ⊢t ⊢u) (sucᵘ-cong t≤u)

-- If n ≤ m and t ≤ u, then sucᵘᵏ n t ≤ sucᵘᵏ m u

≤-sucᵘᵏ
  : ∀ {t u n m}
  → n ≤ m
  → Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ sucᵘᵏ n t ≤ sucᵘᵏ m u ∷Level
≤-sucᵘᵏ z≤n t≤u = supᵘ-subᵏ t≤u
≤-sucᵘᵏ (s≤s n≤m) t≤u = ≤-sucᵘ (≤-sucᵘᵏ n≤m t≤u)

-- A variant of supᵘ-comm

supᵘ-comm-assoc
  : ∀ {t u v}
  → Γ ⊢ t ∷ Level
  → Γ ⊢ u ∷ Level
  → Γ ⊢ v ∷ Level
  → Γ ⊢ t supᵘ (u supᵘ v) ≡ u supᵘ (t supᵘ v) ∷ Level
supᵘ-comm-assoc ⊢t ⊢u ⊢v =
  trans (sym′ (supᵘ-assoc ⊢t ⊢u ⊢v))
    (trans (supᵘ-cong (supᵘ-comm ⊢t ⊢u) (refl ⊢v))
      (supᵘ-assoc ⊢u ⊢t ⊢v))
