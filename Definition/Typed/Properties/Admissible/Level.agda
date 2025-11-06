------------------------------------------------------------------------
-- Admissible rules for Level as well as some lemmas related to
-- _⊢_≡_∷Level
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
import Definition.Typed.Properties.Admissible.Level.Primitive R as LP
open import Definition.Typed.Reasoning.Term R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat as N using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

open LP public hiding (supᵘ-zeroʳⱼ)

private variable
  n                                        : Nat
  Γ                                        : Con Term _
  A B B₁ B₂ l l₁ l₂ l₂′ l₃ t t₁ t₂ u u₁ u₂ : Term _

------------------------------------------------------------------------
-- Lemmas related to _⊢_≤_∷Level

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
supᵘ-subᵏ {k = 0}      t≤u = t≤u
supᵘ-subᵏ {k = N.1+ k} t≤u = supᵘ-sub′ (supᵘ-subᵏ t≤u)

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
  → n N.≤ m
  → Γ ⊢ t ≤ u ∷Level
  → Γ ⊢ sucᵘᵏ n t ≤ sucᵘᵏ m u ∷Level
≤-sucᵘᵏ N.z≤n       t≤u = supᵘ-subᵏ t≤u
≤-sucᵘᵏ (N.s≤s n≤m) t≤u = ≤-sucᵘ (≤-sucᵘᵏ n≤m t≤u)

------------------------------------------------------------------------
-- Some lemmas related to _⊢_∷Level or _⊢_≡_∷Level

opaque

  -- If Γ ⊢ l ∷Level holds and Level is allowed, then Γ ⊢ l ∷ Level
  -- holds.

  ⊢∷Level→⊢∷Level :
    Level-allowed →
    Γ ⊢ l ∷Level →
    Γ ⊢ l ∷ Level
  ⊢∷Level→⊢∷Level _  (term _ ⊢l)          = ⊢l
  ⊢∷Level→⊢∷Level ok (literal not-ok _ _) = ⊥-elim (not-ok ok)

opaque

  -- If Γ ⊢ l₁ ≡ l₂ ∷Level holds and Level is allowed, then
  -- Γ ⊢ l₁ ≡ l₂ ∷ Level holds.

  ⊢≡∷Level→⊢≡∷Level :
    Level-allowed →
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ l₁ ≡ l₂ ∷ Level
  ⊢≡∷Level→⊢≡∷Level _  (term _ l₁≡l₂)       = l₁≡l₂
  ⊢≡∷Level→⊢≡∷Level ok (literal not-ok _ _) = ⊥-elim (not-ok ok)

opaque

  -- A variant of _⊢_∷Level.term.

  term-⊢∷ : Γ ⊢ l ∷ Level → Γ ⊢ l ∷Level
  term-⊢∷ ⊢l = term (inversion-Level-⊢ (wf-⊢∷ ⊢l)) ⊢l

opaque

  -- A variant of _⊢_≡_∷Level.term.

  term-⊢≡∷ : Γ ⊢ l₁ ≡ l₂ ∷ Level → Γ ⊢ l₁ ≡ l₂ ∷Level
  term-⊢≡∷ l₁≡l₂ = term (inversion-Level-⊢ (wf-⊢≡∷ l₁≡l₂ .proj₁)) l₁≡l₂

------------------------------------------------------------------------
-- A lemma related to suc

opaque

  -- A variant of sucᵘ-cong.

  sucᵘ-cong-⊢≡∷L :
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ sucᵘ l₁ ≡ sucᵘ l₂ ∷Level
  sucᵘ-cong-⊢≡∷L (term ok l₁≡l₂) =
    term ok (sucᵘ-cong l₁≡l₂)
  sucᵘ-cong-⊢≡∷L (literal not-ok ⊢Γ l-lit) =
    literal not-ok ⊢Γ (sucᵘ l-lit)

------------------------------------------------------------------------
-- A lemma related to sucᵘᵏ

opaque

  -- A typing rule for sucᵘᵏ.

  ⊢sucᵘᵏ : Γ ⊢ t ∷ Level → Γ ⊢ sucᵘᵏ n t ∷ Level
  ⊢sucᵘᵏ {n = 0}      ⊢t = ⊢t
  ⊢sucᵘᵏ {n = N.1+ _} ⊢t = sucᵘⱼ (⊢sucᵘᵏ ⊢t)

------------------------------------------------------------------------
-- Some lemmas related to _supᵘ_

opaque

  -- The level zeroᵘ is a right unit for _supᵘ_.

  supᵘ-zeroʳⱼ :
    Γ ⊢ l ∷ Level →
    Γ ⊢ l supᵘ zeroᵘ ≡ l ∷ Level
  supᵘ-zeroʳⱼ ⊢l =
    LP.supᵘ-zeroʳⱼ (inversion-Level-⊢ (wf-⊢∷ ⊢l)) ⊢l

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

------------------------------------------------------------------------
-- Some lemmas related to _supᵘₗ_

opaque
  unfolding size-of-Level

  -- A variant of _⊢_≡_∷_.supᵘ-zeroˡ.

  supᵘₗ-zeroˡ :
    Γ ⊢ l ∷Level →
    Γ ⊢ zeroᵘ supᵘₗ l ≡ l ∷Level
  supᵘₗ-zeroˡ (term ok ⊢l) =
    PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-zeroˡ ⊢l)
  supᵘₗ-zeroˡ {l} (literal not-ok ⊢Γ l-lit) =
    PE.subst (flip (_⊢_≡_∷Level _) _)
      (l                         ≡˘⟨ ↓ᵘ-size-of-Level ⟩
       ↓ᵘ (size-of-Level l-lit)  ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok zeroᵘ l-lit ⟩
       zeroᵘ supᵘₗ l             ∎) $
    literal not-ok ⊢Γ l-lit

opaque
  unfolding size-of-Level

  -- A variant of supᵘ-zeroʳⱼ.

  supᵘₗ-zeroʳ :
    ⊢ Γ →
    Γ ⊢ l ∷Level →
    Γ ⊢ l supᵘₗ zeroᵘ ≡ l ∷Level
  supᵘₗ-zeroʳ ⊢Γ ⊢l =
    trans-⊢≡∷L (supᵘₗ-comm ⊢l (⊢zeroᵘ ⊢Γ)) (supᵘₗ-zeroˡ ⊢l)

opaque
  unfolding size-of-Level

  -- A variant of _⊢_≡_∷_.supᵘ-sucᵘ.

  supᵘₗ-sucᵘ :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ sucᵘ l₁ supᵘₗ sucᵘ l₂ ≡ sucᵘ (l₁ supᵘₗ l₂) ∷Level
  supᵘₗ-sucᵘ (term ok ⊢l₁) (term _ ⊢l₂) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡supᵘ ok)
      (PE.cong sucᵘ $ PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-sucᵘ ⊢l₁ ⊢l₂)
  supᵘₗ-sucᵘ (term ok _) (literal not-ok _ _) =
    ⊥-elim (not-ok ok)
  supᵘₗ-sucᵘ (literal not-ok _ _) (term ok _) =
    ⊥-elim (not-ok ok)
  supᵘₗ-sucᵘ (literal not-ok ⊢Γ l₁-lit) (literal _ _ l₂-lit) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡↓ᵘ⊔ not-ok (sucᵘ l₁-lit) (sucᵘ l₂-lit))
      (PE.cong sucᵘ $ PE.sym $ supᵘₗ≡↓ᵘ⊔ not-ok l₁-lit l₂-lit) $
    literal not-ok ⊢Γ Level-literal-↓ᵘ

opaque

  -- A variant of supᵘ-assoc.

  supᵘₗ-assoc :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ l₃ ∷Level →
    Γ ⊢ (l₁ supᵘₗ l₂) supᵘₗ l₃ ≡ l₁ supᵘₗ (l₂ supᵘₗ l₃) ∷Level
  supᵘₗ-assoc (term ok ⊢l₁) (term _ ⊢l₂) (term _ ⊢l₃) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $
       PE.trans (PE.cong (_supᵘₗ _) $ supᵘₗ≡supᵘ ok) $
       supᵘₗ≡supᵘ ok)
      (PE.sym $
       PE.trans (PE.cong (_ supᵘₗ_) $ supᵘₗ≡supᵘ ok) $
       supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-assoc ⊢l₁ ⊢l₂ ⊢l₃)
  supᵘₗ-assoc (term ok _) (literal not-ok _ _) _ =
    ⊥-elim (not-ok ok)
  supᵘₗ-assoc (term ok _) _ (literal not-ok _ _) =
    ⊥-elim (not-ok ok)
  supᵘₗ-assoc (literal not-ok _ _) (term ok _) _ =
    ⊥-elim (not-ok ok)
  supᵘₗ-assoc (literal not-ok _ _) _ (term ok _) =
    ⊥-elim (not-ok ok)
  supᵘₗ-assoc
    {l₁} {l₂} {l₃}
    (literal not-ok ⊢Γ l₁-lit) (literal _ _ l₂-lit)
    (literal _ _ l₃-lit) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (↓ᵘ (size-of-Level l₁-lit N.⊔ size-of-Level Level-literal-↓ᵘ)   ≡⟨ PE.cong (↓ᵘ_ ∘→ (size-of-Level _ N.⊔_))
                                                                           size-of-Level-Level-literal-↓ᵘ ⟩
       ↓ᵘ (size-of-Level l₁-lit N.⊔
           (size-of-Level l₂-lit N.⊔ size-of-Level l₃-lit))           ≡˘⟨ PE.cong ↓ᵘ_ $ N.⊔-assoc (size-of-Level _) _ _ ⟩

       ↓ᵘ ((size-of-Level l₁-lit N.⊔ size-of-Level l₂-lit) N.⊔
           size-of-Level l₃-lit)                                      ≡˘⟨ PE.cong (↓ᵘ_ ∘→ (N._⊔ size-of-Level _))
                                                                            size-of-Level-Level-literal-↓ᵘ ⟩

       ↓ᵘ (size-of-Level Level-literal-↓ᵘ N.⊔ size-of-Level l₃-lit)   ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok Level-literal-↓ᵘ l₃-lit ⟩

       (↓ᵘ (size-of-Level l₁-lit N.⊔ size-of-Level l₂-lit)) supᵘₗ l₃  ≡˘⟨ PE.cong (_supᵘₗ _) $ supᵘₗ≡↓ᵘ⊔ not-ok l₁-lit l₂-lit ⟩

       (l₁ supᵘₗ l₂) supᵘₗ l₃                                         ∎)
      (↓ᵘ (size-of-Level l₁-lit N.⊔ size-of-Level Level-literal-↓ᵘ)   ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok l₁-lit Level-literal-↓ᵘ ⟩
       l₁ supᵘₗ (↓ᵘ (size-of-Level l₂-lit N.⊔ size-of-Level l₃-lit))  ≡˘⟨ PE.cong (_ supᵘₗ_) $ supᵘₗ≡↓ᵘ⊔ not-ok l₂-lit l₃-lit ⟩
       l₁ supᵘₗ (l₂ supᵘₗ l₃)                                         ∎) $
    literal not-ok ⊢Γ Level-literal-↓ᵘ

opaque

  -- A variant of supᵘ-idem.

  supᵘₗ-idem :
    Γ ⊢ l ∷Level →
    Γ ⊢ l supᵘₗ l ≡ l ∷Level
  supᵘₗ-idem (term ok ⊢l) =
    PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-idem ⊢l)
  supᵘₗ-idem {l} (literal not-ok ⊢Γ l-lit) =
    PE.subst (flip (_⊢_≡_∷Level _) _)
      (l                                                 ≡˘⟨ ↓ᵘ-size-of-Level ⟩
       ↓ᵘ (size-of-Level l-lit)                          ≡˘⟨ PE.cong ↓ᵘ_ $ N.⊔-idem _ ⟩
       ↓ᵘ (size-of-Level l-lit N.⊔ size-of-Level l-lit)  ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok l-lit l-lit ⟩
       l supᵘₗ l                                         ∎) $
    literal not-ok ⊢Γ l-lit

opaque
  unfolding size-of-Level

  -- A variant of supᵘ-sub.

  supᵘₗ-sub :
    Γ ⊢ l ∷Level →
    Γ ⊢ l supᵘₗ sucᵘ l ≡ sucᵘ l ∷Level
  supᵘₗ-sub (term ok ⊢l) =
    PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-sub ⊢l)
  supᵘₗ-sub {l} (literal not-ok ⊢Γ l-lit) =
    PE.subst (flip (_⊢_≡_∷Level _) _)
      (sucᵘ l                                                   ≡˘⟨ ↓ᵘ-size-of-Level ⟩
       ↓ᵘ (N.1+ (size-of-Level l-lit))                          ≡˘⟨ PE.cong ↓ᵘ_ $ N.m≤n⇒m⊔n≡n (N.n≤1+n _) ⟩
       ↓ᵘ (size-of-Level l-lit N.⊔ N.1+ (size-of-Level l-lit))  ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok l-lit (sucᵘ l-lit) ⟩
       l supᵘₗ sucᵘ l                                           ∎) $
    literal not-ok ⊢Γ (sucᵘ l-lit)
