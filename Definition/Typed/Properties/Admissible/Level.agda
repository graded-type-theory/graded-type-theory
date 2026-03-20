------------------------------------------------------------------------
-- Admissible rules for Level as well as some other lemmas related to
-- Level
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
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Level R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat as N using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation

open LP public hiding (supᵘ-zeroʳⱼ)

private variable
  n n₁ n₂                                                  : Nat
  ξ                                                        : DExt _ _ _
  Γ                                                        : Cons _ _
  A B B₁ B₂ l l₁ l₁₁ l₁₂ l₂ l₂′ l₂₁ l₂₂ l₃ t t₁ t₂ u u₁ u₂ : Term _

------------------------------------------------------------------------
-- Some lemmas related to U and/or Id

opaque

  -- If Level is not small, then Level is not in any universe.

  ¬Level-is-small→¬Level∷U :
    ¬ Level-is-small → ¬ Γ ⊢ Level ∷ U t
  ¬Level-is-small→¬Level∷U ¬small Level∷Ut =
    ¬small (inversion-Level Level∷Ut .proj₂)

opaque

  -- If Level is not small, then Id Level t u does not belong to any
  -- universe.

  ¬Level-is-small→¬Id-Level∷U :
    ¬ Level-is-small →
    ¬ Γ ⊢ Id Level t u ∷ U l
  ¬Level-is-small→¬Id-Level∷U not-ok ⊢Id =
    let _ , Level∷U , _ = inversion-Id-U ⊢Id in
    ¬Level-is-small→¬Level∷U not-ok Level∷U

opaque

  -- If Level is allowed, then the type Id Level t u can be formed for
  -- well-typed levels t and u.

  ⊢Id-Level :
    Level-allowed →
    Γ ⊢ t ∷ Level →
    Γ ⊢ u ∷ Level →
    Γ ⊢ Id Level t u
  ⊢Id-Level ok ⊢t ⊢u =
    Idⱼ (Levelⱼ′ ok (wfTerm ⊢t)) ⊢t ⊢u

------------------------------------------------------------------------
-- Some lemmas related to _⊢_∷Level, _⊢_≡_∷Level or _⊢_≤ₗ_∷Level

opaque

  -- A variant of _⊢_∷Level.term.

  term-⊢∷ : Γ ⊢ l ∷ Level → Γ ⊢ l ∷Level
  term-⊢∷ ⊢l = term (inversion-Level-⊢ (wf-⊢∷ ⊢l)) ⊢l

opaque

  -- A variant of _⊢_≡_∷Level.term.

  term-⊢≡∷ : Γ ⊢ l₁ ≡ l₂ ∷ Level → Γ ⊢ l₁ ≡ l₂ ∷Level
  term-⊢≡∷ l₁≡l₂ = term (inversion-Level-⊢ (wf-⊢≡∷ l₁≡l₂ .proj₁)) l₁≡l₂

opaque

  -- The relation _⊢_≤_∷Level is contained in _⊢_≤ₗ_∷Level.

  term-⊢≤∷L : Γ ⊢ l₁ ≤ l₂ ∷Level → Γ ⊢ l₁ ≤ₗ l₂ ∷Level
  term-⊢≤∷L l₁≤l₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≤l₂ .proj₁) in
    PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym (supᵘₗ≡supᵘ ok)) $
    term-⊢≡∷ l₁≤l₂

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
-- Some lemmas related to sucᵘᵏ and ↓ᵘ_

opaque

  -- A typing rule for sucᵘᵏ.

  ⊢sucᵘᵏ : Γ ⊢ t ∷Level → Γ ⊢ sucᵘᵏ n t ∷Level
  ⊢sucᵘᵏ {n = 0}      ⊢t = ⊢t
  ⊢sucᵘᵏ {n = N.1+ _} ⊢t = ⊢sucᵘ (⊢sucᵘᵏ ⊢t)

opaque

  -- A typing rule for ↓ᵘ_.

  ⊢↓ᵘ : ⊢ Γ → Γ ⊢ ↓ᵘ n ∷Level
  ⊢↓ᵘ ⊢Γ = ⊢sucᵘᵏ (⊢zeroᵘ ⊢Γ)

opaque

  -- Level literals are well-formed levels in well-formed contexts.

  Level-literal→⊢∷L : ⊢ Γ → Level-literal l → Γ ⊢ l ∷Level
  Level-literal→⊢∷L ⊢Γ zeroᵘ        = ⊢zeroᵘ ⊢Γ
  Level-literal→⊢∷L ⊢Γ (sucᵘ l-lit) = ⊢sucᵘ (Level-literal→⊢∷L ⊢Γ l-lit)

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
    Γ ⊢ l ∷Level →
    Γ ⊢ l supᵘₗ zeroᵘ ≡ l ∷Level
  supᵘₗ-zeroʳ {l} ⊢l =
    l supᵘₗ zeroᵘ  ≡⟨ supᵘₗ-comm ⊢l (⊢zeroᵘ (wfLevel ⊢l)) ⟩⊢
    zeroᵘ supᵘₗ l  ≡⟨ supᵘₗ-zeroˡ ⊢l ⟩⊢∎
    l              ∎

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

  -- A variant of supᵘₗ-sucᵘ.

  supᵘₗ-↓ᵘ :
    ⊢ Γ → Γ ⊢ (↓ᵘ n₁) supᵘₗ (↓ᵘ n₂) ≡ ↓ᵘ (n₁ N.⊔ n₂) ∷Level
  supᵘₗ-↓ᵘ {n₁ = 0} ⊢Γ =
    supᵘₗ-zeroˡ (⊢↓ᵘ ⊢Γ)
  supᵘₗ-↓ᵘ {n₁ = N.1+ _} {n₂ = 0} ⊢Γ =
    supᵘₗ-zeroʳ (⊢↓ᵘ ⊢Γ)
  supᵘₗ-↓ᵘ {n₁ = N.1+ n₁} {n₂ = N.1+ n₂} ⊢Γ =
    (↓ᵘ N.1+ n₁) supᵘₗ (↓ᵘ N.1+ n₂)  ≡⟨ supᵘₗ-sucᵘ (⊢↓ᵘ ⊢Γ) (⊢↓ᵘ ⊢Γ) ⟩⊢
    sucᵘ ((↓ᵘ n₁) supᵘₗ (↓ᵘ n₂))     ≡⟨ sucᵘ-cong-⊢≡∷L (supᵘₗ-↓ᵘ ⊢Γ) ⟩⊢∎
    ↓ᵘ (N.1+ n₁ N.⊔ N.1+ n₂)         ∎

opaque
  unfolding inline _supᵘₗ_

  -- Inlining commutes with _supᵘₗ_ for well-formed levels.

  inline-supᵘₗ :
    Γ ⊢ l₁ ∷Level → Γ ⊢ l₂ ∷Level →
    inline ξ (l₁ supᵘₗ l₂) PE.≡ inline ξ l₁ supᵘₗ inline ξ l₂
  inline-supᵘₗ ⊢l₁ ⊢l₂ with level-support in eq
  … | level-type _ =
    PE.refl
  … | only-literals =
    case ⊢l₁ of λ where
      (term ok _) →
        ⊥-elim $ Level-allowed⇔≢ .proj₁ ok eq
      (literal _ _ l₁-lit) → case ⊢l₂ of λ where
        (term ok _) →
          ⊥-elim $ Level-allowed⇔≢ .proj₁ ok eq
        (literal _ _ l₂-lit) →
          inline-supᵘₗ′ l₁-lit l₂-lit

------------------------------------------------------------------------
-- Some lemmas related to _⊢_≤ₗ_∷Level

opaque

  -- A well-formedness lemma.

  wf-⊢≤ₗ∷L : Γ ⊢ l₁ ≤ₗ l₂ ∷Level → Γ ⊢ l₁ ∷Level × Γ ⊢ l₂ ∷Level
  wf-⊢≤ₗ∷L l₁≤l₂ =
    let ⊢⊔ , _ = wf-⊢≡∷L l₁≤l₂ in
    inversion-supᵘₗ ⊢⊔

opaque

  -- Reflexivity.

  refl-⊢≤ₗ∷L :
    Γ ⊢ l ∷Level →
    Γ ⊢ l ≤ₗ l ∷Level
  refl-⊢≤ₗ∷L = supᵘₗ-idem

opaque

  -- Reflexivity.

  reflexive-⊢≤ₗ∷L :
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level
  reflexive-⊢≤ₗ∷L {l₁} {l₂} l₁≡l₂ =
    let _ , ⊢l₂ = wf-⊢≡∷L l₁≡l₂ in
    l₁ supᵘₗ l₂  ≡⟨ supᵘₗ-cong l₁≡l₂ (refl-⊢≡∷L ⊢l₂) ⟩⊢
    l₂ supᵘₗ l₂  ≡⟨ supᵘₗ-idem ⊢l₂ ⟩⊢∎
    l₂           ∎

opaque

  -- Transitivity.

  trans-⊢≤ₗ∷L :
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ l₂ ≤ₗ l₃ ∷Level →
    Γ ⊢ l₁ ≤ₗ l₃ ∷Level
  trans-⊢≤ₗ∷L {l₁} {l₂} {l₃} l₁≤l₂ l₂≤l₃ =
    let ⊢l₁ , ⊢l₂ = wf-⊢≤ₗ∷L l₁≤l₂
        _   , ⊢l₃ = wf-⊢≤ₗ∷L l₂≤l₃
    in
    l₁ supᵘₗ l₃             ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁) (sym-⊢≡∷L l₂≤l₃) ⟩⊢
    l₁ supᵘₗ l₂ supᵘₗ l₃    ≡˘⟨ supᵘₗ-assoc ⊢l₁ ⊢l₂ ⊢l₃ ⟩⊢
    (l₁ supᵘₗ l₂) supᵘₗ l₃  ≡⟨ supᵘₗ-cong l₁≤l₂ (refl-⊢≡∷L ⊢l₃) ⟩⊢
    l₂ supᵘₗ l₃             ≡⟨ l₂≤l₃ ⟩⊢∎
    l₃                      ∎

opaque

  -- Antisymmetry.

  antisym-⊢≤ₗ∷L :
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ l₂ ≤ₗ l₁ ∷Level →
    Γ ⊢ l₁ ≡ l₂ ∷Level
  antisym-⊢≤ₗ∷L {l₁} {l₂} l₁≤l₂ l₂≤l₁ =
    let ⊢l₁ , ⊢l₂ = wf-⊢≤ₗ∷L l₁≤l₂ in
    l₁           ≡˘⟨ l₂≤l₁ ⟩⊢
    l₂ supᵘₗ l₁  ≡⟨ supᵘₗ-comm ⊢l₂ ⊢l₁ ⟩⊢
    l₁ supᵘₗ l₂  ≡⟨ l₁≤l₂ ⟩⊢∎
    l₂           ∎

opaque

  -- The function sucᵘ is monotone.

  sucᵘ-mono :
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ sucᵘ l₁ ≤ₗ sucᵘ l₂ ∷Level
  sucᵘ-mono {l₁} {l₂} l₁≤l₂ =
    let ⊢l₁ , ⊢l₂ = wf-⊢≤ₗ∷L l₁≤l₂ in
    sucᵘ l₁ supᵘₗ sucᵘ l₂  ≡⟨ supᵘₗ-sucᵘ ⊢l₁ ⊢l₂ ⟩⊢
    sucᵘ (l₁ supᵘₗ l₂)     ≡⟨ sucᵘ-cong-⊢≡∷L l₁≤l₂ ⟩⊢∎
    sucᵘ l₂                ∎

opaque

  -- The function _supᵘₗ_ is monotone.

  supᵘₗ-mono :
    Γ ⊢ l₁₁ ≤ₗ l₂₁ ∷Level →
    Γ ⊢ l₁₂ ≤ₗ l₂₂ ∷Level →
    Γ ⊢ l₁₁ supᵘₗ l₁₂ ≤ₗ l₂₁ supᵘₗ l₂₂ ∷Level
  supᵘₗ-mono {l₁₁} {l₂₁} {l₁₂} {l₂₂} l₁₁≤l₂₁ l₁₂≤l₂₂ =
    let ⊢l₁₁ , ⊢l₂₁ = wf-⊢≤ₗ∷L l₁₁≤l₂₁
        ⊢l₁₂ , ⊢l₂₂ = wf-⊢≤ₗ∷L l₁₂≤l₂₂
    in
    (l₁₁ supᵘₗ l₁₂) supᵘₗ (l₂₁ supᵘₗ l₂₂)  ≡⟨ supᵘₗ-assoc ⊢l₁₁ ⊢l₁₂ (⊢supᵘₗ ⊢l₂₁ ⊢l₂₂) ⟩⊢
    l₁₁ supᵘₗ (l₁₂ supᵘₗ (l₂₁ supᵘₗ l₂₂))  ≡˘⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁₁) $
                                               supᵘₗ-assoc ⊢l₁₂ ⊢l₂₁ ⊢l₂₂ ⟩⊢
    l₁₁ supᵘₗ ((l₁₂ supᵘₗ l₂₁) supᵘₗ l₂₂)  ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁₁) $
                                              supᵘₗ-cong (supᵘₗ-comm ⊢l₁₂ ⊢l₂₁) (refl-⊢≡∷L ⊢l₂₂) ⟩⊢
    l₁₁ supᵘₗ ((l₂₁ supᵘₗ l₁₂) supᵘₗ l₂₂)  ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁₁) $
                                              supᵘₗ-assoc ⊢l₂₁ ⊢l₁₂ ⊢l₂₂ ⟩⊢
    l₁₁ supᵘₗ (l₂₁ supᵘₗ (l₁₂ supᵘₗ l₂₂))  ≡˘⟨ supᵘₗ-assoc ⊢l₁₁ ⊢l₂₁ (⊢supᵘₗ ⊢l₁₂ ⊢l₂₂) ⟩⊢
    (l₁₁ supᵘₗ l₂₁) supᵘₗ (l₁₂ supᵘₗ l₂₂)  ≡⟨ supᵘₗ-cong l₁₁≤l₂₁ l₁₂≤l₂₂ ⟩⊢∎
    l₂₁ supᵘₗ l₂₂                          ∎

opaque
  unfolding size-of-Level

  -- A variant of supᵘ-sub.

  supᵘₗ-sub :
    Γ ⊢ l ∷Level →
    Γ ⊢ l ≤ₗ sucᵘ l ∷Level
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

opaque

  -- If l₁ is bounded by l₂, then l₁ is also bounded by sucᵘ l₂.

  step-⊢≤ₗ∷L :
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ l₁ ≤ₗ sucᵘ l₂ ∷Level
  step-⊢≤ₗ∷L {l₁} {l₂} l₁≤l₂ =
    let ⊢l₁ , ⊢l₂ = wf-⊢≤ₗ∷L l₁≤l₂ in
    l₁ supᵘₗ sucᵘ l₂                  ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁) $
                                         sucᵘ-cong-⊢≡∷L (sym-⊢≡∷L l₁≤l₂) ⟩⊢
    l₁ supᵘₗ sucᵘ (l₁ supᵘₗ l₂)       ≡˘⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁) $
                                          supᵘₗ-sucᵘ ⊢l₁ ⊢l₂ ⟩⊢
    l₁ supᵘₗ (sucᵘ l₁ supᵘₗ sucᵘ l₂)  ≡˘⟨ supᵘₗ-assoc ⊢l₁ (⊢sucᵘ ⊢l₁) (⊢sucᵘ ⊢l₂) ⟩⊢
    (l₁ supᵘₗ sucᵘ l₁) supᵘₗ sucᵘ l₂  ≡⟨ supᵘₗ-cong (supᵘₗ-sub ⊢l₁) (refl-⊢≡∷L (⊢sucᵘ ⊢l₂)) ⟩⊢
    sucᵘ l₁ supᵘₗ sucᵘ l₂             ≡⟨ supᵘₗ-sucᵘ ⊢l₁ ⊢l₂ ⟩⊢
    sucᵘ (l₁ supᵘₗ l₂)                ≡⟨ sucᵘ-cong-⊢≡∷L l₁≤l₂ ⟩⊢∎
    sucᵘ l₂                           ∎

opaque

  -- The function sucᵘᵏ is monotone.

  sucᵘᵏ-mono :
    n₁ N.≤ n₂ →
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ sucᵘᵏ n₁ l₁ ≤ₗ sucᵘᵏ n₂ l₂ ∷Level
  sucᵘᵏ-mono (N.z≤n {n = 0}) l₁≤l₂ =
    l₁≤l₂
  sucᵘᵏ-mono (N.z≤n {n = N.1+ _}) l₁≤l₂ =
    step-⊢≤ₗ∷L (sucᵘᵏ-mono N.z≤n l₁≤l₂)
  sucᵘᵏ-mono (N.s≤s n₁≤n₂) l₁≤l₂ =
    sucᵘ-mono (sucᵘᵏ-mono n₁≤n₂ l₁≤l₂)

------------------------------------------------------------------------
-- Lemmas related to _⊢_≤_∷Level

opaque

  -- A well-formedness lemma.

  wf-⊢≤ : Γ ⊢ l₁ ≤ l₂ ∷Level → Γ ⊢ l₁ ∷ Level × Γ ⊢ l₂ ∷ Level
  wf-⊢≤ l₁≤l₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≤l₂ .proj₁) in
    Σ.map (⊢∷Level→⊢∷Level ok) (⊢∷Level→⊢∷Level ok)
      (wf-⊢≤ₗ∷L (term-⊢≤∷L l₁≤l₂))

opaque

  -- Reflexivity.

  ⊢≤-refl : Γ ⊢ l₁ ≡ l₂ ∷ Level → Γ ⊢ l₁ ≤ l₂ ∷Level
  ⊢≤-refl l₁≡l₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≡l₂ .proj₁) in
    ⊢≤ₗ∷Level→⊢≤∷Level ok (reflexive-⊢≤ₗ∷L (term-⊢≡∷ l₁≡l₂))

opaque

  -- Transitivity.

  ⊢≤-trans :
    Γ ⊢ l₁ ≤ l₂ ∷Level → Γ ⊢ l₂ ≤ l₃ ∷Level → Γ ⊢ l₁ ≤ l₃ ∷Level
  ⊢≤-trans l₁≤l₂ l₂≤l₃ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≤l₂ .proj₁) in
    ⊢≤ₗ∷Level→⊢≤∷Level ok
      (trans-⊢≤ₗ∷L (term-⊢≤∷L l₁≤l₂) (term-⊢≤∷L l₂≤l₃))

opaque

  -- Antisymmetry.

  ⊢≤-antisymmetric :
    Γ ⊢ l₁ ≤ l₂ ∷Level → Γ ⊢ l₂ ≤ l₁ ∷Level → Γ ⊢ l₁ ≡ l₂ ∷ Level
  ⊢≤-antisymmetric l₁≤l₂ l₂≤l₁ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≤l₂ .proj₁) in
    ⊢≡∷Level→⊢≡∷Level ok
      (antisym-⊢≤ₗ∷L (term-⊢≤∷L l₁≤l₂) (term-⊢≤∷L l₂≤l₁))

opaque

  -- A variant of supᵘ-sub.
  --
  -- See also Definition.Typed.EqualityRelation.≅ₜ-supᵘ-sub′.

  supᵘ-sub′ : Γ ⊢ l₁ ≤ l₂ ∷Level → Γ ⊢ l₁ ≤ sucᵘ l₂ ∷Level
  supᵘ-sub′ l₁≤l₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≤l₂ .proj₁) in
    ⊢≤ₗ∷Level→⊢≤∷Level ok (step-⊢≤ₗ∷L (term-⊢≤∷L l₁≤l₂))

opaque

  -- A variant of supᵘ-sub′.

  supᵘ-subᵏ : Γ ⊢ l₁ ≤ l₂ ∷Level → Γ ⊢ l₁ ≤ sucᵘᵏ n l₂ ∷Level
  supᵘ-subᵏ {n = 0}      = idᶠ
  supᵘ-subᵏ {n = N.1+ _} = supᵘ-sub′ ∘→ supᵘ-subᵏ

opaque

  -- The function sucᵘ is monotone.

  ≤-sucᵘ :
    Γ ⊢ l₁ ≤ l₂ ∷Level →
    Γ ⊢ sucᵘ l₁ ≤ sucᵘ l₂ ∷Level
  ≤-sucᵘ l₁≤l₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≤l₂ .proj₁) in
    ⊢≤ₗ∷Level→⊢≤∷Level ok (sucᵘ-mono (term-⊢≤∷L l₁≤l₂))

opaque

  -- The function sucᵘᵏ is monotone.

  ≤-sucᵘᵏ :
    n₁ N.≤ n₂ →
    Γ ⊢ l₁ ≤ l₂ ∷Level →
    Γ ⊢ sucᵘᵏ n₁ l₁ ≤ sucᵘᵏ n₂ l₂ ∷Level
  ≤-sucᵘᵏ n₁≤n₂ l₁≤l₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ l₁≤l₂ .proj₁) in
    ⊢≤ₗ∷Level→⊢≤∷Level ok (sucᵘᵏ-mono n₁≤n₂ (term-⊢≤∷L l₁≤l₂))
