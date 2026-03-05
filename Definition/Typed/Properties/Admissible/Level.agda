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
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Reasoning.Level R
open import Definition.Typed.Syntactic R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Allowed-literal R
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
  m n n₁ n₂                      : Nat
  X                              : Set _
  ξ                              : DExt _ _ _
  Γ                              : Cons _ _
  A B B₁ B₂ t t₁ t₂ t₃ u u₁ u₂ v : Term _
  l l₁ l₁₁ l₁₂ l₂ l₂′ l₂₁ l₂₂ l₃ : Lvl _

------------------------------------------------------------------------
-- Lemmas related to Allowed-literal

opaque

  -- If A reduces to Level and level t is an allowed literal, then
  -- anything can be derived.

  ⇒*Level→Allowed-literal→ :
    Γ ⊢ A ⇒* Level → Allowed-literal (level t) → X
  ⇒*Level→Allowed-literal→ ⇒*Level ok =
    let okᴸ = inversion-Level-⊢ (wf-⊢≡ (subset* ⇒*Level) .proj₂) in
    Level-allowed→Allowed-literal→ okᴸ ok

opaque

  -- If something reduces at type Level and level t is an allowed
  -- literal, then anything can be derived.

  ⇒*∷Level→Allowed-literal→ :
    Γ ⊢ t ⇒* u ∷ Level → Allowed-literal (level v) → X
  ⇒*∷Level→Allowed-literal→ ⇒*∷L ok =
    let okᴸ = inversion-Level-⊢ (wf-⊢≡∷ (subset*Term ⇒*∷L) .proj₁) in
    Level-allowed→Allowed-literal→ okᴸ ok

------------------------------------------------------------------------
-- Some lemmas related to U and/or Id

opaque

  -- If Level is not small, then Level is not in any universe.

  ¬Level-is-small→¬Level∷U :
    ¬ Level-is-small → ¬ Γ ⊢ Level ∷ U l
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

  term-⊢∷ : Γ ⊢ t ∷ Level → Γ ⊢ level t ∷Level
  term-⊢∷ ⊢t = term (inversion-Level-⊢ (wf-⊢∷ ⊢t)) ⊢t

opaque

  -- A variant of _⊢_≡_∷Level.term.

  term-⊢≡∷ : Γ ⊢ t₁ ≡ t₂ ∷ Level → Γ ⊢ level t₁ ≡ level t₂ ∷Level
  term-⊢≡∷ t₁≡t₂ = term (inversion-Level-⊢ (wf-⊢≡∷ t₁≡t₂ .proj₁)) t₁≡t₂

opaque
  unfolding _⊢_≤ₗ_∷Level

  -- If Γ ⊢ t₁ ≤ t₂ ∷Level holds, then Γ ⊢ level t₁ ≤ₗ level t₂ ∷Level
  -- also holds.

  term-⊢≤∷L : Γ ⊢ t₁ ≤ t₂ ∷Level → Γ ⊢ level t₁ ≤ₗ level t₂ ∷Level
  term-⊢≤∷L l₁≤l₂ =
    let ⊢Level , ⊢sup , _ = wf-⊢≡∷ l₁≤l₂
        ok                = inversion-Level-⊢ ⊢Level
        ⊢t₁ , _           = inversion-supᵘ ⊢sup
    in
    term-⊢∷ ⊢t₁ ,
    PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym (supᵘₗ≡supᵘ ok))
      (term-⊢≡∷ l₁≤l₂)

------------------------------------------------------------------------
-- Some lemmas related to 1ᵘ+

opaque

  -- A variant of sucᵘ-cong.

  1ᵘ+-cong :
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ 1ᵘ+ l₁ ≡ 1ᵘ+ l₂ ∷Level
  1ᵘ+-cong (term ok l₁≡l₂) =
    term ok (sucᵘ-cong l₁≡l₂)
  1ᵘ+-cong (literal ok ⊢Γ) =
    literal (Allowed-literal-1ᵘ+-⇔ .proj₂ ok) ⊢Γ

opaque

  -- A typing rule for 1ᵘ+ⁿ.

  ⊢1ᵘ+ⁿ : ∀ n → Γ ⊢ l ∷Level → Γ ⊢ 1ᵘ+ⁿ n l ∷Level
  ⊢1ᵘ+ⁿ 0        ⊢t = ⊢t
  ⊢1ᵘ+ⁿ (N.1+ n) ⊢t = ⊢1ᵘ+ (⊢1ᵘ+ⁿ n ⊢t)

opaque

  -- A variant of ⊢1ᵘ+ⁿ.

  ⊢1ᵘ+ⁿ-level : ∀ n → Γ ⊢ level t ∷Level → Γ ⊢ level (1ᵘ+ⁿ n t) ∷Level
  ⊢1ᵘ+ⁿ-level n ⊢t =
    PE.subst (_⊢_∷Level _) (1ᵘ+ⁿ-level≡ n) $
    ⊢1ᵘ+ⁿ n ⊢t

opaque
  unfolding ↓ᵘ_

  -- A typing rule for ↓ᵘ_.

  ⊢↓ᵘ : ⊢ Γ → Γ ⊢ level (↓ᵘ n) ∷Level
  ⊢↓ᵘ {n} ⊢Γ = ⊢1ᵘ+ⁿ-level n (⊢zeroᵘ ⊢Γ)

------------------------------------------------------------------------
-- Some lemmas related to _supᵘ_

opaque

  -- The level zeroᵘ is a right unit for _supᵘ_.

  supᵘ-zeroʳⱼ :
    Γ ⊢ t ∷ Level →
    Γ ⊢ t supᵘ zeroᵘ ≡ t ∷ Level
  supᵘ-zeroʳⱼ ⊢t =
    LP.supᵘ-zeroʳⱼ (inversion-Level-⊢ (wf-⊢∷ ⊢t)) ⊢t

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
  unfolding size-of-Level _supᵘₗ_

  -- A variant of _⊢_≡_∷_.supᵘ-zeroˡ.

  supᵘₗ-zeroˡ :
    Γ ⊢ l ∷Level →
    Γ ⊢ zeroᵘₗ supᵘₗ l ≡ l ∷Level
  supᵘₗ-zeroˡ (term ok ⊢l) =
    PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-zeroˡ ⊢l)
  supᵘₗ-zeroˡ (literal {l = ωᵘ+ _} ok ⊢Γ) =
    literal ok ⊢Γ
  supᵘₗ-zeroˡ (literal {l = level t} ok ⊢Γ) =
    let t-lit , not-ok = Allowed-literal-level-⇔ .proj₁ ok in
    PE.subst (flip (_⊢_≡_∷Level _) _)
      (level t                           ≡˘⟨ PE.cong level ↓ᵘ-size-of-Level ⟩
       level (↓ᵘ (size-of-Level t-lit))  ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok zeroᵘ t-lit ⟩
       zeroᵘₗ supᵘₗ level t              ∎) $
    literal ok ⊢Γ

opaque
  unfolding size-of-Level

  -- A variant of supᵘ-zeroʳⱼ.

  supᵘₗ-zeroʳ :
    Γ ⊢ l ∷Level →
    Γ ⊢ l supᵘₗ zeroᵘₗ ≡ l ∷Level
  supᵘₗ-zeroʳ {l} ⊢l =
    l supᵘₗ zeroᵘₗ  ≡⟨ supᵘₗ-comm ⊢l (⊢zeroᵘ (wfLevel ⊢l)) ⟩⊢
    zeroᵘₗ supᵘₗ l  ≡⟨ supᵘₗ-zeroˡ ⊢l ⟩⊢∎
    l               ∎

opaque
  unfolding size-of-Level ↓ᵘ_ _supᵘₗ_

  -- A variant of _⊢_≡_∷_.supᵘ-sucᵘ.

  supᵘₗ-1ᵘ+ :
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ 1ᵘ+ l₁ supᵘₗ 1ᵘ+ l₂ ≡ 1ᵘ+ (l₁ supᵘₗ l₂) ∷Level
  supᵘₗ-1ᵘ+ (term ok ⊢l₁) (term _ ⊢l₂) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡supᵘ ok)
      (PE.cong 1ᵘ+ $ PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-sucᵘ ⊢l₁ ⊢l₂)
  supᵘₗ-1ᵘ+ (term ok₁ _) (literal ok₂ ⊢Γ)
    with Allowed-literal→Infinite ok₁ ok₂
  … | ωᵘ+ =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok₂) ⊢Γ
  supᵘₗ-1ᵘ+ (literal ok₁ ⊢Γ) (term ok₂ _)
    with Allowed-literal→Infinite ok₂ ok₁
  … | ωᵘ+ =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok₁) ⊢Γ
  supᵘₗ-1ᵘ+ (literal {l = ωᵘ+ _} ok ⊢Γ) (literal {l = ωᵘ+ _} _ _) =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-1ᵘ+ (literal {l = ωᵘ+ _} ok ⊢Γ) (literal {l = level _} _ _) =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-1ᵘ+ (literal {l = level _} _ ⊢Γ) (literal {l = ωᵘ+ _} ok _) =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-1ᵘ+
    (literal {l = level _} ok₁ ⊢Γ) (literal {l = level _} ok₂ _) =
    let t₁-lit , not-ok = Allowed-literal-level-⇔ .proj₁ ok₁
        t₂-lit , _      = Allowed-literal-level-⇔ .proj₁ ok₂
    in
    PE.subst₂ (_⊢_≡_∷Level _)
      (PE.sym $ supᵘₗ≡↓ᵘ⊔ not-ok (sucᵘ t₁-lit) (sucᵘ t₂-lit))
      (PE.cong 1ᵘ+ $ PE.sym $ supᵘₗ≡↓ᵘ⊔ not-ok t₁-lit t₂-lit) $
    literal
      (Allowed-literal-level-⇔ .proj₂
         (Level-literal-↓ᵘ {m = N.1+ (size-of-Level t₁-lit N.⊔ _)} ,
          not-ok))
      ⊢Γ

opaque
  unfolding _supᵘₗ_

  -- A variant of supᵘ-assoc.

  supᵘₗ-assoc :
    {l₁ l₂ l₃ : Lvl n} →
    Γ ⊢ l₁ ∷Level →
    Γ ⊢ l₂ ∷Level →
    Γ ⊢ l₃ ∷Level →
    Γ ⊢ (l₁ supᵘₗ l₂) supᵘₗ l₃ ≡ l₁ supᵘₗ (l₂ supᵘₗ l₃) ∷Level
  supᵘₗ-assoc
    (term {t = t₁} ok ⊢t₁) (term {t = t₂} _ ⊢t₂) (term {t = t₃} _ ⊢t₃) =
    PE.subst₂ (_⊢_≡_∷Level _)
      (level ((t₁ supᵘ t₂) supᵘ t₃)              ≡˘⟨ supᵘₗ≡supᵘ ok ⟩
       level (t₁ supᵘ t₂) supᵘₗ level t₃         ≡˘⟨ PE.cong (_supᵘₗ level t₃) (supᵘₗ≡supᵘ ok) ⟩
       (level t₁ supᵘₗ level t₂) supᵘₗ level t₃  ∎)
      (level (t₁ supᵘ (t₂ supᵘ t₃))              ≡˘⟨ supᵘₗ≡supᵘ ok ⟩
       level t₁ supᵘₗ level (t₂ supᵘ t₃)         ≡˘⟨ PE.cong (level t₁ supᵘₗ_) (supᵘₗ≡supᵘ ok) ⟩
       level t₁ supᵘₗ (level t₂ supᵘₗ level t₃)  ∎) $
    term ok (supᵘ-assoc ⊢t₁ ⊢t₂ ⊢t₃)
  supᵘₗ-assoc (term ok₁ _) (term _ _) (literal ok₃ ⊢Γ)
    with Allowed-literal→Infinite ok₁ ok₃
  … | ωᵘ+ =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok₃) ⊢Γ
  supᵘₗ-assoc (term ok₁ _) (literal ok₂ ⊢Γ) (term _ _)
    with Allowed-literal→Infinite ok₁ ok₂
  … | ωᵘ+ =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok₂) ⊢Γ
  supᵘₗ-assoc (term ok₁ _) (literal ok₂ ⊢Γ) (literal ok₃ _)
    with Allowed-literal→Infinite ok₁ ok₂
       | Allowed-literal→Infinite ok₁ ok₃
  … | ωᵘ+ | ωᵘ+ =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok₂) ⊢Γ
  supᵘₗ-assoc (literal ok₁ ⊢Γ) (term ok₂ _) (term _ _)
    with Allowed-literal→Infinite ok₂ ok₁
  … | ωᵘ+ =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok₁) ⊢Γ
  supᵘₗ-assoc (literal ok₁ ⊢Γ) (term ok₂ _) (literal ok₃ _)
    with Allowed-literal→Infinite ok₂ ok₁
       | Allowed-literal→Infinite ok₂ ok₃
  … | ωᵘ+ | ωᵘ+ =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok₁) ⊢Γ
  supᵘₗ-assoc (literal ok₁ ⊢Γ) (literal ok₂ _) (term ok₃ _)
    with Allowed-literal→Infinite ok₃ ok₁
       | Allowed-literal→Infinite ok₃ ok₂
  … | ωᵘ+ | ωᵘ+ =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok₁) ⊢Γ
  supᵘₗ-assoc
    (literal {l = ωᵘ+ m} ok ⊢Γ) (literal {l = ωᵘ+ _} _ _)
    (literal {l = ωᵘ+ _} _ _) =
    PE.subst (_⊢_≡_∷Level _ _) (PE.cong ωᵘ+ (N.⊔-assoc m _ _)) $
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-assoc
    (literal {l = ωᵘ+ _} ok ⊢Γ) (literal {l = ωᵘ+ _} _ _)
    (literal {l = level _} _ _) =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-assoc
    (literal {l = ωᵘ+ _} ok ⊢Γ) (literal {l = level _} _ _)
    (literal {l = ωᵘ+ _} _ _) =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-assoc
    (literal {l = ωᵘ+ _} ok ⊢Γ) (literal {l = level _} _ _)
    (literal {l = level _} _ _) =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-assoc
    (literal {l = level _} _ ⊢Γ) (literal {l = ωᵘ+ _} ok _)
    (literal {l = ωᵘ+ _} _ _) =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-assoc
    (literal {l = level _} _ ⊢Γ) (literal {l = ωᵘ+ _} ok _)
    (literal {l = level _} _ _) =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-assoc
    (literal {l = level _} _ ⊢Γ) (literal {l = level _} _ _)
    (literal {l = ωᵘ+ _} ok _) =
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-assoc
    {n} (literal {l = level t₁} ok₁ ⊢Γ) (literal {l = level t₂} ok₂ _)
    (literal {l = level t₃} ok₃ _) =
    let t₁-lit , not-ok = Allowed-literal-level-⇔ .proj₁ ok₁
        t₂-lit , _      = Allowed-literal-level-⇔ .proj₁ ok₂
        t₃-lit , _      = Allowed-literal-level-⇔ .proj₁ ok₃
    in
    PE.subst₂ (_⊢_≡_∷Level _)
      (level (↓ᵘ (size-of-Level t₁-lit N.⊔
                  size-of-Level {n = n} Level-literal-↓ᵘ))               ≡⟨ PE.cong (level ∘→ ↓ᵘ_ ∘→ (size-of-Level _ N.⊔_))
                                                                            size-of-Level-Level-literal-↓ᵘ ⟩
       level (↓ᵘ (size-of-Level t₁-lit N.⊔
                  (size-of-Level t₂-lit N.⊔ size-of-Level t₃-lit)))      ≡˘⟨ PE.cong (level ∘→ ↓ᵘ_) $ N.⊔-assoc (size-of-Level _) _ _ ⟩

       level (↓ᵘ ((size-of-Level t₁-lit N.⊔ size-of-Level t₂-lit) N.⊔
                  size-of-Level t₃-lit))                                 ≡˘⟨ PE.cong (level ∘→ ↓ᵘ_ ∘→ (N._⊔ size-of-Level _))
                                                                             size-of-Level-Level-literal-↓ᵘ ⟩
       level
         (↓ᵘ (size-of-Level Level-literal-↓ᵘ N.⊔ size-of-Level t₃-lit))  ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok Level-literal-↓ᵘ t₃-lit ⟩

       level (↓ᵘ (size-of-Level t₁-lit N.⊔ size-of-Level t₂-lit)) supᵘₗ
       level t₃                                                          ≡˘⟨ PE.cong (_supᵘₗ level t₃) $ supᵘₗ≡↓ᵘ⊔ not-ok t₁-lit t₂-lit ⟩

       (level t₁ supᵘₗ level t₂) supᵘₗ level t₃                          ∎)
      (level (↓ᵘ (size-of-Level t₁-lit N.⊔
                  size-of-Level Level-literal-↓ᵘ))                 ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok t₁-lit Level-literal-↓ᵘ ⟩

       level t₁ supᵘₗ
       level (↓ᵘ (size-of-Level t₂-lit N.⊔ size-of-Level t₃-lit))  ≡˘⟨ PE.cong (level t₁ supᵘₗ_) $ supᵘₗ≡↓ᵘ⊔ not-ok t₂-lit t₃-lit ⟩

       level t₁ supᵘₗ (level t₂ supᵘₗ level t₃)                    ∎) $
    literal (Allowed-literal-level-⇔ .proj₂ (Level-literal-↓ᵘ , not-ok))
      ⊢Γ

opaque
  unfolding _supᵘₗ_

  -- A variant of supᵘ-idem.

  supᵘₗ-idem :
    Γ ⊢ l ∷Level →
    Γ ⊢ l supᵘₗ l ≡ l ∷Level
  supᵘₗ-idem (term ok ⊢l) =
    PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-idem ⊢l)
  supᵘₗ-idem (literal {l = ωᵘ+ _} ok ⊢Γ) =
    PE.subst (_⊢_≡_∷Level _ _)
      (PE.cong ωᵘ+ (N.⊔-idem _)) $
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-idem (literal {l = level t} ok ⊢Γ) =
    let t-lit , not-ok = Allowed-literal-level-⇔ .proj₁ ok in
    PE.subst (flip (_⊢_≡_∷Level _) _)
      (level t                                                   ≡˘⟨ PE.cong level ↓ᵘ-size-of-Level ⟩
       level (↓ᵘ (size-of-Level t-lit))                          ≡˘⟨ PE.cong (level ∘→ ↓ᵘ_) $ N.⊔-idem _ ⟩
       level (↓ᵘ (size-of-Level t-lit N.⊔ size-of-Level t-lit))  ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok t-lit t-lit ⟩
       level t supᵘₗ level t                                     ∎) $
    literal ok ⊢Γ

opaque
  unfolding ↓ᵘ_

  -- A variant of supᵘₗ-1ᵘ+.

  supᵘₗ-↓ᵘ :
    ⊢ Γ →
    Γ ⊢ level (↓ᵘ n₁) supᵘₗ level (↓ᵘ n₂) ≡ level (↓ᵘ (n₁ N.⊔ n₂))
      ∷Level
  supᵘₗ-↓ᵘ {n₁ = 0} {n₂} ⊢Γ =
    supᵘₗ-zeroˡ (⊢↓ᵘ {n = n₂} ⊢Γ)
  supᵘₗ-↓ᵘ {n₁ = N.1+ n₁} {n₂ = 0} ⊢Γ =
    supᵘₗ-zeroʳ (⊢↓ᵘ {n = N.1+ n₁} ⊢Γ)
  supᵘₗ-↓ᵘ {n₁ = N.1+ n₁} {n₂ = N.1+ n₂} ⊢Γ =
    level (↓ᵘ (N.1+ n₁)) supᵘₗ level (↓ᵘ (N.1+ n₂))  ≡⟨ supᵘₗ-1ᵘ+ (⊢↓ᵘ {n = n₁} ⊢Γ) (⊢↓ᵘ {n = n₂} ⊢Γ) ⟩⊢
    1ᵘ+ (level (↓ᵘ n₁) supᵘₗ level (↓ᵘ n₂))          ≡⟨ 1ᵘ+-cong (supᵘₗ-↓ᵘ {n₁ = n₁} ⊢Γ) ⟩⊢∎
    level (sucᵘ (↓ᵘ (n₁ N.⊔ n₂)))                    ∎

opaque
  unfolding inline _supᵘₗ_

  -- Inlining commutes with _supᵘₗ_ for well-formed levels.

  inline-supᵘₗ :
    Γ ⊢ l₁ ∷Level → Γ ⊢ l₂ ∷Level →
    inline ξ (l₁ supᵘₗ l₂) PE.≡ inline ξ l₁ supᵘₗ inline ξ l₂
  inline-supᵘₗ {ξ} (term {t = t₁} ok ⊢t₁) (term {t = t₂} _ ⊢t₂) =
    inline ξ (level t₁ supᵘₗ level t₂)             ≡⟨ PE.cong (inline _) (supᵘₗ≡supᵘ ok) ⟩
    inline ξ (level (t₁ supᵘ t₂))                  ≡⟨⟩
    level (inline ξ t₁ supᵘ inline ξ t₂)           ≡˘⟨ supᵘₗ≡supᵘ ok ⟩
    level (inline ξ t₁) supᵘₗ level (inline ξ t₂)  ≡⟨⟩
    inline ξ (level t₁) supᵘₗ inline ξ (level t₂)  ∎
  inline-supᵘₗ (term ok₁ _) (literal ok₂ _)
    with Allowed-literal→Infinite ok₁ ok₂
  … | ωᵘ+ =
    PE.refl
  inline-supᵘₗ (literal ok₁ _) (term ok₂ _)
    with Allowed-literal→Infinite ok₂ ok₁
  … | ωᵘ+ =
    PE.refl
  inline-supᵘₗ (literal {l = ωᵘ+ _} _ _) (literal {l = ωᵘ+ _} _ _) =
    PE.refl
  inline-supᵘₗ (literal {l = ωᵘ+ _} _ _) (literal {l = level _} _ _) =
    PE.refl
  inline-supᵘₗ (literal {l = level _} _ _) (literal {l = ωᵘ+ _} _ _) =
    PE.refl
  inline-supᵘₗ
    {ξ} (literal {l = level t₁} ok₁ _) (literal {l = level t₂} ok₂ _) =
    let t₁-lit , not-ok = Allowed-literal-level-⇔ .proj₁ ok₁
        t₂-lit , _      = Allowed-literal-level-⇔ .proj₁ ok₂
    in
    inline ξ (level t₁ supᵘₗ level t₂)             ≡⟨ PE.cong (inline _) (supᵘₗ≡supᵘₗ′ not-ok) ⟩
    inline ξ (level (t₁ supᵘₗ′ t₂))                ≡⟨⟩
    level (inline ξ (t₁ supᵘₗ′ t₂))                ≡⟨ PE.cong level (inline-supᵘₗ′ t₁-lit t₂-lit) ⟩
    level (inline ξ t₁ supᵘₗ′ inline ξ t₂)         ≡˘⟨ supᵘₗ≡supᵘₗ′ not-ok ⟩
    level (inline ξ t₁) supᵘₗ level (inline ξ t₂)  ≡⟨⟩
    inline ξ (level t₁) supᵘₗ inline ξ (level t₂)  ∎

------------------------------------------------------------------------
-- Some lemmas related to _⊢_≤ₗ_∷Level

opaque
  unfolding _⊢_≤ₗ_∷Level

  -- If l₁ is a well-formed level and l₁ supᵘₗ l₂ is judgementally
  -- equal to l₂, then Γ ⊢ l₁ ≤ₗ l₂ ∷Level holds.

  ⊢≡∷L→⊢≤ₗ∷L :
    Γ ⊢ l₁ ∷Level → Γ ⊢ l₁ supᵘₗ l₂ ≡ l₂ ∷Level →
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level
  ⊢≡∷L→⊢≤ₗ∷L = _,_

opaque
  unfolding _⊢_≤ₗ_∷Level

  -- If Γ ⊢ l₁ ≤ₗ l₂ ∷Level, then l₁ supᵘₗ l₂ is judgementally equal
  -- to l₂.

  ⊢≤ₗ∷L→⊢≡∷L : Γ ⊢ l₁ ≤ₗ l₂ ∷Level → Γ ⊢ l₁ supᵘₗ l₂ ≡ l₂ ∷Level
  ⊢≤ₗ∷L→⊢≡∷L = proj₂

opaque
  unfolding _⊢_≤ₗ_∷Level

  -- A well-formedness lemma.

  wf-⊢≤ₗ∷L : Γ ⊢ l₁ ≤ₗ l₂ ∷Level → Γ ⊢ l₁ ∷Level × Γ ⊢ l₂ ∷Level
  wf-⊢≤ₗ∷L (⊢l₁ , ≡l₂) =
    let _ , ⊢l₂ = wf-⊢≡∷L ≡l₂ in
    ⊢l₁ , ⊢l₂

opaque

  -- Reflexivity.

  refl-⊢≤ₗ∷L :
    Γ ⊢ l ∷Level →
    Γ ⊢ l ≤ₗ l ∷Level
  refl-⊢≤ₗ∷L ⊢l = ⊢≡∷L→⊢≤ₗ∷L ⊢l (supᵘₗ-idem ⊢l)

opaque

  -- Reflexivity.

  reflexive-⊢≤ₗ∷L :
    Γ ⊢ l₁ ≡ l₂ ∷Level →
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level
  reflexive-⊢≤ₗ∷L {l₁} {l₂} l₁≡l₂ =
    let ⊢l₁ , ⊢l₂ = wf-⊢≡∷L l₁≡l₂ in
    ⊢≡∷L→⊢≤ₗ∷L ⊢l₁
      (l₁ supᵘₗ l₂  ≡⟨ supᵘₗ-cong l₁≡l₂ (refl-⊢≡∷L ⊢l₂) ⟩⊢
       l₂ supᵘₗ l₂  ≡⟨ supᵘₗ-idem ⊢l₂ ⟩⊢∎
       l₂           ∎)

opaque
  unfolding _⊢_≤ₗ_∷Level

  -- Transitivity.

  trans-⊢≤ₗ∷L :
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ l₂ ≤ₗ l₃ ∷Level →
    Γ ⊢ l₁ ≤ₗ l₃ ∷Level
  trans-⊢≤ₗ∷L {l₁} {l₂} {l₃} (⊢l₁ , l₁⊔l₂≡l₂) (⊢l₂ , l₂⊔l₃≡l₃) =
    let _ , ⊢l₃ = wf-⊢≡∷L l₂⊔l₃≡l₃ in
    ⊢l₁ ,
    (l₁ supᵘₗ l₃             ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁) (sym-⊢≡∷L l₂⊔l₃≡l₃) ⟩⊢
     l₁ supᵘₗ l₂ supᵘₗ l₃    ≡˘⟨ supᵘₗ-assoc ⊢l₁ ⊢l₂ ⊢l₃ ⟩⊢
     (l₁ supᵘₗ l₂) supᵘₗ l₃  ≡⟨ supᵘₗ-cong l₁⊔l₂≡l₂ (refl-⊢≡∷L ⊢l₃) ⟩⊢
     l₂ supᵘₗ l₃             ≡⟨ l₂⊔l₃≡l₃ ⟩⊢∎
     l₃                      ∎)

opaque
  unfolding _⊢_≤ₗ_∷Level

  -- Antisymmetry.

  antisym-⊢≤ₗ∷L :
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ l₂ ≤ₗ l₁ ∷Level →
    Γ ⊢ l₁ ≡ l₂ ∷Level
  antisym-⊢≤ₗ∷L {l₁} {l₂} (⊢l₁ , l₁⊔l₂≡l₂) (⊢l₂ , l₂⊔l₁≡l₁) =
    l₁           ≡˘⟨ l₂⊔l₁≡l₁ ⟩⊢
    l₂ supᵘₗ l₁  ≡⟨ supᵘₗ-comm ⊢l₂ ⊢l₁ ⟩⊢
    l₁ supᵘₗ l₂  ≡⟨ l₁⊔l₂≡l₂ ⟩⊢∎
    l₂           ∎

opaque

  -- The level zeroᵘₗ is the least well-formed level.

  zeroᵘₗ≤ₗ :
    Γ ⊢ l ∷Level →
    Γ ⊢ zeroᵘₗ ≤ₗ l ∷Level
  zeroᵘₗ≤ₗ ⊢l = ⊢≡∷L→⊢≤ₗ∷L (⊢zeroᵘ (wfLevel ⊢l)) (supᵘₗ-zeroˡ ⊢l)

opaque
  unfolding _supᵘₗ_

  -- The level level t is below ωᵘ+ m (given certain assumptions).

  level≤ₗωᵘ+ :
    Omega-plus-allowed →
    Γ ⊢ level t ∷Level →
    Γ ⊢ level t ≤ₗ ωᵘ+ m ∷Level
  level≤ₗωᵘ+ ok ⊢t =
    ⊢≡∷L→⊢≤ₗ∷L ⊢t $
    refl-⊢≡∷L (literal (Allowed-literal-ωᵘ+-⇔ .proj₂ ok) (wfLevel ⊢t))

opaque
  unfolding _⊢_≤ₗ_∷Level

  -- The function 1ᵘ+ is monotone.

  1ᵘ+-mono :
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ 1ᵘ+ l₁ ≤ₗ 1ᵘ+ l₂ ∷Level
  1ᵘ+-mono {l₁} {l₂} (⊢l₁ , l₁⊔l₂≡l₂) =
    let _ , ⊢l₂ = wf-⊢≡∷L l₁⊔l₂≡l₂ in
    ⊢1ᵘ+ ⊢l₁ ,
    (1ᵘ+ l₁ supᵘₗ 1ᵘ+ l₂  ≡⟨ supᵘₗ-1ᵘ+ ⊢l₁ ⊢l₂ ⟩⊢
     1ᵘ+ (l₁ supᵘₗ l₂)    ≡⟨ 1ᵘ+-cong l₁⊔l₂≡l₂ ⟩⊢∎
     1ᵘ+ l₂               ∎)

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
    ⊢≡∷L→⊢≤ₗ∷L (⊢supᵘₗ ⊢l₁₁ ⊢l₁₂)
      ((l₁₁ supᵘₗ l₁₂) supᵘₗ (l₂₁ supᵘₗ l₂₂)  ≡⟨ supᵘₗ-assoc ⊢l₁₁ ⊢l₁₂ (⊢supᵘₗ ⊢l₂₁ ⊢l₂₂) ⟩⊢
       l₁₁ supᵘₗ (l₁₂ supᵘₗ (l₂₁ supᵘₗ l₂₂))  ≡˘⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁₁) $
                                                  supᵘₗ-assoc ⊢l₁₂ ⊢l₂₁ ⊢l₂₂ ⟩⊢
       l₁₁ supᵘₗ ((l₁₂ supᵘₗ l₂₁) supᵘₗ l₂₂)  ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁₁) $
                                                 supᵘₗ-cong (supᵘₗ-comm ⊢l₁₂ ⊢l₂₁) (refl-⊢≡∷L ⊢l₂₂) ⟩⊢
       l₁₁ supᵘₗ ((l₂₁ supᵘₗ l₁₂) supᵘₗ l₂₂)  ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁₁) $
                                                 supᵘₗ-assoc ⊢l₂₁ ⊢l₁₂ ⊢l₂₂ ⟩⊢
       l₁₁ supᵘₗ (l₂₁ supᵘₗ (l₁₂ supᵘₗ l₂₂))  ≡˘⟨ supᵘₗ-assoc ⊢l₁₁ ⊢l₂₁ (⊢supᵘₗ ⊢l₁₂ ⊢l₂₂) ⟩⊢
       (l₁₁ supᵘₗ l₂₁) supᵘₗ (l₁₂ supᵘₗ l₂₂)  ≡⟨ supᵘₗ-cong (⊢≤ₗ∷L→⊢≡∷L l₁₁≤l₂₁) (⊢≤ₗ∷L→⊢≡∷L l₁₂≤l₂₂) ⟩⊢∎
       l₂₁ supᵘₗ l₂₂                          ∎)

opaque
  unfolding size-of-Level _supᵘₗ_

  -- A variant of supᵘ-sub.

  supᵘₗ-sub :
    Γ ⊢ l ∷Level →
    Γ ⊢ l ≤ₗ 1ᵘ+ l ∷Level
  supᵘₗ-sub ⊢l@(term ok ⊢t) =
    ⊢≡∷L→⊢≤ₗ∷L ⊢l $
    PE.subst (flip (_⊢_≡_∷Level _) _) (PE.sym $ supᵘₗ≡supᵘ ok) $
    term ok (supᵘ-sub ⊢t)
  supᵘₗ-sub ⊢l@(literal {l = ωᵘ+ _} ok ⊢Γ) =
    ⊢≡∷L→⊢≤ₗ∷L ⊢l $
    PE.subst (_⊢_≡_∷Level _ _) (PE.cong ωᵘ+ (N.m≤n⇒m⊔n≡n (N.n≤1+n _))) $
    literal (Allowed-literal-ωᵘ+-→-Allowed-literal-ωᵘ+ ok) ⊢Γ
  supᵘₗ-sub ⊢l@(literal {l = level t} ok ⊢Γ) =
    let t-lit , not-ok = Allowed-literal-level-⇔ .proj₁ ok in
    ⊢≡∷L→⊢≤ₗ∷L ⊢l $
    PE.subst (flip (_⊢_≡_∷Level _) _)
      (level (sucᵘ t)                                                   ≡˘⟨ PE.cong level ↓ᵘ-size-of-Level ⟩
       level (↓ᵘ (N.1+ (size-of-Level t-lit)))                          ≡˘⟨ PE.cong (level ∘→ ↓ᵘ_) $ N.m≤n⇒m⊔n≡n (N.n≤1+n _) ⟩
       level (↓ᵘ (size-of-Level t-lit N.⊔ N.1+ (size-of-Level t-lit)))  ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok t-lit (sucᵘ t-lit) ⟩
       level t supᵘₗ level (sucᵘ t)                                     ∎)
      (literal (Allowed-literal-1ᵘ+-⇔ .proj₂ ok) ⊢Γ)

opaque
  unfolding _⊢_≤ₗ_∷Level

  -- If l₁ is bounded by l₂, then l₁ is also bounded by 1ᵘ+ l₂.

  step-⊢≤ₗ∷L :
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ l₁ ≤ₗ 1ᵘ+ l₂ ∷Level
  step-⊢≤ₗ∷L {l₁} {l₂} (⊢l₁ , l₁⊔l₂≡l₂) =
    let _ , ⊢l₂ = wf-⊢≡∷L l₁⊔l₂≡l₂ in
    ⊢l₁ ,
    (l₁ supᵘₗ 1ᵘ+ l₂                 ≡⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁) (1ᵘ+-cong (sym-⊢≡∷L l₁⊔l₂≡l₂)) ⟩⊢
     l₁ supᵘₗ 1ᵘ+ (l₁ supᵘₗ l₂)      ≡˘⟨ supᵘₗ-cong (refl-⊢≡∷L ⊢l₁) (supᵘₗ-1ᵘ+ ⊢l₁ ⊢l₂) ⟩⊢
     l₁ supᵘₗ (1ᵘ+ l₁ supᵘₗ 1ᵘ+ l₂)  ≡˘⟨ supᵘₗ-assoc ⊢l₁ (⊢1ᵘ+ ⊢l₁) (⊢1ᵘ+ ⊢l₂) ⟩⊢
     (l₁ supᵘₗ 1ᵘ+ l₁) supᵘₗ 1ᵘ+ l₂  ≡⟨ supᵘₗ-cong (supᵘₗ-sub ⊢l₁ .proj₂) (refl-⊢≡∷L (⊢1ᵘ+ ⊢l₂)) ⟩⊢
     1ᵘ+ l₁ supᵘₗ 1ᵘ+ l₂             ≡⟨ supᵘₗ-1ᵘ+ ⊢l₁ ⊢l₂ ⟩⊢
     1ᵘ+ (l₁ supᵘₗ l₂)               ≡⟨ 1ᵘ+-cong l₁⊔l₂≡l₂ ⟩⊢∎
     1ᵘ+ l₂                          ∎)

opaque

  -- The function 1ᵘ+ⁿ is, in a certain sense, monotone.

  1ᵘ+ⁿ-mono :
    n₁ N.≤ n₂ →
    Γ ⊢ l₁ ≤ₗ l₂ ∷Level →
    Γ ⊢ 1ᵘ+ⁿ n₁ l₁ ≤ₗ 1ᵘ+ⁿ n₂ l₂ ∷Level
  1ᵘ+ⁿ-mono (N.z≤n {n = 0}) l₁≤l₂ =
    l₁≤l₂
  1ᵘ+ⁿ-mono (N.z≤n {n = N.1+ n}) l₁≤l₂ =
    step-⊢≤ₗ∷L (1ᵘ+ⁿ-mono (N.z≤n {n = n}) l₁≤l₂)
  1ᵘ+ⁿ-mono (N.s≤s n₁≤n₂) l₁≤l₂ =
    1ᵘ+-mono (1ᵘ+ⁿ-mono n₁≤n₂ l₁≤l₂)

------------------------------------------------------------------------
-- Lemmas related to _⊢_≤_∷Level

opaque

  -- A well-formedness lemma.

  wf-⊢≤ : Γ ⊢ t₁ ≤ t₂ ∷Level → Γ ⊢ t₁ ∷ Level × Γ ⊢ t₂ ∷ Level
  wf-⊢≤ t₁≤t₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ t₁≤t₂ .proj₁) in
    Σ.map (⊢∷Level→⊢∷Level ok) (⊢∷Level→⊢∷Level ok)
      (wf-⊢≤ₗ∷L (term-⊢≤∷L t₁≤t₂))

opaque

  -- Reflexivity.

  ⊢≤-refl : Γ ⊢ t₁ ≡ t₂ ∷ Level → Γ ⊢ t₁ ≤ t₂ ∷Level
  ⊢≤-refl t₁≡t₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ t₁≡t₂ .proj₁) in
    ⊢≤ₗ∷Level→⊢≤∷Level ok (reflexive-⊢≤ₗ∷L (term-⊢≡∷ t₁≡t₂))

opaque

  -- Transitivity.

  ⊢≤-trans :
    Γ ⊢ t₁ ≤ t₂ ∷Level → Γ ⊢ t₂ ≤ t₃ ∷Level → Γ ⊢ t₁ ≤ t₃ ∷Level
  ⊢≤-trans t₁≤t₂ t₂≤t₃ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ t₁≤t₂ .proj₁) in
    ⊢≤ₗ∷Level→⊢≤∷Level ok
      (trans-⊢≤ₗ∷L (term-⊢≤∷L t₁≤t₂) (term-⊢≤∷L t₂≤t₃))

opaque

  -- Antisymmetry.

  ⊢≤-antisymmetric :
    Γ ⊢ t₁ ≤ t₂ ∷Level → Γ ⊢ t₂ ≤ t₁ ∷Level → Γ ⊢ t₁ ≡ t₂ ∷ Level
  ⊢≤-antisymmetric t₁≤t₂ t₂≤t₁ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ t₁≤t₂ .proj₁) in
    ⊢≡∷Level→⊢≡∷Level ok
      (antisym-⊢≤ₗ∷L (term-⊢≤∷L t₁≤t₂) (term-⊢≤∷L t₂≤t₁))

opaque

  -- A variant of supᵘ-sub.
  --
  -- See also Definition.Typed.EqualityRelation.≅ₜ-supᵘ-sub′.

  supᵘ-sub′ : Γ ⊢ t₁ ≤ t₂ ∷Level → Γ ⊢ t₁ ≤ sucᵘ t₂ ∷Level
  supᵘ-sub′ t₁≤t₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ t₁≤t₂ .proj₁) in
    ⊢≤ₗ∷Level→⊢≤∷Level ok (step-⊢≤ₗ∷L (term-⊢≤∷L t₁≤t₂))

opaque

  -- A variant of supᵘ-sub′.

  supᵘ-subⁿ : ∀ n → Γ ⊢ t₁ ≤ t₂ ∷Level → Γ ⊢ t₁ ≤ 1ᵘ+ⁿ n t₂ ∷Level
  supᵘ-subⁿ 0        = idᶠ
  supᵘ-subⁿ (N.1+ n) = supᵘ-sub′ ∘→ supᵘ-subⁿ n

opaque

  -- The function sucᵘ is monotone.

  ≤-sucᵘ :
    Γ ⊢ t₁ ≤ t₂ ∷Level →
    Γ ⊢ sucᵘ t₁ ≤ sucᵘ t₂ ∷Level
  ≤-sucᵘ t₁≤t₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ t₁≤t₂ .proj₁) in
    ⊢≤ₗ∷Level→⊢≤∷Level ok (1ᵘ+-mono (term-⊢≤∷L t₁≤t₂))

opaque

  -- The function 1ᵘ+ⁿ is monotone.

  ≤-1ᵘ+ⁿ :
    n₁ N.≤ n₂ →
    Γ ⊢ t₁ ≤ t₂ ∷Level →
    Γ ⊢ 1ᵘ+ⁿ n₁ t₁ ≤ 1ᵘ+ⁿ n₂ t₂ ∷Level
  ≤-1ᵘ+ⁿ {n₁} {n₂} n₁≤n₂ t₁≤t₂ =
    let ok = inversion-Level-⊢ (wf-⊢≡∷ t₁≤t₂ .proj₁) in
    ⊢≤ₗ∷Level→⊢≤∷Level ok $
    PE.subst₂ (_⊢_≤ₗ_∷Level _) (1ᵘ+ⁿ-level≡ n₁) (1ᵘ+ⁿ-level≡ n₂) $
    1ᵘ+ⁿ-mono n₁≤n₂ (term-⊢≤∷L t₁≤t₂)

------------------------------------------------------------------------
-- An inequality

opaque

  -- Finite levels are not equal to infinite levels.

  level≢ωᵘ+ : ¬ Γ ⊢ level t ≡ ωᵘ+ m ∷Level
  level≢ωᵘ+ ()
