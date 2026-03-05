------------------------------------------------------------------------
-- The term former _supᵘₗ_
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Untyped.Sup
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Allowed-literal R
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product as Σ
open import Tools.PropositionalEquality
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎

private variable
  n             : Nat
  ρ             : Wk _ _
  σ             : Subst _ _
  A B t t₁ t₂ u : Term _
  l l₁ l₂       : Lvl _
  k             : Term-kind
  b             : BinderMode
  p q           : M

opaque

  -- A variant of _supᵘ_.
  --
  -- If only level literals are allowed, and the inputs are
  -- literals, then a literal is returned.

  infixr 30 _supᵘₗ_

  _supᵘₗ_ : Term[ k ] n → Term[ k ] n → Term[ k ] n
  _supᵘₗ_ {k = tm} t₁ t₂ with level-support
  … | only-literals = t₁ supᵘₗ′ t₂
  … | level-type _  = t₁ supᵘ t₂
  ωᵘ+ m₁   supᵘₗ ωᵘ+ m₂   = ωᵘ+ (m₁ ⊔ m₂)
  ωᵘ+ m₁   supᵘₗ level _  = ωᵘ+ m₁
  level _  supᵘₗ ωᵘ+ m₂   = ωᵘ+ m₂
  level t₁ supᵘₗ level t₂ = level (t₁ supᵘₗ t₂)

opaque
  unfolding _supᵘₗ_

  -- A weakening lemma for _supᵘₗ_.

  wk-supᵘₗ :
    {l₁ l₂ : Term[ k ] n} →
    wk ρ (l₁ supᵘₗ l₂) ≡ wk ρ l₁ supᵘₗ wk ρ l₂
  wk-supᵘₗ {k = tm} with level-support
  … | only-literals = wk-supᵘₗ′
  … | level-type _  = refl
  wk-supᵘₗ {l₁ = ωᵘ+ _}   {l₂ = ωᵘ+ _}   = refl
  wk-supᵘₗ {l₁ = ωᵘ+ _}   {l₂ = level _} = refl
  wk-supᵘₗ {l₁ = level _} {l₂ = ωᵘ+ _}   = refl
  wk-supᵘₗ {l₁ = level _} {l₂ = level _} = cong level wk-supᵘₗ

opaque
  unfolding _supᵘₗ_

  -- A substitution lemma for _supᵘₗ_.

  supᵘₗ-[]′ :
    {l₁ l₂ : Term[ k ] n} →
    (¬ Level-allowed →
     Level-literal (l₁ [ σ ]) × Level-literal (l₂ [ σ ]) →
     Level-literal l₁ × Level-literal l₂) →
    l₁ supᵘₗ l₂ [ σ ] ≡ (l₁ [ σ ]) supᵘₗ (l₂ [ σ ])
  supᵘₗ-[]′ {k = tm} {σ} {l₁ = t₁} {l₂ = t₂} hyp
    with level-support in eq
  … | level-type _  = refl
  … | only-literals
    using not-ok ← ¬Level-allowed⇔ .proj₂ eq
    with Level-literal? (t₁ [ σ ]) ×-dec Level-literal? (t₂ [ σ ])
  … | yes both =
    uncurry supᵘₗ′-[] (hyp not-ok both)
  … | no not-both =
    t₁ supᵘₗ′ t₂ [ σ ]            ≡⟨ (cong _[ _ ] $
                                      supᵘₗ′≡supᵘ λ (t₁-lit , t₂-lit) →
                                      not-both (Level-literal-[] t₁-lit , Level-literal-[] t₂-lit)) ⟩
    t₁ supᵘ t₂ [ σ ]              ≡⟨⟩
    (t₁ [ σ ]) supᵘ (t₂ [ σ ])    ≡˘⟨ supᵘₗ′≡supᵘ not-both ⟩
    (t₁ [ σ ]) supᵘₗ′ (t₂ [ σ ])  ∎
  supᵘₗ-[]′ {l₁ = ωᵘ+ _}   {l₂ = ωᵘ+ _}   _   = refl
  supᵘₗ-[]′ {l₁ = ωᵘ+ _}   {l₂ = level _} _   = refl
  supᵘₗ-[]′ {l₁ = level _} {l₂ = ωᵘ+ _}   _   = refl
  supᵘₗ-[]′ {l₁ = level _} {l₂ = level _} hyp =
    cong level $
    supᵘₗ-[]′ λ not-ok →
    Σ.map (λ { (level l) → l }) (λ { (level l) → l }) ∘→
    hyp not-ok ∘→
    Σ.map level level

opaque
  unfolding _supᵘₗ_

  -- A "computation rule" for _supᵘₗ_.

  supᵘₗ≡supᵘ-tm :
    Level-allowed →
    t₁ supᵘₗ t₂ ≡ t₁ supᵘ t₂
  supᵘₗ≡supᵘ-tm ok with level-support in eq
  … | level-type _ =
    refl
  … | only-literals =
    ⊥-elim (¬Level-allowed⇔ .proj₂ eq ok)

opaque
  unfolding _supᵘₗ_

  -- A "computation rule" for _supᵘₗ_.

  supᵘₗ≡supᵘ :
    Level-allowed →
    level t₁ supᵘₗ level t₂ ≡ level (t₁ supᵘ t₂)
  supᵘₗ≡supᵘ ok = cong level (supᵘₗ≡supᵘ-tm ok)

opaque
  unfolding _supᵘₗ_

  -- A "computation rule" rule for _supᵘₗ_.

  supᵘₗ≡supᵘₗ′-tm :
    ¬ Level-allowed →
    t₁ supᵘₗ t₂ ≡ t₁ supᵘₗ′ t₂
  supᵘₗ≡supᵘₗ′-tm not-ok with level-support in eq
  … | only-literals =
    refl
  … | level-type _ =
    case trans (sym eq) (¬Level-allowed⇔ .proj₁ not-ok) of λ ()

opaque
  unfolding _supᵘₗ_

  -- A "computation rule" rule for _supᵘₗ_.

  supᵘₗ≡supᵘₗ′ :
    ¬ Level-allowed →
    level t₁ supᵘₗ level t₂ ≡ level (t₁ supᵘₗ′ t₂)
  supᵘₗ≡supᵘₗ′ not-ok = cong level (supᵘₗ≡supᵘₗ′-tm not-ok)

opaque

  -- A variant of supᵘₗ≡supᵘₗ′-tm.

  supᵘₗ≡↓ᵘ⊔-tm :
    ¬ Level-allowed →
    (t₁-lit : Level-literal t₁) (t₂-lit : Level-literal t₂) →
    t₁ supᵘₗ t₂ ≡
    ↓ᵘ (size-of-Level t₁-lit ⊔ size-of-Level t₂-lit)
  supᵘₗ≡↓ᵘ⊔-tm {t₁} {t₂} not-ok t₁-lit t₂-lit =
    t₁ supᵘₗ  t₂                                      ≡⟨ supᵘₗ≡supᵘₗ′-tm not-ok ⟩
    t₁ supᵘₗ′ t₂                                      ≡⟨ supᵘₗ′≡↓ᵘ⊔ t₁-lit t₂-lit ⟩
    ↓ᵘ (size-of-Level t₁-lit ⊔ size-of-Level t₂-lit)  ∎

opaque
  unfolding _supᵘₗ_

  -- A variant of supᵘₗ≡supᵘₗ′.

  supᵘₗ≡↓ᵘ⊔ :
    ¬ Level-allowed →
    (t₁-lit : Level-literal t₁) (t₂-lit : Level-literal t₂) →
    level t₁ supᵘₗ level t₂ ≡
    level (↓ᵘ (size-of-Level t₁-lit ⊔ size-of-Level t₂-lit))
  supᵘₗ≡↓ᵘ⊔ not-ok t₁-lit t₂-lit =
    cong level (supᵘₗ≡↓ᵘ⊔-tm not-ok t₁-lit t₂-lit)

opaque
  unfolding _supᵘₗ_

  -- The level l₁ supᵘₗ l₂ is infinite if and only if l₁ or l₂ is.

  Infinite-supᵘₗ-⇔ :
    Infinite (l₁ supᵘₗ l₂) ⇔ (Infinite l₁ ⊎ Infinite l₂)
  Infinite-supᵘₗ-⇔ = to _ _ , from
    where
    to :
      (l₁ l₂ : Lvl n) → Infinite (l₁ supᵘₗ l₂) →
      Infinite l₁ ⊎ Infinite l₂
    to (ωᵘ+ _)   _         _  = inj₁ ωᵘ+
    to (level _) (ωᵘ+ _)   _  = inj₂ ωᵘ+
    to (level _) (level _) ()

    from : Infinite l₁ ⊎ Infinite l₂ → Infinite (l₁ supᵘₗ l₂)
    from {l₂ = ωᵘ+ _}   (inj₁ ωᵘ+) = ωᵘ+
    from {l₂ = level _} (inj₁ ωᵘ+) = ωᵘ+
    from {l₁ = ωᵘ+ _}   (inj₂ ωᵘ+) = ωᵘ+
    from {l₁ = level _} (inj₂ ωᵘ+) = ωᵘ+

opaque
  unfolding _supᵘₗ_

  -- If t₁ supᵘₗ t₂ is a level literal, then both t₁ and t₂ are level
  -- literals, and Level is not allowed.

  Level-literal-supᵘₗ-→-tm :
    Level-literal (t₁ supᵘₗ t₂) →
    ¬ Level-allowed × Level-literal t₁ × Level-literal t₂
  Level-literal-supᵘₗ-→-tm lit with level-support in eq
  Level-literal-supᵘₗ-→-tm ()  | level-type _
  Level-literal-supᵘₗ-→-tm lit | only-literals =
    let not-ok      = ¬Level-allowed⇔ .proj₂ eq
        lit₁ , lit₂ = Level-literal-supᵘₗ′⇔ .proj₁ lit
    in
    not-ok , lit₁ , lit₂

opaque
  unfolding _supᵘₗ_

  -- If level t₁ supᵘₗ level t₂ is a level literal, then both t₁ and
  -- t₂ are level literals, and Level is not allowed.

  Level-literal-supᵘₗ-level-→ :
    Level-literal (level t₁ supᵘₗ level t₂) →
    ¬ Level-allowed × Level-literal t₁ × Level-literal t₂
  Level-literal-supᵘₗ-level-→ =
    Level-literal-supᵘₗ-→-tm ∘→ Level-literal-level-⇔ .proj₁

private opaque
  unfolding _supᵘₗ_

  -- A lemma used below.

  →Level-literal-supᵘₗ :
    {l₁ l₂ : Term[ k ] n} →
    Infinite l₁ ⊎ Infinite l₂ ⊎
    ¬ Level-allowed × Level-literal l₁ × Level-literal l₂ →
    Level-literal (l₁ supᵘₗ l₂)
  →Level-literal-supᵘₗ {k = tm} (inj₂ (inj₂ (not-ok , lit₁ , lit₂))) =
    subst Level-literal (sym (supᵘₗ≡supᵘₗ′-tm not-ok))
      (Level-literal-supᵘₗ′⇔ .proj₂ (lit₁ , lit₂))
  →Level-literal-supᵘₗ (inj₂ (inj₂ (_ , ωᵘ+     , ωᵘ+)))     = ωᵘ+
  →Level-literal-supᵘₗ (inj₂ (inj₂ (_ , ωᵘ+     , level _))) = ωᵘ+
  →Level-literal-supᵘₗ (inj₂ (inj₂ (_ , level _ , ωᵘ+)))     = ωᵘ+
  →Level-literal-supᵘₗ
    (inj₂ (inj₂ (not-ok , level lit₁ , level lit₂))) =
    Level-literal-level-⇔ .proj₂ $
    →Level-literal-supᵘₗ (inj₂ (inj₂ (not-ok , lit₁ , lit₂)))
  →Level-literal-supᵘₗ {k = tm}       (inj₁ ())
  →Level-literal-supᵘₗ {l₂ = ωᵘ+ _}   (inj₁ ωᵘ+)        = ωᵘ+
  →Level-literal-supᵘₗ {l₂ = level _} (inj₁ ωᵘ+)        = ωᵘ+
  →Level-literal-supᵘₗ {k = tm}       (inj₂ (inj₁ ()))
  →Level-literal-supᵘₗ {l₁ = ωᵘ+ _}   (inj₂ (inj₁ ωᵘ+)) = ωᵘ+
  →Level-literal-supᵘₗ {l₁ = level _} (inj₂ (inj₁ ωᵘ+)) = ωᵘ+

opaque
  unfolding →Level-literal-supᵘₗ

  -- The level l₁ supᵘₗ l₂ is a level literal if and only if
  -- * l₁ is infinite,
  -- * l₂ is infinite, or
  -- * neither is infinite, both are level literals, and Level is not
  --   allowed.

  Level-literal-supᵘₗ-⇔ :
    {l₁ l₂ : Term[ k ] n} →
    Level-literal (l₁ supᵘₗ l₂) ⇔
    (Infinite l₁ ⊎ Infinite l₂ ⊎
     ¬ Level-allowed × ¬ Infinite l₁ × ¬ Infinite l₂ ×
     Level-literal l₁ × Level-literal l₂)
  Level-literal-supᵘₗ-⇔ =
    to _ _ _ ,
    →Level-literal-supᵘₗ ∘→
    ⊎.map idᶠ (⊎.map idᶠ (Σ.map idᶠ (proj₂ ∘→ proj₂)))
    where
    to :
      ∀ k (l₁ l₂ : Term[ k ] n) → Level-literal (l₁ supᵘₗ l₂) →
      Infinite l₁ ⊎ Infinite l₂ ⊎
      ¬ Level-allowed × ¬ Infinite l₁ × ¬ Infinite l₂ ×
      Level-literal l₁ × Level-literal l₂
    to tm _ _ lit =
      let not-ok , lit₁ , lit₂ = Level-literal-supᵘₗ-→-tm lit in
      inj₂ (inj₂ (not-ok , (λ ()) , (λ ()) , lit₁ , lit₂))
    to _ (ωᵘ+ _)   _         _           = inj₁ ωᵘ+
    to _ _         (ωᵘ+ _)   _           = inj₂ (inj₁ ωᵘ+)
    to _ (level _) (level _) (level lit) =
      let not-ok , lit₁ , lit₂ = Level-literal-supᵘₗ-→-tm lit in
      inj₂ (inj₂ (not-ok , (λ ()) , (λ ()) , level lit₁ , level lit₂))

opaque
  unfolding →Level-literal-supᵘₗ

  -- A variant of Level-literal-supᵘₗ-⇔. The level l₁ supᵘₗ l₂ is a
  -- level literal if and only if
  -- * l₁ is infinite,
  -- * l₂ is infinite, or
  -- * both are level literals and Level is not allowed.

  Level-literal-supᵘₗ-⇔′ :
    {l₁ l₂ : Term[ k ] n} →
    Level-literal (l₁ supᵘₗ l₂) ⇔
    (Infinite l₁ ⊎ Infinite l₂ ⊎
     ¬ Level-allowed × Level-literal l₁ × Level-literal l₂)
  Level-literal-supᵘₗ-⇔′ =
    ⊎.map idᶠ (⊎.map idᶠ (Σ.map idᶠ (proj₂ ∘→ proj₂))) ∘→
    Level-literal-supᵘₗ-⇔ .proj₁ ,
    →Level-literal-supᵘₗ

opaque

  -- If Level is not allowed, then level t₁ supᵘₗ level t₂ is a level
  -- literal if and only if t₁ and t₂ are.

  Level-literal-supᵘₗ-level-⇔ :
    ¬ Level-allowed →
    Level-literal (level t₁ supᵘₗ level t₂) ⇔
    (Level-literal t₁ × Level-literal t₂)
  Level-literal-supᵘₗ-level-⇔ not-ok =
    proj₂ ∘→ Level-literal-supᵘₗ-level-→ ,
    (λ (lit₁ , lit₂) →
       Level-literal-supᵘₗ-⇔′ .proj₂
         (inj₂ (inj₂ (not-ok , level lit₁ , level lit₂))))

opaque
  unfolding _supᵘₗ_

  -- If Level is not allowed, then t₁ supᵘₗ t₂ is a level literal if
  -- and only if t₁ and t₂ are.

  Level-literal-supᵘₗ-⇔-tm :
    ¬ Level-allowed →
    Level-literal (t₁ supᵘₗ t₂) ⇔
    (Level-literal t₁ × Level-literal t₂)
  Level-literal-supᵘₗ-⇔-tm {t₁} {t₂} not-ok =
    Level-literal (t₁ supᵘₗ t₂)              ⇔˘⟨ Level-literal-level-⇔ ⟩
    Level-literal (level (t₁ supᵘₗ t₂))      ⇔⟨ id⇔ ⟩
    Level-literal (level t₁ supᵘₗ level t₂)  ⇔⟨ Level-literal-supᵘₗ-level-⇔ not-ok ⟩
    Level-literal t₁ × Level-literal t₂      □⇔

opaque
  unfolding Allowed-literal _supᵘₗ_

  -- If l₁ and l₂ are allowed literals, then l₁ supᵘₗ l₂ is.

  Allowed-literal-supᵘₗ :
    Allowed-literal l₁ → Allowed-literal l₂ →
    Allowed-literal (l₁ supᵘₗ l₂)
  Allowed-literal-supᵘₗ {l₁ = ωᵘ+ _}   {l₂ = ωᵘ+ _}   ok _  = ok
  Allowed-literal-supᵘₗ {l₁ = ωᵘ+ _}   {l₂ = level _} ok _  = ok
  Allowed-literal-supᵘₗ {l₁ = level _} {l₂ = ωᵘ+ _}   _  ok = ok
  Allowed-literal-supᵘₗ
    {l₁ = level _} {l₂ = level _} (lit₁ , not-ok) (lit₂ , _) =
    Level-literal-level-⇔ .proj₁
      (Level-literal-supᵘₗ-⇔′ .proj₂
         (inj₂ (inj₂ (not-ok , level lit₁ , level lit₂)))) ,
    not-ok

opaque
  unfolding Allowed-literal _supᵘₗ_

  -- If l₁ supᵘₗ l₂ is an allowed literal, then l₁ or l₂ is.

  Allowed-literal-supᵘₗ-→ :
    Allowed-literal (l₁ supᵘₗ l₂) →
    Allowed-literal l₁ ⊎ Allowed-literal l₂
  Allowed-literal-supᵘₗ-→ {l₁ = ωᵘ+ _} {l₂ = ωᵘ+ _} ok =
    inj₁ ok
  Allowed-literal-supᵘₗ-→ {l₁ = ωᵘ+ _} {l₂ = level _} ok =
    inj₁ ok
  Allowed-literal-supᵘₗ-→ {l₁ = level _} {l₂ = ωᵘ+ _} ok =
    inj₂ ok
  Allowed-literal-supᵘₗ-→ {l₁ = level _} {l₂ = level _} (sup-lit , ok) =
    let _ , t₁-lit , _ =
          Level-literal-supᵘₗ-level-→
            (Level-literal-level-⇔ .proj₂ sup-lit)
    in
    inj₁ (t₁-lit , ok)

opaque
  unfolding _supᵘₗ_ size-of-Level

  -- If l is a level that is a level literal, and Level is not allowed
  -- or l is infinite, then zeroᵘₗ supᵘₗ l is equal to l.

  Level-literal→zeroᵘₗ-supᵘₗ :
    ¬ Level-allowed ⊎ Infinite l →
    Level-literal l →
    zeroᵘₗ supᵘₗ l ≡ l
  Level-literal→zeroᵘₗ-supᵘₗ _ ωᵘ+ =
    refl
  Level-literal→zeroᵘₗ-supᵘₗ (inj₁ not-ok) (level {t} t-lit) =
    zeroᵘₗ supᵘₗ level t              ≡⟨ supᵘₗ≡↓ᵘ⊔ not-ok zeroᵘ t-lit ⟩
    level (↓ᵘ (size-of-Level t-lit))  ≡⟨ cong level ↓ᵘ-size-of-Level ⟩
    level t                           ∎
  Level-literal→zeroᵘₗ-supᵘₗ (inj₂ ()) (level _)

opaque
  unfolding _supᵘₗ_

  -- If l₁ and l₂ are level literals, and either Level is not allowed
  -- or one of l₁ and l₂ is infinite, then l₁ supᵘₗ l₂ is equal to
  -- l₂ supᵘₗ l₁.

  Level-literal→supᵘₗ-comm :
    ¬ Level-allowed ⊎ Infinite l₁ ⊎ Infinite l₂ →
    Level-literal l₁ → Level-literal l₂ →
    l₁ supᵘₗ l₂ ≡ l₂ supᵘₗ l₁
  Level-literal→supᵘₗ-comm _ (ωᵘ+ {m}) ωᵘ+ =
    cong ωᵘ+ (⊔-comm m _)
  Level-literal→supᵘₗ-comm _ ωᵘ+ (level _) =
    refl
  Level-literal→supᵘₗ-comm _ (level _) ωᵘ+ =
    refl
  Level-literal→supᵘₗ-comm
    (inj₁ not-ok) (level {t = t₁} t₁-lit) (level {t = t₂} t₂-lit) =
    level t₁ supᵘₗ level t₂                                   ≡⟨ supᵘₗ≡↓ᵘ⊔ not-ok t₁-lit t₂-lit ⟩
    level (↓ᵘ (size-of-Level t₁-lit ⊔ size-of-Level t₂-lit))  ≡⟨ cong (level ∘→ ↓ᵘ_) (⊔-comm (size-of-Level _) _) ⟩
    level (↓ᵘ (size-of-Level t₂-lit ⊔ size-of-Level t₁-lit))  ≡˘⟨ supᵘₗ≡↓ᵘ⊔ not-ok t₂-lit t₁-lit ⟩
    level t₂ supᵘₗ level t₁                                   ∎
  Level-literal→supᵘₗ-comm (inj₂ (inj₁ ())) (level _) _
  Level-literal→supᵘₗ-comm (inj₂ (inj₂ ())) _         (level _)

opaque
  unfolding _supᵘₗ_

  -- If l₁ supᵘₗ l₂ [ σ ] is a level literal, then l₁ supᵘₗ l₂ is a
  -- level literal.

  Level-literal-supᵘₗ-[]₁ :
    {l₁ l₂ : Term[ k ] n} →
    Level-literal (l₁ supᵘₗ l₂ [ σ ]) →
    Level-literal (l₁ supᵘₗ l₂)
  Level-literal-supᵘₗ-[]₁ {k = tm} {σ} {l₁ = t₁} {l₂ = t₂}
    with Level-allowed?
  … | yes ok =
    Level-literal (t₁ supᵘₗ t₂ [ σ ])  ≡⟨ cong (Level-literal ∘→ _[ σ ]) (supᵘₗ≡supᵘ-tm ok) ⟩→
    Level-literal (t₁ supᵘ t₂ [ σ ])   →⟨ (λ ()) ⟩
    Level-literal (t₁ supᵘₗ t₂)        □
  … | no not-ok
    with Level-literal? t₁ ×-dec Level-literal? t₂
  … | yes both =
    Level-literal (t₁ supᵘₗ t₂ [ σ ])    →⟨ (λ _ → both) ⟩
    Level-literal t₁ × Level-literal t₂  →⟨ Level-literal-supᵘₗ-⇔-tm not-ok .proj₂ ⟩
    Level-literal (t₁ supᵘₗ t₂)          □
  … | no not-both =
    Level-literal (t₁ supᵘₗ t₂ [ σ ])   ≡⟨ cong (Level-literal ∘→ _[ σ ]) (supᵘₗ≡supᵘₗ′-tm not-ok) ⟩→
    Level-literal (t₁ supᵘₗ′ t₂ [ σ ])  ≡⟨ cong (Level-literal ∘→ _[ σ ]) (supᵘₗ′≡supᵘ not-both) ⟩→
    Level-literal (t₁ supᵘ t₂ [ σ ])    →⟨ (λ ()) ⟩
    Level-literal (t₁ supᵘₗ t₂)         □
  Level-literal-supᵘₗ-[]₁ {l₁ = ωᵘ+ _} {l₂ = ωᵘ+ _} _ =
    ωᵘ+
  Level-literal-supᵘₗ-[]₁ {l₁ = ωᵘ+ _} {l₂ = level _} _ =
    ωᵘ+
  Level-literal-supᵘₗ-[]₁ {l₁ = level _} {l₂ = ωᵘ+ _} _ =
    ωᵘ+
  Level-literal-supᵘₗ-[]₁ {σ} {l₁ = level t₁} {l₂ = level t₂} =
    Level-literal (level t₁ supᵘₗ level t₂ [ σ ])  →⟨ idᶠ ⟩
    Level-literal (level (t₁ supᵘₗ t₂ [ σ ]))      ⇔⟨ Level-literal-level-⇔ ⟩→
    Level-literal (t₁ supᵘₗ t₂ [ σ ])              →⟨ Level-literal-supᵘₗ-[]₁ ⟩
    Level-literal (t₁ supᵘₗ t₂)                    ⇔˘⟨ Level-literal-level-⇔ ⟩→
    Level-literal (level (t₁ supᵘₗ t₂))            →⟨ idᶠ ⟩
    Level-literal (level t₁ supᵘₗ level t₂)        □

opaque
  unfolding _supᵘₗ_

  -- If l₁ supᵘₗ l₂ [ σ ] is a level literal, then
  -- (l₁ [ σ ]) supᵘₗ (l₂ [ σ ]) is a level literal.

  Level-literal-supᵘₗ-[]₂ :
    {l₁ l₂ : Term[ k ] n} →
    Level-literal (l₁ supᵘₗ l₂ [ σ ]) →
    Level-literal ((l₁ [ σ ]) supᵘₗ (l₂ [ σ ]))
  Level-literal-supᵘₗ-[]₂ {k = tm} {σ} {l₁ = t₁} {l₂ = t₂} =
    Level-literal (t₁ supᵘₗ t₂ [ σ ])                      →⟨ Level-literal-supᵘₗ-[]₁ ⟩

    Level-literal (t₁ supᵘₗ t₂)                            →⟨ Level-literal-supᵘₗ-→-tm ⟩

    ¬ Level-allowed × Level-literal t₁ × Level-literal t₂  →⟨ Σ.map idᶠ (Σ.map Level-literal-[] Level-literal-[]) ⟩

    ¬ Level-allowed × Level-literal (t₁ [ σ ]) ×
    Level-literal (t₂ [ σ ])                               →⟨ (λ (not-okᴸ , lits) → Level-literal-supᵘₗ-⇔-tm not-okᴸ .proj₂ lits) ⟩

    Level-literal ((t₁ [ σ ]) supᵘₗ (t₂ [ σ ]))            □
  Level-literal-supᵘₗ-[]₂ {l₁ = ωᵘ+ _} {l₂ = ωᵘ+ _} _ =
    ωᵘ+
  Level-literal-supᵘₗ-[]₂ {l₁ = ωᵘ+ _} {l₂ = level _} _ =
    ωᵘ+
  Level-literal-supᵘₗ-[]₂ {l₁ = level _} {l₂ = ωᵘ+ _} _ =
    ωᵘ+
  Level-literal-supᵘₗ-[]₂ {σ} {l₁ = level t₁} {l₂ = level t₂} =
    Level-literal (level t₁ supᵘₗ level t₂ [ σ ])            ⇔⟨ Level-literal-level-⇔ ⟩→
    Level-literal (t₁ supᵘₗ t₂ [ σ ])                        →⟨ Level-literal-supᵘₗ-[]₂ ⟩
    Level-literal ((t₁ [ σ ]) supᵘₗ (t₂ [ σ ]))              ⇔˘⟨ Level-literal-level-⇔ ⟩→
    Level-literal ((level t₁ [ σ ]) supᵘₗ (level t₂ [ σ ]))  □

opaque
  unfolding
    Level-literal→Universe-level Level-literal-level-⇔
    Level-literal-supᵘₗ-level-⇔ Level-literal-supᵘₗ-⇔′

  -- A lemma relating Level-literal→Universe-level,
  -- Level-literal-supᵘₗ-level-⇔ and size-of-Level.

  Level-literal→Universe-level-Level-literal-supᵘₗ-level-⇔ :
    {not-ok : ¬ Level-allowed}
    {t₁-lit : Level-literal t₁}
    {t₂-lit : Level-literal t₂} →
    Level-literal→Universe-level
      (Level-literal-supᵘₗ-level-⇔ not-ok .proj₂ (t₁-lit , t₂-lit)) ≡
    0ᵘ+ (size-of-Level t₁-lit ⊔ size-of-Level t₂-lit)
  Level-literal→Universe-level-Level-literal-supᵘₗ-level-⇔
    {not-ok} {t₁-lit = t₁} {t₂-lit = t₂} =
    (0ᵘ+ $ size-of-Level $
     subst Level-literal (sym (supᵘₗ≡supᵘₗ′-tm not-ok)) $
     Level-literal-supᵘₗ′⇔ .proj₂ (t₁ , t₂))                      ≡⟨ cong 0ᵘ+ size-of-Level-subst ⟩

    0ᵘ+ (size-of-Level (Level-literal-supᵘₗ′⇔ .proj₂ (t₁ , t₂)))  ≡⟨ cong 0ᵘ+ size-of-Level-Level-literal-supᵘₗ′⇔ ⟩

    0ᵘ+ (size-of-Level t₁ ⊔ size-of-Level t₂)                     ∎

opaque
  unfolding
    Allowed-literal→Universe-level Allowed-literal-supᵘₗ
    Level-literal-supᵘₗ-level-⇔

  -- A lemma relating Allowed-literal→Universe-level and
  -- Allowed-literal-supᵘₗ.

  Allowed-literal→Universe-level-Allowed-literal-supᵘₗ :
    {ok₁ : Allowed-literal l₁} {ok₂ : Allowed-literal l₂} →
    Allowed-literal→Universe-level (Allowed-literal-supᵘₗ ok₁ ok₂) ≡
    Allowed-literal→Universe-level ok₁ ⊔ᵘ
    Allowed-literal→Universe-level ok₂
  Allowed-literal→Universe-level-Allowed-literal-supᵘₗ = lemma _ _ _ _
    where
    lemma :
      (l₁ l₂ : Lvl n)
      (ok₁ : Allowed-literal l₁) (ok₂ : Allowed-literal l₂) →
      Allowed-literal→Universe-level {l = l₁ supᵘₗ l₂}
        (Allowed-literal-supᵘₗ {l₁ = l₁} ok₁ ok₂) ≡
      Allowed-literal→Universe-level {l = l₁} ok₁ ⊔ᵘ
      Allowed-literal→Universe-level {l = l₂} ok₂
    lemma (ωᵘ+ _)    (ωᵘ+ _)    _               _          = refl
    lemma (ωᵘ+ _)    (level _)  _               _          = refl
    lemma (level _)  (ωᵘ+ _)    _               _          = refl
    lemma (level t₁) (level t₂) (lit₁ , not-ok) (lit₂ , _) =
      (0ᵘ+ $ size-of-Level $ Level-literal-level-⇔ .proj₁ $
       Level-literal-supᵘₗ-level-⇔ not-ok .proj₂ (lit₁ , lit₂))    ≡˘⟨ Level-literal→Universe-level-level ⟩

      Level-literal→Universe-level
        (Level-literal-supᵘₗ-level-⇔ not-ok .proj₂ (lit₁ , lit₂))  ≡⟨ Level-literal→Universe-level-Level-literal-supᵘₗ-level-⇔ ⟩

      0ᵘ+ (size-of-Level lit₁ ⊔ size-of-Level lit₂)                ∎

opaque
  unfolding _supᵘₗ_ _supᵘₗ′_

  -- Applications of _supᵘₗ_ are equal to (applications of) ↓ᵘ_ or
  -- _supᵘ_.

  supᵘₗ≡ :
    (t₁ t₂ : Term n) →
    (∃ λ n → t₁ supᵘₗ t₂ ≡ ↓ᵘ n) ⊎ t₁ supᵘₗ t₂ ≡ t₁ supᵘ t₂
  supᵘₗ≡ t₁ t₂ with level-support
  … | level-type _  = inj₂ refl
  … | only-literals
    with Level-literal? t₁ ×-dec Level-literal? t₂
  …   | no _  = inj₂ refl
  …   | yes _ = inj₁ (_ , refl)

opaque
  unfolding ↓ᵘ_

  -- Applications of _supᵘₗ_ are not equal to Level.

  supᵘₗ≢Level : t₁ supᵘₗ t₂ ≢ Level
  supᵘₗ≢Level {t₁} {t₂} eq with supᵘₗ≡ t₁ t₂
  … | inj₁ (0 , eq′)    = case trans (sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case trans (sym eq) eq′ of λ ()
  … | inj₂ eq′          = case trans (sym eq) eq′ of λ ()

opaque
  unfolding ↓ᵘ_

  -- Applications of _supᵘₗ_ are not equal to applications of Lift.

  supᵘₗ≢Lift : t₁ supᵘₗ t₂ ≢ Lift l A
  supᵘₗ≢Lift {t₁} {t₂} eq with supᵘₗ≡ t₁ t₂
  … | inj₁ (0 , eq′)    = case trans (sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case trans (sym eq) eq′ of λ ()
  … | inj₂ eq′          = case trans (sym eq) eq′ of λ ()

opaque
  unfolding ↓ᵘ_

  -- Applications of _supᵘₗ_ are not equal to applications of
  -- ΠΣ⟨_⟩_,_▷_▹_.

  supᵘₗ≢ΠΣ : t₁ supᵘₗ t₂ ≢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  supᵘₗ≢ΠΣ {t₁} {t₂} eq with supᵘₗ≡ t₁ t₂
  … | inj₁ (0 , eq′)    = case trans (sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case trans (sym eq) eq′ of λ ()
  … | inj₂ eq′          = case trans (sym eq) eq′ of λ ()

opaque
  unfolding ↓ᵘ_

  -- Applications of _supᵘₗ_ are not equal to applications of Id.

  supᵘₗ≢Id : t₁ supᵘₗ t₂ ≢ Id A t u
  supᵘₗ≢Id {t₁} {t₂} eq with supᵘₗ≡ t₁ t₂
  … | inj₁ (0 , eq′)    = case trans (sym eq) eq′ of λ ()
  … | inj₁ (1+ _ , eq′) = case trans (sym eq) eq′ of λ ()
  … | inj₂ eq′          = case trans (sym eq) eq′ of λ ()
