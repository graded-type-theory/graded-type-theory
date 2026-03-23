------------------------------------------------------------------------
-- Inversion lemmas
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Inversion
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
import Definition.Typed.Inversion.Primitive R as I
open import Definition.Typed.Properties.Admissible.Level.Primitive R
open import Definition.Typed.Properties.Admissible.U.Primitive R
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Substitution.Primitive R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Allowed-literal R
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Properties M
open import Definition.Untyped.Sup R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat as N
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎

open I public

private variable
  α m n               : Nat
  x                   : Fin _
  Γ                   : Cons _ _
  A B C t t₁ t₂ u v w : Term _
  l l₁ l₂             : Lvl _
  b                   : BinderMode
  s                   : Strength
  p q q′ r            : M

------------------------------------------------------------------------
-- Inversion for variables

opaque

  -- Inversion for var.

  inversion-var : Γ ⊢ var x ∷ A → ∃ λ B → x ∷ B ∈ Γ .vars × Γ ⊢ A ≡ B
  inversion-var ⊢x@(var _ x∈) =
    _ , x∈ , refl (wf-⊢ ⊢x)
  inversion-var (conv ⊢var eq) =
    let a , b , c = inversion-var ⊢var in
    a , b , trans (sym eq) c

------------------------------------------------------------------------
-- Inversion for definitions

opaque

  -- Inversion for defn.

  inversion-defn : Γ ⊢ defn α ∷ A
                 → ∃ λ A′ → α ↦∷ A′ ∈ Γ .defs × (Γ ⊢ A ≡ wk wk₀ A′)
  inversion-defn (defn {A′ = A} ⊢Γ α↦t PE.refl) =
    A , α↦t , refl (W.wk (W.wk₀∷ʷ⊇ ⊢Γ) (wf-↦∈ α↦t (defn-wf ⊢Γ)))
  inversion-defn (conv ⊢α eq) =
    let A , α↦t , A≡A′ = inversion-defn ⊢α
    in  A , α↦t , trans (sym eq) A≡A′

------------------------------------------------------------------------
-- Inversion for Level

opaque

  -- Inversion for sucᵘ.

  inversion-sucᵘ :
    Γ ⊢ sucᵘ t ∷ A →
    Γ ⊢ t ∷ Level × Γ ⊢ A ≡ Level
  inversion-sucᵘ (sucᵘⱼ ⊢t) =
    let ok = inversion-Level-⊢ (wf-⊢ ⊢t) in
    ⊢t , refl (Levelⱼ′ ok (wf ⊢t))
  inversion-sucᵘ (conv ⊢sucᵘ eq) =
    let ⊢t , A≡ = inversion-sucᵘ ⊢sucᵘ in
    ⊢t , trans (sym eq) A≡

opaque

  -- Inversion for sucᵘ.

  inversion-sucᵘ-⊢ :
    Γ ⊢ sucᵘ t →
    Γ ⊢ t ∷ Level × ∃ λ l → Γ ⊢ U l ≡ Level
  inversion-sucᵘ-⊢ (univ ⊢sucᵘ) =
    let ⊢t , U≡Level = inversion-sucᵘ ⊢sucᵘ in
    ⊢t , _ , U≡Level

opaque

  -- Inversion for 1ᵘ+.

  inversion-1ᵘ+-⊢∷L :
    Γ ⊢ 1ᵘ+ l ∷Level →
    Γ ⊢ l ∷Level
  inversion-1ᵘ+-⊢∷L {l = level _} (term ok ⊢sucᵘ) =
    term ok (inversion-sucᵘ ⊢sucᵘ .proj₁)
  inversion-1ᵘ+-⊢∷L {l = level _} (literal ok ⊢Γ) =
    literal
      (Allowed-literal-level-⇔ .proj₂ $
       Σ.map (Level-literal-1ᵘ+-⇔ .proj₁) idᶠ $
       Allowed-literal-level-⇔ .proj₁ ok)
      ⊢Γ
  inversion-1ᵘ+-⊢∷L {l = ωᵘ+ _} (literal ok ⊢Γ) =
    literal
      (Allowed-literal-ωᵘ+-⇔ .proj₂ $
       Allowed-literal-ωᵘ+-⇔ .proj₁ ok)
      ⊢Γ

opaque

  -- Inversion for 1ᵘ+ⁿ.

  inversion-1ᵘ+ⁿ : ∀ n → Γ ⊢ 1ᵘ+ⁿ n l ∷Level → Γ ⊢ l ∷Level
  inversion-1ᵘ+ⁿ 0      = idᶠ
  inversion-1ᵘ+ⁿ (1+ n) = inversion-1ᵘ+ⁿ n ∘→ inversion-1ᵘ+-⊢∷L

opaque
  unfolding ↓ᵘ_

  -- Inversion for ↓ᵘ_.

  inversion-↓ᵘ : Γ ⊢ ↓ᵘ n ∷ A → Γ ⊢ A ≡ Level
  inversion-↓ᵘ {n = 0}    = inversion-zeroᵘ
  inversion-↓ᵘ {n = 1+ _} = proj₂ ∘→ inversion-sucᵘ

opaque
  unfolding ↓ᵘ_

  -- Inversion for ↓ᵘ_.

  inversion-↓ᵘ-⊢ : Γ ⊢ (↓ᵘ n) → ∃ λ l → Γ ⊢ U l ≡ Level
  inversion-↓ᵘ-⊢ {n = 0}    = inversion-zeroᵘ-⊢
  inversion-↓ᵘ-⊢ {n = 1+ _} = proj₂ ∘→ inversion-sucᵘ-⊢

opaque

  -- Inversion for supᵘ.

  inversion-supᵘ :
    Γ ⊢ t₁ supᵘ t₂ ∷ A →
    Γ ⊢ t₁ ∷ Level × Γ ⊢ t₂ ∷ Level × Γ ⊢ A ≡ Level
  inversion-supᵘ (supᵘⱼ ⊢t₁ ⊢t₂) =
    let ok = inversion-Level-⊢ (wf-⊢ ⊢t₁) in
    ⊢t₁ , ⊢t₂ , refl (Levelⱼ′ ok (wf ⊢t₁))
  inversion-supᵘ (conv ⊢supᵘ eq) =
    let ⊢t₁ , ⊢t₂ , A≡ = inversion-supᵘ ⊢supᵘ in
    ⊢t₁ , ⊢t₂ , trans (sym eq) A≡

opaque

  -- Inversion for supᵘ.

  inversion-supᵘ-⊢ :
    Γ ⊢ t₁ supᵘ t₂ →
    Γ ⊢ t₁ ∷ Level × Γ ⊢ t₂ ∷ Level × ∃ λ l → Γ ⊢ U l ≡ Level
  inversion-supᵘ-⊢ (univ eq) =
    let ⊢t₁ , ⊢t₂ , U≡Level = inversion-supᵘ eq in
    ⊢t₁ , ⊢t₂ , _ , U≡Level

opaque
  unfolding _supᵘₗ′_

  -- Inversion for _supᵘₗ′_.

  inversion-supᵘₗ′-⊢∷ :
    Γ ⊢ t₁ supᵘₗ′ t₂ ∷ A →
    Γ ⊢ t₁ ∷ Level × Γ ⊢ t₂ ∷ Level × Γ ⊢ A ≡ Level
  inversion-supᵘₗ′-⊢∷ {t₁} {t₂} ⊢sup
    with Level-literal? t₁ ×-dec Level-literal? t₂
  … | no _ =
    inversion-supᵘ ⊢sup
  … | yes (t₁-lit , t₂-lit) =
    let ≡Level = inversion-↓ᵘ ⊢sup
        ok     = inversion-Level-⊢ (wf-⊢ ≡Level .proj₂)
        ⊢Γ     = wf ≡Level
    in
    ⊢∷Level→⊢∷Level ok (Level-literal→⊢∷L ⊢Γ (level t₁-lit) (λ ())) ,
    ⊢∷Level→⊢∷Level ok (Level-literal→⊢∷L ⊢Γ (level t₂-lit) (λ ())) ,
    ≡Level

opaque
  unfolding _supᵘₗ_

  -- Inversion for _supᵘₗ_.

  inversion-supᵘₗ-⊢∷ :
    Γ ⊢ t₁ supᵘₗ t₂ ∷ A →
    Γ ⊢ t₁ ∷ Level × Γ ⊢ t₂ ∷ Level × Γ ⊢ A ≡ Level
  inversion-supᵘₗ-⊢∷ ⊢sup with level-support
  … | only-literals = inversion-supᵘₗ′-⊢∷ ⊢sup
  … | level-type _  = inversion-supᵘ ⊢sup

opaque

  -- Inversion for _supᵘₗ_.

  inversion-supᵘₗ-⊢ :
    Γ ⊢ t₁ supᵘₗ t₂ →
    Γ ⊢ t₁ ∷ Level × Γ ⊢ t₂ ∷ Level × (∃ λ l → Γ ⊢ U l ≡ Level)
  inversion-supᵘₗ-⊢ ⊢sup = inversion-supᵘₗ-⊢′ ⊢sup PE.refl
    where
    inversion-supᵘₗ-⊢′ :
      Γ ⊢ A → t₁ supᵘₗ t₂ PE.≡ A →
      Γ ⊢ t₁ ∷ Level × Γ ⊢ t₂ ∷ Level × (∃ λ l → Γ ⊢ U l ≡ Level)
    inversion-supᵘₗ-⊢′ (Levelⱼ _ _) eq =
      ⊥-elim (supᵘₗ≢Level eq)
    inversion-supᵘₗ-⊢′ (univ ⊢sup) PE.refl =
      let ⊢t₁ , ⊢t₂ , ≡Level = inversion-supᵘₗ-⊢∷ ⊢sup in
      ⊢t₁ , ⊢t₂ , _ , ≡Level
    inversion-supᵘₗ-⊢′ (Liftⱼ _ _) eq =
      ⊥-elim (supᵘₗ≢Lift eq)
    inversion-supᵘₗ-⊢′ (ΠΣⱼ _ _) eq =
      ⊥-elim (supᵘₗ≢ΠΣ eq)
    inversion-supᵘₗ-⊢′ (Idⱼ _ _ _) eq =
      ⊥-elim (supᵘₗ≢Id eq)

opaque
  unfolding _supᵘₗ_

  -- An inversion lemma for _supᵘₗ_ for terms.
  --
  -- Full inversion does not necessarily hold for _supᵘₗ_, see
  -- Definition.Typed.Consequences.Inversion.¬-inversion-supᵘₗ.

  inversion-supᵘₗ-level :
    Γ ⊢ level (t₁ supᵘₗ t₂) ∷Level →
    Γ ⊢ level t₁ ∷Level × Γ ⊢ level t₂ ∷Level
  inversion-supᵘₗ-level {t₁} {t₂} (term {t} ok ⊢t) =
    let ⊢t₁ , ⊢t₂ , _ =
          inversion-supᵘ $
          PE.subst (flip (_⊢_∷_ _) _)
            (level-PE-injectivity
               (level t                  ≡⟨⟩
                level t₁ supᵘₗ level t₂  ≡⟨ supᵘₗ≡supᵘ ok ⟩
                level (t₁ supᵘ t₂)       ∎))
            ⊢t
    in
    term ok ⊢t₁ , term ok ⊢t₂
  inversion-supᵘₗ-level (literal ok ⊢Γ) =
    let not-ok , t₁-lit , t₂-lit =
          Level-literal-supᵘₗ-level-→ (Allowed-literal→Level-literal ok)
    in
    literal (Allowed-literal-level-⇔ .proj₂ (t₁-lit , not-ok)) ⊢Γ ,
    literal (Allowed-literal-level-⇔ .proj₂ (t₂-lit , not-ok)) ⊢Γ

opaque
  unfolding _supᵘₗ_

  -- An inversion lemma for _supᵘₗ_.
  --
  -- Full inversion does not necessarily hold for _supᵘₗ_, see
  -- Definition.Typed.Consequences.Inversion.¬-inversion-supᵘₗ.

  inversion-supᵘₗ :
    Γ ⊢ l₁ supᵘₗ l₂ ∷Level →
    l₁ supᵘₗ l₂ PE.≡ l₁ × Γ ⊢ l₁ ∷Level ⊎
    l₁ supᵘₗ l₂ PE.≡ l₂ × Γ ⊢ l₂ ∷Level ⊎
    Γ ⊢ l₁ ∷Level × Γ ⊢ l₂ ∷Level
  inversion-supᵘₗ {l₁ = ωᵘ+ m₁} {l₂ = ωᵘ+ m₂} ⊢⊔ with N.≤-total m₁ m₂
  … | inj₁ m₁≤m₂ =
    let eq = PE.cong ωᵘ+ (m≤n⇒m⊔n≡n m₁≤m₂) in
    inj₂ (inj₁ (eq , PE.subst (_⊢_∷Level _) eq ⊢⊔))
  … | inj₂ m₂≤m₁ =
    let eq = PE.cong ωᵘ+ (m≥n⇒m⊔n≡m m₂≤m₁) in
    inj₁ (eq , PE.subst (_⊢_∷Level _) eq ⊢⊔)
  inversion-supᵘₗ {l₁ = ωᵘ+ _} {l₂ = level _} ⊢⊔ =
    inj₁ (PE.refl , ⊢⊔)
  inversion-supᵘₗ {l₁ = level _} {l₂ = ωᵘ+ _} ⊢⊔ =
    inj₂ (inj₁ (PE.refl , ⊢⊔))
  inversion-supᵘₗ {l₁ = level _} {l₂ = level _} ⊢⊔ =
    inj₂ (inj₂ (inversion-supᵘₗ-level ⊢⊔))

opaque

  -- Inversion for ωᵘ+.

  inversion-ωᵘ+ :
    Γ ⊢ ωᵘ+ m ∷Level →
    Omega-plus-allowed × ⊢ Γ
  inversion-ωᵘ+ (literal ok ⊢Γ) =
    Allowed-literal-ωᵘ+-⇔ .proj₁ ok , ⊢Γ

opaque

  -- Inversion for level.

  inversion-level :
    Γ ⊢ level t ∷Level →
    Level-allowed × Γ ⊢ t ∷ Level ⊎
    ¬ Level-allowed × Level-literal t × ⊢ Γ
  inversion-level (term ok ⊢t) =
    inj₁ (ok , ⊢t)
  inversion-level (literal ok ⊢Γ) =
    let not-ok , lit = Allowed-literal-level-⇔ .proj₁ ok in
    inj₂ (lit , not-ok , ⊢Γ)

------------------------------------------------------------------------
-- Inversion for Lift

opaque

  -- Inversion for lower.

  inversion-lower : Γ ⊢ lower t ∷ A → ∃₂ λ l B → Γ ⊢ t ∷ Lift l B × Γ ⊢ A ≡ B
  inversion-lower (conv x x₁) =
    let _ , _ , ⊢t , A≡B = inversion-lower x
    in _ , _ , ⊢t , trans (sym x₁) A≡B
  inversion-lower (lowerⱼ x) = _ , _ , x , refl (inversion-Lift (wf-⊢ x) .proj₂)

------------------------------------------------------------------------
-- Inversion for Unit

opaque

  -- If a term has type Unit s l, then Unit-allowed s holds.

  ⊢∷Unit→Unit-allowed : Γ ⊢ t ∷ Unit s → Unit-allowed s
  ⊢∷Unit→Unit-allowed {Γ} {t} {s} =
    Γ ⊢ t ∷ Unit s  →⟨ wf-⊢ ⟩
    Γ ⊢ Unit s      →⟨ inversion-Unit ⟩
    Unit-allowed s  □

opaque

  -- Inversion for unitrec.

  inversion-unitrec :
    Γ ⊢ unitrec p q A t u ∷ B →
    (Γ »∙ Unitʷ ⊢ A) ×
    Γ ⊢ t ∷ Unitʷ ×
    Γ ⊢ u ∷ A [ starʷ ]₀ ×
    Γ ⊢ B ≡ A [ t ]₀
  inversion-unitrec (unitrecⱼ ⊢A ⊢t ⊢u) =
    ⊢A , ⊢t , ⊢u , refl (subst-⊢₀ ⊢A ⊢t)
  inversion-unitrec (conv ⊢ur eq) =
    let a , b , c , d = inversion-unitrec ⊢ur
    in  a , b , c , trans (sym eq) d

------------------------------------------------------------------------
-- Inversion for Π and Σ

opaque

  -- If a term has type ΠΣ⟨ b ⟩ p , q ▷ A ▹ B, then ΠΣ-allowed b p q
  -- holds.

  ⊢∷ΠΣ→ΠΣ-allowed :
    Γ ⊢ t ∷ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B → ΠΣ-allowed b p q
  ⊢∷ΠΣ→ΠΣ-allowed {Γ} {t} {b} {p} {q} {A} {B} =
    Γ ⊢ t ∷ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B  →⟨ wf-⊢ ⟩
    Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B      →⟨ proj₂ ∘→ proj₂ ∘→ inversion-ΠΣ ⟩
    ΠΣ-allowed b p q               □

opaque

  -- Inversion for lam.

  inversion-lam :
    Γ ⊢ lam p t ∷ A →
    ∃₃ λ B C q →
      (Γ ⊢ B) × Γ »∙ B ⊢ t ∷ C ×
      Γ ⊢ A ≡ Π p , q ▷ B ▹ C ×
      Π-allowed p q
  inversion-lam (lamⱼ _ ⊢t ok) =
    let ⊢B = wf-⊢ ⊢t in
    _ , _ , _ , ⊢∙→⊢ (wf ⊢B) , ⊢t , refl (ΠΣⱼ ⊢B ok) , ok
  inversion-lam (conv ⊢lam eq) =
    let a , b , c , d , e , f , g = inversion-lam ⊢lam in
    a , b , c , d , e , trans (sym eq) f , g

opaque

  -- Inversion for _∘⟨_⟩_.

  inversion-app :
    Γ ⊢ t ∘⟨ p ⟩ u ∷ A →
    ∃₃ λ B C q → Γ ⊢ t ∷ Π p , q ▷ B ▹ C × Γ ⊢ u ∷ B × Γ ⊢ A ≡ C [ u ]₀
  inversion-app (⊢t ∘ⱼ ⊢u) =
    _ , _ , _ , ⊢t , ⊢u , refl (substTypeΠ (wf-⊢ ⊢t) ⊢u)
  inversion-app (conv ⊢app eq) =
    let a , b , c , d , e , f = inversion-app ⊢app in
    a , b , c , d , e , trans (sym eq) f

opaque

  -- Inversion for snd.

  inversion-snd :
    Γ ⊢ snd p t ∷ A →
    ∃₃ λ B C q →
      (Γ ⊢ B) × (Γ »∙ B ⊢ C) ×
      Γ ⊢ t ∷ Σˢ p , q ▷ B ▹ C ×
      Γ ⊢ A ≡ C [ fst p t ]₀
  inversion-snd (sndⱼ ⊢C ⊢t) =
    _ , _ , _ , ⊢∙→⊢ (wf ⊢C) , ⊢C , ⊢t ,
    refl (subst-⊢₀ ⊢C (fstⱼ ⊢C ⊢t))
  inversion-snd (conv ⊢snd eq) =
    let a , b , c , d , e , f , g = inversion-snd ⊢snd in
    a , b , c , d , e , f , trans (sym eq) g

opaque

  -- Inversion for prodrec.

  inversion-prodrec :
    Γ ⊢ prodrec r p q′ A t u ∷ B →
    ∃₃ λ C D q →
      (Γ ⊢ C) × (Γ »∙ C ⊢ D) ×
      (Γ »∙ Σʷ p , q ▷ C ▹ D ⊢ A) ×
      Γ ⊢ t ∷ Σʷ p , q ▷ C ▹ D ×
      Γ »∙ C »∙ D ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² ×
      Γ ⊢ B ≡ A [ t ]₀
  inversion-prodrec (prodrecⱼ ⊢A ⊢t ⊢u) =
    let ⊢D = ⊢∙→⊢ (wf ⊢u) in
    _ , _ , _ , ⊢∙→⊢ (wf ⊢D) , ⊢D , ⊢A , ⊢t , ⊢u ,
    refl (subst-⊢₀ ⊢A ⊢t)
  inversion-prodrec (conv ⊢pr eq) =
    let a , b , c , d , e , f , g , h , i = inversion-prodrec ⊢pr in
    a , b , c , d , e , f , g , h , trans (sym eq) i

------------------------------------------------------------------------
-- Inversion for ℕ

opaque

  -- Inversion for natrec.

  inversion-natrec :
    Γ ⊢ natrec p q r A t u v ∷ B →
    (Γ »∙ ℕ ⊢ A) ×
    Γ ⊢ t ∷ A [ zero ]₀ ×
    Γ »∙ ℕ »∙ A ⊢ u ∷ A [ suc (var x1) ]↑² ×
    Γ ⊢ v ∷ ℕ ×
    Γ ⊢ B ≡ A [ v ]₀
  inversion-natrec (natrecⱼ ⊢t ⊢u ⊢v) =
    let ⊢A = ⊢∙→⊢ (wf ⊢u) in
    ⊢A , ⊢t , ⊢u , ⊢v , refl (subst-⊢₀ ⊢A ⊢v)
  inversion-natrec (conv ⊢nr eq) =
    let a , b , c , d , e = inversion-natrec ⊢nr in
    a , b , c , d , trans (sym eq) e

------------------------------------------------------------------------
-- Inversion for Id

opaque

  -- Inversion for Id.

  inversion-Id-U :
    Γ ⊢ Id A t u ∷ B →
    ∃ λ l → Γ ⊢ A ∷ U l × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A × Γ ⊢ B ≡ U l
  inversion-Id-U = λ where
    (Idⱼ ⊢A ⊢t ⊢u) →
      _ , ⊢A , ⊢t , ⊢u ,
      refl (⊢U (inversion-U-Level (wf-⊢ ⊢A)))
    (conv ⊢Id C≡B) →
      case inversion-Id-U ⊢Id of λ {
        (_ , ⊢A , ⊢t , ⊢u , C≡U) →
      _ , ⊢A , ⊢t , ⊢u , trans (sym C≡B) C≡U }

opaque

  -- A variant of inversion-Id-U.

  inversion-Id∷U :
    Γ ⊢ Id A t u ∷ U l →
    Γ ⊢ A ∷ U l × Γ ⊢ t ∷ A × Γ ⊢ u ∷ A
  inversion-Id∷U ⊢Id =
    let _ , ⊢A , ⊢t , ⊢u , ≡U = inversion-Id-U ⊢Id in
    conv ⊢A (sym ≡U) , ⊢t , ⊢u

opaque

  -- Inversion for rfl.

  inversion-rfl :
    Γ ⊢ rfl ∷ A →
    ∃₂ λ B t → (Γ ⊢ B) × Γ ⊢ t ∷ B × Γ ⊢ A ≡ Id B t t
  inversion-rfl = λ where
    ⊢rfl@(rflⱼ ⊢t)  →
      _ , _ , wf-⊢ ⊢t , ⊢t , refl (wf-⊢ ⊢rfl)
    (conv ⊢rfl eq) →
      let a , b , c , d , e = inversion-rfl ⊢rfl in
      a , b , c , d , trans (sym eq) e

opaque

  -- Inversion for J.

  inversion-J :
    Γ ⊢ J p q A t B u v w ∷ C →
    (Γ ⊢ A) ×
    Γ ⊢ t ∷ A ×
    (Γ »∙ A »∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B) ×
    Γ ⊢ u ∷ B [ t , rfl ]₁₀ ×
    Γ ⊢ v ∷ A ×
    Γ ⊢ w ∷ Id A t v ×
    Γ ⊢ C ≡ B [ v , w ]₁₀
  inversion-J = λ where
    ⊢J@(Jⱼ ⊢t ⊢B ⊢u ⊢v ⊢w) →
      ⊢∙→⊢ (wf (⊢∙→⊢ (wf ⊢B))) , ⊢t , ⊢B , ⊢u , ⊢v , ⊢w ,
      refl (wf-⊢ ⊢J)
    (conv ⊢J eq) →
      let a , b , c , d , e , f , g = inversion-J ⊢J in
      a , b , c , d , e , f , trans (sym eq) g

opaque

  -- Inversion for K.

  inversion-K :
    Γ ⊢ K p A t B u v ∷ C →
    (Γ ⊢ A) ×
    Γ ⊢ t ∷ A ×
    (Γ »∙ Id A t t ⊢ B) ×
    Γ ⊢ u ∷ B [ rfl ]₀ ×
    Γ ⊢ v ∷ Id A t t ×
    K-allowed ×
    Γ ⊢ C ≡ B [ v ]₀
  inversion-K = λ where
    ⊢K@(Kⱼ ⊢B ⊢u ⊢v ok) →
        let ⊢A , ⊢t , _ = inversion-Id (⊢∙→⊢ (wf ⊢B)) in
        ⊢A , ⊢t , ⊢B , ⊢u , ⊢v , ok
      , refl (wf-⊢ ⊢K)
    (conv ⊢K eq) →
      let a , b , c , d , e , f , g = inversion-K ⊢K in
      a , b , c , d , e , f , trans (sym eq) g

opaque

  -- Inversion for []-cong.

  inversion-[]-cong :
    Γ ⊢ []-cong s l A t u v ∷ B →
    let open Erased s in
      Γ ⊢ l ∷Level ×
      (Γ ⊢ A) ×
      Γ ⊢ t ∷ A ×
      Γ ⊢ u ∷ A ×
      Γ ⊢ v ∷ Id A t u ×
      []-cong-allowed s ×
      Γ ⊢ B ≡ Id (Erased l A) ([ t ]) ([ u ])
  inversion-[]-cong = λ where
    ⊢[]-cong@([]-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v ok) →
        ⊢l , ⊢A , ⊢t , ⊢u , ⊢v , ok
      , refl (wf-⊢ ⊢[]-cong)
    (conv ⊢bc eq) →
      let a , b , c , d , e , f , g = inversion-[]-cong ⊢bc in
      a , b , c , d , e , f , trans (sym eq) g
