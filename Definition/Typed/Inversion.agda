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
open import Definition.Typed.Syntactic R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased
open import Definition.Untyped.Sup R

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

open I public

private variable
  α n                   : Nat
  x                     : Fin _
  Γ                     : Cons _ _
  A B C l l₁ l₂ t u v w : Term _
  b                     : BinderMode
  s                     : Strength
  p q q′ r              : M

------------------------------------------------------------------------
-- Inversion for variables

opaque

  -- Inversion for var.

  inversion-var : Γ ⊢ var x ∷ A → ∃ λ B → x ∷ B ∈ Γ .vars × Γ ⊢ A ≡ B
  inversion-var ⊢x@(var _ x∈) =
    _ , x∈ , refl (syntacticTerm ⊢x)
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
    Γ ⊢ sucᵘ l ∷ A →
    Γ ⊢ l ∷ Level × Γ ⊢ A ≡ Level
  inversion-sucᵘ (sucᵘⱼ ⊢l) =
    let ok = inversion-Level-⊢ (wf-⊢∷ ⊢l) in
    ⊢l , refl (Levelⱼ′ ok (wfTerm ⊢l))
  inversion-sucᵘ (conv ⊢sucᵘ eq) =
    let ⊢l , A≡ = inversion-sucᵘ ⊢sucᵘ in
    ⊢l , trans (sym eq) A≡

opaque

  -- Inversion for sucᵘ.

  inversion-sucᵘ-⊢ :
    Γ ⊢ sucᵘ l →
    Γ ⊢ l ∷ Level × ∃ λ l′ → Γ ⊢ U l′ ≡ Level
  inversion-sucᵘ-⊢ (univ ⊢sucᵘ) =
    let ⊢l , U≡Level = inversion-sucᵘ ⊢sucᵘ in
    ⊢l , _ , U≡Level

opaque

  -- Inversion for sucᵘ.

  inversion-sucᵘ-⊢∷L :
    Γ ⊢ sucᵘ l ∷Level →
    Γ ⊢ l ∷Level
  inversion-sucᵘ-⊢∷L (term ok ⊢sucᵘ) =
    term ok (inversion-sucᵘ ⊢sucᵘ .proj₁)
  inversion-sucᵘ-⊢∷L (literal not-ok ⊢Γ (sucᵘ l-lit)) =
    literal not-ok ⊢Γ l-lit

opaque

  -- Inversion for sucᵘᵏ.

  inversion-sucᵘᵏ-⊢∷L : Γ ⊢ sucᵘᵏ n l ∷Level → Γ ⊢ l ∷Level
  inversion-sucᵘᵏ-⊢∷L {n = 0}    = idᶠ
  inversion-sucᵘᵏ-⊢∷L {n = 1+ _} =
    inversion-sucᵘᵏ-⊢∷L ∘→ inversion-sucᵘ-⊢∷L

opaque

  -- Inversion for ↓ᵘ_.

  inversion-↓ᵘ : Γ ⊢ ↓ᵘ n ∷ A → Γ ⊢ A ≡ Level
  inversion-↓ᵘ {n = 0}    = inversion-zeroᵘ
  inversion-↓ᵘ {n = 1+ _} = proj₂ ∘→ inversion-sucᵘ

opaque

  -- Inversion for ↓ᵘ_.

  inversion-↓ᵘ-⊢ : Γ ⊢ (↓ᵘ n) → ∃ λ l → Γ ⊢ U l ≡ Level
  inversion-↓ᵘ-⊢ {n = 0}    = inversion-zeroᵘ-⊢
  inversion-↓ᵘ-⊢ {n = 1+ _} = proj₂ ∘→ inversion-sucᵘ-⊢

opaque

  -- Inversion for supᵘ.

  inversion-supᵘ :
    Γ ⊢ l₁ supᵘ l₂ ∷ A →
    Γ ⊢ l₁ ∷ Level × Γ ⊢ l₂ ∷ Level × Γ ⊢ A ≡ Level
  inversion-supᵘ (supᵘⱼ ⊢l₁ ⊢l₂) =
    let ok = inversion-Level-⊢ (wf-⊢∷ ⊢l₁) in
    ⊢l₁ , ⊢l₂ , refl (Levelⱼ′ ok (wfTerm ⊢l₁))
  inversion-supᵘ (conv ⊢supᵘ eq) =
    let ⊢l₁ , ⊢l₂ , A≡ = inversion-supᵘ ⊢supᵘ in
    ⊢l₁ , ⊢l₂ , trans (sym eq) A≡

opaque

  -- Inversion for supᵘ.

  inversion-supᵘ-⊢ :
    Γ ⊢ l₁ supᵘ l₂ →
    Γ ⊢ l₁ ∷ Level × Γ ⊢ l₂ ∷ Level × ∃ λ l → Γ ⊢ U l ≡ Level
  inversion-supᵘ-⊢ (univ eq) =
    let ⊢l₁ , ⊢l₂ , U≡Level = inversion-supᵘ eq in
    ⊢l₁ , ⊢l₂ , _ , U≡Level

opaque
  unfolding _supᵘₗ′_

  -- Inversion for _supᵘₗ′_.

  inversion-supᵘₗ′-⊢∷ :
    Γ ⊢ l₁ supᵘₗ′ l₂ ∷ A →
    Γ ⊢ l₁ ∷ Level × Γ ⊢ l₂ ∷ Level × Γ ⊢ A ≡ Level
  inversion-supᵘₗ′-⊢∷ {l₁} {l₂} ⊢sup
    with Level-literal? l₁ ×-dec Level-literal? l₂
  … | no _ =
    inversion-supᵘ ⊢sup
  … | yes (l₁-lit , l₂-lit) =
    let ≡Level = inversion-↓ᵘ ⊢sup
        ok     = inversion-Level-⊢ (wf-⊢≡ ≡Level .proj₂)
        ⊢Γ     = wfEq ≡Level
    in
    ⊢∷Level→⊢∷Level ok (Level-literal→⊢∷Level ⊢Γ l₁-lit) ,
    ⊢∷Level→⊢∷Level ok (Level-literal→⊢∷Level ⊢Γ l₂-lit) ,
    ≡Level

opaque
  unfolding _supᵘₗ_

  -- Inversion for _supᵘₗ_.

  inversion-supᵘₗ-⊢∷ :
    Γ ⊢ l₁ supᵘₗ l₂ ∷ A →
    Γ ⊢ l₁ ∷ Level × Γ ⊢ l₂ ∷ Level × Γ ⊢ A ≡ Level
  inversion-supᵘₗ-⊢∷ ⊢sup with level-support
  … | only-literals = inversion-supᵘₗ′-⊢∷ ⊢sup
  … | level-type _  = inversion-supᵘ ⊢sup

opaque

  -- Inversion for _supᵘₗ_.

  inversion-supᵘₗ-⊢ :
    Γ ⊢ l₁ supᵘₗ l₂ →
    Γ ⊢ l₁ ∷ Level × Γ ⊢ l₂ ∷ Level × (∃ λ l → Γ ⊢ U l ≡ Level)
  inversion-supᵘₗ-⊢ ⊢sup = inversion-supᵘₗ-⊢′ ⊢sup PE.refl
    where
    inversion-supᵘₗ-⊢′ :
      Γ ⊢ A → l₁ supᵘₗ l₂ PE.≡ A →
      Γ ⊢ l₁ ∷ Level × Γ ⊢ l₂ ∷ Level × (∃ λ l → Γ ⊢ U l ≡ Level)
    inversion-supᵘₗ-⊢′ (Levelⱼ _ _) eq =
      ⊥-elim (supᵘₗ≢Level eq)
    inversion-supᵘₗ-⊢′ (univ ⊢sup) PE.refl =
      let ⊢l₁ , ⊢l₂ , ≡Level = inversion-supᵘₗ-⊢∷ ⊢sup in
      ⊢l₁ , ⊢l₂ , _ , ≡Level
    inversion-supᵘₗ-⊢′ (Liftⱼ _ _) eq =
      ⊥-elim (supᵘₗ≢Lift eq)
    inversion-supᵘₗ-⊢′ (ΠΣⱼ _ _) eq =
      ⊥-elim (supᵘₗ≢ΠΣ eq)
    inversion-supᵘₗ-⊢′ (Idⱼ _ _ _) eq =
      ⊥-elim (supᵘₗ≢Id eq)

opaque

  -- Inversion for supᵘₗ.

  inversion-supᵘₗ :
    Γ ⊢ l₁ supᵘₗ l₂ ∷Level →
    Γ ⊢ l₁ ∷Level × Γ ⊢ l₂ ∷Level
  inversion-supᵘₗ (term ok ⊢sup) =
    let ⊢l₁ , ⊢l₂ , _ =
          inversion-supᵘ $
          PE.subst (flip (_⊢_∷_ _) _) (supᵘₗ≡supᵘ ok) ⊢sup
    in
    term ok ⊢l₁ , term ok ⊢l₂
  inversion-supᵘₗ (literal not-ok ⊢Γ sup-lit) =
    let l₁-lit , l₂-lit = Level-literal-supᵘₗ⇔ not-ok .proj₁ sup-lit in
    literal not-ok ⊢Γ l₁-lit , literal not-ok ⊢Γ l₂-lit

------------------------------------------------------------------------
-- Inversion for Lift

opaque

  -- Inversion for lower.

  inversion-lower : Γ ⊢ lower t ∷ A → ∃₂ λ l B → Γ ⊢ t ∷ Lift l B × Γ ⊢ A ≡ B
  inversion-lower (conv x x₁) =
    let _ , _ , ⊢t , A≡B = inversion-lower x
    in _ , _ , ⊢t , trans (sym x₁) A≡B
  inversion-lower (lowerⱼ x) = _ , _ , x , refl (inversion-Lift (syntacticTerm x) .proj₂)

------------------------------------------------------------------------
-- Inversion for Unit

opaque

  -- If a term has type Unit s l, then Unit-allowed s holds.

  ⊢∷Unit→Unit-allowed : Γ ⊢ t ∷ Unit s → Unit-allowed s
  ⊢∷Unit→Unit-allowed {Γ} {t} {s} =
    Γ ⊢ t ∷ Unit s  →⟨ syntacticTerm ⟩
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
  inversion-unitrec (unitrecⱼ ⊢A ⊢t ⊢u _) =
    ⊢A , ⊢t , ⊢u , refl (substType ⊢A ⊢t)
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
    Γ ⊢ t ∷ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B  →⟨ syntacticTerm ⟩
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
    let ⊢B = syntacticTerm ⊢t in
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
    _ , _ , _ , ⊢t , ⊢u , refl (substTypeΠ (syntacticTerm ⊢t) ⊢u)
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
    refl (substType ⊢C (fstⱼ ⊢C ⊢t))
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
  inversion-prodrec (prodrecⱼ ⊢A ⊢t ⊢u _) =
    let ⊢D = ⊢∙→⊢ (wfTerm ⊢u) in
    _ , _ , _ , ⊢∙→⊢ (wf ⊢D) , ⊢D , ⊢A , ⊢t , ⊢u ,
    refl (substType ⊢A ⊢t)
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
    let ⊢A = ⊢∙→⊢ (wfTerm ⊢u) in
    ⊢A , ⊢t , ⊢u , ⊢v , refl (substType ⊢A ⊢v)
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
      refl (⊢U (inversion-U-Level (wf-⊢∷ ⊢A)))
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
      _ , _ , syntacticTerm ⊢t , ⊢t , refl (syntacticTerm ⊢rfl)
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
      refl (syntacticTerm ⊢J)
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
      , refl (syntacticTerm ⊢K)
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
      , refl (syntacticTerm ⊢[]-cong)
    (conv ⊢bc eq) →
      let a , b , c , d , e , f , g = inversion-[]-cong ⊢bc in
      a , b , c , d , e , f , trans (sym eq) g
