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
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased

open import Tools.Fin
open import Tools.Function
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

open I public

private variable
  x                     : Fin _
  Γ                     : Con Term _
  A B C l l₁ l₂ t u v w : Term _
  b                     : BinderMode
  s                     : Strength
  p q q′ r              : M

------------------------------------------------------------------------
-- Inversion for variables

opaque

  -- Inversion for var.

  inversion-var : Γ ⊢ var x ∷ A → ∃ λ B → x ∷ B ∈ Γ × Γ ⊢ A ≡ B
  inversion-var ⊢x@(var _ x∈) =
    _ , x∈ , refl (syntacticTerm ⊢x)
  inversion-var (conv ⊢var eq) =
    let a , b , c = inversion-var ⊢var in
    a , b , trans (sym eq) c

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
    (Γ ∙ Unitʷ ⊢ A) ×
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
      (Γ ⊢ B) × Γ ∙ B ⊢ t ∷ C ×
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
      (Γ ⊢ B) × (Γ ∙ B ⊢ C) ×
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
      (Γ ⊢ C) × (Γ ∙ C ⊢ D) ×
      (Γ ∙ Σʷ p , q ▷ C ▹ D ⊢ A) ×
      Γ ⊢ t ∷ Σʷ p , q ▷ C ▹ D ×
      Γ ∙ C ∙ D ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² ×
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
    (Γ ∙ ℕ ⊢ A) ×
    Γ ⊢ t ∷ A [ zero ]₀ ×
    Γ ∙ ℕ ∙ A ⊢ u ∷ A [ suc (var x1) ]↑² ×
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

  -- If Level is not small, then Id Level t u does not belong to any
  -- universe.

  ¬Level-is-small→¬Id-Level∷U :
    ¬ Level-is-small →
    ¬ Γ ⊢ Id Level t u ∷ U l
  ¬Level-is-small→¬Id-Level∷U not-ok ⊢Id =
    let _ , Level∷U , _ = inversion-Id-U ⊢Id in
    ¬Level-is-small→¬Level∷U not-ok Level∷U

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
    (Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B) ×
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
    (Γ ∙ Id A t t ⊢ B) ×
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
      Γ ⊢ A ∷ U l ×
      Γ ⊢ t ∷ A ×
      Γ ⊢ u ∷ A ×
      Γ ⊢ v ∷ Id A t u ×
      []-cong-allowed s ×
      Γ ⊢ B ≡ Id (Erased l A) ([ t ]) ([ u ])
  inversion-[]-cong = λ where
    ⊢[]-cong@([]-congⱼ _ ⊢A ⊢t ⊢u ⊢v ok) →
        ⊢A , ⊢t , ⊢u , ⊢v , ok
      , refl (syntacticTerm ⊢[]-cong)
    (conv ⊢bc eq) →
      let a , b , c , d , e , f = inversion-[]-cong ⊢bc in
      a , b , c , d , e , trans (sym eq) f
