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
open import Definition.Typed.Properties.Well-formed R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Syntactic R
import Definition.Typed.Weakening R as W
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
import Definition.Untyped.Erased 𝕄 as Erased

open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

open I public

private variable
  ∇             : DCon (Term 0) _
  x             : Fin _
  α             : Nat
  Γ             : Con Term _
  A B C t u v w : Term _
  b             : BinderMode
  l             : Universe-level
  s             : Strength
  p q q′ r      : M

------------------------------------------------------------------------
-- Inversion for variables

opaque

  -- Inversion for var.

  inversion-var : ∇ » Γ ⊢ var x ∷ A → ∃ λ B → x ∷ B ∈ Γ × ∇ » Γ ⊢ A ≡ B
  inversion-var ⊢x@(var _ x∈) =
    _ , x∈ , refl (syntacticTerm ⊢x)
  inversion-var (conv ⊢var eq) =
    let a , b , c = inversion-var ⊢var in
    a , b , trans (sym eq) c

------------------------------------------------------------------------
-- Inversion for definitions

opaque

  -- Inversion for defn.

  inversion-defn : ∇ » Γ ⊢ defn α ∷ A
                 → ∃ λ A′ → α ↦∷ A′ ∈ ∇ × (∇ » Γ ⊢ A ≡ wk wk₀ A′)
  inversion-defn (defn {A′ = A} ⊢Γ α↦t PE.refl) =
    A , α↦t , refl (W.wk (W.wk₀∷ʷ⊇ ⊢Γ) (wf-↦∈ α↦t (defn-wf ⊢Γ)))
  inversion-defn (conv ⊢α eq) =
    let A , α↦t , A≡A′ = inversion-defn ⊢α
    in  A , α↦t , trans (sym eq) A≡A′

------------------------------------------------------------------------
-- Inversion for Unit

opaque

  -- If a term has type Unit s l, then Unit-allowed s holds.

  ⊢∷Unit→Unit-allowed : ∇ » Γ ⊢ t ∷ Unit s l → Unit-allowed s
  ⊢∷Unit→Unit-allowed {∇} {Γ} {t} {s} {l} =
    ∇ » Γ ⊢ t ∷ Unit s l  →⟨ syntacticTerm ⟩
    ∇ » Γ ⊢ Unit s l      →⟨ inversion-Unit ⟩
    Unit-allowed s        □

opaque

  -- Inversion for unitrec.

  inversion-unitrec :
    ∇ » Γ ⊢ unitrec l p q A t u ∷ B →
    (∇ » Γ ∙ Unitʷ l ⊢ A) ×
    ∇ » Γ ⊢ t ∷ Unitʷ l ×
    ∇ » Γ ⊢ u ∷ A [ starʷ l ]₀ ×
    ∇ » Γ ⊢ B ≡ A [ t ]₀
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
    ∇ » Γ ⊢ t ∷ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B → ΠΣ-allowed b p q
  ⊢∷ΠΣ→ΠΣ-allowed {∇} {Γ} {t} {b} {p} {q} {A} {B} =
    ∇ » Γ ⊢ t ∷ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B  →⟨ syntacticTerm ⟩
    ∇ » Γ ⊢ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B      →⟨ proj₂ ∘→ proj₂ ∘→ inversion-ΠΣ ⟩
    ΠΣ-allowed b p q                   □

opaque

  -- Inversion for lam.

  inversion-lam :
    ∇ » Γ ⊢ lam p t ∷ A →
    ∃₃ λ B C q →
      (∇ » Γ ⊢ B) × ∇ » Γ ∙ B ⊢ t ∷ C ×
      ∇ » Γ ⊢ A ≡ Π p , q ▷ B ▹ C ×
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
    ∇ » Γ ⊢ t ∘⟨ p ⟩ u ∷ A →
    ∃₃ λ B C q → ∇ » Γ ⊢ t ∷ Π p , q ▷ B ▹ C × ∇ » Γ ⊢ u ∷ B × ∇ » Γ ⊢ A ≡ C [ u ]₀
  inversion-app (⊢t ∘ⱼ ⊢u) =
    _ , _ , _ , ⊢t , ⊢u , refl (substTypeΠ (syntacticTerm ⊢t) ⊢u)
  inversion-app (conv ⊢app eq) =
    let a , b , c , d , e , f = inversion-app ⊢app in
    a , b , c , d , e , trans (sym eq) f

opaque

  -- Inversion for snd.

  inversion-snd :
    ∇ » Γ ⊢ snd p t ∷ A →
    ∃₃ λ B C q →
      (∇ » Γ ⊢ B) × (∇ » Γ ∙ B ⊢ C) ×
      ∇ » Γ ⊢ t ∷ Σˢ p , q ▷ B ▹ C ×
      ∇ » Γ ⊢ A ≡ C [ fst p t ]₀
  inversion-snd (sndⱼ ⊢C ⊢t) =
    _ , _ , _ , ⊢∙→⊢ (wf ⊢C) , ⊢C , ⊢t ,
    refl (substType ⊢C (fstⱼ ⊢C ⊢t))
  inversion-snd (conv ⊢snd eq) =
    let a , b , c , d , e , f , g = inversion-snd ⊢snd in
    a , b , c , d , e , f , trans (sym eq) g

opaque

  -- Inversion for prodrec.

  inversion-prodrec :
    ∇ » Γ ⊢ prodrec r p q′ A t u ∷ B →
    ∃₃ λ C D q →
      (∇ » Γ ⊢ C) × (∇ » Γ ∙ C ⊢ D) ×
      (∇ » Γ ∙ Σʷ p , q ▷ C ▹ D ⊢ A) ×
      ∇ » Γ ⊢ t ∷ Σʷ p , q ▷ C ▹ D ×
      ∇ » Γ ∙ C ∙ D ⊢ u ∷ A [ prodʷ p (var x1) (var x0) ]↑² ×
      ∇ » Γ ⊢ B ≡ A [ t ]₀
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
    ∇ » Γ ⊢ natrec p q r A t u v ∷ B →
    (∇ » Γ ∙ ℕ ⊢ A) ×
    ∇ » Γ ⊢ t ∷ A [ zero ]₀ ×
    ∇ » Γ ∙ ℕ ∙ A ⊢ u ∷ A [ suc (var x1) ]↑² ×
    ∇ » Γ ⊢ v ∷ ℕ ×
    ∇ » Γ ⊢ B ≡ A [ v ]₀
  inversion-natrec (natrecⱼ ⊢t ⊢u ⊢v) =
    let ⊢A = ⊢∙→⊢ (wfTerm ⊢u) in
    ⊢A , ⊢t , ⊢u , ⊢v , refl (substType ⊢A ⊢v)
  inversion-natrec (conv ⊢nr eq) =
    let a , b , c , d , e = inversion-natrec ⊢nr in
    a , b , c , d , trans (sym eq) e

------------------------------------------------------------------------
-- Inversion for Id

opaque

  -- Inversion for rfl.

  inversion-rfl :
    ∇ » Γ ⊢ rfl ∷ A →
    ∃₂ λ B t → (∇ » Γ ⊢ B) × ∇ » Γ ⊢ t ∷ B × ∇ » Γ ⊢ A ≡ Id B t t
  inversion-rfl = λ where
    ⊢rfl@(rflⱼ ⊢t)  →
      _ , _ , syntacticTerm ⊢t , ⊢t , refl (syntacticTerm ⊢rfl)
    (conv ⊢rfl eq) →
      let a , b , c , d , e = inversion-rfl ⊢rfl in
      a , b , c , d , trans (sym eq) e

opaque

  -- Inversion for J.

  inversion-J :
    ∇ » Γ ⊢ J p q A t B u v w ∷ C →
    (∇ » Γ ⊢ A) ×
    ∇ » Γ ⊢ t ∷ A ×
    (∇ » Γ ∙ A ∙ Id (wk1 A) (wk1 t) (var x0) ⊢ B) ×
    ∇ » Γ ⊢ u ∷ B [ t , rfl ]₁₀ ×
    ∇ » Γ ⊢ v ∷ A ×
    ∇ » Γ ⊢ w ∷ Id A t v ×
    ∇ » Γ ⊢ C ≡ B [ v , w ]₁₀
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
    ∇ » Γ ⊢ K p A t B u v ∷ C →
    (∇ » Γ ⊢ A) ×
    ∇ » Γ ⊢ t ∷ A ×
    (∇ » Γ ∙ Id A t t ⊢ B) ×
    ∇ » Γ ⊢ u ∷ B [ rfl ]₀ ×
    ∇ » Γ ⊢ v ∷ Id A t t ×
    K-allowed ×
    ∇ » Γ ⊢ C ≡ B [ v ]₀
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
    ∇ » Γ ⊢ []-cong s A t u v ∷ B →
    let open Erased s in
      (∇ » Γ ⊢ A) ×
      ∇ » Γ ⊢ t ∷ A ×
      ∇ » Γ ⊢ u ∷ A ×
      ∇ » Γ ⊢ v ∷ Id A t u ×
      []-cong-allowed s ×
      ∇ » Γ ⊢ B ≡ Id (Erased A) ([ t ]) ([ u ])
  inversion-[]-cong = λ where
    ⊢[]-cong@([]-congⱼ _ ⊢t ⊢u ⊢v ok) →
        syntacticTerm ⊢t , ⊢t , ⊢u , ⊢v , ok
      , refl (syntacticTerm ⊢[]-cong)
    (conv ⊢bc eq) →
      let a , b , c , d , e , f = inversion-[]-cong ⊢bc in
      a , b , c , d , e , trans (sym eq) f
