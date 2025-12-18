------------------------------------------------------------------------
-- Lemmas related to definitions
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Properties.Definition
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties.Admissible.Empty R
open import Definition.Typed.Properties.Admissible.Equality R
open import Definition.Typed.Properties.Admissible.Erased R
open import Definition.Typed.Properties.Admissible.Identity.Primitive R
open import Definition.Typed.Properties.Admissible.Nat R
open import Definition.Typed.Properties.Admissible.Pi R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Admissible.Unit R
open import Definition.Typed.Properties.Admissible.Var R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
import Definition.Typed.Reasoning.Term R as TmR
import Definition.Typed.Reasoning.Type R as TyR
open import Definition.Typed.Stability R
open import Definition.Typed.Substitution.Primitive R
open import Definition.Typed.Weakening R hiding (wk)
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Pi M
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum
open import Tools.Vec using (ε)

open import Definition.Typed.Properties.Definition.Primitive R
  public

private variable
  α l m n n′          : Nat
  x                   : Fin _
  ∇ ∇′                : DCon _ _
  ξ ξ′                : DExt _ _ _
  Γ                   : Con Term _
  A B C t t₁ t₂ u v w : Term _
  ω                   : Opacity _
  φ                   : Unfolding _
  p q                 : M

------------------------------------------------------------------------
-- Some well-formedness lemmas

opaque

  -- If ∇ ∙⟨ ω ⟩[ t ∷ A ] is well-formed, then A is a well-formed
  -- type.

  »∙→⊢ : » ∇ ∙⟨ ω ⟩[ t ∷ A ] → ∇ » ε ⊢ A
  »∙→⊢ ∙ᵒ⟨ _ ⟩[ _ ∷ ⊢A ] = ⊢A
  »∙→⊢ ∙ᵗ[ ⊢t ]          = wf-⊢∷ ⊢t

opaque

  -- If ∇ ∙⟨ ω ⟩[ t ∷ A ] is well-formed, then ∇ is well-formed.

  »∙→» : » ∇ ∙⟨ ω ⟩[ t ∷ A ] → » ∇
  »∙→» = defn-wf ∘→ wf ∘→ »∙→⊢

opaque
  unfolding _ᵈ•_

  -- If ∇ ᵈ• ξ is well-formed, then ∇ is well-formed.

  »ᵈ•→» : » ∇ ᵈ• ξ → » ∇
  »ᵈ•→» {ξ = idᵉ}          = idᶠ
  »ᵈ•→» {ξ = step ξ _ _ _} = »ᵈ•→» {ξ = ξ} ∘→ »∙→»

------------------------------------------------------------------------
-- Properties related to inlining and Transᵉ

opaque
 unfolding Transᵉ inline
 mutual

  -- The result of inline-< is invariant under transparentisation of
  -- definition context extensions.

  inline-<-Transᵉ :
    {l≤α : l ≤ α} {α<n : α <′ n} →
    inline-< ξ l≤α α<n PE.≡ inline-< (Transᵉ φ ξ) l≤α α<n
  inline-<-Transᵉ {ξ = idᵉ} {l≤α} {α<n = α<l} =
    ⊥-elim $ n≮n _ (≤-trans (<′⇒< α<l) l≤α)
  inline-<-Transᵉ {ξ = step _ tra _ t} {α<n = ≤′-reflexive _} =
    inline-Transᵉ t
  inline-<-Transᵉ {ξ = step ξ tra _ _} {α<n = ≤′-step _} =
    inline-<-Transᵉ {ξ = ξ}
  inline-<-Transᵉ
    {ξ = step _ (opa _) _ t} {φ = _ ⁰} {α<n = ≤′-reflexive _} =
    inline-Transᵉ t
  inline-<-Transᵉ
    {ξ = step ξ (opa _) _ _} {φ = _ ⁰} {α<n = ≤′-step _} =
    inline-<-Transᵉ {ξ = ξ}
  inline-<-Transᵉ
    {ξ = step _ (opa _) _ t} {φ = _ ¹} {α<n = ≤′-reflexive _} =
    inline-Transᵉ t
  inline-<-Transᵉ
    {ξ = step ξ (opa _) _ _} {φ = _ ¹} {α<n = ≤′-step _} =
    inline-<-Transᵉ {ξ = ξ}

  -- The result of inline-Nat is invariant under transparentisation of
  -- definition context extensions.

  inline-Nat-Transᵉ :
    {ξ : DExt (Term 0) n l} →
    inline-Nat ξ α PE.≡ inline-Nat (Transᵉ φ ξ) α
  inline-Nat-Transᵉ {n} {l} {α} {ξ} with l ≤? α
  … | no _ = PE.refl
  … | yes _ with α <′? n
  …   | yes _ = inline-<-Transᵉ {ξ = ξ}
  …   | no _  = PE.refl

  -- The result of inline is invariant under transparentisation of
  -- definition context extensions.

  inline-Transᵉ :
    {ξ : DExt (Term 0) n l} →
    (t : Term m) →
    inline ξ t PE.≡ inline (Transᵉ φ ξ) t
  inline-Transᵉ (var _) =
    PE.refl
  inline-Transᵉ {ξ} (defn _) =
    PE.cong (wk _) (inline-Nat-Transᵉ {ξ = ξ})
  inline-Transᵉ (U _) =
    PE.refl
  inline-Transᵉ Empty =
    PE.refl
  inline-Transᵉ (emptyrec p A t) =
    PE.cong₂ (emptyrec _) (inline-Transᵉ A) (inline-Transᵉ t)
  inline-Transᵉ (Unit _ _) =
    PE.refl
  inline-Transᵉ (star _ _) =
    PE.refl
  inline-Transᵉ (unitrec _ _ _ A t u) =
    PE.cong₃ (unitrec _ _ _) (inline-Transᵉ A) (inline-Transᵉ t)
      (inline-Transᵉ u)
  inline-Transᵉ (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) =
    PE.cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (inline-Transᵉ A) (inline-Transᵉ B)
  inline-Transᵉ (lam p t) =
    PE.cong (lam _) (inline-Transᵉ t)
  inline-Transᵉ (t ∘⟨ p ⟩ u) =
    PE.cong₂ (_∘⟨ _ ⟩_) (inline-Transᵉ t) (inline-Transᵉ u)
  inline-Transᵉ (prod s p t u) =
    PE.cong₂ (prod _ _) (inline-Transᵉ t) (inline-Transᵉ u)
  inline-Transᵉ (fst p t) =
    PE.cong (fst _) (inline-Transᵉ t)
  inline-Transᵉ (snd p t) =
    PE.cong (snd _) (inline-Transᵉ t)
  inline-Transᵉ (prodrec r p q A t u) =
    PE.cong₃ (prodrec _ _ _) (inline-Transᵉ A) (inline-Transᵉ t)
      (inline-Transᵉ u)
  inline-Transᵉ ℕ =
    PE.refl
  inline-Transᵉ zero =
    PE.refl
  inline-Transᵉ (suc t) =
    PE.cong suc (inline-Transᵉ t)
  inline-Transᵉ (natrec p q r A t u v) =
    PE.cong₄ (natrec _ _ _) (inline-Transᵉ A) (inline-Transᵉ t)
      (inline-Transᵉ u) (inline-Transᵉ v)
  inline-Transᵉ (Id A t u) =
    PE.cong₃ Id (inline-Transᵉ A) (inline-Transᵉ t) (inline-Transᵉ u)
  inline-Transᵉ rfl =
    PE.refl
  inline-Transᵉ (J p q A t B u v w) =
    PE.cong₆ (J _ _) (inline-Transᵉ A) (inline-Transᵉ t)
      (inline-Transᵉ B) (inline-Transᵉ u) (inline-Transᵉ v)
      (inline-Transᵉ w)
  inline-Transᵉ (K p A t B u v) =
    PE.cong₅ (K _) (inline-Transᵉ A) (inline-Transᵉ t) (inline-Transᵉ B)
      (inline-Transᵉ u) (inline-Transᵉ v)
  inline-Transᵉ ([]-cong s A t u v) =
    PE.cong₄ ([]-cong _) (inline-Transᵉ A) (inline-Transᵉ t)
      (inline-Transᵉ u) (inline-Transᵉ v)

------------------------------------------------------------------------
-- Properties related to inlining and »_⊇_

opaque
  unfolding inline-< _ᵈ•_

  -- The result of inline-< is invariant under a certain kind of
  -- extension.

  inline-<-⊇ :
    {ξ  : DExt (Term 0) n  l}
    {ξ′ : DExt (Term 0) n′ l}
    {l≤α : l ≤ α} {α<n  : α <′ n} {α<n′ : α <′ n′} →
    » ∇ ᵈ• ξ′ ⊇ ∇ ᵈ• ξ →
    inline-< ξ l≤α α<n PE.≡ inline-< ξ′ l≤α α<n′
  inline-<-⊇ {ξ′ = idᵉ} {l≤α} {α<n′ = α<l} _ =
    ⊥-elim (n≮n _ (≤-trans (<′⇒< α<l) l≤α))
  inline-<-⊇ {ξ} {ξ′ = step ξ′ _ _ _} {α<n} {α<n′ = ≤′-refl} ξ′∙⊇ξ =
    case inv-»∙⊇ ξ′∙⊇ξ of λ where
      (inj₁ (PE.refl , eq)) →
        case ᵈ•-PE-injectivity {ξ₁ = step ξ′ _ _ _} {ξ₂ = ξ} eq of λ {
          (_ , PE.refl) →
        case PE.singleton α<n of λ where
          (≤′-reflexive _ , PE.refl) →
            PE.refl
          (≤′-step α<α , PE.refl) →
            ⊥-elim $ n≮n _ (<′⇒< α<α) }
      (inj₂ (ξ′⊇ξ , _)) →
        ⊥-elim (n≮n _ (≤-trans (<′⇒< α<n) (⊇→≤ ξ′⊇ξ)))
  inline-<-⊇
    {ξ} {ξ′ = step ξ′ _ _ _} {α<n} {α<n′ = ≤′-step α<n′} ξ′∙⊇ξ =
    case inv-»∙⊇ ξ′∙⊇ξ of λ where
      (inj₁ (PE.refl , eq)) →
        case ᵈ•-PE-injectivity {ξ₁ = step ξ′ _ _ _} {ξ₂ = ξ} eq of λ {
          (_ , PE.refl) →
        case PE.singleton α<n of λ where
          (≤′-step _ , PE.refl) →
            PE.cong (inline-< ξ′ _) <′-propositional
          (≤′-refl , PE.refl) →
            ⊥-elim $ n≮n _ (<′⇒< α<n′) }
      (inj₂ (ξ′⊇ξ , _)) →
        inline-<-⊇ {ξ = ξ} {ξ′ = ξ′} ξ′⊇ξ

opaque
  unfolding inline-Nat

  -- The result of inline-Nat is invariant under a certain kind of
  -- extension (for names that are in scope).

  inline-Nat-⊇ :
    {ξ  : DExt (Term 0) n  l}
    {ξ′ : DExt (Term 0) n′ l} →
    » ∇ ᵈ• ξ′ ⊇ ∇ ᵈ• ξ →
    α <′ n →
    inline-Nat ξ α PE.≡ inline-Nat ξ′ α
  inline-Nat-⊇ {n} {l} {n′} {α} {ξ} {ξ′} ξ′⊇ξ α<n with l ≤? α
  … | no _  = PE.refl
  … | yes _ with α <′? n | α <′? n′
  …   | yes _   | yes _   = inline-<-⊇ ξ′⊇ξ
  …   | no α≮n  | _       = ⊥-elim (α≮n α<n)
  …   | _       | no α≮n′ =
    ⊥-elim (α≮n′ (<⇒<′ (≤-trans (<′⇒< α<n) (⊇→≤ ξ′⊇ξ))))

opaque
 unfolding inline
 mutual

  -- The result of inline is invariant under a certain kind of
  -- extension (for well-formed types).

  inline-⊇-⊢ :
    » ∇ ᵈ• ξ′ ⊇ ∇ ᵈ• ξ →
    ∇ ᵈ• ξ » Γ ⊢ A →
    inline ξ A PE.≡ inline ξ′ A
  inline-⊇-⊢ _ (Uⱼ _) =
    PE.refl
  inline-⊇-⊢ ∇′⊇∇ (univ ⊢A) =
    inline-⊇-⊢∷ ∇′⊇∇ ⊢A
  inline-⊇-⊢ _ (Emptyⱼ _) =
    PE.refl
  inline-⊇-⊢ _ (Unitⱼ _ _) =
    PE.refl
  inline-⊇-⊢ ∇′⊇∇ (ΠΣⱼ ⊢B _) =
    PE.cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (inline-⊇-⊢ ∇′⊇∇ (⊢∙→⊢ (wf ⊢B)))
      (inline-⊇-⊢ ∇′⊇∇ ⊢B)
  inline-⊇-⊢ _ (ℕⱼ _) =
    PE.refl
  inline-⊇-⊢ ∇′⊇∇ (Idⱼ ⊢A ⊢t ⊢u) =
    PE.cong₃ Id (inline-⊇-⊢ ∇′⊇∇ ⊢A) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
      (inline-⊇-⊢∷ ∇′⊇∇ ⊢u)

  -- The result of inline is invariant under a certain kind of
  -- extension (for well-typed terms).

  inline-⊇-⊢∷ :
    » ∇ ᵈ• ξ′ ⊇ ∇ ᵈ• ξ →
    ∇ ᵈ• ξ » Γ ⊢ t ∷ A →
    inline ξ t PE.≡ inline ξ′ t
  inline-⊇-⊢∷ ∇′⊇∇ (conv ⊢t _) =
    inline-⊇-⊢∷ ∇′⊇∇ ⊢t
  inline-⊇-⊢∷ _ (var _ _) =
    PE.refl
  inline-⊇-⊢∷ ∇′⊇∇ (defn _ α↦ _) =
    PE.cong (wk _) $ inline-Nat-⊇ ∇′⊇∇ (<⇒<′ (scoped-↦∈ α↦))
  inline-⊇-⊢∷ _ (Uⱼ _) =
    PE.refl
  inline-⊇-⊢∷ _ (Emptyⱼ _) =
    PE.refl
  inline-⊇-⊢∷ ∇′⊇∇ (emptyrecⱼ ⊢A ⊢t) =
    PE.cong₂ (emptyrec _) (inline-⊇-⊢ ∇′⊇∇ ⊢A) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
  inline-⊇-⊢∷ _ (Unitⱼ _ _) =
    PE.refl
  inline-⊇-⊢∷ _ (starⱼ _ _) =
    PE.refl
  inline-⊇-⊢∷ ∇′⊇∇ (unitrecⱼ ⊢A ⊢t ⊢u _) =
    PE.cong₃ (unitrec _ _ _) (inline-⊇-⊢ ∇′⊇∇ ⊢A) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
      (inline-⊇-⊢∷ ∇′⊇∇ ⊢u)
  inline-⊇-⊢∷ ∇′⊇∇ (ΠΣⱼ ⊢A ⊢B _) =
    PE.cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (inline-⊇-⊢∷ ∇′⊇∇ ⊢A)
      (inline-⊇-⊢∷ ∇′⊇∇ ⊢B)
  inline-⊇-⊢∷ ∇′⊇∇ (lamⱼ _ ⊢t _) =
    PE.cong (lam _) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
  inline-⊇-⊢∷ ∇′⊇∇ (⊢t ∘ⱼ ⊢u) =
    PE.cong₂ (_∘⟨ _ ⟩_) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t) (inline-⊇-⊢∷ ∇′⊇∇ ⊢u)
  inline-⊇-⊢∷ ∇′⊇∇ (prodⱼ _ ⊢t ⊢u _) =
    PE.cong₂ (prod _ _) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t) (inline-⊇-⊢∷ ∇′⊇∇ ⊢u)
  inline-⊇-⊢∷ ∇′⊇∇ (fstⱼ _ ⊢t) =
    PE.cong (fst _) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
  inline-⊇-⊢∷ ∇′⊇∇ (sndⱼ _ ⊢t) =
    PE.cong (snd _) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
  inline-⊇-⊢∷ ∇′⊇∇ (prodrecⱼ ⊢A ⊢t ⊢u _) =
    PE.cong₃ (prodrec _ _ _) (inline-⊇-⊢ ∇′⊇∇ ⊢A) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
      (inline-⊇-⊢∷ ∇′⊇∇ ⊢u)
  inline-⊇-⊢∷ _ (ℕⱼ _) =
    PE.refl
  inline-⊇-⊢∷ _ (zeroⱼ _) =
    PE.refl
  inline-⊇-⊢∷ ∇′⊇∇ (sucⱼ ⊢t) =
    PE.cong suc (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
  inline-⊇-⊢∷ ∇′⊇∇ (natrecⱼ ⊢t ⊢u ⊢v) =
    PE.cong₄ (natrec _ _ _) (inline-⊇-⊢ ∇′⊇∇ (⊢∙→⊢ (wfTerm ⊢u)))
      (inline-⊇-⊢∷ ∇′⊇∇ ⊢t) (inline-⊇-⊢∷ ∇′⊇∇ ⊢u) (inline-⊇-⊢∷ ∇′⊇∇ ⊢v)
  inline-⊇-⊢∷ ∇′⊇∇ (Idⱼ ⊢A ⊢t ⊢u) =
    PE.cong₃ Id (inline-⊇-⊢∷ ∇′⊇∇ ⊢A) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
      (inline-⊇-⊢∷ ∇′⊇∇ ⊢u)
  inline-⊇-⊢∷ _ (rflⱼ _) =
    PE.refl
  inline-⊇-⊢∷ ∇′⊇∇ (Jⱼ ⊢t ⊢B ⊢u ⊢v ⊢w) =
    PE.cong₆ (J _ _) (inline-⊇-⊢ ∇′⊇∇ (wf-⊢∷ ⊢t)) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
      (inline-⊇-⊢ ∇′⊇∇ ⊢B) (inline-⊇-⊢∷ ∇′⊇∇ ⊢u) (inline-⊇-⊢∷ ∇′⊇∇ ⊢v)
      (inline-⊇-⊢∷ ∇′⊇∇ ⊢w)
  inline-⊇-⊢∷ ∇′⊇∇ (Kⱼ ⊢B ⊢u ⊢v _) =
    let ⊢A , ⊢t , _ = inversion-Id (wf-⊢∷ ⊢v) in
    PE.cong₅ (K _) (inline-⊇-⊢ ∇′⊇∇ ⊢A) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
      (inline-⊇-⊢ ∇′⊇∇ ⊢B) (inline-⊇-⊢∷ ∇′⊇∇ ⊢u) (inline-⊇-⊢∷ ∇′⊇∇ ⊢v)
  inline-⊇-⊢∷ ∇′⊇∇ ([]-congⱼ ⊢A ⊢t ⊢u ⊢v _) =
    PE.cong₄ ([]-cong _) (inline-⊇-⊢ ∇′⊇∇ ⊢A) (inline-⊇-⊢∷ ∇′⊇∇ ⊢t)
      (inline-⊇-⊢∷ ∇′⊇∇ ⊢u) (inline-⊇-⊢∷ ∇′⊇∇ ⊢v)

opaque
  unfolding inlineᵈ

  -- A variant of inline-⊇-⊢.

  inlineᵈ-⊇-⊢ :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ A →
    inlineᵈ ∇ A PE.≡ inlineᵈ ∇′ A
  inlineᵈ-⊇-⊢ ∇⊇∇′ ⊢A =
    inline-⊇-⊢
      (PE.subst₂ »_⊇_ (PE.sym εᵈ•as-DExt) (PE.sym εᵈ•as-DExt) ∇⊇∇′)
      (PE.subst₂ _⊢_ (PE.cong (_» _) $ PE.sym εᵈ•as-DExt) PE.refl ⊢A)

opaque
  unfolding inlineᵈ

  -- A variant of inline-⊇-⊢∷.

  inlineᵈ-⊇-⊢∷ :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t ∷ A →
    inlineᵈ ∇ t PE.≡ inlineᵈ ∇′ t
  inlineᵈ-⊇-⊢∷ ∇⊇∇′ ⊢t =
    inline-⊇-⊢∷
      (PE.subst₂ »_⊇_ (PE.sym εᵈ•as-DExt) (PE.sym εᵈ•as-DExt) ∇⊇∇′)
      (PE.subst₃ _⊢_∷_
         (PE.cong (_» _) $ PE.sym εᵈ•as-DExt) PE.refl PE.refl
         ⊢t)

opaque
  unfolding inline

  -- The result of inline-Con is invariant under a certain kind of
  -- extension (for well-formed contexts).

  inline-Con-⊇ :
    » ∇ ᵈ• ξ′ ⊇ ∇ ᵈ• ξ →
    ∇ ᵈ• ξ »⊢ Γ →
    inline-Con ξ Γ PE.≡ inline-Con ξ′ Γ
  inline-Con-⊇ _    (ε _)  = PE.refl
  inline-Con-⊇ ξ′⊇ξ (∙ ⊢A) =
    PE.cong₂ _∙_ (inline-Con-⊇ ξ′⊇ξ (wf ⊢A)) (inline-⊇-⊢ ξ′⊇ξ ⊢A)

opaque
  unfolding _ᵈ•_

  -- If α points to A in the well-formed context ∇ ᵈ• ξ, but not in ξ,
  -- then inline ξ has no effect on A.

  ≰→↦→inline≡ :
    {ξ : DExt (Term 0) n l} →
    » ∇ ᵈ• ξ → ¬ l ≤ α → α ↦∷ A ∈ ∇ ᵈ• ξ →
    inline ξ A PE.≡ A
  ≰→↦→inline≡ {A} {ξ} »ξ l≰α α↦ =
    inline ξ A    ≡˘⟨ inline-⊇-⊢ (ᵈ•⊇ {ξ = ξ} »ξ) (wf-↦∈ (≰→↦∈→↦∈ {ξ = ξ} l≰α α↦) (»ᵈ•→» {ξ = ξ} »ξ)) ⟩
    inline idᵉ A  ≡⟨ inline-id _ ⟩
    A             ∎

opaque
  unfolding _ᵈ•_

  -- If α points to t in the well-formed context ∇ ᵈ• ξ, but not in ξ,
  -- then inline ξ has no effect on t.

  ≰→↦∷→inline≡ :
    {ξ : DExt (Term 0) n l} →
    » ∇ ᵈ• ξ → ¬ l ≤ α → α ↦ t ∷ A ∈ ∇ ᵈ• ξ →
    inline ξ t PE.≡ t
  ≰→↦∷→inline≡ {t} {ξ} »ξ l≰α α↦ =
    inline ξ t    ≡˘⟨ inline-⊇-⊢∷ (ᵈ•⊇ {ξ = ξ} »ξ) (wf-↦∷∈ (≰→↦∷∈→↦∷∈ {ξ = ξ} l≰α α↦) (»ᵈ•→» {ξ = ξ} »ξ)) ⟩
    inline idᵉ t  ≡⟨ inline-id _ ⟩
    t             ∎

------------------------------------------------------------------------
-- Some preservation lemmas related to inlining

opaque
  unfolding inline-Con

  -- If x ∷ A ∈ Γ holds, then x ∷ inline ξ A ∈ inline-Con ξ Γ holds.

  inline∈ : x ∷ A ∈ Γ → x ∷ inline ξ A ∈ inline-Con ξ Γ
  inline∈ (here {A}) =
    PE.subst₂ (_∷_∈_ _) (wk-inline A) PE.refl here
  inline∈ (there {A} x∈) =
    PE.subst₂ (_∷_∈_ _) (wk-inline A) PE.refl $
    there (inline∈ x∈)

opaque
  unfolding inline _ᵈ•_

  -- If α points to t, then inline-< ξ l≤α α<n is propositionally
  -- equal to inline ξ t, given certain assumptions.

  inline-<≡ :
    {ξ : DExt (Term 0) n l}
    {l≤α : l ≤ α} {α<n : α <′ n} →
    » ∇ ᵈ• ξ → α ↦ t ∷ A ∈ ∇ ᵈ• ξ →
    inline-< ξ l≤α α<n PE.≡ inline ξ t
  inline-<≡ {ξ = idᵉ} {l≤α = n≤α} {α<n} _ _ =
    ⊥-elim (n≮n _ (≤-trans (<′⇒< α<n) n≤α))
  inline-<≡ {ξ = step _ _ _ _} {α<n = ≤′-reflexive _} ∙ᵗ[ ⊢t ] here =
    inline-⊇-⊢∷ (stepᵗ₁ ⊢t) ⊢t
  inline-<≡ {ξ = step _ _ _ _} {α<n = ≤′-refl} _ (there α∈) =
    ⊥-elim (n≮n _ (scoped-↦∷∈ α∈))
  inline-<≡ {ξ = step _ _ _ _} {α<n = ≤′-step α<α} _ here =
    ⊥-elim (n≮n _ (<′⇒< α<α))
  inline-<≡
    {t} {ξ = step ξ _ _ _} {l≤α} {α<n = ≤′-step α<n}
    (∙ᵒ⟨_⟩[_∷_] {φ} {t = u} {A = B} ok ⊢u ⊢B) (there α∈) =
    let s = stepᵒ₁ ok ⊢B ⊢u in
    inline-< ξ l≤α α<n             ≡⟨ inline-<≡ (defn-wf (wf ⊢B)) α∈ ⟩

    inline ξ t                     ≡⟨ inline-⊇-⊢∷ s $
                                      PE.subst₂ (_⊢_∷_ _) wk₀-closed wk₀-closed $
                                      wf-⊢≡∷ (δ-red (wf ⊢B) α∈ PE.refl PE.refl) .proj₂ .proj₂ ⟩
    inline (step ξ (opa φ) B u) t  ∎
  inline-<≡
    {t} {ξ = step ξ _ _ _} {l≤α} {α<n = ≤′-step α<n}
    (∙ᵗ[_] {t = u} {A = B} ⊢t) (there α∈) =
    let s = stepᵗ₁ ⊢t in
    inline-< ξ l≤α α<n         ≡⟨ inline-<≡ (defn-wf (wfTerm ⊢t)) α∈ ⟩

    inline ξ t                 ≡⟨ inline-⊇-⊢∷ s $
                                  PE.subst₂ (_⊢_∷_ _) wk₀-closed wk₀-closed $
                                  wf-⊢≡∷ (δ-red (wfTerm ⊢t) α∈ PE.refl PE.refl) .proj₂ .proj₂ ⟩
    inline (step ξ tra B u) t  ∎

opaque

  -- If α points to t in ξ, then inline-Nat ξ α is propositionally
  -- equal to inline ξ t, given certain assumptions.

  inline-Nat≡ :
    {ξ : DExt (Term 0) n l} →
    » ∇ ᵈ• ξ → l ≤ α → α ↦ t ∷ A ∈ ∇ ᵈ• ξ →
    inline-Nat ξ α PE.≡ inline ξ t
  inline-Nat≡ {l} {α} {t} {ξ} »ξ l≤α α∈ =
    inline-Nat ξ α                         ≡⟨ <-inline-Nat ⟩
    inline-< ξ l≤α (<⇒<′ (scoped-↦∷∈ α∈))  ≡⟨ inline-<≡ »ξ α∈ ⟩
    inline ξ t                             ∎

opaque
 unfolding inline _ᵈ•_
 mutual

  -- The function inline-< produces well-typed terms, given
  -- certain assumptions.

  ⊢inline-<∷ :
    {ξ : DExt (Term 0) n l}
    {l≤α : l ≤ α} {α<n : α <′ n} →
    » ∇ ᵈ• ξ → α ↦∷ A ∈ ∇ ᵈ• ξ →
    glassify ∇ » ε ⊢ inline-< ξ l≤α α<n ∷ inline ξ A
  ⊢inline-<∷ {ξ = idᵉ} {l≤α = n≤α} {α<n} _ _ =
    ⊥-elim (n≮n _ (≤-trans (<′⇒< α<n) n≤α))
  ⊢inline-<∷ {ξ = step _ _ _ _} {α<n = ≤′-step α<α} _ here =
    ⊥-elim (n≮n _ (<′⇒< α<α))
  ⊢inline-<∷ {ξ = step ξ _ _ _} {α<n = ≤′-reflexive _} ∙ᵗ[ ⊢t ] here =
    PE.subst (_⊢_∷_ _ _)
      (inline-⊇-⊢ {ξ′ = step ξ _ _ _} {ξ = ξ} (stepᵗ₁ ⊢t) (wf-⊢∷ ⊢t)) $
    ⊢inline∷ {ξ = ξ} ⊢t
  ⊢inline-<∷ {∇} {ξ = step ξ _ _ _} {α<n = ≤′-reflexive _}
    (∙ᵒ⟨_⟩[_∷_] {φ} {t} {A} ok ⊢t ⊢A) here =
    PE.subst₃ _⊢_∷_
      (PE.cong (_» _) glassify-factor)
      (inline (Transᵉ φ ξ) t  ≡˘⟨ inline-Transᵉ t ⟩
       inline ξ t             ∎)
      (inline (Transᵉ φ ξ) A          ≡˘⟨ inline-Transᵉ {ξ = ξ} A ⟩
       inline ξ A                     ≡⟨ inline-⊇-⊢ {ξ′ = step ξ _ _ _} {ξ = ξ} (stepᵒ₁ ok ⊢A ⊢t) ⊢A ⟩
       inline (step ξ (opa φ) A t) A  ∎) $
    ⊢inline∷ {ξ = Transᵉ φ ξ} $
    PE.subst₃ _⊢_∷_ (PE.cong (_» _) Trans-ᵈ•) PE.refl PE.refl ⊢t
  ⊢inline-<∷ {ξ = step _ _ _ _} {α<n = ≤′-reflexive eq} _ (there α↦) =
    ⊥-elim $ n≮n _ $ PE.subst (_< _) (1+-injective eq) (scoped-↦∈ α↦)
  ⊢inline-<∷ {ξ = step ξ _ _ _} {α<n = ≤′-step _} ∙ᵗ[ ⊢t ] (there α↦) =
    PE.subst (_⊢_∷_ _ _)
      (inline-⊇-⊢ (stepᵗ₁ ⊢t) $
       PE.subst (_⊢_ _) wk₀-closed $
       wf-⊢∷ (defn (wfTerm ⊢t) α↦ PE.refl)) $
    ⊢inline-<∷ {ξ = ξ} (defn-wf (wfTerm ⊢t)) α↦
  ⊢inline-<∷ {ξ = step ξ _ _ _} {α<n = ≤′-step _}
    ∙ᵒ⟨ ok ⟩[ ⊢t ∷ ⊢A ] (there α↦) =
    PE.subst (_⊢_∷_ _ _)
      (inline-⊇-⊢ (stepᵒ₁ ok ⊢A ⊢t) $
       PE.subst (_⊢_ _) wk₀-closed $
       wf-⊢∷ (defn (wf ⊢A) α↦ PE.refl)) $
    ⊢inline-<∷ {ξ = ξ} (defn-wf (wf ⊢A)) α↦

  -- The function inline-Nat produces well-typed terms, given certain
  -- assumptions.

  ⊢inline-Nat∷ :
    {ξ : DExt (Term 0) n l} →
    » ∇ ᵈ• ξ → α ↦∷ A ∈ ∇ ᵈ• ξ →
    glassify ∇ » ε ⊢ inline-Nat ξ α ∷ inline ξ A
  ⊢inline-Nat∷ {n} {l} {α} {ξ} »ξ α↦ with l ≤? α
  … | no l≰α =
    glassify-⊢∷ $
    defn (ε (»ᵈ•→» {ξ = ξ} »ξ))
      (PE.subst (flip (_↦∷_∈_ _) _) (PE.sym $ ≰→↦→inline≡ »ξ l≰α α↦)
         (≰→↦∈→↦∈ {ξ = ξ} l≰α α↦))
      (PE.sym $ wk-id _)
  … | yes l≤α with α <′? n
  …   | no α≮n = ⊥-elim $ α≮n (<⇒<′ (scoped-↦∈ α↦))
  …   | yes _  = ⊢inline-<∷ »ξ α↦

  -- If α points to t in ξ, then inline-< ξ α<n reduces to inline ξ t,
  -- given certain assumptions.

  ⊢inline-<⇒*∷ :
    {ξ : DExt (Term 0) n l}
    {l≤α : l ≤ α} {α<n : α <′ n} →
    » ∇ ᵈ• ξ → α ↦ t ∷ A ∈ ∇ ᵈ• ξ →
    glassify ∇ » ε ⊢ inline-< ξ l≤α α<n ⇒* inline ξ t ∷ inline ξ A
  ⊢inline-<⇒*∷ »ξ α↦t =
    PE.subst₂ (_⊢_⇒*_∷_ _ _) (inline-<≡ »ξ α↦t) PE.refl $
    id (⊢inline-<∷ »ξ (↦∷∈⇒↦∈ α↦t))

  -- If α points to t in ξ, then inline-< ξ α<n is definitionally
  -- equal to inline ξ t, given certain assumptions.

  ⊢inline-<≡∷ :
    {ξ : DExt (Term 0) n l}
    {l≤α : l ≤ α} {α<n : α <′ n} →
    » ∇ ᵈ• ξ → α ↦ t ∷ A ∈ ∇ ᵈ• ξ →
    glassify ∇ » ε ⊢ inline-< ξ l≤α α<n ≡ inline ξ t ∷ inline ξ A
  ⊢inline-<≡∷ »ξ α↦t = subset*Term (⊢inline-<⇒*∷ »ξ α↦t)

  -- If α points to t in ξ, then inline-Nat ξ α reduces to inline ξ t,
  -- given certain assumptions.

  ⊢inline-Nat⇒*∷ :
    {ξ : DExt (Term 0) n l} →
    » ∇ ᵈ• ξ → α ↦ t ∷ A ∈ ∇ ᵈ• ξ →
    glassify ∇ » ε ⊢ inline-Nat ξ α ⇒* inline ξ t ∷ inline ξ A
  ⊢inline-Nat⇒*∷ {n} {l} {α} {ξ} »ξ α↦ with l ≤? α
  … | no l≰α =
    glassify-⇒*∷ $
    PE.subst₂ (_⊢_⇒*_∷_ _ _)
      (PE.trans (wk-id _) (PE.sym (≰→↦∷→inline≡ »ξ l≰α α↦)))
      (PE.trans (wk-id _) (PE.sym (≰→↦→inline≡ »ξ l≰α (↦∷∈⇒↦∈ α↦)))) $
    redMany $
    δ-red (ε (»ᵈ•→» {ξ = ξ} »ξ))
      (≰→↦∷∈→↦∷∈ {ξ = ξ} l≰α α↦) PE.refl PE.refl
  … | yes l≤α with α <′? n
  …   | no α≮n = ⊥-elim $ α≮n (<⇒<′ (scoped-↦∷∈ α↦))
  …   | yes _  = ⊢inline-<⇒*∷ »ξ α↦

  -- If α points to t in ξ, then inline-Nat ξ α is definitionally
  -- equal to inline ξ t, given certain assumptions.

  ⊢inline-Nat≡∷ :
    {ξ : DExt (Term 0) n l} →
    » ∇ ᵈ• ξ → α ↦ t ∷ A ∈ ∇ ᵈ• ξ →
    glassify ∇ » ε ⊢ inline-Nat ξ α ≡ inline ξ t ∷ inline ξ A
  ⊢inline-Nat≡∷ »ξ α↦ = subset*Term (⊢inline-Nat⇒*∷ »ξ α↦)

  -- Inlining preserves context well-formedness.

  ⊢inline-Con :
    ∇ ᵈ• ξ »⊢ Γ →
    glassify ∇ »⊢ inline-Con ξ Γ
  ⊢inline-Con {ξ} (ε »ξ) = ε (glassify-» (»ᵈ•→» {ξ = ξ} »ξ))
  ⊢inline-Con     (∙ ⊢A) = ∙ ⊢inline ⊢A

  -- Inlining preserves type well-formedness.

  ⊢inline :
    ∇ ᵈ• ξ » Γ ⊢ A →
    glassify ∇ » inline-Con ξ Γ ⊢ inline ξ A
  ⊢inline (Uⱼ ⊢Γ) =
    Uⱼ (⊢inline-Con ⊢Γ)
  ⊢inline (univ ⊢A) =
    univ (⊢inline∷ ⊢A)
  ⊢inline (Emptyⱼ ⊢Γ) =
    Emptyⱼ (⊢inline-Con ⊢Γ)
  ⊢inline (Unitⱼ ⊢Γ ok) =
    Unitⱼ (⊢inline-Con ⊢Γ) ok
  ⊢inline (ΠΣⱼ ⊢B ok) =
    ΠΣⱼ (⊢inline ⊢B) ok
  ⊢inline (ℕⱼ ⊢Γ) =
    ℕⱼ (⊢inline-Con ⊢Γ)
  ⊢inline (Idⱼ ⊢A ⊢t ⊢u) =
    Idⱼ (⊢inline ⊢A) (⊢inline∷ ⊢t) (⊢inline∷ ⊢u)

  -- Inlining preserves well-typedness.

  ⊢inline∷ :
    ∇ ᵈ• ξ » Γ ⊢ t ∷ A →
    glassify ∇ » inline-Con ξ Γ ⊢ inline ξ t ∷ inline ξ A
  ⊢inline∷ (conv ⊢t B≡A) =
    conv (⊢inline∷ ⊢t) (⊢inline≡inline B≡A)
  ⊢inline∷ (var ⊢Γ x∈) =
    var (⊢inline-Con ⊢Γ) (inline∈ x∈)
  ⊢inline∷ (defn {A′} ⊢Γ α↦ PE.refl) =
    PE.subst (_⊢_∷_ _ _) (wk-inline A′) $
    wkTerm (wk₀∷ʷ⊇ (⊢inline-Con ⊢Γ)) (⊢inline-Nat∷ (defn-wf ⊢Γ) α↦)
  ⊢inline∷ (Uⱼ ⊢Γ) =
    Uⱼ (⊢inline-Con ⊢Γ)
  ⊢inline∷ (Emptyⱼ ⊢Γ) =
    Emptyⱼ (⊢inline-Con ⊢Γ)
  ⊢inline∷ (emptyrecⱼ ⊢A ⊢t) =
    emptyrecⱼ (⊢inline ⊢A) (⊢inline∷ ⊢t)
  ⊢inline∷ (Unitⱼ ⊢Γ ok) =
    Unitⱼ (⊢inline-Con ⊢Γ) ok
  ⊢inline∷ (starⱼ ⊢Γ ok) =
    starⱼ (⊢inline-Con ⊢Γ) ok
  ⊢inline∷ (unitrecⱼ {A} ⊢A ⊢t ⊢u ok) =
    PE.subst (_⊢_∷_ _ _) (PE.sym $ inline-[]₀ A) $
    unitrecⱼ (⊢inline ⊢A) (⊢inline∷ ⊢t)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢u)) ok
  ⊢inline∷ (ΠΣⱼ ⊢A ⊢B ok) =
    ΠΣⱼ (⊢inline∷ ⊢A) (⊢inline∷ ⊢B) ok
  ⊢inline∷ (lamⱼ ⊢B ⊢t ok) =
    lamⱼ (⊢inline ⊢B) (⊢inline∷ ⊢t) ok
  ⊢inline∷ (_∘ⱼ_ {G = B} ⊢t ⊢u) =
    PE.subst (_⊢_∷_ _ _) (PE.sym $ inline-[]₀ B) $
    ⊢inline∷ ⊢t ∘ⱼ ⊢inline∷ ⊢u
  ⊢inline∷ (prodⱼ {G = B} ⊢B ⊢t ⊢u ok) =
    prodⱼ (⊢inline ⊢B) (⊢inline∷ ⊢t)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢u)) ok
  ⊢inline∷ (fstⱼ ⊢B ⊢t) =
    fstⱼ (⊢inline ⊢B) (⊢inline∷ ⊢t)
  ⊢inline∷ (sndⱼ {G = B} ⊢B ⊢t) =
    PE.subst (_⊢_∷_ _ _) (PE.sym $ inline-[]₀ B) $
    sndⱼ (⊢inline ⊢B) (⊢inline∷ ⊢t)
  ⊢inline∷ (prodrecⱼ {A} ⊢A ⊢t ⊢u ok) =
    PE.subst (_⊢_∷_ _ _) (PE.sym $ inline-[]₀ A) $
    prodrecⱼ (⊢inline ⊢A) (⊢inline∷ ⊢t)
      (PE.subst (_⊢_∷_ _ _) (inline-[][]↑ A) (⊢inline∷ ⊢u)) ok
  ⊢inline∷ (ℕⱼ ⊢Γ) =
    ℕⱼ (⊢inline-Con ⊢Γ)
  ⊢inline∷ (zeroⱼ ⊢Γ) =
    zeroⱼ (⊢inline-Con ⊢Γ)
  ⊢inline∷ (sucⱼ ⊢t) =
    sucⱼ (⊢inline∷ ⊢t)
  ⊢inline∷ (natrecⱼ {A} ⊢t ⊢u ⊢v) =
    PE.subst (_⊢_∷_ _ _) (PE.sym $ inline-[]₀ A) $
    natrecⱼ (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢t))
      (PE.subst (_⊢_∷_ _ _) (inline-[][]↑ A) (⊢inline∷ ⊢u))
      (⊢inline∷ ⊢v)
  ⊢inline∷ (Idⱼ ⊢A ⊢t ⊢u) =
    Idⱼ (⊢inline∷ ⊢A) (⊢inline∷ ⊢t) (⊢inline∷ ⊢u)
  ⊢inline∷ (rflⱼ ⊢t) =
    rflⱼ (⊢inline∷ ⊢t)
  ⊢inline∷ (Jⱼ {t} {A} {B} _ ⊢B ⊢u _ ⊢w) =
    PE.subst (_⊢_∷_ _ _) (PE.sym $ inline-[]₁₀ B) $
    Jⱼ′
      (PE.subst (flip _⊢_ _)
         (PE.sym $ PE.cong (_»∙_ _) $
          PE.cong₃ Id (wk-inline A) (wk-inline t) PE.refl) $
       ⊢inline ⊢B)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₁₀ B) (⊢inline∷ ⊢u))
      (⊢inline∷ ⊢w)
  ⊢inline∷ (Kⱼ {B} ⊢B ⊢u ⊢v ok) =
    PE.subst (_⊢_∷_ _ _) (PE.sym $ inline-[]₀ B) $
    Kⱼ (⊢inline ⊢B)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢u))
      (⊢inline∷ ⊢v) ok
  ⊢inline∷ ([]-congⱼ _ _ _ ⊢v ok) =
    []-congⱼ′ ok (⊢inline∷ ⊢v)

  -- Inlining preserves definitional equality.

  ⊢inline≡inline :
    ∇ ᵈ• ξ » Γ ⊢ A ≡ B →
    glassify ∇ » inline-Con ξ Γ ⊢ inline ξ A ≡ inline ξ B
  ⊢inline≡inline = λ where
    (refl ⊢A) →
      refl (⊢inline ⊢A)
    (sym B≡A) →
      sym (⊢inline≡inline B≡A)
    (trans A≡B B≡C) →
      trans (⊢inline≡inline A≡B) (⊢inline≡inline B≡C)
    (univ A≡B) →
      univ (⊢inline≡inline∷ A≡B)
    (ΠΣ-cong A₁≡B₁ A₂≡B₂ ok) →
      ΠΣ-cong (⊢inline≡inline A₁≡B₁) (⊢inline≡inline A₂≡B₂) ok
    (Id-cong A≡B t₁≡u₁ t₂≡u₂) →
      Id-cong (⊢inline≡inline A≡B) (⊢inline≡inline∷ t₁≡u₁)
        (⊢inline≡inline∷ t₂≡u₂)

  -- Inlining preserves definitional equality.

  ⊢inline≡inline∷ :
    ∇ ᵈ• ξ » Γ ⊢ t ≡ u ∷ A →
    glassify ∇ » inline-Con ξ Γ ⊢ inline ξ t ≡ inline ξ u ∷ inline ξ A
  ⊢inline≡inline∷ = λ where
    (refl ⊢t) →
      refl (⊢inline∷ ⊢t)
    (sym _ t₂≡t₁) →
      sym′ (⊢inline≡inline∷ t₂≡t₁)
    (trans t₁≡t₂ t₂≡t₃) →
      trans (⊢inline≡inline∷ t₁≡t₂) (⊢inline≡inline∷ t₂≡t₃)
    (conv t₁≡t₂ B≡A) →
      conv (⊢inline≡inline∷ t₁≡t₂) (⊢inline≡inline B≡A)
    (δ-red {t′ = t} {A′ = A} ⊢Γ α↦t PE.refl PE.refl) →
      PE.subst₂ (_⊢_≡_∷_ _ _) (wk-inline t) (wk-inline A) $
      wkEqTerm (wk₀∷ʷ⊇ (⊢inline-Con ⊢Γ)) $
      ⊢inline-Nat≡∷ (defn-wf ⊢Γ) α↦t
    (emptyrec-cong A₁≡A₂ t₁≡t₂) →
      emptyrec-cong (⊢inline≡inline A₁≡A₂) (⊢inline≡inline∷ t₁≡t₂)
    (unitrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ _ _) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ A₁) $
      unitrec-cong′ (⊢inline≡inline A₁≡A₂) (⊢inline≡inline∷ t₁≡t₂)
        (PE.subst (_⊢_≡_∷_ _ _ _) (inline-[]₀ A₁) $
         ⊢inline≡inline∷ u₁≡u₂)
    (unitrec-β {A} ⊢A ⊢t _ _) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ A) $
      unitrec-β-≡ (⊢inline ⊢A)
        (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢t))
    (unitrec-β-η {A} ⊢A ⊢t ⊢u _ η) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ A) $
      unitrec-β-η-≡ (⊢inline ⊢A) (⊢inline∷ ⊢t)
        (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢u)) η
    (η-unit ⊢t₁ ⊢t₂ ok) →
      η-unit (⊢inline∷ ⊢t₁) (⊢inline∷ ⊢t₂) ok
    (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) →
      ΠΣ-cong (⊢inline≡inline∷ A₁≡A₂) (⊢inline≡inline∷ B₁≡B₂) ok
    (app-cong {G = B} t₁≡t₂ u₁≡u₂) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ B) $
      app-cong (⊢inline≡inline∷ t₁≡t₂) (⊢inline≡inline∷ u₁≡u₂)
    (β-red {G = B} {t} _ ⊢t ⊢u PE.refl ok) →
      PE.subst₂ (_⊢_≡_∷_ _ _)
        (PE.sym $ inline-[]₀ t) (PE.sym $ inline-[]₀ B) $
      β-red-≡ (⊢inline∷ ⊢t) (⊢inline∷ ⊢u) ok
    (η-eq {f = t₁} {g = t₂} ⊢B ⊢t₁ ⊢t₂ t₁0≡t₂0 ok) →
      η-eq′ (⊢inline∷ ⊢t₁) (⊢inline∷ ⊢t₂)
        (PE.subst₃ (_⊢_≡_∷_ _)
           (PE.cong (_∘⟨ _ ⟩ _) $ PE.sym $ wk-inline t₁)
           (PE.cong (_∘⟨ _ ⟩ _) $ PE.sym $ wk-inline t₂) PE.refl $
         ⊢inline≡inline∷ t₁0≡t₂0)
    (fst-cong _ t₁≡t₂) →
      fst-cong′ (⊢inline≡inline∷ t₁≡t₂)
    (Σ-β₁ {G = B} ⊢B ⊢t₁ ⊢t₂ PE.refl ok) →
      Σ-β₁-≡ (⊢inline ⊢B) (⊢inline∷ ⊢t₁)
        (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢t₂)) ok
    (snd-cong {G = B} _ t₁≡t₂) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ B) $
      snd-cong′ (⊢inline≡inline∷ t₁≡t₂)
    (Σ-β₂ {G = B} ⊢B ⊢t₁ ⊢t₂ PE.refl ok) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ B) $
      Σ-β₂-≡ (⊢inline ⊢B) (⊢inline∷ ⊢t₁)
        (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢t₂)) ok
    (Σ-η {G = B} _ ⊢t₁ ⊢t₂ fst≡fst snd≡snd _) →
      Σ-η′ (⊢inline∷ ⊢t₁) (⊢inline∷ ⊢t₂) (⊢inline≡inline∷ fst≡fst)
        (PE.subst (_⊢_≡_∷_ _ _ _) (inline-[]₀ B) $
         ⊢inline≡inline∷ snd≡snd)
    (prod-cong {G = B} ⊢B t₁≡t₂ u₁≡u₂ ok) →
      prod-cong (⊢inline ⊢B) (⊢inline≡inline∷ t₁≡t₂)
        (PE.subst (_⊢_≡_∷_ _ _ _) (inline-[]₀ B) $
         ⊢inline≡inline∷ u₁≡u₂)
        ok
    (prodrec-cong {G = B} {A = C₁} C₁≡C₂ t₁≡t₂ u₁≡u₂ ok) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ C₁) $
      prodrec-cong′ (⊢inline≡inline C₁≡C₂) (⊢inline≡inline∷ t₁≡t₂)
        (PE.subst (_⊢_≡_∷_ _ _ _) (inline-[][]↑ C₁) $
         ⊢inline≡inline∷ u₁≡u₂)
    (prodrec-β {G = B} {A = C} {u = v} ⊢C ⊢t ⊢u ⊢v PE.refl ok) →
      PE.subst₂ (_⊢_≡_∷_ _ _)
        (PE.sym $ inline-[]₁₀ v) (PE.sym $ inline-[]₀ C) $
      prodrec-β-≡ (⊢inline ⊢C) (⊢inline∷ ⊢t)
        (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢u))
        (PE.subst (_⊢_∷_ _ _) (inline-[][]↑ C) (⊢inline∷ ⊢v))
    (suc-cong t₁≡t₂) →
      suc-cong (⊢inline≡inline∷ t₁≡t₂)
    (natrec-cong {A = A₁} A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ A₁) $
      natrec-cong (⊢inline≡inline A₁≡A₂)
        (PE.subst (_⊢_≡_∷_ _ _ _) (inline-[]₀ A₁) $
         ⊢inline≡inline∷ t₁≡t₂)
        (PE.subst (_⊢_≡_∷_ _ _ _) (inline-[][]↑ A₁) $
         ⊢inline≡inline∷ u₁≡u₂)
        (⊢inline≡inline∷ v₁≡v₂)
    (natrec-zero {A} ⊢t ⊢u) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ A) $
      natrec-zero
        (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢t))
        (PE.subst (_⊢_∷_ _ _) (inline-[][]↑ A) (⊢inline∷ ⊢u))
    (natrec-suc {A} {s = u} ⊢t ⊢u ⊢v) →
      PE.subst₂ (_⊢_≡_∷_ _ _)
        (PE.sym $ inline-[]₁₀ u) (PE.sym $ inline-[]₀ A) $
      natrec-suc (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢t))
        (PE.subst (_⊢_∷_ _ _) (inline-[][]↑ A) (⊢inline∷ ⊢u))
        (⊢inline∷ ⊢v)
    (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) →
      Id-cong (⊢inline≡inline∷ A₁≡A₂) (⊢inline≡inline∷ t₁≡t₂)
        (⊢inline≡inline∷ u₁≡u₂)
    (J-cong {A₁} {t₁} {B₁} A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₁₀ B₁) $
      J-cong′ (⊢inline≡inline A₁≡A₂) (⊢inline≡inline∷ t₁≡t₂)
        (PE.subst₃ _⊢_≡_
           (PE.sym $ PE.cong (_»∙_ _) $
            PE.cong₃ Id (wk-inline A₁) (wk-inline t₁) PE.refl)
           PE.refl PE.refl $
         ⊢inline≡inline B₁≡B₂)
        (PE.subst (_⊢_≡_∷_ _ _ _) (inline-[]₁₀ B₁) $
         ⊢inline≡inline∷ u₁≡u₂)
        (⊢inline≡inline∷ v₁≡v₂) (⊢inline≡inline∷ w₁≡w₂)
    (J-β {t} {A} {B} ⊢t ⊢B ⊢u PE.refl) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₁₀ B) $
      J-β-≡ (⊢inline∷ ⊢t)
        (PE.subst (flip _⊢_ _)
           (PE.sym $ PE.cong (_»∙_ _) $
            PE.cong₃ Id (wk-inline A) (wk-inline t) PE.refl) $
         ⊢inline ⊢B)
        (PE.subst (_⊢_∷_ _ _) (inline-[]₁₀ B) (⊢inline∷ ⊢u))
    (K-cong {B₁} A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ B₁) $
      K-cong (⊢inline≡inline A₁≡A₂) (⊢inline≡inline∷ t₁≡t₂)
        (⊢inline≡inline B₁≡B₂)
        (PE.subst (_⊢_≡_∷_ _ _ _) (inline-[]₀ B₁) $
         ⊢inline≡inline∷ u₁≡u₂)
        (⊢inline≡inline∷ v₁≡v₂) ok
    (K-β {B} ⊢B ⊢u ok) →
      PE.subst (_⊢_≡_∷_ _ _ _) (PE.sym $ inline-[]₀ B) $
      K-β (⊢inline ⊢B)
        (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢u)) ok
    ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) →
      []-cong-cong (⊢inline≡inline A₁≡A₂) (⊢inline≡inline∷ t₁≡t₂)
        (⊢inline≡inline∷ u₁≡u₂) (⊢inline≡inline∷ v₁≡v₂) ok
    ([]-cong-β ⊢t PE.refl ok) →
      []-cong-β (⊢inline∷ ⊢t) PE.refl ok
    (equality-reflection ok ⊢Id ⊢v) →
      equality-reflection ok (⊢inline ⊢Id) (⊢inline∷ ⊢v)

opaque
  unfolding inline

  -- Inlining preserves reduction.

  ⊢inline⇒inline∷ :
    ∇ ᵈ• ξ » Γ ⊢ t₁ ⇒ t₂ ∷ A →
    glassify ∇ » inline-Con ξ Γ ⊢
      inline ξ t₁ ⇒* inline ξ t₂ ∷ inline ξ A
  ⊢inline⇒inline∷ (conv t₁⇒t₂ A≡B) =
    conv* (⊢inline⇒inline∷ t₁⇒t₂) (⊢inline≡inline A≡B)
  ⊢inline⇒inline∷ (δ-red {t′ = t} {A′ = A} ⊢Γ α↦ PE.refl PE.refl) =
    PE.subst₂ (_⊢_⇒*_∷_ _ _) (wk-inline t) (wk-inline A) $
    wkRed*Term (wk₀∷ʷ⊇ (⊢inline-Con ⊢Γ)) $
    ⊢inline-Nat⇒*∷ (defn-wf ⊢Γ) α↦
  ⊢inline⇒inline∷ (emptyrec-subst ⊢A t₁⇒t₂) =
    emptyrec-subst* (⊢inline⇒inline∷ t₁⇒t₂) (⊢inline ⊢A)
  ⊢inline⇒inline∷ (unitrec-subst {A} ⊢A ⊢u t₁⇒t₂ _ no-η) =
    PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ inline-[]₀ A) $
    unitrec-subst* (⊢inline⇒inline∷ t₁⇒t₂) (⊢inline ⊢A)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢u))
      no-η
  ⊢inline⇒inline∷ (unitrec-β {A} ⊢A ⊢u _ _) =
    redMany $
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ inline-[]₀ A) $
    unitrec-β-⇒ (⊢inline ⊢A)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢u))
  ⊢inline⇒inline∷ (unitrec-β-η {A} ⊢A ⊢t ⊢u _ η) =
    redMany $
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ inline-[]₀ A) $
    unitrec-β-η-⇒ (⊢inline ⊢A) (⊢inline∷ ⊢t)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢u)) η
  ⊢inline⇒inline∷ (app-subst {G = B} t₁⇒t₂ ⊢u) =
    PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ inline-[]₀ B) $
    app-subst* (⊢inline⇒inline∷ t₁⇒t₂) (⊢inline∷ ⊢u)
  ⊢inline⇒inline∷ (β-red {G = B} {t} _ ⊢t ⊢u PE.refl ok) =
    redMany $
    PE.subst₂ (_⊢_⇒_∷_ _ _)
      (PE.sym $ inline-[]₀ t) (PE.sym $ inline-[]₀ B) $
    β-red-⇒ (⊢inline∷ ⊢t) (⊢inline∷ ⊢u) ok
  ⊢inline⇒inline∷ (fst-subst _ t₁⇒t₂) =
    fst-subst* (⊢inline⇒inline∷ t₁⇒t₂)
  ⊢inline⇒inline∷ (Σ-β₁ {G = B} ⊢B ⊢t ⊢u PE.refl ok) =
    redMany $
    Σ-β₁-⇒ (⊢inline ⊢B) (⊢inline∷ ⊢t)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢u)) ok
  ⊢inline⇒inline∷ (snd-subst {G = B} _ t₁⇒t₂) =
    PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ inline-[]₀ B) $
    snd-subst* (⊢inline⇒inline∷ t₁⇒t₂)
  ⊢inline⇒inline∷ (Σ-β₂ {G = B} ⊢B ⊢t ⊢u PE.refl ok) =
    redMany $
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ inline-[]₀ B) $
    Σ-β₂-⇒ (⊢inline ⊢B) (⊢inline∷ ⊢t)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢u)) ok
  ⊢inline⇒inline∷ (prodrec-subst {A = C} ⊢C ⊢u t₁⇒t₂ _) =
    PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ inline-[]₀ C) $
    prodrec-subst* (⊢inline ⊢C) (⊢inline⇒inline∷ t₁⇒t₂)
      (PE.subst (_⊢_∷_ _ _) (inline-[][]↑ C) (⊢inline∷ ⊢u))
  ⊢inline⇒inline∷
    (prodrec-β {G = B} {A = C} {u = v} ⊢C ⊢t ⊢u ⊢v PE.refl _) =
    redMany $
    PE.subst₂ (_⊢_⇒_∷_ _ _)
      (PE.sym $ inline-[]₁₀ v) (PE.sym $ inline-[]₀ C) $
    prodrec-β-⇒ (⊢inline ⊢C) (⊢inline∷ ⊢t)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢u))
      (PE.subst (_⊢_∷_ _ _) (inline-[][]↑ C) (⊢inline∷ ⊢v))
  ⊢inline⇒inline∷ (natrec-subst {A} ⊢t ⊢u v₁⇒v₂) =
    PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ inline-[]₀ A) $
    natrec-subst* (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢t))
      (PE.subst (_⊢_∷_ _ _) (inline-[][]↑ A) (⊢inline∷ ⊢u))
      (⊢inline⇒inline∷ v₁⇒v₂)
  ⊢inline⇒inline∷ (natrec-zero {A} ⊢t ⊢u) =
    redMany $
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ inline-[]₀ A) $
    natrec-zero (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢t))
      (PE.subst (_⊢_∷_ _ _) (inline-[][]↑ A) (⊢inline∷ ⊢u))
  ⊢inline⇒inline∷ (natrec-suc {A} {s = u} ⊢t ⊢u ⊢v) =
    redMany $
    PE.subst₂ (_⊢_⇒_∷_ _ _)
      (PE.sym $ inline-[]₁₀ u) (PE.sym $ inline-[]₀ A) $
    natrec-suc (PE.subst (_⊢_∷_ _ _) (inline-[]₀ A) (⊢inline∷ ⊢t))
      (PE.subst (_⊢_∷_ _ _) (inline-[][]↑ A) (⊢inline∷ ⊢u))
      (⊢inline∷ ⊢v)
  ⊢inline⇒inline∷ (J-subst {t} {A} {B} ⊢t ⊢B ⊢u ⊢v w₁⇒w₂) =
    PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ inline-[]₁₀ B) $
    J-subst*
      (PE.subst₂ _⊢_
         (PE.sym $ PE.cong (_»_ _) $ PE.cong (_∙_ _) $
          PE.cong₃ Id (wk-inline A) (wk-inline t) PE.refl)
         PE.refl $
       ⊢inline ⊢B)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₁₀ B) (⊢inline∷ ⊢u))
      (⊢inline⇒inline∷ w₁⇒w₂)
  ⊢inline⇒inline∷ (J-β {t} {A} {B} ⊢t ⊢t′ t≡t′ ⊢B B[]≡B[] ⊢u) =
    redMany $
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ inline-[]₁₀ B) $
    J-β-⇒ (⊢inline≡inline∷ t≡t′)
      (PE.subst₂ _⊢_
         (PE.sym $ PE.cong (_»_ _) $ PE.cong (_∙_ _) $
          PE.cong₃ Id (wk-inline A) (wk-inline t) PE.refl)
         PE.refl $
       ⊢inline ⊢B)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₁₀ B) (⊢inline∷ ⊢u))
  ⊢inline⇒inline∷ (K-subst {B} ⊢B ⊢u v₁⇒v₂ ok) =
    PE.subst (_⊢_⇒*_∷_ _ _ _) (PE.sym $ inline-[]₀ B) $
    K-subst* (⊢inline ⊢B)
      (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢u))
      (⊢inline⇒inline∷ v₁⇒v₂) ok
  ⊢inline⇒inline∷ (K-β {B} ⊢B ⊢u ok) =
    redMany $
    PE.subst (_⊢_⇒_∷_ _ _ _) (PE.sym $ inline-[]₀ B) $
    K-β (⊢inline ⊢B) (PE.subst (_⊢_∷_ _ _) (inline-[]₀ B) (⊢inline∷ ⊢u))
      ok
  ⊢inline⇒inline∷ ([]-cong-subst _ _ _ v₁⇒v₂ ok) =
    []-cong-subst* (⊢inline⇒inline∷ v₁⇒v₂) ok
  ⊢inline⇒inline∷ ([]-cong-β _ _ _ t≡t′ ok) =
    redMany $
    []-cong-β-⇒ (⊢inline≡inline∷ t≡t′) ok

opaque

  -- Inlining preserves reduction.

  ⊢inline⇒*inline∷ :
    ∇ ᵈ• ξ » Γ ⊢ t ⇒* u ∷ A →
    glassify ∇ » inline-Con ξ Γ ⊢ inline ξ t ⇒* inline ξ u ∷ inline ξ A
  ⊢inline⇒*inline∷ (id ⊢t)      = id (⊢inline∷ ⊢t)
  ⊢inline⇒*inline∷ (t⇒u ⇨ u⇒*v) =
    ⊢inline⇒inline∷ t⇒u ⇨∷* ⊢inline⇒*inline∷ u⇒*v

opaque
  unfolding inline

  -- Inlining preserves reduction.

  ⊢inline⇒inline :
    ∇ ᵈ• ξ » Γ ⊢ A ⇒ B →
    glassify ∇ » inline-Con ξ Γ ⊢ inline ξ A ⇒* inline ξ B
  ⊢inline⇒inline (univ A⇒B) = univ* (⊢inline⇒inline∷ A⇒B)

opaque

  -- Inlining preserves reduction.

  ⊢inline⇒*inline :
    ∇ ᵈ• ξ » Γ ⊢ A ⇒* B →
    glassify ∇ » inline-Con ξ Γ ⊢ inline ξ A ⇒* inline ξ B
  ⊢inline⇒*inline (id ⊢A)      = id (⊢inline ⊢A)
  ⊢inline⇒*inline (A⇒B ⇨ B⇒*C) =
    ⊢inline⇒inline A⇒B ⇨* ⊢inline⇒*inline B⇒*C

opaque

  -- Inlining preserves reduction for transparent contexts.

  ⊢inline↘inline :
    glassify (∇ ᵈ• ξ) » Γ ⊢ A ↘ B →
    glassify ∇ » inline-Con ξ Γ ⊢ inline ξ A ↘ inline ξ B
  ⊢inline↘inline (A⇒*B , B-whnf) =
    PE.subst₃ _⊢_⇒*_
      (PE.cong₂ _»_ (glassify-idem _) (inline-Con-glassifyᵉ _))
      (inline-glassifyᵉ _) (inline-glassifyᵉ _)
      (⊢inline⇒*inline $
       PE.subst₃ _⊢_⇒*_ (PE.cong (_» _) glassify-ᵈ•) PE.refl PE.refl
         A⇒*B) ,
    Whnf-inline B-whnf

opaque

  -- Inlining preserves reduction for transparent contexts.

  ⊢inline↘inline∷ :
    glassify (∇ ᵈ• ξ) » Γ ⊢ t ↘ u ∷ A →
    glassify ∇ » inline-Con ξ Γ ⊢ inline ξ t ↘ inline ξ u ∷ inline ξ A
  ⊢inline↘inline∷ (t⇒*u , u-whnf) =
    PE.subst₄ _⊢_⇒*_∷_
      (PE.cong₂ _»_ (glassify-idem _) (inline-Con-glassifyᵉ _))
      (inline-glassifyᵉ _) (inline-glassifyᵉ _) (inline-glassifyᵉ _)
      (⊢inline⇒*inline∷ $
       PE.subst₄ _⊢_⇒*_∷_
         (PE.cong (_» _) glassify-ᵈ•) PE.refl PE.refl PE.refl
         t⇒*u) ,
    Whnf-inline u-whnf

------------------------------------------------------------------------
-- Variants of some of the preservations lemmas related to inlining,
-- expressed for the "ᵈ" variants of the inlining functions

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline.

  ⊢inlineᵈ :
    ∇ » Γ ⊢ A →
    ε » inline-Conᵈ ∇ Γ ⊢ inlineᵈ ∇ A
  ⊢inlineᵈ =
    ⊢inline ∘→
    PE.subst₂ _⊢_ (PE.cong (_» _) (PE.sym εᵈ•as-DExt)) PE.refl

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline∷.

  ⊢inlineᵈ∷ :
    ∇ » Γ ⊢ t ∷ A →
    ε » inline-Conᵈ ∇ Γ ⊢ inlineᵈ ∇ t ∷ inlineᵈ ∇ A
  ⊢inlineᵈ∷ =
    ⊢inline∷ ∘→
    PE.subst₃ _⊢_∷_ (PE.cong (_» _) (PE.sym εᵈ•as-DExt)) PE.refl PE.refl

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline≡inline.

  ⊢inlineᵈ≡inlineᵈ :
    ∇ » Γ ⊢ A ≡ B →
    ε » inline-Conᵈ ∇ Γ ⊢ inlineᵈ ∇ A ≡ inlineᵈ ∇ B
  ⊢inlineᵈ≡inlineᵈ =
    ⊢inline≡inline ∘→
    PE.subst₃ _⊢_≡_ (PE.cong (_» _) (PE.sym εᵈ•as-DExt)) PE.refl PE.refl

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline≡inline∷.

  ⊢inlineᵈ≡inlineᵈ∷ :
    ∇ » Γ ⊢ t ≡ u ∷ A →
    ε » inline-Conᵈ ∇ Γ ⊢ inlineᵈ ∇ t ≡ inlineᵈ ∇ u ∷ inlineᵈ ∇ A
  ⊢inlineᵈ≡inlineᵈ∷ =
    ⊢inline≡inline∷ ∘→
    PE.subst₄ _⊢_≡_∷_
      (PE.cong (_» _) (PE.sym εᵈ•as-DExt)) PE.refl PE.refl PE.refl

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline⇒inline∷.

  ⊢inlineᵈ⇒inlineᵈ∷ :
    ∇ » Γ ⊢ t₁ ⇒ t₂ ∷ A →
    ε » inline-Conᵈ ∇ Γ ⊢ inlineᵈ ∇ t₁ ⇒* inlineᵈ ∇ t₂ ∷ inlineᵈ ∇ A
  ⊢inlineᵈ⇒inlineᵈ∷ =
    ⊢inline⇒inline∷ ∘→
    PE.subst₄ _⊢_⇒_∷_
      (PE.cong (_» _) (PE.sym εᵈ•as-DExt)) PE.refl PE.refl PE.refl

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline⇒*inline∷.

  ⊢inlineᵈ⇒*inlineᵈ∷ :
    ∇ » Γ ⊢ t ⇒* u ∷ A →
    ε » inline-Conᵈ ∇ Γ ⊢ inlineᵈ ∇ t ⇒* inlineᵈ ∇ u ∷ inlineᵈ ∇ A
  ⊢inlineᵈ⇒*inlineᵈ∷ =
    ⊢inline⇒*inline∷ ∘→
    PE.subst₄ _⊢_⇒*_∷_
      (PE.cong (_» _) (PE.sym εᵈ•as-DExt)) PE.refl PE.refl PE.refl

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline⇒inline.

  ⊢inlineᵈ⇒inlineᵈ :
    ∇ » Γ ⊢ A ⇒ B →
    ε » inline-Conᵈ ∇ Γ ⊢ inlineᵈ ∇ A ⇒* inlineᵈ ∇ B
  ⊢inlineᵈ⇒inlineᵈ =
    ⊢inline⇒inline ∘→
    PE.subst₃ _⊢_⇒_ (PE.cong (_» _) (PE.sym εᵈ•as-DExt)) PE.refl PE.refl

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline⇒*inline.

  ⊢inlineᵈ⇒*inlineᵈ :
    ∇ » Γ ⊢ A ⇒* B →
    ε » inline-Conᵈ ∇ Γ ⊢ inlineᵈ ∇ A ⇒* inlineᵈ ∇ B
  ⊢inlineᵈ⇒*inlineᵈ =
    ⊢inline⇒*inline ∘→
    PE.subst₃ _⊢_⇒*_
      (PE.cong (_» _) (PE.sym εᵈ•as-DExt)) PE.refl PE.refl

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline↘inline.

  ⊢inlineᵈ↘inlineᵈ :
    glassify ∇ » Γ ⊢ A ↘ B →
    ε » inline-Conᵈ ∇ Γ ⊢ inlineᵈ ∇ A ↘ inlineᵈ ∇ B
  ⊢inlineᵈ↘inlineᵈ =
    ⊢inline↘inline ∘→
    PE.subst₃ _⊢_↘_
      (PE.cong (_» _) (PE.cong glassify $ PE.sym εᵈ•as-DExt))
      PE.refl PE.refl

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline↘inline∷.

  ⊢inlineᵈ↘inlineᵈ∷ :
    glassify ∇ » Γ ⊢ t ↘ u ∷ A →
    ε » inline-Conᵈ ∇ Γ ⊢ inlineᵈ ∇ t ↘ inlineᵈ ∇ u ∷ inlineᵈ ∇ A
  ⊢inlineᵈ↘inlineᵈ∷ =
    ⊢inline↘inline∷ ∘→
    PE.subst₄ _⊢_↘_∷_
      (PE.cong (_» _) (PE.cong glassify $ PE.sym εᵈ•as-DExt))
      PE.refl PE.refl PE.refl

------------------------------------------------------------------------
-- Inlining produces definitionally equal terms

opaque
 unfolding inline _ᵈ•_
 mutual

  -- Inlining produces definitionally equal terms, given certain
  -- assumptions.

  ⊢inline-<≡defn∷ :
    {ξ : DExt (Term 0) n l} →
    {l≤α : l ≤ α} {α<n : α <′ n} →
    » ∇ ᵈ• ξ → α ↦∷ A ∈ ∇ ᵈ• ξ →
    glassify (∇ ᵈ• ξ) » ε ⊢ inline-< ξ l≤α α<n ≡ defn α ∷ A
  ⊢inline-<≡defn∷ {ξ = idᵉ} {l≤α = n≤α} {α<n} _ _ =
    ⊥-elim (n≮n _ (≤-trans (<′⇒< α<n) n≤α))
  ⊢inline-<≡defn∷ {α} {ξ = step ξ _ _ t} {α<n = ≤′-reflexive _}
    »ξ∙@(∙ᵗ[ ⊢t ]) here =
    inline ξ t  ≡⟨ defn-wkEqTerm (stepᵗ₁ (glassify-⊢∷ ⊢t)) (⊢inline≡∷ ⊢t) ⟩⊢
    t           ≡˘⟨ δ-red (ε (glassify-» »ξ∙)) here (PE.sym $ wk-id _) (PE.sym $ wk-id _) ⟩⊢∎
    defn α      ∎
    where
    open TmR
  ⊢inline-<≡defn∷ {α} {∇} {ξ = step ξ _ _ t} {α<n = ≤′-reflexive _}
    »ξ∙@(∙ᵒ⟨_⟩[_∷_] {φ} _ ⊢t _) here =
    inline ξ t  ≡⟨ defn-wkEqTerm
                     (stepᵗ₁ $
                      PE.subst₃ _⊢_∷_
                        (PE.cong (_» _) glassify-factor) PE.refl PE.refl $
                      glassify-⊢∷ ⊢t)
                     (PE.subst₄ _⊢_≡_∷_
                        (PE.cong (_» _)
                           (glassify
                              (Trans (remainder ξ φ) ∇ ᵈ• Transᵉ φ ξ)  ≡˘⟨ PE.cong glassify Trans-ᵈ• ⟩

                            glassify (Trans φ (∇ ᵈ• ξ))                ≡⟨ glassify-factor ⟩

                            glassify (∇ ᵈ• ξ)                          ∎))
                        (PE.sym $ inline-Transᵉ t) PE.refl PE.refl $
                      ⊢inline≡∷ $
                      PE.subst₃ _⊢_∷_ (PE.cong (_» _) Trans-ᵈ•) PE.refl PE.refl ⊢t) ⟩⊢
    t           ≡˘⟨ δ-red (ε (glassify-» »ξ∙)) here (PE.sym $ wk-id _) (PE.sym $ wk-id _) ⟩⊢∎
    defn α      ∎
    where
    open TmR
  ⊢inline-<≡defn∷ {ξ = step _ _ _ _} {α<n = ≤′-reflexive eq}
    _ (there α↦) =
    ⊥-elim $ n≮n _ $ PE.subst (_< _) (1+-injective eq) (scoped-↦∈ α↦)
  ⊢inline-<≡defn∷ {ξ = step _ _ _ _} {α<n = ≤′-step α<α} _ here =
    ⊥-elim (n≮n _ (<′⇒< α<α))
  ⊢inline-<≡defn∷ {ξ = step ξ _ _ _} {α<n = ≤′-step _}
    ∙ᵗ[ ⊢t ] (there α↦) =
    defn-wkEqTerm (stepᵗ₁ (glassify-⊢∷ ⊢t)) $
    ⊢inline-<≡defn∷ {ξ = ξ} (defn-wf (wfTerm ⊢t)) α↦
  ⊢inline-<≡defn∷ {ξ = step ξ _ _ _} {α<n = ≤′-step _}
    ∙ᵒ⟨ _ ⟩[ ⊢t ∷ ⊢A ] (there α↦) =
    defn-wkEqTerm
      (stepᵗ₁ $
       PE.subst₃ _⊢_∷_
         (PE.cong (_» _) glassify-factor) PE.refl PE.refl $
       glassify-⊢∷ ⊢t) $
    ⊢inline-<≡defn∷ {ξ = ξ} (defn-wf (wf ⊢A)) α↦

  -- Inlining produces definitionally equal terms, given certain
  -- assumptions.

  ⊢inline-Nat≡defn∷ :
    {ξ : DExt (Term 0) n l} →
    » ∇ ᵈ• ξ → α ↦∷ A ∈ ∇ ᵈ• ξ →
    glassify (∇ ᵈ• ξ) » ε ⊢ inline-Nat ξ α ≡ defn α ∷ A
  ⊢inline-Nat≡defn∷ {n} {l} {α} {ξ} »ξ α↦
    with l ≤? α
       | refl
           (defn (ε (glassify-» »ξ)) (glassify-↦∈ α↦)
              (PE.sym $ wk-id _))
  … | no _  | eq = eq
  … | yes _ | eq with α <′? n
  …   | no _  = eq
  …   | yes _ = ⊢inline-<≡defn∷ {ξ = ξ} »ξ α↦

  -- Inlining produces definitionally equal types, given a certain
  -- assumption.

  ⊢inline≡ :
    ∇ ᵈ• ξ » Γ ⊢ A →
    glassify (∇ ᵈ• ξ) » Γ ⊢ inline ξ A ≡ A
  ⊢inline≡ (Uⱼ ⊢Γ) =
    refl (Uⱼ (glassify-⊢′ ⊢Γ))
  ⊢inline≡ (univ ⊢A) =
    univ (⊢inline≡∷ ⊢A)
  ⊢inline≡ (Emptyⱼ ⊢Γ) =
    refl (Emptyⱼ (glassify-⊢′ ⊢Γ))
  ⊢inline≡ (Unitⱼ ⊢Γ ok) =
    refl (Unitⱼ (glassify-⊢′ ⊢Γ) ok)
  ⊢inline≡ (ΠΣⱼ ⊢B ok) =
    let ≡A = ⊢inline≡ (⊢∙→⊢ (wf ⊢B)) in
    ΠΣ-cong ≡A (stabilityEq (refl-∙ (sym ≡A)) (⊢inline≡ ⊢B)) ok
  ⊢inline≡ (ℕⱼ ⊢Γ) =
    refl (ℕⱼ (glassify-⊢′ ⊢Γ))
  ⊢inline≡ (Idⱼ ⊢A ⊢t ⊢u) =
    let ≡A = ⊢inline≡ ⊢A in
    Id-cong ≡A (conv (⊢inline≡∷ ⊢t) (sym ≡A))
      (conv (⊢inline≡∷ ⊢u) (sym ≡A))

  -- Inlining produces definitionally equal terms, given a certain
  -- assumption.

  ⊢inline≡∷ :
    ∇ ᵈ• ξ » Γ ⊢ t ∷ A →
    glassify (∇ ᵈ• ξ) » Γ ⊢ inline ξ t ≡ t ∷ A
  ⊢inline≡∷ (conv ⊢t B≡A) =
    conv (⊢inline≡∷ ⊢t) (glassify-⊢≡ B≡A)
  ⊢inline≡∷ (var ⊢Γ x∈) =
    refl (var (glassify-⊢′ ⊢Γ) x∈)
  ⊢inline≡∷ {ξ} (defn ⊢Γ α↦ PE.refl) =
    wkEqTerm (wk₀∷ʷ⊇ (glassify-⊢′ ⊢Γ)) $
    ⊢inline-Nat≡defn∷ {ξ = ξ} (defn-wf ⊢Γ) α↦
  ⊢inline≡∷ (Uⱼ ⊢Γ) =
    refl (Uⱼ (glassify-⊢′ ⊢Γ))
  ⊢inline≡∷ (Emptyⱼ ⊢Γ) =
    refl (Emptyⱼ (glassify-⊢′ ⊢Γ))
  ⊢inline≡∷ (emptyrecⱼ ⊢A ⊢t) =
    let ≡A = ⊢inline≡ ⊢A in
    conv (emptyrec-cong ≡A (⊢inline≡∷ ⊢t)) ≡A
  ⊢inline≡∷ (Unitⱼ ⊢Γ ok) =
    refl (Unitⱼ (glassify-⊢′ ⊢Γ) ok)
  ⊢inline≡∷ (starⱼ ⊢Γ ok) =
    refl (starⱼ (glassify-⊢′ ⊢Γ) ok)
  ⊢inline≡∷ (unitrecⱼ ⊢A ⊢t ⊢u ok) =
    let ≡A = ⊢inline≡ ⊢A
        ≡t = ⊢inline≡∷ ⊢t
    in
    conv
      (unitrec-cong′ ≡A ≡t
         (conv (⊢inline≡∷ ⊢u) $
          substTypeEq (sym ≡A) $
          refl (starⱼ (glassify-⊢′ (wfTerm ⊢t)) ok)))
      (substTypeEq ≡A ≡t)
  ⊢inline≡∷ (ΠΣⱼ ⊢A ⊢B ok) =
    let ≡A = ⊢inline≡∷ ⊢A in
    ΠΣ-cong ≡A (stabilityEqTerm (refl-∙ (sym (univ ≡A))) (⊢inline≡∷ ⊢B))
      ok
  ⊢inline≡∷ (lamⱼ _ ⊢t ok) =
    lam-cong (⊢inline≡∷ ⊢t) ok
  ⊢inline≡∷ (⊢t ∘ⱼ ⊢u) =
    let _ , ⊢B , _ = inversion-ΠΣ (wf-⊢∷ ⊢t)
        ≡u         = ⊢inline≡∷ ⊢u
    in
    conv (app-cong (⊢inline≡∷ ⊢t) ≡u)
      (substTypeEq (refl (glassify-⊢ ⊢B)) ≡u)
  ⊢inline≡∷ (prodⱼ ⊢B ⊢t ⊢u ok) =
    let ⊢B = glassify-⊢ ⊢B
        ≡t = ⊢inline≡∷ ⊢t
    in
    prod-cong ⊢B ≡t
      (conv (⊢inline≡∷ ⊢u) (substTypeEq (refl ⊢B) (sym′ ≡t))) ok
  ⊢inline≡∷ (fstⱼ _ ⊢t) =
    fst-cong′ (⊢inline≡∷ ⊢t)
  ⊢inline≡∷ (sndⱼ ⊢B ⊢t) =
    let ≡t = ⊢inline≡∷ ⊢t in
    conv (snd-cong′ ≡t)
      (substTypeEq (refl (glassify-⊢ ⊢B)) (fst-cong′ ≡t))
  ⊢inline≡∷ (prodrecⱼ ⊢A ⊢t ⊢u _) =
    let ≡A = ⊢inline≡ ⊢A
        ≡t = ⊢inline≡∷ ⊢t
    in
    conv
      (prodrec-cong′ ≡A ≡t
         (conv (⊢inline≡∷ ⊢u) (subst↑²TypeEq-prod (sym ≡A))))
      (substTypeEq ≡A ≡t)
  ⊢inline≡∷ (ℕⱼ ⊢Γ) =
    refl (ℕⱼ (glassify-⊢′ ⊢Γ))
  ⊢inline≡∷ (zeroⱼ ⊢Γ) =
    refl (zeroⱼ (glassify-⊢′ ⊢Γ))
  ⊢inline≡∷ (sucⱼ ⊢t) =
    suc-cong (⊢inline≡∷ ⊢t)
  ⊢inline≡∷ (natrecⱼ ⊢t ⊢u ⊢v) =
    let ⊢A = ⊢∙→⊢ (wfTerm ⊢u)
        ≡A = ⊢inline≡ ⊢A
        ≡v = ⊢inline≡∷ ⊢v
    in
    conv
      (natrec-cong ≡A
         (conv (⊢inline≡∷ ⊢t) $
          substTypeEq (sym ≡A) (refl (zeroⱼ (glassify-⊢′ (wfTerm ⊢t)))))
         (stabilityEqTerm (refl-∙ (sym ≡A)) $
          conv (⊢inline≡∷ ⊢u) $
          subst↑²TypeEq (sym ≡A) (refl (sucⱼ (var₁ (glassify-⊢ ⊢A)))))
         ≡v)
      (substTypeEq ≡A ≡v)
  ⊢inline≡∷ (Idⱼ ⊢A ⊢t ⊢u) =
    let ≡A  = ⊢inline≡∷ ⊢A
        ≡A′ = univ ≡A
    in
    Id-cong ≡A (conv (⊢inline≡∷ ⊢t) (sym ≡A′))
      (conv (⊢inline≡∷ ⊢u) (sym ≡A′))
  ⊢inline≡∷ (rflⱼ ⊢t) =
    refl (rflⱼ (glassify-⊢∷ ⊢t))
  ⊢inline≡∷ {ξ} (Jⱼ {t} {A} {v} ⊢t ⊢B ⊢u ⊢v ⊢w) =
    let ⊢A  = wf-⊢∷ ⊢t
        ⊢A′ = glassify-⊢ ⊢A
        ⊢t′ = glassify-⊢∷ ⊢t
        ≡A  = ⊢inline≡ ⊢A
        ≡t  = ⊢inline≡∷ ⊢t
        ≡B  = ⊢inline≡ ⊢B
        ≡v  = ⊢inline≡∷ ⊢v
        ≡w  = ⊢inline≡∷ ⊢w
    in
    conv
      (J-cong′ ≡A (conv ≡t (sym ≡A))
         (stabilityEq
             (refl-∙ (sym ≡A) ∙
              Id-cong (wkEq₁ ⊢A′ (sym ≡A)) (wkEqTerm₁ ⊢A′ (sym′ ≡t))
                (refl (var₀ ⊢A′)))
             ≡B)
         (conv (⊢inline≡∷ ⊢u) $
          substTypeEq₂ (sym ≡B) (sym′ ≡t)
            (refl (PE.subst (_⊢_∷_ _ _) ≡Id-wk1-wk1-0[]₀ (rflⱼ ⊢t′))))
         (conv ≡v (sym ≡A))
         (conv ≡w (Id-cong (sym ≡A) (sym′ ≡t) (sym′ ≡v))))
      (substTypeEq₂ ≡B ≡v $
       conv ≡w
         (Id A t v                                     ≡⟨ Id-cong (refl ⊢A′) (refl ⊢t′) (sym′ ≡v) ⟩⊢∎≡
          Id A t (inline ξ v)                          ≡⟨ ≡Id-wk1-wk1-0[]₀ ⟩
          Id (wk1 A) (wk1 t) (var x0) [ inline ξ v ]₀  ∎))
    where
    open TyR
  ⊢inline≡∷ (Kⱼ ⊢B ⊢u ⊢v ok) =
    let ⊢A , ⊢t , _ = inversion-Id (⊢∙→⊢ (wf ⊢B))
        ≡A          = ⊢inline≡ ⊢A
        ≡t          = ⊢inline≡∷ ⊢t
        ≡B          = ⊢inline≡ ⊢B
        ≡v          = ⊢inline≡∷ ⊢v
        Id-A-t-t≡   = Id-cong (sym ≡A) (sym′ ≡t) (sym′ ≡t)
    in
    conv
      (K-cong ≡A (conv ≡t (sym ≡A))
         (stabilityEq (refl-∙ Id-A-t-t≡) ≡B)
         (conv (⊢inline≡∷ ⊢u) $
          substTypeEq (sym ≡B) (refl (rflⱼ (glassify-⊢∷ ⊢t))))
         (conv ≡v Id-A-t-t≡) ok)
      (substTypeEq ≡B ≡v)
  ⊢inline≡∷ ([]-congⱼ ⊢A ⊢t ⊢u ⊢v ok) =
    let ≡A  = ⊢inline≡ ⊢A
        ≡t  = conv (⊢inline≡∷ ⊢t) (sym ≡A)
        ≡u  = conv (⊢inline≡∷ ⊢u) (sym ≡A)
        ok′ = []-cong→Erased ok
    in
    conv
      ([]-cong-cong ≡A ≡t ≡u
         (conv (⊢inline≡∷ ⊢v) (sym (Id-cong ≡A ≡t ≡u))) ok)
      (Id-cong (Erased-cong ok′ ≡A) ([]-cong′ ok′ ≡t) ([]-cong′ ok′ ≡u))

opaque
  unfolding inlineᵈ

  -- A variant of ⊢inline≡.

  ⊢inlineᵈ≡ :
    ∇ » Γ ⊢ A →
    glassify ∇ » Γ ⊢ inlineᵈ ∇ A ≡ A
  ⊢inlineᵈ≡ =
    PE.subst₃ _⊢_≡_
      (PE.cong ((_» _) ∘→ glassify) εᵈ•as-DExt) PE.refl PE.refl ∘→
    ⊢inline≡ ∘→
    PE.subst₂ _⊢_ (PE.cong (_» _) (PE.sym εᵈ•as-DExt)) PE.refl

opaque
  unfolding inlineᵈ

  -- A variant of ⊢inline≡∷.

  ⊢inlineᵈ≡∷ :
    ∇ » Γ ⊢ t ∷ A →
    glassify ∇ » Γ ⊢ inlineᵈ ∇ t ≡ t ∷ A
  ⊢inlineᵈ≡∷ =
    PE.subst₄ _⊢_≡_∷_
      (PE.cong ((_» _) ∘→ glassify) εᵈ•as-DExt)
      PE.refl PE.refl PE.refl ∘→
    ⊢inline≡∷ ∘→
    PE.subst₃ _⊢_∷_ (PE.cong (_» _) (PE.sym εᵈ•as-DExt)) PE.refl PE.refl

opaque
  unfolding inline-Con

  -- Inlining produces definitionally equal contexts, given a certain
  -- assumption.

  ⊢inline-Con≡ :
    ∇ ᵈ• ξ »⊢ Γ →
    glassify (∇ ᵈ• ξ) »⊢ inline-Con ξ Γ ≡ Γ
  ⊢inline-Con≡ (ε »∇) = ε (glassify-» »∇)
  ⊢inline-Con≡ (∙ ⊢A) =
    symConEq (symConEq (⊢inline-Con≡ (wf ⊢A)) ∙ sym (⊢inline≡ ⊢A))

opaque
  unfolding inline-Conᵈ

  -- A variant of ⊢inline-Con≡.

  ⊢inline-Conᵈ≡ :
    ∇ »⊢ Γ →
    glassify ∇ »⊢ inline-Conᵈ ∇ Γ ≡ Γ
  ⊢inline-Conᵈ≡ =
    PE.subst₃ _»⊢_≡_ (PE.cong glassify εᵈ•as-DExt) PE.refl PE.refl ∘→
    ⊢inline-Con≡ ∘→
    PE.subst (λ ⊢Γ → ⊢Γ »⊢ _) (PE.sym εᵈ•as-DExt)

------------------------------------------------------------------------
-- Some lemmas related to context extensions and glassification

opaque

  -- If a type A is well-formed under ∇ and inhabited under
  -- glassify ∇, then A is inhabited under an extension of ∇ (assuming
  -- that at least one Π-type is allowed or the variable context is
  -- empty).

  inhabited-under-extension :
    ∃₂ Π-allowed or-empty Γ →
    ∇ » Γ ⊢ A → glassify ∇ » Γ ⊢ t ∷ A →
    ∃₃ λ n (∇′ : DCon (Term 0) n) u → » ∇′ ⊇ ∇ × ∇′ » Γ ⊢ u ∷ A
  inhabited-under-extension {Γ} ok ⊢A ⊢t =
    let »∇ = defn-wf (wf ⊢A) in
    case Opacity-allowed? of λ where
      (no no-opacity) →
        let transparent = »→Transparent no-opacity »∇ in
        _ , _ , _ , id⊇ ,
        PE.subst₃ _⊢_∷_
          (PE.cong (_» _) (PE.sym transparent)) PE.refl PE.refl
        ⊢t
      (yes opacity) →
        let p,q,ok : ∃₂ λ p q → Π-allowed p q or-empty Γ
            p,q,ok = case ok of λ where
              (possibly-nonempty ⦃ ok = p , q , ok ⦄) →
                p , q , possibly-nonempty ⦃ ok = ok ⦄
              ε →
                Modality.ω 𝕄 , Modality.ω 𝕄 , ε

            ok = p,q,ok .proj₂ .proj₂

            ext-ok =
              stepᵒ₁ opacity (⊢Πs ok ⊢A)
                (⊢lams ok $
                 PE.subst₃ _⊢_∷_
                   (PE.cong (_» _) $ PE.sym Trans-ones) PE.refl PE.refl
                   ⊢t)
        in
        _ , _ , _ , ext-ok ,
        ⊢apps ok (defn (ε (wf-»⊇ ext-ok »∇)) here (PE.sym $ wk-id _))

opaque
  unfolding _ᵈ•_

  -- If a type A is well-formed under ∇ and inhabited under a
  -- well-formed extension of ∇, then A is inhabited under glassify ∇.

  inhabited-under-glassified-context :
    ∇ » Γ ⊢ A → » ∇′ ⊇ ∇ → ∇′ » Γ ⊢ t ∷ A →
    ∃ λ t → glassify ∇ » Γ ⊢ t ∷ A
  inhabited-under-glassified-context {Γ} {A} {t} ⊢A ∇′⊇∇ ⊢t =
    case »⊇→ ∇′⊇∇ of λ {
      (ξ , PE.refl) →
    inline ξ t ,
    PE.subst₃ _⊢_∷_
      (PE.cong (_»_ _)
         (inline-Con ξ Γ    ≡˘⟨ inline-Con-⊇ ∇′⊇∇ (wf ⊢A) ⟩
          inline-Con idᵉ Γ  ≡⟨ inline-Con-id _ ⟩
          Γ                 ∎))
      PE.refl
      (inline ξ A    ≡˘⟨ inline-⊇-⊢ ∇′⊇∇ ⊢A ⟩
       inline idᵉ A  ≡⟨ inline-id _ ⟩
       A             ∎)
      (⊢inline∷ ⊢t) }

------------------------------------------------------------------------
-- Opaque[_∷_]

-- A definition context with a single opaque definition of the given
-- type (the second argument) that is equal to the given term (the
-- first argument).

Opaque[_∷_] : Term 0 → Term 0 → DCon (Term 0) 1
Opaque[ t ∷ A ] = ε ∙⟨ opa ε ⟩[ t ∷ A ]

opaque

  -- There are no transparent definitions in Opaque[ u ∷ B ].

  ¬↦∷∈Opaque : ¬ α ↦ t ∷ A ∈ Opaque[ u ∷ B ]
  ¬↦∷∈Opaque (there ())

opaque
  unfolding Trans

  -- If t has type A and opaque definitions are allowed, then
  -- Opaque[ t ∷ A ] is well-formed.

  »Opaque : Opacity-allowed → ε » ε ⊢ t ∷ A → » Opaque[ t ∷ A ]
  »Opaque ok ⊢t = ∙ᵒ⟨ ok ⟩[ ⊢t ∷ wf-⊢∷ ⊢t ]

-- Below it is assumed that opaque definitions are allowed, and that
-- there are three closed terms A, t and u that satisfy ε » ε ⊢ u ∷ A
-- (there are no requirements on t).

module _
  (ok : Opacity-allowed)
  {A t u : Term 0}
  (⊢u : ε » ε ⊢ u ∷ A)
  where

  opaque mutual

    -- If Γ is well-formed under Opaque[ t ∷ A ] and α points to B in
    -- Opaque[ t ∷ A ], then defn α has type wk wk₀ B under
    -- Opaque[ u ∷ A ] and Γ.

    definition-irrelevant-defn :
      Opaque[ t ∷ A ] »⊢ Γ → α ↦∷ B ∈ Opaque[ t ∷ A ] →
      Opaque[ u ∷ A ] » Γ ⊢ defn α ∷ wk wk₀ B
    definition-irrelevant-defn ⊢Γ here =
      defn (definition-irrelevant-»⊢ ⊢Γ) here PE.refl
    definition-irrelevant-defn ⊢Γ (there ())

    -- Any context that is well-formed under Opaque[ t ∷ A ] is also
    -- well-formed under Opaque[ u ∷ A ].

    definition-irrelevant-»⊢ : Opaque[ t ∷ A ] »⊢ Γ → Opaque[ u ∷ A ] »⊢ Γ
    definition-irrelevant-»⊢ (ε _)  = ε (»Opaque ok ⊢u)
    definition-irrelevant-»⊢ (∙ ⊢A) = ∙ definition-irrelevant-⊢ ⊢A

    -- Any type that is well-formed under Opaque[ t ∷ A ] is also
    -- well-formed under Opaque[ u ∷ A ].

    definition-irrelevant-⊢ :
      Opaque[ t ∷ A ] » Γ ⊢ B → Opaque[ u ∷ A ] » Γ ⊢ B
    definition-irrelevant-⊢ (Uⱼ ⊢Γ) =
      Uⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢ (univ ⊢A) =
      univ (definition-irrelevant-⊢∷ ⊢A)
    definition-irrelevant-⊢ (Emptyⱼ ⊢Γ) =
      Emptyⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢ (Unitⱼ ⊢Γ ok) =
      Unitⱼ (definition-irrelevant-»⊢ ⊢Γ) ok
    definition-irrelevant-⊢ (ΠΣⱼ ⊢A ok) =
      ΠΣⱼ (definition-irrelevant-⊢ ⊢A) ok
    definition-irrelevant-⊢ (ℕⱼ ⊢Γ) =
      ℕⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢ (Idⱼ ⊢A ⊢t ⊢u) =
      Idⱼ (definition-irrelevant-⊢ ⊢A) (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u)

    -- Any term that is well-typed under Opaque[ t ∷ A ] is also
    -- well-typed under Opaque[ u ∷ A ].

    definition-irrelevant-⊢∷ :
      Opaque[ t ∷ A ] » Γ ⊢ v ∷ B →
      Opaque[ u ∷ A ] » Γ ⊢ v ∷ B
    definition-irrelevant-⊢∷ (conv ⊢t B≡A) =
      conv (definition-irrelevant-⊢∷ ⊢t) (definition-irrelevant-⊢≡ B≡A)
    definition-irrelevant-⊢∷ (var ⊢Γ x∈) =
      var (definition-irrelevant-»⊢ ⊢Γ) x∈
    definition-irrelevant-⊢∷ (defn ⊢Γ α↦ PE.refl) =
      definition-irrelevant-defn ⊢Γ α↦
    definition-irrelevant-⊢∷ (Uⱼ ⊢Γ) =
      Uⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢∷ (Emptyⱼ ⊢Γ) =
      Emptyⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢∷ (emptyrecⱼ ⊢A ⊢t) =
      emptyrecⱼ (definition-irrelevant-⊢ ⊢A)
        (definition-irrelevant-⊢∷ ⊢t)
    definition-irrelevant-⊢∷ (Unitⱼ ⊢Γ ok) =
      Unitⱼ (definition-irrelevant-»⊢ ⊢Γ) ok
    definition-irrelevant-⊢∷ (starⱼ ⊢Γ ok) =
      starⱼ (definition-irrelevant-»⊢ ⊢Γ) ok
    definition-irrelevant-⊢∷ (unitrecⱼ ⊢A ⊢t ⊢u ok) =
      unitrecⱼ (definition-irrelevant-⊢ ⊢A) (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u) ok
    definition-irrelevant-⊢∷ (ΠΣⱼ ⊢A ⊢B ok) =
      ΠΣⱼ (definition-irrelevant-⊢∷ ⊢A) (definition-irrelevant-⊢∷ ⊢B) ok
    definition-irrelevant-⊢∷ (lamⱼ ⊢B ⊢t ok) =
      lamⱼ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢t) ok
    definition-irrelevant-⊢∷ (⊢t ∘ⱼ ⊢u) =
      definition-irrelevant-⊢∷ ⊢t ∘ⱼ definition-irrelevant-⊢∷ ⊢u
    definition-irrelevant-⊢∷ (prodⱼ ⊢B ⊢t ⊢u ok) =
      prodⱼ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u) ok
    definition-irrelevant-⊢∷ (fstⱼ ⊢B ⊢t) =
      fstⱼ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢t)
    definition-irrelevant-⊢∷ (sndⱼ ⊢B ⊢t) =
      sndⱼ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢t)
    definition-irrelevant-⊢∷ (prodrecⱼ ⊢A ⊢t ⊢u ok) =
      prodrecⱼ (definition-irrelevant-⊢ ⊢A) (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u) ok
    definition-irrelevant-⊢∷ (ℕⱼ ⊢Γ) =
      ℕⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢∷ (zeroⱼ ⊢Γ) =
      zeroⱼ (definition-irrelevant-»⊢ ⊢Γ)
    definition-irrelevant-⊢∷ (sucⱼ ⊢t) =
      sucⱼ (definition-irrelevant-⊢∷ ⊢t)
    definition-irrelevant-⊢∷ (natrecⱼ ⊢t ⊢u ⊢v) =
      natrecⱼ (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u) (definition-irrelevant-⊢∷ ⊢v)
    definition-irrelevant-⊢∷ (Idⱼ ⊢A ⊢t ⊢u) =
      Idⱼ (definition-irrelevant-⊢∷ ⊢A) (definition-irrelevant-⊢∷ ⊢t)
        (definition-irrelevant-⊢∷ ⊢u)
    definition-irrelevant-⊢∷ (rflⱼ ⊢t) =
      rflⱼ (definition-irrelevant-⊢∷ ⊢t)
    definition-irrelevant-⊢∷ (Jⱼ _ ⊢B ⊢u _ ⊢w) =
      Jⱼ′ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢u)
        (definition-irrelevant-⊢∷ ⊢w)
    definition-irrelevant-⊢∷ (Kⱼ ⊢B ⊢u ⊢v ok) =
      Kⱼ (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢u)
        (definition-irrelevant-⊢∷ ⊢v) ok
    definition-irrelevant-⊢∷ ([]-congⱼ _ _ _ ⊢v ok) =
      []-congⱼ′ ok (definition-irrelevant-⊢∷ ⊢v)

    -- Definitional equalities that hold under Opaque[ t ∷ A ] also
    -- hold under Opaque[ u ∷ A ].

    definition-irrelevant-⊢≡ :
      Opaque[ t ∷ A ] » Γ ⊢ B ≡ C →
      Opaque[ u ∷ A ] » Γ ⊢ B ≡ C
    definition-irrelevant-⊢≡ = λ where
      (refl ⊢A) →
        refl (definition-irrelevant-⊢ ⊢A)
      (sym B≡A) →
        sym (definition-irrelevant-⊢≡ B≡A)
      (trans A≡B B≡C) →
        trans (definition-irrelevant-⊢≡ A≡B)
          (definition-irrelevant-⊢≡ B≡C)
      (univ A≡B) →
        univ (definition-irrelevant-⊢≡∷ A≡B)
      (ΠΣ-cong A₁≡B₁ A₂≡B₂ ok) →
        ΠΣ-cong (definition-irrelevant-⊢≡ A₁≡B₁)
          (definition-irrelevant-⊢≡ A₂≡B₂) ok
      (Id-cong A≡B t₁≡u₁ t₂≡u₂) →
        Id-cong (definition-irrelevant-⊢≡ A≡B)
          (definition-irrelevant-⊢≡∷ t₁≡u₁)
          (definition-irrelevant-⊢≡∷ t₂≡u₂)

    -- Definitional equalities that hold under Opaque[ t ∷ A ] also
    -- hold under Opaque[ u ∷ A ].

    definition-irrelevant-⊢≡∷ :
      Opaque[ t ∷ A ] » Γ ⊢ v ≡ w ∷ B →
      Opaque[ u ∷ A ] » Γ ⊢ v ≡ w ∷ B
    definition-irrelevant-⊢≡∷ = λ where
      (refl ⊢t) →
        refl (definition-irrelevant-⊢∷ ⊢t)
      (sym _ t₂≡t₁) →
        sym′ (definition-irrelevant-⊢≡∷ t₂≡t₁)
      (trans t₁≡t₂ t₂≡t₃) →
        trans (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ t₂≡t₃)
      (conv t₁≡t₂ B≡A) →
        conv (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡ B≡A)
      (δ-red _ α↦t _ _) →
        ⊥-elim (¬↦∷∈Opaque α↦t)
      (emptyrec-cong A₁≡A₂ t₁≡t₂) →
        emptyrec-cong (definition-irrelevant-⊢≡ A₁≡A₂)
         (definition-irrelevant-⊢≡∷ t₁≡t₂)
      (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ _ _) →
        unitrec-cong′ (definition-irrelevant-⊢≡ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
      (unitrec-β ⊢A ⊢t _ _) →
        unitrec-β-≡ (definition-irrelevant-⊢ ⊢A)
          (definition-irrelevant-⊢∷ ⊢t)
      (unitrec-β-η ⊢A ⊢t ⊢u _ η) →
        unitrec-β-η-≡ (definition-irrelevant-⊢ ⊢A)
          (definition-irrelevant-⊢∷ ⊢t) (definition-irrelevant-⊢∷ ⊢u) η
      (η-unit ⊢t₁ ⊢t₂ ok) →
        η-unit (definition-irrelevant-⊢∷ ⊢t₁)
          (definition-irrelevant-⊢∷ ⊢t₂) ok
      (ΠΣ-cong A₁≡A₂ B₁≡B₂ ok) →
        ΠΣ-cong (definition-irrelevant-⊢≡∷ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ B₁≡B₂) ok
      (app-cong t₁≡t₂ u₁≡u₂) →
        app-cong (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
      (β-red _ ⊢t ⊢u PE.refl ok) →
        β-red-≡ (definition-irrelevant-⊢∷ ⊢t)
          (definition-irrelevant-⊢∷ ⊢u) ok
      (η-eq ⊢B ⊢t₁ ⊢t₂ t₁0≡t₂0 ok) →
        η-eq′ (definition-irrelevant-⊢∷ ⊢t₁)
          (definition-irrelevant-⊢∷ ⊢t₂)
          (definition-irrelevant-⊢≡∷ t₁0≡t₂0)
      (fst-cong _ t₁≡t₂) →
        fst-cong′ (definition-irrelevant-⊢≡∷ t₁≡t₂)
      (Σ-β₁ ⊢B ⊢t₁ ⊢t₂ PE.refl ok) →
        Σ-β₁-≡ (definition-irrelevant-⊢ ⊢B)
          (definition-irrelevant-⊢∷ ⊢t₁) (definition-irrelevant-⊢∷ ⊢t₂)
           ok
      (snd-cong _ t₁≡t₂) →
        snd-cong′ (definition-irrelevant-⊢≡∷ t₁≡t₂)
      (Σ-β₂ ⊢B ⊢t₁ ⊢t₂ PE.refl ok) →
        Σ-β₂-≡ (definition-irrelevant-⊢ ⊢B)
          (definition-irrelevant-⊢∷ ⊢t₁) (definition-irrelevant-⊢∷ ⊢t₂)
          ok
      (Σ-η _ ⊢t₁ ⊢t₂ fst≡fst snd≡snd _) →
        Σ-η′ (definition-irrelevant-⊢∷ ⊢t₁)
          (definition-irrelevant-⊢∷ ⊢t₂)
          (definition-irrelevant-⊢≡∷ fst≡fst)
          (definition-irrelevant-⊢≡∷ snd≡snd)
      (prod-cong ⊢B t₁≡t₂ u₁≡u₂ ok) →
        prod-cong (definition-irrelevant-⊢ ⊢B)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂) ok
      (prodrec-cong C₁≡C₂ t₁≡t₂ u₁≡u₂ ok) →
        prodrec-cong′ (definition-irrelevant-⊢≡ C₁≡C₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
      (prodrec-β ⊢C ⊢t ⊢u ⊢v PE.refl ok) →
        prodrec-β-≡ (definition-irrelevant-⊢ ⊢C)
          (definition-irrelevant-⊢∷ ⊢t) (definition-irrelevant-⊢∷ ⊢u)
          (definition-irrelevant-⊢∷ ⊢v)
      (suc-cong t₁≡t₂) →
        suc-cong (definition-irrelevant-⊢≡∷ t₁≡t₂)
      (natrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) →
        natrec-cong (definition-irrelevant-⊢≡ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
          (definition-irrelevant-⊢≡∷ v₁≡v₂)
      (natrec-zero ⊢t ⊢u) →
        natrec-zero (definition-irrelevant-⊢∷ ⊢t)
          (definition-irrelevant-⊢∷ ⊢u)
      (natrec-suc ⊢t ⊢u ⊢v) →
        natrec-suc (definition-irrelevant-⊢∷ ⊢t)
          (definition-irrelevant-⊢∷ ⊢u) (definition-irrelevant-⊢∷ ⊢v)
      (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) →
        Id-cong (definition-irrelevant-⊢≡∷ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
      (J-cong A₁≡A₂ ⊢t₁ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) →
        J-cong′ (definition-irrelevant-⊢≡ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡ B₁≡B₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
          (definition-irrelevant-⊢≡∷ v₁≡v₂)
          (definition-irrelevant-⊢≡∷ w₁≡w₂)
      (J-β ⊢t ⊢B ⊢u PE.refl) →
        J-β-≡ (definition-irrelevant-⊢∷ ⊢t) (definition-irrelevant-⊢ ⊢B)
          (definition-irrelevant-⊢∷ ⊢u)
      (K-cong A₁≡A₂ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) →
        K-cong (definition-irrelevant-⊢≡ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡ B₁≡B₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
          (definition-irrelevant-⊢≡∷ v₁≡v₂) ok
      (K-β ⊢B ⊢u ok) →
        K-β (definition-irrelevant-⊢ ⊢B) (definition-irrelevant-⊢∷ ⊢u)
          ok
      ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) →
        []-cong-cong (definition-irrelevant-⊢≡ A₁≡A₂)
          (definition-irrelevant-⊢≡∷ t₁≡t₂)
          (definition-irrelevant-⊢≡∷ u₁≡u₂)
          (definition-irrelevant-⊢≡∷ v₁≡v₂) ok
      ([]-cong-β ⊢t PE.refl ok) →
        []-cong-β (definition-irrelevant-⊢∷ ⊢t) PE.refl ok
      (equality-reflection ok ⊢Id ⊢v) →
        equality-reflection ok (definition-irrelevant-⊢ ⊢Id)
          (definition-irrelevant-⊢∷ ⊢v)
