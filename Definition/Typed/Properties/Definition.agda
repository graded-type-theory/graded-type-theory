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
open import Definition.Typed.Properties.Admissible.Identity R
open import Definition.Typed.Properties.Admissible.Nat R
open import Definition.Typed.Properties.Admissible.Pi R
open import Definition.Typed.Properties.Admissible.Sigma R
open import Definition.Typed.Properties.Admissible.Unit R
open import Definition.Typed.Properties.Reduction R
open import Definition.Typed.Properties.Well-formed R
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
open import Tools.Vec using (ε)

open import Definition.Typed.Properties.Definition.Primitive R
  public

private variable
  α n n′              : Nat
  x                   : Fin _
  ∇ ∇′                : DCon _ _
  Γ                   : Con Term _
  A B C t t₁ t₂ u v w : Term _
  φ                   : Unfolding _
  p q                 : M

------------------------------------------------------------------------
-- Some lemmas related to context extensions

opaque

  -- If a closed type A is well-formed under ∇ and inhabited under
  -- glassify ∇, then A is inhabited under an extension of ∇.
  --
  -- See also inhabited-under-extension below.

  inhabited-under-extension₀ :
    ∇ » ε ⊢ A → glassify ∇ » ε ⊢ t ∷ A →
    ∃₃ λ n (∇′ : DCon (Term 0) n) u → » ∇′ ⊇ ∇ × ∇′ » ε ⊢ u ∷ A
  inhabited-under-extension₀ {A} {t} ⊢A ⊢t =
    let »∇ = defn-wf (wf ⊢A) in
    case Opacity-allowed? of λ where
      (no no-opacity) →
        let transparent = »→Transparent no-opacity »∇ in
        _  , _ , t , id⊇ ,
        PE.subst₃ _⊢_∷_
          (PE.cong (_» _) (PE.sym transparent)) PE.refl PE.refl
        ⊢t
      (yes opacity) →
        let ext-ok =
              stepᵒ₁ opacity ⊢A
                (PE.subst₃ _⊢_∷_
                   (PE.cong (_» _) $ PE.sym Trans-ones) PE.refl PE.refl
                   ⊢t) in
        _ , _ , defn _ , ext-ok ,
        defn (ε (wf-»⊇ ext-ok »∇)) here (PE.sym $ wk-id _)

opaque

  -- If a type A is well-formed under ∇ and inhabited under
  -- glassify ∇, then A is inhabited under an extension of ∇ (assuming
  -- that at least one Π-type is allowed).

  inhabited-under-extension :
    Π-allowed p q →
    ∇ » Γ ⊢ A → glassify ∇ » Γ ⊢ t ∷ A →
    ∃₃ λ n (∇′ : DCon (Term 0) n) u → » ∇′ ⊇ ∇ × ∇′ » Γ ⊢ u ∷ A
  inhabited-under-extension {p} {q} {Γ} {A} {t} ok ⊢A ⊢t =
    let »∇ = defn-wf (wf ⊢A) in
    case Opacity-allowed? of λ where
      (no no-opacity) →
        let transparent = »→Transparent no-opacity »∇ in
        _ , _ , t , id⊇ ,
        PE.subst₃ _⊢_∷_
          (PE.cong (_» _) (PE.sym transparent)) PE.refl PE.refl
        ⊢t
      (yes opacity) →
        let ext-ok =
              stepᵒ₁ opacity (⊢Πs ok ⊢A)
                (⊢lams ok $
                 PE.subst₃ _⊢_∷_
                   (PE.cong (_» _) $ PE.sym Trans-ones) PE.refl PE.refl
                   ⊢t)
        in
        _ , _ , apps p Γ (defn _) , ext-ok ,
        ⊢apps ok (defn (ε (wf-»⊇ ext-ok »∇)) here (PE.sym $ wk-id _))

------------------------------------------------------------------------
-- Properties related to inlining of definitions

opaque
 unfolding inline Trans
 mutual

  -- The result of inline-< is invariant under transparentisation of
  -- definition contexts.

  inline-<-Trans :
    (α<n : α <′ n) →
    inline-< ∇ α<n PE.≡ inline-< (Trans φ ∇) α<n
  inline-<-Trans {∇ = ε} α<n =
    ⊥-elim (n≮0 (<′⇒< α<n))
  inline-<-Trans {∇ = _ ∙⟨ tra ⟩[ t ∷ _ ]} (≤′-reflexive _) =
    inline-Trans t
  inline-<-Trans {∇ = ∇ ∙⟨ tra ⟩[ t ∷ _ ]} (≤′-step α<n) =
    inline-<-Trans {∇ = ∇} α<n
  inline-<-Trans
    {∇ = _ ∙⟨ opa _ ⟩[ t ∷ _ ]} {φ = _ ⁰} (≤′-reflexive _) =
    inline-Trans t
  inline-<-Trans {∇ = ∇ ∙⟨ opa _ ⟩!} {φ = _ ⁰} (≤′-step α<n) =
    inline-<-Trans {∇ = ∇} α<n
  inline-<-Trans
    {∇ = _ ∙⟨ opa _ ⟩[ t ∷ _ ]} {φ = _ ¹} (≤′-reflexive _) =
    inline-Trans t
  inline-<-Trans {∇ = ∇ ∙⟨ opa _ ⟩!} {φ = _ ¹} (≤′-step α<n) =
    inline-<-Trans {∇ = ∇} α<n

  -- The result of inline-Nat is invariant under transparentisation of
  -- definition contexts.

  inline-Nat-Trans :
    {∇ : DCon (Term 0) n} →
    inline-Nat ∇ α PE.≡ inline-Nat (Trans φ ∇) α
  inline-Nat-Trans {n} {α} {∇} with α <′? n
  … | yes α<n = inline-<-Trans {∇ = ∇} α<n
  … | no _    = PE.refl

  -- The result of inline is invariant under transparentisation of
  -- definition contexts.

  inline-Trans :
    (t : Term n) →
    inline ∇ t PE.≡ inline (Trans φ ∇) t
  inline-Trans (var _) =
    PE.refl
  inline-Trans {∇} (defn _) =
    PE.cong (wk _) (inline-Nat-Trans {∇ = ∇})
  inline-Trans (U _) =
    PE.refl
  inline-Trans Empty =
    PE.refl
  inline-Trans (emptyrec p A t) =
    PE.cong₂ (emptyrec _) (inline-Trans A) (inline-Trans t)
  inline-Trans (Unit _ _) =
    PE.refl
  inline-Trans (star _ _) =
    PE.refl
  inline-Trans (unitrec _ _ _ A t u) =
    PE.cong₃ (unitrec _ _ _) (inline-Trans A) (inline-Trans t)
      (inline-Trans u)
  inline-Trans (ΠΣ⟨ _ ⟩ _ , _ ▷ A ▹ B) =
    PE.cong₂ (ΠΣ⟨ _ ⟩ _ , _ ▷_▹_) (inline-Trans A) (inline-Trans B)
  inline-Trans (lam p t) =
    PE.cong (lam _) (inline-Trans t)
  inline-Trans (t ∘⟨ p ⟩ u) =
    PE.cong₂ (_∘⟨ _ ⟩_) (inline-Trans t) (inline-Trans u)
  inline-Trans (prod s p t u) =
    PE.cong₂ (prod _ _) (inline-Trans t) (inline-Trans u)
  inline-Trans (fst p t) =
    PE.cong (fst _) (inline-Trans t)
  inline-Trans (snd p t) =
    PE.cong (snd _) (inline-Trans t)
  inline-Trans (prodrec r p q A t u) =
    PE.cong₃ (prodrec _ _ _) (inline-Trans A) (inline-Trans t)
      (inline-Trans u)
  inline-Trans ℕ =
    PE.refl
  inline-Trans zero =
    PE.refl
  inline-Trans (suc t) =
    PE.cong suc (inline-Trans t)
  inline-Trans (natrec p q r A t u v) =
    PE.cong₄ (natrec _ _ _) (inline-Trans A) (inline-Trans t)
      (inline-Trans u) (inline-Trans v)
  inline-Trans (Id A t u) =
    PE.cong₃ Id (inline-Trans A) (inline-Trans t) (inline-Trans u)
  inline-Trans rfl =
    PE.refl
  inline-Trans (J p q A t B u v w) =
    PE.cong₆ (J _ _) (inline-Trans A) (inline-Trans t) (inline-Trans B)
      (inline-Trans u) (inline-Trans v) (inline-Trans w)
  inline-Trans (K p A t B u v) =
    PE.cong₅ (K _) (inline-Trans A) (inline-Trans t) (inline-Trans B)
      (inline-Trans u) (inline-Trans v)
  inline-Trans ([]-cong s A t u v) =
    PE.cong₄ ([]-cong _) (inline-Trans A) (inline-Trans t)
      (inline-Trans u) (inline-Trans v)

opaque
 unfolding inline
 mutual

  -- The result of inline-< is invariant under definition context
  -- extension.

  inline-<-⊇ :
    {∇  : DCon (Term 0) n}
    {∇′ : DCon (Term 0) n′} →
    » ∇′ ⊇ ∇ →
    (α<n  : α <′ n)
    (α<n′ : α <′ n′) →
    inline-< ∇ α<n PE.≡ inline-< ∇′ α<n′
  inline-<-⊇ {∇} id⊇ α<n α<n′ =
    PE.cong (inline-< ∇) <′-propositional
  inline-<-⊇ (step ∇′⊇∇ _) α<n ≤′-refl =
    ⊥-elim (n≮n _ (≤-trans (<′⇒< α<n) (⊇→≤ ∇′⊇∇)))
  inline-<-⊇ (step ∇′⊇∇ _) α<n (≤′-step α<n′) =
    inline-<-⊇ ∇′⊇∇ α<n α<n′

  -- The result of inline-Nat is invariant under definition context
  -- extension (for names that are in scope).

  inline-Nat-⊇ :
    {∇  : DCon (Term 0) n}
    {∇′ : DCon (Term 0) n′} →
    » ∇′ ⊇ ∇ →
    α <′ n →
    inline-Nat ∇ α PE.≡ inline-Nat ∇′ α
  inline-Nat-⊇ {n} {n′} {α} ∇′⊇∇ α<n with α <′? n | α <′? n′
  … | yes α<n | yes α<n′ = inline-<-⊇ ∇′⊇∇ α<n α<n′
  … | no α≮n  | _        = ⊥-elim (α≮n α<n)
  … | _       | no α≮n′  =
    ⊥-elim (α≮n′ (<⇒<′ (≤-trans (<′⇒< α<n) (⊇→≤ ∇′⊇∇))))

  -- The result of inline is invariant under definition context
  -- extension (for well-formed types).

  inline-⊇-⊢ :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ A →
    inline ∇ A PE.≡ inline ∇′ A
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

  -- The result of inline is invariant under definition context
  -- extension (for well-typed terms).

  inline-⊇-⊢∷ :
    » ∇′ ⊇ ∇ →
    ∇ » Γ ⊢ t ∷ A →
    inline ∇ t PE.≡ inline ∇′ t
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
  unfolding inline-Con

  -- If x ∷ A ∈ Γ holds, then x ∷ inline ∇ A ∈ inline-Con ∇ Γ holds.

  inline∈ : x ∷ A ∈ Γ → x ∷ inline ∇ A ∈ inline-Con ∇ Γ
  inline∈ here =
    PE.subst₂ (_∷_∈_ _) (wk-inline _) PE.refl here
  inline∈ (there x∈) =
    PE.subst₂ (_∷_∈_ _) (wk-inline _) PE.refl $
    there (inline∈ x∈)

opaque
  unfolding inline

  -- If α points to t, then inline-< ∇ α<n is propositionally equal to
  -- inline ∇ t, given certain assumptions.

  inline-<≡ :
    {∇ : DCon (Term 0) n}
    (α<n : α <′ n) →
    » ∇ → α ↦ t ∷ A ∈ ∇ →
    inline-< ∇ α<n PE.≡ inline ∇ t
  inline-<≡ α<0 ε _ =
    ⊥-elim (n≮0 (<′⇒< α<0))
  inline-<≡ (≤′-reflexive _) (∙ᵗ[_] {∇} {t} {A} ⊢t) here =
    inline ∇ t                      ≡⟨ inline-⊇-⊢∷ (stepᵗ₁ ⊢t) ⊢t ⟩
    inline (∇ ∙⟨ tra ⟩[ t ∷ A ]) t  ∎
  inline-<≡ ≤′-refl _ (there α∈) =
    ⊥-elim (n≮n _ (scoped-↦∷∈ α∈))
  inline-<≡ (≤′-step α<α) _ here =
    ⊥-elim (n≮n _ (<′⇒< α<α))
  inline-<≡
    {t} (≤′-step α<n)
    (∙ᵒ⟨_⟩[_∷_] {φ} {∇} {t = u} {A = B} ok ⊢u ⊢B) (there α∈) =
    let s = stepᵒ₁ ok ⊢B ⊢u in
    inline-< ∇ α<n                    ≡⟨ inline-<≡ α<n (defn-wf (wf ⊢B)) α∈ ⟩

    inline ∇ t                        ≡⟨ inline-⊇-⊢∷ s $
                                         PE.subst₂ (_⊢_∷_ _) wk₀-closed wk₀-closed $
                                         wf-⊢≡∷ (δ-red (wf ⊢B) α∈ PE.refl PE.refl) .proj₂ .proj₂ ⟩
    inline (∇ ∙⟨ opa φ ⟩[ u ∷ B ]) t  ∎
  inline-<≡
    {t} (≤′-step α<n) (∙ᵗ[_] {∇} {t = u} {A = B} ⊢t) (there α∈) =
    let s = stepᵗ₁ ⊢t in
    inline-< ∇ α<n                    ≡⟨ inline-<≡ α<n (defn-wf (wfTerm ⊢t)) α∈ ⟩

    inline ∇ t                        ≡⟨ inline-⊇-⊢∷ s $
                                         PE.subst₂ (_⊢_∷_ _) wk₀-closed wk₀-closed $
                                         wf-⊢≡∷ (δ-red (wfTerm ⊢t) α∈ PE.refl PE.refl) .proj₂ .proj₂ ⟩
    inline (∇ ∙⟨ tra ⟩[ u ∷ B ]) t  ∎

opaque

  -- If α points to t, then inline-Nat ∇ α is propositionally equal to
  -- inline ∇ t, given certain assumptions.

  inline-Nat≡ :
    » ∇ → α ↦ t ∷ A ∈ ∇ →
    inline-Nat ∇ α PE.≡ inline ∇ t
  inline-Nat≡ {∇} {α} {t} »∇ α∈ =
    inline-Nat ∇ α                     ≡⟨ <-inline-Nat (<⇒<′ (scoped-↦∷∈ α∈)) ⟩
    inline-< ∇ (<⇒<′ (scoped-↦∷∈ α∈))  ≡⟨ inline-<≡ _ »∇ α∈ ⟩
    inline ∇ t                         ∎

opaque
 unfolding inline inline-Con
 mutual

  -- The function inline-< produces well-typed terms, given
  -- certain assumptions.

  ⊢inline-<∷ :
    {∇ : DCon (Term 0) n}
    (α<n : α <′ n) →
    » ∇ → α ↦∷ A ∈ ∇ →
    ε » ε ⊢ inline-< ∇ α<n ∷ inline ∇ A
  ⊢inline-<∷ α<0 ε _ =
    ⊥-elim (n≮0 (<′⇒< α<0))
  ⊢inline-<∷
    (≤′-reflexive _) (∙ᵒ⟨_⟩[_∷_] {φ} {∇} {t} {A} ok ⊢t ⊢A) here =
    PE.subst₂ (_⊢_∷_ _)
      (PE.sym $ inline-Trans t)
      (inline (Trans φ ∇) A              ≡˘⟨ inline-Trans A ⟩
       inline ∇ A                        ≡⟨ inline-⊇-⊢ (stepᵒ₁ ok ⊢A ⊢t) ⊢A ⟩
       inline (∇ ∙⟨ opa φ ⟩[ t ∷ A ]) A  ∎) $
    ⊢inline∷ ⊢t
  ⊢inline-<∷ (≤′-reflexive _) ∙ᵗ[ ⊢t ] here =
    PE.subst (_⊢_∷_ _ _) (inline-⊇-⊢ (stepᵗ₁ ⊢t) (wf-⊢∷ ⊢t)) $
    ⊢inline∷ ⊢t
  ⊢inline-<∷ ≤′-refl _ (there α∈) =
    ⊥-elim (n≮n _ (scoped-↦∈ α∈))
  ⊢inline-<∷ (≤′-step α<α) _ here =
    ⊥-elim (n≮n _ (<′⇒< α<α))
  ⊢inline-<∷ (≤′-step α<n) ∙ᵒ⟨ ok ⟩[ ⊢t ∷ ⊢B ] (there α∈) =
    PE.subst (_⊢_∷_ _ _)
      (inline-⊇-⊢ (stepᵒ₁ ok ⊢B ⊢t) $
       PE.subst (_⊢_ _) wk₀-closed $
       wf-⊢∷ (defn (wf ⊢B) α∈ PE.refl)) $
    ⊢inline-<∷ α<n (defn-wf (wf ⊢B)) α∈
  ⊢inline-<∷ (≤′-step α<n) ∙ᵗ[ ⊢t ] (there α∈) =
    PE.subst (_⊢_∷_ _ _)
      (inline-⊇-⊢ (stepᵗ₁ ⊢t) $
       PE.subst (_⊢_ _) wk₀-closed $
       wf-⊢∷ (defn (wfTerm ⊢t) α∈ PE.refl)) $
    ⊢inline-<∷ α<n (defn-wf (wfTerm ⊢t)) α∈

  -- The function inline-Nat produces well-typed terms, given certain
  -- assumptions.

  ⊢inline-Nat∷ :
    » ∇ → α ↦∷ A ∈ ∇ →
    ε » ε ⊢ inline-Nat ∇ α ∷ inline ∇ A
  ⊢inline-Nat∷ »∇ α∈ =
    PE.subst (flip (_⊢_∷_ _) _)
      (PE.sym $ <-inline-Nat (<⇒<′ (scoped-↦∈ α∈))) $
    ⊢inline-<∷ _ »∇ α∈

  -- If α points to t, then inline-< ∇ α<n is definitionally equal to
  -- inline ∇ t, given certain assumptions.

  ⊢inline-<≡∷ :
    {∇ : DCon (Term 0) n}
    (α<n : α <′ n) →
    » ∇ → α ↦ t ∷ A ∈ ∇ →
    ε » ε ⊢ inline-< ∇ α<n ≡ inline ∇ t ∷ inline ∇ A
  ⊢inline-<≡∷ α<n »∇ α↦t =
    PE.subst₂ (_⊢_≡_∷_ _ _) (inline-<≡ α<n »∇ α↦t) PE.refl $
    refl (⊢inline-<∷ α<n »∇ (↦∷∈⇒↦∈ α↦t))

  -- If α points to t, then inline-Nat ∇ α is definitionally equal to
  -- inline ∇ t, given certain assumptions.

  ⊢inline-Nat≡∷ :
    » ∇ → α ↦ t ∷ A ∈ ∇ →
    ε » ε ⊢ inline-Nat ∇ α ≡ inline ∇ t ∷ inline ∇ A
  ⊢inline-Nat≡∷ »∇ α∈ =
    PE.subst₃ (_⊢_≡_∷_ _)
      (PE.sym $ <-inline-Nat (<⇒<′ (scoped-↦∷∈ α∈))) PE.refl PE.refl $
    ⊢inline-<≡∷ _ »∇ α∈

  -- Inlining preserves context well-formedness.

  ⊢inline-Con : ∇ »⊢ Γ → ε »⊢ inline-Con ∇ Γ
  ⊢inline-Con (ε _)  = ε ε
  ⊢inline-Con (∙ ⊢A) = ∙ ⊢inline ⊢A

  -- Inlining preserves type well-formedness.

  ⊢inline :
    ∇ » Γ ⊢ A →
    ε » inline-Con ∇ Γ ⊢ inline ∇ A
  ⊢inline (Uⱼ ⊢Γ) =
    Uⱼ (⊢inline-Con ⊢Γ)
  ⊢inline (univ ⊢A) =
    univ (⊢inline∷ ⊢A)
  ⊢inline (Emptyⱼ ⊢Γ) =
    Emptyⱼ (⊢inline-Con ⊢Γ)
  ⊢inline (Unitⱼ ⊢Γ ok) =
    Unitⱼ (⊢inline-Con ⊢Γ) ok
  ⊢inline (ΠΣⱼ ⊢A ok) =
    ΠΣⱼ (⊢inline ⊢A) ok
  ⊢inline (ℕⱼ ⊢Γ) =
    ℕⱼ (⊢inline-Con ⊢Γ)
  ⊢inline (Idⱼ ⊢A ⊢t ⊢u) =
    Idⱼ (⊢inline ⊢A) (⊢inline∷ ⊢t) (⊢inline∷ ⊢u)

  -- Inlining preserves well-typedness.

  ⊢inline∷ :
    ∇ » Γ ⊢ t ∷ A →
    ε » inline-Con ∇ Γ ⊢ inline ∇ t ∷ inline ∇ A
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
    ∇ » Γ ⊢ A ≡ B →
    ε » inline-Con ∇ Γ ⊢ inline ∇ A ≡ inline ∇ B
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
    ∇ » Γ ⊢ t ≡ u ∷ A →
    ε » inline-Con ∇ Γ ⊢ inline ∇ t ≡ inline ∇ u ∷ inline ∇ A
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
  unfolding inline inline-Con

  -- Inlining preserves reduction.

  ⊢inline⇒inline∷ :
    ∇ » Γ ⊢ t₁ ⇒ t₂ ∷ A →
    ε » inline-Con ∇ Γ ⊢ inline ∇ t₁ ⇒* inline ∇ t₂ ∷ inline ∇ A
  ⊢inline⇒inline∷ (conv t₁⇒t₂ A≡B) =
    conv* (⊢inline⇒inline∷ t₁⇒t₂) (⊢inline≡inline A≡B)
  ⊢inline⇒inline∷
    {∇} (δ-red {α} {t′ = t} {A′ = A} ⊢Γ α↦ PE.refl PE.refl) =
    PE.subst₂ (_⊢_⇒*_∷_ _ _)
      (inline ∇ (defn α)        ≡⟨⟩
       wk wk₀ (inline-Nat ∇ α)  ≡⟨ PE.cong (wk _) $ inline-Nat≡ (defn-wf ⊢Γ) α↦ ⟩
       wk wk₀ (inline ∇ t)      ≡⟨ wk-inline t ⟩
       inline ∇ (wk wk₀ t)      ∎)
      (wk-inline A) $
    id $
    wkTerm (wk₀∷ʷ⊇ (⊢inline-Con ⊢Γ))
      (⊢inline-Nat∷ (defn-wf ⊢Γ) (↦∷∈⇒↦∈ α↦))
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
    ∇ » Γ ⊢ t ⇒* u ∷ A →
    ε » inline-Con ∇ Γ ⊢ inline ∇ t ⇒* inline ∇ u ∷ inline ∇ A
  ⊢inline⇒*inline∷ (id ⊢t)      = id (⊢inline∷ ⊢t)
  ⊢inline⇒*inline∷ (t⇒u ⇨ u⇒*v) =
    ⊢inline⇒inline∷ t⇒u ⇨∷* ⊢inline⇒*inline∷ u⇒*v

opaque
  unfolding inline

  -- Inlining preserves reduction.

  ⊢inline⇒inline :
    ∇ » Γ ⊢ A ⇒ B →
    ε » inline-Con ∇ Γ ⊢ inline ∇ A ⇒* inline ∇ B
  ⊢inline⇒inline (univ A⇒B) = univ* (⊢inline⇒inline∷ A⇒B)

opaque

  -- Inlining preserves reduction.

  ⊢inline⇒*inline :
    ∇ » Γ ⊢ A ⇒* B →
    ε » inline-Con ∇ Γ ⊢ inline ∇ A ⇒* inline ∇ B
  ⊢inline⇒*inline (id ⊢A)      = id (⊢inline ⊢A)
  ⊢inline⇒*inline (A⇒B ⇨ B⇒*C) =
    ⊢inline⇒inline A⇒B ⇨* ⊢inline⇒*inline B⇒*C

opaque

  -- Inlining preserves reduction for transparent contexts.

  ⊢inline↘inline :
    glassify ∇ » Γ ⊢ A ↘ B →
    ε » inline-Con ∇ Γ ⊢ inline ∇ A ↘ inline ∇ B
  ⊢inline↘inline (A⇒*B , B-whnf) =
    PE.subst₃ _⊢_⇒*_ (PE.cong (_»_ _) $ inline-Con-glassify _)
      (inline-glassify _) (inline-glassify _)
      (⊢inline⇒*inline A⇒*B) ,
    Whnf-inline B-whnf

opaque

  -- Inlining preserves reduction for transparent contexts.

  ⊢inline↘inline∷ :
    glassify ∇ » Γ ⊢ t ↘ u ∷ A →
    ε » inline-Con ∇ Γ ⊢ inline ∇ t ↘ inline ∇ u ∷ inline ∇ A
  ⊢inline↘inline∷ (t⇒*u , u-whnf) =
    PE.subst₄ _⊢_⇒*_∷_ (PE.cong (_»_ _) $ inline-Con-glassify _)
      (inline-glassify _) (inline-glassify _) (inline-glassify _)
      (⊢inline⇒*inline∷ t⇒*u) ,
    Whnf-inline u-whnf

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
