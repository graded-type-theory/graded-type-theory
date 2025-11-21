------------------------------------------------------------------------
-- Some lemmas related to Names<
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Names-below
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open import Definition.Typed R
open import Definition.Typed.Inversion R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening.Definition R
open import Definition.Typed.Well-formed R

open import Definition.Untyped M
open import Definition.Untyped.Names-below M
open import Definition.Untyped.Properties M

open import Tools.Empty
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  α n             : Nat
  ∇ ∇₁ ∇₂         : DCon (Term 0) _
  Γ               : Con Term _
  A B C l t u v w : Term _

opaque mutual

  -- If ∇ » Γ ⊢ A holds, where ∇ has length n, then A only uses names
  -- below n.

  ⊢→Names< :
    {∇ : DCon (Term 0) n} →
    ∇ » Γ ⊢ A → Names< n A
  ⊢→Names< (Levelⱼ _ _) =
    Level
  ⊢→Names< (univ ⊢A) =
    ⊢∷→Names< ⊢A
  ⊢→Names< (Liftⱼ ⊢l ⊢A) =
    Lift (⊢∷L→Names< ⊢l) (⊢→Names< ⊢A)
  ⊢→Names< (ΠΣⱼ ⊢B _) =
    ΠΣ (⊢→Names< (⊢∙→⊢ (wf ⊢B))) (⊢→Names< ⊢B)
  ⊢→Names< (Idⱼ ⊢A ⊢t ⊢u) =
    Id (⊢→Names< ⊢A) (⊢∷→Names< ⊢t) (⊢∷→Names< ⊢u)

  -- If ∇ » Γ ⊢ t ∷ A holds, where ∇ has length n, then t only uses
  -- names below n.

  ⊢∷→Names< :
    {∇ : DCon (Term 0) n} →
    ∇ » Γ ⊢ t ∷ A → Names< n t
  ⊢∷→Names< (conv ⊢t _) =
    ⊢∷→Names< ⊢t
  ⊢∷→Names< (var _ _) =
    var
  ⊢∷→Names< (defn ⊢Γ α↦ _) =
    defn (scoped-↦∈ α↦)
  ⊢∷→Names< (Levelⱼ _ _) =
    Level
  ⊢∷→Names< (zeroᵘⱼ _ _) =
    zeroᵘ
  ⊢∷→Names< (sucᵘⱼ ⊢l) =
    sucᵘ (⊢∷→Names< ⊢l)
  ⊢∷→Names< (supᵘⱼ ⊢l₁ ⊢l₂) =
    supᵘ (⊢∷→Names< ⊢l₁) (⊢∷→Names< ⊢l₂)
  ⊢∷→Names< (Uⱼ ⊢l) =
    U (⊢∷L→Names< ⊢l)
  ⊢∷→Names< (Liftⱼ _ ⊢l ⊢A) =
    Lift (⊢∷L→Names< ⊢l) (⊢∷→Names< ⊢A)
  ⊢∷→Names< (liftⱼ _ _ ⊢t) =
    lift (⊢∷→Names< ⊢t)
  ⊢∷→Names< (lowerⱼ ⊢t) =
    lower (⊢∷→Names< ⊢t)
  ⊢∷→Names< (Emptyⱼ _) =
    Empty
  ⊢∷→Names< (emptyrecⱼ ⊢A ⊢t) =
    emptyrec (⊢→Names< ⊢A) (⊢∷→Names< ⊢t)
  ⊢∷→Names< (Unitⱼ _ _) =
    Unit
  ⊢∷→Names< (starⱼ _ _) =
    star
  ⊢∷→Names< (unitrecⱼ ⊢A ⊢t ⊢u _) =
    unitrec (⊢→Names< ⊢A) (⊢∷→Names< ⊢t) (⊢∷→Names< ⊢u)
  ⊢∷→Names< (ΠΣⱼ _ ⊢A ⊢B _) =
    ΠΣ (⊢∷→Names< ⊢A) (⊢∷→Names< ⊢B)
  ⊢∷→Names< (lamⱼ _ ⊢t _) =
    lam (⊢∷→Names< ⊢t)
  ⊢∷→Names< (⊢t ∘ⱼ ⊢u) =
    app (⊢∷→Names< ⊢t) (⊢∷→Names< ⊢u)
  ⊢∷→Names< (prodⱼ _ ⊢t ⊢u _) =
    prod (⊢∷→Names< ⊢t) (⊢∷→Names< ⊢u)
  ⊢∷→Names< (fstⱼ _ ⊢t) =
    fst (⊢∷→Names< ⊢t)
  ⊢∷→Names< (sndⱼ _ ⊢t) =
    snd (⊢∷→Names< ⊢t)
  ⊢∷→Names< (prodrecⱼ ⊢C ⊢t ⊢u _) =
    prodrec (⊢→Names< ⊢C) (⊢∷→Names< ⊢t) (⊢∷→Names< ⊢u)
  ⊢∷→Names< (ℕⱼ _) =
    ℕ
  ⊢∷→Names< (zeroⱼ _) =
    zero
  ⊢∷→Names< (sucⱼ ⊢t) =
    suc (⊢∷→Names< ⊢t)
  ⊢∷→Names< (natrecⱼ ⊢t ⊢u ⊢v) =
    natrec (⊢→Names< (⊢∙→⊢ (wfTerm ⊢u))) (⊢∷→Names< ⊢t) (⊢∷→Names< ⊢u)
      (⊢∷→Names< ⊢v)
  ⊢∷→Names< (Idⱼ ⊢A ⊢t ⊢u) =
    Id (⊢∷→Names< ⊢A) (⊢∷→Names< ⊢t) (⊢∷→Names< ⊢u)
  ⊢∷→Names< (rflⱼ ⊢t) =
    rfl
  ⊢∷→Names< (Jⱼ ⊢t ⊢B ⊢u ⊢v ⊢w) =
    J (⊢→Names< (wf-⊢∷ ⊢t)) (⊢∷→Names< ⊢t) (⊢→Names< ⊢B) (⊢∷→Names< ⊢u)
      (⊢∷→Names< ⊢v) (⊢∷→Names< ⊢w)
  ⊢∷→Names< (Kⱼ ⊢B ⊢u ⊢v _) =
    let ⊢A , ⊢t , _ = inversion-Id (wf-⊢∷ ⊢v) in
    K (⊢→Names< ⊢A) (⊢∷→Names< ⊢t) (⊢→Names< ⊢B) (⊢∷→Names< ⊢u)
      (⊢∷→Names< ⊢v)
  ⊢∷→Names< ([]-congⱼ ⊢l ⊢A ⊢t ⊢u ⊢v _) =
    []-cong (⊢∷L→Names< ⊢l) (⊢→Names< ⊢A) (⊢∷→Names< ⊢t) (⊢∷→Names< ⊢u)
      (⊢∷→Names< ⊢v)

  -- If ∇ » Γ ⊢ l ∷Level holds, where ∇ has length n, then l only uses
  -- names below n.

  ⊢∷L→Names< :
    {∇ : DCon (Term 0) n} →
    ∇ » Γ ⊢ l ∷Level → Names< n l
  ⊢∷L→Names< (term _ ⊢l) =
    ⊢∷→Names< ⊢l
  ⊢∷L→Names< (literal _ _ l-lit) =
    Level-literal→Names< l-lit

opaque

  -- If ∇ is well-formed and α points to some type A in ∇, then A only
  -- uses names below α.

  ↦∷→Names< : » ∇ → α ↦∷ A ∈ ∇ → Names< α A
  ↦∷→Names< ε        ()
  ↦∷→Names< ∙ᵗ[ ⊢t ] here =
    ⊢→Names< (wf-⊢∷ ⊢t)
  ↦∷→Names< ∙ᵗ[ ⊢t ] (there α↦) =
    ↦∷→Names< (defn-wf (wfTerm ⊢t)) α↦
  ↦∷→Names< ∙ᵒ⟨ _ ⟩[ _ ∷ ⊢A ] here =
    ⊢→Names< ⊢A
  ↦∷→Names< ∙ᵒ⟨ _ ⟩[ _ ∷ ⊢A ] (there α↦) =
    ↦∷→Names< (defn-wf (wf ⊢A)) α↦

opaque

  -- If ∇ is well-formed and α points to some term t in ∇, then t only
  -- uses names below α.

  ↦→Names< : » ∇ → α ↦ t ∷ A ∈ ∇ → Names< α t
  ↦→Names< ε        ()
  ↦→Names< ∙ᵗ[ ⊢t ] here =
    ⊢∷→Names< ⊢t
  ↦→Names< ∙ᵗ[ ⊢t ] (there α↦) =
    ↦→Names< (defn-wf (wfTerm ⊢t)) α↦
  ↦→Names< ∙ᵒ⟨ _ ⟩[ _ ∷ ⊢A ] (there α↦) =
    ↦→Names< (defn-wf (wf ⊢A)) α↦

opaque

  -- If α points to t in ∇₂, ∇₂ is an extension of ∇₁, and α is not
  -- out of range for ∇₁, then α points to t in ∇₁.

  <→⊇→↦→↦ :
    {∇₁ : DCon (Term 0) n} →
    α < n →
    » ∇₂ ⊇ ∇₁ →
    α ↦ t ∷ A ∈ ∇₂ →
    α ↦ t ∷ A ∈ ∇₁
  <→⊇→↦→↦ _   id⊇            α↦t         = α↦t
  <→⊇→↦→↦ α<n (step ∇₂⊇∇₁ _) (there α↦t) = <→⊇→↦→↦ α<n ∇₂⊇∇₁ α↦t
  <→⊇→↦→↦ α<n (step ∇₂⊇∇₁ _) here        =
    ⊥-elim (n≮n _ (≤-trans α<n (⊇→≤ ∇₂⊇∇₁)))
