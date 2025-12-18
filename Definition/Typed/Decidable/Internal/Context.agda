------------------------------------------------------------------------
-- Some definitions related to contexts used by
-- Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.Decidable.Internal.Context
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR

open import Definition.Typed TR as T hiding (Trans)
open import Definition.Typed.Decidable.Internal.Monad TR
open import Definition.Typed.Decidable.Internal.Term TR
open import Definition.Typed.Decidable.Internal.Weakening TR
open import Definition.Typed.Properties TR
open import Definition.Typed.Reasoning.Type TR
open import Definition.Typed.Weakening.Definition TR
open import Definition.Typed.Well-formed TR

open import Definition.Untyped M as U
  using (Opacity; Unfolding; Wk; _⁰; _¹; _⊔ᵒ_; _»_; _↦∷_∈_; _↦_∷_∈_)
open import Definition.Untyped.Properties M

open U.Con
open Opacity
open Wk
open _↦∷_∈_
open _↦_∷_∈_

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Maybe using (nothing; just)
open import Tools.Nat as N using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
import Tools.Vec as V

private variable
  α m n : Nat
  x     : Fin _
  c     : Constants
  ∇     : DCon _ _
  γ     : Contexts _
  φ     : Unfolding _
  A t   : Term _ _

------------------------------------------------------------------------
-- Lookup procedures

-- Definition context lookup for types.

type-of : DCon c n → Nat → Check c (Term c 0)
type-of (base _) _ =
  fail "No definition was found: the base context was encountered."
type-of ε _ =
  fail "No definition was found: an empty context was encountered."
type-of (_∙⟨_⟩[_∷_] {n} _ _ _ _) α with α N.≟ n
type-of (_∙⟨_⟩[_∷_]     ∇ _ _ _) α | no _  = type-of ∇ α
type-of (_∙⟨_⟩[_∷_]     _ _ _ A) α | yes _ = return A

opaque

  -- Soundness for type-of.

  type-of-sound :
    (∇ : DCon c n) →
    OK (type-of ∇ α) A γ →
    α ↦∷ ⌜ A ⌝ γ ∈ ⌜ ∇ ⌝ᶜᵈ γ
  type-of-sound     (base _)                 not-ok
  type-of-sound     ε                        not-ok
  type-of-sound {α} (_∙⟨_⟩[_∷_] {n} ∇ _ _ _) _      with α N.≟ n
  type-of-sound     _                        ok!    | yes PE.refl = here
  type-of-sound     (∇ ∙⟨ _ ⟩[ _ ∷ _ ])      eq     | no _        =
    there (type-of-sound ∇ eq)

-- Definition context lookup for definitions.

definition-of : DCon c n → Nat → Check c (Term c 0 × Term c 0)
definition-of (base _) _ =
  fail "No definition was found: the base context was encountered."
definition-of ε _ =
  fail "No definition was found: an empty context was encountered."
definition-of (_∙⟨_⟩[_∷_] {n} _ _ _ _) α with α N.≟ n
definition-of (∇ ∙⟨ _     ⟩[ _ ∷ _ ])  α | no _  = definition-of ∇ α
definition-of (_ ∙⟨ tra   ⟩[ t ∷ A ])  _ | yes _ = return (t , A)
definition-of (_ ∙⟨ opa _ ⟩[ _ ∷ _ ])  _ | yes _ =
  fail "Tried to access an opaque definition."

opaque

  -- Soundness for definition-of.

  definition-of-sound :
    (∇ : DCon c n) →
    OK (definition-of ∇ α) (t , A) γ →
    » ⌜ ∇ ⌝ᶜᵈ γ →
    α ↦ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ ∈ ⌜ ∇ ⌝ᶜᵈ γ ×
    (∀ {B} →
     α ↦∷ B ∈ ⌜ ∇ ⌝ᶜᵈ γ →
     ⌜ ∇ ⌝ᶜᵈ γ » ε ⊢ ⌜ A ⌝ γ ≡ B)
  definition-of-sound     (base _)                 not-ok
  definition-of-sound     ε                        not-ok
  definition-of-sound {α} (_∙⟨_⟩[_∷_] {n} _ _ _ _) _      _
    with α N.≟ n
  definition-of-sound _ not-ok ∙ᵒ⟨ _ ⟩[ _ ∷ _ ] | yes _
  definition-of-sound
    {γ} (_ ∙⟨ _ ⟩[ _ ∷ A ]) ok! ∙ᵗ[ ⊢t ] | yes PE.refl =
    here ,
    (λ {B = B} α↦ →
       ⌜ A ⌝ γ  ≡⟨ refl (defn-wk (stepᵗ₁ ⊢t) (wf-⊢∷ ⊢t)) ⟩⊢∎≡
       ⌜ A ⌝ γ  ≡⟨ unique-↦∈ here α↦ PE.refl ⟩
       B        ∎)
  definition-of-sound (∇ ∙⟨ _ ⟩[ _ ∷ _ ]) eq »∙ | no _ =
    let α↦ , hyp = definition-of-sound ∇ eq (»∙→» »∙) in
    there α↦ ,
    (λ where
       here       → ⊥-elim (N.n≮n _ (↦∷∈→< (↦∷∈⇒↦∈ α↦)))
       (there α↦) → defn-wkEq (»∙→»∙⊇ »∙) (hyp α↦))

-- Variable context indexing.
--
-- This procedure can fail if the base context is used.

index : Con c n → Fin n → Check c (Term c n)
index base _ =
  fail "Expected a non-empty context, found the base context."
index ε       ()
index (_ ∙ A) x0     = return (weaken (step id) A)
index (Γ ∙ _) (x +1) = wk (step id) <$> index Γ x

opaque

  -- Soundness for index.

  index-sound :
    ∀ Δ {A : Term c n} {B γ} →
    OK (index Δ x) A γ →
    ⌜ A ⌝ γ PE.≡ B ⇔ x ∷ B ∈ ⌜ Δ ⌝ᶜᵛ γ
  index-sound          base    not-ok
  index-sound {x = ()} ε
  index-sound {x = x0} (_ ∙ _) ok!    =
    (λ { PE.refl → here }) , (λ { here → PE.refl })
  index-sound {x = _ +1} (Δ ∙ _) {γ} eq
    with inv-<$> eq
  … | inv A eq PE.refl =
    (λ { PE.refl →
         PE.subst (flip (_∷_∈_ _) _) (PE.sym (⌜wk⌝ A)) $
         there (index-sound Δ eq .proj₁ PE.refl) }) ,
    (λ { (there {A = B} x∈) →
         ⌜ wk (step id) A ⌝ γ  ≡⟨ ⌜wk⌝ A ⟩
         U.wk1 (⌜ A ⌝ γ)       ≡⟨ PE.cong U.wk1 (index-sound Δ eq .proj₂ x∈) ⟩
         U.wk1 B               ∎ })

------------------------------------------------------------------------
-- Transparentisation

-- Transparentisation.

Trans : Unfolding n → DCon c n → DCon c n
Trans φ (base nothing) =
  base (just φ)
Trans φ (base (just φ′)) =
  base (just (φ′ ⊔ᵒ φ))
Trans _ ε =
  ε
Trans φ (∇ ∙⟨ tra ⟩[ t ∷ A ]) =
  Trans (V.tail φ) ∇ ∙⟨ tra ⟩[ t ∷ A ]
Trans (φ ⁰) (∇ ∙⟨ o ⟩[ t ∷ A ]) =
  Trans φ ∇ ∙⟨ o ⟩[ t ∷ A ]
Trans (φ ¹) (∇ ∙⟨ opa φ′ ⟩[ t ∷ A ]) =
  Trans (φ ⊔ᵒᵗ φ′) ∇ ∙⟨ tra ⟩[ t ∷ A ]

opaque
  unfolding T.Trans

  -- Transparentisation is correctly implemented.

  ⌜Trans⌝ᶜᵈ :
    (∇ : DCon c n) → ⌜ Trans φ ∇ ⌝ᶜᵈ γ PE.≡ T.Trans φ (⌜ ∇ ⌝ᶜᵈ γ)
  ⌜Trans⌝ᶜᵈ (base nothing) =
    PE.refl
  ⌜Trans⌝ᶜᵈ {φ} {γ} (base (just φ′)) =
    T.Trans (φ′ ⊔ᵒ φ) (γ .⌜base⌝ .U.defs)       ≡˘⟨ Trans-trans ⟩
    T.Trans φ (T.Trans φ′ (γ .⌜base⌝ .U.defs))  ∎
  ⌜Trans⌝ᶜᵈ ε =
    PE.refl
  ⌜Trans⌝ᶜᵈ (∇ ∙⟨ tra ⟩[ _ ∷ _ ]) =
    PE.cong U._∙! (⌜Trans⌝ᶜᵈ ∇)
  ⌜Trans⌝ᶜᵈ {φ = _ ⁰} (∇ ∙⟨ opa _ ⟩[ _ ∷ _ ]) =
    PE.cong U._∙! (⌜Trans⌝ᶜᵈ ∇)
  ⌜Trans⌝ᶜᵈ {φ = _ ¹} (∇ ∙⟨ opa _ ⟩[ _ ∷ _ ]) =
    PE.cong U._∙! (⌜Trans⌝ᶜᵈ ∇)

------------------------------------------------------------------------
-- Well-formed meta-contexts

-- The "type or term" is well-formed.

Type-or-term-wf : Cons c m n → Type-or-term c n → Contexts c → Set a
Type-or-term-wf Γ (type A)   γ = ⌜ Γ ⌝ᶜ γ ⊢ A
Type-or-term-wf Γ (term t A) γ = ⌜ Γ ⌝ᶜ γ ⊢ t ∷ ⌜ A ⌝ γ

-- Meta-con-wf Γ γ means that the meta-context in γ is well-formed
-- with respect to Γ.

record Meta-con-wf (∇ : DCon c n) (γ : Contexts c) : Set a where
  no-eta-equality
  field
    bindings-wf :
      ∀ {n} (x : Meta-var c n) →
      let Δ , T = γ .metas .bindings x in
      Type-or-term-wf (∇ » Δ) T γ

open Meta-con-wf public

opaque

  -- Empty meta-variable contexts are well-formed.

  Meta-con-wf-empty :
    c .ms PE.≡ 0 → Meta-con-wf {c} ∇ γ
  Meta-con-wf-empty PE.refl .bindings-wf (var () _)
