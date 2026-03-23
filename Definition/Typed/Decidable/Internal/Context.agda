------------------------------------------------------------------------
-- Some definitions related to contexts used by
-- Definition.Typed.Decidable.Internal
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality
open import Graded.Mode

module Definition.Typed.Decidable.Internal.Context
  {a b} {M : Set a} {Mode : Set b}
  {𝕄 : Modality M}
  (𝐌 : IsMode Mode 𝕄)
  (TR : Type-restrictions 𝕄)
  where

open Type-restrictions TR using (No-equality-reflection)

open import Definition.Typed TR as T hiding (Trans)
open import Definition.Typed.Decidable.Internal.Constraint 𝐌 TR
open import Definition.Typed.Decidable.Internal.Monad 𝐌 TR
open import Definition.Typed.Decidable.Internal.Term 𝐌 TR
open import Definition.Typed.Decidable.Internal.Weakening 𝐌 TR
open import Definition.Typed.Properties.Definition TR
open import Definition.Typed.Reasoning.Type TR
open import Definition.Typed.Stability TR
open import Definition.Typed.Weakening.Definition TR
open import Definition.Typed.Well-formed TR

open import Definition.Untyped M as U
  using (Opacity; Term-kind; Unfolding; Wk;
         _⁰; _¹; _⊔ᵒ_; _»_; _↦∷_∈_; _↦_∷_∈_)
open import Definition.Untyped.Properties M

open U.Con
open U.DCon
open Opacity
open Wk
open _↦∷_∈_
open _↦_∷_∈_

open import Tools.Bool
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.List as L using (List; All)
open import Tools.Maybe using (nothing; just)
open import Tools.Nat as N using (Nat)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎
open import Tools.Unit
import Tools.Vec as V

private variable
  B         : Set _
  C x y z   : B
  P         : B → Set _
  α m n     : Nat
  c         : Constants
  ∇         : DCon _ _
  γ         : Contexts _
  st        : Stack-trace _
  φ         : Unfolding _
  A A₁ A₂ t : Term _ _
  k         : Term-kind

------------------------------------------------------------------------
-- Translation of contexts

-- Turns definition contexts into regular definition contexts.

⌜_⌝ᶜᵈ : DCon c n → Contexts c → U.DCon (U.Term 0) n
⌜ base nothing      ⌝ᶜᵈ γ = γ .⌜base⌝ .U.defs
⌜ base (just φ)     ⌝ᶜᵈ γ = T.Trans φ (γ .⌜base⌝ .U.defs)
⌜ ε                 ⌝ᶜᵈ _ = ε
⌜ ∇ ∙⟨ n ⟩[ t ∷ A ] ⌝ᶜᵈ γ = ⌜ ∇ ⌝ᶜᵈ γ ∙⟨ n ⟩[ ⌜ t ⌝ γ ∷ ⌜ A ⌝ γ ]

-- Turns variable contexts into regular variable contexts.

⌜_⌝ᶜᵛ : Con c n → Contexts c → U.Con U.Term n
⌜ base  ⌝ᶜᵛ γ = γ .⌜base⌝ .U.vars
⌜ ε     ⌝ᶜᵛ _ = ε
⌜ Γ ∙ A ⌝ᶜᵛ γ = ⌜ Γ ⌝ᶜᵛ γ ∙ ⌜ A ⌝ γ

-- Turns context pairs into regular context pairs.

⌜_⌝ᶜ : Cons c m n → Contexts c → U.Cons m n
⌜ Γ ⌝ᶜ γ = ⌜ Γ .defs ⌝ᶜᵈ γ » ⌜ Γ .vars ⌝ᶜᵛ γ

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
    OK (type-of ∇ α) A γ st →
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
    OK (definition-of ∇ α) (t , A) γ st →
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
       ⌜ A ⌝ γ  ≡⟨ refl (defn-wk (stepᵗ₁ ⊢t) (wf-⊢ ⊢t)) ⟩⊢∎≡
       ⌜ A ⌝ γ  ≡⟨ unique-↦∈ here α↦ PE.refl ⟩
       B        ∎)
  definition-of-sound (∇ ∙⟨ _ ⟩[ _ ∷ _ ]) eq »∙ | no _ =
    let α↦ , hyp = definition-of-sound ∇ eq (»∙→» »∙) in
    there α↦ ,
    (λ where
       here       → ⊥-elim (N.n≮n _ (↦∷∈→< (↦∷∈⇒↦∈ α↦)))
       (there α↦) → defn-wk (»∙→»∙⊇ »∙) (hyp α↦))

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
    OK (index Δ x) A γ st →
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

Type-or-term-wf : Cons c m n → Type-or-term c k n → Contexts c → Set a
Type-or-term-wf Γ (type A)   γ = ⌜ Γ ⌝ᶜ γ ⊢ A
Type-or-term-wf Γ (term t A) γ = ⌜ Γ ⌝ᶜ γ ⊢ t ∷ ⌜ A ⌝ γ
Type-or-term-wf Γ (level l)  γ = ⌜ Γ ⌝ᶜ γ ⊢ l ∷Level

-- The equality is well-formed.

data Equality-wf (Γ : Cons c m n) (γ : Contexts c) :
       (_ _ : Type-or-term c k n) → Set a where
  type  : ∀ {A₁ A₂} →
          ⌜ Γ ⌝ᶜ γ ⊢ A₁ ≡ A₂ →
          Equality-wf Γ γ (type A₁) (type A₂)
  term  : ∀ {t₁ t₂} →
          ⌜ Γ ⌝ᶜ γ ⊢ ⌜ A₁ ⌝ γ ≡ ⌜ A₂ ⌝ γ →
          ⌜ Γ ⌝ᶜ γ ⊢ t₁ ≡ t₂ ∷ ⌜ A₁ ⌝ γ →
          Equality-wf Γ γ (term t₁ A₁) (term t₂ A₂)
  level : ∀ {l₁ l₂} →
          ⌜ Γ ⌝ᶜ γ ⊢ l₁ ≡ l₂ ∷Level →
          Equality-wf Γ γ (level l₁) (level l₂)

-- Meta-con-wf Γ γ means that the meta-context in γ is well-formed
-- with respect to Γ.

record Meta-con-wf (∇ : DCon c n) (γ : Contexts c) : Set a where
  no-eta-equality
  field
    bindings-wf :
      ∀ {n} (x : Meta-var c k n) →
      let Δ , T = γ .metas .bindings x in
      Type-or-term-wf (∇ » Δ) T γ
    equalities-wf :
      All (λ (_ , x₁ , x₂) →
             let Δ₁ , T₁ = γ .metas .bindings x₁
                 Δ₂ , T₂ = γ .metas .bindings x₂
             in
             ⌜ ∇ ⌝ᶜᵈ γ »⊢ ⌜ Δ₁ ⌝ᶜᵛ γ ≡ ⌜ Δ₂ ⌝ᶜᵛ γ ×
             Equality-wf (∇ » Δ₁) γ T₁ T₂)
          (γ .metas .equalities)

open Meta-con-wf public

opaque

  -- Empty meta-variable contexts are well-formed.

  Meta-con-wf-empty :
    c .ms PE.≡ 0 → Meta-con-wf {c} ∇ γ
  Meta-con-wf-empty     ms≡0 .bindings-wf   = ⊥-elim ∘→ ¬-Meta-var ms≡0
  Meta-con-wf-empty {c} ms≡0 .equalities-wf =
    vacuously-true _
    where
    vacuously-true :
      (xs : List
              (∃ λ ((k , n) : Term-kind × Nat) →
                 Meta-var c k n × Meta-var c k n)) →
      All P xs
    vacuously-true L.[]                = L.[]
    vacuously-true ((_ , x , _) L.∷ _) = ⊥-elim (¬-Meta-var ms≡0 x)

------------------------------------------------------------------------
-- Well-formed contexts

-- The constraints are satisfied.

Constraints-satisfied : Contexts c → Set a
Constraints-satisfied γ = All (λ C → ⟦ C ⟧ᶜ γ) (constraints γ)

-- The contexts are well-formed.

record Contexts-wf (∇ : DCon c n) (γ : Contexts c) : Set a where
  field
    -- The meta-variable context is well-formed.
    metas-wf : Meta-con-wf ∇ γ

    -- The constraints are satisfied.
    constraints-wf : Constraints-satisfied γ

open Contexts-wf public

private opaque

  -- Some lemmas used below.

  constraints⁰-satisfied :
    Constraints-satisfied γ →
    All (λ C → T (satisfied?⁰ C γ) → ⟦ C ⟧ᶜ⁰) all-nullary-constraints
  constraints⁰-satisfied {γ} =
    L.All-filterᵇ .proj₁ ∘→ All.map⁻ ∘→
    All.++⁻ˡ (constraints⁰-as-list γ)

  constraints⁺-satisfied :
    Constraints-satisfied γ →
    All (λ C → ⟦ constr⁺ C ⟧ᶜ γ) (γ .constraints⁺)
  constraints⁺-satisfied {γ} =
    All.map⁻ ∘→ All.++⁻ʳ (constraints⁰-as-list γ)

opaque

  -- Soundness for satisfied?⁰.

  satisfied?⁰-sound :
    Constraints-satisfied γ →
    ∀ C → T (satisfied?⁰ C γ) → ⟦ constr⁰ C ⟧ᶜ γ
  satisfied?⁰-sound sat k-allowed =
    L.lookup (constraints⁰-satisfied sat) (L.here PE.refl)
  satisfied?⁰-sound sat level-allowed =
    L.lookup (constraints⁰-satisfied sat) (L.there (L.here PE.refl))
  satisfied?⁰-sound sat level-is-small =
    L.lookup (constraints⁰-satisfied sat)
      (L.there (L.there (L.here PE.refl)))
  satisfied?⁰-sound sat omega-plus-allowed =
    L.lookup (constraints⁰-satisfied sat)
      (L.there (L.there (L.there (L.here PE.refl))))
  satisfied?⁰-sound sat no-equality-reflection =
    L.lookup (constraints⁰-satisfied sat)
      (L.there (L.there (L.there (L.there (L.here PE.refl)))))
  satisfied?⁰-sound sat opacity-allowed =
    L.lookup (constraints⁰-satisfied sat)
      (L.there (L.there (L.there (L.there (L.there (L.here PE.refl))))))
  satisfied?⁰-sound sat unfolding-mode-transitive =
    L.lookup (constraints⁰-satisfied sat)
      (L.there $
       L.there (L.there (L.there (L.there (L.there (L.here PE.refl))))))

opaque

  -- Soundness for satisfied?⁺.

  satisfied?⁺-sound :
    Constraints-satisfied γ → T (satisfied?⁺ C γ) → ⟦ C ⟧ᶜ⁺ γ
  satisfied?⁺-sound {γ} {C} wf sat
    with L.member? _≟ᶜ_ C (γ .constraints⁺)
  satisfied?⁺-sound _  () | nothing
  satisfied?⁺-sound wf _  | just C∈ =
    L.lookup (constraints⁺-satisfied wf) C∈

opaque

  -- Soundness for satisfied?.

  satisfied?-sound :
    Constraints-satisfied γ → ∀ C → T (satisfied? C γ) → ⟦ C ⟧ᶜ γ
  satisfied?-sound wf (constr⁰ C) = satisfied?⁰-sound wf C
  satisfied?-sound wf (constr⁺ _) = satisfied?⁺-sound wf

opaque

  -- An inversion lemma for require.

  inv-require′ :
    Constraints-satisfied γ →
    ∀ C → OK (require C) tt γ st → ⟦ C ⟧ᶜ γ
  inv-require′ wf C = satisfied?-sound wf C ∘→ inv-require-T C

opaque

  -- A variant of inv-require′.

  inv-require′⁰ :
    Constraints-satisfied γ →
    ∀ C → OK (require⁰ C) tt γ st → ⟦ C ⟧ᶜ⁰
  inv-require′⁰ wf = inv-require′ wf ∘→ constr⁰

opaque

  -- An inversion lemma for require.

  inv-require :
    Contexts-wf ∇ γ → ∀ C → OK (require C) tt γ st → ⟦ C ⟧ᶜ γ
  inv-require ⊢γ = inv-require′ (⊢γ .constraints-wf)

opaque

  -- A variant of inv-require.

  inv-require⁰ :
    Contexts-wf ∇ γ →
    ∀ C → OK (require (constr⁰ C)) tt γ st → ⟦ constr⁰ C ⟧ᶜ γ
  inv-require⁰ ⊢γ = inv-require ⊢γ ∘→ constr⁰

opaque

  -- A variant of inv-require.

  inv-require⁺ :
    Contexts-wf ∇ γ →
    OK (require (constr⁺ C)) tt γ st → ⟦ constr⁺ C ⟧ᶜ γ
  inv-require⁺ ⊢γ = inv-require ⊢γ (constr⁺ _)

opaque

  -- An inversion lemma for if-no-equality-reflection.

  inv-if-no-equality-reflection :
    Contexts-wf ∇ γ →
    OK (if-no-equality-reflection x y) z γ st →
    No-equality-reflection × OK x z γ st ⊎ OK y z γ st
  inv-if-no-equality-reflection ⊢γ =
    ⊎.map
      (Σ.map
         (satisfied?⁰-sound (⊢γ .constraints-wf) no-equality-reflection)
         idᶠ)
      idᶠ ∘→
    inv-if-no-equality-reflection-∈
