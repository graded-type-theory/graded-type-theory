------------------------------------------------------------------------
-- Unary variants of some relations
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Unary
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Kit R
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Whnf R
open import Definition.LogicalRelation.Weakening.Restricted R

open import Definition.Typed R
open import Definition.Typed.Properties R

open import Definition.Untyped M hiding (K)
open import Definition.Untyped.Neutral M type-variant

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum

private variable
  n              : Nat
  Γ              : Con Term _
  A B t t₁ t₂ t′ : Term _
  l l′           : Universe-level
  l′<l           : _ <ᵘ _
  s              : Strength
  t-prod t-prod′ : Product _
  t-id           : Identity _
  p q            : M

------------------------------------------------------------------------
-- Neutral terms

-- Unary reducibility for neutral terms.

record _⊩neNf_∷_ (Γ : Con Term n) (k A : Term n) : Set a where
  no-eta-equality
  pattern
  constructor neNfₜ
  field
    neutrals-included : Neutrals-included
    neK               : Neutral k
    k≡k               : Γ ⊢~ k ∷ A

opaque

  -- The relation _⊩neNf_∷_ is pointwise logically equivalent to the
  -- diagonal of _⊩neNf_≡_∷_.

  ⊩neNf∷⇔⊩neNf≡∷ : Γ ⊩neNf t ∷ B ⇔ Γ ⊩neNf t ≡ t ∷ B
  ⊩neNf∷⇔⊩neNf≡∷ =
      (λ where
         (neNfₜ a b c) → neNfₜ₌ a b b c)
    , (λ where
         (neNfₜ₌ a b _ c) → neNfₜ a b c)

-- Unary reducibility for terms that reduce to neutral terms.

record _⊩ne_∷_/_ (Γ : Con Term n) (t A : Term n) (⊩A : Γ ⊩ne A) :
         Set a where
  no-eta-equality
  pattern
  constructor neₜ
  open _⊩ne_ ⊩A
  field
    k  : Term n
    d  : Γ ⊢ t ⇒* k ∷ K
    nf : Γ ⊩neNf k ∷ K

opaque

  -- The relation _⊩ne_∷_/_ is pointwise logically equivalent to the
  -- diagonal of _⊩ne_≡_∷_.

  ⊩ne∷⇔⊩ne≡∷ : ∀ {⊩B} → Γ ⊩ne t ∷ B / ⊩B ⇔ Γ ⊩ne t ≡ t ∷ B / ⊩B
  ⊩ne∷⇔⊩ne≡∷ =
      (λ where
         (neₜ _ t⇒u ⊩u) → neₜ₌ _ _ t⇒u t⇒u (⊩neNf∷⇔⊩neNf≡∷ .proj₁ ⊩u))
    , (λ where
         (neₜ₌ _ _ t⇒u t⇒v u≡v@(neNfₜ₌ _ u-ne v-ne _)) →
           neₜ _ t⇒u
             (⊩neNf∷⇔⊩neNf≡∷ .proj₂ $
              PE.subst (flip (_⊩neNf_≡_∷_ _ _) _)
                (whrDet*Term (t⇒v , ne v-ne) (t⇒u , ne u-ne)) u≡v))

------------------------------------------------------------------------
-- U

-- Unary reducibility for universe terms.

record _⊩U_∷U/_ (Γ : Con Term n) (t : Term n) (l′<l : l′ <ᵘ l) :
         Set a where
  no-eta-equality
  pattern
  constructor Uₜ
  open LogRelKit (kit′ l′<l)
  field
    C      : Term n
    ⇒*C    : Γ ⊢ t ⇒* C ∷ U l′
    C-type : Type C
    ≅C     : Γ ⊢≅ C ∷ U l′
    ⊩t     : Γ ⊩ t

opaque

  -- The relation _⊩U_∷U/_ is pointwise logically equivalent to
  -- the diagonal of a certain relation.

  ⊩U∷U⇔⊩U≡∷U : Γ ⊩U t ∷U/ l′<l ⇔ LogRel._⊩₁U_≡_∷U/_ _ kit′ Γ t t l′<l
  ⊩U∷U⇔⊩U≡∷U {l′<l} =
      (λ where
         (Uₜ _ t⇒A A-type ≅A ⊩t) →
           Uₜ₌ _ _ t⇒A t⇒A A-type A-type ≅A ⊩t ⊩t
             (⊩<≡⇔⊩≡ l′<l .proj₂ $ reflEq $ ⊩<⇔⊩ l′<l .proj₁ ⊩t))
    , (λ where
         (Uₜ₌ _ _ t⇒A t⇒B A-type B-type A≅B ⊩t _ _) →
           Uₜ _ t⇒A A-type
             (PE.subst (flip (_⊢_≅_∷_ _ _) _)
                (whrDet*Term (t⇒B , typeWhnf B-type)
                   (t⇒A , typeWhnf A-type))
                A≅B)
             ⊩t)

------------------------------------------------------------------------
-- Empty

-- A property for terms of the empty type in WHNF.

data Empty-prop (Γ : Con Term n) (t : Term n) : Set a where
  ne : Γ ⊩neNf t ∷ Empty → Empty-prop Γ t

opaque

  -- The relation Empty-prop is pointwise logically equivalent to the
  -- diagonal of [Empty]-prop.

  Empty-prop⇔[Empty]-prop : Empty-prop Γ t ⇔ [Empty]-prop Γ t t
  Empty-prop⇔[Empty]-prop =
      (λ { (ne ⊩t) → ne (⊩neNf∷⇔⊩neNf≡∷ .proj₁ ⊩t) })
    , (λ { (ne ⊩t) → ne (⊩neNf∷⇔⊩neNf≡∷ .proj₂ ⊩t) })

opaque

  -- If t satisfies Empty-prop Γ, then t is a neutral term (a specific
  -- kind of WHNF).

  empty : Empty-prop Γ t → Neutral t
  empty (ne (neNfₜ _ t-ne _)) = t-ne

-- Unary reducibility for terms of the empty type.

record _⊩Empty_∷Empty (Γ : Con Term n) (t : Term n) : Set a where
  no-eta-equality
  pattern
  constructor Emptyₜ
  field
    u    : Term n
    ⇒*u  : Γ ⊢ t ⇒* u ∷ Empty
    ≅u   : Γ ⊢≅ u ∷ Empty
    prop : Empty-prop Γ u

opaque

  -- The relation _⊩Empty_∷Empty is pointwise logically equivalent to
  -- the diagonal of _⊩Empty_≡_∷Empty.

  ⊩Empty∷Empty⇔⊩Empty≡∷Empty : Γ ⊩Empty t ∷Empty ⇔ Γ ⊩Empty t ≡ t ∷Empty
  ⊩Empty∷Empty⇔⊩Empty≡∷Empty =
      (λ where
         (Emptyₜ _ ⇒u ≅u u-prop) →
           Emptyₜ₌ _ _ ⇒u ⇒u ≅u
             (Empty-prop⇔[Empty]-prop .proj₁ u-prop))
    , (λ where
         (Emptyₜ₌ u v t⇒u t⇒v u≅v u-v-prop) →
           let u-ne , v-ne = esplit u-v-prop
               v≡u         = whrDet*Term (t⇒v , ne v-ne) (t⇒u , ne u-ne)
           in
           Emptyₜ _ t⇒u (PE.subst (flip (_⊢_≅_∷_ _ _) _) v≡u u≅v)
             (Empty-prop⇔[Empty]-prop .proj₂ $
              PE.subst ([Empty]-prop _ _) v≡u u-v-prop))

------------------------------------------------------------------------
-- Unit

-- A property for terms of unit type in WHNF.

data Unit-prop′ (Γ : Con Term n) (l : Universe-level) (s : Strength) :
       Term n → Set a where
  starᵣ : Unit-prop′ Γ l s (star s l)
  ne    : Γ ⊩neNf t ∷ Unit s l → Unit-prop′ Γ l s t

opaque

  -- The relation Unit-prop′ Γ l 𝕨 is pointwise logically equivalent
  -- to the diagonal of [Unitʷ]-prop Γ l.

  Unit-prop′-𝕨⇔[Unitʷ]-prop : Unit-prop′ Γ l 𝕨 t ⇔ [Unitʷ]-prop Γ l t t
  Unit-prop′-𝕨⇔[Unitʷ]-prop =
      (λ where
         starᵣ   → starᵣ
         (ne ⊩t) → ne (⊩neNf∷⇔⊩neNf≡∷ .proj₁ ⊩t))
    , flip lemma PE.refl
    where
    lemma : [Unitʷ]-prop Γ l t t′ → t PE.≡ t′ → Unit-prop′ Γ l 𝕨 t
    lemma starᵣ _         = starᵣ
    lemma (ne ⊩t) PE.refl = ne (⊩neNf∷⇔⊩neNf≡∷ .proj₂ ⊩t)

-- A property for terms of unit type in WHNF.

data Unit-prop (Γ : Con Term n) (l : Universe-level) :
       Strength → Term n → Set a where
  Unitₜʷ : Unit-prop′ Γ l 𝕨 t → ¬ Unitʷ-η → Unit-prop Γ l 𝕨 t
  Unitₜˢ : Unit-with-η s → Unit-prop Γ l s t

opaque

  -- The relation Unit-prop is pointwise logically equivalent to the
  -- diagonal of [Unit]-prop.

  Unit-prop⇔[Unit]-prop : Unit-prop Γ l s t ⇔ [Unit]-prop Γ l s t t
  Unit-prop⇔[Unit]-prop =
      (λ where
         (Unitₜʷ prop no-η) →
           Unitₜ₌ʷ (Unit-prop′-𝕨⇔[Unitʷ]-prop .proj₁ prop) no-η
         (Unitₜˢ η) → Unitₜ₌ˢ η)
    , (λ where
         (Unitₜ₌ʷ prop no-η) →
           Unitₜʷ (Unit-prop′-𝕨⇔[Unitʷ]-prop .proj₂ prop) no-η
         (Unitₜ₌ˢ η) → Unitₜˢ η)

opaque

  -- A "smart constructor" for Unit-prop.

  Unit-prop′→Unit-prop :
    Unit-prop′ Γ l s t →
    Unit-prop Γ l s t
  Unit-prop′→Unit-prop {s} prop =
    case Unit-with-η? s of λ where
      (inj₁ η)                → Unitₜˢ η
      (inj₂ (PE.refl , no-η)) → Unitₜʷ prop no-η

-- Unary reducibility for terms of unit type.

record _⊩Unit⟨_,_⟩_∷Unit
         (Γ : Con Term n) (l : Universe-level) (s : Strength)
         (t : Term n) :
         Set a where
  no-eta-equality
  pattern
  constructor Unitₜ
  field
    u    : Term n
    ↘u   : Γ ⊢ t ↘ u ∷ Unit s l
    prop : Unit-prop Γ l s u

opaque

  -- The relation _⊩Unit⟨_,_⟩_∷Unit is pointwise logically equivalent
  -- to the diagonal of _⊩Unit⟨_,_⟩_≡_∷Unit.

  ⊩Unit∷Unit⇔⊩Unit≡∷Unit :
    Γ ⊩Unit⟨ l , s ⟩ t ∷Unit ⇔ Γ ⊩Unit⟨ l , s ⟩ t ≡ t ∷Unit
  ⊩Unit∷Unit⇔⊩Unit≡∷Unit =
      (λ (Unitₜ _ ↘u prop) →
         Unitₜ₌ _ _ ↘u ↘u (Unit-prop⇔[Unit]-prop .proj₁ prop))
    , (λ (Unitₜ₌ _ _ ↘u ↘v prop) →
         Unitₜ _ ↘u
           (Unit-prop⇔[Unit]-prop .proj₂ $
            PE.subst ([Unit]-prop _ _ _ _) (whrDet*Term ↘v ↘u) prop))

------------------------------------------------------------------------
-- Π

-- Unary term reducibility for Π-types.

record _⊩⟨_⟩Π_∷_/_ (Γ : Con Term n) (l : Universe-level) (t A : Term n)
         (⊩A : Γ ⊩′⟨ l ⟩B⟨ BΠ p q ⟩ A) :
         Set a where
  no-eta-equality
  pattern
  constructor Πₜ
  open _⊩ₗB⟨_⟩_ ⊩A
  field
    u     : Term n
    ⇒*u   : Γ ⊢ t ⇒* u ∷ Π p , q ▷ F ▹ G
    u-fun : Function u
    ≅u    : Γ ⊢≅ u ∷ Π p , q ▷ F ▹ G
    ⊩u    : ∀ {m} {ρ : Wk m n} {Δ : Con Term m} {v w}
            (Δ⊇Γ : ρ ∷ʷʳ Δ ⊇ Γ)
            (⊩v : Δ ⊩⟨ l ⟩ v ∷ wk ρ F / [F] Δ⊇Γ) →
            Δ ⊩⟨ l ⟩ w ∷ wk ρ F / [F] Δ⊇Γ →
            Δ ⊩⟨ l ⟩ v ≡ w ∷ wk ρ F / [F] Δ⊇Γ →
            Δ ⊩⟨ l ⟩ wk ρ u ∘⟨ p ⟩ v ≡ wk ρ u ∘⟨ p ⟩ w ∷
              wk (lift ρ) G [ v ]₀ / [G] Δ⊇Γ ⊩v

opaque

  -- The relation _⊩⟨_⟩Π_∷_/_ is pointwise logically equivalent to the
  -- diagonal of a certain relation.

  ⊩Π∷⇔⊩Π≡∷ :
    (⊩A : Γ ⊩′⟨ l ⟩B⟨ BΠ p q ⟩ A) →
    Γ ⊩⟨ l ⟩Π t ∷ A / ⊩A ⇔
    LogRel._⊩ₗΠ_≡_∷_/_ l kit′ Γ t t A ⊩A
  ⊩Π∷⇔⊩Π≡∷ record{} =
      (λ (Πₜ _ t⇒u u-fun ≅u ⊩u) →
         _ , _ , t⇒u , t⇒u , u-fun , u-fun , ≅u , ⊩u)
    , (λ (_ , _ , t⇒u , t⇒v , u-fun , v-fun , u≅v , u≡v) →
         case whrDet*Term (t⇒u , functionWhnf u-fun)
                (t⇒v , functionWhnf v-fun) of λ {
           PE.refl →
         Πₜ _ t⇒u u-fun u≅v (λ {_ _ _ _} → u≡v) })

------------------------------------------------------------------------
-- Σ

-- A property for terms of Σ-type in WHNF.

data Σ-prop (Γ : Con Term n) :
  (t : Term n) (s : Strength) → Product t →
  Γ ⊩′⟨ l ⟩B⟨ BΣ s p q ⟩ A → Set a where
  𝕤 :
    {⊩A : Γ ⊩′⟨ l ⟩B⟨ BΣ 𝕤 p q ⟩ A} →
    let open _⊩ₗB⟨_⟩_ ⊩A
        id-Γ = id (wfEq (≅-eq A≡A))
    in
    (t-prod : Product t) →
    (⊩fst : Γ ⊩⟨ l ⟩ fst p t ∷ wk id F / [F] id-Γ) →
    Γ ⊩⟨ l ⟩ snd p t ∷ wk (lift id) G [ fst p t ]₀ / [G] id-Γ ⊩fst →
    Σ-prop Γ t 𝕤 t-prod ⊩A
  𝕨-prodₙ :
    {⊩A : Γ ⊩′⟨ l ⟩B⟨ BΣ 𝕨 p q ⟩ A} →
    let open _⊩ₗB⟨_⟩_ ⊩A
        id-Γ = id (wfEq (≅-eq A≡A))
    in
    (⊩t₁ : Γ ⊩⟨ l ⟩ t₁ ∷ wk id F / [F] id-Γ) →
    Γ ⊩⟨ l ⟩ t₂ ∷ wk (lift id) G [ t₁ ]₀ / [G] id-Γ ⊩t₁ →
    Σ-prop Γ (prodʷ p t₁ t₂) 𝕨 prodₙ ⊩A
  𝕨-ne :
    {⊩A : Γ ⊩′⟨ l ⟩B⟨ BΣ 𝕨 p q ⟩ A} →
    let open _⊩ₗB⟨_⟩_ ⊩A in
    Neutrals-included →
    (t-ne : Neutral t) →
    Γ ⊢~ t ∷ Σʷ p , q ▷ F ▹ G →
    Σ-prop Γ t 𝕨 (ne t-ne) ⊩A

opaque

  private

    -- Some lemmas used below.

    [Σ]-prop→Σ-prop :
      ∀ s t-prod t-prod′ (⊩A : Γ ⊩′⟨ l ⟩B⟨ BΣ s p q ⟩ A) →
      LogRel.[Σ]-prop l kit′ s t t Γ ⊩A t-prod t-prod′ →
      Σ-prop Γ t s t-prod ⊩A
    [Σ]-prop→Σ-prop 𝕤 t-prod _ record{} (⊩fst , _ , _ , ⊩snd) =
      𝕤 t-prod ⊩fst ⊩snd
    [Σ]-prop→Σ-prop
      𝕨 prodₙ prodₙ record{}
      (PE.refl , PE.refl , PE.refl , _ , ⊩t₁ , _ , _ , ⊩t₂) =
      𝕨-prodₙ ⊩t₁ ⊩t₂
    [Σ]-prop→Σ-prop 𝕨 (ne t-ne) (ne _) record{} (inc , ~t) =
      𝕨-ne inc t-ne ~t
    [Σ]-prop→Σ-prop 𝕨 prodₙ  (ne _) record{} ()
    [Σ]-prop→Σ-prop 𝕨 (ne _) prodₙ  record{} ()

    Σ-prop→[Σ]-prop :
      (⊩A : Γ ⊩′⟨ l ⟩B⟨ BΣ s p q ⟩ A) →
      ∀ t-prod′ →
      Σ-prop Γ t s t-prod ⊩A →
      LogRel.[Σ]-prop l kit′ s t t Γ ⊩A t-prod t-prod′
    Σ-prop→[Σ]-prop record{} _ (𝕤 _ ⊩fst ⊩snd) =
      ⊩fst , ⊩fst , ⊩fst , ⊩snd
    Σ-prop→[Σ]-prop record{} prodₙ (𝕨-prodₙ ⊩t₁ ⊩t₂) =
      PE.refl , PE.refl , PE.refl , PE.refl ,
      ⊩t₁ , ⊩t₁ , ⊩t₁ , ⊩t₂
    Σ-prop→[Σ]-prop record{} (ne _) (𝕨-ne inc _ ~t) =
      inc , ~t
    Σ-prop→[Σ]-prop record{} (ne ()) (𝕨-prodₙ _ _)
    Σ-prop→[Σ]-prop record{} prodₙ (𝕨-ne _ () _)

  -- A variant of Σ-prop⇔[Σ]-prop (which is defined below).

  Σ-prop⇔[Σ]-prop′ :
    {⊩A : Γ ⊩′⟨ l ⟩B⟨ BΣ s p q ⟩ A} →
    Σ-prop Γ t s t-prod ⊩A ⇔
    LogRel.[Σ]-prop l kit′ s t t Γ ⊩A t-prod t-prod′
  Σ-prop⇔[Σ]-prop′ = Σ-prop→[Σ]-prop _ _ , [Σ]-prop→Σ-prop _ _ _ _

  -- The relation Σ-prop is pointwise logically equivalent to a
  -- certain relation.

  Σ-prop⇔[Σ]-prop :
    {⊩A : Γ ⊩′⟨ l ⟩B⟨ BΣ s p q ⟩ A} →
    Σ-prop Γ t s t-prod ⊩A ⇔
    LogRel.[Σ]-prop l kit′ s t t Γ ⊩A t-prod t-prod
  Σ-prop⇔[Σ]-prop = Σ-prop⇔[Σ]-prop′

-- Unary term reducibility for Σ-types.

record _⊩⟨_⟩Σ_∷_/_ (Γ : Con Term n) (l : Universe-level) (t A : Term n)
         (⊩A : Γ ⊩′⟨ l ⟩B⟨ BΣ s p q ⟩ A) :
         Set a where
  no-eta-equality
  pattern
  constructor Σₜ
  open _⊩ₗB⟨_⟩_ ⊩A
  field
    u      : Term n
    ⇒*u    : Γ ⊢ t ⇒* u ∷ Σ⟨ s ⟩ p , q ▷ F ▹ G
    u-prod : Product u
    ≅u     : Γ ⊢≅ u ∷ Σ⟨ s ⟩ p , q ▷ F ▹ G
    prop   : Σ-prop Γ u s u-prod ⊩A

opaque

  -- The relation _⊩⟨_⟩Σ_∷_/_ is pointwise logically equivalent to the
  -- diagonal of a certain relation.

  ⊩Σ∷⇔⊩Σ≡∷ :
    (⊩A : Γ ⊩′⟨ l ⟩B⟨ BΣ s p q ⟩ A) →
    Γ ⊩⟨ l ⟩Σ t ∷ A / ⊩A ⇔
    LogRel._⊩ₗΣ_≡_∷_/_ l kit′ Γ t t A ⊩A
  ⊩Σ∷⇔⊩Σ≡∷ record{} =
      (λ (Σₜ _ t⇒u u-prod ≅u prop) →
         _ , _ , t⇒u , t⇒u , ≅u , u-prod , u-prod ,
         Σ-prop⇔[Σ]-prop .proj₁ prop)
    , (λ (_ , _ , t⇒u , t⇒v , u≅v , u-prod , v-prod , prop) →
         case whrDet*Term (t⇒u , productWhnf u-prod)
                (t⇒v , productWhnf v-prod) of λ {
           PE.refl →
         Σₜ _ t⇒u u-prod u≅v (Σ-prop⇔[Σ]-prop′ .proj₂ prop) })

------------------------------------------------------------------------
-- ℕ

mutual

  -- Unary reducibility for natural number terms.

  record _⊩ℕ_∷ℕ (Γ : Con Term n) (t : Term n) : Set a where
    inductive
    no-eta-equality
    pattern
    constructor ℕₜ
    field
      u    : Term n
      ⇒*u  : Γ ⊢ t ⇒* u ∷ ℕ
      ≅u   : Γ ⊢≅ u ∷ ℕ
      prop : Natural-prop Γ u

  -- A property for natural number terms in WHNF.

  data Natural-prop (Γ : Con Term n) : Term n → Set a where
    sucᵣ  : Γ ⊩ℕ t ∷ℕ → Natural-prop Γ (suc t)
    zeroᵣ : Natural-prop Γ zero
    ne    : Γ ⊩neNf t ∷ ℕ → Natural-prop Γ t

private

  -- Some lemmas used below.

  opaque mutual

    ⊩ℕ∷ℕ→⊩ℕ≡∷ℕ : Γ ⊩ℕ t ∷ℕ → Γ ⊩ℕ t ≡ t ∷ℕ
    ⊩ℕ∷ℕ→⊩ℕ≡∷ℕ (ℕₜ _ t⇒u ≅u u-prop) =
      ℕₜ₌ _ _ t⇒u t⇒u ≅u (Natural-prop→[Natural]-prop u-prop)

    Natural-prop→[Natural]-prop :
      Natural-prop Γ t → [Natural]-prop Γ t t
    Natural-prop→[Natural]-prop = λ where
      (sucᵣ ⊩t) → sucᵣ (⊩ℕ∷ℕ→⊩ℕ≡∷ℕ ⊩t)
      zeroᵣ     → zeroᵣ
      (ne ⊩t)   → ne (⊩neNf∷⇔⊩neNf≡∷ .proj₁ ⊩t)

  opaque mutual

    ⊩ℕ≡∷ℕ→⊩ℕ∷ℕ : Γ ⊩ℕ t ≡ t ∷ℕ → Γ ⊩ℕ t ∷ℕ
    ⊩ℕ≡∷ℕ→⊩ℕ∷ℕ (ℕₜ₌ _ _ t⇒u t⇒v u≅v u-v-prop) =
      let u-nat , v-nat = split u-v-prop
          v≡u           = whrDet*Term (t⇒v , naturalWhnf v-nat)
                            (t⇒u , naturalWhnf u-nat)
      in
      ℕₜ _ t⇒u (PE.subst (flip (_⊢_≅_∷_ _ _) _) v≡u u≅v)
        ([Natural]-prop→Natural-prop v≡u u-v-prop)

    [Natural]-prop→Natural-prop :
      t′ PE.≡ t → [Natural]-prop Γ t t′ → Natural-prop Γ t
    [Natural]-prop→Natural-prop PE.refl = λ where
      (sucᵣ ⊩t) → sucᵣ (⊩ℕ≡∷ℕ→⊩ℕ∷ℕ ⊩t)
      zeroᵣ     → zeroᵣ
      (ne ⊩t)   → ne (⊩neNf∷⇔⊩neNf≡∷ .proj₂ ⊩t)

opaque

  -- The relation _⊩ℕ_∷ℕ is pointwise logically equivalent to the
  -- diagonal of _⊩ℕ_≡_∷ℕ.

  ⊩ℕ∷ℕ⇔⊩ℕ≡∷ℕ : Γ ⊩ℕ t ∷ℕ ⇔ Γ ⊩ℕ t ≡ t ∷ℕ
  ⊩ℕ∷ℕ⇔⊩ℕ≡∷ℕ = ⊩ℕ∷ℕ→⊩ℕ≡∷ℕ , ⊩ℕ≡∷ℕ→⊩ℕ∷ℕ

opaque

  -- The relation Natural-prop is pointwise logically equivalent to
  -- the diagonal of [Natural]-prop.

  Natural-prop⇔[Natural]-prop : Natural-prop Γ t ⇔ [Natural]-prop Γ t t
  Natural-prop⇔[Natural]-prop =
    Natural-prop→[Natural]-prop , [Natural]-prop→Natural-prop PE.refl

opaque

  -- If t satisfies Natural-prop Γ, then t is a "Natural" (a specific
  -- kind of WHNF).

  natural : Natural-prop Γ t → Natural t
  natural (sucᵣ _)              = sucₙ
  natural zeroᵣ                 = zeroₙ
  natural (ne (neNfₜ _ t-ne _)) = ne t-ne

------------------------------------------------------------------------
-- Id

opaque

  -- A variant of ⊩Id∷-view⇔ (which is defined below).

  ⊩Id∷-view⇔′ :
    {⊩A : Γ ⊩′⟨ l ⟩Id A}
    {t-id t-id′ : Identity t} →
    let open _⊩ₗId_ ⊩A in
    ⊩Id∷-view ⊩A t t-id ⇔
    Identity-rec t-id
      (Identity-rec t-id′
         (Γ ⊩⟨ l ⟩ lhs ≡ rhs ∷ Ty / ⊩Ty)
         (Lift _ ⊥))
      (Identity-rec t-id′
         (Lift _ ⊥)
         (Neutrals-included ×
          Γ ⊢~ t ∷ Id Ty lhs rhs))
  ⊩Id∷-view⇔′ {Γ} {l} {A} {t} {⊩A} = lemma₁ _ , lemma₂ _ _
    where
    open _⊩ₗId_ ⊩A

    lemma₁ :
      (t-id′ : Identity t) →
      ⊩Id∷-view ⊩A t t-id →
      Identity-rec t-id
        (Identity-rec t-id′
           (Γ ⊩⟨ l ⟩ lhs ≡ rhs ∷ Ty / ⊩Ty)
           (Lift _ ⊥))
        (Identity-rec t-id′
           (Lift _ ⊥)
           (Neutrals-included ×
            Γ ⊢~ t ∷ Id Ty lhs rhs))
    lemma₁ rflₙ    (rflᵣ lhs≡rhs) = lhs≡rhs
    lemma₁ (ne _)  (ne inc _ ~t)  = inc , ~t
    lemma₁ rflₙ    (ne _ () _)
    lemma₁ (ne ()) (rflᵣ _)

    lemma₂ :
      (t-id t-id′ : Identity t) →
      Identity-rec t-id
        (Identity-rec t-id′
           (Γ ⊩⟨ l ⟩ lhs ≡ rhs ∷ Ty / ⊩Ty)
           (Lift _ ⊥))
        (Identity-rec t-id′
           (Lift _ ⊥)
           (Neutrals-included ×
            Γ ⊢~ t ∷ Id Ty lhs rhs)) →
      ⊩Id∷-view ⊩A t t-id
    lemma₂ rflₙ      rflₙ    lhs≡rhs    = rflᵣ lhs≡rhs
    lemma₂ (ne t-ne) (ne _)  (inc , ~t) = ne inc t-ne ~t
    lemma₂ rflₙ      (ne ())
    lemma₂ (ne ())   rflₙ

  -- The relation ⊩Id∷-view is pointwise logically equivalent to a
  -- certain relation.

  ⊩Id∷-view⇔ :
    {⊩A : Γ ⊩′⟨ l ⟩Id A} →
    let open _⊩ₗId_ ⊩A in
    ⊩Id∷-view ⊩A t t-id ⇔
    Identity-rec t-id
      (Identity-rec t-id
         (Γ ⊩⟨ l ⟩ lhs ≡ rhs ∷ Ty / ⊩Ty)
         (Lift _ ⊥))
      (Identity-rec t-id
         (Lift _ ⊥)
         (Neutrals-included ×
          Γ ⊢~ t ∷ Id Ty lhs rhs))
  ⊩Id∷-view⇔ = ⊩Id∷-view⇔′

-- Unary term reducibility for identity types.

record _⊩⟨_⟩Id_∷_/_ (Γ : Con Term n) (l : Universe-level) (t A : Term n)
         (⊩A : Γ ⊩′⟨ l ⟩Id A) :
         Set a where
  no-eta-equality
  pattern
  constructor Idₜ
  open _⊩ₗId_ ⊩A
  field
    u    : Term n
    ⇒*u  : Γ ⊢ t ⇒* u ∷ Id Ty lhs rhs
    u-id : Identity u
    prop : ⊩Id∷-view ⊩A u u-id

opaque

  -- The relation _⊩⟨_⟩Id_∷_/_ is pointwise logically equivalent to
  -- the diagonal of a certain relation.

  ⊩Id∷⇔⊩Id≡∷ :
    (⊩A : Γ ⊩′⟨ l ⟩Id A) →
    Γ ⊩⟨ l ⟩Id t ∷ A / ⊩A ⇔
    LogRel._⊩ₗId_≡_∷_/_ l kit′ Γ t t A ⊩A
  ⊩Id∷⇔⊩Id≡∷ _ =
      (λ ⊩t →
         let open _⊩⟨_⟩Id_∷_/_ ⊩t in
         _ , _ , ⇒*u , ⇒*u , u-id , u-id , ⊩Id∷-view⇔ .proj₁ prop)
    , (λ (u , v , t⇒u , t⇒v , u-id , v-id , rest) →
         record
           { ⇒*u  = t⇒u
           ; u-id = u-id
           ; prop =
               case whrDet*Term (t⇒u , identityWhnf u-id)
                      (t⇒v , identityWhnf v-id) of λ {
                 PE.refl →
               ⊩Id∷-view⇔′ .proj₂ rest }
           })
