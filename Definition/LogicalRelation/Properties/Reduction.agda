------------------------------------------------------------------------
-- The logical relation is backwards-closed under reductions
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Reduction
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (Wk; K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
-- The imported operator _,_ is not "supposed" to be used below, but
-- another operator with the same name is used, and if this import
-- statement is removed, then some code below fails to type-check (at
-- the time of writing).
open import Definition.Typed.Substitution R using (_,_)
import Definition.Typed.Weakening R as Wk
open import Definition.Typed.Well-formed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties.Kit R
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Universe R
open import Definition.LogicalRelation.Properties.Transitivity R
open import Definition.LogicalRelation.Properties.Whnf R
open import Definition.LogicalRelation.Unary R

open import Tools.Function
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum using (inj₁; inj₂)

private
  variable
    n       : Nat
    Γ       : Con Term n
    A B t u : Term n
    l       : Universe-level

-- Weak head expansion of reducible types.
redSubst* : ∀ {A B : Term n} {l}
          → Γ ⊢ A ⇒* B
          → Γ ⊩⟨ l ⟩ B
          → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst* D (Uᵣ′ l′ l< D′) =
  Uᵣ′ l′ l< (D ⇨* D′) , D′
redSubst* D (ℕᵣ D′) =
  ℕᵣ (D ⇨* D′) , D′
redSubst* D (Emptyᵣ D′) =
  Emptyᵣ (D ⇨* D′) , D′
redSubst* D (Unitᵣ (Unitₜ D′ ok)) =
  Unitᵣ (Unitₜ (D ⇨* D′) ok) , D′
redSubst* D (ne′ inc _ D′ neK K≡K) =
    ne′ inc _ (D ⇨* D′) neK K≡K
  , ne₌ inc _ D′ neK K≡K
redSubst*
  D (Bᵣ′ W F G D′ A≡A [F] [G] G-ext ok) =
    Bᵣ′ W F G (D ⇨* D′) A≡A [F] [G] G-ext ok
  , B₌ _ _ D′ A≡A (λ ρ → reflEq ([F] ρ)) (λ ρ [a] → reflEq ([G] ρ [a]))
redSubst* A⇒*B (Idᵣ ⊩B) =
    Idᵣ record
      { ⇒*Id  = A⇒*B ⇨* ⇒*Id
      ; ⊩Ty   = ⊩Ty
      ; ⊩lhs  = ⊩lhs
      ; ⊩rhs  = ⊩rhs
      }
  , Id₌′ ⇒*Id (reflEq ⊩Ty) (reflEqTerm ⊩Ty ⊩lhs) (reflEqTerm ⊩Ty ⊩rhs)
  where
  open _⊩ₗId_ ⊩B
redSubst* D (emb ≤ᵘ-refl x) with redSubst* D x
redSubst* D (emb ≤ᵘ-refl x) | y , y₁ = emb ≤ᵘ-refl y , y₁
redSubst* A⇒*B (emb (≤ᵘ-step p) ⊩B) =
  let ⊩A , A≡B = redSubst* A⇒*B (emb p ⊩B) in
    emb-<-⊩ ≤ᵘ-refl ⊩A
  , irrelevanceEq ⊩A (emb-<-⊩ ≤ᵘ-refl ⊩A) A≡B

opaque

  -- Weak head expansion of reducible terms.
  redSubst*Term : ∀ {A : Term n} {t u l}
                → Γ ⊢ t ⇒* u ∷ A
                → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ u ∷ A / [A]
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
  redSubst*Term t⇒u (Uᵣ′ l ≤ᵘ-refl D) ⊩u =
    let Uₜ A d typeA A≡A [u] = ⊩U∷U⇔⊩U≡∷U .proj₂ ⊩u
        A≡K = subset* D
        d′ = conv* t⇒u A≡K ⇨∷* d
        q = redSubst* (univ* (conv* t⇒u A≡K))
              (univEq (Uᵣ′ l ≤ᵘ-refl (id (wf-⊢≡ (subset* D) .proj₂)))
                 (⊩U∷U⇔⊩U≡∷U .proj₁ (Uₜ A d typeA A≡A [u])))
    in
    Uₜ₌ A A d′ d typeA typeA A≡A (proj₁ q) [u] (proj₂ q)
  redSubst*Term t⇒u ⊩U@(Uᵣ′ l (≤ᵘ-step l<) D) ⊩u =
    let Uₜ A D′ typeA A≡A [u] = ⊩U∷U⇔⊩U≡∷U .proj₂ ⊩u
        Un = Uᵣ′ l l< D
        eq = redSubst*Term t⇒u Un
               (⊩U∷U⇔⊩U≡∷U .proj₁ (Uₜ A D′ typeA A≡A [u]))
    in
    irrelevanceEqTerm Un ⊩U eq
  redSubst*Term t⇒u (ℕᵣ D) ⊩u =
    let ℕₜ n d n≡n prop = ⊩ℕ∷ℕ⇔⊩ℕ≡∷ℕ .proj₂ ⊩u
        t⇒u′ = conv* t⇒u (subset* D)
    in
    ℕₜ₌ n n (t⇒u′ ⇨∷* d) d n≡n (Natural-prop⇔[Natural]-prop .proj₁ prop)
  redSubst*Term t⇒u (Emptyᵣ D) ⊩u =
    let Emptyₜ n d n≡n prop = ⊩Empty∷Empty⇔⊩Empty≡∷Empty .proj₂ ⊩u
        t⇒u′ = conv* t⇒u (subset* D)
    in
    Emptyₜ₌ n n (t⇒u′ ⇨∷* d) d n≡n (Empty-prop⇔[Empty]-prop .proj₁ prop)
  redSubst*Term t⇒u (Unitᵣ (Unitₜ D _)) ⊩u =
    case ⊩Unit∷Unit⇔⊩Unit≡∷Unit .proj₂ ⊩u of λ
      (Unitₜ v u↘v prop) →
    Unitₜ₌ v v (⇒*∷→↘∷→↘∷ (conv* t⇒u (subset* D)) u↘v) u↘v
      (Unit-prop⇔[Unit]-prop .proj₁ prop)
  redSubst*Term t⇒u (ne′ _ _ D neK K≡K) ⊩u =
    let neₜ k d (neNfₜ inc neK₁ k≡k) = ⊩ne∷⇔⊩ne≡∷ .proj₂ ⊩u
        A≡K = subset* D
        d′  = conv* t⇒u A≡K ⇨∷* d
    in
    neₜ₌ k k d′ d (neNfₜ₌ inc neK₁ neK₁ k≡k)
  redSubst*Term t⇒u (Bᵣ BΠ! ⊩A@(Bᵣ F G D A≡A [F] [G] G-ext _)) [u] =
    let Πₜ f d funcF f≡f [f] = ⊩Π∷⇔⊩Π≡∷ ⊩A .proj₂ [u]
        d′   = conv* t⇒u (subset* D) ⇨∷* d
    in
    Πₜ₌ f f d′ d funcF funcF f≡f
      (λ [ρ] [a] → [f] [ρ] (reflEqTerm ([F] [ρ]) [a]))
  redSubst*Term t⇒u (Bᵣ BΣˢ ⊩A@(Bᵣ F G D A≡A [F] [G] G-ext _)) [u] =
    let Σₜ p d pProd p≅p pProp = ⊩Σ∷⇔⊩Σ≡∷ ⊩A .proj₂ [u]
        d′ = conv* t⇒u (subset* D) ⇨∷* d
    in
    Σₜ₌ p p d′ d pProd pProd p≅p (Σ-prop⇔[Σ]-prop .proj₁ pProp)
  redSubst*Term t⇒u (Bᵣ BΣʷ ⊩A@(Bᵣ F G D A≡A [F] [G] G-ext _)) [u] =
    case ⊩Σ∷⇔⊩Σ≡∷ ⊩A .proj₂ [u] of λ where
      (Σₜ p d prodₙ p≅p pProp) →
        let d′ = conv* t⇒u (subset* D) ⇨∷* d in
        Σₜ₌ p p d′ d prodₙ prodₙ p≅p (Σ-prop⇔[Σ]-prop .proj₁ pProp)
      (Σₜ p d (ne x) p≅p pProp) →
        let d′ = conv* t⇒u (subset* D) ⇨∷* d
        in
        Σₜ₌ p p d′ d (ne x) (ne x) p≅p (Σ-prop⇔[Σ]-prop .proj₁ pProp)
  redSubst*Term {Γ} {A} {t} {l} t⇒*u (Idᵣ ⊩A) ⊩u =
    let Idₜ u′ u⇒*u′ u′-id prop = ⊩Id∷⇔⊩Id≡∷ ⊩A .proj₂ ⊩u in
    _ , _ , conv* t⇒*u (subset* ⇒*Id) ⇨∷* u⇒*u′ , u⇒*u′ , u′-id ,
    u′-id , ⊩Id∷-view⇔ .proj₁ prop
    where
    open _⊩ₗId_ ⊩A
  redSubst*Term t⇒u (emb ≤ᵘ-refl     ⊩A) = redSubst*Term t⇒u ⊩A
  redSubst*Term t⇒u (emb (≤ᵘ-step p) ⊩A) = redSubst*Term t⇒u (emb p ⊩A)

-- Weak head expansion of reducible types with single reduction step.
redSubst : ∀ {A B : Term n} {l}
         → Γ ⊢ A ⇒ B
         → Γ ⊩⟨ l ⟩ B
         → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
         → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst A⇒B [B] = redSubst* (redMany-⊢ A⇒B) [B]

-- Weak head expansion of reducible terms with single reduction step.
redSubstTerm : ∀ {A t u : Term n} {l}
             → Γ ⊢ t ⇒ u ∷ A
             → ([A] : Γ ⊩⟨ l ⟩ A)
             → Γ ⊩⟨ l ⟩ u ∷ A / [A]
             → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubstTerm t⇒u [A] [u] = redSubst*Term (redMany t⇒u) [A] [u]

opaque

  -- If A is reducible and reduces to B, then B is reducible and equal
  -- to A.

  redSubst*′ :
    Γ ⊢ A ⇒* B → (⊩A : Γ ⊩⟨ l ⟩ A) →
    (Γ ⊩⟨ l ⟩ B) × Γ ⊩⟨ l ⟩ A ≡ B / ⊩A
  redSubst*′ A⇒*B ⊩U@(Uᵣ′ l l< D) =
    case whrDet↘ (D , Uₙ) A⇒*B of λ
      B⇒*U →
    Uᵣ′ l l< B⇒*U , B⇒*U
  redSubst*′ A⇒*B (ℕᵣ A⇒*ℕ) =
    case whrDet↘ (A⇒*ℕ , ℕₙ) A⇒*B of λ
      B⇒*ℕ →
    ℕᵣ B⇒*ℕ , B⇒*ℕ
  redSubst*′ A⇒*B (Emptyᵣ A⇒*Empty) =
    case whrDet↘ (A⇒*Empty , Emptyₙ) A⇒*B of λ
      B⇒*Empty →
    Emptyᵣ B⇒*Empty , B⇒*Empty
  redSubst*′ A⇒*B (Unitᵣ (Unitₜ A⇒*Unit ok)) =
    case whrDet↘ (A⇒*Unit , Unitₙ) A⇒*B of λ
      B⇒*Unit →
    Unitᵣ (Unitₜ B⇒*Unit ok) , B⇒*Unit
  redSubst*′ A⇒*B (ne′ inc C A⇒*C C-ne C≅C) =
    case whrDet↘ (A⇒*C , ne C-ne) A⇒*B of λ
      B⇒*C →
    ne′ inc C B⇒*C C-ne C≅C , ne₌ inc C B⇒*C C-ne C≅C
  redSubst*′ A⇒*B (Bᵣ′ W C D A⇒*ΠΣ ΠΣ≡ΠΣ ⊩C ⊩D D≡D ok) =
    case whrDet↘ (A⇒*ΠΣ , ⟦ W ⟧ₙ) A⇒*B of λ
      B⇒*ΠΣ →
      Bᵣ′ _ _ _ B⇒*ΠΣ ΠΣ≡ΠΣ ⊩C ⊩D D≡D ok
    , B₌ _ _ B⇒*ΠΣ ΠΣ≡ΠΣ (λ _ → reflEq (⊩C _)) (λ _ _ → reflEq (⊩D _ _))
  redSubst*′ A⇒*B (Idᵣ (Idᵣ Ty lhs rhs A⇒*Id ⊩Ty ⊩lhs ⊩rhs)) =
    case whrDet↘ (A⇒*Id , Idₙ) A⇒*B of λ
      B⇒*Id →
      Idᵣ (Idᵣ Ty lhs rhs B⇒*Id ⊩Ty ⊩lhs ⊩rhs)
    , Id₌′ B⇒*Id (reflEq ⊩Ty) (reflEqTerm ⊩Ty ⊩lhs)
        (reflEqTerm ⊩Ty ⊩rhs)
  redSubst*′ A⇒*B (emb ≤ᵘ-refl ⊩A) =
      case redSubst*′ A⇒*B ⊩A of λ
        (⊩B , A≡B) → (emb ≤ᵘ-refl ⊩B) ,
          (irrelevanceEq ⊩A (emb ≤ᵘ-refl ⊩A) A≡B)
  redSubst*′ A⇒*B (emb (≤ᵘ-step p) ⊩A) =
      case redSubst*′ A⇒*B (emb p ⊩A) of λ
        (⊩B , A≡B) →
        emb-<-⊩ ≤ᵘ-refl ⊩B
      , irrelevanceEq (emb p ⊩A) (emb (≤ᵘ-step p) ⊩A) A≡B

opaque

  -- If t is reducible and reduces to u, then u is "reducibly equal"
  -- to t.

  redSubst*Term′ :
    Γ ⊢ t ⇒* u ∷ A → (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A
  redSubst*Term′ t⇒*u ⊩U@(Uᵣ′ l ≤ᵘ-refl D) ⊩t =
    let Uₜ A t⇒*A A-type A≅A ⊩t = ⊩U∷U⇔⊩U≡∷U .proj₂ ⊩t in
    case whrDet↘Term (t⇒*A , typeWhnf A-type)
           (conv* t⇒*u (subset* D)) of λ
      u⇒*A →
      case redSubst*′ (univ* (conv* t⇒*u (subset* D))) ⊩t of λ
        (⊩u , t≡u) →
    Uₜ₌ A A t⇒*A u⇒*A A-type A-type A≅A ⊩t ⊩u t≡u
  redSubst*Term′ t⇒*u ⊩U@(Uᵣ′ l (≤ᵘ-step l<) D) ⊩t =
    let Uₜ A t⇒*A A-type A≅A ⊩t = ⊩U∷U⇔⊩U≡∷U .proj₂ ⊩t in
    irrelevanceEqTerm (Uᵣ′ l l< D) ⊩U
      (redSubst*Term′ t⇒*u (Uᵣ′ l l< D)
         (⊩U∷U⇔⊩U≡∷U .proj₁ (Uₜ A t⇒*A A-type A≅A ⊩t)))
  redSubst*Term′ t⇒*u (ℕᵣ A⇒*ℕ) ⊩t =
    let ℕₜ v t⇒*v v≅v v-ok = ⊩ℕ∷ℕ⇔⊩ℕ≡∷ℕ .proj₂ ⊩t in
    case whrDet↘Term (t⇒*v , naturalWhnf (natural v-ok))
           (conv* t⇒*u (subset* A⇒*ℕ)) of λ
      u⇒*v →
    ℕₜ₌ v v t⇒*v u⇒*v v≅v (Natural-prop⇔[Natural]-prop .proj₁ v-ok)
  redSubst*Term′ t⇒*u (Emptyᵣ A⇒*Empty) ⊩t =
    let Emptyₜ v t⇒*v v≅v v-ok = ⊩Empty∷Empty⇔⊩Empty≡∷Empty .proj₂ ⊩t in
    case whrDet↘Term (t⇒*v , ne (empty v-ok))
           (conv* t⇒*u (subset* A⇒*Empty)) of λ
      u⇒*v →
    Emptyₜ₌ v v t⇒*v u⇒*v v≅v (Empty-prop⇔[Empty]-prop .proj₁ v-ok)
  redSubst*Term′ t⇒*u (Unitᵣ (Unitₜ A⇒*Unit _)) ⊩t =
    case ⊩Unit∷Unit⇔⊩Unit≡∷Unit .proj₂ ⊩t of λ
      (Unitₜ v t↘v@(_ , v-whnf) prop) →
    Unitₜ₌ v v t↘v
      (whrDet↘Term t↘v (conv* t⇒*u (subset* A⇒*Unit)) , v-whnf)
      (Unit-prop⇔[Unit]-prop .proj₁ prop)
  redSubst*Term′ t⇒*u (ne′ _ B A⇒*B B-ne B≅B) ⊩t =
    let neₜ v t⇒*v prop@(neNfₜ _ v-ne _) = ⊩ne∷⇔⊩ne≡∷ .proj₂ ⊩t
        u⇒*v = whrDet↘Term (t⇒*v , ne v-ne) (conv* t⇒*u (subset* A⇒*B))
    in
    neₜ₌ v v t⇒*v u⇒*v (⊩neNf∷⇔⊩neNf≡∷ .proj₁ prop)
  redSubst*Term′ t⇒*u (Bᵣ BΠ! ⊩A@(Bᵣ C D A⇒*Π Π≡Π ⊩C ⊩D D≡D ok)) ⊩t =
    let Πₜ v t⇒*v v-fun ≅v ⊩v = ⊩Π∷⇔⊩Π≡∷ ⊩A .proj₂ ⊩t
        u⇒*v = whrDet↘Term (t⇒*v , functionWhnf v-fun)
                 (conv* t⇒*u (subset* A⇒*Π))
    in
    v , v , t⇒*v , u⇒*v , v-fun , v-fun , ≅v , ⊩v
  redSubst*Term′
    t⇒*u (Bᵣ (BΣ s _ _) ⊩A@(Bᵣ C D A⇒*Σ Σ≡Σ ⊩C ⊩D D≡D ok)) ⊩t =
    let Σₜ v t⇒*v v-prod ≅v prop = ⊩Σ∷⇔⊩Σ≡∷ ⊩A .proj₂ ⊩t
        u⇒*v = whrDet↘Term (t⇒*v , productWhnf v-prod)
                 (conv* t⇒*u (subset* A⇒*Σ))
    in
    v , v , t⇒*v , u⇒*v , ≅v , v-prod , v-prod ,
    Σ-prop⇔[Σ]-prop .proj₁ prop
  redSubst*Term′ t⇒*u (Idᵣ ⊩A@(Idᵣ Ty lhs rhs A⇒*Id ⊩Ty ⊩lhs ⊩rhs)) ⊩t =
    let Idₜ v t⇒*v v-id prop = ⊩Id∷⇔⊩Id≡∷ ⊩A .proj₂ ⊩t
        u⇒*v = whrDet↘Term (t⇒*v , identityWhnf v-id)
                 (conv* t⇒*u (subset* A⇒*Id))
    in
    v , v , t⇒*v , u⇒*v , v-id , v-id , ⊩Id∷-view⇔ .proj₁ prop
  redSubst*Term′ t⇒*u (emb ≤ᵘ-refl ⊩A)     = redSubst*Term′ t⇒*u ⊩A
  redSubst*Term′ t⇒*u (emb (≤ᵘ-step p) ⊩A) =
    redSubst*Term′ t⇒*u (emb p ⊩A)
