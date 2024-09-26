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
import Definition.Typed.Weakening R as Wk
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R {{eqrel}}
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties.Kit R
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Universe R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Properties.Transitivity R
open import Definition.LogicalRelation.Properties.Whnf R

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
redSubst* D (Levelᵣ [ ⊢B , ⊢Level , D′ ]) =
  let ⊢A = redFirst* D
  in  Levelᵣ ([ ⊢A , ⊢Level , D ⇨* D′ ]) , D′
redSubst* D (Uᵣ′ l′ [l′] l< [ ⊢A₁ , ⊢B , D′ ]) =
  let ⊢A = redFirst* D
  in Uᵣ′ l′ [l′] l< ([ ⊢A , ⊢B , D ⇨* D′ ])  , [ ⊢A₁ , ⊢B , D′ ]
redSubst* D (ℕᵣ [ ⊢B , ⊢ℕ , D′ ]) =
  let ⊢A = redFirst* D
  in  ℕᵣ ([ ⊢A , ⊢ℕ , D ⇨* D′ ]) , D′
redSubst* D (Emptyᵣ [ ⊢B , ⊢Empty , D′ ]) =
  let ⊢A = redFirst* D
  in  Emptyᵣ ([ ⊢A , ⊢Empty , D ⇨* D′ ]) , D′
redSubst* D (Unitᵣ (Unitₜ k [k] k≡ [ ⊢B , ⊢Unit , D′ ] ok)) =
  let ⊢A = redFirst* D
  in  Unitᵣ (Unitₜ k [k] k≡ [ ⊢A , ⊢Unit , D ⇨* D′ ] ok) , D′
redSubst* D (ne′ _ [ ⊢B , ⊢K , D′ ] neK K≡K) =
  let ⊢A = redFirst* D
  in  (ne′ _ [ ⊢A , ⊢K , D ⇨* D′ ] neK K≡K)
  ,   (ne₌ _ [ ⊢B , ⊢K , D′ ] neK K≡K)
redSubst*
  D (Bᵣ′ W F G D′@([ _ , ⊢ΠFG , D″ ]) ⊢F ⊢G A≡A [F] [G] G-ext ok) =
  let ⊢A = redFirst* D
  in  (Bᵣ′ W F G [ ⊢A , ⊢ΠFG , D ⇨* D″ ] ⊢F ⊢G A≡A [F] [G] G-ext ok)
  ,   (B₌ _ _ D′ A≡A (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
        (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a])))
redSubst* A⇒*B (Idᵣ ⊩B) =
  case redFirst* A⇒*B of λ {
    ⊢A →
    (Idᵣ record
       { ⇒*Id  = [ ⊢A , _⊢_:⇒*:_.⊢B ⇒*Id , A⇒*B ⇨* _⊢_:⇒*:_.D ⇒*Id ]
       ; ⊩Ty   = ⊩Ty
       ; ⊩lhs  = ⊩lhs
       ; ⊩rhs  = ⊩rhs
       })
  , Id₌′ ⇒*Id (reflEq ⊩Ty) (reflEqTerm ⊩Ty ⊩lhs) (reflEqTerm ⊩Ty ⊩rhs) }
  where
  open _⊩ₗId_ ⊩B
redSubst* D (emb ≤ᵘ-refl x) with redSubst* D x
redSubst* D (emb ≤ᵘ-refl x) | y , y₁ = emb ≤ᵘ-refl y , y₁
redSubst* A⇒*B (emb (≤ᵘ-step p) ⊩B) =
  let ⊩A , A≡B = redSubst* A⇒*B (emb p ⊩B) in
    emb-<-⊩ ≤ᵘ-refl ⊩A
  , irrelevanceEq ⊩A (emb-<-⊩ ≤ᵘ-refl ⊩A) A≡B

-- Weak head expansion of reducible terms.
redSubst*Term : ∀ {A : Term n} {t u l}
              → Γ ⊢ t ⇒* u ∷ A
              → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ u ∷ A / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubst*Term t⇒u (Levelᵣ D) (Levelₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let A≡Level = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡Level
      t⇒u′ = conv* t⇒u A≡Level
  in  Levelₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] n≡n prop
  ,   Levelₜ₌ n n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] [ ⊢u , ⊢n , d ]
          n≡n (reflLevel-prop prop)
redSubst*Term
  t⇒u (Uᵣ′ l [l] ≤ᵘ-refl D) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [u]) =
  let A≡K  = subset* (red D)
      [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ conv (redFirst*Term t⇒u) A≡K , ⊢u , conv* t⇒u A≡K ⇨∷* d ]
      q = redSubst* (univ* (conv* t⇒u A≡K))
            (univEq (Uᵣ′ l [l] ≤ᵘ-refl (idRed:*: (_⊢_:⇒*:_.⊢B D)))
               (Uₜ A [d] typeA A≡A [u])
               .proj₂)
  in Uₜ A [d′] typeA A≡A {!   !} ,
  {!Uₜ₌ A A [d′] [d] typeA typeA A≡A (proj₁ q) [u] (proj₂ q)!}
  -- in {!Uₜ A [d′] typeA A≡A (proj₁ q)!} ,
  -- {!Uₜ₌ A A [d′] [d] typeA typeA A≡A (proj₁ q) [u] (proj₂ q)!}
redSubst*Term t⇒u ⊩U@(Uᵣ′ l [l] (≤ᵘ-step l<) D) (Uₜ A D′ typeA A≡A [u]) =
  let Un = Uᵣ′ l [l] l< D
      y , eq = redSubst*Term t⇒u Un (Uₜ A D′ typeA A≡A [u])
      y′ = irrelevanceTerm Un ⊩U y
  in y′ , irrelevanceEqTerm Un ⊩U eq
redSubst*Term t⇒u (ℕᵣ D) (ℕₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let A≡ℕ  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡ℕ
      t⇒u′ = conv* t⇒u A≡ℕ
  in  ℕₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] n≡n prop
  ,   ℕₜ₌ n n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] [ ⊢u , ⊢n , d ]
          n≡n (reflNatural-prop prop)
redSubst*Term t⇒u (Emptyᵣ D) (Emptyₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let A≡Empty  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡Empty
      t⇒u′ = conv* t⇒u A≡Empty
  in  Emptyₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] n≡n prop
  ,   Emptyₜ₌ n n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] [ ⊢u , ⊢n , d ]
          n≡n (reflEmpty-prop prop)
redSubst*Term
  t⇒u (Unitᵣ {s} (Unitₜ k [k] k≡ D _)) (Unitₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let A≡Unit  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡Unit
      t⇒u′ = conv* t⇒u A≡Unit
      d′ = [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ]
  in  Unitₜ n d′ n≡n prop
  ,   (case Unit-with-η? s of λ where
         (inj₁ η)                → Unitₜ₌ˢ ⊢t ⊢u η
         (inj₂ (PE.refl , no-η)) →
           Unitₜ₌ʷ n n d′ [ ⊢u , ⊢n , d ] n≡n (reflUnitʷ-prop prop)
             no-η)
redSubst*Term t⇒u (ne′ _ D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] (neNfₜ neK₁ ⊢k k≡k)) =
  let A≡K  = subset* (red D)
      [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ conv (redFirst*Term t⇒u) A≡K , ⊢u , conv* t⇒u A≡K ⇨∷* d ]
  in  neₜ k [d′] (neNfₜ neK₁ ⊢k k≡k) , neₜ₌ k k [d′] [d] (neNfₜ₌ neK₁ neK₁ k≡k)
redSubst*Term
  {Γ = Γ} {A = A} {t} {u} {l}
  t⇒u (Πᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
  [u]@(Πₜ f [d]@([ ⊢t , ⊢u , d ]) funcF f≡f [f] [f]₁) =
  let A≡ΠFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΠFG
      [d′] = [ conv (redFirst*Term t⇒u) A≡ΠFG , ⊢u , t⇒u′ ⇨∷* d ]
      [u′] = Πₜ f [d′] funcF f≡f [f] [f]₁
  in  [u′]
  ,   Πₜ₌ f f [d′] [d] funcF funcF f≡f [u′] [u] λ [ρ] ⊢Δ [a] →
        [f] [ρ] ⊢Δ [a] [a] (reflEqTerm ([F] [ρ] ⊢Δ) [a])
redSubst*Term
  {Γ = Γ} {A} {t} {u} {l}
  t⇒u (Bᵣ′ BΣˢ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
  [u]@(Σₜ p [d]@([ ⊢t , ⊢u , d ]) p≅p pProd pProp) =

  let A≡ΣFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΣFG
      [d′] = [ conv (redFirst*Term t⇒u) A≡ΣFG , ⊢u , conv* t⇒u A≡ΣFG ⇨∷* d ]
      [fstp] , [sndp] = pProp
      [u′] = Σₜ p [d′] p≅p pProd pProp
  in  [u′] , Σₜ₌ p p [d′] [d] pProd pProd p≅p [u′] [u]
                 ([fstp] , [fstp] , reflEqTerm ([F] Wk.id (wf ⊢F)) [fstp] ,
                   reflEqTerm ([G] Wk.id (wf ⊢F) [fstp]) [sndp])
redSubst*Term
  {Γ = Γ} {A} {t} {u} {l}
  t⇒u (Bᵣ′ BΣʷ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
  [u]@(Σₜ p [d]@([ ⊢t , ⊢u , d ]) p≅p prodₙ pProp) =
  let A≡ΣFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΣFG
      [d′] = [ conv (redFirst*Term t⇒u) A≡ΣFG , ⊢u , conv* t⇒u A≡ΣFG ⇨∷* d ]
      p′≡p″ , [p₁] , [p₂] , m≡Σʷ = pProp
      [p₁≡p₁] = reflEqTerm ([F] Wk.id (wf ⊢F)) [p₁]
      [p₂≡p₂] = reflEqTerm ([G] Wk.id (wf ⊢F) [p₁]) [p₂]
      [u′] = Σₜ p [d′] p≅p prodₙ pProp
  in  [u′] ,
      Σₜ₌ p p [d′] [d] prodₙ prodₙ p≅p [u′] [u]
        (p′≡p″ , p′≡p″ , [p₁] , [p₁] , [p₂] , [p₂] , [p₁≡p₁] , [p₂≡p₂])
redSubst*Term
  {Γ = Γ} {A} {t} {u} {l}
  t⇒u (Bᵣ′ BΣʷ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
  [u]@(Σₜ p [d]@([ ⊢t , ⊢u , d ]) p≅p (ne x) p~p) =
  let A≡ΣFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΣFG
      [d′] = [ conv (redFirst*Term t⇒u) A≡ΣFG , ⊢u , conv* t⇒u A≡ΣFG ⇨∷* d ]
      [u′] = Σₜ p [d′] p≅p (ne x) p~p
  in  [u′] , Σₜ₌ p p [d′] [d] (ne x) (ne x) p≅p [u′] [u] p~p
redSubst*Term
  {Γ = Γ} {A = A} {t = t} {l = l} t⇒*u (Idᵣ ⊩A) ⊩u@(u′ , u⇒*u′ , rest) =
  case subset* (red ⇒*Id) of λ {
    A≡Id →
  let ⊩t : Γ ⊩⟨ l ⟩ t ∷ A / Idᵣ ⊩A
      ⊩t =
          u′
        , [ conv (redFirst*Term t⇒*u) A≡Id
          , _⊢_:⇒*:_∷_.⊢u u⇒*u′
          , conv* t⇒*u A≡Id ⇨∷* (redₜ u⇒*u′)
          ]
        , rest
  in
    ⊩t
  , ⊩Id≡∷ ⊩t ⊩u
      (case ⊩Id∷-view-inhabited ⊩u of λ where
         (ne _ u′~u′) → u′~u′
         (rflᵣ _)     → _) }
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
redSubst A⇒B [B] = redSubst* (A⇒B ⇨ id (escape [B])) [B]

-- Weak head expansion of reducible terms with single reduction step.
redSubstTerm : ∀ {A t u : Term n} {l}
             → Γ ⊢ t ⇒ u ∷ A
             → ([A] : Γ ⊩⟨ l ⟩ A)
             → Γ ⊩⟨ l ⟩ u ∷ A / [A]
             → Γ ⊩⟨ l ⟩ t ∷ A / [A]
             × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubstTerm t⇒u [A] [u] = redSubst*Term (t⇒u ⇨ id (escapeTerm [A] [u])) [A] [u]

opaque

  -- If A is reducible and reduces to B, then B is reducible and equal
  -- to A.

  redSubst*′ :
    Γ ⊢ A :⇒*: B → (⊩A : Γ ⊩⟨ l ⟩ A) →
    (Γ ⊩⟨ l ⟩ B) × Γ ⊩⟨ l ⟩ A ≡ B / ⊩A
  redSubst*′ A⇒*B (Levelᵣ A⇒*Level) =
    case whrDet:⇒*: Levelₙ A⇒*Level A⇒*B of λ
      B⇒*Level →
    Levelᵣ B⇒*Level , red B⇒*Level
  redSubst*′ A⇒*B ⊩U@(Uᵣ′ l [l] l< D) =
    case whrDet:⇒*: Uₙ D A⇒*B of λ
      B⇒*U →
    Uᵣ′ l [l] l< B⇒*U , B⇒*U
  redSubst*′ A⇒*B (ℕᵣ A⇒*ℕ) =
    case whrDet:⇒*: ℕₙ A⇒*ℕ A⇒*B of λ
      B⇒*ℕ →
    ℕᵣ B⇒*ℕ , red B⇒*ℕ
  redSubst*′ A⇒*B (Emptyᵣ A⇒*Empty) =
    case whrDet:⇒*: Emptyₙ A⇒*Empty A⇒*B of λ
      B⇒*Empty →
    Emptyᵣ B⇒*Empty , red B⇒*Empty
  redSubst*′ A⇒*B (Unitᵣ (Unitₜ k [k] k≡ A⇒*Unit ok)) =
    case whrDet:⇒*: Unitₙ A⇒*Unit A⇒*B of λ
      B⇒*Unit →
    Unitᵣ (Unitₜ k [k] k≡ B⇒*Unit ok) , red B⇒*Unit
  redSubst*′ A⇒*B (ne′ C A⇒*C C-ne C≅C) =
    case whrDet:⇒*: (ne C-ne) A⇒*C A⇒*B of λ
      B⇒*C →
    ne′ C B⇒*C C-ne C≅C , ne₌ C B⇒*C C-ne C≅C
  redSubst*′ A⇒*B (Bᵣ′ W C D A⇒*ΠΣ ⊢C ⊢D ΠΣ≡ΠΣ ⊩C ⊩D D≡D ok) =
    case whrDet:⇒*: ⟦ W ⟧ₙ A⇒*ΠΣ A⇒*B of λ
      B⇒*ΠΣ →
      Bᵣ′ _ _ _ B⇒*ΠΣ ⊢C ⊢D ΠΣ≡ΠΣ ⊩C ⊩D D≡D ok
    , B₌ _ _ B⇒*ΠΣ ΠΣ≡ΠΣ (λ _ _ → reflEq (⊩C _ _))
        (λ _ _ _ → reflEq (⊩D _ _ _))
  redSubst*′ A⇒*B (Idᵣ (Idᵣ Ty lhs rhs A⇒*Id ⊩Ty ⊩lhs ⊩rhs)) =
    case whrDet:⇒*: Idₙ A⇒*Id A⇒*B of λ
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

  -- If t is reducible and reduces to u, then u is reducible and equal
  -- to t.

  redSubst*Term′ :
    Γ ⊢ t :⇒*: u ∷ A → (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ u ∷ A / ⊩A × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A
  redSubst*Term′ t⇒*u (Levelᵣ A⇒*Level) (Levelₜ v t⇒*v v≅v v-ok) =
    case whrDet:⇒*:Term (level v-ok) t⇒*v
           (convRed:*: t⇒*u (subset* (red A⇒*Level))) of λ
      u⇒*v →
      Levelₜ v u⇒*v v≅v v-ok
    , Levelₜ₌ v v t⇒*v u⇒*v v≅v (reflLevel-prop v-ok)
  redSubst*Term′ t⇒*u ⊩U@(Uᵣ′ l [l] ≤ᵘ-refl D) (Uₜ A t⇒*A A-type A≅A ⊩t) =
    case whrDet:⇒*:Term (typeWhnf A-type) t⇒*A
      (convRed:*: t⇒*u (subset* (red D))) of λ
      u⇒*A →
      case redSubst*′ (univ:*: (convRed:*: t⇒*u (subset* (red D)))) ⊩t of λ
        (⊩u , t≡u) →
      Uₜ A u⇒*A A-type A≅A ⊩u
    , Uₜ₌ A A t⇒*A u⇒*A A-type A-type A≅A ⊩t ⊩u t≡u
  redSubst*Term′
    t⇒*u ⊩U@(Uᵣ′ l [l] (≤ᵘ-step l<) D) (Uₜ A t⇒*A A-type A≅A ⊩t) =
    case redSubst*Term′ t⇒*u (Uᵣ′ l [l] l< D) (Uₜ A t⇒*A A-type A≅A ⊩t) of λ
      (⊩u , t≡u) → (irrelevanceTerm (Uᵣ′ l [l] l< D) ⊩U ⊩u)
        , irrelevanceEqTerm (Uᵣ′ l [l] l< D) ⊩U t≡u
  redSubst*Term′ t⇒*u (ℕᵣ A⇒*ℕ) (ℕₜ v t⇒*v v≅v v-ok) =
    case whrDet:⇒*:Term (naturalWhnf (natural v-ok)) t⇒*v
           (convRed:*: t⇒*u (subset* (red A⇒*ℕ))) of λ
      u⇒*v →
      ℕₜ v u⇒*v v≅v v-ok
    , ℕₜ₌ v v t⇒*v u⇒*v v≅v (reflNatural-prop v-ok)
  redSubst*Term′ t⇒*u (Emptyᵣ A⇒*Empty) (Emptyₜ v t⇒*v v≅v v-ok) =
    case whrDet:⇒*:Term (ne (empty v-ok)) t⇒*v
           (convRed:*: t⇒*u (subset* (red A⇒*Empty))) of λ
      u⇒*v →
      Emptyₜ v u⇒*v v≅v v-ok
    , Emptyₜ₌ v v t⇒*v u⇒*v v≅v (reflEmpty-prop v-ok)
  redSubst*Term′
    t⇒*u (Unitᵣ {s} (Unitₜ k [k] k≡ A⇒*Unit _)) (Unitₜ v t⇒*v v≅v v-ok) =
    case whrDet:⇒*:Term (unit v-ok) t⇒*v
           (convRed:*: t⇒*u (subset* (red A⇒*Unit))) of λ
      u⇒*v →
      Unitₜ v u⇒*v v≅v v-ok
    , (case Unit-with-η? s of λ where
         (inj₁ η) →
           Unitₜ₌ˢ (⊢t-redₜ t⇒*v) (⊢t-redₜ u⇒*v) η
         (inj₂ (PE.refl , no-η)) →
           Unitₜ₌ʷ v v t⇒*v u⇒*v v≅v (reflUnitʷ-prop v-ok) no-η)
  redSubst*Term′
    t⇒*u (ne′ B A⇒*B B-ne B≅B) (neₜ v t⇒*v v-ok@(neNfₜ v-ne _ v~v)) =
    case whrDet:⇒*:Term (ne v-ne) t⇒*v
           (convRed:*: t⇒*u (subset* (red A⇒*B))) of λ
      u⇒*v →
      neₜ v u⇒*v v-ok
    , neₜ₌ v v t⇒*v u⇒*v (neNfₜ₌ v-ne v-ne v~v)
  redSubst*Term′
    t⇒*u ⊩A@(Bᵣ′ BΠ! C D A⇒*Π ⊢C ⊢D Π≡Π ⊩C ⊩D D≡D ok)
    ⊩t@(v , t⇒*v , v-fun , v≅v , v∘≡v∘ , ⊩v∘) =
    case whrDet:⇒*:Term (functionWhnf v-fun) t⇒*v
           (convRed:*: t⇒*u (subset* (red A⇒*Π))) of λ
      u⇒*v →
    case v , u⇒*v , v-fun , v≅v , v∘≡v∘ , ⊩v∘ of λ
      (⊩u : _ ⊩⟨ _ ⟩ _ ∷ _ / ⊩A) →
      ⊩u
    , ( v , v , t⇒*v , u⇒*v , v-fun , v-fun , v≅v , ⊩t , ⊩u
      , (λ _ _ _ → reflEqTerm (⊩D _ _ _) (⊩v∘ _ _ _))
      )
  redSubst*Term′
    t⇒*u ⊩A@(Bᵣ′ (BΣ s _ _) C D A⇒*Σ ⊢C ⊢D Σ≡Σ ⊩C ⊩D D≡D ok)
    ⊩t@(v , t⇒*v , v≅v , v-prod , v-ok) =
    case whrDet:⇒*:Term (productWhnf v-prod) t⇒*v
           (convRed:*: t⇒*u (subset* (red A⇒*Σ))) of λ
      u⇒*v →
    case v , u⇒*v , v≅v , v-prod , v-ok of λ
      (⊩u : _ ⊩⟨ _ ⟩ _ ∷ _ / ⊩A) →
      ⊩u
    , ( v , v , t⇒*v , u⇒*v , v≅v , ⊩t , ⊩u , v-prod , v-prod
      , (case PE.singleton s of λ where
           (𝕤 , PE.refl) →
             case v-ok of λ
               (⊩fst , ⊩snd) →
               ⊩fst , ⊩fst , reflEqTerm (⊩C _ _) ⊩fst
             , reflEqTerm (⊩D _ _ _) ⊩snd
           (𝕨 , PE.refl) →
             case PE.singleton v-prod of λ where
               (ne _  , PE.refl) → v-ok
               (prodₙ , PE.refl) →
                 case v-ok of λ
                   (eq , ⊩fst , ⊩snd , _) →
                   eq , eq , ⊩fst , ⊩fst , ⊩snd , ⊩snd
                 , reflEqTerm (⊩C _ _) ⊩fst
                 , reflEqTerm (⊩D _ _ _) ⊩snd)
      )
  redSubst*Term′
    t⇒*u (Idᵣ (Idᵣ Ty lhs rhs A⇒*Id ⊩Ty ⊩lhs ⊩rhs))
    (v , t⇒*v , v-id , v-ok) =
    case whrDet:⇒*:Term (identityWhnf v-id) t⇒*v
           (convRed:*: t⇒*u (subset* (red A⇒*Id))) of λ
      u⇒*v →
      (v , u⇒*v , v-id , v-ok)
    , ( v , v , t⇒*v , u⇒*v , v-id , v-id
      , (case PE.singleton v-id of λ where
           (rflₙ , PE.refl) → v-ok
           (ne _ , PE.refl) → v-ok)
      )
  redSubst*Term′ t⇒*u (emb ≤ᵘ-refl ⊩A)     = redSubst*Term′ t⇒*u ⊩A
  redSubst*Term′ t⇒*u (emb (≤ᵘ-step p) ⊩A) =
    redSubst*Term′ t⇒*u (emb p ⊩A)
