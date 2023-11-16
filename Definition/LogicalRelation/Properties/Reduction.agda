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

open import Definition.Untyped M hiding (Wk; _∷_; K)
open import Definition.Typed R
open import Definition.Typed.Properties R
import Definition.Typed.Weakening R as Wk
open import Definition.Typed.RedSteps R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Universe R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Properties.Transitivity R

open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n

-- Weak head expansion of reducible types.
redSubst* : ∀ {A B : Term n} {l}
          → Γ ⊢ A ⇒* B
          → Γ ⊩⟨ l ⟩ B
          → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A)
          → Γ ⊩⟨ l ⟩ A ≡ B / [A]
redSubst* D (Uᵣ′ l′ l< ⊢Γ) rewrite redU* D =
  Uᵣ′ l′ l< ⊢Γ , PE.refl
redSubst* D (ℕᵣ [ ⊢B , ⊢ℕ , D′ ]) =
  let ⊢A = redFirst* D
  in  ℕᵣ ([ ⊢A , ⊢ℕ , D ⇨* D′ ]) , D′
redSubst* D (Emptyᵣ [ ⊢B , ⊢Empty , D′ ]) =
  let ⊢A = redFirst* D
  in  Emptyᵣ ([ ⊢A , ⊢Empty , D ⇨* D′ ]) , D′
redSubst* D (Unitᵣ (Unitₜ [ ⊢B , ⊢Unit , D′ ] ok)) =
  let ⊢A = redFirst* D
  in  Unitᵣ (Unitₜ [ ⊢A , ⊢Unit , D ⇨* D′ ] ok) , D′
redSubst* D (ne′ K [ ⊢B , ⊢K , D′ ] neK K≡K) =
  let ⊢A = redFirst* D
  in  (ne′ K [ ⊢A , ⊢K , D ⇨* D′ ] neK K≡K)
  ,   (ne₌ _ [ ⊢B , ⊢K , D′ ] neK K≡K)
redSubst* D (Bᵣ′ W F G [ ⊢B , ⊢ΠFG , D′ ] ⊢F ⊢G A≡A [F] [G] G-ext ok) =
  let ⊢A = redFirst* D
  in  (Bᵣ′ W F G [ ⊢A , ⊢ΠFG , D ⇨* D′ ] ⊢F ⊢G A≡A [F] [G] G-ext ok)
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
redSubst* D (emb 0<1 x) with redSubst* D x
redSubst* D (emb 0<1 x) | y , y₁ = emb 0<1 y , y₁

-- Weak head expansion of reducible terms.
redSubst*Term : ∀ {A : Term n} {t u l}
              → Γ ⊢ t ⇒* u ∷ A
              → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ u ∷ A / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              × Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
redSubst*Term t⇒u (Uᵣ′ .⁰ 0<1 ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [u]) =
  let [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ redFirst*Term t⇒u , ⊢u , t⇒u ⇨∷* d ]
      q = redSubst* (univ* t⇒u) (univEq (Uᵣ′ ⁰ 0<1 ⊢Γ) (Uₜ A [d] typeA A≡A [u]))
  in Uₜ A [d′] typeA A≡A (proj₁ q)
  ,  Uₜ₌ A A [d′] [d] typeA typeA A≡A (proj₁ q) [u] (proj₂ q)
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
redSubst*Term t⇒u (Unitᵣ {s = 𝕤} (Unitₜ D _)) (Unitₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let A≡Unit  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡Unit
      t⇒u′ = conv* t⇒u A≡Unit
  in  Unitₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] n≡n prop
  ,   Unitₜ₌ ⊢t ⊢u
redSubst*Term t⇒u (Unitᵣ {s = 𝕨} (Unitₜ D _)) (Unitₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let A≡Unit  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡Unit
      t⇒u′ = conv* t⇒u A≡Unit
      d′ = [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ]
  in  Unitₜ n d′ n≡n prop
  ,   Unitₜ₌ n n d′ [ ⊢u , ⊢n , d ] n≡n (reflUnitʷ-prop prop)
redSubst*Term t⇒u (ne′ K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] (neNfₜ neK₁ ⊢k k≡k)) =
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
redSubst*Term t⇒u (emb 0<1 x) [u] = redSubst*Term t⇒u x [u]

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
