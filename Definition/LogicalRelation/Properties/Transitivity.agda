------------------------------------------------------------------------
-- Equality in the logical relation is transitive
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Transitivity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.ShapeView R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Irrelevance R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Conversion R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Kit R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Primitive R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Reflexivity R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Symmetry R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Whnf R ⦃ eqrel ⦄

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum

private
  variable
    n ℓ                     : Nat
    Γ                       : Con Term n
    A B Ty′ lhs′ rhs′ t u v : Term _
    l                       : Universe-level
    s                       : Strength

mutual
  transEqTermℕ : ∀ {n n′ n″}
               → Γ ⊩ℕ n  ≡ n′  ∷ℕ
               → Γ ⊩ℕ n′ ≡ n″ ∷ℕ
               → Γ ⊩ℕ n  ≡ n″ ∷ℕ
  transEqTermℕ (ℕₜ₌ k _ d d′ t≡u prop) (ℕₜ₌ _ k″ d₁ d″ t≡u₁ prop₁) =
    let k₁Whnf = naturalWhnf (proj₁ (split prop₁))
        k′Whnf = naturalWhnf (proj₂ (split prop))
        k₁≡k′ = whrDet*Term (d₁ , k₁Whnf) (d′ , k′Whnf)
        prop′ = PE.subst (λ x → [Natural]-prop _ x _) k₁≡k′ prop₁
    in  ℕₜ₌ k k″ d d″
          (≅ₜ-trans t≡u (PE.subst (λ x → _ ⊢ x ≅ _ ∷ _) k₁≡k′ t≡u₁))
          (transNatural-prop prop prop′)

  transNatural-prop : ∀ {k k′ k″}
                    → [Natural]-prop Γ k k′
                    → [Natural]-prop Γ k′ k″
                    → [Natural]-prop Γ k k″
  transNatural-prop (sucᵣ x) (sucᵣ x₁) = sucᵣ (transEqTermℕ x x₁)
  transNatural-prop (sucᵣ _) (ne (neNfₜ₌ _ (ne () _) _ _))
  transNatural-prop zeroᵣ prop₁ = prop₁
  transNatural-prop prop zeroᵣ = prop
  transNatural-prop (ne (neNfₜ₌ _ _ (ne () _) _)) (sucᵣ _)
  transNatural-prop (ne [k≡k′]) (ne [k′≡k″]) =
    ne (transEqTermNe [k≡k′] [k′≡k″])

-- Empty
transEmpty-prop : ∀ {k k′ k″}
  → [Empty]-prop Γ k k′
  → [Empty]-prop Γ k′ k″
  → [Empty]-prop Γ k k″
transEmpty-prop (ne [k≡k′]) (ne [k′≡k″]) =
  ne (transEqTermNe [k≡k′] [k′≡k″])

transEqTermEmpty : ∀ {n n′ n″}
  → Γ ⊩Empty n  ≡ n′ ∷Empty
  → Γ ⊩Empty n′ ≡ n″ ∷Empty
  → Γ ⊩Empty n  ≡ n″ ∷Empty
transEqTermEmpty
  (Emptyₜ₌ k _ d d′ t≡u prop) (Emptyₜ₌ _ k″ d₁ d″ t≡u₁ prop₁) =
  let k₁Whnf = ne (proj₁ (esplit prop₁))
      k′Whnf = ne (proj₂ (esplit prop))
      k₁≡k′ = whrDet*Term (d₁ , k₁Whnf) (d′ , k′Whnf)
      prop′ = PE.subst (λ x → [Empty]-prop _ x _) k₁≡k′ prop₁
  in Emptyₜ₌ k k″ d d″
       (≅ₜ-trans t≡u (PE.subst (λ x → _ ⊢ x ≅ _ ∷ _) k₁≡k′ t≡u₁))
       (transEmpty-prop prop prop′)

-- Transitivity for [Unit]-prop′ Γ l 𝕨.
transUnit-prop′ :
  [Unit]-prop′ Γ 𝕨 t u →
  [Unit]-prop′ Γ 𝕨 u v →
  [Unit]-prop′ Γ 𝕨 t v
transUnit-prop′ starᵣ starᵣ = starᵣ
transUnit-prop′ (ne t≡u) (ne u≡v) = ne (transEqTermNe t≡u u≡v)
transUnit-prop′ starᵣ (ne (neNfₜ₌ _ (ne () _) _ _))
transUnit-prop′ (ne (neNfₜ₌ _ _ (ne () _) _)) starᵣ

transUnit-prop : ∀ {k k′ k″}
  → [Unit]-prop Γ s k k′
  → [Unit]-prop Γ s k′ k″
  → [Unit]-prop Γ s k k″
transUnit-prop (Unitₜ₌ʷ prop₁ no-η) (Unitₜ₌ʷ prop₂ _) =
  Unitₜ₌ʷ (transUnit-prop′ prop₁ prop₂) no-η
transUnit-prop (Unitₜ₌ʷ _ no-η) (Unitₜ₌ˢ η) =
  ⊥-elim (no-η (Unit-with-η-𝕨→Unitʷ-η η))
transUnit-prop (Unitₜ₌ˢ η) (Unitₜ₌ʷ _ no-η) =
  ⊥-elim (no-η (Unit-with-η-𝕨→Unitʷ-η η))
transUnit-prop (Unitₜ₌ˢ η) (Unitₜ₌ˢ _) =
  Unitₜ₌ˢ η


record TransKit (l : Universe-level) : Set a where
  field
    -- Transitivity of type equality.
    transEq : ∀ {A B C l′ l″}
              ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B) ([C] : Γ ⊩⟨ l″ ⟩ C)
            → Γ ⊩⟨ l ⟩  A ≡ B / [A]
            → Γ ⊩⟨ l′ ⟩ B ≡ C / [B]
            → Γ ⊩⟨ l ⟩  A ≡ C / [A]

    -- Transitivity of term equality.
    transEqTerm : {n : Nat} → ∀ {Γ : Con Term n} {A t u v}
                  ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
                → Γ ⊩⟨ l ⟩ u ≡ v ∷ A / [A]
                → Γ ⊩⟨ l ⟩ t ≡ v ∷ A / [A]

    -- A variant of the constructor Id₌.
    Id₌′ :
      {⊩A : Γ ⊩′⟨ l ⟩Id A} →
      let open _⊩ₗId_ ⊩A in
      Γ ⊢ B ⇒* Id Ty′ lhs′ rhs′ →
      Γ ⊩⟨ l ⟩ Ty ≡ Ty′ / ⊩Ty →
      Γ ⊩⟨ l ⟩ lhs ≡ lhs′ ∷ Ty / ⊩Ty →
      Γ ⊩⟨ l ⟩ rhs ≡ rhs′ ∷ Ty / ⊩Ty →
      Γ ⊩⟨ l ⟩ A ≡ B / Idᵣ ⊩A

private module Trans (l : Universe-level) (rec : ∀ {l′} → l′ <ᵘ l → TransKit l′) where

  module Rec {l′} (l′< : l′ <ᵘ l) = TransKit (rec l′<)

  -- Helper function for transitivity of type equality using shape views.
  transEqT : ∀ {n} {Γ : Con Term n} {A B C l′ l″}
             {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B} {[C] : Γ ⊩⟨ l″ ⟩ C}
           → ShapeView₃ Γ l l′ l″ A B C [A] [B] [C]
           → Γ ⊩⟨ l ⟩  A ≡ B / [A]
           → Γ ⊩⟨ l′ ⟩ B ≡ C / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C / [A]

  -- Transitivity of type equality.
  transEq : ∀ {A B C l′ l″}
            ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B) ([C] : Γ ⊩⟨ l″ ⟩ C)
          → Γ ⊩⟨ l ⟩  A ≡ B / [A]
          → Γ ⊩⟨ l′ ⟩ B ≡ C / [B]
          → Γ ⊩⟨ l ⟩  A ≡ C / [A]
  transEq [A] [B] [C] A≡B B≡C =
    transEqT
      (combine (goodCases [A] [B] A≡B) (goodCases [B] [C] B≡C))
      A≡B B≡C

  -- Transitivity of type equality with some propositonally equal types.
  transEq′ : ∀ {A B B′ C C′ l′ l″} → B PE.≡ B′ → C PE.≡ C′
           → ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B) ([C] : Γ ⊩⟨ l″ ⟩ C)
           → Γ ⊩⟨ l ⟩  A ≡ B′ / [A]
           → Γ ⊩⟨ l′ ⟩ B ≡ C′ / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C  / [A]
  transEq′ PE.refl PE.refl [A] [B] [C] A≡B B≡C =
    transEq [A] [B] [C] A≡B B≡C

  -- Transitivity of term equality.
  transEqTerm : {n : Nat} → ∀ {Γ : Con Term n} {A t u v}
                ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
              → Γ ⊩⟨ l ⟩ u ≡ v ∷ A / [A]
              → Γ ⊩⟨ l ⟩ t ≡ v ∷ A / [A]

  -- A variant of the constructor Id₌.
  Id₌′ :
    {⊩A : Γ ⊩′⟨ l ⟩Id A} →
    let open _⊩ₗId_ ⊩A in
    Γ ⊢ B ⇒* Id Ty′ lhs′ rhs′ →
    Γ ⊩⟨ l ⟩ Ty ≡ Ty′ / ⊩Ty →
    Γ ⊩⟨ l ⟩ lhs ≡ lhs′ ∷ Ty / ⊩Ty →
    Γ ⊩⟨ l ⟩ rhs ≡ rhs′ ∷ Ty / ⊩Ty →
    Γ ⊩⟨ l ⟩ A ≡ B / Idᵣ ⊩A
  Id₌′ {⊩A = ⊩A} ⇒*Id′ Ty≡Ty′ lhs≡lhs′ rhs≡rhs′ = record
    { ⇒*Id′             = ⇒*Id′
    ; Ty≡Ty′            = Ty≡Ty′
    ; lhs≡lhs′          = lhs≡lhs′
    ; rhs≡rhs′          = rhs≡rhs′
    ; lhs≡rhs→lhs′≡rhs′ = λ lhs≡rhs →
        transEqTerm ⊩Ty (symEqTerm ⊩Ty lhs≡lhs′) $
        transEqTerm ⊩Ty lhs≡rhs rhs≡rhs′
    ; lhs′≡rhs′→lhs≡rhs = λ lhs′≡rhs′ →
        transEqTerm ⊩Ty lhs≡lhs′ $
        transEqTerm ⊩Ty lhs′≡rhs′ $
        symEqTerm ⊩Ty rhs≡rhs′
    }
    where
    open _⊩ₗId_ ⊩A

  transEqT (Levelᵥ D D′ D″) A≡B B≡C = B≡C
  transEqT
    (Liftᵥ LiftA (Liftᵣ D₀ _ [F′]) (Liftᵣ D₁ _ [F″]))
    (Lift₌ D k≡k′ F≡F′)
    (Lift₌ D′ k′≡k″ F′≡F″)
    = case whrDet* (D₀ , Liftₙ) (D , Liftₙ) of λ {
        PE.refl →
      case whrDet* (D₁ , Liftₙ) (D′ , Liftₙ) of λ {
        PE.refl →
      Lift₌ D′
        (transEqTermLevel k≡k′ k′≡k″)
        (transEq _ [F′] [F″] F≡F′ F′≡F″) }}
  transEqT (ℕᵥ D D′ D″) A≡B B≡C = B≡C
  transEqT (Emptyᵥ D D′ D″) A≡B B≡C = B≡C
  transEqT (Unitᵥ _ (Unitᵣ B⇒*Unit₁ _) _) (Unit₌ B⇒*Unit₂) (Unit₌ C⇒*Unit) =
    Unit₌ C⇒*Unit
  transEqT
    (ne (ne _ _ D neK K≡K) (ne _ K₁ D₁ neK₁ _) (ne _ K₂ D₂ neK₂ _))
    (ne₌ _ M D′ neM K≡M) (ne₌ inc M₁ D″ neM₁ K≡M₁)
    rewrite whrDet* (D₁ , ne neK₁) (D′ , ne neM)
          | whrDet* (D₂ , ne neK₂) (D″ , ne neM₁) =
    ne₌ inc M₁ D″ neM₁ (≅-trans K≡M K≡M₁)
  transEqT {n = n} {Γ = Γ} {l′ = l′} {l″ = l″}
          (Bᵥ W W′ W″ (Bᵣ F G D A≡A [F] [G] G-ext _)
                (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _)
                (Bᵣ F₂ G₂ D₂ A≡A₂ [F]₂ [G]₂ G-ext₂ _))
          (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
          (B₌ F″ G″ D″ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
    case B-PE-injectivity W′ W
          (whrDet* (D₁ , ⟦ W′ ⟧ₙ) (D′ , ⟦ W ⟧ₙ)) of λ {
      (PE.refl , PE.refl , PE.refl) →
    case B-PE-injectivity W″ W′
          (whrDet* (D₂ , ⟦ W″ ⟧ₙ) (D″ , ⟦ W′ ⟧ₙ)) of λ {
      (PE.refl , PE.refl , PE.refl) →
    B₌ F″ G″ D″ (≅-trans A≡B A≡B₁)
      (λ ρ → transEq ([F] ρ) ([F]₁ ρ) ([F]₂ ρ) ([F≡F′] ρ) ([F≡F′]₁ ρ))
      (λ ρ [a] →
        let [a′] = convTerm₁ ([F] ρ) ([F]₁ ρ) ([F≡F′] ρ) [a]
            [a″] = convTerm₁ ([F]₁ ρ) ([F]₂ ρ) ([F≡F′]₁ ρ) [a′]
        in  transEq ([G] ρ [a]) ([G]₁ ρ [a′]) ([G]₂ ρ [a″])
              ([G≡G′] ρ [a]) ([G≡G′]₁ ρ [a′])) }}
  transEqT (Uᵥ (Uᵣ l′ [l′] l< ⇒*U) (Uᵣ l′₁ [l′₁] l<₁ ⇒*U₁) (Uᵣ l′₂ [l′₂] l<₂ ⇒*U₂)) (U₌ k D l′≡k) (U₌ k′ D₁ k≡k′)
    with whrDet* (⇒*U₁ , Uₙ) (D , Uₙ)  | whrDet* (⇒*U₂ , Uₙ) (D₁ , Uₙ)
  ... | PE.refl | PE.refl =
      U₌ k′ D₁ (transEqTermLevel l′≡k k≡k′)
  transEqT (Idᵥ ⊩A ⊩B@record{} ⊩C@record{}) A≡B B≡C =
    case whrDet* (_⊩ₗId_.⇒*Id ⊩B , Idₙ)
          (_⊩ₗId_≡_/_.⇒*Id′ A≡B , Idₙ) of λ {
      PE.refl →
    case whrDet* (_⊩ₗId_.⇒*Id ⊩C , Idₙ)
          (_⊩ₗId_≡_/_.⇒*Id′ B≡C , Idₙ) of λ {
      PE.refl →
    Id₌′
      (_⊩ₗId_≡_/_.⇒*Id′ B≡C)
      (transEq
        (_⊩ₗId_.⊩Ty ⊩A)
        (_⊩ₗId_.⊩Ty ⊩B)
        (_⊩ₗId_.⊩Ty ⊩C)
        (_⊩ₗId_≡_/_.Ty≡Ty′ A≡B)
        (_⊩ₗId_≡_/_.Ty≡Ty′ B≡C))
      (transEqTerm
        (_⊩ₗId_.⊩Ty ⊩A)
        (_⊩ₗId_≡_/_.lhs≡lhs′ A≡B) $
      convEqTerm₂
        (_⊩ₗId_.⊩Ty ⊩A)
        (_⊩ₗId_.⊩Ty ⊩B)
        (_⊩ₗId_≡_/_.Ty≡Ty′ A≡B)
        (_⊩ₗId_≡_/_.lhs≡lhs′ B≡C))
      (transEqTerm
        (_⊩ₗId_.⊩Ty ⊩A)
        (_⊩ₗId_≡_/_.rhs≡rhs′ A≡B) $
      convEqTerm₂
        (_⊩ₗId_.⊩Ty ⊩A)
        (_⊩ₗId_.⊩Ty ⊩B)
        (_⊩ₗId_≡_/_.Ty≡Ty′ A≡B)
        (_⊩ₗId_≡_/_.rhs≡rhs′ B≡C)) }}

  transEqTerm (Levelᵣ D) [t≡u] [u≡v] = transEqTermLevel [t≡u] [u≡v]
  transEqTerm
    (Liftᵣ′ D [k] [F])
    (Liftₜ₌ _ _ t↘ u↘ t≡u)
    (Liftₜ₌ _ _ u↘′ v↘ u≡v)
    = case whrDet*Term u↘ u↘′ of λ {
      PE.refl →
    Liftₜ₌ _ _ t↘ v↘ (transEqTerm [F] t≡u u≡v) }
  transEqTerm (Uᵣ′ _ [k] k< D)
              (Uₜ₌ A B d d′ typeA typeB t≡u [t] [u] [t≡u])
              (Uₜ₌ A₁ B₁ d₁ d₁′ typeA₁ typeB₁ t≡u₁ [t]₁ [u]₁ [t≡u]₁) =
    case whrDet*Term (d₁ , typeWhnf typeA₁) (d′ , typeWhnf typeB) of λ where
    PE.refl →
      Uₜ₌ A B₁ d d₁′ typeA typeB₁ (≅ₜ-trans t≡u t≡u₁) [t] [u]₁ $
        ⊩<≡⇔⊩≡ k< .proj₂ $ Rec.transEq k<
          (⊩<⇔⊩ k< .proj₁ [t])
          (⊩<⇔⊩ k< .proj₁ [t]₁)
          (⊩<⇔⊩ k< .proj₁ [u]₁)
          (⊩<≡⇔⊩≡ k< .proj₁ [t≡u])
          (⊩<≡⇔⊩≡ k< .proj₁ [t≡u]₁)
  transEqTerm (ℕᵣ D) [t≡u] [u≡v] = transEqTermℕ [t≡u] [u≡v]
  transEqTerm (Emptyᵣ D) [t≡u] [u≡v] = transEqTermEmpty [t≡u] [u≡v]
  transEqTerm
    (Unitᵣ _) (Unitₜ₌ _ _ ↘u₁ ↘u₂ prop₁) (Unitₜ₌ _ _ ↘v₁ ↘v₂ prop₂) =
    case whrDet*Term ↘u₂ ↘v₁ of λ {
      PE.refl →
    Unitₜ₌ _ _ ↘u₁ ↘v₂ (transUnit-prop prop₁ prop₂) }
  transEqTerm
    {n} (ne′ _ _ D neK K≡K) (neₜ₌ k m d d′ (neNfₜ₌ _ neK₁ neM k≡m))
    (neₜ₌ k₁ m₁ d₁ d″ (neNfₜ₌ inc neK₂ neM₁ k≡m₁)) =
    let k₁≡m = whrDet*Term (d₁ , ne! neK₂) (d′ , ne! neM)
    in  neₜ₌ k m₁ d d″
            (neNfₜ₌ inc neK₁ neM₁
                    (~-trans k≡m (PE.subst (λ (x : Term n) → _ ⊢ x ~ _ ∷ _) k₁≡m k≡m₁)))
  transEqTerm (Bᵣ′ BΠ! F G D A≡A [F] [G] G-ext _)
    (Πₜ₌ f g d d′ funcF funcG f≡g [f≡g])
    (Πₜ₌ f₁ g₁ d₁ d₁′ funcF₁ funcG₁ f≡g₁ [f≡g]₁)
    rewrite whrDet*Term (d′ , Functionᵃ→Whnf funcG)
              (d₁ , Functionᵃ→Whnf funcF₁) =
    Πₜ₌ f g₁ d d₁′ funcF funcG₁ (≅ₜ-trans f≡g f≡g₁)
      (λ ρ ⊩v ⊩w v≡w →
        transEqTerm ([G] ρ ⊩v) ([f≡g] ρ ⊩v ⊩v (reflEqTerm ([F] ρ) ⊩v))
          ([f≡g]₁ ρ ⊩v ⊩w v≡w))
  transEqTerm
    {n = n} {Γ = Γ} (Bᵣ′ (BΣ 𝕤 p′ q) F G D A≡A [F] [G] G-ext _)
    (Σₜ₌ p r d d′ pProd rProd p≅r ([fstp] , [fstr] , [fst≡] , [snd≡]))
    (Σₜ₌ p₁ r₁ d₁ d₁′ pProd₁ rProd₁ p≅r₁
      ([fstp]₁ , [fstr]₁ , [fst≡]₁ , [snd≡]₁)) =
    let p₁≡r = whrDet*Term (d₁ , Productᵃ→Whnf pProd₁)
                (d′ , Productᵃ→Whnf rProd)
        p≅r₁ = ≅ₜ-trans p≅r
                (PE.subst
                    (λ (x : Term n) → Γ ⊢ x ≅ r₁ ∷ Σˢ p′ , q ▷ F ▹ G)
                    p₁≡r p≅r₁)
        [F]′ = [F] _
        [fst≡]′ = transEqTerm [F]′ [fst≡]
          (PE.subst
            (λ (x : Term n) →
                Γ ⊩⟨ _ ⟩ fst _ x ≡ fst _ r₁ ∷ wk id F / [F]′)
            p₁≡r [fst≡]₁)
        [Gfstp≡Gfstp₁] = G-ext _ [fstp] [fstp]₁
          (PE.subst
            (λ (x : Term n) →
                Γ ⊩⟨ _ ⟩ fst _ p ≡ fst _ x ∷ wk id F / [F]′)
            (PE.sym p₁≡r) [fst≡])
        [Gfstp] = [G] _ [fstp]
        [Gfstp₁] = [G] _ [fstp]₁
        [snd≡]₁′ = convEqTerm₂ [Gfstp] [Gfstp₁] [Gfstp≡Gfstp₁] [snd≡]₁
        [snd≡]′ = transEqTerm [Gfstp] [snd≡]
          (PE.subst
            (λ (x : Term n) →
                Γ ⊩⟨ _ ⟩ snd _ x ≡ snd _ r₁ ∷ wk (lift id) G [ fst _ p ]₀ /
                  [Gfstp])
            p₁≡r [snd≡]₁′)
    in  Σₜ₌ p r₁ d d₁′ pProd rProd₁ p≅r₁ ([fstp] , [fstr]₁ , [fst≡]′ , [snd≡]′)
  transEqTerm
    {n = n} {Γ = Γ}
    (Bᵣ′ (BΣ 𝕨 p″ q) F G D A≡A [F] [G] G-ext _)
    (Σₜ₌ p r d d′ prodₙ prodₙ p≅r
      (PE.refl , PE.refl , PE.refl , PE.refl ,
        [p₁] , [r₁] , [p₁≡r₁] , [p₂≡r₂]))
    (Σₜ₌ p′ r′ d₁ d₁′ prodₙ prodₙ p′≅r′
      (PE.refl , PE.refl , PE.refl , PE.refl ,
        [p₁]′ , [r₁]′ , [p′₁≡r′₁] , [p′₂≡r′₂])) =
    let p′≡r = whrDet*Term (d₁ , prodₙ) (d′ , prodₙ)
        _ , _ , p′₁≡r₁ , p′₂≡r₂ = prod-PE-injectivity p′≡r
        p≅r′ = ≅ₜ-trans p≅r
                  (PE.subst (λ x → Γ ⊢ x ≅ r′ ∷ Σʷ p″ , q ▷ F ▹ G)
                    p′≡r p′≅r′)
        [F]′ = [F] _
        [p₁≡r′₁] = transEqTerm [F]′ [p₁≡r₁] (PE.subst (λ (x : Term n) → Γ ⊩⟨ _ ⟩ x ≡ _ ∷ wk id F / [F]′) p′₁≡r₁ [p′₁≡r′₁])
        [Gp≡Gp₁] = G-ext _ [p₁] [p₁]′
                        (PE.subst (λ (x : Term n) → Γ ⊩⟨ _ ⟩ _ ≡ x ∷ wk id F / [F]′)
                                  (PE.sym p′₁≡r₁) [p₁≡r₁])
        [Gp] = [G] _ [p₁]
        [Gp′] = [G] _ [p₁]′
        [r₂≡r′₂] = convEqTerm₂ [Gp] [Gp′] [Gp≡Gp₁]
                              (PE.subst (λ (x : Term n) → Γ ⊩⟨ _ ⟩ x ≡ _ ∷ wk (lift id) G [ _ ]₀ / [Gp′])
                                        p′₂≡r₂ [p′₂≡r′₂])
        [p₂≡r′₂] = transEqTerm [Gp] [p₂≡r₂] [r₂≡r′₂]
    in  Σₜ₌ p r′ d d₁′ prodₙ prodₙ p≅r′
          (PE.refl , PE.refl , PE.refl , PE.refl ,
          [p₁] , [r₁]′ , [p₁≡r′₁] , [p₂≡r′₂])
  transEqTerm
    {n = n} {Γ = Γ} (Bᵣ′ (BΣ 𝕨 p′ q) F G D A≡A [F] [G] G-ext _)
    (Σₜ₌ p r d d′ (ne x) (ne x₁) p≅r (_ , p~r))
    (Σₜ₌ p₁ r₁ d₁ d₁′ (ne x₂) (ne x₃) p≅r₁ (inc , p₁~r₁)) =
    let p₁≡r = whrDet*Term (d₁ , ne! x₂) (d′ , ne! x₁)
        p≅r₁ = ≅ₜ-trans p≅r
                  (PE.subst
                    (λ (x : Term n) → Γ ⊢ x ≅ r₁ ∷ Σʷ p′ , q ▷ F ▹ G)
                    p₁≡r p≅r₁)
        p~r₁ = ~-trans p~r
                (PE.subst
                    (λ (x : Term n) → Γ ⊢ x ~ _ ∷ Σʷ p′ , q ▷ F ▹ G)
                    p₁≡r p₁~r₁)
    in  Σₜ₌ p r₁ d d₁′ (ne x) (ne x₃) p≅r₁ (inc , p~r₁)
  transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
              (Σₜ₌ p r d d′ prodₙ prodₙ p≅r prop)
              (Σₜ₌ p₁ r₁ d₁ d₁′ (ne x) (ne x₁) p≅r₁ prop₁) =
    ⊥-elim $
    prod≢ne (ne⁻ x) (whrDet*Term (d′ , prodₙ) (d₁ , ne (ne⁻ x)))
  transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
              (Σₜ₌ p r d d′ (ne x) (ne x₁) p≅r prop)
              (Σₜ₌ p₁ r₁ d₁ d₁′ prodₙ prodₙ p≅r₁ prop₁) =
    ⊥-elim $
    prod≢ne (ne⁻ x₁) (whrDet*Term (d₁ , prodₙ) (d′ , ne (ne⁻ x₁)))
  transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
              (Σₜ₌ p r d d′ prodₙ (ne x) p≅r (lift ()))
              (Σₜ₌ p₁ r₁ d₁ d₁′ pProd₁ rProd₁ p≅r₁ prop₁)
  transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
              (Σₜ₌ p r d d′ (ne x) prodₙ p≅r (lift ()))
              (Σₜ₌ p₁ r₁ d₁ d₁′ pProd₁ rProd₁ p≅r₁ prop₁)
  transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
              (Σₜ₌ p r d d′ pProd rProd p≅r prop)
              (Σₜ₌ p₁ r₁ d₁ d₁′ prodₙ (ne x) p≅r₁ (lift ()))
  transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
              (Σₜ₌ p r d d′ pProd rProd p≅r prop)
              (Σₜ₌ p₁ r₁ d₁ d₁′ (ne x) prodₙ p≅r₁ (lift ()))
  transEqTerm
    (Idᵣ ⊩A)
    t≡u@(_ , _ , _ , u⇒*u′ , _ , u′-id , _)
    u≡v@(_ , _ , u⇒*u″ , _ , u″-id , _) =
    case whrDet*Term
          (u⇒*u′ , Identityᵃ→Whnf u′-id)
          (u⇒*u″ , Identityᵃ→Whnf u″-id) of λ {
      PE.refl →
    let ⊩t , _      = ⊩Id≡∷⁻¹ ⊩A t≡u
        _  , ⊩v , _ = ⊩Id≡∷⁻¹ ⊩A u≡v
    in
    ⊩Id≡∷ ⊩A ⊩t ⊩v
      (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
        (ne _ _ u′-n t′~u′) → case ⊩Id≡∷-view-inhabited ⊩A u≡v of λ where
          (ne inc _ _ u′~v′) → inc , ~-trans t′~u′ u′~v′
          (rfl₌ _)       →
            ⊥-elim $ rfl≢ne (ne⁻ u′-n) $
            whrDet*Term (u⇒*u″ , rflₙ) (u⇒*u′ , ne (ne⁻ u′-n))
        (rfl₌ _) → case ⊩Id≡∷-view-inhabited ⊩A u≡v of λ where
          (rfl₌ _)        → _
          (ne _ u″-n _ _) →
            ⊥-elim $ rfl≢ne (ne⁻ u″-n) $
            whrDet*Term (u⇒*u′ , rflₙ) (u⇒*u″ , ne (ne⁻ u″-n))) }

private opaque
  transKit : ∀ l → TransKit l
  transKit l = <ᵘ-rec TransKit (λ l rec → record { Trans l rec }) l

module _ {l} where open TransKit (transKit l) public
