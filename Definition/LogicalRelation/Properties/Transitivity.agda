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
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties.Conversion R
open import Definition.LogicalRelation.Properties.Symmetry R
open import Definition.LogicalRelation.Properties.Whnf R

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Sum

private
  variable
    m n ℓ             : Nat
    ∇                 : DCon (Term 0) m
    Γ                 : Con Term n
    A B Ty′ lhs′ rhs′ : Term _
    l                 : Universe-level

transEqTermNe : ∀ {t t′ t″ A}
              → ∇ » Γ ⊩neNf t  ≡ t′ ∷ A
              → ∇ » Γ ⊩neNf t′ ≡ t″ ∷ A
              → ∇ » Γ ⊩neNf t  ≡ t″ ∷ A
transEqTermNe (neNfₜ₌ neK neM k≡m) (neNfₜ₌ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ neK neM₁ (~-trans k≡m k≡m₁)

mutual
  transEqTermℕ : ∀ {n n′ n″}
               → ∇ » Γ ⊩ℕ n  ≡ n′  ∷ℕ
               → ∇ » Γ ⊩ℕ n′ ≡ n″ ∷ℕ
               → ∇ » Γ ⊩ℕ n  ≡ n″ ∷ℕ
  transEqTermℕ (ℕₜ₌ k _ d d′ t≡u prop) (ℕₜ₌ _ k″ d₁ d″ t≡u₁ prop₁) =
    let k₁Whnf = naturalWhnf (proj₁ (split prop₁))
        k′Whnf = naturalWhnf (proj₂ (split prop))
        k₁≡k′ = whrDet*Term (d₁ , k₁Whnf) (d′ , k′Whnf)
        prop′ = PE.subst (λ x → [Natural]-prop _ x _) k₁≡k′ prop₁
    in  ℕₜ₌ k k″ d d″
          (≅ₜ-trans t≡u (PE.subst (λ x → _ » _ ⊢ x ≅ _ ∷ _) k₁≡k′ t≡u₁))
          (transNatural-prop prop prop′)

  transNatural-prop : ∀ {k k′ k″}
                    → [Natural]-prop (∇ » Γ) k k′
                    → [Natural]-prop (∇ » Γ) k′ k″
                    → [Natural]-prop (∇ » Γ) k k″
  transNatural-prop (sucᵣ x) (sucᵣ x₁) = sucᵣ (transEqTermℕ x x₁)
  transNatural-prop (sucᵣ x) (ne (neNfₜ₌ () neM k≡m))
  transNatural-prop zeroᵣ prop₁ = prop₁
  transNatural-prop prop zeroᵣ = prop
  transNatural-prop (ne (neNfₜ₌ neK () k≡m)) (sucᵣ x₃)
  transNatural-prop (ne [k≡k′]) (ne [k′≡k″]) =
    ne (transEqTermNe [k≡k′] [k′≡k″])

-- Empty
transEmpty-prop : ∀ {k k′ k″}
  → [Empty]-prop (∇ » Γ) k k′
  → [Empty]-prop (∇ » Γ) k′ k″
  → [Empty]-prop (∇ » Γ) k k″
transEmpty-prop (ne [k≡k′]) (ne [k′≡k″]) =
  ne (transEqTermNe [k≡k′] [k′≡k″])

transEqTermEmpty : ∀ {n n′ n″}
  → ∇ » Γ ⊩Empty n  ≡ n′ ∷Empty
  → ∇ » Γ ⊩Empty n′ ≡ n″ ∷Empty
  → ∇ » Γ ⊩Empty n  ≡ n″ ∷Empty
transEqTermEmpty
  (Emptyₜ₌ k _ d d′ t≡u prop) (Emptyₜ₌ _ k″ d₁ d″ t≡u₁ prop₁) =
  let k₁Whnf = ne-whnf (proj₁ (esplit prop₁))
      k′Whnf = ne-whnf (proj₂ (esplit prop))
      k₁≡k′ = whrDet*Term (d₁ , k₁Whnf) (d′ , k′Whnf)
      prop′ = PE.subst (λ x → [Empty]-prop _ x _) k₁≡k′ prop₁
  in Emptyₜ₌ k k″ d d″
       (≅ₜ-trans t≡u (PE.subst (λ x → _ » _ ⊢ x ≅ _ ∷ _) k₁≡k′ t≡u₁))
       (transEmpty-prop prop prop′)

transUnit-prop : ∀ {k k′ k″}
  → [Unitʷ]-prop (∇ » Γ) l k k′
  → [Unitʷ]-prop (∇ » Γ) l k′ k″
  → [Unitʷ]-prop (∇ » Γ) l k k″
transUnit-prop starᵣ eq = eq
transUnit-prop (ne (neNfₜ₌ _ () _)) starᵣ
transUnit-prop (ne [k≡k′]) (ne [k′≡k″]) = ne (transEqTermNe [k≡k′] [k′≡k″])

transEqTermUnit : ∀ {s n n′ n″}
  → ∇ » Γ ⊩Unit⟨ l , s ⟩ n  ≡ n′ ∷Unit
  → ∇ » Γ ⊩Unit⟨ l , s ⟩ n′ ≡ n″ ∷Unit
  → ∇ » Γ ⊩Unit⟨ l , s ⟩ n  ≡ n″ ∷Unit
transEqTermUnit (Unitₜ₌ˢ ⊢t _ ok) (Unitₜ₌ˢ _ ⊢v _) = Unitₜ₌ˢ ⊢t ⊢v ok
transEqTermUnit
  (Unitₜ₌ʷ k _ d d′ k≡k′ prop ok) (Unitₜ₌ʷ _ k‴ d″ d‴ k″≡k‴ prop′ _) =
  let whK″ = proj₁ (usplit prop′)
      whK′ = proj₂ (usplit prop)
      k″≡k′ = whrDet*Term (d″ , whK″) (d′ , whK′)
      k′≡k‴ = PE.subst (λ x → _ » _ ⊢ x ≅ _ ∷ _) k″≡k′ k″≡k‴
      prop″ = PE.subst (λ x → [Unitʷ]-prop _ _ x _) k″≡k′ prop′
  in  Unitₜ₌ʷ k k‴ d d‴ (≅ₜ-trans k≡k′ k′≡k‴)
        (transUnit-prop prop prop″) ok
transEqTermUnit (Unitₜ₌ˢ _ _ (inj₂ ok)) (Unitₜ₌ʷ _ _ _ _ _ _ not-ok) =
  ⊥-elim (not-ok ok)
transEqTermUnit (Unitₜ₌ʷ _ _ _ _ _ _ not-ok) (Unitₜ₌ˢ _ _ (inj₂ ok)) =
  ⊥-elim (not-ok ok)
transEqTermUnit (Unitₜ₌ˢ _ _ (inj₁ ())) (Unitₜ₌ʷ _ _ _ _ _ _ _)
transEqTermUnit (Unitₜ₌ʷ _ _ _ _ _ _ _) (Unitₜ₌ˢ _ _ (inj₁ ()))


-- Helper function for transitivity of type equality using shape views.
transEqT : ∀ {m n} {∇ : DCon (Term 0) m} {Γ : Con Term n} {A B C l l′ l″}
           {[A] : ∇ » Γ ⊩⟨ l ⟩ A} {[B] : ∇ » Γ ⊩⟨ l′ ⟩ B} {[C] : ∇ » Γ ⊩⟨ l″ ⟩ C}
         → ShapeView₃ ∇ Γ l l′ l″ A B C [A] [B] [C]
         → ∇ » Γ ⊩⟨ l ⟩  A ≡ B / [A]
         → ∇ » Γ ⊩⟨ l′ ⟩ B ≡ C / [B]
         → ∇ » Γ ⊩⟨ l ⟩  A ≡ C / [A]

-- Transitivty of type equality.
transEq : ∀ {A B C l l′ l″}
          ([A] : ∇ » Γ ⊩⟨ l ⟩ A) ([B] : ∇ » Γ ⊩⟨ l′ ⟩ B) ([C] : ∇ » Γ ⊩⟨ l″ ⟩ C)
        → ∇ » Γ ⊩⟨ l ⟩  A ≡ B / [A]
        → ∇ » Γ ⊩⟨ l′ ⟩ B ≡ C / [B]
        → ∇ » Γ ⊩⟨ l ⟩  A ≡ C / [A]
transEq [A] [B] [C] A≡B B≡C =
  transEqT
    (combine (goodCases [A] [B] A≡B) (goodCases [B] [C] B≡C))
    A≡B B≡C

-- Transitivty of type equality with some propositonally equal types.
transEq′ : ∀ {A B B′ C C′ l l′ l″} → B PE.≡ B′ → C PE.≡ C′
         → ([A] : ∇ » Γ ⊩⟨ l ⟩ A) ([B] : ∇ » Γ ⊩⟨ l′ ⟩ B) ([C] : ∇ » Γ ⊩⟨ l″ ⟩ C)
         → ∇ » Γ ⊩⟨ l ⟩  A ≡ B′ / [A]
         → ∇ » Γ ⊩⟨ l′ ⟩ B ≡ C′ / [B]
         → ∇ » Γ ⊩⟨ l ⟩  A ≡ C  / [A]
transEq′ PE.refl PE.refl [A] [B] [C] A≡B B≡C =
  transEq [A] [B] [C] A≡B B≡C

-- Transitivty of term equality.
transEqTerm : {m n : Nat} → ∀ {∇ : DCon (Term 0) m} {Γ : Con Term n} {l A t u v}
              ([A] : ∇ » Γ ⊩⟨ l ⟩ A)
            → ∇ » Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
            → ∇ » Γ ⊩⟨ l ⟩ u ≡ v ∷ A / [A]
            → ∇ » Γ ⊩⟨ l ⟩ t ≡ v ∷ A / [A]

-- A variant of the constructor Id₌.
Id₌′ :
  {⊩A : ∇ » Γ ⊩′⟨ l ⟩Id A} →
  let open _⊩ₗId_ ⊩A in
  ∇ » Γ ⊢ B ⇒* Id Ty′ lhs′ rhs′ →
  ∇ » Γ ⊩⟨ l ⟩ Ty ≡ Ty′ / ⊩Ty →
  ∇ » Γ ⊩⟨ l ⟩ lhs ≡ lhs′ ∷ Ty / ⊩Ty →
  ∇ » Γ ⊩⟨ l ⟩ rhs ≡ rhs′ ∷ Ty / ⊩Ty →
  ∇ » Γ ⊩⟨ l ⟩ A ≡ B / Idᵣ ⊩A
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

transEqT (ℕᵥ D D′ D″) A≡B B≡C = B≡C
transEqT (Emptyᵥ D D′ D″) A≡B B≡C = B≡C
transEqT (Unitᵥ _ (Unitₜ B⇒*Unit₁ _) _) B⇒*Unit₂ C⇒*Unit =
  case Unit-PE-injectivity $
       whrDet* (B⇒*Unit₁ , Unitₙ) (B⇒*Unit₂ , Unitₙ) of λ {
    (_ , PE.refl) →
  C⇒*Unit }
transEqT
  (ne (ne _ D neK K≡K) (ne K₁ D₁ neK₁ _) (ne K₂ D₂ neK₂ _))
  (ne₌ M D′ neM K≡M) (ne₌ M₁ D″ neM₁ K≡M₁)
  rewrite whrDet* (D₁ , ne-whnf neK₁) (D′ , ne-whnf neM)
        | whrDet* (D₂ , ne-whnf neK₂) (D″ , ne-whnf neM₁) =
  ne₌ M₁ D″ neM₁ (≅-trans K≡M K≡M₁)
transEqT {n = n} {∇ = ∇} {Γ = Γ} {l = l} {l′ = l′} {l″ = l″}
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
    (λ ξ⊇ ρ → transEq ([F] ξ⊇ ρ) ([F]₁ ξ⊇ ρ) ([F]₂ ξ⊇ ρ) ([F≡F′] ξ⊇ ρ) ([F≡F′]₁ ξ⊇ ρ))
    (λ ξ⊇ ρ [a] →
       let [a′] = convTerm₁ ([F] ξ⊇ ρ) ([F]₁ ξ⊇ ρ) ([F≡F′] ξ⊇ ρ) [a]
           [a″] = convTerm₁ ([F]₁ ξ⊇ ρ) ([F]₂ ξ⊇ ρ) ([F≡F′]₁ ξ⊇ ρ) [a′]
       in  transEq ([G] ξ⊇ ρ [a]) ([G]₁ ξ⊇ ρ [a′]) ([G]₂ ξ⊇ ρ [a″])
             ([G≡G′] ξ⊇ ρ [a]) ([G≡G′]₁ ξ⊇ ρ [a′])) }}
transEqT (Uᵥ (Uᵣ l′ l< ⇒*U) (Uᵣ l′₁ l<₁ ⇒*U₁) (Uᵣ l′₂ l<₂ ⇒*U₂)) D D₁
  rewrite whrDet* (⇒*U₁ , Uₙ) (D , Uₙ)  | whrDet* (⇒*U₂ , Uₙ) (D₁ , Uₙ) =
  D₁
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
transEqT (embᵥ₁ ≤ᵘ-refl     A≡B≡C) = transEqT          A≡B≡C
transEqT (embᵥ₁ (≤ᵘ-step p) A≡B≡C) = transEqT (embᵥ₁ p A≡B≡C)
transEqT (embᵥ₂ ≤ᵘ-refl     A≡B≡C) = transEqT          A≡B≡C
transEqT (embᵥ₂ (≤ᵘ-step p) A≡B≡C) = transEqT (embᵥ₂ p A≡B≡C)
transEqT (embᵥ₃ ≤ᵘ-refl     A≡B≡C) = transEqT          A≡B≡C
transEqT (embᵥ₃ (≤ᵘ-step p) A≡B≡C) = transEqT (embᵥ₃ p A≡B≡C)

transEqTerm (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) B≡C C≡D =
  irrelevanceEqTerm (Uᵣ′ _ p A⇒*U) (Uᵣ′ _ (≤ᵘ-step p) A⇒*U)
    (transEqTerm (Uᵣ′ _ p A⇒*U)
       (irrelevanceEqTerm (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) (Uᵣ′ _ p A⇒*U) B≡C)
       (irrelevanceEqTerm (Uᵣ′ _ (≤ᵘ-step p) A⇒*U) (Uᵣ′ _ p A⇒*U) C≡D))
transEqTerm (Uᵣ′ l′ ≤ᵘ-refl D)
            (Uₜ₌ A B d d′ typeA typeB t≡u [t] [u] [t≡u])
            (Uₜ₌ A₁ B₁ d₁ d₁′ typeA₁ typeB₁ t≡u₁ [t]₁ [u]₁ [t≡u]₁) =
                case whrDet*Term (d₁ , typeWhnf typeA₁) (d′ , typeWhnf typeB) of λ where
                PE.refl →
                    Uₜ₌ A B₁ d  d₁′ typeA typeB₁ (≅ₜ-trans t≡u t≡u₁) [t] [u]₁ (transEq [t] [t]₁ [u]₁ [t≡u] [t≡u]₁)
transEqTerm (ℕᵣ D) [t≡u] [u≡v] = transEqTermℕ [t≡u] [u≡v]
transEqTerm (Emptyᵣ D) [t≡u] [u≡v] = transEqTermEmpty [t≡u] [u≡v]
transEqTerm (Unitᵣ D) [t≡u] [u≡v] = transEqTermUnit [t≡u] [u≡v]
transEqTerm
  {n} (ne′ _ D neK K≡K) (neₜ₌ k m d d′ (neNfₜ₌ neK₁ neM k≡m))
  (neₜ₌ k₁ m₁ d₁ d″ (neNfₜ₌ neK₂ neM₁ k≡m₁)) =
  let k₁≡m = whrDet*Term (d₁ , ne-whnf neK₂) (d′ , ne-whnf neM)
  in  neₜ₌ k m₁ d d″
           (neNfₜ₌ neK₁ neM₁
                   (~-trans k≡m (PE.subst (λ (x : Term n) → _ » _ ⊢ x ~ _ ∷ _) k₁≡m k≡m₁)))
transEqTerm (Bᵣ′ BΠ! F G D A≡A [F] [G] G-ext _)
            (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g])
            (Πₜ₌ f₁ g₁ d₁ d₁′ funcF₁ funcG₁ f≡g₁ [f]₁ [g]₁ [f≡g]₁)
            rewrite whrDet*Term (d′ , functionWhnf funcG)
                            (d₁ , functionWhnf funcF₁) =
  Πₜ₌ f g₁ d d₁′ funcF funcG₁ (≅ₜ-trans f≡g f≡g₁) [f] [g]₁
                (λ ξ⊇ ρ [a] → transEqTerm ([G] ξ⊇ ρ [a])
                                ([f≡g] ξ⊇ ρ [a]) ([f≡g]₁ ξ⊇ ρ [a]))
transEqTerm
  {n = n} {∇ = ∇} {Γ = Γ} (Bᵣ′ (BΣ 𝕤 p′ q) F G D A≡A [F] [G] G-ext _)
  (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u]
     ([fstp] , [fstr] , [fst≡] , [snd≡]))
  (Σₜ₌ p₁ r₁ d₁ d₁′ pProd₁ rProd₁ p≅r₁ [t]₁ [u]₁
     ([fstp]₁ , [fstr]₁ , [fst≡]₁ , [snd≡]₁)) =
  let p₁≡r = whrDet*Term (d₁ , productWhnf pProd₁)
               (d′ , productWhnf rProd)
      p≅r₁ = ≅ₜ-trans p≅r
               (PE.subst
                  (λ (x : Term n) → ∇ » Γ ⊢ x ≅ r₁ ∷ Σˢ p′ , q ▷ F ▹ G)
                  p₁≡r p≅r₁)
      [F]′ = [F] _ _
      [fst≡]′ = transEqTerm [F]′ [fst≡]
        (PE.subst
           (λ (x : Term n) →
              ∇ » Γ ⊩⟨ _ ⟩ fst _ x ≡ fst _ r₁ ∷ wk id F / [F]′)
           p₁≡r [fst≡]₁)
      [Gfstp≡Gfstp₁] = G-ext _ _ [fstp] [fstp]₁
        (PE.subst
           (λ (x : Term n) →
              ∇ » Γ ⊩⟨ _ ⟩ fst _ p ≡ fst _ x ∷ wk id F / [F]′)
           (PE.sym p₁≡r) [fst≡])
      [Gfstp] = [G] _ _ [fstp]
      [Gfstp₁] = [G] _ _ [fstp]₁
      [snd≡]₁′ = convEqTerm₂ [Gfstp] [Gfstp₁] [Gfstp≡Gfstp₁] [snd≡]₁
      [snd≡]′ = transEqTerm [Gfstp] [snd≡]
        (PE.subst
           (λ (x : Term n) →
              ∇ » Γ ⊩⟨ _ ⟩ snd _ x ≡ snd _ r₁ ∷ wk (lift id) G [ fst _ p ]₀ /
                [Gfstp])
           p₁≡r [snd≡]₁′)
  in  Σₜ₌ p r₁ d d₁′ pProd rProd₁ p≅r₁ [t] [u]₁ ([fstp] , [fstr]₁ , [fst≡]′ , [snd≡]′)
transEqTerm
  {n = n} {∇ = ∇} {Γ = Γ}
  (Bᵣ′ (BΣ 𝕨 p″ q) F G D A≡A [F] [G] G-ext _)
  (Σₜ₌ p r d d′ prodₙ prodₙ p≅r [t] [u]
     (PE.refl , PE.refl ,
      [p₁] , [r₁] , [p₂] , [r₂] , [p₁≡r₁] , [p₂≡r₂]))
  (Σₜ₌ p′ r′ d₁ d₁′ prodₙ prodₙ p′≅r′ [t]₁ [u]₁
     (PE.refl , PE.refl ,
      [p₁]′ , [r₁]′ , [p₂]′ , [r₂]′ , [p′₁≡r′₁] , [p′₂≡r′₂])) =
  let p′≡r = whrDet*Term (d₁ , prodₙ) (d′ , prodₙ)
      _ , _ , p′₁≡r₁ , p′₂≡r₂ = prod-PE-injectivity p′≡r
      p≅r′ = ≅ₜ-trans p≅r
                (PE.subst (λ x → ∇ » Γ ⊢ x ≅ r′ ∷ Σʷ p″ , q ▷ F ▹ G)
                   p′≡r p′≅r′)
      [F]′ = [F] _ _
      [p₁≡r′₁] = transEqTerm [F]′ [p₁≡r₁] (PE.subst (λ (x : Term n) → ∇ » Γ ⊩⟨ _ ⟩ x ≡ _ ∷ wk id F / [F]′) p′₁≡r₁ [p′₁≡r′₁])
      [Gp≡Gp₁] = G-ext _ _ [p₁] [p₁]′
                       (PE.subst (λ (x : Term n) → ∇ » Γ ⊩⟨ _ ⟩ _ ≡ x ∷ wk id F / [F]′)
                                 (PE.sym p′₁≡r₁) [p₁≡r₁])
      [Gp] = [G] _ _ [p₁]
      [Gp′] = [G] _ _ [p₁]′
      [r₂≡r′₂] = convEqTerm₂ [Gp] [Gp′] [Gp≡Gp₁]
                             (PE.subst (λ (x : Term n) → ∇ » Γ ⊩⟨ _ ⟩ x ≡ _ ∷ wk (lift id) G [ _ ]₀ / [Gp′])
                                       p′₂≡r₂ [p′₂≡r′₂])
      [p₂≡r′₂] = transEqTerm [Gp] [p₂≡r₂] [r₂≡r′₂]
  in  Σₜ₌ p r′ d d₁′ prodₙ prodₙ p≅r′ [t] [u]₁
        (PE.refl , PE.refl ,
         [p₁] , [r₁]′ , [p₂] , [r₂]′ , [p₁≡r′₁] , [p₂≡r′₂])
transEqTerm
  {n = n} {∇ = ∇} {Γ = Γ} (Bᵣ′ (BΣ 𝕨 p′ q) F G D A≡A [F] [G] G-ext _)
  (Σₜ₌ p r d d′ (ne x) (ne x₁) p≅r [t] [u] p~r)
  (Σₜ₌ p₁ r₁ d₁ d₁′ (ne x₂) (ne x₃) p≅r₁ [t]₁ [u]₁ p₁~r₁) =
  let p₁≡r = whrDet*Term (d₁ , ne-whnf x₂) (d′ , ne-whnf x₁)
      p≅r₁ = ≅ₜ-trans p≅r
                (PE.subst
                   (λ (x : Term n) → ∇ » Γ ⊢ x ≅ r₁ ∷ Σʷ p′ , q ▷ F ▹ G)
                   p₁≡r p≅r₁)
      p~r₁ = ~-trans p~r
               (PE.subst
                  (λ (x : Term n) → ∇ » Γ ⊢ x ~ _ ∷ Σʷ p′ , q ▷ F ▹ G)
                  p₁≡r p₁~r₁)
  in  Σₜ₌ p r₁ d d₁′ (ne x) (ne x₃) p≅r₁ [t] [u]₁ p~r₁
transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
            (Σₜ₌ p r d d′ prodₙ prodₙ p≅r [t] [u] prop)
            (Σₜ₌ p₁ r₁ d₁ d₁′ (ne x) (ne x₁) p≅r₁ [t]₁ [u]₁ prop₁) =
  ⊥-elim (prod≢ne x (whrDet*Term (d′ , prodₙ) (d₁ , ne-whnf x)))
transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
            (Σₜ₌ p r d d′ (ne x) (ne x₁) p≅r [t] [u] prop)
            (Σₜ₌ p₁ r₁ d₁ d₁′ prodₙ prodₙ p≅r₁ [t]₁ [u]₁ prop₁) =
  ⊥-elim (prod≢ne x₁ (whrDet*Term (d₁ , prodₙ) (d′ , ne-whnf x₁)))
transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
            (Σₜ₌ p r d d′ prodₙ (ne y) p≅r [t] [u] (lift ()))
            (Σₜ₌ p₁ r₁ d₁ d₁′ pProd₁ rProd₁ p≅r₁ [t]₁ [u]₁ prop₁)
transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
            (Σₜ₌ p r d d′ (ne x) prodₙ p≅r [t] [u] (lift ()))
            (Σₜ₌ p₁ r₁ d₁ d₁′ pProd₁ rProd₁ p≅r₁ [t]₁ [u]₁ prop₁)
transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
            (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] prop)
            (Σₜ₌ p₁ r₁ d₁ d₁′ prodₙ (ne y) p≅r₁ [t]₁ [u]₁ (lift ()))
transEqTerm (Bᵣ′ BΣʷ _ _ _ _ _ _ _ _)
            (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] prop)
            (Σₜ₌ p₁ r₁ d₁ d₁′ (ne x) prodₙ p≅r₁ [t]₁ [u]₁ (lift ()))
transEqTerm
  (Idᵣ ⊩A)
  t≡u@(_ , _ , _ , u⇒*u′ , _ , u′-id , _)
  u≡v@(_ , _ , u⇒*u″ , _ , u″-id , _) =
  case whrDet*Term
         (u⇒*u′ , identityWhnf u′-id)
         (u⇒*u″ , identityWhnf u″-id) of λ {
    PE.refl →
  let ⊩t , _      = ⊩Id≡∷⁻¹ ⊩A t≡u
      _  , ⊩v , _ = ⊩Id≡∷⁻¹ ⊩A u≡v
  in
  ⊩Id≡∷ ⊩t ⊩v
    (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
       (ne _ u′-n t′~u′) → case ⊩Id≡∷-view-inhabited ⊩A u≡v of λ where
         (ne _ _ u′~v′) → ~-trans t′~u′ u′~v′
         (rfl₌ _)       →
           ⊥-elim $ rfl≢ne u′-n $
           whrDet*Term (u⇒*u″ , rflₙ) (u⇒*u′ , ne-whnf u′-n)
       (rfl₌ _) → case ⊩Id≡∷-view-inhabited ⊩A u≡v of λ where
         (rfl₌ _)      → _
         (ne u″-n _ _) →
           ⊥-elim $ rfl≢ne u″-n $
           whrDet*Term (u⇒*u′ , rflₙ) (u⇒*u″ , ne-whnf u″-n)) }
transEqTerm (emb ≤ᵘ-refl     ⊩A) = transEqTerm ⊩A
transEqTerm (emb (≤ᵘ-step p) ⊩A) = transEqTerm (emb p ⊩A)
