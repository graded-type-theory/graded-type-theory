------------------------------------------------------------------------
-- Irrelevance lemmata for the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality


module Definition.LogicalRelation.Irrelevance
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (Wk; K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Kit R
open import Definition.LogicalRelation.ShapeView R

open import Tools.Function
open import Tools.Level
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    ∇ : DCon (Term 0) m
    Γ Γ′ : Con Term n
    A A′ B B′ C C′ : Term _
    l l′ : Universe-level

-- Irrelevance for propositionally equal types
irrelevance′ : ∀ {A A′ l}
             → A PE.≡ A′
             → ∇ » Γ ⊩⟨ l ⟩ A
             → ∇ » Γ ⊩⟨ l ⟩ A′
irrelevance′ PE.refl [A] = [A]

-- Irrelevance for propositionally equal types and contexts
irrelevanceΓ′ : ∀ {l A A′}
              → Γ PE.≡ Γ′
              → A PE.≡ A′
              → ∇ » Γ  ⊩⟨ l ⟩ A
              → ∇ » Γ′ ⊩⟨ l ⟩ A′
irrelevanceΓ′ PE.refl PE.refl [A] = [A]

mutual
  -- Irrelevance for type equality
  irrelevanceEq : ∀ {A B l l′} (p : ∇ » Γ ⊩⟨ l ⟩ A) (q : ∇ » Γ ⊩⟨ l′ ⟩ A)
                → ∇ » Γ ⊩⟨ l ⟩ A ≡ B / p → ∇ » Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEq p q A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B

  -- Irrelevance for type equality with propositionally equal first types
  irrelevanceEq′ : ∀ {A A′ B l l′} (eq : A PE.≡ A′)
                   (p : ∇ » Γ ⊩⟨ l ⟩ A) (q : ∇ » Γ ⊩⟨ l′ ⟩ A′)
                 → ∇ » Γ ⊩⟨ l ⟩ A ≡ B / p → ∇ » Γ ⊩⟨ l′ ⟩ A′ ≡ B / q
  irrelevanceEq′ PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal types
  irrelevanceEq″ : ∀ {A A′ B B′ l l′} (eqA : A PE.≡ A′) (eqB : B PE.≡ B′)
                    (p : ∇ » Γ ⊩⟨ l ⟩ A) (q : ∇ » Γ ⊩⟨ l′ ⟩ A′)
                  → ∇ » Γ ⊩⟨ l ⟩ A ≡ B / p → ∇ » Γ ⊩⟨ l′ ⟩ A′ ≡ B′ / q
  irrelevanceEq″ PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal second types
  irrelevanceEqR′ : ∀ {A B B′ l} (eqB : B PE.≡ B′) (p : ∇ » Γ ⊩⟨ l ⟩ A)
                  → ∇ » Γ ⊩⟨ l ⟩ A ≡ B / p → ∇ » Γ ⊩⟨ l ⟩ A ≡ B′ / p
  irrelevanceEqR′ PE.refl p A≡B = A≡B

  -- Irrelevance for type equality with propositionally equal types
  -- and contexts.
  irrelevanceEq‴ :
    A PE.≡ A′ → B PE.≡ B′ → Γ PE.≡ Γ′ →
    (⊩A : ∇ » Γ ⊩⟨ l ⟩ A) (⊩A′ : ∇ » Γ′ ⊩⟨ l′ ⟩ A′) →
    ∇ » Γ ⊩⟨ l ⟩ A ≡ B / ⊩A → ∇ » Γ′ ⊩⟨ l′ ⟩ A′ ≡ B′ / ⊩A′
  irrelevanceEq‴ PE.refl PE.refl PE.refl = irrelevanceEq

  -- Helper for irrelevance of type equality using shape view
  irrelevanceEqT : ∀ {A B l l′} {p : ∇ » Γ ⊩⟨ l ⟩ A} {q : ∇ » Γ ⊩⟨ l′ ⟩ A}
                       → ShapeView ∇ Γ l l′ A A p q
                       → ∇ » Γ ⊩⟨ l ⟩ A ≡ B / p → ∇ » Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEqT (ℕᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Unitᵥ (Unitₜ A⇒*Unit₁ _) (Unitₜ A⇒*Unit₂ _)) A≡B =
    case Unit-PE-injectivity $
         whrDet* (A⇒*Unit₁ , Unitₙ) (A⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    A≡B }
  irrelevanceEqT
    (ne (ne _ _ D neK _) (ne _ K₁ D₁ neK₁ K≡K₁)) (ne₌ inc M D′ neM K≡M)
    rewrite whrDet* (D , ne neK) (D₁ , ne neK₁) =
    ne₌ inc M D′ neM K≡M
  irrelevanceEqT
    {∇ = ∇} {Γ = Γ}
    (Bᵥ W (Bᵣ F G D A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠFG≡ΠF₁G₁       = whrDet* (D , ⟦ W ⟧ₙ) (D₁ , ⟦ W ⟧ₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity W W ΠFG≡ΠF₁G₁
    in  B₌ F′ G′ D′
           (PE.subst (λ x → ∇ » Γ ⊢ x ≅ ⟦ W ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B)
           (λ [ξ] {_} {ρ} [ρ] → irrelevanceEq′ (PE.cong (wk ρ) F≡F₁)
                              ([F] [ξ] [ρ]) ([F]₁ [ξ] [ρ]) ([F≡F′] [ξ] [ρ]))
           (λ [ξ] {_} {ρ} [ρ] [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                         ([F]₁ [ξ] [ρ]) ([F] [ξ] [ρ]) [a]₁
              in  irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
                    ([G] [ξ] [ρ] [a]) ([G]₁ [ξ] [ρ] [a]₁) ([G≡G′] [ξ] [ρ] [a]))
  irrelevanceEqT (Uᵥ (Uᵣ _ _ D1) (Uᵣ _ _ D2)) A≡B
    rewrite whrDet* (D1 , Uₙ) (D2 , Uₙ) = A≡B
  irrelevanceEqT (Idᵥ ⊩A@record{} ⊩A′) A≡B =
    case whrDet* (_»_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_»_⊩ₗId_.⇒*Id ⊩A′ , Idₙ) of λ {
      PE.refl →
    record
      { ⇒*Id′    = ⇒*Id′
      ; Ty≡Ty′   = irrelevanceEq (_»_⊩ₗId_.⊩Ty ⊩A) (_»_⊩ₗId_.⊩Ty ⊩A′) Ty≡Ty′
      ; lhs≡lhs′ =
          irrelevanceEqTerm (_»_⊩ₗId_.⊩Ty ⊩A) (_»_⊩ₗId_.⊩Ty ⊩A′) lhs≡lhs′
      ; rhs≡rhs′ =
          irrelevanceEqTerm (_»_⊩ₗId_.⊩Ty ⊩A) (_»_⊩ₗId_.⊩Ty ⊩A′) rhs≡rhs′
      ; lhs≡rhs→lhs′≡rhs′ =
          irrelevanceEqTerm (_»_⊩ₗId_.⊩Ty ⊩A) (_»_⊩ₗId_.⊩Ty ⊩A′) ∘→
          lhs≡rhs→lhs′≡rhs′ ∘→
          irrelevanceEqTerm (_»_⊩ₗId_.⊩Ty ⊩A′) (_»_⊩ₗId_.⊩Ty ⊩A)
      ; lhs′≡rhs′→lhs≡rhs =
          irrelevanceEqTerm (_»_⊩ₗId_.⊩Ty ⊩A) (_»_⊩ₗId_.⊩Ty ⊩A′) ∘→
          lhs′≡rhs′→lhs≡rhs ∘→
          irrelevanceEqTerm (_»_⊩ₗId_.⊩Ty ⊩A′) (_»_⊩ₗId_.⊩Ty ⊩A)
      } }
    where
    open _»_⊩ₗId_≡_/_ A≡B
  irrelevanceEqT (embᵥ₁ ≤ᵘ-refl     A≡A) = irrelevanceEqT          A≡A
  irrelevanceEqT (embᵥ₁ (≤ᵘ-step p) A≡A) = irrelevanceEqT (embᵥ₁ p A≡A)
  irrelevanceEqT (embᵥ₂ ≤ᵘ-refl     A≡A) = irrelevanceEqT          A≡A
  irrelevanceEqT (embᵥ₂ (≤ᵘ-step p) A≡A) = irrelevanceEqT (embᵥ₂ p A≡A)

--------------------------------------------------------------------------------

  -- Irrelevance for terms
  irrelevanceTerm : ∀ {A t l l′} (p : ∇ » Γ ⊩⟨ l ⟩ A) (q : ∇ » Γ ⊩⟨ l′ ⟩ A)
                  → ∇ » Γ ⊩⟨ l ⟩ t ∷ A / p → ∇ » Γ ⊩⟨ l′ ⟩ t ∷ A / q
  irrelevanceTerm p q t = irrelevanceTermT (goodCasesRefl p q) t

  -- Irrelevance for terms with propositionally equal types
  irrelevanceTerm′ : ∀ {A A′ t l l′} (eq : A PE.≡ A′)
                     (p : ∇ » Γ ⊩⟨ l ⟩ A) (q : ∇ » Γ ⊩⟨ l′ ⟩ A′)
                   → ∇ » Γ ⊩⟨ l ⟩ t ∷ A / p → ∇ » Γ ⊩⟨ l′ ⟩ t ∷ A′ / q
  irrelevanceTerm′ PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types and terms
  irrelevanceTerm″ : ∀ {A A′ t t′ l l′}
                      (eqA : A PE.≡ A′) (eqt : t PE.≡ t′)
                      (p : ∇ » Γ ⊩⟨ l ⟩ A) (q : ∇ » Γ ⊩⟨ l′ ⟩ A′)
                    → ∇ » Γ ⊩⟨ l ⟩ t ∷ A / p → ∇ » Γ ⊩⟨ l′ ⟩ t′ ∷ A′ / q
  irrelevanceTerm″ PE.refl PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types, terms and contexts
  irrelevanceTermΓ″ : ∀ {l l′ A A′ t t′}
                     → Γ PE.≡ Γ′
                     → A PE.≡ A′
                     → t PE.≡ t′
                     → ([A]  : ∇ » Γ  ⊩⟨ l  ⟩ A)
                       ([A′] : ∇ » Γ′ ⊩⟨ l′ ⟩ A′)
                     → ∇ » Γ  ⊩⟨ l  ⟩ t ∷ A  / [A]
                     → ∇ » Γ′ ⊩⟨ l′ ⟩ t′ ∷ A′ / [A′]
  irrelevanceTermΓ″ PE.refl PE.refl PE.refl [A] [A′] [t] = irrelevanceTerm [A] [A′] [t]

  -- Helper for irrelevance of terms using shape view
  irrelevanceTermT : ∀ {A t l l′} {p : ∇ » Γ ⊩⟨ l ⟩ A} {q : ∇ » Γ ⊩⟨ l′ ⟩ A}
                         → ShapeView ∇ Γ l l′ A A p q
                         → ∇ » Γ ⊩⟨ l ⟩ t ∷ A / p → ∇ » Γ ⊩⟨ l′ ⟩ t ∷ A / q
  irrelevanceTermT (ℕᵥ D D′) t = t
  irrelevanceTermT (Emptyᵥ D D′) t = t
  irrelevanceTermT (Unitᵥ (Unitₜ A⇒*Unit₁ _) (Unitₜ A⇒*Unit₂ _)) ⊩t =
    case Unit-PE-injectivity $
         whrDet* (A⇒*Unit₁ , Unitₙ) (A⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    ⊩t }
  irrelevanceTermT
    (ne (ne _ _ D neK K≡K) (ne _ K₁ D₁ neK₁ K≡K₁)) (neₜ k d nf)
    with whrDet* (D₁ , ne neK₁) (D , ne neK)
  … | PE.refl = neₜ k d nf
  irrelevanceTermT
    {∇ = ∇} {Γ = Γ} {t = t}
    (Bᵥ BΠ! (Bᵣ F G D A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (Πₜ f d funcF f≡f [f] [f]₁) =
    case whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ) of λ
      ΠFG≡ΠF₁G₁ →
    case B-PE-injectivity BΠ! BΠ! ΠFG≡ΠF₁G₁ of λ
      (F≡F₁ , G≡G₁ , _) →
        Πₜ f (PE.subst (λ x → ∇ » Γ ⊢ t ⇒* f ∷ x) ΠFG≡ΠF₁G₁ d) funcF
           (PE.subst (λ x → ∇ » Γ ⊢≅ f ∷ x) ΠFG≡ΠF₁G₁ f≡f)
           (λ [ξ] {_} {ρ} {Δ} {a} {b} [ρ] [a]₁ [b]₁ [a≡b]₁ →
             let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                        ([F]₁ [ξ] [ρ]) ([F] [ξ] [ρ]) [a]₁
                 [b] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                        ([F]₁ [ξ] [ρ]) ([F] [ξ] [ρ]) [b]₁
                 [a≡b] = irrelevanceEqTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                            ([F]₁ [ξ] [ρ]) ([F] [ξ] [ρ]) [a≡b]₁
             in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                    ([G] [ξ] [ρ] [a]) ([G]₁ [ξ] [ρ] [a]₁)
                                    ([f] [ξ] [ρ] [a] [b] [a≡b]))
           λ [ξ] {_} {ρ} {Δ} {a} [ρ] [a]₁ →
             let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                        ([F]₁ [ξ] [ρ]) ([F] [ξ] [ρ]) [a]₁
             in  irrelevanceTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                  ([G] [ξ] [ρ] [a]) ([G]₁ [ξ] [ρ] [a]₁)
                                  ([f]₁ [ξ] [ρ] [a])
  irrelevanceTermT
    {∇ = ∇} {Γ = Γ} {t = t}
    (Bᵥ BΣˢ (Bᵣ F G D A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (Σₜ p d p≅p pProd ([fstt] , [sndt])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [fstt]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁) ([F] _ _)
                                 ([F]₁ _ _) [fstt]
        [sndt]′ = irrelevanceTerm′ (PE.cong (λ x → wk (lift id) x [ _ ]) G≡G₁)
                                 ([G] _ _ [fstt]) ([G]₁ _ _ [fstt]′) [sndt]
    in  Σₜ p (PE.subst (λ x → ∇ » Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
           (PE.subst (λ x →  ∇ » Γ ⊢≅ p ∷ x) ΣFG≡ΣF₁G₁ p≅p) pProd
           ([fstt]′ , [sndt]′)
  irrelevanceTermT
    {∇ = ∇} {Γ = Γ} {t = t}
    (Bᵥ BΣʷ (Bᵣ F G D A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (Σₜ p d p≅p prodₙ (PE.refl , [t₁] , [t₂] , PE.refl)) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [t₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁) ([F] _ _) ([F]₁ _ _)
                  [t₁]
        [t₂]′ = irrelevanceTerm′ (PE.cong (λ x → wk (lift id) x [ _ ]) G≡G₁)
                                 ([G] _ _ [t₁]) ([G]₁ _ _ [t₁]′) [t₂]
    in  Σₜ p (PE.subst (λ x → ∇ » Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
          (PE.subst (λ x →  ∇ » Γ ⊢≅ p ∷ x) ΣFG≡ΣF₁G₁ p≅p) prodₙ
          (PE.refl , [t₁]′ , [t₂]′ , PE.refl)
  irrelevanceTermT
    {∇ = ∇} {Γ = Γ} {t = t}
    (Bᵥ BΣʷ (Bᵣ F G D A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (Σₜ p d p≅p (ne x) (inc , p~p)) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
    in  Σₜ p (PE.subst (λ x → ∇ » Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
           (PE.subst (λ x →  ∇ » Γ ⊢≅ p ∷ x) ΣFG≡ΣF₁G₁ p≅p) (ne x)
           (inc , PE.subst (λ x → ∇ » Γ ⊢~ p ∷ x) ΣFG≡ΣF₁G₁ p~p)
  irrelevanceTermT (Uᵥ (Uᵣ _ l<1 ⇒*U1) (Uᵣ _ l<2 ⇒*U2)) (Uₜ A d typeA A≡A [t]) with whrDet* (⇒*U1 , Uₙ) (⇒*U2 ,  Uₙ)
  irrelevanceTermT (Uᵥ (Uᵣ _ l<1 _) (Uᵣ _ l<2 _)) (Uₜ A d typeA A≡A [t])
    | PE.refl =
    Uₜ A d typeA A≡A (irrelevance-⊩< l<1 l<2 [t])

  irrelevanceTermT (Idᵥ ⊩A@record{} ⊩A′) ⊩t@(_ , t⇒*u , _) =
    case whrDet* (_»_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_»_⊩ₗId_.⇒*Id ⊩A′ , Idₙ) of λ {
      PE.refl →
      _
    , t⇒*u
    , (case ⊩Id∷-view-inhabited ⊩t of λ where
         (ne inc u-n u~u) → ne u-n , inc , u~u
         (rflᵣ lhs≡rhs)   →
             rflₙ
           , irrelevanceEqTerm
               (_»_⊩ₗId_.⊩Ty ⊩A) (_»_⊩ₗId_.⊩Ty ⊩A′) lhs≡rhs) }
  irrelevanceTermT (embᵥ₁ ≤ᵘ-refl     A≡A) = irrelevanceTermT          A≡A
  irrelevanceTermT (embᵥ₁ (≤ᵘ-step p) A≡A) = irrelevanceTermT (embᵥ₁ p A≡A)
  irrelevanceTermT (embᵥ₂ ≤ᵘ-refl     A≡A) = irrelevanceTermT          A≡A
  irrelevanceTermT (embᵥ₂ (≤ᵘ-step p) A≡A) = irrelevanceTermT (embᵥ₂ p A≡A)

--------------------------------------------------------------------------------

  -- Irrelevance for term equality
  irrelevanceEqTerm : ∀ {A t u l l′} (p : ∇ » Γ ⊩⟨ l ⟩ A) (q : ∇ » Γ ⊩⟨ l′ ⟩ A)
                    → ∇ » Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → ∇ » Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTerm p q t≡u = irrelevanceEqTermT (goodCasesRefl p q) t≡u

  -- Irrelevance for term equality with propositionally equal types
  irrelevanceEqTerm′ : ∀ {A A′ t u l l′} (eq : A PE.≡ A′)
                       (p : ∇ » Γ ⊩⟨ l ⟩ A) (q : ∇ » Γ ⊩⟨ l′ ⟩ A′)
                     → ∇ » Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → ∇ » Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A′ / q
  irrelevanceEqTerm′ PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Irrelevance for term equality with propositionally equal types and terms
  irrelevanceEqTerm″ : ∀ {A A′ t t′ u u′ l l′}
                        (eqt : t PE.≡ t′) (equ : u PE.≡ u′) (eqA : A PE.≡ A′)
                        (p : ∇ » Γ ⊩⟨ l ⟩ A) (q : ∇ » Γ ⊩⟨ l′ ⟩ A′)
                      → ∇ » Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → ∇ » Γ ⊩⟨ l′ ⟩ t′ ≡ u′ ∷ A′ / q
  irrelevanceEqTerm″ PE.refl PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Helper for irrelevance of term equality using shape view
  irrelevanceEqTermT : ∀ {A t u} {l l′} {p : ∇ » Γ ⊩⟨ l ⟩ A} {q : ∇ » Γ ⊩⟨ l′ ⟩ A}
                           → ShapeView ∇ Γ l l′ A A p q
                           → ∇ » Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → ∇ » Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTermT (ℕᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Emptyᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Unitᵥ (Unitₜ A⇒*Unit₁ _) (Unitₜ A⇒*Unit₂ _)) t≡u =
    case Unit-PE-injectivity $
         whrDet* (A⇒*Unit₁ , Unitₙ) (A⇒*Unit₂ , Unitₙ) of λ {
      (_ , PE.refl) →
    t≡u }
  irrelevanceEqTermT
    (ne (ne _ _ D neK K≡K) (ne _ K₁ D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
    with whrDet* (D₁ , ne neK₁) (D , ne neK)
  … | PE.refl = neₜ₌ k m d d′ nf
  irrelevanceEqTermT
    {∇ = ∇} {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΠ! x@(Bᵣ F G D A≡A [F] [G] G-ext _)
       x₁@(Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
    case irrelevanceTerm (Bᵣ BΠ! x) (Bᵣ BΠ! x₁) [f] of λ [f]′ →
    case irrelevanceTerm (Bᵣ BΠ! x) (Bᵣ BΠ! x₁) [g] of λ [g]′ →
    case B-PE-injectivity BΠ! BΠ!
           (whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)) of λ where
      (PE.refl , PE.refl , _) →
        Πₜ₌ f g d d′ funcF funcG f≡g [f]′ [g]′
        λ [ξ] {_} {ρ} {Δ} {a} [ρ] [a]₁ →
          let [a] = irrelevanceTerm ([F]₁ [ξ] [ρ]) ([F] [ξ] [ρ]) [a]₁ in
          irrelevanceEqTerm ([G] [ξ] [ρ] [a]) ([G]₁ [ξ] [ρ] [a]₁)
            ([f≡g] [ξ] [ρ] [a])
  irrelevanceEqTermT
    {∇ = ∇} {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΣˢ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u]
       ([fstp] , [fstr] , [fst≡] , [snd≡])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [A]             = Bᵣ′ BΣ! F G D A≡A [F] [G] G-ext ok
        [A]₁            = Bᵣ′ BΣ! F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁
        [fstp]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _ _) ([F]₁ _ _) [fstp]
        [fstr]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _ _) ([F]₁ _ _) [fstr]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _ _) ([F]₁ _ _) [fst≡]
        [snd≡]′ = irrelevanceEqTerm′
                    (PE.cong (λ x → wk (lift id) x [ fst _ p ]₀) G≡G₁)
                    ([G] _ _ [fstp]) ([G]₁ _ _ [fstp]′) [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → ∇ » Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → ∇ » Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) pProd rProd
            (PE.subst (λ x → ∇ » Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (irrelevanceTerm [A] [A]₁ [t]) (irrelevanceTerm [A] [A]₁ [u])
            ([fstp]′ , [fstr]′ , [fst≡]′ ,  [snd≡]′)
  irrelevanceEqTermT
    {∇ = ∇} {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΣʷ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ prodₙ prodₙ p≅r [t] [u]
       (PE.refl , PE.refl ,
        [p₁] , [r₁] , [p₂] , [r₂] , [fst≡] , [snd≡])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [A]             = Bᵣ′ BΣ! F G D A≡A [F] [G] G-ext ok
        [A]₁            = Bᵣ′ BΣ! F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁
                            ok₁
        [p₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                  ([F] _ _) ([F]₁ _ _) [p₁]
        [r₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                  ([F] _ _) ([F]₁ _ _) [r₁]
        [p₂]′ = irrelevanceTerm′ (PE.cong (λ G → wk (lift id) G [ _ ]₀) G≡G₁)
                  ([G] _ _ [p₁]) ([G]₁ _ _ [p₁]′) [p₂]
        [r₂]′ = irrelevanceTerm′ (PE.cong (λ G → wk (lift id) G [ _ ]₀) G≡G₁)
                  ([G] _ _ [r₁]) ([G]₁ _ _ [r₁]′) [r₂]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _ _) ([F]₁ _ _) [fst≡]
        [snd≡]′ = irrelevanceEqTerm′ (PE.cong (λ x → wk (lift id) x [ _ ]₀) G≡G₁)
                    ([G] _ _ [p₁]) ([G]₁ _ _ [p₁]′) [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → ∇ » Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → ∇ » Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) prodₙ prodₙ
            (PE.subst (λ x → ∇ » Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (irrelevanceTerm [A] [A]₁ [t]) (irrelevanceTerm [A] [A]₁ [u])
            (PE.refl , PE.refl ,
             [p₁]′ , [r₁]′ , [p₂]′ , [r₂]′ , [fst≡]′ ,  [snd≡]′)
  irrelevanceEqTermT
    {∇ = ∇} {Γ = Γ} {t = t} {u = u}
    (Bᵥ BΣʷ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ (ne x) (ne y) p≅r [t] [u] (inc , p~r)) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [A]             = Bᵣ′ BΣ! F G D A≡A [F] [G] G-ext ok
        [A]₁            = Bᵣ′ BΣ! F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁
                            ok₁
        p~r′ = PE.subst (λ x → ∇ » Γ ⊢ p ~ r ∷ x) ΣFG≡ΣF₁G₁ p~r
    in  Σₜ₌ p r (PE.subst (λ x → ∇ » Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → ∇ » Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) (ne x) (ne y)
            (PE.subst (λ x → ∇ » Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (irrelevanceTerm [A] [A]₁ [t]) (irrelevanceTerm [A] [A]₁ [u])
            (inc , p~r′)
  irrelevanceEqTermT
    (Bᵥ BΣʷ record{} _) (Σₜ₌ _ _ _ _ prodₙ (ne _) _ _ _ (lift ()))
  irrelevanceEqTermT
    (Bᵥ BΣʷ record{} _) (Σₜ₌ _ _ _ _ (ne _) prodₙ _ _ _ (lift ()))
  irrelevanceEqTermT (Uᵥ (Uᵣ _ l<1 ⇒*U1) (Uᵣ _ l<2 ⇒*U2))
    (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u])
    with whrDet* (⇒*U1 , Uₙ) (⇒*U2 ,  Uₙ)
  irrelevanceEqTermT (Uᵥ (Uᵣ _ l<1 ⇒*U1) (Uᵣ _ l<2 ⇒*U2))
    (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) | PE.refl =
    Uₜ₌ A B d d′ typeA typeB A≡B _ (irrelevance-⊩< l<1 l<2 [u])
      (irrelevance-⊩<≡ l<1 l<2 [t≡u])
  irrelevanceEqTermT
    (Idᵥ ⊩A@record{} ⊩A′) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
    case whrDet* (_»_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_»_⊩ₗId_.⇒*Id ⊩A′ , Idₙ) of λ {
      PE.refl →
      _ , _ , t⇒*t′ , u⇒*u′
    , (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
         (ne inc t′-n u′-n t′~u′) →
           ne t′-n , ne u′-n , inc , t′~u′
         (rfl₌ lhs≡rhs) →
             rflₙ , rflₙ
           , irrelevanceEqTerm
               (_»_⊩ₗId_.⊩Ty ⊩A) (_»_⊩ₗId_.⊩Ty ⊩A′) lhs≡rhs) }
  irrelevanceEqTermT (embᵥ₁ ≤ᵘ-refl     A≡A) = irrelevanceEqTermT          A≡A
  irrelevanceEqTermT (embᵥ₁ (≤ᵘ-step p) A≡A) = irrelevanceEqTermT (embᵥ₁ p A≡A)
  irrelevanceEqTermT (embᵥ₂ ≤ᵘ-refl     A≡A) = irrelevanceEqTermT          A≡A
  irrelevanceEqTermT (embᵥ₂ (≤ᵘ-step p) A≡A) = irrelevanceEqTermT (embᵥ₂ p A≡A)
