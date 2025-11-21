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
open import Definition.Untyped.Neutral.Atomic M type-variant
open import Definition.Untyped.Properties M
open import Definition.Untyped.Whnf M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Escape R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Kit R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Primitive R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Reflexivity R ⦃ eqrel ⦄
open import Definition.LogicalRelation.Properties.Whnf R ⦃ eqrel ⦄
open import Definition.LogicalRelation.ShapeView R ⦃ eqrel ⦄

open import Tools.Function
open import Tools.Level hiding (_⊔_)
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Relation

private
  variable
    m n : Nat
    Γ Γ′ : Cons m n
    A A′ B B′ C C′ t u : Term _
    l l′ : Universe-level

-- Irrelevance for propositionally equal types
irrelevance′ : ∀ {A A′ l}
             → A PE.≡ A′
             → Γ ⊩⟨ l ⟩ A
             → Γ ⊩⟨ l ⟩ A′
irrelevance′ PE.refl [A] = [A]

mutual
  -- Irrelevance for type equality
  irrelevanceEq : ∀ {A B l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEq p q A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B

  -- Irrelevance for type equality with propositionally equal first types
  irrelevanceEq′ : ∀ {A A′ B l l′} (eq : A PE.≡ A′)
                   (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                 → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B / q
  irrelevanceEq′ PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal types
  irrelevanceEq″ : ∀ {A A′ B B′ l l′} (eqA : A PE.≡ A′) (eqB : B PE.≡ B′)
                    (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                  → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B′ / q
  irrelevanceEq″ PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal second types
  irrelevanceEqR′ : ∀ {A B B′ l} (eqB : B PE.≡ B′) (p : Γ ⊩⟨ l ⟩ A)
                  → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l ⟩ A ≡ B′ / p
  irrelevanceEqR′ PE.refl p A≡B = A≡B

  -- Helper for irrelevance of type equality using shape view
  irrelevanceEqT : ∀ {A B l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                       → ShapeView Γ l l′ A A p q
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEqT (Levelᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Liftᵥ (Liftᵣ D1 _ _) (Liftᵣ D2 _ _)) [A≡B]
    = case whrDet* (D1 , Liftₙ) (D2 , Liftₙ) of λ { PE.refl →
      Lift₌ ⇒*Lift′ k≡k′ (irrelevanceEq _ _ F≡F′) }
    where open _⊩ₗLift_≡_/_ [A≡B]
  irrelevanceEqT (ℕᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Unitᵥ (Unitᵣ A⇒*Unit₁ _) (Unitᵣ A⇒*Unit₂ _)) (Unit₌ D) =
    Unit₌ D
  irrelevanceEqT
    (ne (ne _ D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
    rewrite whrDet* (D , ne-whnf neK) (D₁ , ne-whnf neK₁) =
    ne₌ M D′ neM K≡M
  irrelevanceEqT
    {Γ}
    (Bᵥ W (Bᵣ F G D A≡A [F] [G] G-ext _)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠFG≡ΠF₁G₁       = whrDet* (D , ⟦ W ⟧ₙ) (D₁ , ⟦ W ⟧ₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity W W ΠFG≡ΠF₁G₁
    in  B₌ F′ G′ D′
           (PE.subst (λ x → Γ ⊢ x ≅ ⟦ W ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B)
           (λ [ξ] {_} {ρ} [ρ] → irrelevanceEq′ (PE.cong (wk ρ) F≡F₁)
                              ([F] [ξ] [ρ]) ([F]₁ [ξ] [ρ]) ([F≡F′] [ξ] [ρ]))
           (λ [ξ] {_} {ρ} [ρ] [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                         ([F]₁ [ξ] [ρ]) ([F] [ξ] [ρ]) [a]₁
              in  irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
                    ([G] [ξ] [ρ] [a]) ([G]₁ [ξ] [ρ] [a]₁)
                    ([G≡G′] [ξ] [ρ] [a]))
  irrelevanceEqT (Uᵥ (Uᵣ _ _ _ D1) (Uᵣ _ _ _ D2)) A≡B
    = case whrDet* (D1 , Uₙ) (D2 , Uₙ) of λ { PE.refl →
        U₌ k′ ⇒*U′ k≡k′ }
    where
    open _⊩₁U≡_/_ A≡B
  irrelevanceEqT (Idᵥ ⊩A@record{} ⊩A′) A≡B =
    case whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_⊩ₗId_.⇒*Id ⊩A′ , Idₙ) of λ {
      PE.refl →
    record
      { ⇒*Id′    = ⇒*Id′
      ; Ty≡Ty′   = irrelevanceEq (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) Ty≡Ty′
      ; lhs≡lhs′ =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) lhs≡lhs′
      ; rhs≡rhs′ =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) rhs≡rhs′
      ; lhs≡rhs→lhs′≡rhs′ =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) ∘→
          lhs≡rhs→lhs′≡rhs′ ∘→
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A′) (_⊩ₗId_.⊩Ty ⊩A)
      ; lhs′≡rhs′→lhs≡rhs =
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) ∘→
          lhs′≡rhs′→lhs≡rhs ∘→
          irrelevanceEqTerm (_⊩ₗId_.⊩Ty ⊩A′) (_⊩ₗId_.⊩Ty ⊩A)
      } }
    where
    open _⊩ₗId_≡_/_ A≡B

--------------------------------------------------------------------------------

  -- Irrelevance for terms
  irrelevanceTerm : ∀ {A t l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                  → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A / q
  irrelevanceTerm p q t = irrelevanceEqTerm p q t

  -- Irrelevance for terms with propositionally equal types
  irrelevanceTerm′ : ∀ {A A′ t l l′} (eq : A PE.≡ A′)
                     (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                   → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A′ / q
  irrelevanceTerm′ PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types and terms
  irrelevanceTerm″ : ∀ {A A′ t t′ l l′}
                      (eqA : A PE.≡ A′) (eqt : t PE.≡ t′)
                      (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                    → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t′ ∷ A′ / q
  irrelevanceTerm″ PE.refl PE.refl p q t = irrelevanceTerm p q t

--------------------------------------------------------------------------------

  -- Irrelevance for term equality
  irrelevanceEqTerm : ∀ {A t u l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                    → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTerm p q t≡u = irrelevanceEqTermT (goodCasesRefl p q) t≡u

  -- Irrelevance for term equality with propositionally equal types
  irrelevanceEqTerm′ : ∀ {A A′ t u l l′} (eq : A PE.≡ A′)
                       (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                     → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A′ / q
  irrelevanceEqTerm′ PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Irrelevance for term equality with propositionally equal types and terms
  irrelevanceEqTerm″ : ∀ {A A′ t t′ u u′ l l′}
                        (eqt : t PE.≡ t′) (equ : u PE.≡ u′) (eqA : A PE.≡ A′)
                        (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A′)
                      → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t′ ≡ u′ ∷ A′ / q
  irrelevanceEqTerm″ PE.refl PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Helper for irrelevance of term equality using shape view
  irrelevanceEqTermT : ∀ {A t u} {l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                           → ShapeView Γ l l′ A A p q
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / q
  irrelevanceEqTermT (Levelᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT
    (Liftᵥ (Liftᵣ D1 _ [F]) (Liftᵣ D2 _ [F]′))
    (Liftₜ₌ _ _ d1 d2 t≡u) =
    case Lift-PE-injectivity (whrDet* (D1 , Liftₙ) (D2 , Liftₙ)) of λ {
      (PE.refl , PE.refl) →
    Liftₜ₌ _ _ d1 d2 (irrelevanceEqTerm [F] [F]′ t≡u) }
  irrelevanceEqTermT (ℕᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Emptyᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Unitᵥ (Unitᵣ A⇒*Unit₁ _) (Unitᵣ A⇒*Unit₂ _)) t≡u =
    t≡u
  irrelevanceEqTermT
    (ne (ne _ D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ prop)
    with whrDet* (D₁ , ne-whnf neK₁) (D , ne-whnf neK)
  … | PE.refl = neₜ₌ k m d d′ prop
  irrelevanceEqTermT
    {Γ} {t} {u}
    (Bᵥ BΠ! x@(Bᵣ F G D A≡A [F] [G] G-ext _)
       x₁@(Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ _))
    (Πₜ₌ f g d d′ funcF funcG f≡g [f≡g]) =
    case B-PE-injectivity BΠ! BΠ!
           (whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)) of λ where
      (PE.refl , PE.refl , _) →
        Πₜ₌ f g d d′ funcF funcG f≡g
        λ [ξ] [ρ] ⊩v ⊩w v≡w →
          let ⊩v′ = irrelevanceTerm ([F]₁ [ξ] [ρ]) ([F] [ξ] [ρ]) ⊩v in
          irrelevanceEqTerm ([G] [ξ] [ρ] ⊩v′) ([G]₁ [ξ] [ρ] ⊩v) $
          [f≡g] [ξ] [ρ] ⊩v′
            (irrelevanceTerm ([F]₁ [ξ] [ρ]) ([F] [ξ] [ρ]) ⊩w)
            (irrelevanceEqTerm ([F]₁ [ξ] [ρ]) ([F] [ξ] [ρ]) v≡w)
  irrelevanceEqTermT
    {Γ} {t} {u}
    (Bᵥ BΣˢ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ pProd rProd p≅r ([fstp] , [fstr] , [fst≡] , [snd≡])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [fstp]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _ _) ([F]₁ _ _) [fstp]
        [fstr]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _ _) ([F]₁ _ _) [fstr]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _ _) ([F]₁ _ _) [fst≡]
        [snd≡]′ = irrelevanceEqTerm′
                    (PE.cong (λ x → wk (lift id) x [ fst _ p ]₀) G≡G₁)
                    ([G] _ _ [fstp]) ([G]₁ _ _ [fstp]′) [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) pProd rProd
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            ([fstp]′ , [fstr]′ , [fst≡]′ ,  [snd≡]′)
  irrelevanceEqTermT
    {Γ} {t} {u}
    (Bᵥ BΣʷ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ prodₙ prodₙ p≅r
       (PE.refl , PE.refl , PE.refl , PE.refl ,
        [p₁] , [r₁] , [fst≡] , [snd≡])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [p₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                  ([F] _ _) ([F]₁ _ _) [p₁]
        [r₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
                  ([F] _ _) ([F]₁ _ _) [r₁]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk id) F≡F₁)
                    ([F] _ _) ([F]₁ _ _) [fst≡]
        [snd≡]′ = irrelevanceEqTerm′ (PE.cong (λ x → wk (lift id) x [ _ ]₀) G≡G₁)
                    ([G] _ _ [p₁]) ([G]₁ _ _ [p₁]′) [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) prodₙ prodₙ
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (PE.refl , PE.refl , PE.refl , PE.refl ,
             [p₁]′ , [r₁]′ , [fst≡]′ ,  [snd≡]′)
  irrelevanceEqTermT
    {Γ} {t} {u}
    (Bᵥ BΣʷ (Bᵣ F G D A≡A [F] [G] G-ext ok)
       (Bᵣ F₁ G₁ D₁ A≡A₁ [F]₁ [G]₁ G-ext₁ ok₁))
    (Σₜ₌ p r d d′ (ne x) (ne y) p≅r p~r) =
    let ΣFG≡ΣF₁G₁ = whrDet* (D , ΠΣₙ) (D₁ , ΠΣₙ)
        p~r′ = PE.subst (λ x → Γ ⊢ p ~ r ∷ x) ΣFG≡ΣF₁G₁ p~r
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t ⇒* p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u ⇒* r ∷ x) ΣFG≡ΣF₁G₁ d′) (ne x) (ne y)
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            p~r′
  irrelevanceEqTermT
    (Bᵥ BΣʷ record{} _) (Σₜ₌ _ _ _ _ prodₙ (ne _) _ (lift ()))
  irrelevanceEqTermT
    (Bᵥ BΣʷ record{} _) (Σₜ₌ _ _ _ _ (ne _) prodₙ _ (lift ()))
  irrelevanceEqTermT (Uᵥ (Uᵣ k [k] k< ⇒*U1) (Uᵣ k′ [k′] k′< ⇒*U2))
    (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u])
    with whrDet* (⇒*U1 , Uₙ) (⇒*U2 ,  Uₙ)
  ... | PE.refl = Uₜ₌ A B d d′ typeA typeB A≡B _
    (irrelevance-⊩< ↑ᵘ-irrelevance k< k′< [u])
    (irrelevance-⊩<≡ ↑ᵘ-irrelevance k< k′< [t≡u])
  irrelevanceEqTermT
    (Idᵥ ⊩A@record{} ⊩A′) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
    case whrDet* (_⊩ₗId_.⇒*Id ⊩A , Idₙ) (_⊩ₗId_.⇒*Id ⊩A′ , Idₙ) of λ {
      PE.refl →
      _ , _ , t⇒*t′ , u⇒*u′
    , (case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
         (ne t′-n u′-n t′~u′) →
           ne t′-n , ne u′-n , t′~u′
         (rfl₌ lhs≡rhs) →
             rflₙ , rflₙ
           , irrelevanceEqTerm
               (_⊩ₗId_.⊩Ty ⊩A) (_⊩ₗId_.⊩Ty ⊩A′) lhs≡rhs) }
