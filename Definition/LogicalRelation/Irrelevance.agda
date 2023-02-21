open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Irrelevance
  {a} (M : Set a) {{eqrel : EqRelSet M}} where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (Wk; _∷_)
import Definition.Untyped.BindingType M as BT
open import Definition.Typed M
import Definition.Typed.Weakening M as Wk
open import Definition.Typed.Properties M
open import Definition.LogicalRelation M
open import Definition.LogicalRelation.ShapeView M

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≈_)

private
  variable
    n : Nat
    Γ Γ′ : Con Term n

-- Irrelevance for propositionally equal types
irrelevance′ : ∀ {A A′ l}
             → A PE.≡ A′
             → Γ ⊩⟨ l ⟩ A
             → Γ ⊩⟨ l ⟩ A′
irrelevance′ PE.refl [A] = [A]

-- Irrelevance for propositionally equal types and contexts
irrelevanceΓ′ : ∀ {l A A′}
              → Γ PE.≡ Γ′
              → A PE.≡ A′
              → Γ  ⊩⟨ l ⟩ A
              → Γ′ ⊩⟨ l ⟩ A′
irrelevanceΓ′ PE.refl PE.refl [A] = [A]

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

  -- Irrelevance for type equality with propositionally equal types and
  -- a lifting of propositionally equal types
  irrelevanceEqLift″ : ∀ {A A′ B B′ C C′ l l′}
                        (eqA : A PE.≡ A′) (eqB : B PE.≡ B′) (eqC : C PE.≡ C′)
                        (p : Γ ∙ C ⊩⟨ l ⟩ A) (q : Γ ∙ C′ ⊩⟨ l′ ⟩ A′)
                      → Γ ∙ C ⊩⟨ l ⟩ A ≡ B / p → Γ ∙ C′ ⊩⟨ l′ ⟩ A′ ≡ B′ / q
  irrelevanceEqLift″ PE.refl PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Helper for irrelevance of type equality using shape view
  irrelevanceEqT : ∀ {A B l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                       → ShapeView Γ l l′ A A p q
                       → Γ ⊩⟨ l ⟩ A ≡ B / p → Γ ⊩⟨ l′ ⟩ A ≡ B / q
  irrelevanceEqT (ℕᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Unitᵥ D D′) A≡B = A≡B
  irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
                 rewrite whrDet* (red D , ne neK) (red D₁ , ne neK₁) =
    ne₌ M D′ neM K≡M
  irrelevanceEqT {Γ = Γ} (Bᵥ W W′ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) W≋W′)
                 (B₌ F′ G′ W″ D′ W≋W″ A≡B [F≡F′] [G≡G′]) =
    let ΠFG≡ΠF₁G₁       = whrDet* (red D , ⟦ W ⟧ₙ) (red D₁ , ⟦ W′ ⟧ₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity W W′ ΠFG≡ΠF₁G₁
    in  B₌ F′ G′ W″ D′ (BT.trans (BT.sym W≋W′) W≋W″) (PE.subst (λ x → Γ ⊢ x ≅ ⟦ W″ ⟧ F′ ▹ G′) ΠFG≡ΠF₁G₁ A≡B)
           (λ {_} {ρ} [ρ] ⊢Δ → irrelevanceEq′ (PE.cong (wk ρ) F≡F₁) ([F] [ρ] ⊢Δ)
                                    ([F]₁ [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ))
           (λ {_} {ρ} [ρ] ⊢Δ [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                         ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a]₁
              in  irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁)
                                 ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([G≡G′] [ρ] ⊢Δ [a]))
  irrelevanceEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _)) A≡B = A≡B
  irrelevanceEqT (emb⁰¹ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (emb¹⁰ x) A≡B = irrelevanceEqT x A≡B

--------------------------------------------------------------------------------

  -- Irrelevance for terms
  irrelevanceTerm : ∀ {A t l l′} (p : Γ ⊩⟨ l ⟩ A) (q : Γ ⊩⟨ l′ ⟩ A)
                  → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A / q
  irrelevanceTerm p q t = irrelevanceTermT (goodCasesRefl p q) t

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

  -- Irrelevance for terms with propositionally equal types, terms and contexts
  irrelevanceTermΓ″ : ∀ {l l′ A A′ t t′}
                     → Γ PE.≡ Γ′
                     → A PE.≡ A′
                     → t PE.≡ t′
                     → ([A]  : Γ  ⊩⟨ l  ⟩ A)
                       ([A′] : Γ′ ⊩⟨ l′ ⟩ A′)
                     → Γ  ⊩⟨ l  ⟩ t ∷ A  / [A]
                     → Γ′ ⊩⟨ l′ ⟩ t′ ∷ A′ / [A′]
  irrelevanceTermΓ″ PE.refl PE.refl PE.refl [A] [A′] [t] = irrelevanceTerm [A] [A′] [t]

  -- Helper for irrelevance of terms using shape view
  irrelevanceTermT : ∀ {A t l l′} {p : Γ ⊩⟨ l ⟩ A} {q : Γ ⊩⟨ l′ ⟩ A}
                         → ShapeView Γ l l′ A A p q
                         → Γ ⊩⟨ l ⟩ t ∷ A / p → Γ ⊩⟨ l′ ⟩ t ∷ A / q
  irrelevanceTermT (ℕᵥ D D′) t = t
  irrelevanceTermT (Emptyᵥ D D′) t = t
  irrelevanceTermT (Unitᵥ D D′) t = t
  irrelevanceTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ k d nf)
                   with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ k d nf)
    | PE.refl = neₜ k d nf
  irrelevanceTermT {Γ = Γ} {t = t} (Bᵥ BΠ! BΠ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                   (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) Π≋Π′)
                   (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠFG≡ΠF₁G₁ = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , G≡G₁ , W≡W₁ = B-PE-injectivity BΠ! BΠ! ΠFG≡ΠF₁G₁
        p≡p₁ , q≡q₁ = BΠ-PE-injectivity W≡W₁
    in  Πₜ f (PE.subst (λ x → Γ ⊢ t :⇒*: f ∷ x) ΠFG≡ΠF₁G₁ d) funcF
           (PE.subst (λ x → Γ ⊢ f ≅ f ∷ x) ΠFG≡ΠF₁G₁ f≡f)
           (λ {_} {ρ} {Δ} {a} {b} {p′} {p″} [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁ p≈p′ p≈p″ →
             let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                        ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a]₁
                 [b] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                        ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [b]₁
                 [a≡b] = irrelevanceEqTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                            ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a≡b]₁
                 p₁≈p′ = PE.subst (λ q → q ≈ p′) (PE.sym p≡p₁) p≈p′
                 p₁≈p″ = PE.subst (λ q → q ≈ p″) (PE.sym p≡p₁) p≈p″
             in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                    ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                                    ([f] [ρ] ⊢Δ [a] [b] [a≡b] p₁≈p′ p₁≈p″))
           λ {_} {ρ} {Δ} {a} {p′} [ρ] ⊢Δ [a]₁ p≈p′ →
             let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                        ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a]₁
             in  irrelevanceTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                  ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                                  ([f]₁ [ρ] ⊢Δ [a] (PE.subst (λ q → q ≈ p′) (PE.sym p≡p₁) p≈p′))
  irrelevanceTermT {Γ = Γ} {t = t} (Bᵥ BΣₚ BΣₚ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                           (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ q≈q′))
                                   (Σₜ p d p≅p pProd ([fstt] , [sndt])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [fstt]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁) ([F] Wk.id (wf ⊢F))
                                 ([F]₁ Wk.id (wf ⊢F₁)) [fstt]
        [sndt]′ = irrelevanceTerm′ (PE.cong (λ x → wk (lift id) x [ _ ]) G≡G₁)
                                 ([G] Wk.id (wf ⊢F) [fstt]) ([G]₁ Wk.id (wf ⊢F₁) [fstt]′) [sndt]
    in  Σₜ p (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d)
           (PE.subst (λ x →  Γ ⊢ p ≅ p ∷ x) ΣFG≡ΣF₁G₁ p≅p) pProd ([fstt]′ , [sndt]′)
  irrelevanceTermT {Γ = Γ} {t = t} (Bᵥ BΣᵣ BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                          (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ q≈q′))
                                   (Σₜ p d p≅p prodₙ ([t₁] , [t₂] , PE.refl)) =
    let ΣFG≡ΣF₁G₁       = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [t₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁) ([F] Wk.id (wf ⊢F))
                                 ([F]₁ Wk.id (wf ⊢F₁)) [t₁]
        [t₂]′ = irrelevanceTerm′ (PE.cong (λ x → wk (lift id) x [ _ ]) G≡G₁)
                                 ([G] Wk.id (wf ⊢F) [t₁]) ([G]₁ Wk.id (wf ⊢F₁) [t₁]′) [t₂]
    in  Σₜ p (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d)
           (PE.subst (λ x →  Γ ⊢ p ≅ p ∷ x) ΣFG≡ΣF₁G₁ p≅p) prodₙ ([t₁]′ , [t₂]′ , PE.refl)
  irrelevanceTermT {Γ = Γ} {t = t} (Bᵥ BΣᵣ BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                           (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ q≈q′))
                                   (Σₜ p d p≅p (ne x) p~p) =
    let ΣFG≡ΣF₁G₁       = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
    in  Σₜ p (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d)
           (PE.subst (λ x →  Γ ⊢ p ≅ p ∷ x) ΣFG≡ΣF₁G₁ p≅p) (ne x)
           (PE.subst (λ x → Γ ⊢ p ~ p ∷ x) ΣFG≡ΣF₁G₁ p~p)
  irrelevanceTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) t = t
  irrelevanceTermT (emb⁰¹ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb¹⁰ x) t = irrelevanceTermT x t
  -- Impossible cases
  irrelevanceTermT (Bᵥ (BΠ p q) (BΣ x q′) BA BB ()) t
  irrelevanceTermT (Bᵥ (BΣ x q) (BΠ p q′) BA BB ()) t
  irrelevanceTermT (Bᵥ BΣᵣ BΣₚ BA BB ()) t
  irrelevanceTermT (Bᵥ BΣₚ BΣᵣ BA BB ()) t

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
  irrelevanceEqTermT (ℕᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Emptyᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Unitᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
                     with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
    | PE.refl = neₜ₌ k m d d′ nf
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u}
                     (Bᵥ BΠ! BΠ! (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) Π≋Π′)
                     (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
    let ΠFG≡ΠF₁G₁ = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , G≡G₁ , W≡W₁ = B-PE-injectivity BΠ! BΠ! ΠFG≡ΠF₁G₁
        p≡p′ , q≡q₁ = BΠ-PE-injectivity W≡W₁
        [A]         = Bᵣ′ BΠ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [A]₁        = Bᵣ′ BΠ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
    in  Πₜ₌ f g (PE.subst (λ x → Γ ⊢ t :⇒*: f ∷ x) ΠFG≡ΠF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u :⇒*: g ∷ x) ΠFG≡ΠF₁G₁ d′) funcF funcG
            (PE.subst (λ x → Γ ⊢ f ≅ g ∷ x) ΠFG≡ΠF₁G₁ f≡g)
            (irrelevanceTerm′ PE.refl [A] [A]₁ [f])
            (irrelevanceTerm′ PE.refl [A] [A]₁ [g])
            (λ {_} {ρ} {Δ} {a} {p₁} {p₂} [ρ] ⊢Δ [a]₁ p′≈p₁ p′≈p₂ →
               let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁))
                                          ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) [a]₁
                   p≈p₁ = PE.subst (λ p → p ≈ p₁) (PE.sym p≡p′) p′≈p₁
                   p≈p₂ = PE.subst (λ p → p ≈ p₂) (PE.sym p≡p′) p′≈p₂
               in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁)
                                     ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([f≡g] [ρ] ⊢Δ [a] p≈p₁ p≈p₂))
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u} (Bᵥ BΣₚ BΣₚ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                                     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ q≈q′))
                                             (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] ([fstp] , [fstr] , [fst≡] , [snd≡])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [A]             = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [A]₁            = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [fstp]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
          ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
          [fstp]
        [fstr]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
          ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
          [fstr]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk id) F≡F₁)
          ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
          [fst≡]
        [snd≡]′ = irrelevanceEqTerm′ (PE.cong (λ x → wk (lift id) x [ fst p ]) G≡G₁)
          ([G] Wk.id (wf ⊢F) [fstp]) ([G]₁ Wk.id (wf ⊢F₁) [fstp]′)
          [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u :⇒*: r ∷ x) ΣFG≡ΣF₁G₁ d′) pProd rProd
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (irrelevanceTerm [A] [A]₁ [t]) (irrelevanceTerm [A] [A]₁ [u])
            ([fstp]′ , [fstr]′ , [fst≡]′ ,  [snd≡]′)
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u} (Bᵥ BΣᵣ BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                                     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ q≈q′))
                                             (Σₜ₌ p r d d′ prodₙ prodₙ p≅r [t] [u] ([p₁] , [r₁] , [p₂] , [r₂] , [fst≡] , [snd≡])) =
    let ΣFG≡ΣF₁G₁       = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [A]             = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [A]₁            = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [p₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
          ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
          [p₁]
        [r₁]′ = irrelevanceTerm′ (PE.cong (wk id) F≡F₁)
          ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
          [r₁]
        [p₂]′ = irrelevanceTerm′ (PE.cong (λ G → wk (lift id) G [ _ ]) G≡G₁)
                                 ([G] Wk.id (wf ⊢F) [p₁])
                                 ([G]₁ Wk.id (wf ⊢F₁) [p₁]′) [p₂]
        [r₂]′ = irrelevanceTerm′ (PE.cong (λ G → wk (lift id) G [ _ ]) G≡G₁)
                                 ([G] Wk.id (wf ⊢F) [r₁])
                                 ([G]₁ Wk.id (wf ⊢F₁) [r₁]′) [r₂]
        [fst≡]′ = irrelevanceEqTerm′ (PE.cong (wk id) F≡F₁)
          ([F] Wk.id (wf ⊢F)) ([F]₁ Wk.id (wf ⊢F₁))
          [fst≡]
        [snd≡]′ = irrelevanceEqTerm′ (PE.cong (λ x → wk (lift id) x [ _ ]) G≡G₁)
          ([G] Wk.id (wf ⊢F) [p₁]) ([G]₁ Wk.id (wf ⊢F₁) [p₁]′)
          [snd≡]
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u :⇒*: r ∷ x) ΣFG≡ΣF₁G₁ d′) prodₙ prodₙ
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (irrelevanceTerm [A] [A]₁ [t]) (irrelevanceTerm [A] [A]₁ [u])
            ([p₁]′ , [r₁]′ , [p₂]′ , [r₂]′ , [fst≡]′ ,  [snd≡]′)
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u} (Bᵥ BΣᵣ BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                                     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ q≈q′))
                                             (Σₜ₌ p r d d′ (ne x) (ne y) p≅r [t] [u] p~r) =
    let ΣFG≡ΣF₁G₁       = whrDet* (red D , Σₙ) (red D₁ , Σₙ)
        F≡F₁ , G≡G₁ , _ = B-PE-injectivity BΣ! BΣ! ΣFG≡ΣF₁G₁
        [A]             = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [A]₁            = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        p~r′ = PE.subst (λ x → Γ ⊢ p ~ r ∷ x) ΣFG≡ΣF₁G₁ p~r
    in  Σₜ₌ p r (PE.subst (λ x → Γ ⊢ t :⇒*: p ∷ x) ΣFG≡ΣF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u :⇒*: r ∷ x) ΣFG≡ΣF₁G₁ d′) (ne x) (ne y)
            (PE.subst (λ x → Γ ⊢ p ≅ r ∷ x) ΣFG≡ΣF₁G₁ p≅r)
            (irrelevanceTerm [A] [A]₁ [t]) (irrelevanceTerm [A] [A]₁ [u])
            p~r′
  irrelevanceEqTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) t≡u = t≡u
  irrelevanceEqTermT (emb⁰¹ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb¹⁰ x) t≡u = irrelevanceEqTermT x t≡u
  -- Impossible cases
  irrelevanceEqTermT (Bᵥ (BΠ p q) (BΣ x q′) BA BB ()) t≡u
  irrelevanceEqTermT (Bᵥ (BΣ x q) (BΠ p q′) BA BB ()) t≡u
  irrelevanceEqTermT (Bᵥ BΣᵣ BΣₚ BA BB ()) t≡u
  irrelevanceEqTermT (Bᵥ BΣₚ BΣᵣ BA BB ()) t≡u
  irrelevanceEqTermT (Bᵥ BΣᵣ BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ q≈q′))
                     (Σₜ₌ p r d d′ prodₙ (ne x) p≅r [t] [u] ())
  irrelevanceEqTermT (Bᵥ BΣᵣ BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Σ≋Σ q≈q′))
                     (Σₜ₌ p r d d′ (ne x) prodₙ p≅r [t] [u] ())
