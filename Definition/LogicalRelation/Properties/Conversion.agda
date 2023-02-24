open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Conversion
  {a} (M : Set a) {{eqrel : EqRelSet M}} where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (Wk; _∷_)
import Definition.Untyped.BindingType M as BT
open import Definition.Typed M
open import Definition.Typed.RedSteps M
open import Definition.Typed.Properties M
import Definition.Typed.Weakening M as Wk
open import Definition.LogicalRelation M
open import Definition.LogicalRelation.ShapeView M
open import Definition.LogicalRelation.Irrelevance M

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality as PE using (≈-trans; ≈-sym)

private
  variable
    n : Nat
    p q : M
    Γ : Con Term n

-- Conversion of syntactic reduction closures.
convRed:*: : ∀ {t u A B} → Γ ⊢ t :⇒*: u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t :⇒*: u ∷ B
convRed:*: [ ⊢t , ⊢u , d ] A≡B = [ conv ⊢t  A≡B , conv ⊢u  A≡B , conv* d  A≡B ]

mutual
  -- Helper function for conversion of terms converting from left to right.
  convTermT₁ : ∀ {l l′ A B t} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
             → ShapeView Γ l l′ A B [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B / [A]
             → Γ ⊩⟨ l ⟩  t ∷ A / [A]
             → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
  convTermT₁ (ℕᵥ D D′) A≡B t = t
  convTermT₁ (Emptyᵥ D D′) A≡B t = t
  convTermT₁ (Unitᵥ D D′) A≡B t = t
  convTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq (~-to-≅ K≡M))
    in  neₜ k (convRed:*: d K≡K₁)
            (neNfₜ neK₂ (conv ⊢k K≡K₁) (~-conv k≡k K≡K₁))
  convTermT₁ {Γ = Γ} (Bᵥ (BΠ p q) (BΠ p′ q′) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Π≋Π p≈p′ q≈q′))
                     (B₌ F′ G′ BΠ! D′ W≋W′ A≡B [F≡F′] [G≡G′]) (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠF₁G₁≡ΠF′G′       = whrDet* (red D₁ , Πₙ) (D′ , Πₙ )
        F₁≡F′ , G₁≡G′ , Π₁≡Π′ = B-PE-injectivity BΠ! BΠ! ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π p , q ▷ F ▹ G ≡ x) (PE.sym ΠF₁G₁≡ΠF′G′)
                             (≅-eq A≡B)
    in  Πₜ f (convRed:*: d ΠFG≡ΠF₁G₁) funcF (≅-conv f≡f ΠFG≡ΠF₁G₁)
           (λ {_} {ρ} [ρ] ⊢Δ [a] [b] [a≡b] p′≈p₁ p′≈p₂ →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a]₁)
                                           ([G≡G′] [ρ] ⊢Δ [a]₁)
              in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁]
                              ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁
                                   (≈-trans p≈p′ p′≈p₁) (≈-trans p≈p′ p′≈p₂)))
          (λ {_} {ρ} [ρ] ⊢Δ [a] p′≈p″ →
             let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                          ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                 [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                 [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                   (PE.sym G₁≡G′))
                                          ([G] [ρ] ⊢Δ [a]₁)
                                          ([G≡G′] [ρ] ⊢Δ [a]₁)
             in  convTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁ (≈-trans p≈p′ p′≈p″)))
  convTermT₁
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ Σₚ p q) BΣₚ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
       (BT.Σ≋Σ _))
    (B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f pProd ([f₁] , [f₂])) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σₚ p , q ▷ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
            (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [f₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id (wf ⊢F₁)) F≡F₁ [f₁]
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk (lift id) G [ _ ] ≡ wk (lift id) x [ _ ] / [G] Wk.id ⊢Γ [f₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [f₁])
        [f₂]₁ = convTerm₁ ([G] Wk.id ⊢Γ [f₁]) ([G]₁ Wk.id (wf ⊢F₁) [f₁]₁) G≡G₁ [f₂]
    in  Σₜ f (convRed:*: d ΣFG≡ΣF₁G₁) (≅-conv f≡f ΣFG≡ΣF₁G₁) pProd ([f₁]₁ , [f₂]₁)
  convTermT₁
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ Σᵣ p q) BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
       (BT.Σ≋Σ _))
    (B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f prodₙ (PE.refl , [f₁] , [f₂] , PE.refl)) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σᵣ p , q ▷ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
            (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [f₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id (wf ⊢F₁)) F≡F₁ [f₁]
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk (lift id) G [ _ ] ≡ wk (lift id) x [ _ ] / [G] Wk.id ⊢Γ [f₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [f₁])
        [f₂]₁ = convTerm₁ ([G] Wk.id ⊢Γ [f₁]) ([G]₁ Wk.id (wf ⊢F₁) [f₁]₁) G≡G₁ [f₂]
    in  Σₜ f (convRed:*: d ΣFG≡ΣF₁G₁) (≅-conv f≡f ΣFG≡ΣF₁G₁) prodₙ
          (PE.refl , [f₁]₁ , [f₂]₁ , PE.refl)
  convTermT₁
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ Σᵣ p q) BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) Σ≋Σ′)
    (B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f (ne x) f~f) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σᵣ p , q ▷ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
            (≅-eq A≡B)
    in  Σₜ f (convRed:*: d ΣFG≡ΣF₁G₁) (≅-conv f≡f ΣFG≡ΣF₁G₁)
           (ne x) (~-conv f~f ΣFG≡ΣF₁G₁)
  convTermT₁ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t = t
  convTermT₁ (emb⁰¹ x) A≡B t = convTermT₁ x A≡B t
  convTermT₁ (emb¹⁰ x) A≡B t = convTermT₁ x A≡B t
  -- Impossible cases
  convTermT₁ (Bᵥ BΠ! BΣ! BA BB ()) A≡B t
  convTermT₁ (Bᵥ BΣ! BΠ! BA BB ()) A≡B t
  convTermT₁ (Bᵥ BΣᵣ BΣₚ BA BB ()) A≡B t
  convTermT₁ (Bᵥ BΣₚ BΣᵣ BA BB ()) A≡B t
  convTermT₁ (Bᵥ BΠ! BΠ! BA BB x) (B₌ F′ G′ BΣ! D′ () A≡B [F≡F′] [G≡G′]) t
  convTermT₁ (Bᵥ BΣ! BΣ! BA BB x) (B₌ F′ G′ BΠ! D′ () A≡B [F≡F′] [G≡G′]) t


  -- Helper function for conversion of terms converting from right to left.
  convTermT₂ : ∀ {l l′ A B t} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
           → ShapeView Γ l l′ A B [A] [B]
           → Γ ⊩⟨ l ⟩  A ≡ B / [A]
           → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
           → Γ ⊩⟨ l ⟩  t ∷ A / [A]
  convTermT₂ (ℕᵥ D D′) A≡B t = t
  convTermT₂ (Emptyᵥ D D′) A≡B t = t
  convTermT₂ (Unitᵥ D D′) A≡B t = t
  convTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in  neₜ k (convRed:*: d K₁≡K)
            (neNfₜ neK₂ (conv ⊢k K₁≡K) (~-conv k≡k K₁≡K))
  convTermT₂ {Γ = Γ} (Bᵥ (BΠ p q) (BΠ p′ q′) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                            (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Π≋Π p≈p′ q≈q′))
             (B₌ F′ G′ BΠ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
             (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠF₁G₁≡ΠF′G′       = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΠ! BΠ! ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π p , q ▷ F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ f (convRed:*: d (sym ΠFG≡ΠF₁G₁)) funcF (≅-conv f≡f (sym ΠFG≡ΠF₁G₁))
           (λ {_} {ρ} [ρ] ⊢Δ [a] [b] [a≡b] p≈p₁ p≈p₂ →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G′] [ρ] ⊢Δ [a])
              in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                              [G≡G₁] ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁
                                          (≈-trans (≈-sym p≈p′) p≈p₁)
                                          (≈-trans (≈-sym p≈p′) p≈p₂)))
           (λ {_} {ρ} [ρ] ⊢Δ [a] p′≈p″ →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G′] [ρ] ⊢Δ [a])
              in  convTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                            [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁ (≈-trans (≈-sym p≈p′) p′≈p″)))
  convTermT₂
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ Σₚ p q) BΣₚ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
       (BT.Σ≋Σ _))
    (B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f pProd ([f₁]₁ , [f₂]₁)) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σₚ p , q ▷ F ▹ G ≡ x)
            (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [f₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id (wf ⊢F₁)) F≡F₁ [f₁]₁
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk (lift id) G [ _ ] ≡ wk (lift id) x [ _ ] / [G] Wk.id ⊢Γ [f₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [f₁])
        [f₂] = convTerm₂ ([G] Wk.id ⊢Γ [f₁]) ([G]₁ Wk.id (wf ⊢F₁) [f₁]₁) G≡G₁ [f₂]₁
    in  Σₜ f (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (≅-conv f≡f (sym ΣFG≡ΣF₁G₁)) pProd ([f₁] , [f₂])
  convTermT₂
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ Σᵣ p q) BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
       (BT.Σ≋Σ _))
    (B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f (prodₙ {t = f₁} {u = f₂})
       (PE.refl , [f₁]₁ , [f₂]₁ , PE.refl)) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σᵣ p , q ▷ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
            (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [f₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id (wf ⊢F₁)) F≡F₁ [f₁]₁
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ l ⟩ wk (lift id) G [ f₁ ] ≡ wk (lift id) x [ f₁ ] / [G] Wk.id ⊢Γ [f₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [f₁])
        [f₂] = convTerm₂ ([G] Wk.id ⊢Γ [f₁]) ([G]₁ Wk.id (wf ⊢F₁) [f₁]₁) G≡G₁ [f₂]₁
    in  Σₜ f (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (≅-conv f≡f (sym ΣFG≡ΣF₁G₁)) prodₙ
          (PE.refl , [f₁] , [f₂] , PE.refl)
  convTermT₂
    {Γ = Γ} {l = l} {l′ = l′}
    (Bᵥ (BΣ Σᵣ p q) BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) Σ≋Σ′)
    (B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ f d f≡f (ne x) f~f) =
    let ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        ΣFG≡ΣF₁G₁ =
          PE.subst (λ x → Γ ⊢ Σᵣ p , q ▷ F ▹ G ≡ x) (PE.sym ΣF₁G₁≡ΣF′G′)
            (≅-eq A≡B)
    in  Σₜ f (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (≅-conv f≡f (sym ΣFG≡ΣF₁G₁))
           (ne x) (~-conv f~f (sym ΣFG≡ΣF₁G₁))
  convTermT₂ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t = t
  convTermT₂ (emb⁰¹ x) A≡B t = convTermT₂ x A≡B t
  convTermT₂ (emb¹⁰ x) A≡B t = convTermT₂ x A≡B t
  -- Impossible cases
  convTermT₂ (Bᵥ BΠ! BΣ! BA BB ()) A≡B t
  convTermT₂ (Bᵥ BΣ! BΠ! BA BB ()) A≡B t
  convTermT₂ (Bᵥ BΣᵣ BΣₚ BA BB ()) A≡B t
  convTermT₂ (Bᵥ BΣₚ BΣᵣ BA BB ()) A≡B t
  convTermT₂ (Bᵥ BΠ! BΠ! BA BB x) (B₌ F′ G′ BΣ! D′ () A≡B [F≡F′] [G≡G′]) t
  convTermT₂ (Bᵥ BΣ! BΣ! BA BB x) (B₌ F′ G′ BΠ! D′ () A≡B [F≡F′] [G≡G′]) t

  -- Conversion of terms converting from left to right.
  convTerm₁ : ∀ {A B t l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
            → Γ ⊩⟨ l ⟩  A ≡ B / [A]
            → Γ ⊩⟨ l ⟩  t ∷ A / [A]
            → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
  convTerm₁ [A] [B] A≡B t = convTermT₁ (goodCases [A] [B] A≡B) A≡B t

  -- Conversion of terms converting from right to left.
  convTerm₂ : ∀ {A B t l l′} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩  A ≡ B / [A]
          → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A / [A]
  -- NOTE: this would be easier to define by mutual induction with symEq (which needs conversion),
  -- rather than by defining everything from scratch for both left-to-right and right-to-left,
  -- but with the mutual definition termination checking fails in Agda.
  convTerm₂ [A] [B] A≡B t = convTermT₂ (goodCases [A] [B] A≡B) A≡B t

  -- Conversion of terms converting from right to left
  -- with some propositionally equal types.
  convTerm₂′ : ∀ {A B B′ t l l′} → B PE.≡ B′
          → ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
          → Γ ⊩⟨ l ⟩  A ≡ B′ / [A]
          → Γ ⊩⟨ l′ ⟩ t ∷ B / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A / [A]
  convTerm₂′ PE.refl [A] [B] A≡B t = convTerm₂ [A] [B] A≡B t


  -- Helper function for conversion of term equality converting from left to right.
  convEqTermT₁ : ∀ {l l′ A B t u} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
               → ShapeView Γ l l′ A B [A] [B]
               → Γ ⊩⟨ l ⟩  A ≡ B / [A]
               → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
               → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B / [B]
  convEqTermT₁ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (Emptyᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (Unitᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq (~-to-≅ K≡M))
    in  neₜ₌ k m (convRed:*: d K≡K₁)
                 (convRed:*: d′ K≡K₁)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K≡K₁))
  convEqTermT₁ {Γ = Γ} (Bᵥ (BΠ p q) (BΠ p′ q′) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                              (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Π≋Π p≈p′ q≈q′))
               (B₌ F′ G′ BΠ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
               (Πₜ₌ f g d d′ funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Bᵣ′ BΠ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΠ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = B₌ F′ G′ BΠ! D′ W≋W′ A≡B [F≡F′] [G≡G′]
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π p , q ▷ F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (convRed:*: d ΠFG≡ΠF₁G₁) (convRed:*: d′ ΠFG≡ΠF₁G₁)
            funcF funcG (≅-conv t≡u ΠFG≡ΠF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            (λ {_} {ρ} [ρ] ⊢Δ [a] p′≈p₁ p′≈p₂ →
               let F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΠ! BΠ! (whrDet* (red D₁ , Πₙ) (D′ , Πₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                            ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                   [a]₁ = convTerm₂ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                     (PE.sym G₁≡G′))
                                            ([G] [ρ] ⊢Δ [a]₁)
                                            ([G≡G′] [ρ] ⊢Δ [a]₁)
                   p≈p₁ = ≈-trans p≈p′ p′≈p₁
                   p≈p₂ = ≈-trans p≈p′ p′≈p₂
               in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a])
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁ p≈p₁ p≈p₂))
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΣ Σₚ p′ q) BΣₚ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
       (BT.Σ≋Σ _))
    (B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ pProd rProd p≅r [t] [u]
       ([p₁] , [r₁] , [fst≡] , [snd≡])) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σₚ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [p₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [p₁]
        [r₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [r₁]
        [fst≡]₁ = convEqTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ] ≡ wk (lift id) x [ _ ] / [G] Wk.id ⊢Γ [p₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [p₁])
        [snd≡]₁ = convEqTerm₁ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) G≡G₁ [snd≡]
    in  Σₜ₌ p r (convRed:*: d ΣFG≡ΣF₁G₁) (convRed:*: d′ ΣFG≡ΣF₁G₁)
            pProd rProd (≅-conv p≅r ΣFG≡ΣF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            ([p₁]₁ , [r₁]₁ , [fst≡]₁ , [snd≡]₁)
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΣ Σᵣ p′ q) BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
       (BT.Σ≋Σ _))
    (B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (prodₙ {t = p₁}) prodₙ p≅r [t] [u]
       (PE.refl , PE.refl ,
        [p₁] , [r₁] , [p₂] , [r₂] , [fst≡] , [snd≡])) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σᵣ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        Gp≡G₁p = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ] ≡ wk (lift id) x [ _ ] / [G] Wk.id ⊢Γ [p₁])
                          (PE.sym G₁≡G′) ([G≡G′] Wk.id ⊢Γ [p₁])
        Gr≡G₁r = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ] ≡ wk (lift id) x [ _ ] / [G] Wk.id ⊢Γ [r₁])
                          (PE.sym G₁≡G′) ([G≡G′] Wk.id ⊢Γ [r₁])
        [p₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [p₁]
        [r₁]₁ = convTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [r₁]
        [p₂]₁ = convTerm₁ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) Gp≡G₁p [p₂]
        [r₂]₁ = convTerm₁ ([G] Wk.id ⊢Γ [r₁]) ([G]₁ Wk.id ⊢Γ₁ [r₁]₁) Gr≡G₁r [r₂]
        [fst≡]₁ = convEqTerm₁ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ p₁ ] ≡ wk (lift id) x [ p₁ ] / [G] Wk.id ⊢Γ [p₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [p₁])
        [snd≡]₁ = convEqTerm₁ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) G≡G₁ [snd≡]
    in  Σₜ₌ p r (convRed:*: d ΣFG≡ΣF₁G₁) (convRed:*: d′ ΣFG≡ΣF₁G₁)
            prodₙ prodₙ (≅-conv p≅r ΣFG≡ΣF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            (PE.refl , PE.refl ,
             [p₁]₁ , [r₁]₁ , [p₂]₁ , [r₂]₁ , [fst≡]₁ , [snd≡]₁)
  convEqTermT₁
    {Γ = Γ}
    (Bᵥ (BΣ Σᵣ p′ q) BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) Σ≋Σ′)
    (B₌ F′ G′ BΣ! D′ W≋W′  A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (ne x) (ne y) p≅r [t] [u] p~r) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σᵣ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        p~r₁ = ~-conv p~r ΣFG≡ΣF₁G₁
    in  Σₜ₌ p r (convRed:*: d ΣFG≡ΣF₁G₁) (convRed:*: d′ ΣFG≡ΣF₁G₁)
            (ne x) (ne y) (≅-conv p≅r ΣFG≡ΣF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            p~r₁
  convEqTermT₁ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t≡u = t≡u
  convEqTermT₁ (emb⁰¹ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u
  convEqTermT₁ (emb¹⁰ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u
  -- Impossible cases
  convEqTermT₁ (Bᵥ BΠ! BΣ! BA BB ()) A≡B t≡u
  convEqTermT₁ (Bᵥ BΣ! BΠ! BA BB ()) A≡B t≡u
  convEqTermT₁ (Bᵥ BΣᵣ BΣₚ BA BB ()) A≡B t≡u
  convEqTermT₁ (Bᵥ BΣₚ BΣᵣ BA BB ()) A≡B t≡u
  convEqTermT₁ (Bᵥ BΠ! BΠ! BA BB x) (B₌ F′ G′ BΣ! D′ () A≡B [F≡F′] [G≡G′]) t≡u
  convEqTermT₁ (Bᵥ BΣ! BΣ! BA BB x) (B₌ F′ G′ BΠ! D′ () A≡B [F≡F′] [G≡G′]) t≡u
  convEqTermT₁ (Bᵥ BΣᵣ BΣᵣ BA BB x) (B₌ F′ G′ BΣₚ D′ () A≡B [F≡F′] [G≡G′]) t≡u
  convEqTermT₁ (Bᵥ BΣᵣ BΣᵣ BA BB x) A≡B (Σₜ₌ p r d d′ prodₙ (ne y) t≡u [t] [u] ())
  convEqTermT₁ (Bᵥ BΣᵣ BΣᵣ BA BB x) A≡B (Σₜ₌ p r d d′ (ne y) prodₙ t≡u [t] [u] ())

  -- Helper function for conversion of term equality converting from right to left.
  convEqTermT₂ : ∀ {l l′ A B t u} {[A] : Γ ⊩⟨ l ⟩ A} {[B] : Γ ⊩⟨ l′ ⟩ B}
             → ShapeView Γ l l′ A B [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B / [A]
             → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B / [B]
             → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
  convEqTermT₂ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (Emptyᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (Unitᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in  neₜ₌ k m (convRed:*: d K₁≡K) (convRed:*: d′ K₁≡K)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K₁≡K))
  convEqTermT₂ {Γ = Γ} (Bᵥ (BΠ p q) (BΠ p′ q′) (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                              (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) (BT.Π≋Π p≈p′ q≈q′))
               (B₌ F′ G′ BΠ! D′ W≋W′ A≡B [F≡F′] [G≡G′])
               (Πₜ₌ f g d d′ funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Bᵣ′ BΠ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΠ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = B₌ F′ G′ BΠ! D′ W≋W′ A≡B [F≡F′] [G≡G′]
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π p , q ▷ F ▹ G ≡ x)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (convRed:*: d (sym ΠFG≡ΠF₁G₁)) (convRed:*: d′ (sym ΠFG≡ΠF₁G₁))
            funcF funcG (≅-conv t≡u (sym ΠFG≡ΠF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            (λ {_} {ρ} [ρ] ⊢Δ [a] p≈p₁ p≈p₂ →
               let F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΠ! BΠ! (whrDet* (red D₁ , Πₙ) (D′ , Πₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                            ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                   [a]₁ = convTerm₁ ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                     (PE.sym G₁≡G′))
                                            ([G] [ρ] ⊢Δ [a])
                                            ([G≡G′] [ρ] ⊢Δ [a])
                   p′≈p₁ = ≈-trans (≈-sym p≈p′) p≈p₁
                   p′≈p₂ = ≈-trans (≈-sym p≈p′) p≈p₂
               in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁ p′≈p₁ p′≈p₂))
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΣ Σₚ p′ q) BΣₚ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
       (BT.Σ≋Σ _))
    (B₌ F′ G′ BΣₚ D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ pProd rProd t≡u [t] [u]
       ([p₁]₁ , [r₁]₁ , [fst≡]₁ , [snd≡]₁)) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σₚ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [p₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [p₁]₁
        [r₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [r₁]₁
        [fst≡] = convEqTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]₁
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ] ≡ wk (lift id) x [ _ ] / [G] Wk.id ⊢Γ [p₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [p₁])
        [snd≡] = convEqTerm₂ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) G≡G₁ [snd≡]₁
    in  Σₜ₌ p r (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (convRed:*: d′ (sym ΣFG≡ΣF₁G₁))
            pProd rProd (≅-conv t≡u (sym ΣFG≡ΣF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            ([p₁] , [r₁] , [fst≡] , [snd≡])
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΣ Σᵣ p′ q) BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
       (BT.Σ≋Σ _))
    (B₌ F′ G′ BΣᵣ D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (prodₙ {t = p₁}) prodₙ t≡u [t] [u]
       (PE.refl , PE.refl ,
        [p₁]₁ , [r₁]₁ , [p₂]₁ , [r₂]₁ , [fst≡]₁ , [snd≡]₁)) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σᵣ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        ⊢Γ = wf ⊢F
        ⊢Γ₁ = wf ⊢F₁
        F≡F₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk id F ≡ wk id x / [F] Wk.id ⊢Γ)
                        (PE.sym F₁≡F′)
                        ([F≡F′] Wk.id ⊢Γ)
        [p₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [p₁]₁
        [r₁] = convTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [r₁]₁
        Gp≡G₁p = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ] ≡ wk (lift id) x [ _ ] / [G] Wk.id ⊢Γ [p₁])
                          (PE.sym G₁≡G′) ([G≡G′] Wk.id ⊢Γ [p₁])
        Gr≡G₁r = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ _ ] ≡ wk (lift id) x [ _ ] / [G] Wk.id ⊢Γ [r₁])
                          (PE.sym G₁≡G′) ([G≡G′] Wk.id ⊢Γ [r₁])
        [p₂] = convTerm₂ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) Gp≡G₁p [p₂]₁
        [r₂] = convTerm₂ ([G] Wk.id ⊢Γ [r₁]) ([G]₁ Wk.id ⊢Γ₁ [r₁]₁) Gr≡G₁r [r₂]₁
        [fst≡] = convEqTerm₂ ([F] Wk.id ⊢Γ) ([F]₁ Wk.id ⊢Γ₁) F≡F₁ [fst≡]₁
        G≡G₁ = PE.subst (λ x → Γ ⊩⟨ _ ⟩ wk (lift id) G [ p₁ ] ≡ wk (lift id) x [ p₁ ] / [G] Wk.id ⊢Γ [p₁])
                        (PE.sym G₁≡G′)
                        ([G≡G′] Wk.id ⊢Γ [p₁])
        [snd≡] = convEqTerm₂ ([G] Wk.id ⊢Γ [p₁]) ([G]₁ Wk.id ⊢Γ₁ [p₁]₁) G≡G₁ [snd≡]₁
    in  Σₜ₌ p r (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (convRed:*: d′ (sym ΣFG≡ΣF₁G₁))
            prodₙ prodₙ (≅-conv t≡u (sym ΣFG≡ΣF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            (PE.refl , PE.refl ,
             [p₁] , [r₁] , [p₂] , [r₂] , [fst≡] , [snd≡])
  convEqTermT₂
    {Γ = Γ}
    (Bᵥ (BΣ Σᵣ p′ q) BΣᵣ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
       (Bᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) Σ≋Σ′)
    (B₌ F′ G′ BΣᵣ D′ W≋W′ A≡B [F≡F′] [G≡G′])
    (Σₜ₌ p r d d′ (ne x) (ne y) t≡u [t] [u] p~r₁) =
    let [A] = Bᵣ′ BΣ! F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Bᵣ′ BΣ! F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = B₌ F′ G′ BΣ! D′ W≋W′ A≡B [F≡F′] [G≡G′]
        ΣF₁G₁≡ΣF′G′       = whrDet* (red D₁ , Σₙ) (D′ , Σₙ)
        F₁≡F′ , G₁≡G′ , _ = B-PE-injectivity BΣ! BΣ! ΣF₁G₁≡ΣF′G′
        ΣFG≡ΣF₁G₁ = PE.subst (λ x → Γ ⊢ Σᵣ p′ , q ▷ F ▹ G ≡ x)
                             (PE.sym ΣF₁G₁≡ΣF′G′) (≅-eq A≡B)
        p~r = ~-conv p~r₁ (sym ΣFG≡ΣF₁G₁)
    in  Σₜ₌ p r (convRed:*: d (sym ΣFG≡ΣF₁G₁)) (convRed:*: d′ (sym ΣFG≡ΣF₁G₁))
            (ne x) (ne y) (≅-conv t≡u (sym ΣFG≡ΣF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            p~r
  convEqTermT₂ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t≡u = t≡u
  convEqTermT₂ (emb⁰¹ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u
  convEqTermT₂ (emb¹⁰ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u
  -- Impossible cases
  convEqTermT₂ (Bᵥ BΠ! BΣ! BA BB ()) A≡B t≡u
  convEqTermT₂ (Bᵥ BΣ! BΠ! BA BB ()) A≡B t≡u
  convEqTermT₂ (Bᵥ BΣᵣ BΣₚ BA BB ()) A≡B t≡u
  convEqTermT₂ (Bᵥ BΣₚ BΣᵣ BA BB ()) A≡B t≡u
  convEqTermT₂ (Bᵥ BΠ! BΠ! BA BB x) (B₌ F′ G′ BΣ! D′ () A≡B [F≡F′] [G≡G′]) t≡u
  convEqTermT₂ (Bᵥ BΣ! BΣ! BA BB x) (B₌ F′ G′ BΠ! D′ () A≡B [F≡F′] [G≡G′]) t≡u
  convEqTermT₂ (Bᵥ BΣᵣ BΣᵣ BA BB x) (B₌ F′ G′ BΣₚ D′ () A≡B [F≡F′] [G≡G′]) t≡u
  convEqTermT₂ (Bᵥ BΣₚ BΣₚ BA BB x) (B₌ F′ G′ BΣᵣ D′ () A≡B [F≡F′] [G≡G′]) t≡u
  convEqTermT₂ (Bᵥ BΣᵣ BΣᵣ BA BB x) A≡B (Σₜ₌ p r d d′ prodₙ (ne y) t≡u [t] [u] ())
  convEqTermT₂ (Bᵥ BΣᵣ BΣᵣ BA BB x) A≡B (Σₜ₌ p r d d′ (ne y) prodₙ t≡u [t] [u] ())

  -- Conversion of term equality converting from left to right.
  convEqTerm₁ : ∀ {l l′ A B t u} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
              → Γ ⊩⟨ l ⟩  A ≡ B / [A]
              → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
              → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B / [B]
  convEqTerm₁ [A] [B] A≡B t≡u = convEqTermT₁ (goodCases [A] [B] A≡B) A≡B t≡u

  -- Conversion of term equality converting from right to left.
  convEqTerm₂ : ∀ {l l′ A B t u} ([A] : Γ ⊩⟨ l ⟩ A) ([B] : Γ ⊩⟨ l′ ⟩ B)
            → Γ ⊩⟨ l ⟩  A ≡ B / [A]
            → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B / [B]
            → Γ ⊩⟨ l ⟩  t ≡ u ∷ A / [A]
  convEqTerm₂ [A] [B] A≡B t≡u = convEqTermT₂ (goodCases [A] [B] A≡B) A≡B t≡u
